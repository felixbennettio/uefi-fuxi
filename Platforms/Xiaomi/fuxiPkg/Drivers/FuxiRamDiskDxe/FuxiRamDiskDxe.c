/** @file
  Expose the UniXNU payload volume as a block device.

  v2: `fastboot boot` loads our boot image; ABL then places the DTB (reserved
  by SEC at a fixed address, printed as "reserved DT") and the ramdisk inside
  the 0xA8000000..0xB8000000 window and records both in the DT /chosen node.
  The original driver trusted a SEC hint HOB that Mu-Silicium never publishes
  (wrong GUID) and skipped reserved memory when scanning, so the payload was
  never found. This version, in order:

    1. reads the incoming x0 (DTB) from the Mu-Silicium entry-argument HOB,
    2. falls back to the DT address observed in the SEC log on this device,
    3. falls back to scanning the ABL kernel window for an FDT magic,
    4. publishes /chosen linux,initrd-start..end as the payload volume,
    5. falls back to the original memory-map scan (non-reserved memory),
    6. falls back to probing the ABL kernel window for a FAT boot sector.

  SPDX-License-Identifier: BSD-2-Clause-Patent
**/

#include <Uefi.h>
#include <Library/UefiBootServicesTableLib.h>
#include <Library/UefiLib.h>
#include <Library/BaseLib.h>
#include <Library/BaseMemoryLib.h>
#include <Library/MemoryAllocationLib.h>
#include <Library/DevicePathLib.h>
#include <Library/HobLib.h>
#include <Protocol/BlockIo.h>
#include <Protocol/DevicePath.h>

#define FUXI_LABEL_OFFSET  0x47
#define FUXI_LABEL_LENGTH  7
#define FUXI_BLOCK_SIZE    512

// ABL loads the kernel, the ramdisk and the DTB inside this window; SEC
// reserves it in its memory map ("Kernel", handed to the next payload).
#define FUXI_KERNEL_WINDOW_BASE  0xA8000000ULL
#define FUXI_KERNEL_WINDOW_END   0xB8000000ULL

// DT address SEC printed as "reserved DT 0xB6098000..0xB615FFFF" on this
// device. Deterministic for this ABL, but only the first guess tried.
#define FUXI_KNOWN_DT_BASE  0xB6098000ULL

// Mu-Silicium SEC stores the incoming x0 (DTB address) in this HOB as UINT64.
STATIC CONST EFI_GUID mDtbHobGuid = {
  0xDAEE82E6, 0x8090, 0x4E72, { 0xBF, 0xB9, 0x78, 0xC1, 0x3C, 0xD4, 0xE3, 0x59 }
};

#define FDT_MAGIC      0xD00DFEED
#define FDT_BEGIN_NODE 1
#define FDT_END_NODE   2
#define FDT_PROP       3
#define FDT_NOP        4
#define FDT_END        9

STATIC EFI_BLOCK_IO_MEDIA  mMedia;
STATIC EFI_BLOCK_IO_PROTOCOL  mBlockIo;
STATIC UINT8                  *mVolumeBase;
STATIC BOOLEAN                mLastLabeled;
STATIC UINT64                 mVolumeBytes;

STATIC
BOOLEAN
Scannable (
  IN EFI_MEMORY_TYPE  Type
  )
{
  // Only types that the memory map guarantees are backed by normal RAM.
  // Reserved and MMIO ranges can be listed yet still fault when read.
  return (Type == EfiConventionalMemory) || (Type == EfiLoaderData) ||
         (Type == EfiLoaderCode) || (Type == EfiBootServicesData) ||
         (Type == EfiBootServicesCode) || (Type == EfiRuntimeServicesData) ||
         (Type == EfiRuntimeServicesCode);
}

STATIC
BOOLEAN
IsPayloadVolume (
  IN CONST UINT8  *Sector,
  OUT UINT64      *TotalSectors
  )
{
  UINT16  BytesPerSector;
  UINT32  SectorsPerFat;
  UINT32  Total32;
  UINT16  Total16;

  if ((Sector[510] != 0x55) || (Sector[511] != 0xAA)) {
    return FALSE;
  }

  // Prefer the expected label, but accept any plausible FAT volume so a
  // differently labelled payload still mounts.
  mLastLabeled = (CompareMem (Sector + FUXI_LABEL_OFFSET, "FUXIESP", FUXI_LABEL_LENGTH) == 0);

  BytesPerSector = (UINT16)(Sector[11] | (Sector[12] << 8));
  if (BytesPerSector != FUXI_BLOCK_SIZE) {
    return FALSE;
  }

  Total16 = (UINT16)(Sector[19] | (Sector[20] << 8));
  Total32 = (UINT32)(Sector[32] | (Sector[33] << 8) | (Sector[34] << 16) | ((UINT32)Sector[35] << 24));
  *TotalSectors = (Total16 != 0) ? Total16 : Total32;
  if (*TotalSectors == 0) {
    return FALSE;
  }

  SectorsPerFat = (UINT32)(Sector[36] | (Sector[37] << 8) | (Sector[38] << 16) | ((UINT32)Sector[39] << 24));
  if (SectorsPerFat == 0) {
    return FALSE;
  }

  //
  // Only a large volume can be the payload; this rejects stray boot sectors in
  // unrelated RAM without trusting the label alone.
  //
  if (*TotalSectors < (64ULL * 1024 * 1024 / FUXI_BLOCK_SIZE)) {
    return FALSE;
  }

  return TRUE;
}

STATIC
UINT32
ReadBe32 (
  IN CONST VOID  *P
  )
{
  CONST UINT8  *B = (CONST UINT8 *)P;

  return ((UINT32)B[0] << 24) | ((UINT32)B[1] << 16) | ((UINT32)B[2] << 8) | (UINT32)B[3];
}

STATIC
UINT64
ReadBe64 (
  IN CONST VOID  *P
  )
{
  return ((UINT64)ReadBe32 (P) << 32) | (UINT64)ReadBe32 ((CONST UINT8 *)P + 4);
}

//
// Minimal FDT walker: return /chosen linux,initrd-start and -end. Avoids a
// dependency on any FdtLib the platform DSC may or may not link.
//
STATIC
BOOLEAN
ReadChosenInitrd (
  IN  CONST VOID  *Fdt,
  OUT UINT64      *Start,
  OUT UINT64      *End
  )
{
  CONST UINT8  *Base       = (CONST UINT8 *)Fdt;
  UINT32       TotalSize   = ReadBe32 (Base + 4);
  UINT32       OffStruct   = ReadBe32 (Base + 8);
  UINT32       OffStrings  = ReadBe32 (Base + 12);
  CONST UINT8  *P;
  CONST UINT8  *Limit;
  UINTN        Depth    = 0;
  BOOLEAN      InChosen = FALSE;
  BOOLEAN      HaveStart = FALSE;
  BOOLEAN      HaveEnd   = FALSE;
  UINT64       S = 0;
  UINT64       E = 0;

  if ((ReadBe32 (Base) != FDT_MAGIC) || (TotalSize < 40) || (TotalSize > 0x400000) ||
      (OffStruct >= TotalSize) || (OffStrings >= TotalSize))
  {
    return FALSE;
  }

  P     = Base + OffStruct;
  Limit = Base + TotalSize;

  while (P + 4 <= Limit) {
    UINT32 Token = ReadBe32 (P);
    P += 4;

    if (Token == FDT_BEGIN_NODE) {
      UINTN  NameLen = 0;

      while (P[NameLen] != 0) {
        NameLen++;
      }

      Depth++;
      if ((Depth == 2) && (CompareMem (P, "chosen", 7) == 0)) {
        InChosen = TRUE;
      }

      P = (CONST UINT8 *)(((UINTN)P + NameLen + 1 + 3) & ~(UINTN)3);
    } else if (Token == FDT_END_NODE) {
      if (InChosen) {
        // All properties of /chosen are behind us.
        break;
      }

      if (Depth == 0) {
        break;
      }

      Depth--;
    } else if (Token == FDT_PROP) {
      UINT32       Len     = ReadBe32 (P);
      UINT32       NameOff;
      CONST UINT8  *Val;

      P += 4;
      NameOff = ReadBe32 (P);
      P += 4;
      Val = P;
      P += (Len + 3) & ~3;

      if (InChosen && ((Len == 4) || (Len == 8) || (Len == 16))) {
        CONST CHAR8  *PropName = (CONST CHAR8 *)(Base + OffStrings + NameOff);
        UINT64       Val64;

        if (Len == 4) {
          Val64 = ReadBe32 (Val);
        } else {
          Val64 = ReadBe64 (Val);
        }

        if (CompareMem (PropName, "linux,initrd-start", 19) == 0) {
          S        = Val64;
          HaveStart = TRUE;
        } else if (CompareMem (PropName, "linux,initrd-end", 17) == 0) {
          E        = Val64;
          HaveEnd = TRUE;
        }
      }
    } else if ((Token == FDT_NOP) || (Token == FDT_END)) {
      if (Token == FDT_END) {
        break;
      }
    } else {
      // Unknown token: the structure block is not something we understand.
      break;
    }
  }

  if (!HaveStart || !HaveEnd || (E <= S)) {
    return FALSE;
  }

  *Start = S;
  *End   = E;
  return TRUE;
}

//
// Locate the ABL device tree: entry-argument HOB, then the address from the
// SEC log, then a magic scan of the ABL kernel window.
//
STATIC
UINT64
FindDeviceTree (
  VOID
  )
{
  EFI_HOB_GUID_TYPE  *Hob;
  UINT64             Addr;

  Hob = GetFirstGuidHob (&mDtbHobGuid);
  if ((Hob != NULL) && (GET_GUID_HOB_DATA_SIZE (Hob) >= sizeof (UINT64))) {
    UINT64 Cand = ReadUnaligned64 ((CONST UINT64 *)GET_GUID_HOB_DATA (Hob));

    if ((Cand >= 0x80000000ULL) && (Cand < 0x100000000ULL) &&
        (ReadBe32 ((VOID *)(UINTN)Cand) == FDT_MAGIC))
    {
      Print (L"FUXIRAMDISK: dtb from entry-arg hob at %lx\n", Cand);
      return Cand;
    }
  }

  if (ReadBe32 ((VOID *)(UINTN)FUXI_KNOWN_DT_BASE) == FDT_MAGIC) {
    Print (L"FUXIRAMDISK: dtb at the known address %lx\n", (UINT64)FUXI_KNOWN_DT_BASE);
    return FUXI_KNOWN_DT_BASE;
  }

  for (Addr = FUXI_KERNEL_WINDOW_BASE; Addr + 0x1000 <= FUXI_KERNEL_WINDOW_END; Addr += 4) {
    if (ReadBe32 ((VOID *)(UINTN)Addr) == FDT_MAGIC) {
      Print (L"FUXIRAMDISK: dtb found by window scan at %lx\n", Addr);
      return Addr;
    }
  }

  return 0;
}

STATIC
BOOLEAN
ScanWindowForPayload (
  VOID
  )
{
  UINT64  Addr;
  UINT64  Total;

  for (Addr = FUXI_KERNEL_WINDOW_BASE; Addr + FUXI_BLOCK_SIZE <= FUXI_KERNEL_WINDOW_END; Addr += FUXI_BLOCK_SIZE) {
    if (IsPayloadVolume ((UINT8 *)(UINTN)Addr, &Total)) {
      mVolumeBase  = (UINT8 *)(UINTN)Addr;
      mVolumeBytes = Total * FUXI_BLOCK_SIZE;
      Print (L"FUXIRAMDISK: fat volume in kernel window at %lx\n", Addr);
      return TRUE;
    }
  }

  return FALSE;
}

STATIC
EFI_STATUS
EFIAPI
FuxiBlockReset (
  IN EFI_BLOCK_IO_PROTOCOL  *This,
  IN BOOLEAN                ExtendedVerification
  )
{
  return EFI_SUCCESS;
}

STATIC
EFI_STATUS
EFIAPI
FuxiBlockRead (
  IN EFI_BLOCK_IO_PROTOCOL  *This,
  IN UINT32                 MediaId,
  IN EFI_LBA                Lba,
  IN UINTN                  BufferSize,
  OUT VOID                  *Buffer
  )
{
  UINT64  Offset;
  UINT64  End;

  if ((MediaId != 0) && (MediaId != This->Media->MediaId)) {
    return EFI_MEDIA_CHANGED;
  }

  if (Buffer == NULL) {
    return EFI_INVALID_PARAMETER;
  }

  if ((BufferSize % FUXI_BLOCK_SIZE) != 0) {
    return EFI_BAD_BUFFER_SIZE;
  }

  Offset = Lba * FUXI_BLOCK_SIZE;
  End    = Offset + BufferSize;
  if ((End < Offset) || (End > mVolumeBytes)) {
    return EFI_INVALID_PARAMETER;
  }

  CopyMem (Buffer, mVolumeBase + Offset, BufferSize);
  return EFI_SUCCESS;
}

STATIC
EFI_STATUS
EFIAPI
FuxiBlockWrite (
  IN EFI_BLOCK_IO_PROTOCOL  *This,
  IN UINT32                 MediaId,
  IN EFI_LBA                Lba,
  IN UINTN                  BufferSize,
  IN VOID                   *Buffer
  ){
  return EFI_WRITE_PROTECTED;
}

STATIC
EFI_STATUS
EFIAPI
FuxiBlockFlush (
  IN EFI_BLOCK_IO_PROTOCOL  *This
  )
{
  return EFI_SUCCESS;
}

BOOLEAN
LocatePayload (
  VOID
  )
{
  EFI_STATUS             Status;
  EFI_MEMORY_DESCRIPTOR  *Map;
  UINTN                  MapSize;
  UINTN                  MapKey;
  UINTN                  DescSize;
  UINT32                 DescVersion;
  UINTN                  Index;
  UINTN                  Count;
  UINT64                 Address;
  UINT64                 TotalSectors;
  UINT8                  *Page;
  UINT64                 RegionEnd;

  MapSize = 0;
  gBS->GetMemoryMap (&MapSize, NULL, &MapKey, &DescSize, &DescVersion);
  MapSize += 16 * DescSize;
  Map = AllocatePool (MapSize);
  if (Map == NULL) {
    return FALSE;
  }

  Status = gBS->GetMemoryMap (&MapSize, Map, &MapKey, &DescSize, &DescVersion);
  if (EFI_ERROR (Status)) {
    FreePool (Map);
    return FALSE;
  }

  Count = MapSize / DescSize;
  Print (L"FUXIRAMDISK: scanning %lu memory regions\n", (UINT64)Count);
  for (Index = 0; Index < Count; Index++) {
    EFI_MEMORY_DESCRIPTOR  *Entry = (EFI_MEMORY_DESCRIPTOR *)((UINT8 *)Map + Index * DescSize);

    if (!Scannable (Entry->Type)) {
      continue;
    }

    RegionEnd = Entry->PhysicalStart + (Entry->NumberOfPages << 12);

    // The bootloader may place the ramdisk on a 512-byte boundary.
    for (Address = Entry->PhysicalStart; Address + FUXI_BLOCK_SIZE <= RegionEnd; Address += FUXI_BLOCK_SIZE) {
      Page = (UINT8 *)(UINTN)Address;
      if (!IsPayloadVolume (Page, &TotalSectors)) {
        continue;
      }

      Print (L"FUXIRAMDISK: candidate at %lx, %lu sectors, labelled=%d\n",
             Address, TotalSectors, mLastLabeled ? 1 : 0);

      if (Address + TotalSectors * FUXI_BLOCK_SIZE > RegionEnd) {
        // The bootloader may have described the ramdisk as several adjacent
        // descriptors; trust the BPB size rather than dropping a real volume.
        Print (L"FUXIRAMDISK: volume at %lx crosses its descriptor, using the BPB size\n", Address);
      }

      mVolumeBase  = Page;
      mVolumeBytes = TotalSectors * FUXI_BLOCK_SIZE;
      FreePool (Map);
      return TRUE;
    }
  }

  FreePool (Map);
  return FALSE;
}

//
// Publish mVolumeBase/mVolumeBytes (already set) as a read-only block device.
//
STATIC
EFI_STATUS
InstallVolume (
  VOID
  )
{
  EFI_STATUS                Status;
  EFI_HANDLE                Handle;
  EFI_DEVICE_PATH_PROTOCOL  *Path;
  VENDOR_DEVICE_PATH        Vendor;

  ZeroMem (&Vendor, sizeof (Vendor));
  Vendor.Header.Type    = HARDWARE_DEVICE_PATH;
  Vendor.Header.SubType = HW_VENDOR_DP;
  SetDevicePathNodeLength (&Vendor.Header, sizeof (VENDOR_DEVICE_PATH));
  CopyGuid (&Vendor.Guid, &gEfiCallerIdGuid);

  Path = AppendDevicePathNode (NULL, (EFI_DEVICE_PATH_PROTOCOL *)&Vendor);
  if (Path == NULL) {
    return EFI_OUT_OF_RESOURCES;
  }

  ZeroMem (&mMedia, sizeof (mMedia));
  mMedia.MediaId          = 1;
  mMedia.RemovableMedia   = FALSE;
  mMedia.MediaPresent     = TRUE;
  mMedia.LogicalPartition = FALSE;
  mMedia.ReadOnly         = TRUE;
  mMedia.WriteCaching     = FALSE;
  mMedia.BlockSize        = FUXI_BLOCK_SIZE;
  mMedia.IoAlign          = 0;
  mMedia.LastBlock        = (EFI_LBA)(mVolumeBytes / FUXI_BLOCK_SIZE) - 1;

  mBlockIo.Revision    = EFI_BLOCK_IO_PROTOCOL_REVISION;
  mBlockIo.Media       = &mMedia;
  mBlockIo.Reset       = FuxiBlockReset;
  mBlockIo.ReadBlocks  = FuxiBlockRead;
  mBlockIo.WriteBlocks = FuxiBlockWrite;
  mBlockIo.FlushBlocks = FuxiBlockFlush;

  Handle = NULL;
  Status = gBS->InstallMultipleProtocolInterfaces (
                  &Handle,
                  &gEfiBlockIoProtocolGuid,
                  &mBlockIo,
                  &gEfiDevicePathProtocolGuid,
                  Path,
                  NULL
                  );
  if (EFI_ERROR (Status)) {
    return Status;
  }

  Print (L"FUXIRAMDISK: payload at %lx, %lu KiB as a read-only block device\n",
         (UINT64)(UINTN)mVolumeBase, mVolumeBytes / 1024);
  return EFI_SUCCESS;
}

EFI_STATUS
EFIAPI
FuxiRamDiskEntry (
  IN EFI_HANDLE        ImageHandle,
  IN EFI_SYSTEM_TABLE  *SystemTable
  )
{
  UINT64  Dtb;
  UINT64  Start;
  UINT64  End;
  UINT64  TotalSectors;

  gBS->Stall (1500000);
  Print (L"FUXIRAMDISK: driver entry v2\n");

  Dtb = FindDeviceTree ();
  if (Dtb != 0) {
    if (ReadChosenInitrd ((VOID *)(UINTN)Dtb, &Start, &End)) {
      Print (L"FUXIRAMDISK: /chosen initrd %lx-%lx\n", Start, End);

      if ((Start >= 0x80000000ULL) && (End <= 0x100000000ULL) &&
          (End - Start >= 0x100000ULL) && ((End - Start) <= 0x20000000ULL) &&
          IsPayloadVolume ((UINT8 *)(UINTN)Start, &TotalSectors))
      {
        mVolumeBase  = (UINT8 *)(UINTN)Start;
        mVolumeBytes = End - Start;
        if (mVolumeBytes % FUXI_BLOCK_SIZE != 0) {
          mVolumeBytes = ((mVolumeBytes + FUXI_BLOCK_SIZE - 1) / FUXI_BLOCK_SIZE) * FUXI_BLOCK_SIZE;
        }

        if (!EFI_ERROR (InstallVolume ())) {
          gBS->Stall (2000000);
          return EFI_SUCCESS;
        }
      } else {
        Print (L"FUXIRAMDISK: /chosen initrd rejected\n");
      }
    } else {
      Print (L"FUXIRAMDISK: no initrd in /chosen\n");
    }
  } else {
    Print (L"FUXIRAMDISK: no device tree found\n");
  }

  // Memory-map scan: only non-reserved memory, so it cannot see the ABL
  // window, but keep it as a fallback for other load styles.
  if (LocatePayload ()) {
    if (!EFI_ERROR (InstallVolume ())) {
      gBS->Stall (2000000);
      return EFI_SUCCESS;
    }
  }

  // Direct probe of the reserved ABL kernel window.
  if (ScanWindowForPayload ()) {
    if (!EFI_ERROR (InstallVolume ())) {
      gBS->Stall (2000000);
      return EFI_SUCCESS;
    }
  }

  Print (L"FUXIRAMDISK: no payload found\n");
  gBS->Stall (2000000);
  return EFI_SUCCESS;
}
