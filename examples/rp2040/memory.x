MEMORY {
  /* NOTE K = KiB = 1024 bytes */
  BOOT   (rx)  : ORIGIN = 0x10000000, LENGTH = 256
  FLASH  (rx)  : ORIGIN = 0x10000100, LENGTH = 2M - 256
  RAM    (rwx) : ORIGIN = 0x20000000, LENGTH = 264K
}

SECTIONS {
    .boot_loader : {
        KEEP(*(.boot_loader*));
    } >BOOT
} INSERT BEFORE .text;
