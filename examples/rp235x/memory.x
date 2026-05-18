MEMORY {
  /* NOTE K = KiB = 1024 bytes */
  FLASH  (rx)  : ORIGIN = 0x10000000, LENGTH = 4M
  RAM    (rwx) : ORIGIN = 0x20000000, LENGTH = 520K
}

SECTIONS {
    /* ### Boot ROM info
     *
     * Goes after .vector_table, to keep it in the first 4K of flash
     * where the Boot ROM (and picotool) can find it
     */
    .image_def : ALIGN(4)
    {
        KEEP(*(.image_def));
    } > FLASH

} INSERT AFTER .vector_table;

/* move .text to start /after/ the boot info */
_stext = ADDR(.image_def) + SIZEOF(.image_def);
