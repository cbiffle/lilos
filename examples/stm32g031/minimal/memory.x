MEMORY
{
  /* NOTE K = KiBi = 1024 bytes */
  FLASH  (rx)  : ORIGIN = 0x08000000, LENGTH = 64K 
  RAM    (rwx) : ORIGIN = 0x20000000, LENGTH = 8K
}
