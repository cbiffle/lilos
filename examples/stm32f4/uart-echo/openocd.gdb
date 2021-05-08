target extended-remote :3333

# print demangled symbols
set print asm-demangle on

# detect unhandled exceptions, hard faults and panics
break DefaultHandler
break UserHardFault
break rust_begin_unwind

monitor arm semihosting enable

# send captured ITM to the file itm.fifo
# (the microcontroller SWO pin must be connected to the programmer SWO pin)
# final number must match the core clock frequency at the time you want to
# record output
monitor tpiu config internal itm.txt uart off 160000000

# # OR: make the microcontroller SWO pin output compatible with UART (8N1)
# # 16000000 must match the core clock frequency
# # 2000000 is the frequency of the SWO pin
# monitor tpiu config external uart off 16000000 2000000

# enable ITM port 0
monitor itm port 0 on

load
