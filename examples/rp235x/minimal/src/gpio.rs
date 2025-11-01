//! RP235x GPIO helper library

use rp235x_pac::io_bank0::gpio::gpio_ctrl::FUNCSEL_A;
use rp235x_pac::{IO_BANK0, PADS_BANK0, SIO};

#[inline(always)]
pub fn led_config_output(sio: &SIO, led_pin: usize) {
    let mask = 1u32 << led_pin as u32;
    // Set GPIO as output
    sio.gpio_oe_set().write(|w| unsafe { w.bits(mask) });
}

#[inline(always)]
pub fn led_config_io(
    io_bank0: &IO_BANK0,
    pads_bank0: &PADS_BANK0,
    led_pin: usize,
) {
    pads_bank0.gpio(led_pin).modify(|_, w| {
        // Set input enable on, output disable off
        // RP2350: input enable defaults to off, so this is important!
        w.ie().set_bit();
        w.od().clear_bit();
        w
    });

    // Zero all fields apart from fsel; we want this IO to do what the peripheral tells it.
    // This doesn't affect e.g. pullup/pulldown, as these are in pad controls.
    unsafe {
        io_bank0
            .gpio(led_pin)
            .gpio_ctrl()
            .write_with_zero(|w| w.funcsel().variant(FUNCSEL_A::SIO));
    };

    pads_bank0.gpio(led_pin).modify(|_, w| {
        // RP2350: remove pad isolation now a function is wired up
        w.iso().clear_bit();
        w
    });
}

pub fn led_toggle(sio: &SIO, led_pin: usize) {
    let mask = 1u32 << led_pin as u32;
    sio.gpio_out_xor().write(|w| unsafe { w.bits(mask) });
}
