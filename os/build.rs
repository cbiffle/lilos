// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

fn main() {
    println!(r#"cargo:rustc-check-cfg=cfg(lilos_has_basepri)"#);
    println!(r#"cargo:rustc-check-cfg=cfg(lilos_has_native_rmw)"#);

    match std::env::var("TARGET").unwrap().as_str() {
        "thumbv7m-none-eabi"
        | "thumbv7em-none-eabi"
        | "thumbv7em-none-eabihf" => {
            // Turn on BASEPRI support for interrupt priority filtering.
            println!("cargo:rustc-cfg=lilos_has_basepri");
            // Use native atomic RMW operations
            println!("cargo:rustc-cfg=lilos_has_native_rmw");
        }
        "thumbv6m-none-eabi" => {
            // Don't turn anything on.
        }
        "riscv64gc-unknown-none-elf" => {}
        "riscv32imac-unknown-none-elf" => {}
        t => {
            panic!("unknown target {}, update build.rs", t);
        }
    }
}
