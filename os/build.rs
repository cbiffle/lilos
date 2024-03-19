fn main() {
    match std::env::var("TARGET").unwrap().as_str() {
        "thumbv7m-none-eabi" | "thumbv7em-none-eabi" | "thumbv7em-none-eabihf" => {
            // Turn on BASEPRI support for interrupt priority filtering.
            println!("cargo:rustc-cfg=feature=\"has-basepri\"");
            // Use native atomic RMW operations
            println!("cargo:rustc-cfg=feature=\"has-native-rmw\"");
        }
        "thumbv6m-none-eabi" => {
            // Don't turn anything on.
        }
        t => {
            panic!("unknown target {}, update build.rs", t);
        }
    }
}
