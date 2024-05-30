RUSTFLAGS="-C code-model=medium -C relocation-model=static -C link-arg=-T$(realpath $(dirname $0))/memory.x -C link-arg=-Tlink.x" cargo +nightly -Z build-std $*
