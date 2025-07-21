rustup install nightly-2024-08-07
rustup component add --toolchain nightly-2024-08-07 rustc-dev
rustup override set nightly-2024-08-07
SYSROOT=$(rustc --print sysroot)
LIB_PATH="$SYSROOT/lib"
export RUSTFLAGS="-L $LIB_PATH"
export LD_LIBRARY_PATH="$LD_LIBRARY_PATH:$LIB_PATH"
echo "RUSTFLAGS set to: $RUSTFLAGS"
echo "LD_LIBRARY_PATH set to: $LD_LIBRARY_PATH"
cargo install --debug --locked --path . --force
cargo fdep