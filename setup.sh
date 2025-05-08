rustup install nightly-2024-08-07
rustup component add --toolchain nightly-2024-08-07 rustc-dev
rustup override set nightly-2024-08-07
export RUSTFLAGS="-L ~/.rustup/toolchains/nightly-2023-08-01-aarch64-apple-darwin/lib"
export LD_LIBRARY_PATH="$LD_LIBRARY_PATH:~/.rustup/toolchains/nightly-2023-08-01-aarch64-apple-darwin/lib"
cargo install --debug --locked --path . --force
cargo fdep