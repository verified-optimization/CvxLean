#!/bin/bash

RUSTFLAGS="--cfg stop_on_success"  cargo build --release --manifest-path egg-pre-dcp/Cargo.toml
mkdir -p egg-pre-dcp/utils
cp egg-pre-dcp/target/release/egg-pre-dcp egg-pre-dcp/utils/egg-pre-dcp
