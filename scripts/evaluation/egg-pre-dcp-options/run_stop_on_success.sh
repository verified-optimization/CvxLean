#!/bin/bash

SCRIPT=$(readlink -f $0)
DIR=`dirname $SCRIPT`
OUT=$1

cd egg-pre-dcp

RUSTFLAGS="--cfg stop_on_success" cargo test test_dgp:: -- --test-threads=1 --nocapture >> ../$OUT
RUSTFLAGS="--cfg stop_on_success" cargo test test_almost_dgp:: -- --test-threads=1 --nocapture >> ../$OUT
RUSTFLAGS="--cfg stop_on_success" cargo test test_dqcp:: -- --test-threads=1 --nocapture >> ../$OUT
RUSTFLAGS="--cfg stop_on_success" cargo test test_stanford:: -- --test-threads=1 --nocapture >> ../$OUT
RUSTFLAGS="--cfg stop_on_success" cargo test test_quiz:: -- --test-threads=1 --nocapture >> ../$OUT
RUSTFLAGS="--cfg stop_on_success" cargo test test_main_example:: -- --test-threads=1 --nocapture >> ../$OUT
