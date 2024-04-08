#!/bin/bash

cd egg-pre-dcp

RUSTFLAGS="--cfg stop_on_success" cargo test test_dgp::test_gp4 -- --test-threads=1 --nocapture
RUSTFLAGS="--cfg stop_on_success" cargo test test_dgp::test_gp5 -- --test-threads=1 --nocapture
RUSTFLAGS="--cfg stop_on_success" cargo test test_dgp::test_gp8 -- --test-threads=1 --nocapture
RUSTFLAGS="--cfg stop_on_success" cargo test test_dgp::test_gp9 -- --test-threads=1 --nocapture
RUSTFLAGS="--cfg stop_on_success" cargo test test_almost_dgp::test_agp3 -- --test-threads=1 --nocapture
RUSTFLAGS="--cfg stop_on_success" cargo test test_dqcp::test_qcp4 -- --test-threads=1 --nocapture
RUSTFLAGS="--cfg stop_on_success" cargo test test_stanford::test_stan3 -- --test-threads=1 --nocapture
RUSTFLAGS="--cfg stop_on_success" cargo test test_stanford::test_stan4 -- --test-threads=1 --nocapture
RUSTFLAGS="--cfg stop_on_success" cargo test test_quiz::test_quiz9 -- --test-threads=1 --nocapture
RUSTFLAGS="--cfg stop_on_success" cargo test test_main_example::test_main_example -- --test-threads=1 --nocapture
