#!/bin/bash

# There are 6 examples with shorter explanations on interative mode. We expected stop-on-success to 
# yield shorter explanations. We isolate them here to understand what is happening.

cd egg-pre-dcp

# This is the smallest.

cargo test test_stanford::test_stan2 -- --exact --test-threads=1 --nocapture
RUSTFLAGS="--cfg stop_on_success" cargo test test_stanford::test_stan2 -- --exact --test-threads=1 --nocapture

# This is the largest.

# cargo test test_dgp::test_gp6 -- --exact --test-threads=1 --nocapture
# RUSTFLAGS="--cfg stop_on_success" cargo test test_dgp::test_gp6 -- --exact --test-threads=1 --nocapture
