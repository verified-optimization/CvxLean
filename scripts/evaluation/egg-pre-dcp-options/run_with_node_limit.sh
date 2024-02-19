#!/bin/bash

SCRIPT=$(readlink -f $0)
DIR=`dirname $SCRIPT`
LIM=$1
OUT=$2_$LIM.txt

cd egg-pre-dcp

EGG_PRE_DCP_NODE_LIMIT="$LIM" cargo test test_dgp:: -- --test-threads=1 --nocapture >> ../$OUT
EGG_PRE_DCP_NODE_LIMIT="$LIM" cargo test test_almost_dgp:: -- --test-threads=1 --nocapture >> ../$OUT
EGG_PRE_DCP_NODE_LIMIT="$LIM" cargo test test_dqcp:: -- --test-threads=1 --nocapture >> ../$OUT
EGG_PRE_DCP_NODE_LIMIT="$LIM" cargo test test_stanford:: -- --test-threads=1 --nocapture >> ../$OUT
EGG_PRE_DCP_NODE_LIMIT="$LIM" cargo test test_quiz:: -- --test-threads=1 --nocapture >> ../$OUT
EGG_PRE_DCP_NODE_LIMIT="$LIM" cargo test test_main_example:: -- --test-threads=1 --nocapture >> ../$OUT
