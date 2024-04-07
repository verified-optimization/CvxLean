#!/bin/bash

OUT=$1

mkdir -p ./evaluation/data/$OUT

./scripts/evaluation/egg-pre-dcp-options/run_stop_on_success.sh ./scripts/evaluation/data/$OUT/stop_on_success.txt;
./scripts/evaluation/egg-pre-dcp-options/run_iterative.sh ./scripts/evaluation/data/$OUT/iterative.txt;
