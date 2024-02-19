#!/bin/bash

OUT=$1

mkdir -p ./evaluation/data/$OUT

./evaluation/egg-pre-dcp-options/run_stop_on_success.sh ./evaluation/data/$OUT/stop_on_success.txt;
./evaluation/egg-pre-dcp-options/run_iterative.sh ./evaluation/data/$OUT/iterative.txt;
