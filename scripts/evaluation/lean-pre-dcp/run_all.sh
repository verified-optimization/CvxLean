#!/bin/bash

OUT=$1

mkdir -p ./evaluation/data/$OUT

./scripts/evaluation/lean-pre-dcp/run.sh ./evaluation/data/$OUT/lean_pre_dcp_test_out_1.txt;
./scripts/evaluation/lean-pre-dcp/run.sh ./evaluation/data/$OUT/lean_pre_dcp_test_out_2.txt;
./scripts/evaluation/lean-pre-dcp/run.sh ./evaluation/data/$OUT/lean_pre_dcp_test_out_3.txt;
./scripts/evaluation/lean-pre-dcp/run.sh ./evaluation/data/$OUT/lean_pre_dcp_test_out_4.txt; 
./scripts/evaluation/lean-pre-dcp/run.sh ./evaluation/data/$OUT/lean_pre_dcp_test_out_5.txt 
