#!/bin/bash

OUT=$1

rm -rf .lake/build/lib/CvxLean/Test/PreDCP

TMP=$(cat CvxLeanTest.lean)

L=("Unit" "MainExample" "DGP" "AlmostDGP" "DQCP" "Quiz" "Stanford")
for s in ${L[@]}; do
  echo "import CvxLean.Test.PreDCP.$s" > CvxLeanTest.lean
  lake build CvxLeanTest >> $OUT
done

echo $TMP > CvxLeanTest.lean
