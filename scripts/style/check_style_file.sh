#!/bin/bash

errors=$(python3 ./.lake/packages/mathlib/scripts/lint-style.py $1 | grep -vE "ERR_COP")

if [ -z "$errors" ]; then
  exit 0
else
  echo "$errors"
  exit 1
fi
