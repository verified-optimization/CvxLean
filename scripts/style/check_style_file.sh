#!/bin/bash

python3 ./.lake/packages/mathlib/scripts/lint-style.py $1 | grep -vE "ERR_COP"
