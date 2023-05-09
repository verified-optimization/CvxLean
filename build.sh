#!/bin/bash
lake update
(cd lake-packages/mathlib && lake build)
(cd lake-packages/std && lake build)
lake build CvxLean
lake build CvxLeanTest