#!/bin/bash
lake update
(cd lean_packages/mathlib && lake build)
(cd lean_packages/std && lake build)
lake build CvxLean
lake build CvxLeanTest