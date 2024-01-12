#!/bin/bash
touch solver/problem.cbf
touch solver/problem.sol
lake update
lake exe cache get
lake run EggClean
lake build EggConvexify
lake build CvxLean
