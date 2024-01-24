#!/bin/bash
lake update
lake exe cache get
lake run EggClean
lake build EggPreDCP
lake build CvxLean
