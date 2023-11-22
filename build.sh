#!/bin/bash
lake update
lake exe cache get
lake build EggConvexify
lake build CvxLean
lake build CvxLeanTest