import Lake
open System Lake DSL

package CvxLean

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"@"68b21e12e6d612e77f34febea2e00a9358ce2f76"

@[default_target]
lean_lib CvxLeanTest

@[default_target]
lean_lib CvxLean
