import Lake
open System Lake DSL

package CvxLean

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"@"62e4694"

@[default_target]
lean_lib CvxLeanTest

@[default_target]
lean_lib CvxLean
