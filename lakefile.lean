import Lake
open System Lake DSL

package CvxLean

require mathlibport from git
  "https://github.com/leanprover-community/mathlib3port.git"@"f4e5dfe2aa778b4cc42620b6b58442504348d20d"

require ffi from "ffi"

@[default_target]
lean_lib CvxLeanTest

@[default_target]
lean_lib CvxLean
