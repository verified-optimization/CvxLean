import Lake
open System Lake DSL

package CvxLean

require mathlibport from git
  "https://github.com/leanprover-community/mathlib3port.git"@"ab0dfcdc6ab88c354403b531fcbfe6622bf3c252"

require ffi from "ffi"

@[default_target]
lean_lib CvxLeanTest

@[default_target]
lean_lib CvxLean
