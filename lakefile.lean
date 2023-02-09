import Lake
open System Lake DSL

package CvxLean

require mathlibport from git
  "https://github.com/leanprover-community/mathlib3port.git"@"e1ef11de97cea5fcd3772993509fa5bd19a2521d"

require ffi from "ffi"

@[default_target]
lean_lib CvxLeanTest

@[default_target]
lean_lib CvxLean
