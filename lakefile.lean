import Lake
open System Lake DSL

package CvxLean

require mathlibport from git
  "https://github.com/leanprover-community/mathlib3port.git"@"db402ab7e576d998c8cbc97b0d1897c712f34fb5"

require ffi from "ffi"

@[default_target]
lean_lib CvxLeanTest

@[default_target]
lean_lib CvxLean
