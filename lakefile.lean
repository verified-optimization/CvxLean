import Lake
open System Lake DSL

package CvxLean

require optlibport from git
  "https://github.com/verified-optimization/optlibport.git"@"495dc2b4a6202546569c2a841e3129f388ce2511"

require ffi from "ffi"

@[default_target]
lean_lib CvxLeanTest

@[default_target]
lean_lib CvxLean
