import Lake
open System Lake DSL

package CvxLean

require optlibport from git
  "https://github.com/verified-optimization/optlibport.git"@"d106243410275d88bece3c6bedcbe158779e2164"

require arb from "arb"

lean_lib CvxLeanTest

@[defaultTarget]
lean_lib CvxLean
