import Lake
open System Lake DSL

package CvxLean

require optlibport from git
  "https://github.com/verified-optimization/optlibport.git"@"f727fd39188f575670d6f105f34b5eca0ee67e32"

require ffi from "ffi"

@[default_target]
lean_lib CvxLeanTest

@[default_target]
lean_lib CvxLean
