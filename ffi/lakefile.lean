import Lake
open System Lake DSL

def arbDir : FilePath := "/Users/ramonfernandezmir/Documents/PhD-code/verification-tools/arb"
def flintDir : FilePath := "/Users/ramonfernandezmir/Documents/PhD-code/verification-tools/flint2"

package ffi {
  srcDir := "lean"
  precompileModules := true
  moreLinkArgs := #["-larb", "-lflint"]
  moreLeancArgs := #[]
}

@[default_target]
lean_lib FFI where 
  precompileModules := true

target leanarb.o (pkg : Package) : FilePath := do
  let oFile := pkg.buildDir / "c" / "leanarb.o"
  let srcJob ← inputFile <| pkg.dir / "c" / "leanarb.c"
  let flags := #["-I" ++ (← getLeanIncludeDir).toString, "-fPIC"]
  buildFileAfterDep oFile srcJob (extraDepTrace := computeHash flags) fun srcFile => do
    compileO "leanarb.c" oFile srcFile flags "gcc" -- (← getLeanc)

extern_lib libleanarb (pkg : Package) := do 
  let name := nameToStaticLib "leanarb"
  let ffiO ← fetch <| pkg.target ``leanarb.o
  buildStaticLib (pkg.buildDir / defaultLibDir / name) #[ffiO]

@[default_target]
lean_exe ffi {
  root := `Main
}
