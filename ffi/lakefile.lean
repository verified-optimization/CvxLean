import Lake
open System Lake DSL

def arbDir : FilePath := "/Users/ramonfernandezmir/Documents/PhD-code/verification-tools/arb"

package ffi {
  srcDir := "lean"
  precompileModules := true
  moreLinkArgs := #["-larb"]
  moreLeancArgs := #[]
}

@[defaultTarget]
lean_lib FFI

target leanarb.o (pkg : Package) : FilePath := do
  let oFile := pkg.buildDir / "c" / "leanarb.o"
  let srcJob ← inputFile <| pkg.dir / "c" / "leanarb.c"
  let flags := #[
    "-I" ++ (← getLeanIncludeDir).toString,
    "-O3", "-fPIC"]
  buildFileAfterDep oFile srcJob (extraDepTrace := computeHash flags) fun srcFile => do
    compileO "leanarb.c" oFile srcFile flags "gcc" -- (← getLeanc)

extern_lib libleanarb (pkg : Package) := do 
  IO.FS.createDirAll (pkg.buildDir / "lib")
  proc {
    cmd := "cp"
    args := #[
      (arbDir / "libarb.a").toString,
      (pkg.buildDir / "lib" / "libarb.a").toString ]
  }

  let name := nameToStaticLib "leanffi"
  let ffiO ← fetch <| pkg.target ``leanarb.o
  buildStaticLib (pkg.buildDir / "src" / name) #[ffiO]

@[defaultTarget]
lean_exe ffi {
  root := `Main
}
