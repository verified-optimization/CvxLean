import Lake
open System Lake DSL

def arbDir : FilePath := "/Users/ramonfernandezmir/Documents/PhD-code/verification-tools/arb"
def flintDir : FilePath := "/Users/ramonfernandezmir/Documents/PhD-code/verification-tools/flint2"

package ffi {
  srcDir := "lean"
  precompileModules := true
  moreLinkArgs := #[
    "-L" ++ arbDir.toString,
    "-I" ++ arbDir.toString,
    "-larb",
    "-L" ++ arbDir.toString,
    "-I" ++ arbDir.toString,
    "-lflint", "-lmpfr", "-lgmp",
    "-lstdc++"]
}

@[defaultTarget]
lean_lib FFI

target leanarb.o (pkg : Package) : FilePath := do
  let oFile := pkg.buildDir / "c" / "leanarb.o"
  let srcJob ← inputFile <| pkg.dir / "c" / "leanarb.c"
  let flags := #[
    "-I" ++ (← getLeanIncludeDir).toString, 
    "-I" ++ arbDir.toString,
    "-O3", "-fPIC"]
  buildFileAfterDep oFile srcJob (extraDepTrace := computeHash flags) fun srcFile => do
    compileO "leanarb.c" oFile srcFile flags "clang"

extern_lib libleanarb (pkg : Package) := do 
  -- let name := nameToStaticLib "leanffi"
  -- let libFile := pkg.buildDir / "c" / name
  -- let arbO ← fetch <| pkg.target ``ffi.o
  -- let linkJobs := #[arbO]
  -- let linkArgs := #[
  --   "-L/usr/local/lib", 
  --   "-lstdc++",
  --   "-larb", "-lflint", "-lmpfr", "-lgmp", "-lSystem"]
  -- let name := libFile.fileName.getD libFile.toString
  -- buildFileAfterDepArray libFile linkJobs
  --   (extraDepTrace := computeHash linkArgs) fun links => do
  --     compileSharedLib name libFile (links.map toString ++ linkArgs) (← getLeanc)
  IO.FS.createDirAll (pkg.buildDir / "lib")
  proc {
    cmd := "cp"
    args := #[
      (arbDir / "libarb.a").toString,
      (pkg.buildDir / "lib" / "libarb.a").toString ]
  }
  proc {
    cmd := "cp"
    args := #[
      (flintDir / "libflint.a").toString,
      (pkg.buildDir / "lib" / "libflint.a").toString ]
  }

  let name := nameToStaticLib "leanffi"
  let ffiO ← fetch <| pkg.target ``leanarb.o
  let libFile := pkg.buildDir / "lib" / name
  let linkJobs := #[ffiO]
  let linkArgs := #[
    "-L" ++ arbDir.toString,
    "-I" ++ arbDir.toString,
    "-larb",
    "-L" ++ flintDir.toString,
    "-I" ++ flintDir.toString,
    "-lflint", 
    "-lmpfr", 
    "-lgmp"]
  --buildLeanSharedLib (pkg.buildDir / "lib" / name) #[ffiO]
  let name := libFile.fileName.getD libFile.toString
  buildFileAfterDepArray libFile linkJobs
    (extraDepTrace := computeHash linkArgs) fun links => do
      compileSharedLib name libFile (links.map toString ++ linkArgs) (← getLeanc)

@[defaultTarget]
lean_exe ffi {
  root := `Main
}
