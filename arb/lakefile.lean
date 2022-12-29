import Lake
open System Lake DSL

package arb {
  srcDir := "lean"
  precompileModules := true
}

lean_lib Arb

target arb.o (pkg : Package) : FilePath := do
  let oFile := pkg.buildDir / "c" / "arb.o"
  let srcJob ← inputFile <| pkg.dir / "c" / "arb.c"
  let flags := #[
      "-I", (← getLeanIncludeDir).toString,
      "-fPIC", "-larb", "-lflint", "-lmpfr", "-lgmp"]
  buildFileAfterDep oFile srcJob (extraDepTrace := computeHash flags) fun srcFile => do
    compileO "arb.c" oFile srcFile flags "gcc"

extern_lib libleanarb (pkg : Package) := do 
  let name := nameToStaticLib "leanarb"
  let arbO ← fetch <| pkg.target ``arb.o
  buildStaticLib (pkg.buildDir / "c" / name) #[arbO]