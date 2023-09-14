import Lake
open System Lake DSL

package CvxLean

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ 
  "c35ba47375c4f80f3ba26a7301b17eadfac2562c"

-- meta if get_config? env = some "dev" then
-- require «doc-gen4» from git 
--   "https://github.com/leanprover/doc-gen4" @ "main"

@[default_target]
lean_lib CvxLeanTest

@[default_target]
lean_lib CvxLean

def compileCargo (name : String) (manifestFile : FilePath)
 (cargo : FilePath := "cargo") : LogIO Unit := do
  logInfo s!"Creating {name}"
  proc {
    cmd := cargo.toString
    args := #["build", "--release", "--manifest-path", manifestFile.toString]
  }

def buildCargo (targetFile : FilePath) (manifestFile : FilePath) 
(targetDest : FilePath) (oFileJobs : Array (BuildJob FilePath)) :
SchedulerM (BuildJob FilePath) :=
  let name := targetFile.fileName.getD targetFile.toString
  buildFileAfterDepArray targetFile oFileJobs fun _ => do
    compileCargo name manifestFile
    createParentDirs targetDest
    proc {
      cmd := "cp"
      args := #[targetFile.toString, targetDest.toString]
    }

@[default_target]
target EggConvexify (pkg) : FilePath := do
  let buildDir := pkg.dir / "rewriter"
  let binFile := buildDir / "target" / "release" / "egg-convexify"
  let dest := buildDir / "utils" / "egg-convexify"
  let manifestFile := buildDir / "Cargo.toml"
  buildCargo binFile manifestFile dest #[]

script EggClean := do
  let targetDir : FilePath := "." / "rewriter" / "target"
  let utilsDir : FilePath  := "." / "rewriter" / "utils"
  let out ← 
  IO.Process.output { 
    cmd := "rm"
    args := #["-rf", targetDir.toString]
  } *> 
  IO.Process.output { 
    cmd := "rm"
    args := #["-rf", utilsDir.toString]
  }
  pure out.exitCode
