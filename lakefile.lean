import Lake
open System Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @
  "1250aa83953a2c7d5819cebea08ad7fdef997d49"

meta if get_config? env = some "dev" then
require scilean from git
  "https://github.com/verified-optimization/SciLean" @
  "master"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/verified-optimization/doc-gen4" @
  "main"

package CvxLean

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
target EggPreDCP (pkg) : FilePath := do
  let buildDir := pkg.dir / "egg-pre-dcp"
  let binFile := buildDir / "target" / "release" / "egg-pre-dcp"
  let dest := buildDir / "utils" / "egg-pre-dcp"
  let manifestFile := buildDir / "Cargo.toml"
  buildCargo binFile manifestFile dest #[]

script EggClean := do
  let targetDir : FilePath := "." / "egg-pre-dcp" / "target"
  let utilsDir : FilePath  := "." / "egg-pre-dcp" / "utils"
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
