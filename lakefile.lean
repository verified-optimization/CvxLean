import Lake

open System Lake DSL

package CvxLean where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @
  "efad919b6687484ee26ac7c65a29c972d2112b8d"

meta if get_config? env = some "scilean" then
require scilean from git
  "https://github.com/verified-optimization/SciLean" @
  "master"

meta if get_config? doc = some "on" then
require «doc-gen4» from git
  "https://github.com/verified-optimization/doc-gen4.git" @
  "main"

@[default_target]
lean_lib CvxLean

@[default_target]
lean_lib CvxLeanTest

def compileCargo (name : String) (manifestFile : FilePath) (cargo : FilePath := "cargo")
    (env : Array (String × Option String)) : LogIO Unit := do
  logInfo s!"Creating {name}"
  proc {
    env := env
    cmd := cargo.toString
    args := #["build", "--release", "--manifest-path", manifestFile.toString]
  }

def buildCargo (targetFile : FilePath) (manifestFile : FilePath) (targetDest : FilePath)
    (oFileJobs : Array (BuildJob FilePath)) (stopOnSuccess : Bool) :
    SpawnM (BuildJob FilePath) :=
  let name := targetFile.fileName.getD targetFile.toString
  buildFileAfterDepArray targetFile oFileJobs fun _ => do
    let env := if stopOnSuccess then #[("RUSTFLAGS", some "--cfg stop_on_success")] else #[]
    compileCargo name manifestFile (env := env)
    createParentDirs targetDest
    proc {
      cmd := "cp"
      args := #[targetFile.toString, targetDest.toString]
    }

target EggPreDCP (pkg) : FilePath := do
  let buildDir := pkg.dir / "egg-pre-dcp"
  let binFile := buildDir / "target" / "release" / "egg-pre-dcp"
  let dest := buildDir / "utils" / "egg-pre-dcp"
  let manifestFile := buildDir / "Cargo.toml"
  buildCargo binFile manifestFile dest #[] false

target EggPreDCPStopOnSuccess (pkg) : FilePath := do
  let buildDir := pkg.dir / "egg-pre-dcp"
  let binFile := buildDir / "target" / "release" / "egg-pre-dcp"
  let dest := buildDir / "utils" / "egg-pre-dcp"
  let manifestFile := buildDir / "Cargo.toml"
  buildCargo binFile manifestFile dest #[] true

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
