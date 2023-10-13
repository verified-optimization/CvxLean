import Lake
open Lake DSL

package «workaround» where
  -- add package configuration options here

lean_lib «Workaround» where
  -- add library configuration options here

@[default_target]
lean_exe «workaround» where
  root := `Main
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"
require «CvxLean» from ".."
