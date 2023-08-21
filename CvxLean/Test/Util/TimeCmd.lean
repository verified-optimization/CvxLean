import Lean

open Lean Elab Command

syntax (name := time_cmd) "time_cmd " command : command

@[command_elab «time_cmd»]
def evalTimeCmd : CommandElab := fun stx => match stx with
| `(time_cmd $cmd) => do
  let before ← BaseIO.toIO IO.monoMsNow
  elabCommand cmd
  let after ← BaseIO.toIO IO.monoMsNow
  let diff := after - before
  IO.println s!"{diff} ms"
| _ => throwUnsupportedSyntax
