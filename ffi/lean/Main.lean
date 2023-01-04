import Lean 
import FFI 

open Lean

def main : IO Unit := do 
  let r := sqrtBounds (mkRat 100 101)
  IO.println s!"{r}"

#eval main
