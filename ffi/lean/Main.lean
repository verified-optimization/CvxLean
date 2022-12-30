import Lean 
import FFI 

open Lean

def main : IO Unit := do 
  let r := sqrtBounds (mkRat 1 3)
  IO.println s!"{r}"
  
