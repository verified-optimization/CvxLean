import Lean 
import FFI 

open Lean

def main : IO Unit := do 
  let r := sqrtBounds (mkRat (Int.ofNat $ 10 ^ 10) 1)
  IO.println s!"{r}"

#eval main
