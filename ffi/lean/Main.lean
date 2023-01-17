import FFI
import Std.Data.Rat

open Std Rat

def main : IO Unit := do 
  let prec : Nat := 10
  let n : Nat := 2
  let m : Nat := 1

  let a11 := [1.0 ± 0.00001]
  let a12 := [2.0 ± 0.00001]
  let a21 := [3.0 ± 0.00001]
  let a22 := [4.0 ± 0.00001]
  let A := 
    #[#[a11, a12], 
      #[a21, a22]]

  let b1 := [5.0 ± 0.00001]
  let b2 := [6.0 ± 0.00001]
  let B := 
    #[#[b1], 
      #[b2]]

  let t1 := [-4.0 ± 0.00001]
  let t2 := [ 4.5 ± 0.00001]
  let T := 
    #[#[t1], 
      #[t2]]

  let X := Ball.linearSystem prec n m A B T

  IO.println s!"X : {X}"

#eval timeit "as" main
