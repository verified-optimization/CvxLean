import Lean 
import FFI

open Lean

def main : IO Unit := do 
  -- for i in [0:2] do
  --   let mid := mkRat 250000000 (i + 1)
  --   let rad := mkRat 1 100000
  --   let ball := Ball.mk mid rad
  --   IO.println s!"ball : {ball}"
  --   let ballSqrt := Ball.sqrt 10 ball
  --   IO.println s!"ballSqrt : {ballSqrt}"
  let n : Nat := 2
  let m : Nat := 1

  let a11 := mkRat 1 1
  let a12 := mkRat 2 1
  let a21 := mkRat 3 1
  let a22 := mkRat 4 1
  let ba11 := Ball.mk a11 (mkRat 1 100000)
  let ba12 := Ball.mk a12 (mkRat 1 100000)
  let ba21 := Ball.mk a21 (mkRat 1 100000)
  let ba22 := Ball.mk a22 (mkRat 1 100000)
  let A : Array (Array (Ball Rat)) := #[#[ba11, ba12], #[ba21, ba22]]

  let b1 := mkRat 5 1
  let b2 := mkRat 6 1
  let bb1 := Ball.mk b1 (mkRat 1 100000)
  let bb2 := Ball.mk b2 (mkRat 1 100000)
  let B := #[#[bb1], #[bb2]]

  let t1 := mkRat (-4) 1
  let t2 := mkRat 9 2
  let bt1 := Ball.mk t1 (mkRat 1 100000)
  let bt2 := Ball.mk t2 (mkRat 1 100000)
  let T := #[#[bt1], #[bt2]]

  let X : Array (Array (Ball Rat)) := Ball.linearSystem 100 n m A B T
  IO.println s!"A : {A}"
  IO.println s!"X : {X}"

#eval timeit "as" main
