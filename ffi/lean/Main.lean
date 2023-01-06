import Lean 
import FFI

open Lean

def main : IO Unit := do 
  for i in [0:2] do
    let mid := mkRat 250000000 (i + 1)
    let rad := mkRat 1 100000
    let ball := Ball.mk mid rad
    IO.println s!"ball : {ball}"
    let ballSqrt := Ball.sqrt 10 ball
    IO.println s!"ballSqrt : {ballSqrt}"

#eval timeit "as" main
