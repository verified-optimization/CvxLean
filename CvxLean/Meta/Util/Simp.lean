import Lean

/-!
Custom `simp` configuration.
-/

open Lean Meta

def aggressiveSimpConfig : Simp.Config :=
  { zeta             := true
    beta             := true
    eta              := true
    iota             := true
    proj             := true
    decide           := true
    arith            := true
    dsimp            := true
    unfoldPartialApp := true
    etaStruct        := .all }
