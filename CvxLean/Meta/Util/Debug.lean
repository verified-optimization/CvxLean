import Lean

/-!
Custom debug trace classes.
-/

open Lean Meta

builtin_initialize
  registerTraceClass `CvxLean
  registerTraceClass `CvxLean.debug
