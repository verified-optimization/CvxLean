import Lean

/-!
Custom debug trace classes.
-/

open Lean Meta

initialize
  registerTraceClass `CvxLean
  registerTraceClass `CvxLean.debug
