import Lean

/-!
Pretty-priner options to control how to show minimization problems and labels.
-/

register_option pp.optMinimization : Bool := {
  defValue := true
  group    := "pp"
  descr    := "(pretty printer) pretty-print minimization problems."
}

register_option pp.CvxLean.labels : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) display CvxLean labels."
}
