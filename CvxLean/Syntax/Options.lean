import Lean

/-!
Pretty-priner options to control how to show minimization problems and labels.
-/

namespace CvxLean

register_option pp.optMinimization : Bool := {
  defValue := true
  group    := "pp"
  descr    := "(pretty printer) pretty-print minimization problems."
}

register_option pp.labels : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) display CvxLean labels."
}

end CvxLean
