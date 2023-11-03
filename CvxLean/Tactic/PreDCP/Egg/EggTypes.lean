import Lean
import CvxLean.Tactic.DCP.Tree

def EggTree := CvxLean.Tree String String

structure EggMinimization where
  objFun : String
  constrs : List (String × String)

/-- Corresponds to the domain structure. -/
structure EggDomain where
  hi : String
  lo : String
  hi_open : String
  lo_open : String
