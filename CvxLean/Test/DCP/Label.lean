import CvxLean.Syntax.Label

def testLabel := {** 0 ** x **}

/-
def testLabel : Nat :=
0
-/
#print testLabel

set_option pp.CvxLean.labels true

/-
def testLabel : Nat :=
{** 0 |x**}
-/
#print testLabel


#check {** Nat ** x **} × {** Nat ** y **} × {** Nat ** z**}