import CvxLean.Syntax.Label

def testLabel := {** 0 ** x **}

#print testLabel

set_option pp.CvxLean.labels true

#print testLabel

#check {** Nat ** x **} × {** Nat ** y **} × {** Nat ** z**}
