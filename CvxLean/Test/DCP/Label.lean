import CvxLean.Syntax.Label

/-!
Making labels explicitly, and printing them.

### TODO

* This does show what is expected because `pp.labels` had to be disabled for `doc-gen` to work.
-/

def testLabel := {** 0 ** x **}

#print testLabel

--set_option pp.labels true

#print testLabel

#check {** Nat ** x **} × {** Nat ** y **} × {** Nat ** z**}
