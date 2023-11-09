import SciLean

#check SciLean.realToFloat
#check SciLean.isomorph `RealToFloat

section SciLeanTest

open SciLean

@[simp high]
axiom isomorphicType_equiv_zero
  : (IsomorphicType.equiv `RealToFloat) (0 : ℝ) = (0 : Float)

lemma l
  : SciLean.isomorph `RealToFloat (fun (p : Real × (Fin 2 → Real)) => Real.exp p.1 + p.2 0 ≤ 0 ∧ Real.exp p.1 + p.2 1 ≤ 0)
    =
    fun (p : Float × (Fin 2 → Float)) => Float.exp p.1 + p.2 0 ≤ 0 ∧ Float.exp p.1 + p.2 1 ≤ 0 :=
by
  conv =>
    lhs
    ftrans; ftrans; simp

-- TODO: This needs to be computable.
noncomputable def f := SciLean.isomorph `RealToFloat <|
  fun (p : Real × (Fin 2 → Real)) => Real.exp p.1 + p.2 0

end SciLeanTest
