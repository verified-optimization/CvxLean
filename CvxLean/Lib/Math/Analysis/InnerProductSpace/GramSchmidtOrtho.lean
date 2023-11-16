import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

section GramSchmidt

variable (𝕜 : Type _) {E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι : Type _} [LinearOrder ι] [LocallyFiniteOrderBot ι] [IsWellOrder ι (· < · : ι → ι → Prop)]

attribute [instance] IsWellOrder.toHasWellFounded

local notation "⟪" x "," y "⟫" => @inner 𝕜 _ _ x y

lemma repr_gramSchmidt_diagonal {i : ι} (b : Basis ι 𝕜 E) :
  b.repr (gramSchmidt 𝕜 b i) i = 1 := by 
  rw [gramSchmidt_def, LinearEquiv.map_sub, Finsupp.sub_apply, Basis.repr_self,
    Finsupp.single_eq_same, sub_eq_self, map_sum, Finsupp.coe_finset_sum,
    Finset.sum_apply, Finset.sum_eq_zero]
  intros j hj
  rw [Finset.mem_Iio] at hj
  simp [orthogonalProjection_singleton, gramSchmidt_triangular hj]

end GramSchmidt
