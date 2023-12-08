import CvxLean.Tactic.DCP.Atoms
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Cones
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Le
import CvxLean.Tactic.DCP.AtomLibrary.Fns.VecCons
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Add
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Sub
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Mul

namespace CvxLean

open Real

declare_atom powOne [affine] (x : ℝ)+ : x ^ (1 : ℝ) :=
bconditions
homogenity by
  simp
additivity by
  simp
optimality by
  intros _ h
  simp [h]

declare_atom powNegOne [convex] (x : ℝ)- : x ^ (-1) :=
vconditions
  (hx : 0 < x)
implementationVars (t : ℝ)
implementationObjective (t)
implementationConstraints
  (c1 : soCone (t + x) ![t - x, 2])
  (c2 : 0 ≤ t)
  (c3 : 0 ≤ x)
solution
  (t := x ^ (-1))
solutionEqualsAtom rfl
feasibility
  (c1 : by
    have hxnn := le_of_lt hx
    have hinv : 0 < x ^ (-1) := by rwa [rpow_neg_one, inv_pos]
    have hinvnn := le_of_lt hinv
    rw [soCone_add_sub_two_of_nonneg hinvnn hxnn, rpow_neg_one]
    field_simp)
  (c2 : by
    have hinv : 0 < x ^ (-1) := by rwa [rpow_neg_one, inv_pos]
    exact le_of_lt hinv)
  (c3 : le_of_lt hx)
optimality by
  intros y hy
  rw [soCone_add_sub_two_of_nonneg c2 c3] at c1
  have hxpos : 0 < x := by
    cases (lt_or_eq_of_le c3) with
    | inl h => exact h
    | inr h => rw [←h] at c1; linarith
  have hypos := lt_of_lt_of_le hxpos hy
  rw [rpow_neg_one, inv_eq_one_div, div_le_iff hypos]
  apply le_trans c1
  apply mul_le_mul_of_nonneg_left hy c2
vconditionElimination
  (hx : by
    -- TODO: some repetition here.
    intros y hy
    rw [soCone_add_sub_two_of_nonneg c2 c3] at c1
    cases (lt_or_eq_of_le c3) with
      | inl h => linarith
      | inr h => rw [←h] at c1; linarith)

-- NOTE(RFM): It is not straightforward to express it in terms of x ^ (-1) and
-- x ^ 2 because of vconditions.
declare_atom powNegTwo [convex] (x : ℝ)- : x ^ (-2) :=
vconditions
  (hx : 0 < x)
implementationVars (t₀ : ℝ) (t₁ : ℝ)
implementationObjective (t₀)
implementationConstraints
  (c1 : soCone (x + t₁) ![x - t₁, 2])
  (c2 : soCone (t₀ + 1) ![t₀ - 1, 2 * t₁])
  (c3 : 0 ≤ t₀)
  (c4 : 0 ≤ t₁)
  (c5 : 0 ≤ x)
solution
  (t₀ := x ^ (-2)) (t₁ := x ^ (-1))
solutionEqualsAtom rfl
feasibility
  (c1 : by
    dsimp
    have hxnn := le_of_lt hx
    have hinv : 0 < x ^ (-1) := by rwa [rpow_neg_one, inv_pos]
    have hinvnn := le_of_lt hinv
    rw [soCone_add_sub_two_of_nonneg hxnn hinvnn, rpow_neg_one]
    field_simp)
  (c2 : by
    dsimp
    have hxnn := le_of_lt hx
    have hinv : 0 < x ^ (-1) := by rwa [rpow_neg_one, inv_pos]
    have hxneg2 : 0 < x ^ (-2) := by
      rw [(by norm_num : (-2 : ℝ) = (-1) + (-1)), rpow_add hx]
      apply mul_pos <;> exact hinv
    have hxneg2nn := le_of_lt hxneg2
    have h1nn : 0 ≤ (1 : ℝ) := by norm_num
    rw [soCone_add_sub_two_mul_of_nonneg (x ^ (-1)) hxneg2nn h1nn]
    rw [←rpow_mul hxnn]
    field_simp)
  (c3 : by
    dsimp
    rw [rpow_neg (le_of_lt hx), inv_nonneg, rpow_two]
    exact sq_nonneg x)
  (c4 : by
    dsimp
    rw [rpow_neg (le_of_lt hx), inv_nonneg, rpow_one]
    exact le_of_lt hx)
  (c5 : le_of_lt hx)
optimality by
  intros y hy
  have h1nn : 0 ≤ (1 : ℝ) := by norm_num
  rw [soCone_add_sub_two_of_nonneg c5 c4] at c1
  rw [soCone_add_sub_two_mul_of_nonneg t₁ c3 h1nn] at c2
  -- Establish basic positivity facts.
  have hxpos : 0 < x := by
    cases (lt_or_eq_of_le c5) with
    | inl h => exact h
    | inr h => rw [←h] at c1; linarith
  have hypos := lt_of_lt_of_le hxpos hy
  have hynn := le_of_lt hypos
  have hy2pos : 0 < y ^ (2 : ℝ):= by
    rw [rpow_two]
    exact pow_two_pos_of_ne_zero y (ne_of_gt hypos)
  have ht₁pos : 0 < t₁ := by
    cases (lt_or_eq_of_le c4) with
    | inl h => exact h
    | inr h => rw [←h] at c1; linarith
  have ht₁2pos : 0 < t₁ ^ (2 : ℝ) := by
    rw [rpow_two]
    exact pow_two_pos_of_ne_zero t₁ (ne_of_gt ht₁pos)
  have ht₁inv : 0 < t₁ ^ (-1) := by rwa [rpow_neg_one, inv_pos]
  have ht₀pos : 0 < t₀ := by
    cases (lt_or_eq_of_le c3) with
    | inl h => exact h
    | inr h => rw [←h] at c2; linarith
  -- Combine c1 and c2 appropriately to get t₀ ^ (-1) ≤ y ^ 2.
  have ht₁invx : t₁ ^ (-1) ≤ x := by
    rw [rpow_neg c4, rpow_one]
    rwa [←div_le_iff ht₁pos, ←inv_eq_one_div] at c1
  have ht₁invy : t₁ ^ (-1) ≤ y := le_trans ht₁invx hy
  have ht₁invnn := le_of_lt ht₁inv
  have ht₁neg2y2 : t₁ ^ (-2) ≤ y ^ (2 : ℝ) := by
    have h := mul_le_mul ht₁invy ht₁invy ht₁invnn hynn
    rw [←rpow_add ht₁pos] at h
    norm_num at h
    rw [←pow_two, ←rpow_two] at h
    exact h
  have ht₀invt₁neg2 : t₀ ^ (-1) ≤ t₁ ^ (-2) := by
    rw [mul_one] at c2
    have ht₀1 : 0 < t₀ ^ (1 : ℝ) := by rwa [rpow_one]
    rw [rpow_neg c3, rpow_neg c4, inv_le_inv ht₀1 ht₁2pos, rpow_one]
    exact c2
  have ht₀invy2 := le_trans ht₀invt₁neg2 ht₁neg2y2
  -- Fit inequality to goal.
  rw [rpow_neg hynn, inv_eq_one_div, div_le_iff hy2pos]
  rw [mul_comm, ←div_le_iff ht₀pos, ←inv_eq_one_div]
  rw [←rpow_one t₀, ←rpow_neg c3]
  exact ht₀invy2
vconditionElimination
  (hx : by
    -- TODO: some repetition here.
    intros y hy
    have h1nn : 0 ≤ (1 : ℝ) := by norm_num
    rw [soCone_add_sub_two_of_nonneg c5 c4] at c1
    rw [soCone_add_sub_two_mul_of_nonneg t₁ c3 h1nn] at c2
    have hxpos : 0 < x := by
      cases (lt_or_eq_of_le c5) with
      | inl h => exact h
      | inr h => rw [←h] at c1; linarith
    exact lt_of_lt_of_le hxpos hy)

end CvxLean
