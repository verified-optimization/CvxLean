import Mathbin.Data.Nat.Basic

lemma Nat.le_eq_LessThanOrEqual : Nat.le = Nat.LessThanOrEqual := by
  ext m n
  constructor
  · intro h
    induction h with
    | refl => apply Nat.LessThanOrEqual.refl
    | step _ h => apply Nat.LessThanOrEqual.step h
  · intro h
    induction h with
    | refl => apply Nat.le.refl
    | step _ h => apply Nat.le.step h

lemma Nat.hasLt_eq_instLTNat : Nat.hasLt = instLTNat := by
  simp only [Nat.le_eq_LessThanOrEqual, Nat.hasLt, instLTNat, Nat.lt]
