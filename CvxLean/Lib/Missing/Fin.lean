import Mathlib.Data.List.Basic
import Mathbin.Data.Fin.Basic
import Mathbin.Data.Fintype.Basic
import CvxLean.Lib.Missing.Nat

noncomputable instance : Fintype (Fin n) := {
  elems := by exact 
    (Finset.univ : Finset (Finₓ n)).image fun ⟨i, hi⟩ => 
      ⟨i, by rw [←Nat.hasLt_eq_instLTNat]; exact hi⟩
  complete := by
    intros j
    rw [Finset.mem_image]
    use ⟨j.1, by rw [Nat.hasLt_eq_instLTNat]; exact j.2⟩
    use Finset.mem_univ _
}

def Finx.val : Finₓ n → Nat := fun x => x.val
