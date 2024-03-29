import Mathlib.Data.Fin.Basic

/-!
Basic properties about `Fin`.
-/

namespace Fin

variable {n : ℕ}

instance [i : Fact (0 < n)] : OfNat (Fin n) 0 := ⟨⟨0, i.out⟩⟩

instance {n m x : ℕ} : OfNat (Fin n.succ ⊕ Fin m.succ) (x) where
  ofNat := if x <= n then Sum.inl (Fin.ofNat x) else Sum.inr (Fin.ofNat (x - n.succ))

end Fin
