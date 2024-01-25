import Mathlib.Data.Fin.Basic

namespace Fin

variable {n : ℕ}

instance [i : Fact (0 < n)] : OfNat (Fin n) 0 := ⟨⟨0, i.out⟩⟩

end Fin
