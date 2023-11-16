import CvxLean.Lib.Math.Data.Real

namespace Vec

variable {m : Type u} {n : Type v} [Fintype m] [Fintype n] {α : Type w}

def abs [Abs α] (x : m → α) : m → α :=
  fun i => Abs.abs (x i)

instance [Abs α] : Abs (m → α) := ⟨abs⟩

section Real

variable (x y : m → Real)

noncomputable def exp : m → Real :=
  fun i => Real.exp (x i)

noncomputable def log : m → Real :=
  fun i => Real.log (x i)

noncomputable def entr : m → Real :=
  fun i => Real.entr (x i)

noncomputable def huber [Fintype m] (x : m → Real) : m → Real :=
  fun i => Real.huber (x i)

noncomputable def kl_div : m → Real :=
  fun i => Real.kl_div (x i) (y i)

end Real

end Vec
