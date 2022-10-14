import Mathbin.Data.Real.Basic
import Mathbin.LinearAlgebra.Matrix.Default
import Lean

attribute [-instance] coeDecidableEq

macro "ℝ" : term => 
  do return Lean.TSyntax.raw (← `(Real))
macro "∑" i:Lean.Parser.Term.funBinder "," t:term : term => 
  do return Lean.TSyntax.raw (← `(Finset.sum Finset.univ (fun $i => $t)))
macro "∑" i:Lean.Parser.Term.funBinder "in" s:term "," t:term : term => 
  do return Lean.TSyntax.raw (← `(Finset.sum $s (fun $i => $t)))
macro "∏" i:Lean.Parser.Term.funBinder "," t:term : term => 
  do return Lean.TSyntax.raw (← `(Finset.prod Finset.univ (fun $i => $t)))
macro "∏" i:Lean.Parser.Term.funBinder "in" s:term "," t:term : term => 
  do return Lean.TSyntax.raw (← `(Finset.prod $s (fun $i => $t)))
macro:75 l:term:75 " ⬝ " r:term:76 : term => 
  do return Lean.TSyntax.raw (← `(Matrix.mul $l $r))
macro:75 l:term:75 " ⬝ᵥ " r:term:76 : term => 
  do return Lean.TSyntax.raw (← `(Matrix.dotProduct $l $r))
macro:50 l:term:50 " ∈ " r:term:51 : term => 
  do return Lean.TSyntax.raw (← `(HasMem.Mem $l $r))
macro:75 l:term:75 " • " r:term:76 : term => 
  do return Lean.TSyntax.raw (← `(HasSmul.smul $l $r))

macro "![" ts:term,* "]" : term => do
  let ts : Array (Lean.TSyntax _) := ts.getElems
  let res ← ts.foldrM (init := ← `(Matrix.vecEmpty)) fun t acc =>
      `(Matrix.vecCons $t $acc)
  return res.raw

section Logic

@[simp] theorem and_left_comm (a b c : Prop) : (a ∧ (b ∧ c)) = (b ∧ (a ∧ c)) := by rw [← and_assoc, and_comm a b, and_assoc]

end Logic

namespace Nat

instance : LE ℕ := { le := Nat.le }

attribute [-instance] Nat.hasSub
instance : Sub ℕ :=
  ⟨Nat.sub⟩

attribute [-instance] Nat.hasAdd
instance : Add ℕ :=
  ⟨Nat.add⟩

attribute [-instance] Nat.hasMul
instance : Mul ℕ :=
  ⟨Nat.mul⟩

attribute [-instance] Nat.inhabited
instance inhabited' : Inhabited ℕ :=
  ⟨Nat.zero⟩

instance decidableEq' : DecidableEq ℕ
  | zero, zero => isTrue rfl
  | succ x, zero => isFalse fun h => Nat.noConfusion h
  | zero, succ y => isFalse fun h => Nat.noConfusion h
  | succ x, succ y =>
    match Nat.decidableEq' x y with
    | Decidable.isTrue xeqy => isTrue (xeqy ▸ Eq.refl (succ x))
    | Decidable.isFalse xney => isFalse fun h => Nat.noConfusion h fun xeqy => absurd xeqy xney

end Nat

namespace Pi

attribute [-instance] Pi.hasZero
instance hasZero' {I : Type} {f : I → Type} [∀ i, Zero (f i)] : Zero (∀ i : I, f i) :=
  ⟨fun _ => Zero.zero⟩

attribute [-instance] Pi.hasOne
instance hasOne' {I : Type} {f : I → Type} [∀ i, One (f i)] : One (∀ i : I, f i) :=
  ⟨fun _ => One.one⟩

end Pi

namespace Bool

attribute [-instance] Bool.inhabited
instance Bool.inhabited' : Inhabited Bool :=
  ⟨false⟩

end Bool

namespace Prod

attribute [-instance] Prod.inhabited
instance Prod.inhabited' [Inhabited α] [Inhabited β] : Inhabited (Prod α β) :=
  ⟨(default, default)⟩

end Prod

namespace List

attribute [-instance] List.inhabited
instance List.inhabited' (α : Type u) : Inhabited (List α) :=
  ⟨List.nil⟩

attribute [-instance] List.hasAppend
instance : Append (List α) :=
  ⟨List.append⟩

end List

namespace Lean

instance (sep) : Coe (Syntax.SepArray sep) (Array Syntax) where
  coe := Syntax.SepArray.getElems

end Lean

section LinearOrder

variable [LinearOrderₓ α]

instance (a b : α) : Decidable (a < b) :=
  LinearOrderₓ.decidableLt a b

instance (a b : α) : Decidable (a ≤ b) :=
  LinearOrderₓ.decidableLe a b

instance (a b : α) : Decidable (a = b) :=
  LinearOrderₓ.decidableEq a b

end LinearOrder

namespace Int

attribute [-instance] Int.decidableLt
instance Int.decidableLt' : LT Int :=
  ⟨Int.Lt⟩

attribute [-instance] Int.linearOrder Int.hasSub

instance Int.hasZero' : Zero ℤ :=
  ⟨ofNat 0⟩

instance Int.hasOne' : One ℤ :=
  ⟨ofNat 1⟩

instance Int.hasSub' : Sub ℤ :=
  ⟨Int.sub⟩

instance Int.hasSAdd' : Add ℤ :=
  ⟨Int.add⟩

instance Decidable.true' : Decidable True :=
  isTrue trivialₓ

instance Decidable.false' : Decidable False :=
  isFalse not_false

def decidableNonneg' (a : ℤ) : Decidable (Nonneg a) :=
  Int.casesOn a (fun a => Decidable.true') fun a => Decidable.false'

instance decidableLe' (a b : ℤ) : Decidable (a ≤ b) :=
  decidableNonneg' (b - a)

instance decidableLt' (a b : ℤ) : Decidable (a < b) :=
  decidableNonneg' (b - (a + ofNat 1))

instance decidableEq' (a b : ℤ) : Decidable (a = b) :=
match a, b with
| ofNat a, ofNat b => by rw [ofNat_eq_ofNat_iff]; apply Nat.decidableEq'
| negSucc a, ofNat b => Decidable.isFalse λ h => by cases h
| ofNat a, negSucc b => Decidable.isFalse λ h => by cases h
| negSucc a, negSucc b => by rw [negSucc_ofNat_inj_iff]; apply Nat.decidableEq'

end Int

def Implies.decidable' [Decidable p] [Decidable q] : Decidable (p → q) :=
  if hp : p then if hq : q then isTrue fun h => hq else isFalse fun h : p → q => absurd (h hp) hq
  else isTrue fun h => absurd h hp

attribute [-instance] Ne.decidable
instance Ne.decidable' {α : Sort u} [DecidableEq α] (a b : α) : Decidable (a ≠ b) :=
  Implies.decidable'
