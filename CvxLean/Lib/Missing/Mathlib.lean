-- import Mathbin.Data.Real.Basic
-- import Mathbin.LinearAlgebra.Matrix.Default
-- import Lean

-- attribute [-instance] coeDecidableEq

-- macro "ℝ" : term => 
--   `(Real)
-- -- macro "∑" i:Lean.Parser.Term.funBinder "," t:term : term => 
-- --   `(Finset.sum Finset.univ (fun $i => $t))
-- macro "∑" i:Lean.Parser.Term.funBinder "in" s:term "," t:term : term => 
--   `(Finset.sum $s (fun $i => $t))
-- macro "∏" i:Lean.Parser.Term.funBinder "," t:term : term => 
--   `(Finset.prod Finset.univ (fun $i => $t))
-- macro "∏" i:Lean.Parser.Term.funBinder "in" s:term "," t:term : term => 
--   `(Finset.prod $s (fun $i => $t))
-- macro:75 l:term:75 " ⬝ " r:term:76 : term => 
--   `(Matrix.mul $l $r)
-- macro:75 l:term:75 " ⬝ᵥ " r:term:76 : term => 
--   `(Matrix.dotProduct $l $r)
-- macro:50 l:term:50 " ∈ " r:term:51 : term => 
--   `(HasMem.Mem $l $r)
-- macro:75 l:term:75 " • " r:term:76 : term => 
--   `(HasSmul.smul $l $r)

-- macro "![" ts:term,* "]" : term => do
--   let ts : Array (Lean.TSyntax _) := ts.getElems
--   let res ← ts.foldrM (init := ← `(Matrix.vecEmpty)) fun t acc =>
--       `(Matrix.vecCons $t $acc)
--   return res

-- section Logic

-- end Logic

-- namespace Nat

-- instance : LE ℕ := { le := Nat.le }

-- attribute [-instance] Nat.hasSub
-- instance : Sub ℕ :=
--   ⟨Nat.sub⟩

-- attribute [-instance] Nat.hasAdd
-- instance : Add ℕ :=
--   ⟨Nat.add⟩

-- attribute [-instance] Nat.hasMul
-- instance : Mul ℕ :=
--   ⟨Nat.mul⟩

-- attribute [-instance] Nat.inhabited
-- instance inhabited' : Inhabited ℕ :=
--   ⟨Nat.zero⟩

-- instance decidableEq' : DecidableEq ℕ
--   | zero, zero => isTrue rfl
--   | succ x, zero => isFalse fun h => Nat.noConfusion h
--   | zero, succ y => isFalse fun h => Nat.noConfusion h
--   | succ x, succ y =>
--     match Nat.decidableEq' x y with
--     | Decidable.isTrue xeqy => isTrue (xeqy ▸ Eq.refl (succ x))
--     | Decidable.isFalse xney => isFalse fun h => Nat.noConfusion h fun xeqy => absurd xeqy xney

-- end Nat

-- namespace Pi

-- instance hasZero' {I : Type} {f : I → Type} [∀ i, Zero (f i)] : Zero (∀ i : I, f i) :=
--   ⟨fun _ => Zero.zero⟩

-- instance hasOne' {I : Type} {f : I → Type} [∀ i, One (f i)] : One (∀ i : I, f i) :=
--   ⟨fun _ => One.one⟩

-- end Pi

-- namespace Bool

-- attribute [-instance] Bool.inhabited
-- instance Bool.inhabited' : Inhabited Bool :=
--   ⟨false⟩

-- end Bool

-- namespace Prod

-- attribute [-instance] Prod.inhabited
-- instance Prod.inhabited' [Inhabited α] [Inhabited β] : Inhabited (Prod α β) :=
--   ⟨(default, default)⟩

-- end Prod

-- namespace List

-- attribute [-instance] List.inhabited
-- instance List.inhabited' (α : Type u) : Inhabited (List α) :=
--   ⟨List.nil⟩

-- attribute [-instance] List.hasAppend
-- instance : Append (List α) :=
--   ⟨List.append⟩

-- end List

-- namespace Lean

-- instance (sep) : Coe (Syntax.SepArray sep) (Array Syntax) where
--   coe := Syntax.SepArray.getElems

-- end Lean

-- section LinearOrder

-- variable [LinearOrder α]

-- set_option pp.all true

-- attribute [-instance] LinearOrder.toDistribLattice
-- instance (a b : α) : Decidable (a < b) :=
--   LinearOrder.decidable_lt a b

-- instance (a b : α) : Decidable (a ≤ b) :=
--   LinearOrder.decidable_le a b

-- instance (a b : α) : Decidable (a = b) :=
--   LinearOrder.decidable_eq a b

-- end LinearOrder

-- namespace Int

-- attribute [-instance] Int.linearOrder Int.hasSub

-- instance Int.hasZero' : Zero ℤ :=
--   ⟨ofNat 0⟩

-- instance Int.hasOne' : One ℤ :=
--   ⟨ofNat 1⟩

-- instance Int.hasSub' : Sub ℤ :=
--   ⟨Int.sub⟩

-- instance Int.hasSAdd' : Add ℤ :=
--   ⟨Int.add⟩

-- instance Decidable.true' : Decidable True :=
--   isTrue trivial

-- instance Decidable.false' : Decidable False :=
--   isFalse not_false

-- def decidableNonneg' (a : ℤ) : Decidable (NonNeg a) :=
--   Int.decNonneg a

-- instance decidableLe' (a b : ℤ) : Decidable (a ≤ b) :=
--   Int.decLe a b

-- instance decidableLt' (a b : ℤ) : Decidable (a < b) :=
--   Int.decLt a b

-- instance decidableEq' (a b : ℤ) : Decidable (a = b) :=
--   Int.decEq a b 

-- end Int

-- def Implies.decidable' [Decidable p] [Decidable q] : Decidable (p → q) :=
--   if hp : p then if hq : q then isTrue fun h => hq else isFalse fun h : p → q => absurd (h hp) hq
--   else isTrue fun h => absurd h hp

-- attribute [-instance] Ne.decidable
-- instance Ne.decidable' {α : Sort u} [DecidableEq α] (a b : α) : Decidable (a ≠ b) :=
--   Implies.decidable'
