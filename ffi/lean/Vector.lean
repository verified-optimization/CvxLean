import Lean
import Std.Classes.SetNotation
import Std.Data.Array.Lemmas

structure Vector (n : Nat) (α) where
  a : Array α 
  h : a.size = n := by decide

def Vector.toFun {n} {α} : Vector n α → Fin n → α
  | ⟨x, hx⟩ => fun ⟨i, hi⟩ => x.get ⟨i, hx.symm ▸ hi⟩

def Matrix (r c : Nat) (α) := 
  Vector r (Vector c α)

def Matrix.mk (r c : Nat)
  (A : Array (Array α)) 
  (h₁ : A.size = r := by decide)
  (h₂ : ∀ (i : Fin (Array.size A)), Array.size A[i] = c := by decide)
  : Matrix r c α :=
  ⟨A.mapIdx (fun i _ => ⟨A[i], h₂ i⟩), by { rw [Array.size_mapIdx]; exact h₁ }⟩

def Matrix.toFun {r c} {α} (x : Matrix r c α) : Fin r → Fin c → α :=
  fun i => ((Vector.toFun x) i).toFun