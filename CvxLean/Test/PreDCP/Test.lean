import CvxLean.Command.Reduction
import CvxLean.Command.Equivalence
import CvxLean.Tactic.PreDCP.Convexify

open CvxLean Minimization Real

def p := 
  optimization (x y : ℝ)
    minimize (x * y)
    subject to 
      h1 : 0 ≤ x
      h2 : 0 ≤ y

def q := 
  optimization (x : ℝ)
    minimize (x)
    subject to
      h1 : x ≤ x

-- def s1 : Solution p → Solution q := 
--   fun _ => ⟨0, le_refl _, fun y => le_refl _⟩

def s2 : Solution q → Solution p := 
  fun _ => ⟨⟨0, 0⟩, ⟨le_refl _, le_refl _⟩, fun y => by {
    simp [p, objFun]
    exact mul_nonneg y.2.1 y.2.2
  }⟩

def x : {| p |} = {| q |} := sorry

#check Equivalence

def m : ℝ → ℝ := by 
  have := Quotient.exact x 
  simp [HasEquiv.Equiv, Setoid.r] at this
  have := this.1

  

reduction r1/q' : p := by 
  have _ := s1 done
  exact done

reduction r2/p' : q := by
  have _ := s2 done
  exact done
