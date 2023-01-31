import CvxLean.Lib.Minimization 
import CvxLean.Syntax.Minimization
import CvxLean.Lib.Approximation.Real 
import CvxLean.Lib.Cones

open CvxLean Minimization

def ArithForm.posOrthCone : ArithForm := 
  ArithForm.le (DyadicExpr.num 0) (DyadicExpr.var 0)

-- This is the kind of theorem I need
theorem ArithForm.posOrth_correct 
  : ArithForm.posOrthCone.interpret [x] = Real.posOrthCone x := by 
  simp only [ArithForm.posOrthCone, Real.posOrthCone]
  simp only [ArithForm.interpret, DyadicExpr.interpret]
  simp only [Dyadic.toRealOfNat, List.get!]
  norm_cast

theorem test : Real.posOrthCone (Dyadic.mk 1 (-1)).toReal := by
  rw [←ArithForm.posOrth_correct]
  apply ArithForm.approx_correct 
    10 (ArithForm.posOrthCone) [(Dyadic.mk 1 (-1)).toReal] [some (Interval.mk (Dyadic.mk 1 (-2)) 1)]
  { simp only [DyadicExpr.boundedByList]
    apply And.intro True.intro ;
    intro i;
    simp only [DyadicExpr.boundedByOpt]
    intros hi hi';
    simp only [DyadicExpr.boundedBy]
    have : i = 0 := Nat.le_antisymm (Nat.le_of_lt_succ hi) (Nat.zero_le _);
    subst i;
    simp only [List.get, Dyadic.toReal_le]; }
  { simp only [ArithForm.posOrthCone, ArithForm.approx, DyadicExpr.approx]
    show _ ≤ _;
    simp only [Dyadic.roundUp, Dyadic.roundDown] }

def prob : Minimization ℝ ℝ := 
  optimization (x : ℝ)
    minimize (x) 
    subject to
      h : x ≥ 0

def solDyadic : Dyadic := Dyadic.mk 0 0 

noncomputable def sol : ℝ := solDyadic.toReal

noncomputable def probSol : Solution prob := by 
  simp only [prob]
  apply Solution.mk sol
  { simp only [constraints, sol, solDyadic];
    simp only [Real.commRing];
    sorry } 
  sorry
