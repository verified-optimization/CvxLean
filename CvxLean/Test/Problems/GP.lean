import CvxLean.Command.Solve
import CvxLean.Tactic.Conv.ConvOpt

section GP

open CvxLean Minimization Real

noncomputable def gp :=
  optimization (x y z : ℝ) 
    minimize (x / y)
    subject to 
      h1 : 0 < x
      h2 : 0 < y
      h3 : 0 < z
      h4 : 2 <= x
      h5 : x <= 3 
      h6 : x^2 + 3 * y / z <= x^0.5
      h7 : x * y = z

inductive I
| x : I
| y : List I → I

class ExpMap (α : Type u) :=
  (exp : α → α)

noncomputable instance : ExpMap ℝ := 
  ⟨Real.exp⟩

instance [ExpMap α] [ExpMap β] : ExpMap (α × β) := 
  ⟨fun x => ⟨ExpMap.exp x.1, ExpMap.exp x.2⟩⟩

class LogMap (α : Type u) :=
  (log : α → α)

noncomputable instance : LogMap ℝ :=
  ⟨Real.log⟩

instance [LogMap α] [LogMap β] : LogMap (α × β) :=
  ⟨fun x => ⟨LogMap.log x.1, LogMap.log x.2⟩⟩

syntax "dirty_split_ands " Lean.Parser.Tactic.casesTarget ",i=" num  : tactic
macro_rules 
  | `(tactic| dirty_split_ands $n,i=$i) => do 
    let nStr := n.raw.reprint.get!.splitOn[0]!
    let iNum := i.raw.isNatLit?.getD 0
    let iStr := iNum.repr.splitOn[0]!
    let i' := Lean.Syntax.mkNumLit (iNum + 1).repr
    let a := Lean.mkIdent (Lean.Name.mkSimple (nStr ++ iStr))
    let b := Lean.mkIdent (Lean.Name.mkSimple nStr)
    `(tactic| first | rcases $n with ⟨$a, $b⟩ ; dirty_split_ands $n,i=$i' | skip)

syntax "dirty_split_ands " Lean.Parser.Tactic.casesTarget : tactic
macro_rules 
  | `(tactic| dirty_split_ands $n) => do 
    `(tactic| dirty_split_ands $n,i=1)

lemma xxx : (0 + x) * x * (0 + 9) = (x + 0) * x * (0 + 9) := by 
  convert rfl using 2
  rw [add_comm]

reduction red/gp2 : gp := by 
  unfold gp
  -- map-objFun-log
  apply map_objective 
    (g := Real.log) 
    (hg := fun x y csx csy => by { 
      dirty_split_ands csx ; dirty_split_ands csy ;
      simp only [maximizeNeg]; refine' (log_le_log _ _).1 <;>
      field_simp <;> positivity })
  -- map_exp 
  -- map_exp
  -- map_exp
  apply map_domain 
    (g := fun x => ExpMap.exp x)
    (f := fun x => LogMap.log x)
    (hfg := fun x hcs => by {  
      dirty_split_ands hcs ; simp [LogMap.log, ExpMap.exp]
      convert rfl <;> rw [exp_log (by assumption)] })
  simp only [Function.comp, ExpMap.exp, LogMap.log]
  -- conv_constr => 
  --   case h1 => simp 
  exact done

end GP
