import CvxLean.Lib.Missing.ToExpr
import CvxLean.Lib.Missing.Array
import CvxLean.Tactic.Solver.Mosek.Sol

namespace CvxLean

namespace Meta

-- Generate symmetric matrix variable.

section Generation

open Std Lean Lean.Meta

/-- -/
def generateMatrixExpr (n : Nat) (A : Array (Array Float)) : Expr := 
  mkLambda `i Lean.BinderInfo.default (mkApp (mkConst ``Fin) (toExpr n)) (
    mkLambda `j Lean.BinderInfo.default (mkApp (mkConst ``Fin) (toExpr n)) (
      let Ai := 
        mkApp4 (mkConst ``Array.get! [levelZero]) 
          (mkApp (mkConst ``Array [levelZero]) (mkConst ``Float)) 
          (mkApp (mkConst ``instInhabitedArray) (mkConst ``Float))
          (toExpr A) 
          (mkApp2 (mkConst ``Fin.val) (toExpr n) (mkBVar 1))
      let Aij := 
        mkApp4 (mkConst ``Array.get! [levelZero])
          (mkConst ``Float)
          (mkConst ``instInhabitedFloat)
          (Ai)
          (mkApp2 (mkConst ``Fin.val) (toExpr n) (mkBVar 0))
      Aij))

/-- -/
def generateMatrixFromIndexedList (n : Nat) (l : List (Nat × Nat × Float)) 
  : MetaM (Array (Array Float)) := do 
  let mut A : Array (Array Float) := DArray.zeroes n n 
  for ⟨i, j, val⟩ in l do
    A := A.set! i (A[i]!.set! j val)
    A := A.set! j (A[j]!.set! i val)
  return A

/-- -/
def generateSymmMatrixFromVariables (n : Nat) (smvs : List Sol.SymmMatrixVariable) 
  : MetaM (List (Lean.Name × (Array (Array Float)) × Lean.Name × (Array (Array Float)))) := do
  -- TODO: Build the hashmap when you read the input.
  let mut m : Std.HashMap String (List (Nat × Nat × Float × Float)) := mkHashMap
  for smv in smvs do 
    match smv.primal, smv.dual with 
    | some primalValue, some dualValue =>
        let key := smv.name
        let toInsert : Nat × Nat × Float × Float := ⟨smv.I, smv.J, primalValue, dualValue⟩
        let newList : List (Nat × Nat × Float × Float) := 
          (match (m.find? key) with
          | some value => value 
          | none => []) ++ [toInsert]
        m := m.insert key newList
    | _, _ => continue
  
  let mut res : List (Lean.Name × (Array (Array Float)) × Lean.Name × (Array (Array Float))) := []

  for x in m.1.buckets.1 do 
    for (k, v) in x do 
      let P ← generateMatrixFromIndexedList n (v.map (fun x => ⟨x.1, x.2.1, x.2.2.1⟩))
      let D ← generateMatrixFromIndexedList n (v.map (fun x => ⟨x.1, x.2.1, x.2.2.2⟩))
      let Pname := Lean.Name.mkSimple (k ++ "P")
      let Dname := Lean.Name.mkSimple (k ++ "D")
      res := res ++ [(Pname, P, Dname, D)]

  return res

/-- -/
def generateSymmMatrix (n : Nat) (S : Sol.Result) 
  : MetaM (Lean.Name × (Array (Array Float)) × Lean.Name × (Array (Array Float))) := do 
  let l ← generateSymmMatrixFromVariables n S.symmMatrixVars
  if l.length != 1 then 
    throwError "Exactly one solution matrix is expected, {l.length} given."
  else 
    return l.get! 0

end Generation

end Meta 

end CvxLean 
