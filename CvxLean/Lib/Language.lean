import CvxLean.Lib.Minimization 

attribute [-instance] coeDecidableEq

namespace CvxLean 

inductive Num 
  | nat : Nat → Num
  | real : Real → Num
  | vec (n : Nat) : (Fin n → Real) → Num
  | mat (m n : Nat) : (Fin m → Fin n → Real) → Num

inductive NumType :=
  | N : NumType
  | R : NumType
  | V : Nat → NumType
  | M : Nat → Nat → NumType
deriving DecidableEq

abbrev Var := Nat 

inductive Arith
  | num : Num → Arith
  | var : Var → Arith
  | neg : Arith → Arith
  | add : Arith → Arith → Arith
  | mul : Arith → Arith → Arith
  | log : Arith → Arith
  | exp : Arith → Arith
  | vecAccess : Arith → Arith → Arith
  | matAccess : Arith → Arith → Arith → Arith

def Arith.type (Γ : Var → NumType) : Arith → Option NumType
  | num (Num.nat _) => some NumType.N
  | num (Num.real _) => some NumType.R
  | num (Num.vec n _) => some (NumType.V n)
  | num (Num.mat m n _) => some (NumType.M m n)
  | var x => some (Γ x)
  | neg a => type Γ a
  | add a b => match (type Γ a, type Γ b) with
    | (some t_a, some t_b) => if t_a = t_b then some t_a else none
    | _ => none
  | mul a b => match (type Γ a, type Γ b) with
    | (some t_a, some t_b) => if t_a = t_b then some t_a else none
    | _ => none
  | log a => match type Γ a with
    | some NumType.R => some NumType.R
    | _ => none
  | exp a => match type Γ a with
    | some NumType.R => some NumType.R
    | _ => none
  | vecAccess a b => match (type Γ a, type Γ b) with
    | (some (NumType.V _), some NumType.N) => some NumType.R
    | _ => none
  | matAccess a b c => match (type Γ a, type Γ b, type Γ c) with
    | (some (NumType.M _ _), some NumType.N, some NumType.N) => some NumType.R
    | _ => none

end CvxLean