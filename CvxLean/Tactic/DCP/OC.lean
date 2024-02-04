import Lean

open Lean Lean.Meta

namespace CvxLean

structure OC (α : Type) :=
  (objFun : α)
  (constr : Array α)
deriving Inhabited

namespace OC

variable {α β γ δ ε ζ η θ}

def map (f : α → β) (oc : OC α) : OC β :=
  OC.mk (f oc.objFun) (oc.constr.map f)

def mapM (f : α → MetaM β) (oc : OC α) : MetaM (OC β) := do
  return OC.mk (← f oc.objFun) (← oc.constr.mapM f)

def map2M [Inhabited α] [Inhabited β] (f : α → β → MetaM γ) (a : OC α) (b : OC β) : MetaM (OC γ) := do
  let objFun ← f a.objFun b.objFun
  if a.constr.size != b.constr.size then throwError "different number of constrs"
  let mut constr := #[]
  for i in [:a.constr.size] do
    constr := constr.push $ ← f a.constr[i]! b.constr[i]!
  return OC.mk objFun constr

def map3M [Inhabited α] [Inhabited β] [Inhabited γ] (f : α → β → γ → MetaM δ) (a : OC α) (b : OC β) (c : OC γ) : MetaM (OC δ) := do
  let objFun ← f a.objFun b.objFun c.objFun
  if a.constr.size != b.constr.size ∨ b.constr.size != c.constr.size then throwError "different number of constrs"
  let mut constr := #[]
  for i in [:a.constr.size] do
    constr := constr.push $ ← f a.constr[i]! b.constr[i]! c.constr[i]!
  return OC.mk objFun constr

def map4M [Inhabited α] [Inhabited β] [Inhabited γ] [Inhabited δ] (f : α → β → γ → δ → MetaM ε) (a : OC α) (b : OC β) (c : OC γ) (d : OC δ) : MetaM (OC ε) := do
  let objFun ← f a.objFun b.objFun c.objFun d.objFun
  if a.constr.size != b.constr.size ∨ b.constr.size != c.constr.size ∨ c.constr.size != d.constr.size then throwError "different number of constrs"
  let mut constr := #[]
  for i in [:a.constr.size] do
    constr := constr.push $ ← f a.constr[i]! b.constr[i]! c.constr[i]! d.constr[i]!
  return OC.mk objFun constr

def map5M [Inhabited α] [Inhabited β] [Inhabited γ] [Inhabited δ] [Inhabited ε] (f : α → β → γ → δ → ε → MetaM ζ) (a : OC α) (b : OC β) (c : OC γ) (d : OC δ) (e : OC ε) : MetaM (OC ζ) := do
  let objFun ← f a.objFun b.objFun c.objFun d.objFun e.objFun
  if a.constr.size != b.constr.size ∨ b.constr.size != c.constr.size ∨ c.constr.size != d.constr.size ∨ d.constr.size != e.constr.size then throwError "different number of constrs"
  let mut constr := #[]
  for i in [:a.constr.size] do
    constr := constr.push $ ← f a.constr[i]! b.constr[i]! c.constr[i]! d.constr[i]! e.constr[i]!
  return OC.mk objFun constr

def map6M [Inhabited α] [Inhabited β] [Inhabited γ] [Inhabited δ] [Inhabited ε] [Inhabited ζ] (h : α → β → γ → δ → ε → ζ → MetaM η) (a : OC α) (b : OC β) (c : OC γ) (d : OC δ) (e : OC ε) (f : OC ζ) : MetaM (OC η) := do
  let objFun ← h a.objFun b.objFun c.objFun d.objFun e.objFun f.objFun
  if a.constr.size != b.constr.size ∨ b.constr.size != c.constr.size ∨ c.constr.size != d.constr.size ∨ d.constr.size != e.constr.size ∨ e.constr.size != f.constr.size then throwError "different number of constrs"
  let mut constr := #[]
  for i in [:a.constr.size] do
    constr := constr.push $ ← h a.constr[i]! b.constr[i]! c.constr[i]! d.constr[i]! e.constr[i]! f.constr[i]!
  return OC.mk objFun constr

def map7M [Inhabited α] [Inhabited β] [Inhabited γ] [Inhabited δ] [Inhabited ε] [Inhabited ζ] [Inhabited η]
  (h : α → β → γ → δ → ε → ζ → η → MetaM θ)
  (a : OC α) (b : OC β) (c : OC γ) (d : OC δ) (e : OC ε) (f : OC ζ) (g : OC η) : MetaM (OC θ) := do
  let objFun ← h a.objFun b.objFun c.objFun d.objFun e.objFun f.objFun g.objFun
  if a.constr.size != b.constr.size ∨ b.constr.size != c.constr.size ∨ c.constr.size != d.constr.size ∨ d.constr.size != e.constr.size ∨ e.constr.size != f.constr.size ∨ f.constr.size != g.constr.size then throwError "different number of constrs"
  let mut constr := #[]
  for i in [:a.constr.size] do
    constr := constr.push $ ← h a.constr[i]! b.constr[i]! c.constr[i]! d.constr[i]! e.constr[i]! f.constr[i]! g.constr[i]!
  return OC.mk objFun constr

def mapMwithCounter (f : Nat → α → MetaM (β × Nat)) (oc : OC α) : MetaM (OC β) := do
  let mut n := 0
  let (objFun, n') ← f n oc.objFun
  n := n'
  let mut constrs := #[]
  for constr in oc.constr do
    let (c, n') ← f n constr
    constrs := constrs.push c
    n := n'
  return OC.mk objFun constrs

def map2MwithCounter [Inhabited α] [Inhabited β] (f : Nat → α → β → MetaM (γ × Nat)) (a : OC α) (b : OC β) : MetaM (OC γ) := do
  if a.constr.size != b.constr.size then throwError "different number of constrs"
  let mut n := 0
  let (objFun, n') ← f n a.objFun b.objFun
  n := n'
  let mut constrs := #[]
  for i in [:a.constr.size] do
    let (c, n') ← f n a.constr[i]! b.constr[i]!
    constrs := constrs.push c
    n := n'
  return OC.mk objFun constrs

def fold (oc : OC α) (init : β) (f : β → α → β) : β := Id.run do
  let b ← f init oc.objFun
  let b ← oc.constr.foldl f b
  return b

instance [ToMessageData α] : ToMessageData (OC α) := {
  toMessageData := fun oc => "ObjFun:" ++ toMessageData oc.objFun ++ "\nConstr:" ++ toMessageData oc.constr
}

end OC

end CvxLean
