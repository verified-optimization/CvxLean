import Lean

/-!
This file defines the `OC` type, which is a generic type to split data into objective function data
and constraints data. It is used everywhere in DCP (also in pre-DCP).
-/

open Lean Lean.Meta

namespace CvxLean

/-- Structure to split data into the objective funtion (`objFun`) and the constraints (`constrs`).
-/
structure OC (α : Type) where
  objFun : α
  constrs : Array α
deriving Inhabited

namespace OC

variable {α β γ δ ε ζ η θ}

variable [Inhabited α] [Inhabited β] [Inhabited γ] [Inhabited δ] [Inhabited ε] [Inhabited ζ]
variable [Inhabited η]

/-! Many maps operating on up to 7 `OC`s. -/

def map (f : α → β) (oc : OC α) : OC β :=
  OC.mk (f oc.objFun) (oc.constrs.map f)

def mapM (f : α → MetaM β) (oc : OC α) : MetaM (OC β) := do
  return OC.mk (← f oc.objFun) (← oc.constrs.mapM f)

def map2M (f : α → β → MetaM γ) (a : OC α) (b : OC β) : MetaM (OC γ) := do
  let objFun ← f a.objFun b.objFun
  if a.constrs.size != b.constrs.size then
    throwError "`OC` error: could not map (2), different number of constraints."
  let mut constrs := #[]
  for i in [:a.constrs.size] do
    constrs := constrs.push <| ← f a.constrs[i]! b.constrs[i]!
  return OC.mk objFun constrs

def map3M (f : α → β → γ → MetaM δ) (a : OC α) (b : OC β) (c : OC γ) : MetaM (OC δ) := do
  let objFun ← f a.objFun b.objFun c.objFun
  if a.constrs.size != b.constrs.size || b.constrs.size != c.constrs.size then
    throwError "`OC` error: could not map (3), different number of constraints."
  let mut constrs := #[]
  for i in [:a.constrs.size] do
    constrs := constrs.push <| ← f a.constrs[i]! b.constrs[i]! c.constrs[i]!
  return OC.mk objFun constrs

def map4M (f : α → β → γ → δ → MetaM ε) (a : OC α) (b : OC β) (c : OC γ) (d : OC δ) :
    MetaM (OC ε) := do
  let objFun ← f a.objFun b.objFun c.objFun d.objFun
  if a.constrs.size != b.constrs.size || b.constrs.size != c.constrs.size
    || c.constrs.size != d.constrs.size then
    throwError "`OC` error: could not map (4), different number of constraints."
  let mut constrs := #[]
  for i in [:a.constrs.size] do
    constrs := constrs.push <| ← f a.constrs[i]! b.constrs[i]! c.constrs[i]! d.constrs[i]!
  return OC.mk objFun constrs

def map5M (f : α → β → γ → δ → ε → MetaM ζ) (a : OC α) (b : OC β) (c : OC γ) (d : OC δ) (e : OC ε) :
    MetaM (OC ζ) := do
  let objFun ← f a.objFun b.objFun c.objFun d.objFun e.objFun
  if a.constrs.size != b.constrs.size || b.constrs.size != c.constrs.size
    || c.constrs.size != d.constrs.size || d.constrs.size != e.constrs.size then
    throwError "`OC` error: could not map (5), different number of constraints."
  let mut constrs := #[]
  for i in [:a.constrs.size] do
    constrs := constrs.push <|
      ← f a.constrs[i]! b.constrs[i]! c.constrs[i]! d.constrs[i]! e.constrs[i]!
  return OC.mk objFun constrs

def map6M (h : α → β → γ → δ → ε → ζ → MetaM η) (a : OC α) (b : OC β) (c : OC γ) (d : OC δ)
    (e : OC ε) (f : OC ζ) : MetaM (OC η) := do
  let objFun ← h a.objFun b.objFun c.objFun d.objFun e.objFun f.objFun
  if a.constrs.size != b.constrs.size || b.constrs.size != c.constrs.size
    || c.constrs.size != d.constrs.size || d.constrs.size != e.constrs.size
    || e.constrs.size != f.constrs.size then
    throwError "`OC` error: could not map (6), different number of constraints."
  let mut constrs := #[]
  for i in [:a.constrs.size] do
    constrs := constrs.push <|
      ← h a.constrs[i]! b.constrs[i]! c.constrs[i]! d.constrs[i]! e.constrs[i]! f.constrs[i]!
  return OC.mk objFun constrs

def map7M (h : α → β → γ → δ → ε → ζ → η → MetaM θ) (a : OC α) (b : OC β) (c : OC γ) (d : OC δ)
    (e : OC ε) (f : OC ζ) (g : OC η) : MetaM (OC θ) := do
  let objFun ← h a.objFun b.objFun c.objFun d.objFun e.objFun f.objFun g.objFun
  if a.constrs.size != b.constrs.size || b.constrs.size != c.constrs.size
    || c.constrs.size != d.constrs.size || d.constrs.size != e.constrs.size
    || e.constrs.size != f.constrs.size || f.constrs.size != g.constrs.size then
    throwError "`OC` error: could not map (7), different number of constraints."
  let mut constrs := #[]
  for i in [:a.constrs.size] do
    constrs := constrs.push <|
      ← h a.constrs[i]! b.constrs[i]! c.constrs[i]! d.constrs[i]! e.constrs[i]! f.constrs[i]!
        g.constrs[i]!
  return OC.mk objFun constrs

def mapMwithCounter (f : Nat → α → MetaM (β × Nat)) (oc : OC α) : MetaM (OC β) := do
  let mut n := 0
  let (objFun, n') ← f n oc.objFun
  n := n'
  let mut constrs := #[]
  for constr in oc.constrs do
    let (c, n') ← f n constr
    constrs := constrs.push c
    n := n'
  return OC.mk objFun constrs

def map2MwithCounter (f : Nat → α → β → MetaM (γ × Nat)) (a : OC α) (b : OC β) : MetaM (OC γ) := do
  if a.constrs.size != b.constrs.size then
    throwError "`OC` error: could not map (2C), different number of constraints."
  let mut n := 0
  let (objFun, n') ← f n a.objFun b.objFun
  n := n'
  let mut constrs := #[]
  for i in [:a.constrs.size] do
    let (c, n') ← f n a.constrs[i]! b.constrs[i]!
    constrs := constrs.push c
    n := n'
  return OC.mk objFun constrs

def fold (oc : OC α) (init : β) (f : β → α → β) : β := Id.run do
  let b ← f init oc.objFun
  let b ← oc.constrs.foldl f b
  return b

instance [ToMessageData α] : ToMessageData (OC α) where
  toMessageData := fun oc =>
    "objFun:" ++ toMessageData oc.objFun ++ "\nconstrs:" ++ toMessageData oc.constrs

end OC

end CvxLean
