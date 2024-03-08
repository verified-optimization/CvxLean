import Lean
import CvxLean.Lib.Math.Data.Array

/-!
Simple trees that can have values of different types at the leaves and nodes.
-/

namespace CvxLean

/-- Tree with node labels of type `α` and leaf labels of type `β`. -/
inductive Tree (α β : Type) : Type
  | node (val : α) (children : Array (Tree α β)) : Tree α β
  | leaf (val : β) : Tree α β
deriving Inhabited

namespace Tree

variable {α β γ δ}

open Lean

partial def toMessageData [ToMessageData α] [ToMessageData β] : Tree α β → MessageData
  | Tree.node val children =>
      let children := children.map toMessageData
      MessageData.paren <|
        "node:" ++ ToMessageData.toMessageData val ++
        "[" ++ (MessageData.joinSep children.toList ", ") ++ "]"
  | Tree.leaf val => "leaf:" ++ ToMessageData.toMessageData val

instance [ToMessageData α] [ToMessageData β] : ToMessageData (Tree α β) where
  toMessageData := toMessageData

/-- Zip two trees. -/
partial def zip [Inhabited α] [Inhabited β] [ToMessageData α] [ToMessageData β] [ToMessageData γ]
    [ToMessageData δ] : Tree α γ → Tree β δ → MetaM (Tree (α × β) (γ × δ))
  | node val₁ children₁, node val₂ children₂ => do
      return node (val₁, val₂) (← Array.zipWithM zip children₁ children₂)
  | leaf val₁, leaf val₂ => pure <| leaf (val₁, val₂)
  | t1, t2 => throwError "zipped trees do not match {t1} {t2}"

/-- Map two functions on the values at the nodes and the values at the leafs, respectively. -/
partial def map [Inhabited γ] (f : α → γ) (g : β → δ) : Tree α β → Tree γ δ
  | node val children => node (f val) (children.map (map f g))
  | leaf val => leaf <| g val

/-- Fold a function on the nodes of the tree. -/
partial def fold [Inhabited γ] (init : γ) (f : γ → α → γ) : Tree α β → γ
  | node val children => Id.run do
      let mut res := init
      for child in children do
        res ← fold res f child
      res := f res val
      return res
  | leaf _ => init

/-- For trees with the same type of nodes and leaves, retrieve the value. -/
def val : Tree α α → α
  | node val _ => val
  | leaf val => val

/-- Size of a tree. -/
partial def size : Tree α β → Nat
  | node _ children => children.foldl (fun acc child => acc + size child) 0
  | leaf _ => 1

end Tree

end CvxLean
