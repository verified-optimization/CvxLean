import Mathbin.Data.Rat.Basic

instance : ToString Rat where 
  toString 
  | ⟨n, d, _, _⟩ => if d = 1 then n.repr else n.repr.append <| "/".append d.repr
