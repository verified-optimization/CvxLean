/-! Sparse matrix representation and basic operations. -/

/-- Sparse matrix in Compressed Column Storage (CCS).
See http://netlib.org/linalg/html_templates/node92.html
NOTE: Not quite the same as the definition in splamm.c, we assume m=n. -/
structure SparseMatrix (α : Type) :=
  -- Length of val and rowIdx.
  (nnz : Int)
  -- Length of colPtr (-1).
  (n : Int)
  -- Values of non-zero entries.
  (val : Array α)
  -- Row location of each element in val.
  (rowIdx : Array Int)
  -- Number of values per column, tells us how to split val and rowIdx.
  (colPtr : Array Int)

variable {α}

instance [ToString α] : ToString (SparseMatrix α) where
  toString sp :=
    "(" ++ toString sp.nnz ++
    ", " ++ toString sp.n ++
    ", " ++ toString sp.val ++
    ", " ++ toString sp.rowIdx ++
    ", " ++ toString sp.colPtr ++ ")"

namespace Array

private def countNz (A : Array Float) : Int :=
  A.foldl (fun acc x => if x ≤ 10e-6 ∧ x ≥ -10e-6 then acc else acc + 1) 0

private def indexNz (A : Array Float) : Array (Int × Float) :=
  (A.mapIdx (fun j x => ⟨j.val, x⟩)).filter (fun jx => decide (jx.snd < 0 ∨ 0 < jx.snd))

private def countEq (A : Array Int) (i : Int) : Int :=
  A.foldl (fun acc x => if x = i then acc + 1 else acc) 0

private def partialSum (A : Array Int) (st : Int) : Int :=
  (A.mapIdx (fun i x => if i ≤ st then x else 0)).foldl Int.add 0

private def partialUnSum (A : Array Int) :=
  (A.mapIdx (fun i _x => if i < A.size - 1 then A[i.succ]! - A[i]! - 1 else 0)).pop

private def maximum (A : Array Int) : Int :=
  Option.get! <| List.maximum? A.data

private def take (n : Nat) (A : Array α) : Array α :=
  ⟨List.take n A.data⟩

private def drop (n : Nat) (A : Array α) : Array α :=
  ⟨List.drop n A.data⟩

private def slice (A : Array α) (i j : Int) : Array α :=
  Array.drop (Int.toNat i) (Array.take (Int.toNat j) A)

private def takeGroups (A : Array α) (G : Array Int) : Array (Array α) :=
  (G.mapIdx (fun i _ => if i < G.size - 1 then Array.slice A G[i]! G[i.succ]! else #[])).pop

private def shift (A : Array Int) (shift : Int) : Array Int :=
  A.map (fun x => x + shift)

end Array

namespace DArray

private def countNz (M : Array (Array Float)) : Int :=
  (M.map Array.countNz).foldl Int.add 0

private def indexNz (M : Array (Array Float)) : Array (Int × Int × Float) :=
  ((M.map Array.indexNz).mapIdx (fun i A => A.map (fun jx => ⟨i, jx.fst, jx.snd⟩))).concatMap id

def transpose (A : Array (Array α)) [Inhabited α] : Array (Array α) :=
  A[0]!.mapIdx (fun i _col => A.map (fun r => r[i]!))

end DArray

namespace IndexedMatrix

private def val (I : Array (Int × Int × Float)) : Array Float :=
  I.map (fun ijx => ijx.snd.snd)

private def rowIdx (I : Array (Int × Int × Float)) : Array Int :=
  I.map (fun ijx => ijx.snd.fst)

private def colPtr (I : Array (Int × Int × Float)) (n : Nat) : Array Int :=
  let colIdx : Array Int := I.map (fun ijx => ijx.fst)
  let rangeN : Array Int := (Array.mk (List.range n)).map Int.ofNat
  let colIdxCount : Array Int := rangeN.map (fun k => Array.countEq colIdx k)
  #[0] ++ rangeN.map (fun k => Array.partialSum colIdxCount k)

end IndexedMatrix

namespace SparseMatrix

-- Convert back and forth between sparse matrix and dense matrix representaed as a 2-D array.
section Dense

def ofMatrix (M : Array (Array Float)) : (SparseMatrix Float) :=
  let M := DArray.transpose M
  --let rows := M.size
  let cols := M.size
  let I := DArray.indexNz M
  let val := IndexedMatrix.val I
  let rowIdx := IndexedMatrix.rowIdx I
  let colPtr := IndexedMatrix.colPtr I cols
  { nnz := val.size,
    n := colPtr.size - 1,
    val := val,
    rowIdx := rowIdx,
    colPtr := colPtr }

def toMatrix (M : SparseMatrix Float) : Array (Array Float) :=
  let size := Int.toNat ((Array.maximum M.rowIdx) + 1)
  let vals := Array.takeGroups M.val M.colPtr
  let cols := Array.takeGroups M.rowIdx M.colPtr
  DArray.transpose <| vals.mapIdx (fun i vs =>
    (Array.range size).map (fun j => if cols[i]!.contains (Int.ofNat j) then vs[j]! else 0))

end Dense

-- Make a sparse matrix from two sparse matrices.
section Stack

def hstack (A B : SparseMatrix Float) : SparseMatrix Float :=
  { nnz := A.val.size + B.val.size,
    n := (A.colPtr.size + B.colPtr.size) - 1,
    val := A.val ++ B.val,
    rowIdx := A.rowIdx ++ B.rowIdx,
    colPtr :=
      let colPtrLast := A.colPtr[A.colPtr.size - 1]!
      A.colPtr.pop ++ (Array.shift B.colPtr colPtrLast) }

end Stack

end SparseMatrix
