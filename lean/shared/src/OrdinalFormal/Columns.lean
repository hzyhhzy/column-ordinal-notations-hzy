import Std

/-!
Executable column-graph kernel for RPD and LRD-family notations.

Only newly appended columns need normalization. The old prefix is retained
literally. This is the block form of the finite-union definition in the dated
definition documents, not an operation-history encoding.

Theorems here establish zero-index deletion and fundamental-sequence prefixes.
They do NOT postulate or claim global well-ordering or JavaScript equivalence.
-/

namespace OrdinalFormal.Columns

set_option autoImplicit false
set_option maxHeartbeats 600000

universe u

structure Entry (Row : Type u) where
  row : Row
  parent : Nat
  root : Nat
  deriving Repr, DecidableEq

abbrev Column (Row : Type u) := List (Entry Row)
abbrev Graph (Row : Type u) := List (Column Row)

variable {Row : Type u}

def thenCompare (a : Ordering) (b : Unit → Ordering) : Ordering :=
  match a with
  | .eq => b ()
  | x => x

def entryCompare (cmp : Row → Row → Ordering) (a b : Entry Row) : Ordering :=
  thenCompare (compare a.parent b.parent) fun _ =>
    thenCompare (cmp a.row b.row) fun _ => compare a.root b.root

def controlCompare (cmp : Row → Row → Ordering) (a b : Entry Row) : Ordering :=
  thenCompare (cmp a.row b.row) fun _ =>
    thenCompare (compare a.root b.root) fun _ => compare a.parent b.parent

def listCompare {α : Type u} (cmp : α → α → Ordering) :
    List α → List α → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => thenCompare (cmp a b) fun _ => listCompare cmp as bs

def graphCompare (cmp : Row → Row → Ordering) : Graph Row → Graph Row → Ordering :=
  listCompare (listCompare (entryCompare cmp))

def dedupSorted (cmp : Row → Row → Ordering) : Column Row → Column Row
  | [] => []
  | e :: es =>
    let rest := dedupSorted cmp es
    match rest with
    | [] => [e]
    | f :: _ => if entryCompare cmp e f == .eq then rest else e :: rest

/-- Structurally recursive insertion sort keeps finite oracle equalities
kernel-reducible; no native evaluator axiom is needed by the tests. -/
def insertDescending (cmp : Row → Row → Ordering) (e : Entry Row) :
    Column Row → Column Row
  | [] => [e]
  | f :: fs => if entryCompare cmp e f != .lt then e :: f :: fs
      else f :: insertDescending cmp e fs

def sortDescending (cmp : Row → Row → Ordering) : Column Row → Column Row
  | [] => []
  | e :: es => insertDescending cmp e (sortDescending cmp es)

def normalizeColumn (cmp : Row → Row → Ordering) (c : Column Row) : Column Row :=
  dedupSorted cmp (sortDescending cmp (c.flatMap fun e =>
    (List.range (e.root + 1)).map fun q => { e with root := q }))

def normalize (cmp : Row → Row → Ordering) (g : Graph Row) : Graph Row :=
  g.map (normalizeColumn cmp)

def Valid (g : Graph Row) : Prop :=
  ∀ j : Nat, ∀ e : Entry Row, e ∈ (g[j]?.getD []) → e.root ≤ e.parent ∧ e.parent < j

def RootClosed (g : Graph Row) : Prop :=
  ∀ c ∈ g, ∀ e ∈ c, ∀ q, q ≤ e.root → { e with root := q } ∈ c

def control (cmp : Row → Row → Ordering) : Column Row → Option (Entry Row)
  | [] => none
  | e :: es => some (es.foldl (fun a b =>
      if controlCompare cmp a b == .lt then b else a) e)

def move (cut len block i : Nat) : Nat :=
  if i < cut then i else i + block * len

def moveEntry (cut len block : Nat) (e : Entry Row) : Entry Row :=
  { e with parent := move cut len block e.parent,
           root := move cut len block e.root }

/-- Generated rows depend on the block number, never the final index. -/
abbrev Package (Row : Type u) := Row → Nat → List Row

def ordinarySeam (cmp : Row → Row → Ordering) (last : Column Row)
    (e : Entry Row) (len block : Nat) : Column Row :=
  last.flatMap fun a =>
    ((List.range (move e.parent len block a.root + 1)).filter fun q =>
      cmp a.row e.row == .lt ||
        (cmp a.row e.row == .eq && q < move e.parent len block e.root)).map
      fun q => { row := a.row, parent := move e.parent len block a.parent, root := q }

def generatedSeam (package : Package Row) (e : Entry Row)
    (len block : Nat) : Column Row :=
  (package e.row block).flatMap fun row =>
    (List.range (move e.parent len block e.parent + 1)).map fun q =>
      { row := row, parent := move e.parent len block e.parent, root := q }

/-- The appended block copies the source suffix. Its first column also receives
the seams made with the PREVIOUS block's coordinates. -/
def block (cmp : Row → Row → Ordering) (package : Package Row)
    (g : Graph Row) (e : Entry Row) (b : Nat) : Graph Row :=
  let len := g.length - 1 - e.parent
  (List.range len).map fun i =>
    let source := (g[e.parent + i]?.getD []).map (moveEntry e.parent len (b + 1))
    normalizeColumn cmp (source ++ if i = 0 then
      ordinarySeam cmp (g.getLast?.getD []) e len b ++ generatedSeam package e len b
      else [])

def expand (cmp : Row → Row → Ordering) (package : Package Row)
    (g : Graph Row) (n : Nat) : Graph Row :=
  let front := g.take (g.length - 1)
  match control cmp (g.getLast?.getD []) with
  | none => front
  | some e => front ++ (List.range n).flatMap (block cmp package g e)

@[simp] theorem expand_zero (cmp : Row → Row → Ordering) (package : Package Row)
    (g : Graph Row) : expand cmp package g 0 = g.take (g.length - 1) := by
  simp [expand]
  split <;> simp

@[simp] theorem expand_empty (cmp : Row → Row → Ordering) (package : Package Row)
    (n : Nat) : expand cmp package ([] : Graph Row) n = [] := by
  simp [expand, control]

/-- Full columns, not just edge inclusion, are preserved as a prefix. -/
theorem expand_prefix_succ (cmp : Row → Row → Ordering) (package : Package Row)
    (g : Graph Row) (n : Nat) :
    (expand cmp package g n).IsPrefix (expand cmp package g (n + 1)) := by
  unfold expand
  split
  · exact ⟨[], by simp⟩
  · rename_i e he
    refine ⟨block cmp package g e n, ?_⟩
    simp [List.range_succ, List.flatMap_append, List.append_assoc]

theorem expand_prefix (cmp : Row → Row → Ordering) (package : Package Row)
    (g : Graph Row) {i j : Nat} (h : i ≤ j) :
    (expand cmp package g i).IsPrefix (expand cmp package g j) := by
  induction h with
  | refl => exact ⟨[], by simp⟩
  | @step j hij ih => exact ih.trans (expand_prefix_succ cmp package g j)

end OrdinalFormal.Columns
