import ARDStructure

/-! ARD, skyline edition. Only finite data and executable rules occur here.
The imported ARD namespace is the preserved ARD-legacy semantic backend.
Skyline normalization sorts only supplied triples; it never enumerates roots.
On skyline columns the maximum controller is the last record and the strict
priority filter is exactly deletion of that record. -/

namespace OrdinalFormal.ARDSkyline
open Columns
set_option autoImplicit false

abbrev Entry := ARD.Entry
abbrev Column := ARD.Column
abbrev Graph := ARD.Graph
abbrev Valid := ARD.Valid
abbrev Holds := @ARD.Holds
abbrev CompareLt := ARD.CompareLt
abbrev moveEntry := ARD.moveEntry

def pairLess (a b : Entry) : Prop :=
  a.row < b.row ∨ (a.row = b.row ∧ a.root < b.root)
instance (a b : Entry) : Decidable (pairLess a b) := inferInstanceAs (Decidable (_ ∨ _))

def dominates (a b : Entry) : Prop :=
  b ≠ a ∧ b.parent ≤ a.parent ∧
    (b.row < a.row ∨ (b.row = a.row ∧ b.root ≤ a.root))
instance (a b : Entry) : Decidable (dominates a b) := inferInstanceAs (Decidable (_ ∧ _))

def skyline (c : Column) : Column :=
  dedupSorted compare (sortDescending compare
    (c.filter fun e => !(c.any fun a => decide (dominates a e))))

def predecessor (e : Entry) : Column :=
  if e.root > 0 then [{e with root := e.root - 1}]
  else if e.row > 0 then [⟨e.row - 1, e.parent, e.parent⟩] else []

def seam (last : Column) (e : Entry) (len b : Nat) : Column :=
  ((last.filter fun a => decide (pairLess a e)).map (moveEntry e.parent len b)) ++
    predecessor (moveEntry e.parent len b e)

def block (g : Graph) (e : Entry) (b : Nat) : Graph :=
  let len := g.length - 1 - e.parent
  (List.range len).map fun i =>
    let source := (g[e.parent + i]?.getD []).map (moveEntry e.parent len (b + 1))
    skyline (source ++ if i = 0 then seam (g.getLast?.getD []) e len b else [])

def expand (g : Graph) (n : Nat) : Graph :=
  let front := g.take (g.length - 1)
  match control compare (g.getLast?.getD []) with
  | none => front
  | some e => front ++ (List.range n).flatMap (block g e)

def seed (n : Nat) : Graph :=
  (List.range n).map fun j => if j = 0 then [] else [⟨j-1,j-1,j-1⟩]

def Canonical (g : Graph) : Prop :=
  ∀ c ∈ g, GenericSortedColumns.Sorted compare c

end OrdinalFormal.ARDSkyline
