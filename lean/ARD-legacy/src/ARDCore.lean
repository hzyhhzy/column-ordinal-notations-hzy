import OrdinalFormal.GenericSortedColumns
import OrdinalFormal.SpliceConstruction

/-! ARD's exact finite column rules and the dynamic semantic interface.
Entries store all roots; compressed maximum-root lists denote their root closure.
No well-order, reflection, or initial-supply assertion is assumed as an axiom. -/

namespace OrdinalFormal.ARD

open Columns
set_option autoImplicit false

abbrev Entry := Columns.Entry Nat
abbrev Column := Columns.Column Nat
abbrev Graph := Columns.Graph Nat

def Valid (g : Graph) : Prop :=
  ∀ (j : Nat) (a : Entry), a ∈ g[j]?.getD [] →
    a.row < j ∧ a.root ≤ a.parent ∧ a.parent < j

theorem valid_columns {g : Graph} (hg : Valid g) : Columns.Valid g :=
  fun j a ha => (hg j a ha).2

def moveEntry (cut len b : Nat) (a : Entry) : Entry :=
  ⟨move cut len b a.row, move cut len b a.parent, move cut len b a.root⟩

def ordinarySeam (last : Column) (e : Entry) (len b : Nat) : Column :=
  last.flatMap fun a =>
    ((List.range (move e.parent len b a.root + 1)).filter fun q =>
      a.row < e.row || (a.row == e.row && q < move e.parent len b e.root)).map
      fun q => ⟨move e.parent len b a.row, move e.parent len b a.parent, q⟩

def generatedSeam (e : Entry) (len b : Nat) : Column :=
  (List.range (move e.parent len b e.row)).flatMap fun k =>
    (List.range (move e.parent len b e.parent + 1)).map fun q =>
      ⟨k, move e.parent len b e.parent, q⟩

def seam (g : Graph) (e : Entry) (b : Nat) : Column :=
  ordinarySeam (g.getLast?.getD []) e (g.length - 1 - e.parent) b ++
    generatedSeam e (g.length - 1 - e.parent) b

def block (g : Graph) (e : Entry) (b : Nat) : Graph :=
  let len := g.length - 1 - e.parent
  (List.range len).map fun i =>
    let source := (g[e.parent + i]?.getD []).map (moveEntry e.parent len (b+1))
    normalizeColumn compare (source ++ if i = 0 then seam g e b else [])

def expand (g : Graph) (n : Nat) : Graph :=
  let front := g.take (g.length - 1)
  match control compare (g.getLast?.getD []) with
  | none => front
  | some e => front ++ (List.range n).flatMap (block g e)

def stage (g : Graph) (e : Entry) (b : Nat) : Graph :=
  g.take (g.length - 1) ++ (List.range b).flatMap (block g e)

def width (g : Graph) (e : Entry) (b : Nat) : Nat :=
  g.length - 1 + b * (g.length - 1 - e.parent)

def cut (g : Graph) (e : Entry) (b : Nat) : Nat :=
  e.parent + b * (g.length - 1 - e.parent)

def shift (g : Graph) (e : Entry) (b i : Nat) : Nat :=
  move e.parent (g.length - 1 - e.parent) b i

def seed (n : Nat) : Graph :=
  (List.range n).map fun j => if j = 0 then [] else
    normalizeColumn compare [⟨j-1,j-1,j-1⟩]

def Canonical (g : Graph) : Prop := GenericSortedColumns.Canonical compare g

def CompareLt (g h : Graph) : Prop := graphCompare compare g h = .lt

universe u
variable {Label : Type u}

structure Holds (lt : Label → Label → Prop) (D : Label → Prop)
    (R : Label → Label → Label → Label → Prop) (g : Graph) (f : Nat → Label) : Prop where
  domain : ∀ i, i < g.length → D (f i)
  ordered : ∀ i j, i < j → j < g.length → lt (f i) (f j)
  relations : ∀ j a, a ∈ g[j]?.getD [] → R (f a.row) (f a.root) (f a.parent) (f j)

def NeedValid (n : Nat) (a : Entry) : Prop :=
  a.row < n ∧ a.root ≤ a.parent ∧ a.parent < n

def Ends (R : Label → Label → Label → Label → Prop) (needs : List Entry)
    (f : Nat → Label) (beta : Label) : Prop :=
  ∀ a ∈ needs, R (f a.row) (f a.root) (f a.parent) beta

def Admissible (lt : Label → Label → Prop) (K : Label) (c : Nat) (theta : Label)
    (f : Nat → Label) (a : Entry) : Prop :=
  lt (f a.row) K ∨ (f a.row = K ∧ a.root < c ∧ lt (f a.root) theta)

def FiniteReflection (lt : Label → Label → Prop) (D : Label → Prop)
    (R : Label → Label → Label → Label → Prop) : Prop :=
  ∀ (g : Graph) (c : Nat) (K theta beta : Label) (f : Nat → Label) (needs : List Entry),
    Valid g → c < g.length → Holds lt D R g f →
    ReflectionTransport.Bounded lt g.length f beta → R K theta (f c) beta →
    (∀ a ∈ needs, NeedValid g.length a) →
    (∀ a ∈ needs, Admissible lt K c theta f a) → Ends R needs f beta →
    ∃ h, Holds lt D R g h ∧ (∀ i, i < c → h i = f i) ∧
      ReflectionTransport.Bounded lt g.length h (f c) ∧ Ends R needs h (f c)

end OrdinalFormal.ARD
