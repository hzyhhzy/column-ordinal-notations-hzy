import OrdinalFormal.Columns

namespace OrdinalFormal.OmegaLRD3

open Columns

set_option maxHeartbeats 800000

/- A finite acyclic syntax tree. `col g e` appends a column to g.
The mutual type, rather than a graph with pointers, rules out cyclic row labels. -/
mutual
  inductive Diagram where
    | nil
    | col (previous : Diagram) (incoming : Edges)
    deriving Repr, DecidableEq
  inductive Edges where
    | nil
    | cons (row : Diagram) (parent root : Nat) (tail : Edges)
    deriving Repr, DecidableEq
end

def Edges.toList : Edges → Column Diagram
  | .nil => []
  | .cons row p q tail => ⟨row, p, q⟩ :: tail.toList

def Edges.ofList : Column Diagram → Edges
  | [] => .nil
  | e :: es => .cons e.row e.parent e.root (.ofList es)

def Diagram.toGraph : Diagram → Graph Diagram
  | .nil => []
  | .col previous incoming => previous.toGraph ++ [incoming.toList]

def Diagram.ofGraph (g : Graph Diagram) : Diagram :=
  g.foldl (fun a c => .col a (.ofList c)) .nil

@[simp] theorem Edges.toList_ofList (es : Column Diagram) :
    (Edges.ofList es).toList = es := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [Edges.ofList, Edges.toList, ih]

@[simp] theorem Edges.ofList_toList (es : Edges) :
    Edges.ofList es.toList = es := by
  cases es with
  | nil => rfl
  | cons row p q tail => simp [Edges.ofList, Edges.toList, Edges.ofList_toList tail]
termination_by sizeOf es

theorem Diagram.toGraph_fold (g : Graph Diagram) (a : Diagram) :
    (g.foldl (fun a c => Diagram.col a (.ofList c)) a).toGraph = a.toGraph ++ g := by
  induction g generalizing a with
  | nil => simp
  | cons c cs ih => simp [List.foldl_cons, ih, Diagram.toGraph, List.append_assoc]

@[simp] theorem Diagram.toGraph_ofGraph (g : Graph Diagram) :
    (Diagram.ofGraph g).toGraph = g := by
  simp [Diagram.ofGraph, Diagram.toGraph_fold, Diagram.toGraph]

@[simp] theorem Diagram.ofGraph_toGraph (a : Diagram) :
    Diagram.ofGraph a.toGraph = a := by
  cases a with
  | nil => rfl
  | col previous incoming =>
    have ih := Diagram.ofGraph_toGraph previous
    simp [Diagram.toGraph, Diagram.ofGraph, List.foldl_append] at ih ⊢
    exact ih
termination_by sizeOf a

mutual
  def Diagram.depth : Diagram → Nat
    | .nil => 0
    | .col previous incoming => max previous.depth incoming.depth
  def Edges.depth : Edges → Nat
    | .nil => 0
    | .cons row _ _ tail => max (row.depth + 1) tail.depth
end

def Diagram.isFinite (a : Diagram) : Bool := a.toGraph.all List.isEmpty

/-- Fuel is a structural nesting bound, not an expansion iteration cap.
`cmp` below always supplies more than enough fuel for both input trees.
No comparison follows a fundamental-sequence path. -/
def compareAt : Nat → Diagram → Diagram → Ordering
  | 0, a, b => graphCompare (fun _ _ => .eq) a.toGraph b.toGraph
  | d + 1, a, b => graphCompare (compareAt d) a.toGraph b.toGraph

def cmp (a b : Diagram) : Ordering := compareAt (a.depth + b.depth + 1) a b

/-- Structural recursion into row labels. At depth zero the graph has no
edges, so its generated package is never used on a well-formed input. -/
def expandAt : Nat → Diagram → Nat → Diagram
  | 0, a, n => Diagram.ofGraph (expand cmp (fun _ _ => []) a.toGraph n)
  | d + 1, a, n =>
    let package : Package Diagram := fun row b =>
      if row.isFinite then [] else Diagram.nil :: (List.range (b + 1)).map (expandAt d row)
    Diagram.ofGraph (expand cmp package a.toGraph n)

def fs (a : Diagram) (n : Nat) : Diagram := expandAt a.depth a n

theorem expandAt_zero (d : Nat) (a : Diagram) :
    (expandAt d a 0).toGraph = a.toGraph.take (a.toGraph.length - 1) := by
  cases d <;> simp [expandAt]

theorem fs_zero (a : Diagram) :
    (fs a 0).toGraph = a.toGraph.take (a.toGraph.length - 1) := expandAt_zero _ _

@[simp] theorem fs_zero_col (a : Diagram) (es : Edges) : fs (.col a es) 0 = a := by
  have h := fs_zero (.col a es)
  simp [Diagram.toGraph] at h
  have := congrArg Diagram.ofGraph h
  simpa using this

theorem expandAt_prefix (d : Nat) (a : Diagram) {i j : Nat} (h : i ≤ j) :
    (expandAt d a i).toGraph.IsPrefix (expandAt d a j).toGraph := by
  cases d <;> simp only [expandAt, Diagram.toGraph_ofGraph]
  · exact expand_prefix _ _ _ h
  · exact expand_prefix _ _ _ h

theorem fs_prefix (a : Diagram) {i j : Nat} (h : i ≤ j) :
    (fs a i).toGraph.IsPrefix (fs a j).toGraph := expandAt_prefix _ _ h

/-- Actual single-column seeds: A0 = 0, A1 = 1, A(n+1) appends
the previous graph as row at parent/root n-1. No spacer column. -/
def seed : Nat → Diagram
  | 0 => .nil
  | d + 1 =>
    let a := seed d
    .col a (.ofList (if d = 0 then [] else normalizeColumn cmp [⟨a, d - 1, d - 1⟩]))

@[simp] theorem seed_width (d : Nat) : (seed d).toGraph.length = d := by
  induction d with
  | zero => rfl
  | succ d ih => simp [seed, Diagram.toGraph, ih]

@[simp] theorem seed_once_zero (d : Nat) : fs (seed (d + 1)) 0 = seed d := by
  simp [seed]

theorem seed_prefix_succ (d : Nat) : (seed d).toGraph.IsPrefix (seed (d + 1)).toGraph := by
  refine ⟨[if d = 0 then [] else normalizeColumn cmp [⟨seed d, d - 1, d - 1⟩]], ?_⟩
  simp [seed, Diagram.toGraph]

inductive Term where
  | finite (a : Diagram)
  | top
  deriving Repr, DecidableEq

def Term.fs : Term → Nat → Term
  | .finite a, n => .finite (OrdinalFormal.OmegaLRD3.fs a n)
  | .top, n => .finite (seed n)

inductive Standard : Term → Prop
  | top : Standard .top
  | child {a : Term} (h : Standard a) (n : Nat) : Standard (a.fs n)

end OrdinalFormal.OmegaLRD3
