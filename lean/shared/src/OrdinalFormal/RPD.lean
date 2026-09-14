import OrdinalFormal.Columns

namespace OrdinalFormal.RPD

open Columns

abbrev Diagram := Graph Nat

def seed (n : Nat) : Diagram :=
  [[], normalizeColumn compare ((List.range (n + 1)).map fun k => ⟨k, 0, 0⟩)]

def fs (g : Diagram) (n : Nat) : Diagram := expand compare (fun _ _ => []) g n

def cmp : Diagram → Diagram → Ordering := graphCompare compare

inductive Term where
  | finite (g : Diagram)
  | top
  deriving Repr, DecidableEq

def Term.fs : Term → Nat → Term
  | .finite g, n => .finite (OrdinalFormal.RPD.fs g n)
  | .top, n => .finite (seed n)

/-- The reachable standard domain is deliberately not all parsable diagrams. -/
inductive Standard : Term → Prop
  | top : Standard .top
  | child {a : Term} (h : Standard a) (n : Nat) : Standard (a.fs n)

@[simp] theorem fs_zero (g : Diagram) : fs g 0 = g.take (g.length - 1) :=
  expand_zero _ _ _

theorem fs_prefix (g : Diagram) {i j : Nat} (h : i ≤ j) :
    (fs g i).IsPrefix (fs g j) := expand_prefix _ _ _ h

end OrdinalFormal.RPD
