import IPDProfileAtoms
import IPDProfileLower

/-!
# Exact finite column operations

Canonical columns store one maximum profile per parent, in descending parent
order. The controller uses the opposite priority: profile first, then parent.
The expansion is written as the unchanged prefix followed by complete blocks;
this is the same block decomposition as the loop in the reference program.
No reflection, initial-supply or well-ordering assertion is assumed here.
-/

namespace IPD
set_option autoImplicit false
set_option maxHeartbeats 800000

structure Edge where
  parent : Nat
  profile : Profile Nat

abbrev Column := List Edge
abbrev Graph := List Column

def Edge.Valid (child : Nat) (e : Edge) : Prop :=
  e.parent < child ∧ ProfileAtoms (fun i => i ≤ e.parent ∨ i = child) e.profile

def Valid (g : Graph) : Prop := ∀ (j : Nat) (e : Edge), e ∈ g[j]?.getD [] → e.Valid j

def Canonical (g : Graph) : Prop :=
  ∀ c ∈ g, c.Pairwise (fun a b => b.parent < a.parent)

noncomputable def insertEdge (e : Edge) : Column → Column
  | [] => [e]
  | a :: as =>
    if a.parent < e.parent then e :: a :: as
    else if e.parent = a.parent then
      if e.profile ≤ a.profile then a :: as else e :: as
    else a :: insertEdge e as

noncomputable def normalize (c : Column) : Column := c.foldr insertEdge []

def ControlLt (a b : Edge) : Prop :=
  a.profile < b.profile ∨ (a.profile = b.profile ∧ a.parent < b.parent)

noncomputable def controller : Column → Option Edge
  | [] => none
  | a :: as => by
    classical
    exact some (as.foldl (fun best e => if ControlLt best e then e else best) a)

def shift (cut width block i : Nat) : Nat :=
  if i < cut then i else i + block * width

theorem shift_strictMono (cut width block : Nat) : StrictMono (shift cut width block) := by
  intro i j hij
  unfold shift
  split <;> split <;> omega

def moveEdge (cut width block : Nat) (e : Edge) : Edge :=
  ⟨shift cut width block e.parent, renameProfile (shift cut width block) e.profile⟩

noncomputable def seam (g : Graph) (e : Edge) (b : Nat) : Column :=
  let last := g.length - 1
  let width := last - e.parent
  (g.getLast?.getD []).filterMap fun old =>
    let moved := moveEdge e.parent width b old
    if old.parent = e.parent then
      Option.map (fun p => (⟨moved.parent, p⟩ : Edge))
        (lowerProfile moved.parent (shift e.parent width b last) b moved.profile)
    else some moved

noncomputable def block (g : Graph) (e : Edge) (b : Nat) : Graph :=
  let width := g.length - 1 - e.parent
  (List.range width).map fun i =>
    let source := (g[e.parent+i]?.getD []).map (moveEdge e.parent width (b+1))
    normalize (source ++ if i = 0 then seam g e b else [])

noncomputable def expand (g : Graph) (n : Nat) : Graph :=
  let front := g.take (g.length - 1)
  match controller (g.getLast?.getD []) with
  | none => front
  | some e => front ++ (List.range n).flatMap (block g e)

def seed (n : Nat) : Graph := [[], [⟨0, ⟨n, Layer.seed 0 1 0 n⟩⟩]]

def EdgeLt (a b : Edge) : Prop :=
  a.parent < b.parent ∨ (a.parent = b.parent ∧ a.profile < b.profile)

def ColumnLt : Column → Column → Prop := List.Lex EdgeLt
def GraphLt : Graph → Graph → Prop := List.Lex ColumnLt

@[simp] theorem expand_zero (g : Graph) : expand g 0 = g.take (g.length-1) := by
  unfold expand
  split <;> simp

@[simp] theorem expand_empty (n : Nat) : expand [] n = [] := by
  simp [expand, controller]

theorem expand_prefix_succ (g : Graph) (n : Nat) :
    (expand g n).IsPrefix (expand g (n+1)) := by
  unfold expand
  split
  · exact ⟨[], by simp⟩
  · rename_i e he
    refine ⟨block g e n, ?_⟩
    simp [List.range_succ, List.flatMap_append, List.append_assoc]

theorem expand_prefix (g : Graph) {i j : Nat} (h : i ≤ j) :
    (expand g i).IsPrefix (expand g j) := by
  induction h with
  | refl => exact ⟨[], by simp⟩
  | @step j _ ih => exact ih.trans (expand_prefix_succ g j)

@[simp] theorem block_length (g : Graph) (e : Edge) (b : Nat) :
    (block g e b).length = g.length-1-e.parent := by simp [block]

theorem blocks_length (g : Graph) (e : Edge) (n : Nat) :
    ((List.range n).flatMap (block g e)).length = n * (g.length-1-e.parent) := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, List.flatMap_append, ih, Nat.add_mul]

end IPD

#print axioms IPD.shift_strictMono
#print axioms IPD.expand_zero
#print axioms IPD.expand_prefix
#print axioms IPD.blocks_length
