import BTnSSBMS.Keys

/-!
An executable, dimension-parametric C-minus encoder. Only a complete key is
reused, and only the parent's saved environment is queried. Forest contexts
are restored by lexical scope; they are not a global memo table.

This module proves termination, width and a uniform linear output bound.
It does not yet prove the block conditions or the order-embedding theorem.
-/
namespace BTnSSBMS
namespace Encoder

structure Binding where
  key : Key
  height : Nat
  latest : Option Nat
  definition : Option Nat
  deriving Repr

def zeroBinding : Binding := ⟨.nil, 0, none, none⟩
def virtualFrame : List Binding := [zeroBinding]

structure Column (d : Nat) where
  values : List Nat
  width : values.length = d + 2
  frame : List Binding

abbrev State (d : Nat) := List (Column d)

def matrix (state : State d) : Matrix := state.map Column.values

def row (d : Nat) (u : Nat → Nat) (height tag : Nat) : List Nat :=
  (List.range d).map u ++ [height, tag]

theorem row_width (d : Nat) (u : Nat → Nat) (height tag : Nat) :
    (row d u height tag).length = d + 2 := by
  simp only [row, List.length_append, List.length_map, List.length_range,
    List.length_cons, List.length_nil]

def emit (state : State d) (u : Nat → Nat) (height tag : Nat)
    (frame : List Binding := []) : State d :=
  state ++ [⟨row d u height tag, row_width d u height tag, frame⟩]

theorem emit_length (state : State d) (u : Nat → Nat) (height tag : Nat)
    (frame : List Binding) :
    (emit state u height tag frame).length = state.length + 1 := by
  simp only [emit, List.length_append, List.length_cons, List.length_nil]

theorem emit_extends (state : State d) (u : Nat → Nat) (height tag : Nat)
    (frame : List Binding) : state <+: emit state u height tag frame :=
  List.prefix_append _ _

def representative (visible : List Nat) (a : ParentLabel) (j : Nat) : Option Nat :=
  (a.parents[j]?.join).bind fun p => visible[p]?

def vector (state : State d) (visible : List Nat) (a : ParentLabel) (j : Nat) : Nat :=
  match (representative visible a j).bind (state[·]?) with
  | none => 0
  | some col => col.values[j]?.getD 0 + 1

def frameAt (state : State d) (position : Option Nat) : List Binding :=
  match position.bind (state[·]?) with
  | none => virtualFrame
  | some col => col.frame

def smaller (frame : List Binding) (key : Key) : List Binding :=
  frame.filter fun b => Keys.compare b.key key == .lt

def equal (frame : List Binding) (key : Key) : Option Binding :=
  frame.find? fun b => Keys.compare b.key key == .eq

/- `base` has an explicit total extension to inconsistent external frames.
`Environment.source_noFallback` proves that this empty-frame extension is
never used by an encoding started from the real empty context. -/
def base (below : List Binding) : Binding := below.getLast?.getD zeroBinding

mutual
  def encode (d : Nat) (e : ParentExpr) (visible : List Nat) (state : State d) : State d :=
    match e with
    | .nil => state
    | .cons a hs t =>
      let key := Keys.ofColumn d visible.length a hs
      let u := vector state visible a
      let frame := frameAt state (representative visible a (d - 1))
      let below := smaller frame key
      match equal frame key with
      | some bound =>
        let p := state.length
        let frame' := below ++ [{bound with latest := some p}]
        let state' := emit state u bound.height 0 frame'
        encode d t (visible ++ [p]) state'
      | none =>
        let c := (base below).height
        let definition := state.length
        let withDefinition := emit state u (c + 1) 1
        let withGuard := emit withDefinition (fun j => u j + 1) (c + 2) 2
        let withForests := encodeForests d hs visible u c below withGuard
        let p := withForests.length
        let frame' := below ++ [⟨key, c + 2, some p, some definition⟩]
        let state' := emit withForests (fun j => u j + 1) (c + 2) 0 frame'
        encode d t (visible ++ [p]) state'
  def encodeForests (d : Nat) (hs : Forests ParentLabel) (visible : List Nat)
      (u : Nat → Nat) (c : Nat) (below : List Binding) (state : State d) : State d :=
    match hs with
    | .nil => state
    | .cons h hs =>
      let slot := state.length
      -- Crucial C-minus rule: omit the owner's new binding from this slot.
      let withSlot := emit state (fun j => u j + 2) (c + 2) 0 below
      let withForest := encode d h (visible ++ [slot]) withSlot
      encodeForests d hs visible u c below withForest
end

mutual
  theorem encode_extends (d : Nat) (e : ParentExpr) (visible : List Nat) (state : State d) :
      state <+: encode d e visible state := by
    cases e with
    | nil => exact List.prefix_refl _
    | cons a hs t =>
      simp only [encode]
      split
      · exact (emit_extends ..).trans (encode_extends d t _ _)
      · refine List.IsPrefix.trans ?_ (encode_extends d t _ _)
        refine List.IsPrefix.trans ?_ (emit_extends ..)
        refine List.IsPrefix.trans ?_ (encodeForests_extends d hs _ _ _ _ _)
        exact (emit_extends ..).trans (emit_extends ..)
  theorem encodeForests_extends (d : Nat) (hs : Forests ParentLabel) (visible : List Nat)
      (u : Nat → Nat) (c : Nat) (below : List Binding) (state : State d) :
      state <+: encodeForests d hs visible u c below state := by
    cases hs with
    | nil => exact List.prefix_refl _
    | cons h hs =>
      exact (emit_extends ..).trans
        ((encode_extends d h _ _).trans (encodeForests_extends d hs _ _ _ _ _))
end

def fromSource (d : Nat) (e : NumericalExpr) : Matrix :=
  matrix (encode d (Parents.annotate d [] e) [] [])

theorem matrix_width (state : State d) :
    ∀ col ∈ matrix state, col.length = d + 2 := by
  intro col h
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp h
  exact c.width

theorem source_width (d : Nat) (e : NumericalExpr) :
    ∀ col ∈ fromSource d e, col.length = d + 2 := matrix_width _

mutual
  theorem encode_bound (d : Nat) (e : ParentExpr) (visible : List Nat) (state : State d) :
      (encode d e visible state).length ≤ state.length + 3 * e.nodes + e.slots := by
    cases e with
    | nil => simp only [encode, Expr.nodes, Expr.slots]; omega
    | cons a hs t =>
      simp only [encode]
      split
      · refine Nat.le_trans (encode_bound d t _ _) ?_
        simp only [emit_length, Expr.nodes, Expr.slots]
        omega
      · refine Nat.le_trans (encode_bound d t _ _) ?_
        let below := smaller (frameAt state (representative visible a (d - 1)))
          (Keys.ofColumn d visible.length a hs)
        let c := (base below).height
        have hh := encodeForests_bound d hs visible (vector state visible a) c below
          (emit (emit state (vector state visible a) (c + 1) 1 [])
            (fun j => vector state visible a j + 1) (c + 2) 2 [])
        dsimp [c, below] at hh
        simp only [emit_length, Expr.nodes, Expr.slots] at hh ⊢
        omega
  theorem encodeForests_bound (d : Nat) (hs : Forests ParentLabel) (visible : List Nat)
      (u : Nat → Nat) (c : Nat) (below : List Binding) (state : State d) :
      (encodeForests d hs visible u c below state).length ≤
        state.length + 3 * hs.nodes + hs.slots := by
    cases hs with
    | nil => simp only [encodeForests, Forests.nodes, Forests.slots]; omega
    | cons h hs =>
      have hh := encode_bound d h (visible ++ [state.length])
        (emit state (fun j => u j + 2) (c + 2) 0 below)
      have ht := encodeForests_bound d hs visible u c below
        (encode d h (visible ++ [state.length]) (emit state (fun j => u j + 2) (c + 2) 0 below))
      simp only [encodeForests, emit_length, Forests.nodes, Forests.slots] at hh ht ⊢
      omega
end

/-- A bound for every finite input, with no dimension or iteration cutoff. -/
theorem source_size_bound (d : Nat) (e : NumericalExpr) :
    (fromSource d e).length ≤ 3 * e.nodes + e.slots := by
  have h := encode_bound d (Parents.annotate d [] e) [] []
  simpa only [fromSource, matrix, List.length_map, List.length_nil,
    Nat.zero_add, Parents.annotate_nodes, Parents.annotate_slots] using h

end Encoder
end BTnSSBMS
