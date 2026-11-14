import BTnSSBMS.EncoderHeadTypes
import BTnSSBMS.EncoderBindingMaterials

/-!
Actual source-entry snapshots of the frozen encoder. A snapshot records
the entire remaining lexical source, its numerical context and visible
representatives, original attachment materials, and the actual output
state before the first output. No alternate execution is introduced.
-/
namespace BTnSSBMS.Encoder

structure Entry (d : Nat) where
  source : ParentContext
  coordinates : List Nat
  attachments : Forests (List Nat)
  tail : NumericalExpr
  visible : List Nat
  owners : List Nat
  materials : List (Forests (List Nat))
  state : State d

def Entry.remaining (entry : Entry d) : NumericalExpr :=
  .cons entry.coordinates entry.attachments entry.tail

def Entry.result (entry : Entry d) : State d :=
  encode d (Parents.annotate d entry.source entry.remaining) entry.visible entry.state

structure Entry.Sound (entry : Entry d) : Prop where
  coherent : Parents.Coherent d entry.source
  valid : Parents.ContextValid entry.source
  view : Parents.NumericalView d entry.source (BMS.parentTable (d + 2) (matrix entry.state)) entry.visible
  materials : VisibleMaterials d entry.source entry.visible entry.owners entry.materials entry.state
  legal : Source.FiniteLegal d entry.source entry.remaining

mutual
  def entries (d : Nat) (e : NumericalExpr) (source : ParentContext) (visible owners : List Nat)
      (materials : List (Forests (List Nat))) (state : State d) : List (Entry d) :=
    match e with
    | .nil => []
    | .cons coordinates hs tail =>
      let a := Parents.label d source coordinates
      let annotated := Parents.annotateForests d (source ++ [a]) hs
      let key := Keys.ofColumn d visible.length a annotated
      let u := vector state visible a
      let frame := frameAt state (representative visible a (d - 1))
      let below := smaller frame key
      let headed := headState d a annotated visible state
      ⟨source, coordinates, hs, tail, visible, owners, materials, state⟩ ::
        ((match equal frame key with
        | some _ => []
        | none =>
          let c := (base below).height
          forestEntries d hs source coordinates visible owners materials hs u c below
            (emit (emit state u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 [])) ++
        entries d tail (source ++ [a]) (visible ++ [headed.length - 1]) owners (materials ++ [hs]) headed)

  def forestEntries (d : Nat) (hs : Forests (List Nat)) (source : ParentContext)
      (coordinates visible owners : List Nat) (materials : List (Forests (List Nat)))
      (ownerMaterial : Forests (List Nat)) (u : Nat → Nat) (c : Nat) (below : List Binding)
      (state : State d) : List (Entry d) :=
    match hs with
    | .nil => []
    | .cons h hs =>
      let a := Parents.label d source coordinates
      let withSlot := emit state (fun j => u j + 2) (c + 2) 0 below
      let withForest := encode d (Parents.annotate d (source ++ [a]) h) (visible ++ [state.length]) withSlot
      entries d h (source ++ [a]) (visible ++ [state.length]) (owners ++ [source.length])
        (materials ++ [ownerMaterial]) withSlot ++
      forestEntries d hs source coordinates visible owners materials ownerMaterial u c below withForest
end

/- Projecting snapshots gives exactly the previously proved exhaustive
first-output trace, including every actually visited nested forest. -/
mutual
  theorem entries_positions (d : Nat) (e : NumericalExpr) (source : ParentContext) (visible owners : List Nat)
      (materials : List (Forests (List Nat))) (state : State d) :
      (entries d e source visible owners materials state).map (fun entry => entry.state.length) =
        headPositions d (Parents.annotate d source e) visible state := by
    cases e with
    | nil => rfl
    | cons coordinates hs tail =>
      simp only [entries, Parents.annotate, headPositions, List.map_cons, List.map_append]
      split
      next bound found =>
        simp only [found, List.map_nil, List.nil_append]
        rw [entries_positions]
        simp only [headState, encode, found, emit_length, Nat.add_sub_cancel]
      next fresh =>
        simp only [fresh]
        rw [forestEntries_positions, entries_positions]
        simp only [headState, encode, fresh, emit_length, Nat.add_sub_cancel]

  theorem forestEntries_positions (d : Nat) (hs : Forests (List Nat)) (source : ParentContext)
      (coordinates visible owners : List Nat) (materials : List (Forests (List Nat)))
      (ownerMaterial : Forests (List Nat)) (u : Nat → Nat) (c : Nat) (below : List Binding)
      (state : State d) :
      (forestEntries d hs source coordinates visible owners materials ownerMaterial u c below state).map
        (fun entry => entry.state.length) =
        forestHeadPositions d (Parents.annotateForests d (source ++ [Parents.label d source coordinates]) hs)
          visible u c below state := by
    cases hs with
    | nil => rfl
    | cons h hs =>
      simp only [forestEntries, Parents.annotateForests, forestHeadPositions, List.map_append,
        entries_positions, forestEntries_positions]
end

theorem Entry.Sound.query {d : Nat} {entry : Entry d} (sound : entry.Sound) :
    MaterialQuery d entry.source entry.coordinates entry.visible entry.owners entry.materials
      entry.state entry.attachments :=
  ⟨queried_frame_inheritedMaterials sound.materials sound.view entry.coordinates,
    sound.coherent, sound.valid, sound.view, sound.legal.1, sound.legal.2.1, sound.legal.2.2.2.1⟩

theorem Entry.Sound.unit {d : Nat} {entry : Entry d} (sound : entry.Sound) :
    Parents.UnitSteps d entry.source :=
  sound.legal.2.1.restrict (Parents.context_valid_append_label d entry.source sound.valid entry.coordinates)
    (List.prefix_append entry.source [Parents.label d entry.source entry.coordinates])

theorem Entry.Sound.width {d : Nat} {entry : Entry d} (sound : entry.Sound) :
    ∀ i, i < entry.source.length → (entry.source[i]?.getD default).coordinates.length = d :=
  fun i inside => (sound.materials.materialContext.legal i inside).1

end BTnSSBMS.Encoder
