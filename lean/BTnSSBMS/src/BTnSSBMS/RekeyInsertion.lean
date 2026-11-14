import BTnSSBMS.FrameInsertion
import BTnSSBMS.CoupledQuery

/-!
Insertion calculations after recomputing complete keys from source
payloads. Old and new query keys need not be syntactically equal. The
last theorem uses the actual relocation comparison theorem, not a
postulated equality of keys. Constructing the spliced frames throughout
an entire execution remains a separate obligation.
-/
namespace BTnSSBMS.Encoder

theorem KeyFrameRel.map_preserving_height (frame : List Binding) (f : Binding → Binding)
    (heights : ∀ b, (f b).height = b.height) :
    KeyFrameRel (fun b => (f b).key) frame (frame.map f) := by
  induction frame with
  | nil => exact .nil
  | cons b frame ih => exact .cons ⟨rfl, heights b⟩ ih

theorem KeyFrameRel.smaller_length {keyOf : Binding → Key} {old relocated : List Binding}
    (related : KeyFrameRel keyOf old relocated) (oldKey newKey : Key)
    (comparisons : ∀ b ∈ old, Keys.compare (keyOf b) newKey = Keys.compare b.key oldKey) :
    (Encoder.smaller relocated newKey).length = (Encoder.smaller old oldKey).length := by
  have same := congrArg List.length (related.smaller oldKey newKey comparisons).heights
  simpa only [List.length_map] using same

theorem KeyFrameRel.freshBit {keyOf : Binding → Key} {old relocated : List Binding}
    (related : KeyFrameRel keyOf old relocated) (oldKey newKey : Key)
    (comparisons : ∀ b ∈ old, Keys.compare (keyOf b) newKey = Keys.compare b.key oldKey) :
    freshBit relocated newKey = freshBit old oldKey := by
  cases found : equal old oldKey with
  | none => simp only [Encoder.freshBit, found, related.equal_none oldKey newKey comparisons found]
  | some b =>
    obtain ⟨next, hit, _⟩ := related.equal_some oldKey newKey comparisons b found
    simp [Encoder.freshBit, found, hit]

theorem FrameKeyInsertion.rekey_height_balance {keyOf : Binding → Key} {old relocated new : List Binding}
    (splice : FrameKeyInsertion relocated new) (related : KeyFrameRel keyOf old relocated)
    (oldOrdered : FrameOrdered old) (oldDense : FrameDense old) (oldZero : HasZero old)
    (newOrdered : FrameOrdered new) (newDense : FrameDense new) (newZero : HasZero new)
    (oldKey newKey : Key)
    (comparisons : ∀ b ∈ old, Keys.compare (keyOf b) newKey = Keys.compare b.key oldKey) :
    firstHeight new newKey + freshBit new newKey =
      firstHeight old oldKey + freshBit old oldKey +
        2 * (splice.inserted.filter (fun k => Keys.compare k newKey == .lt)).length := by
  rw [firstHeight_rank newOrdered newDense newZero, firstHeight_rank oldOrdered oldDense oldZero,
    splice.smaller_length, related.smaller_length oldKey newKey comparisons]
  omega

theorem FrameKeyInsertion.rekey_freshBit_of_absent {keyOf : Binding → Key} {old relocated new : List Binding}
    (splice : FrameKeyInsertion relocated new) (related : KeyFrameRel keyOf old relocated)
    (oldKey newKey : Key)
    (comparisons : ∀ b ∈ old, Keys.compare (keyOf b) newKey = Keys.compare b.key oldKey)
    (absent : newKey ∉ splice.inserted) : freshBit new newKey = freshBit old oldKey := by
  have unchanged := freshBit_congr (left := relocated) (right := new) newKey (by
    rw [splice.present_iff]
    exact ⟨Or.inl, fun h => h.resolve_right absent⟩)
  exact unchanged.trans (related.freshBit oldKey newKey comparisons)

theorem FrameKeyInsertion.rekey_height_lt_shift {keyOf : Binding → Key} {old relocated new : List Binding}
    (splice : FrameKeyInsertion relocated new) (related : KeyFrameRel keyOf old relocated)
    (oldOrdered : FrameOrdered old) (oldDense : FrameDense old) (oldZero : HasZero old)
    (newOrdered : FrameOrdered new) (newDense : FrameDense new) (newZero : HasZero new)
    (oldKey newKey : Key)
    (comparisons : ∀ b ∈ old, Keys.compare (keyOf b) newKey = Keys.compare b.key oldKey)
    (notAbove : ¬ ∀ k ∈ splice.inserted, Keys.compare k newKey = .lt) :
    firstHeight new newKey < firstHeight old oldKey + 2 * splice.inserted.length := by
  have countLe := List.length_filter_le (fun k => Keys.compare k newKey == .lt) splice.inserted
  have countNe : (splice.inserted.filter (fun k => Keys.compare k newKey == .lt)).length ≠
      splice.inserted.length := by
    intro same
    have all := List.length_filter_eq_length_iff.mp same
    exact notAbove (fun k member => by simpa only [beq_iff_eq] using all k member)
  have balance := splice.rekey_height_balance related oldOrdered oldDense oldZero newOrdered newDense newZero
    oldKey newKey comparisons
  have oldBit := freshBit_le_one old oldKey
  omega

theorem FrameKeyInsertion.rekey_height_eq_above {keyOf : Binding → Key} {old relocated new : List Binding}
    (splice : FrameKeyInsertion relocated new) (related : KeyFrameRel keyOf old relocated)
    (oldOrdered : FrameOrdered old) (oldDense : FrameDense old) (oldZero : HasZero old)
    (newOrdered : FrameOrdered new) (newDense : FrameDense new) (newZero : HasZero new)
    (oldKey newKey : Key)
    (comparisons : ∀ b ∈ old, Keys.compare (keyOf b) newKey = Keys.compare b.key oldKey)
    (above : ∀ k ∈ splice.inserted, Keys.compare k newKey = .lt) :
    firstHeight new newKey = firstHeight old oldKey + 2 * splice.inserted.length := by
  have absent : newKey ∉ splice.inserted := by
    intro member
    have impossible := above newKey member
    simp only [Keys.compare_self] at impossible
    contradiction
  have same := splice.rekey_freshBit_of_absent related oldKey newKey comparisons absent
  have all : splice.inserted.filter (fun k => Keys.compare k newKey == .lt) = splice.inserted :=
    List.filter_eq_self.mpr (fun k member => by simp only [above k member, beq_self_eq_true])
  have balance := splice.rekey_height_balance related oldOrdered oldDense oldZero newOrdered newDense newZero
    oldKey newKey comparisons
  rw [all, same] at balance
  omega

theorem FrameKeyInsertion.rekey_height_eq_below {keyOf : Binding → Key} {old relocated new : List Binding}
    (splice : FrameKeyInsertion relocated new) (related : KeyFrameRel keyOf old relocated)
    (oldOrdered : FrameOrdered old) (oldDense : FrameDense old) (oldZero : HasZero old)
    (newOrdered : FrameOrdered new) (newDense : FrameDense new) (newZero : HasZero new)
    (oldKey newKey : Key)
    (comparisons : ∀ b ∈ old, Keys.compare (keyOf b) newKey = Keys.compare b.key oldKey)
    (below : ∀ k ∈ splice.inserted, Keys.compare newKey k = .lt) :
    firstHeight new newKey = firstHeight old oldKey := by
  have absent : newKey ∉ splice.inserted := by
    intro member
    have impossible := below newKey member
    simp only [Keys.compare_self] at impossible
    contradiction
  have same := splice.rekey_freshBit_of_absent related oldKey newKey comparisons absent
  have none : splice.inserted.filter (fun k => Keys.compare k newKey == .lt) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro k member hit
    exact Keys.compare_asymmetric _ _ (below k member) (by simpa only [beq_iff_eq] using hit)
  have balance := splice.rekey_height_balance related oldOrdered oldDense oldZero newOrdered newDense newZero
    oldKey newKey comparisons
  rw [none, same] at balance
  simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at balance
  omega

theorem FrameKeyInsertion.rekey_height_le_shift {keyOf : Binding → Key} {old relocated new : List Binding}
    (splice : FrameKeyInsertion relocated new) (related : KeyFrameRel keyOf old relocated)
    (oldOrdered : FrameOrdered old) (oldDense : FrameDense old) (oldZero : HasZero old)
    (newOrdered : FrameOrdered new) (newDense : FrameDense new) (newZero : HasZero new)
    (oldKey newKey : Key)
    (comparisons : ∀ b ∈ old, Keys.compare (keyOf b) newKey = Keys.compare b.key oldKey) :
    firstHeight new newKey ≤ firstHeight old oldKey + 2 * splice.inserted.length := by
  by_cases above : ∀ k ∈ splice.inserted, Keys.compare k newKey = .lt
  · exact Nat.le_of_eq (splice.rekey_height_eq_above related oldOrdered oldDense oldZero
      newOrdered newDense newZero oldKey newKey comparisons above)
  · exact Nat.le_of_lt (splice.rekey_height_lt_shift related oldOrdered oldDense oldZero
      newOrdered newDense newZero oldKey newKey comparisons above)

/-- Apply all three regimes to actual relocated attachments and actual
saved source payloads. The normalized frame is only a comparison tool;
the theorem does not claim it is itself emitted by the encoder. -/
theorem MaterialQuery.relocation_insertion_queries {d : Nat} {source target : ParentContext}
    {coordinates visible owners moved : List Nat} {materials : List (Forests (List Nat))}
    {state : State d} {hs : Forests (List Nat)}
    (query : MaterialQuery d source coordinates visible owners materials state hs)
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (targetUnit : Parents.UnitSteps d target) (view : Parents.NumericalView d source target moved)
    (targetWidth : ∀ i, i < target.length → (target[i]?.getD default).coordinates.length = d)
    (positive : 0 < d) (ordered : FramesOrdered state) (dense : FramesDense state)
    (good : VisibleGood state visible) :
    let old := frameAt state (representative visible (Parents.label d source coordinates) (d - 1))
    let f := rekeyBinding d source target visible moved materials
    let newCoordinates := Source.relocationHead d source target moved coordinates
    let newAttachments := Source.relocateForests d (source ++ [Parents.label d source coordinates])
      (target ++ [Parents.label d target newCoordinates]) (moved ++ [target.length]) hs
    let oldKey := queryKey d source coordinates hs
    let newKey := queryKey d target newCoordinates newAttachments
    ∀ new, FrameOrdered new → FrameDense new → HasZero new →
      ∀ splice : FrameKeyInsertion (old.map f) new,
        firstHeight new newKey ≤ firstHeight old oldKey + 2 * splice.inserted.length ∧
        ((∀ k ∈ splice.inserted, Keys.compare newKey k = .lt) → firstHeight new newKey = firstHeight old oldKey) ∧
        ((∀ k ∈ splice.inserted, Keys.compare k newKey = .lt) →
          firstHeight new newKey = firstHeight old oldKey + 2 * splice.inserted.length) ∧
        ((¬ ∀ k ∈ splice.inserted, Keys.compare k newKey = .lt) →
          firstHeight new newKey < firstHeight old oldKey + 2 * splice.inserted.length) := by
  dsimp only
  intro new newOrdered newDense newZero splice
  let old := frameAt state (representative visible (Parents.label d source coordinates) (d - 1))
  let f := rekeyBinding d source target visible moved materials
  have related := KeyFrameRel.map_preserving_height old f (rekeyBinding_height d source target visible moved materials)
  have comparisons := query.relocation_comparisons targetCoherent targetValid targetUnit view targetWidth positive
  have oldOrdered : FrameOrdered old := queried_frame_ordered ordered _
  have oldDense : FrameDense old := queried_frame_dense dense _
  have oldZero : HasZero old := queried_frame_has_zero state visible good _ _
  exact ⟨splice.rekey_height_le_shift related oldOrdered oldDense oldZero newOrdered newDense newZero _ _ comparisons,
    splice.rekey_height_eq_below related oldOrdered oldDense oldZero newOrdered newDense newZero _ _ comparisons,
    splice.rekey_height_eq_above related oldOrdered oldDense oldZero newOrdered newDense newZero _ _ comparisons,
    splice.rekey_height_lt_shift related oldOrdered oldDense oldZero newOrdered newDense newZero _ _ comparisons⟩

end BTnSSBMS.Encoder
