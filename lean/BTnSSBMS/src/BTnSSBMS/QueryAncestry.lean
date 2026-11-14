import BTnSSBMS.ClosingKeyOrder
import BTnSSBMS.KeyLevels

/-!
The first actual output is in a retained binding's key-row cone exactly
when the complete query key is larger than that binding's key. Equality
reuses the old definition, not the old representative. These statements
use the computed BMS parents, not a proposed activation flag.
-/
namespace BTnSSBMS.Encoder

theorem equal_member {frame : List Binding} (ordered : FrameOrdered frame)
    (bound : Binding) (member : bound ∈ frame) : equal frame bound.key = some bound := by
  induction frame with
  | nil => simp at member
  | cons first rest ih =>
    obtain ⟨before, tail⟩ := List.pairwise_cons.mp ordered
    rcases List.mem_cons.mp member with rfl | later
    · simp [equal, Keys.compare_self]
    · have less := (before bound later).1
      simpa only [equal, List.find?_cons, less, show (Ordering.lt == .eq) = false from rfl,
        Bool.false_eq_true, if_false] using ih tail later

theorem binding_lt_firstHeight_iff {frame : List Binding}
    (ordered : FrameOrdered frame) (dense : FrameDense frame) (zero : HasZero frame)
    (bound : Binding) (member : bound ∈ frame) (key : Key) :
    bound.height < firstHeight frame key ↔ Keys.compare bound.key key = .lt := by
  have found := equal_member ordered bound member
  have original : firstHeight frame bound.key = bound.height := by simp only [firstHeight, found]
  constructor
  · intro height
    cases compared : Keys.compare bound.key key with
    | lt => rfl
    | eq =>
      have same := Keys.compare_eq_imp _ _ compared
      rw [← same, original] at height
      omega
    | gt =>
      have reverse : Keys.compare key bound.key = .lt := by
        rw [Keys.compare_oriented, compared]; rfl
      have lower := firstHeight_lt_if_upper_bound ordered dense zero key bound.key reverse bound found
      rw [original] at lower
      omega
  · intro less
    simpa only [original] using
      firstHeight_lt_if_lower_bound ordered dense zero bound.key key less bound found

/-- Only the first real emission, proved below to be a prefix of `encode`. -/
def queryHead (d : Nat) (a : ParentLabel) (key : Key) (visible : List Nat) (state : State d) : State d :=
  let frame := frameAt state (representative visible a (d - 1))
  let below := smaller frame key
  let u := vector state visible a
  match equal frame key with
  | some bound => emit state u bound.height 0 (below ++ [{bound with latest := some state.length}])
  | none => emit state u ((base below).height + 1) 1 []

theorem queryHead_length (d : Nat) (a : ParentLabel) (key : Key) (visible : List Nat) (state : State d) :
    (queryHead d a key visible state).length = state.length + 1 := by
  simp only [queryHead]
  split <;> exact emit_length ..

theorem queryHead_extends (d : Nat) (a : ParentLabel) (key : Key) (visible : List Nat) (state : State d) :
    state <+: queryHead d a key visible state := by
  simp only [queryHead]
  split <;> exact emit_extends ..

theorem queryHead_readout (d : Nat) (a : ParentLabel) (key : Key) (visible : List Nat) (state : State d) :
    ∃ tag, Readout (queryHead d a key visible state) state.length
      (firstHeight (frameAt state (representative visible a (d - 1))) key) tag := by
  simp only [queryHead]
  split
  next bound found => exact ⟨0, by simpa only [firstHeight, found] using readout_emit state _ bound.height 0 _⟩
  next fresh => exact ⟨1, by simpa only [firstHeight, fresh] using readout_emit state _ _ 1 []⟩

theorem queryHead_prefix_encode (d : Nat) (a : ParentLabel) (hs : Forests ParentLabel)
    (tail : ParentExpr) (visible : List Nat) (state : State d) :
    queryHead d a (Keys.ofColumn d visible.length a hs) visible state <+:
      encode d (.cons a hs tail) visible state := by
  simp only [queryHead, encode]
  split
  next bound found =>
    rw [found]
    exact encode_extends ..
  next fresh =>
    rw [fresh]
    exact (emit_extends ..).trans ((encodeForests_extends ..).trans
      ((emit_extends ..).trans (encode_extends ..)))

theorem queryHead_key_ancestor_iff {d : Nat} {source : ParentContext} {visible : List Nat}
    (state : State d) (positive : 0 < d) (coherent : Parents.Coherent d source)
    (valid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (ordered : FramesOrdered state) (dense : FramesDense state)
    (realized : FramesRealized state) (paths : FramesAncestral state)
    (coordinates : List Nat) (key : Key)
    (zero : HasZero (frameAt state (representative visible (Parents.label d source coordinates) (d - 1))))
    (bound : Binding)
    (member : bound ∈ frameAt state (representative visible (Parents.label d source coordinates) (d - 1)))
    (position : Nat) (latest : bound.latest = some position) :
    Parents.Ancestor (BMS.parentTable (d + 2) (matrix
      (queryHead d (Parents.label d source coordinates) key visible state))) d position state.length ↔
      Keys.compare bound.key key = .lt := by
  let a := Parents.label d source coordinates
  let frame := frameAt state (representative visible a (d - 1))
  let next := queryHead d a key visible state
  have frameOrder : FrameOrdered frame := queried_frame_ordered ordered _
  have frameDense : FrameDense frame := queried_frame_dense dense _
  have frameKnown : FrameRealized state frame := queried_frame_realized realized _
  have oldOutput : Readout state position bound.height 0 := by
    simpa only [latest] using (frameKnown bound member).1
  have oldBound := readout_bound oldOutput
  constructor
  · intro path
    have strict := path.reading_lt (BMS.parentTable_coherent _ _) (by omega)
    have old := readout_extends (queryHead_extends d a key visible state) oldOutput
    obtain ⟨tag, output⟩ := queryHead_readout d a key visible state
    rw [old.key_reading, output.key_reading] at strict
    exact (binding_lt_firstHeight_iff frameOrder frameDense zero bound member key).mp strict
  · intro less
    have retained : bound ∈ smaller frame key := List.mem_filter.mpr ⟨member, by simp only [less, beq_self_eq_true]⟩
    cases found : equal frame key with
    | some reused =>
      dsimp only [frame, a] at found
      have result := reused_head_result state coherent valid view ordered realized paths coordinates key reused positive found
      obtain ⟨p, selected, path, _⟩ := result.2 bound (List.mem_append_left _ retained)
      have same : p = position := Option.some.inj (selected.symm.trans latest)
      subst p
      simpa only [queryHead, found] using path
    | none =>
      dsimp only [frame, a] at found
      obtain ⟨parent, selected⟩ : ∃ parent, representative visible a (d - 1) = some parent := by
        cases selected : representative visible a (d - 1) with
        | some parent => exact ⟨parent, rfl⟩
        | none =>
          dsimp only [a] at selected
          have virtual : bound ∈ virtualFrame := by simpa only [selected, frameAt, Option.bind_none] using member
          have same : bound = zeroBinding := by simpa only [virtualFrame, List.mem_singleton] using virtual
          simp only [same, zeroBinding] at latest
          cases latest
      dsimp only [a] at selected
      have nonempty : smaller (frameAt state (some parent)) key ≠ [] := by
        have witness : bound ∈ smaller (frameAt state (some parent)) key := by simpa only [frame, a, selected] using retained
        intro empty
        simp only [empty, List.not_mem_nil] at witness
      obtain ⟨_, _, _, _, belowPaths⟩ := fresh_head_result state coherent valid view ordered realized paths
        coordinates key positive parent selected nonempty
      obtain ⟨p, hit, path, _⟩ := belowPaths bound (by simpa only [frame, a, selected] using retained)
      have same : p = position := Option.some.inj (hit.symm.trans latest)
      subst p
      simp only [queryHead]
      rw [found]
      simpa only [selected] using path

def Entry.queryFrame (entry : Entry d) : List Binding :=
  frameAt entry.state (representative entry.visible
    (Parents.label d entry.source entry.coordinates) (d - 1))

theorem source_queryHead_prefix {d : Nat} {e : NumericalExpr} {entry : Entry d}
    (entryMember : entry ∈ entries d e [] [] [] [] []) :
    queryHead d (Parents.label d entry.source entry.coordinates) entry.completeKey entry.visible entry.state <+:
      encode d (Parents.annotate d [] e) [] [] :=
  (queryHead_prefix_encode d (Parents.label d entry.source entry.coordinates)
    (Parents.annotateForests d (entry.source ++ [Parents.label d entry.source entry.coordinates]) entry.attachments)
    (Parents.annotate d (entry.source ++ [Parents.label d entry.source entry.coordinates]) entry.tail)
    entry.visible entry.state).trans (entries_execution d e [] [] [] [] [] entry entryMember).resultPrefix

theorem source_query_key_reading {d : Nat} {e : NumericalExpr} {entry : Entry d}
    (entryMember : entry ∈ entries d e [] [] [] [] []) :
    Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) d entry.state.length =
      firstHeight entry.queryFrame entry.completeKey := by
  obtain ⟨tag, output⟩ := queryHead_readout d (Parents.label d entry.source entry.coordinates)
    entry.completeKey entry.visible entry.state
  exact (readout_extends (source_queryHead_prefix entryMember) output).key_reading

/-- The equivalence holds at every actual first-output occurrence in the
whole standard source domain, including entries in nested forests. -/
theorem standard_query_key_ancestor_iff {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {entry : Entry d}
    (entryMember : entry ∈ entries d e [] [] [] [] []) (bound : Binding)
    (member : bound ∈ entry.queryFrame) (position : Nat) (latest : bound.latest = some position) :
    Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e)) d position entry.state.length ↔
      Keys.compare bound.key entry.completeKey = .lt := by
  have sound := standard_entries_sound positive standard entry entryMember
  let a := Parents.label d entry.source entry.coordinates
  have initial := source_queryHead_prefix entryMember
  have criterion := queryHead_key_ancestor_iff entry.state positive sound.coherent sound.valid sound.view
    (source_entry_framesOrdered entryMember) (source_entry_framesDense entryMember)
    (source_entry_framesRealized entryMember) (standard_entry_framesAncestral positive standard entryMember)
    entry.coordinates entry.completeKey
    (queried_frame_has_zero entry.state entry.visible (source_entries_good d e entry entryMember) a (d - 1))
    bound member position latest
  constructor
  · intro path
    apply criterion.mp
    exact path.restrict (table_prefix initial) (BMS.parentTable_valid _ _)
      (by rw [table_length, queryHead_length]; omega)
  · intro less
    exact (criterion.mpr less).prefix (table_prefix initial)

/-- Exact activation of the key row in the original BMS copy algorithm.
The cap is the highest tag row; the queried binding supplies the old root. -/
theorem standard_query_key_activation_iff {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {entry : Entry d}
    (entryMember : entry ∈ entries d e [] [] [] [] []) (bound : Binding)
    (member : bound ∈ entry.queryFrame) (position : Nat) (latest : bound.latest = some position) :
    d < (BMS.thresholds (BMS.parentTable (d + 2) (fromSource d e)) position (d + 1))[entry.state.length]?.getD 0 ↔
      Keys.compare bound.key entry.completeKey = .lt := by
  have length := (source_queryHead_prefix entryMember).length_le
  rw [queryHead_length] at length
  have inside : entry.state.length < (fromSource d e).length := by
    simp only [fromSource, matrix, List.length_map]
    omega
  rw [BMS.thresholds_ancestry (d + 2) (fromSource d e) position (d + 1) (by omega)
    entry.state.length inside d]
  simp only [Nat.lt_succ_self, true_and]
  exact standard_query_key_ancestor_iff positive standard entryMember bound member position latest

end BTnSSBMS.Encoder
