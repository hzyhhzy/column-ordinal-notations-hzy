import BTnSSBMS.ClosingKeyOrder
import BTnSSBMS.InsertionSaving

/-!
Instantiate insertion arithmetic at actual closing representatives.
The saved frames and their heights come from the real standard execution;
an insertion or an entering-state profile is not assumed as an interface.
The statements compare individual queries, not the complete moved blocks.
-/
namespace BTnSSBMS.Encoder

theorem selfLatest_binding_is_base {state : State d} (stored : FramesStored state)
    {position : Nat} {col : Column d} (lookup : state[position]? = some col)
    {binding : Binding} (member : binding ∈ col.frame) (latest : binding.latest = some position) :
    base col.frame = binding := by
  obtain ⟨i, found⟩ := List.mem_iff_getElem?.mp member
  have inside := (List.getElem?_eq_some_iff.mp found).choose
  obtain ⟨saved, savedLookup, complete⟩ := stored col (List.mem_of_getElem? lookup) i binding found position latest
  have same : saved = col := Option.some.inj (savedLookup.symm.trans lookup)
  subst saved
  have length := congrArg List.length complete
  simp only [List.length_take] at length
  have last : col.frame.length - 1 = i := by omega
  simp only [base, List.getLast?_eq_getElem?, last, found, Option.getD_some]

theorem source_closing_base_key {d : Nat} {e : NumericalExpr} {entry : Entry d}
    (member : entry ∈ entries d e [] [] [] [] []) :
    (base (frameAt (encode d (Parents.annotate d [] e) [] []) (some entry.closing))).key = entry.completeKey := by
  obtain ⟨col, binding, lookup, inside, key, latest⟩ := source_closing_current_binding member
  simp only [frameAt, Option.bind_some, lookup]
  rw [selfLatest_binding_is_base (source_framesStored d e) lookup inside latest]
  exact key

theorem source_closing_hasZero {d : Nat} {e : NumericalExpr} {entry : Entry d}
    (member : entry ∈ entries d e [] [] [] [] []) :
    HasZero (frameAt (encode d (Parents.annotate d [] e) [] []) (some entry.closing)) := by
  have good := headState_good d (Parents.label d entry.source entry.coordinates)
    (Parents.annotateForests d (entry.source ++ [Parents.label d entry.source entry.coordinates]) entry.attachments)
    entry.visible entry.state (source_entries_good d e entry member)
  change VisibleGood entry.headed (entry.visible ++ [entry.closing]) at good
  have initial := entry.headed_prefix_result.trans (entries_execution d e [] [] [] [] [] entry member).resultPrefix
  obtain ⟨col, lookup, zero⟩ := (visibleGood_extends initial good) entry.closing
    (List.mem_append_right _ (List.mem_singleton_self _))
  simpa only [frameAt, Option.bind_some, lookup] using zero

theorem frame_member_key_le_base {frame : List Binding} (ordered : FrameOrdered frame)
    (b : Binding) (member : b ∈ frame) : Keys.compare b.key (base frame).key ≠ .gt := by
  intro larger
  have nonempty : frame ≠ [] := by intro empty; simp [empty] at member
  have reverse : Keys.compare (base frame).key b.key = .lt := by
    rw [Keys.compare_oriented, larger]
    rfl
  have strict := binding_height_lt ordered (base frame) b (base_member nonempty) member reverse
  have weak := member_height_le_base ordered b member
  omega

theorem ordered_append_base_mem {left extra : List Binding}
    (ordered : FrameOrdered (left ++ extra)) (nonempty : extra ≠ []) : base (left ++ extra) ∈ extra := by
  have combined : left ++ extra ≠ [] := by
    intro empty
    have length := congrArg List.length empty
    simp only [List.length_append, List.length_nil] at length
    have positive := List.length_pos_iff.mpr nonempty
    omega
  rcases List.mem_append.mp (base_member combined) with old | new
  · obtain ⟨b, member⟩ : ∃ b, b ∈ extra := by
      cases extra with
      | nil => contradiction
      | cons b tail => exact ⟨b, List.mem_cons_self⟩
    have strict := ((List.pairwise_append.mp ordered).2.2 (base (left ++ extra)) old b member).2
    have weak := member_height_le_base ordered b (List.mem_append_right _ member)
    omega
  · exact new

/-- The inserted keys lie strictly above the old source key, end at the
new source key, and come from the exact saved environment extension. -/
theorem standard_closing_insertion_interval {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {earlier later : Entry d}
    (oldMember : earlier ∈ entries d e [] [] [] [] [])
    (newMember : later ∈ entries d e [] [] [] [] [])
    (before : earlier.closing < later.closing)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e)) d earlier.closing later.closing) :
    let state := encode d (Parents.annotate d [] e) [] []
    let old := frameAt state (some earlier.closing)
    let new := frameAt state (some later.closing)
    ∃ extra, 0 < extra.length ∧ new = old ++ extra ∧
      Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) d later.closing =
        Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) d earlier.closing + 2 * extra.length ∧
      (∀ b ∈ extra, Keys.compare earlier.completeKey b.key = .lt ∧
        Keys.compare b.key later.completeKey ≠ .gt) ∧
      later.completeKey ∈ extra.map Binding.key := by
  dsimp only
  obtain ⟨extra, positiveExtra, shape, height⟩ :=
    standard_closing_frame_extension positive standard oldMember newMember before path
  let state := encode d (Parents.annotate d [] e) [] []
  let old := frameAt state (some earlier.closing)
  let new := frameAt state (some later.closing)
  change new = old ++ extra at shape
  have ordered : FrameOrdered (old ++ extra) := by
    rw [← shape]
    exact queried_frame_ordered (source_framesOrdered d e) _
  have oldBase : (base old).key = earlier.completeKey := source_closing_base_key oldMember
  have newBase : (base (old ++ extra)).key = later.completeKey := by
    rw [← shape]
    exact source_closing_base_key newMember
  have oldNonempty : old ≠ [] := hasZero_nonempty (source_closing_hasZero oldMember)
  refine ⟨extra, positiveExtra, shape, height, ?_, ?_⟩
  · intro b member
    constructor
    · rw [← oldBase]
      exact ((List.pairwise_append.mp ordered).2.2 (base old) (base_member oldNonempty) b member).1
    · rw [← newBase]
      exact frame_member_key_le_base ordered b (List.mem_append_right _ member)
  · exact List.mem_map.mpr ⟨base (old ++ extra),
      ordered_append_base_mem ordered (List.length_pos_iff.mp positiveExtra), newBase⟩

/-- Exact three-way query result at a strict closing chain. The height
increment is the actual target reading difference, not an external rank.
No claim about later source/target queries having the same key is included. -/
theorem standard_closing_query_cases {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {earlier later : Entry d}
    (oldMember : earlier ∈ entries d e [] [] [] [] [])
    (newMember : later ∈ entries d e [] [] [] [] [])
    (before : earlier.closing < later.closing)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e)) d earlier.closing later.closing)
    (query : Key) :
    let state := encode d (Parents.annotate d [] e) [] []
    let old := frameAt state (some earlier.closing)
    let new := frameAt state (some later.closing)
    let gap := Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) d later.closing -
      Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) d earlier.closing
    firstHeight new query ≤ firstHeight old query + gap ∧
      (Keys.compare earlier.completeKey query ≠ .lt → firstHeight new query = firstHeight old query) ∧
      (Keys.compare later.completeKey query = .lt → firstHeight new query = firstHeight old query + gap) ∧
      (Keys.compare later.completeKey query ≠ .lt → firstHeight new query < firstHeight old query + gap) := by
  let state := encode d (Parents.annotate d [] e) [] []
  let old := frameAt state (some earlier.closing)
  let new := frameAt state (some later.closing)
  obtain ⟨extra, _, shape, height, interval, endpoint⟩ :=
    standard_closing_insertion_interval positive standard oldMember newMember before path
  change new = old ++ extra at shape
  have gap : Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) d later.closing -
      Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) d earlier.closing = 2 * extra.length := by omega
  dsimp only
  change firstHeight new query ≤ firstHeight old query + _ ∧ _
  rw [gap, shape]
  let splice := FrameKeyInsertion.of_append old extra
  have oldOrdered : FrameOrdered old := queried_frame_ordered (source_framesOrdered d e) _
  have oldDense : FrameDense old := queried_frame_dense (source_framesDense d e) _
  have oldZero : HasZero old := source_closing_hasZero oldMember
  have newOrdered : FrameOrdered (old ++ extra) := by
    rw [← shape]; exact queried_frame_ordered (source_framesOrdered d e) _
  have newDense : FrameDense (old ++ extra) := by
    rw [← shape]; exact queried_frame_dense (source_framesDense d e) _
  have newZero : HasZero (old ++ extra) := hasZero_append oldZero
  have count : splice.inserted.length = extra.length := by
    simp only [splice, FrameKeyInsertion.of_append, List.length_map]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [count] using splice.height_le_shift oldOrdered oldDense oldZero newOrdered newDense newZero query
  · intro low
    change firstHeight new query = firstHeight old query
    rw [shape]
    apply splice.height_eq_below oldOrdered oldDense oldZero newOrdered newDense newZero query
    intro key member
    obtain ⟨b, inside, rfl⟩ := List.mem_map.mp member
    have strict := (interval b inside).1
    cases compared : Keys.compare query earlier.completeKey with
    | lt => exact Keys.compare_lt_trans _ _ _ compared strict
    | eq => simpa only [Keys.compare_eq_imp _ _ compared] using strict
    | gt =>
      have reverse : Keys.compare earlier.completeKey query = .lt := by
        rw [Keys.compare_oriented, compared]; rfl
      exact False.elim (low reverse)
  · intro high
    change firstHeight new query = firstHeight old query + 2 * extra.length
    rw [shape]
    have all : ∀ key ∈ splice.inserted, Keys.compare key query = .lt := by
      intro key member
      obtain ⟨b, inside, rfl⟩ := List.mem_map.mp member
      have weak := (interval b inside).2
      cases compared : Keys.compare b.key later.completeKey with
      | lt => exact Keys.compare_lt_trans _ _ _ compared high
      | eq => simpa only [Keys.compare_eq_imp _ _ compared] using high
      | gt => contradiction
    simpa only [count] using splice.height_eq_above oldOrdered oldDense oldZero newOrdered newDense newZero query all
  · intro notHigh
    change firstHeight new query < firstHeight old query + 2 * extra.length
    rw [shape]
    have notAll : ¬ ∀ key ∈ splice.inserted, Keys.compare key query = .lt :=
      fun all => notHigh (all later.completeKey endpoint)
    simpa only [count] using splice.height_lt_shift oldOrdered oldDense oldZero newOrdered newDense newZero query notAll

end BTnSSBMS.Encoder
