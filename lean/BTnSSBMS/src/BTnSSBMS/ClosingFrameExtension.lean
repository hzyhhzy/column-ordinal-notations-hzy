import BTnSSBMS.FramePersistence
import BTnSSBMS.ClosingAncestorSources

/-!
The saved-environment extension asserted by the highest-row argument is
now derived for actual closing representatives: a strict key ancestor's
entire frame survives literally, and the height difference is twice the
number of new bindings. This is not the later insertion-domination
inequality for complete transported blocks.
-/
namespace BTnSSBMS.Encoder

theorem selfLatest_frame_height {state : State d} (dense : FramesDense state)
    (known : FramesRealized state) (stored : FramesStored state) {position : Nat}
    (self : SelfLatest state position) {col : Column d} (lookup : state[position]? = some col) :
    0 < col.frame.length ∧ Readout state position (2 * (col.frame.length - 1)) 0 := by
  obtain ⟨saved, savedLookup, b, member, latest⟩ := self
  have same : saved = col := Option.some.inj (savedLookup.symm.trans lookup)
  subst saved
  obtain ⟨i, found⟩ := List.mem_iff_getElem?.mp member
  have inside := (List.getElem?_eq_some_iff.mp found).choose
  obtain ⟨saved, savedLookup, complete⟩ := stored col (List.mem_of_getElem? lookup) i b found position latest
  have same : saved = col := Option.some.inj (savedLookup.symm.trans lookup)
  subst saved
  have length := congrArg List.length complete
  simp only [List.length_take] at length
  have last : i = col.frame.length - 1 := by omega
  have height := dense col (List.mem_of_getElem? lookup) i b found
  have output := (known position col lookup b member).1
  rw [latest, height, last] at output
  exact ⟨by omega, readout_extends (List.take_prefix ..) output⟩

theorem selfLatest_ancestor_frame_prefix {state : State d} (dense : FramesDense state)
    (known : FramesRealized state) (paths : FramesAncestral state) (stored : FramesStored state)
    {left right : Nat} (leftSelf : SelfLatest state left) (rightSelf : SelfLatest state right)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) d left right)
    {oldCol newCol : Column d} (oldLookup : state[left]? = some oldCol)
    (newLookup : state[right]? = some newCol) : oldCol.frame <+: newCol.frame := by
  obtain ⟨col, lookup, b, member, latest⟩ :=
    selfLatest_ancestor_binding dense known paths leftSelf rightSelf path
  have same : col = newCol := Option.some.inj (lookup.symm.trans newLookup)
  subst col
  obtain ⟨i, found⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨col, lookup, saved⟩ := stored newCol (List.mem_of_getElem? newLookup) i b found left latest
  have same : col = oldCol := Option.some.inj (lookup.symm.trans oldLookup)
  subst col
  rw [saved]
  exact List.take_prefix _ _

theorem selfLatest_strict_ancestor_frame_extension {state : State d} (dense : FramesDense state)
    (known : FramesRealized state) (paths : FramesAncestral state) (stored : FramesStored state)
    {left right : Nat} (leftSelf : SelfLatest state left) (rightSelf : SelfLatest state right)
    (before : left < right)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) d left right) :
    ∃ extra : List Binding, 0 < extra.length ∧
      frameAt state (some right) = frameAt state (some left) ++ extra ∧
      Parents.reading (BMS.parentTable (d + 2) (matrix state)) d right =
        Parents.reading (BMS.parentTable (d + 2) (matrix state)) d left + 2 * extra.length := by
  have leftCopy := leftSelf
  have rightCopy := rightSelf
  obtain ⟨oldCol, oldLookup, _⟩ := leftCopy
  obtain ⟨newCol, newLookup, _⟩ := rightCopy
  obtain ⟨extra, shape⟩ := selfLatest_ancestor_frame_prefix dense known paths stored leftSelf rightSelf path
    oldLookup newLookup
  obtain ⟨oldPositive, oldOutput⟩ := selfLatest_frame_height dense known stored leftSelf oldLookup
  obtain ⟨_, newOutput⟩ := selfLatest_frame_height dense known stored rightSelf newLookup
  have increase := path.reading_lt (BMS.parentTable_coherent _ _) (by omega)
  rw [oldOutput.key_reading, newOutput.key_reading] at increase
  have lengths := congrArg List.length shape
  simp only [List.length_append] at lengths
  refine ⟨extra, by omega, ?_, ?_⟩
  · simp only [frameAt, Option.bind_some, oldLookup, newLookup]
    exact shape.symm
  · rw [oldOutput.key_reading, newOutput.key_reading]
    omega

/-- A strict key-row path between actual closing representatives gives
a literal extension of the old complete saved environment, with no
changes to any old key or either of its pointers. -/
theorem standard_closing_frame_extension {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {earlier later : Entry d}
    (oldMember : earlier ∈ entries d e [] [] [] [] [])
    (newMember : later ∈ entries d e [] [] [] [] [])
    (before : earlier.closing < later.closing)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e)) d earlier.closing later.closing) :
    ∃ extra : List Binding, 0 < extra.length ∧
      frameAt (encode d (Parents.annotate d [] e) [] []) (some later.closing) =
        frameAt (encode d (Parents.annotate d [] e) [] []) (some earlier.closing) ++ extra ∧
      Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) d later.closing =
        Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) d earlier.closing + 2 * extra.length := by
  have legal := Source.standard_finiteLegal positive standard
  exact selfLatest_strict_ancestor_frame_extension (source_framesDense d e) (source_framesRealized d e)
    (source_framesAncestral d e positive legal.separated (legal.parented positive)) (source_framesStored d e)
    (earlier.closing_selfLatest.extends (entries_execution d e [] [] [] [] [] earlier oldMember).resultPrefix)
    (later.closing_selfLatest.extends (entries_execution d e [] [] [] [] [] later newMember).resultPrefix)
    before path

end BTnSSBMS.Encoder
