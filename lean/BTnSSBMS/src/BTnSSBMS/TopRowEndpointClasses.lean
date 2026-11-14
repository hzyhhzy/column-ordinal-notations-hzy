import BTnSSBMS.PositiveEndpointOrigins
import BTnSSBMS.EntryOrder

/-!
The complete endpoint classification for the highest (tag) row. Positive
tags have the same actual key parent and tag parent; this excludes them
from a strict key-ancestor pair sharing a tag parent. Thus the two actual
endpoints are P/P or P/slot. This does not prove their block inequalities.
-/
namespace BTnSSBMS.Encoder

theorem FramesRealized.restrict {state next : State d} (known : FramesRealized next)
    (initial : state <+: next) : FramesRealized state := by
  obtain ⟨extra, rfl⟩ := initial
  intro position col lookup
  have inside := (List.getElem?_eq_some_iff.mp lookup).choose
  have nextLookup : (state ++ extra)[position]? = some col := by
    rw [List.getElem?_append_left inside]
    exact lookup
  simpa only [List.take_append_of_le_length (by omega : position + 1 ≤ state.length)] using
    known position col nextLookup

theorem FramesAncestral.restrict {state next : State d} (paths : FramesAncestral next)
    (initial : state <+: next) : FramesAncestral state := by
  intro position col lookup b member
  have inside := (List.getElem?_eq_some_iff.mp lookup).choose
  have nextLookup : next[position]? = some col := by
    obtain ⟨extra, rfl⟩ := initial
    rw [List.getElem?_append_left inside]
    exact lookup
  obtain ⟨root, latest, path, definitions⟩ := paths position col nextLookup b member
  exact ⟨root, latest, path.restrict (table_prefix initial) (BMS.parentTable_valid _ _)
    (by rwa [table_length]), fun q selected =>
      (definitions q selected).restrict (table_prefix initial) (BMS.parentTable_valid _ _)
        (by rwa [table_length])⟩

theorem source_entry_framesRealized {d : Nat} {e : NumericalExpr} {entry : Entry d}
    (member : entry ∈ entries d e [] [] [] [] []) : FramesRealized entry.state :=
  (source_framesRealized d e).restrict (entry.state_prefix_result.trans
    (entries_execution d e [] [] [] [] [] entry member).resultPrefix)

theorem standard_entry_framesAncestral {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {entry : Entry d}
    (member : entry ∈ entries d e [] [] [] [] []) : FramesAncestral entry.state := by
  have legal := Source.standard_finiteLegal positive standard
  exact (source_framesAncestral d e positive legal.separated (legal.parented positive)).restrict
    (entry.state_prefix_result.trans (entries_execution d e [] [] [] [] [] entry member).resultPrefix)

def Entry.guarded (entry : Entry d) : State d :=
  let a := Parents.label d entry.source entry.coordinates
  let hs := Parents.annotateForests d (entry.source ++ [a]) entry.attachments
  let u := vector entry.state entry.visible a
  let c := (base (smaller (frameAt entry.state (representative entry.visible a (d - 1)))
    (Keys.ofColumn d entry.visible.length a hs))).height
  emit (emit entry.state u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 []

theorem Entry.fresh_guard_prefix (entry : Entry d) (fresh : entry.Fresh) :
    entry.guarded <+: entry.headed := by
  dsimp only [Entry.Fresh] at fresh
  simp only [Entry.headed, headState, encode, fresh]
  exact (encodeForests_extends ..).trans (emit_extends ..)

theorem standard_entry_definition_parents {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {entry : Entry d}
    (member : entry ∈ entries d e [] [] [] [] []) (fresh : entry.Fresh) :
    ∃ root,
      Parents.parent (BMS.parentTable (d + 2) (fromSource d e)) d entry.state.length = some root ∧
      Parents.parent (BMS.parentTable (d + 2) (fromSource d e)) (d + 1) entry.state.length = some root := by
  have sound := standard_entries_sound positive standard entry member
  let a := Parents.label d entry.source entry.coordinates
  let hs := Parents.annotateForests d (entry.source ++ [a]) entry.attachments
  let key := Keys.ofColumn d entry.visible.length a hs
  let frame := frameAt entry.state (representative entry.visible a (d - 1))
  let below := smaller frame key
  let c := (base below).height
  let u := vector entry.state entry.visible a
  let defined := emit entry.state u (c + 1) 1 []
  have nonempty : below ≠ [] := hasZero_nonempty
    (fresh_smaller_has_zero
      (queried_frame_has_zero entry.state entry.visible (source_entries_good d e entry member) a (d - 1)) key fresh)
  obtain ⟨position, selected⟩ := fresh_has_representative entry.state sound.view entry.coordinates
    entry.attachments (sound.legal.parented positive).1 fresh
  obtain ⟨root, _, output, parent, _⟩ := fresh_head_result entry.state sound.coherent sound.valid
    sound.view (source_entry_framesOrdered member) (source_entry_framesRealized member)
    (standard_entry_framesAncestral positive standard member) entry.coordinates key positive position selected
    (by simpa only [← selected] using nonempty)
  have keyParent : Parents.parent (BMS.parentTable (d + 2) (matrix defined)) d entry.state.length = some root := by
    simpa only [← selected] using parent
  have tagParent : Parents.parent (BMS.parentTable (d + 2) (matrix defined)) (d + 1) entry.state.length = some root :=
    emitted_tag_parent entry.state u (c + 1) 1 [] root keyParent (by rw [output.tag_reading])
  have initial : defined <+: encode d (Parents.annotate d [] e) [] [] :=
    (emit_extends ..).trans ((entry.fresh_guard_prefix fresh).trans
      (entry.headed_prefix_result.trans (entries_execution d e [] [] [] [] [] entry member).resultPrefix))
  have inside : entry.state.length < (BMS.parentTable (d + 2) (matrix defined)).length := by
    rw [table_length]
    dsimp only [defined]
    rw [emit_length]
    omega
  exact ⟨root,
    (Parents.parent_prefix_eq (table_prefix initial) d entry.state.length inside).symm.trans keyParent,
    (Parents.parent_prefix_eq (table_prefix initial) (d + 1) entry.state.length inside).symm.trans tagParent⟩

theorem standard_entry_guard_parents {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    {entry : Entry d} (member : entry ∈ entries d e [] [] [] [] []) (fresh : entry.Fresh) :
    Parents.parent (BMS.parentTable (d + 2) (fromSource d e)) d (entry.state.length + 1) = some entry.state.length ∧
      Parents.parent (BMS.parentTable (d + 2) (fromSource d e)) (d + 1) (entry.state.length + 1) = some entry.state.length := by
  have initial := (entry.fresh_guard_prefix fresh).trans
    (entry.headed_prefix_result.trans (entries_execution d e [] [] [] [] [] entry member).resultPrefix)
  have inside : entry.state.length + 1 < (BMS.parentTable (d + 2) (matrix entry.guarded)).length := by
    simp only [table_length, Entry.guarded, emit_length]
    omega
  simp only [fromSource]
  constructor
  · rw [← Parents.parent_prefix_eq (table_prefix initial) d (entry.state.length + 1) inside]
    exact guard_key_parent _ _ _ positive
  · rw [← Parents.parent_prefix_eq (table_prefix initial) (d + 1) (entry.state.length + 1) inside]
    exact guard_tag_parent _ _ _ positive

/-- On the entire standard source domain, every positive-tag output has
the same existing parent in the two highest rows. -/
theorem standard_positive_tag_parents {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {position height tag : Nat} (nonzero : 0 < tag)
    (output : Readout (encode d (Parents.annotate d [] e) [] []) position height tag) :
    ∃ root, Parents.parent (BMS.parentTable (d + 2) (fromSource d e)) d position = some root ∧
      Parents.parent (BMS.parentTable (d + 2) (fromSource d e)) (d + 1) position = some root := by
  obtain ⟨entry, member, fresh, left | right⟩ := source_positive_entry d e nonzero output
  · rw [left.2]
    exact standard_entry_definition_parents positive standard member fresh
  · rw [right.2]
    exact ⟨entry.state.length, standard_entry_guard_parents positive member fresh⟩

theorem exists_readout (state : State d) (position : Nat) (inside : position < state.length) :
    ∃ height tag, Readout state position height tag := by
  let col := state[position]
  have keyInside : d < col.values.length := by rw [col.width]; omega
  have tagInside : d + 1 < col.values.length := by rw [col.width]; omega
  exact ⟨col.values[d], col.values[d + 1], col, List.getElem?_eq_getElem inside,
    List.getElem?_eq_getElem keyInside, List.getElem?_eq_getElem tagInside⟩

theorem standard_top_pair_zero {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {a b : Nat} (before : a < b) (inside : b < (fromSource d e).length)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e)) d a b)
    (same : Parents.parent (BMS.parentTable (d + 2) (fromSource d e)) (d + 1) a =
      Parents.parent (BMS.parentTable (d + 2) (fromSource d e)) (d + 1) b) :
    ∃ heightA heightB,
      Readout (encode d (Parents.annotate d [] e) [] []) a heightA 0 ∧
      Readout (encode d (Parents.annotate d [] e) [] []) b heightB 0 := by
  have length : (fromSource d e).length = (encode d (Parents.annotate d [] e) [] []).length := by
    simp only [fromSource, matrix, List.length_map]
  obtain ⟨heightA, tagA, left⟩ := exists_readout (encode d (Parents.annotate d [] e) [] []) a (by omega)
  obtain ⟨heightB, tagB, right⟩ := exists_readout (encode d (Parents.annotate d [] e) [] []) b (by omega)
  have rightZero : tagB = 0 := by
    apply Classical.byContradiction
    intro nonzero
    obtain ⟨root, keyParent, tagParent⟩ := standard_positive_tag_parents positive standard (by omega) right
    have earlier := Parents.parent_earlier (BMS.parentTable_valid _ _) (same.trans tagParent)
    obtain ⟨q, edge, prior⟩ := (Parents.Ancestor.iff_parent (by omega : a ≠ b)).mp path
    have roots : q = root := Option.some.inj (edge.symm.trans keyParent)
    subst q
    have later := prior.le (BMS.parentTable_valid _ _)
    omega
  subst tagB
  have rightNone := Parents.parent_none_of_zero (BMS.parentTable_coherent (d + 2) (fromSource d e))
    (d + 1) b right.tag_reading
  have leftZero : tagA = 0 := by
    apply Classical.byContradiction
    intro nonzero
    obtain ⟨root, _, tagParent⟩ := standard_positive_tag_parents positive standard (by omega) left
    rw [rightNone] at same
    rw [tagParent] at same
    cases same
  subst tagA
  exact ⟨heightA, heightB, left, right⟩

/-- Exhaustive classification of all actual highest-row SB endpoints.
The left endpoint is a source closing representative; the right is a
source closing representative or an actual forest slot. No source SB/G
inequality or target coverage property is assumed. -/
theorem standard_top_pair_classes {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {a b : Nat} (before : a < b) (inside : b < (fromSource d e).length)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e)) d a b)
    (same : Parents.parent (BMS.parentTable (d + 2) (fromSource d e)) (d + 1) a =
      Parents.parent (BMS.parentTable (d + 2) (fromSource d e)) (d + 1) b) :
    ∃ earlier ∈ entries d e [] [] [] [] [], earlier.closing = a ∧
      ((∃ later ∈ entries d e [] [] [] [] [], later.closing = b) ∨
        b ∈ slotPositions d (Parents.annotate d [] e) [] []) := by
  obtain ⟨_, _, left, right⟩ := standard_top_pair_zero positive standard before inside path same
  exact standard_zero_key_pair_classes positive standard left right (by omega) path

end BTnSSBMS.Encoder
