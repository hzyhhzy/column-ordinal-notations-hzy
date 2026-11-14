import BTnSSBMS.EntryRebaseControl

/-!
Numerical parents of actual first outputs, and reflection of a shared
parent through an actual visible origin. The origin assumption is the
proved lexical relation, not an inverse implicitly assumed for an
arbitrary NumericalView.
-/
namespace BTnSSBMS.Encoder

theorem headState_first_parents {d : Nat} {source : ParentContext} {visible : List Nat}
    (state : State d) (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (coordinates : List Nat) (hs : Forests (List Nat)) {j : Nat} (room : j < d) :
    Parents.parent (BMS.parentTable (d + 2) (matrix (headState d (Parents.label d source coordinates)
      (Parents.annotateForests d (source ++ [Parents.label d source coordinates]) hs) visible state)))
      j state.length = representative visible (Parents.label d source coordinates) j := by
  simp only [headState, encode]
  split
  next bound found =>
    rw [emitted_parent]
    exact emitted_head_numerical_parents state coherent valid view coordinates bound.height 0 j room
  next fresh =>
    let a := Parents.label d source coordinates
    let annotated := Parents.annotateForests d (source ++ [a]) hs
    let key := Keys.ofColumn d visible.length a annotated
    let below := smaller (frameAt state (representative visible a (d - 1))) key
    let c := (base below).height
    let u := vector state visible a
    let withD := emit state u (c + 1) 1 []
    let guarded := emit withD (fun k => u k + 1) (c + 2) 2 []
    let forests := encodeForests d annotated visible u c below guarded
    let closed := emit forests (fun k => u k + 1) (c + 2) 0
      (below ++ [⟨key, c + 2, some forests.length, some state.length⟩])
    have extended : withD <+: closed := (emit_extends ..).trans
      ((encodeForests_extends ..).trans (emit_extends ..))
    have original := (emitted_parent state u (c + 1) 1 [] j).trans
      (emitted_head_numerical_parents state coherent valid view coordinates (c + 1) 1 j room)
    exact (Parents.parent_prefix_eq (table_prefix extended) j state.length
      (by rw [table_length, emit_length]; omega)).symm.trans original

theorem Entry.Sound.first_parent {d : Nat} {entry : Entry d} (sound : entry.Sound)
    {j : Nat} (room : j < d) :
    Parents.parent (BMS.parentTable (d + 2) (matrix entry.result)) j entry.state.length =
      ((Parents.label d entry.source entry.coordinates).parents[j]?.join).map (Parents.point entry.visible) := by
  let a := Parents.label d entry.source entry.coordinates
  let annotated := Parents.annotateForests d (entry.source ++ [a]) entry.attachments
  let headed := headState d a annotated entry.visible entry.state
  have extended : headed <+: entry.result := by
    simp only [Entry.result, Entry.remaining, Parents.annotate, encode_split_head]
    exact encode_extends ..
  have inside : entry.state.length < (BMS.parentTable (d + 2) (matrix headed)).length := by
    have bound := headState_first_before_last d a annotated entry.visible entry.state
    have nonempty := headState_nonempty d a annotated entry.visible entry.state
    change entry.state.length ≤ headed.length - 1 at bound
    change 0 < headed.length at nonempty
    rw [table_length]
    omega
  rw [← Parents.parent_prefix_eq (table_prefix extended) j entry.state.length inside,
    headState_first_parents entry.state sound.coherent sound.valid sound.view
      entry.coordinates entry.attachments room, representative_eq_point sound.view]

theorem Entry.Sound.first_parent_in {d : Nat} {entry : Entry d} {state : State d}
    (sound : entry.Sound) (extended : entry.result <+: state) {j : Nat} (room : j < d) :
    Parents.parent (BMS.parentTable (d + 2) (matrix state)) j entry.state.length =
      ((Parents.label d entry.source entry.coordinates).parents[j]?.join).map (Parents.point entry.visible) := by
  have inside : entry.state.length < entry.result.length := by
    have bound := headState_first_before_last d (Parents.label d entry.source entry.coordinates)
      (Parents.annotateForests d (entry.source ++ [Parents.label d entry.source entry.coordinates]) entry.attachments)
      entry.visible entry.state
    have nonempty := headState_nonempty d (Parents.label d entry.source entry.coordinates)
      (Parents.annotateForests d (entry.source ++ [Parents.label d entry.source entry.coordinates]) entry.attachments)
      entry.visible entry.state
    have extendedHead : headState d (Parents.label d entry.source entry.coordinates)
        (Parents.annotateForests d (entry.source ++ [Parents.label d entry.source entry.coordinates]) entry.attachments)
        entry.visible entry.state <+: entry.result := by
      simp only [Entry.result, Entry.remaining, Parents.annotate, encode_split_head]
      exact encode_extends ..
    have longer := extendedHead.length_le
    omega
  exact (Parents.parent_prefix_eq (table_prefix extended) j entry.state.length
    (by rwa [table_length])).symm.trans (sound.first_parent room)

theorem standard_entry_first_parent {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {entry : Entry d}
    (member : entry ∈ entries d e [] [] [] [] []) {j : Nat} (room : j < d) :
    Parents.parent (BMS.parentTable (d + 2) (fromSource d e)) j entry.state.length =
      ((Parents.label d entry.source entry.coordinates).parents[j]?.join).map (Parents.point entry.visible) :=
  (standard_entries_sound positive standard entry member).first_parent_in
    (entries_execution d e [] [] [] [] [] entry member).resultPrefix room

theorem Entry.OriginAt.parent_map {d : Nat} {earlier later : Entry d} {root j : Nat}
    (origin : earlier.OriginAt later.source later.visible later.owners later.materials later.state root)
    (sound : earlier.Sound) (inside : root < later.source.length) :
    ((Parents.label d earlier.source earlier.coordinates).parents[j]?.join).map (Parents.point earlier.visible) =
      (Parents.parent later.source j root).map (Parents.point later.visible) := by
  have parentSame : (Parents.label d earlier.source earlier.coordinates).parents[j]?.join =
      Parents.parent later.source j root := by
    rw [origin.labelEq]
    simp only [Parents.parent, List.getElem?_eq_getElem inside, Option.bind_some, Option.getD_some]
  cases selected : (Parents.label d earlier.source earlier.coordinates).parents[j]?.join with
  | none => simp only [← parentSame, selected, Option.map_none]
  | some p =>
    have bound := Parents.label_parent_bound d earlier.source earlier.coordinates j p selected
    have vBound : p < earlier.visible.length := by rw [sound.view.length]; exact bound
    have initial : earlier.visible <+: later.visible := by rw [origin.visibleEq]; exact List.take_prefix _ _
    obtain ⟨extra, shape⟩ := initial
    rw [← parentSame, selected]
    simp only [Option.map_some]
    rw [← shape]
    simp only [Parents.point, List.getElem?_append_left vBound]

/-- Once a target pair is assigned its genuine visible source origin,
equality of its numerical parents reflects exactly to source parents. -/
theorem standard_entry_shared_parent_reflect {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {earlier later : Entry d}
    (oldMember : earlier ∈ entries d e [] [] [] [] [])
    (newMember : later ∈ entries d e [] [] [] [] []) {root j : Nat}
    (origin : earlier.OriginAt later.source later.visible later.owners later.materials later.state root)
    (inside : root < later.source.length) (room : j < d)
    (same : Parents.parent (BMS.parentTable (d + 2) (fromSource d e)) j earlier.state.length =
      Parents.parent (BMS.parentTable (d + 2) (fromSource d e)) j later.state.length) :
    Parents.parent later.source j root = (Parents.label d later.source later.coordinates).parents[j]?.join := by
  have oldSound := standard_entries_sound positive standard earlier oldMember
  have newSound := standard_entries_sound positive standard later newMember
  rw [standard_entry_first_parent positive standard oldMember room,
    standard_entry_first_parent positive standard newMember room, origin.parent_map oldSound inside] at same
  cases oldParent : Parents.parent later.source j root with
  | none =>
    cases newParent : (Parents.label d later.source later.coordinates).parents[j]?.join with
    | none => rfl
    | some q =>
      simp only [oldParent, newParent, Option.map_none, Option.map_some] at same
      cases same
  | some p =>
    cases newParent : (Parents.label d later.source later.coordinates).parents[j]?.join with
    | none =>
      simp only [oldParent, newParent, Option.map_none, Option.map_some] at same
      cases same
    | some q =>
      have pBound : p < later.source.length := by
        have earlierParent := Parents.parent_earlier newSound.valid oldParent
        omega
      have qBound := Parents.label_parent_bound d later.source later.coordinates j q newParent
      have points : Parents.point later.visible p = Parents.point later.visible q := by
        simpa only [oldParent, newParent, Option.map_some, Option.some.injEq] using same
      have indices := congrArg later.visible.idxOf points
      rw [newSound.view.idxOf_point pBound, newSound.view.idxOf_point qBound] at indices
      exact congrArg some indices

end BTnSSBMS.Encoder
