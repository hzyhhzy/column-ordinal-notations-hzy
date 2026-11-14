import BTnSSBMS.EntryActivation
import BTnSSBMS.TargetPairControl

/-!
Numerical values of actual first outputs under intermediate rebasing.
The root's low rows become the destination's real encoded values; high
rows retain the old values. No equality of absolute source and target
coordinates is assumed. Whole internal block transport is separate.
-/
namespace BTnSSBMS.Encoder

theorem encode_first_numerical_value (d : Nat) (a : ParentLabel) (hs : Forests ParentLabel)
    (tail : ParentExpr) (visible : List Nat) (state : State d) {j : Nat} (room : j < d) :
    Parents.reading (BMS.parentTable (d + 2) (matrix (encode d (.cons a hs tail) visible state)))
      j state.length = vector state visible a j := by
  simp only [encode]
  split
  next bound found =>
    rw [← Parents.reading_prefix (table_prefix (encode_extends ..)) j state.length
      (by rw [table_length, emit_length]; omega)]
    exact emitted_numerical_value _ _ _ _ _ j room
  next fresh =>
    let u := vector state visible a
    let key := Keys.ofColumn d visible.length a hs
    let below := smaller (frameAt state (representative visible a (d - 1))) key
    let c := (base below).height
    let first := emit state u (c + 1) 1 []
    let guarded := emit first (fun k => u k + 1) (c + 2) 2 []
    let forests := encodeForests d hs visible u c below guarded
    let closed := emit forests (fun k => u k + 1) (c + 2) 0
      (below ++ [⟨key, c + 2, some forests.length, some state.length⟩])
    have extended : first <+: encode d tail (visible ++ [forests.length]) closed :=
      (emit_extends ..).trans ((encodeForests_extends ..).trans ((emit_extends ..).trans (encode_extends ..)))
    rw [← Parents.reading_prefix (table_prefix extended) j state.length
      (by rw [table_length]; dsimp only [first]; rw [emit_length]; omega)]
    exact emitted_numerical_value state u (c + 1) 1 [] j room

theorem Entry.first_reading_in {d : Nat} (entry : Entry d) {state : State d}
    (extended : entry.result <+: state) {j : Nat} (room : j < d) :
    Parents.reading (BMS.parentTable (d + 2) (matrix state)) j entry.state.length =
      vector entry.state entry.visible (Parents.label d entry.source entry.coordinates) j := by
  rw [← Parents.reading_prefix (table_prefix extended) j entry.state.length
    (by rw [table_length]; exact entry.first_lt_result)]
  exact encode_first_numerical_value d _ _ _ entry.visible entry.state room

theorem vector_row_shared_prefix {d : Nat} {source : ParentContext}
    {visible nextVisible : List Nat} {state next : State d}
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (visiblePrefix : visible <+: nextVisible) (statePrefix : state <+: next)
    (coordinates : List Nat) (newA : ParentLabel) (j : Nat)
    (same : newA.parents[j]?.join = (Parents.label d source coordinates).parents[j]?.join) :
    vector next nextVisible newA j = vector state visible (Parents.label d source coordinates) j := by
  obtain ⟨visibleExtra, rfl⟩ := visiblePrefix
  obtain ⟨stateExtra, rfl⟩ := statePrefix
  simp only [vector, representative, same]
  cases selected : (Parents.label d source coordinates).parents[j]?.join with
  | none => rfl
  | some p =>
    have inside := Parents.label_parent_bound d source coordinates j p selected
    have visibleInside : p < visible.length := by rw [view.length]; exact inside
    have bounded : Parents.point visible p < state.length := by
      simpa only [table_length] using view.bounded p inside
    have lookup : visible[p]? = some (Parents.point visible p) := by
      simp only [Parents.point, List.getElem?_eq_getElem visibleInside, Option.getD_some]
    simp only [Option.bind_some, List.getElem?_append_left visibleInside, lookup]
    simp only [List.getElem?_append_left bounded]

theorem Entry.OriginAt.partial_rebase_vector {d : Nat} {earlier later : Entry d} {root cut : Nat}
    (origin : earlier.OriginAt later.source later.visible later.owners later.materials later.state root)
    (oldSound : earlier.Sound) (newSound : later.Sound)
    (positive : 0 < cut) (room : cut < d) (inside : root < later.source.length)
    (path : Parents.Ancestor (later.source ++ [Parents.label d later.source later.coordinates])
      (cut - 1) root later.source.length)
    (same : (Parents.label d later.source later.coordinates).parents[cut]?.join =
      Parents.parent later.source cut root) (j : Nat) (row : j < d) :
    let delta := (List.range cut).map
      (fun k => later.coordinates[k]?.getD 0 - earlier.coordinates[k]?.getD 0)
    vector later.state later.visible
      (Parents.label d later.source (Source.shift earlier.coordinates cut delta 1)) j =
      if j < cut then vector later.state later.visible (Parents.label d later.source later.coordinates) j
      else vector earlier.state earlier.visible (Parents.label d earlier.source earlier.coordinates) j := by
  dsimp only
  have width : (later.source[root]?.getD default).coordinates.length = d := by
    rw [← origin.coordinates]
    exact oldSound.legal.1
  have values := Source.partial_rebase_head_values newSound.coherent later.coordinates positive room inside path width
  rw [← origin.coordinates] at values
  have parents := Parents.partial_rebase_head_parents newSound.coherent newSound.valid newSound.unit
    later.coordinates _ newSound.legal.2.1 room inside same values.1 values.2 j row
  by_cases low : j < cut
  · simp only [low, if_true] at parents ⊢
    simp only [vector, representative, parents]
  · simp only [low, if_false] at parents ⊢
    apply vector_row_shared_prefix oldSound.view
      (by rw [origin.visibleEq]; exact List.take_prefix _ _) origin.statePrefix _ _ j
    rw [parents, origin.labelEq, Parents.parent_getD]

theorem standard_origin_rebase_first_numeric {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {earlier later : Entry d}
    (oldMember : earlier ∈ entries d e [] [] [] [] [])
    (newMember : later ∈ entries d e [] [] [] [] []) {root cut : Nat}
    (origin : earlier.OriginAt later.source later.visible later.owners later.materials later.state root)
    (rowPositive : 0 < cut) (room : cut < d) (inside : root < later.source.length)
    (path : Parents.Ancestor (later.source ++ [Parents.label d later.source later.coordinates])
      (cut - 1) root later.source.length)
    (same : (Parents.label d later.source later.coordinates).parents[cut]?.join =
      Parents.parent later.source cut root) (j : Nat) (row : j < d) :
    let delta := (List.range cut).map
      (fun k => later.coordinates[k]?.getD 0 - earlier.coordinates[k]?.getD 0)
    let shifted := encode d (Parents.annotate d later.source
      (Source.copied d root cut delta 1 earlier.source (List.replicate root 0) earlier.remaining))
      later.visible later.state
    Parents.reading (BMS.parentTable (d + 2) (matrix shifted)) j later.state.length =
      if j < cut then Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) j later.state.length
      else Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) j earlier.state.length := by
  dsimp only
  simp only [Entry.remaining, Source.copied_at_root, Parents.annotate]
  rw [encode_first_numerical_value d _ _ _ _ _ row]
  simp only [fromSource]
  rw [earlier.first_reading_in (entries_execution d e [] [] [] [] [] earlier oldMember).resultPrefix row,
    later.first_reading_in (entries_execution d e [] [] [] [] [] later newMember).resultPrefix row]
  exact origin.partial_rebase_vector (standard_entries_sound positive standard earlier oldMember)
    (standard_entries_sound positive standard later newMember) rowPositive room inside path same j row

theorem standard_intermediate_pair_first_numeric {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {a b cut : Nat}
    (rowPositive : 0 < cut) (room : cut < d) (before : a < b) (inside : b < (fromSource d e).length)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e)) (cut - 1) a b)
    (same : Parents.parent (BMS.parentTable (d + 2) (fromSource d e)) cut a =
      Parents.parent (BMS.parentTable (d + 2) (fromSource d e)) cut b) :
    ∃ earlier later root, earlier ∈ entries d e [] [] [] [] [] ∧
      later ∈ entries d e [] [] [] [] [] ∧ root < later.source.length ∧
      earlier.OriginAt later.source later.visible later.owners later.materials later.state root ∧
      earlier.state.length = a ∧ later.state.length = b ∧
      (let delta := (List.range cut).map
        (fun k => later.coordinates[k]?.getD 0 - earlier.coordinates[k]?.getD 0)
      let shifted := encode d (Parents.annotate d later.source
        (Source.copied d root cut delta 1 earlier.source (List.replicate root 0) earlier.remaining))
        later.visible later.state
      ∀ j, j < d → Parents.reading (BMS.parentTable (d + 2) (matrix shifted)) j b =
        if j < cut then Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) j b
        else Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) j a) := by
  obtain ⟨earlier, later, root, oldMember, newMember, bound, origin, _, oldPosition, newPosition,
      sourcePath, shared⟩ :=
    standard_intermediate_pair_source positive standard rowPositive room before inside path same
  refine ⟨earlier, later, root, oldMember, newMember, bound, origin, oldPosition, newPosition, ?_⟩
  dsimp only
  intro j row
  simpa only [oldPosition, newPosition] using
    standard_origin_rebase_first_numeric positive standard oldMember newMember origin
      rowPositive room bound sourcePath shared.symm j row

end BTnSSBMS.Encoder
