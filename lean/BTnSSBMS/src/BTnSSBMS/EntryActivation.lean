import BTnSSBMS.EntryAncestry

/-!
Exact numerical ancestry and activation at actual first-output entries.
The backward direction uses the newly proved visible-origin recovery;
the forward direction follows the actual auxiliary fiber and computed
first parent. Neither direction is assumed of a numerical view.
-/
namespace BTnSSBMS.Encoder

theorem Entry.first_lt_result (entry : Entry d) : entry.state.length < entry.result.length := by
  let a := Parents.label d entry.source entry.coordinates
  let annotated := Parents.annotateForests d (entry.source ++ [a]) entry.attachments
  let headed := headState d a annotated entry.visible entry.state
  have before := headState_first_before_last d a annotated entry.visible entry.state
  have nonempty := headState_nonempty d a annotated entry.visible entry.state
  have extended : headed <+: entry.result := by
    simp only [Entry.result, Entry.remaining, Parents.annotate, encode_split_head]
    exact encode_extends ..
  have longer := extended.length_le
  change entry.state.length ≤ headed.length - 1 at before
  change 0 < headed.length at nonempty
  omega

theorem standard_entry_ancestor_reflect {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {earlier later : Entry d}
    (oldMember : earlier ∈ entries d e [] [] [] [] [])
    (newMember : later ∈ entries d e [] [] [] [] []) {root j : Nat}
    (origin : earlier.OriginAt later.source later.visible later.owners later.materials later.state root)
    (inside : root < later.source.length) (room : j < d)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e))
      j earlier.state.length later.state.length) :
    Parents.Ancestor (later.source ++ [Parents.label d later.source later.coordinates]) j root later.source.length := by
  have oldSound := standard_entries_sound positive standard earlier oldMember
  have newSound := standard_entries_sound positive standard later newMember
  have representativeBound := newSound.view.bounded root inside
  rw [table_length] at representativeBound
  have before : earlier.state.length < later.state.length := by
    have initial := origin.beforeRepresentative
    omega
  obtain ⟨recovered, entry, bound, member, recoveredOrigin, _, position, sourcePath⟩ :=
    standard_first_head_ancestor positive standard newMember room before
      (standard_entry_numericalHead positive standard oldMember) path
  have sameRoot := origin.index_eq_of_first_eq recoveredOrigin oldSound
    (standard_entries_sound positive standard entry member) inside bound position.symm
  simpa only [sameRoot] using sourcePath

theorem standard_entry_ancestor_lift {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {earlier later : Entry d}
    (newMember : later ∈ entries d e [] [] [] [] []) {root j : Nat}
    (fiber : NumericalFiber later.state earlier.state.length (Parents.point later.visible root))
    (inside : root < later.source.length) (room : j < d)
    (path : Parents.Ancestor (later.source ++ [Parents.label d later.source later.coordinates])
      j root later.source.length) :
    Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e))
      j earlier.state.length later.state.length := by
  have sound := standard_entries_sound positive standard later newMember
  have nextValid := Parents.context_valid_append_label d later.source sound.valid later.coordinates
  obtain ⟨q, edge, prior⟩ :=
    (Parents.Ancestor.iff_parent (by omega : root ≠ later.source.length)).mp path
  rw [Parents.append_label_parent] at edge
  have qBound := Parents.label_parent_bound d later.source later.coordinates j q edge
  have sourcePath := prior.restrict (List.prefix_append _ _) nextValid qBound
  have lifted := (fiber.connected j room).trans (sound.view.lift j room root q inside qBound sourcePath)
  have extended := later.state_prefix_result.trans
    (entries_execution d e [] [] [] [] [] later newMember).resultPrefix
  apply Parents.Ancestor.up (p := Parents.point later.visible q) ?_
    (lifted.prefix (table_prefix extended))
  change Parents.parent (BMS.parentTable (d + 2) (fromSource d e)) j later.state.length =
    some (Parents.point later.visible q)
  rw [standard_entry_first_parent positive standard newMember room, edge, Option.map_some]

theorem standard_entry_ancestry_iff {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {earlier later : Entry d}
    (oldMember : earlier ∈ entries d e [] [] [] [] [])
    (newMember : later ∈ entries d e [] [] [] [] []) {root j : Nat}
    (origin : earlier.OriginAt later.source later.visible later.owners later.materials later.state root)
    (fiber : NumericalFiber later.state earlier.state.length (Parents.point later.visible root))
    (inside : root < later.source.length) (room : j < d) :
    Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e)) j earlier.state.length later.state.length ↔
      Parents.Ancestor (later.source ++ [Parents.label d later.source later.coordinates])
        j root later.source.length :=
  ⟨standard_entry_ancestor_reflect positive standard oldMember newMember origin inside room,
    standard_entry_ancestor_lift positive standard newMember fiber inside room⟩

theorem standard_entry_threshold {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {earlier later : Entry d}
    (oldMember : earlier ∈ entries d e [] [] [] [] [])
    (newMember : later ∈ entries d e [] [] [] [] []) {root cap : Nat}
    (origin : earlier.OriginAt later.source later.visible later.owners later.materials later.state root)
    (fiber : NumericalFiber later.state earlier.state.length (Parents.point later.visible root))
    (inside : root < later.source.length) (room : cap ≤ d) :
    (BMS.thresholds (BMS.parentTable (d + 2) (fromSource d e)) earlier.state.length cap)[later.state.length]?.getD 0 =
      Keys.threshold cap root (BMS.thresholds later.source root cap)
        (Parents.label d later.source later.coordinates) := by
  have sound := standard_entries_sound positive standard later newMember
  have targetBound : later.state.length < (fromSource d e).length := by
    have before := later.first_lt_result
    have longer := (entries_execution d e [] [] [] [] [] later newMember).resultPrefix.length_le
    change later.result.length ≤ (encode d (Parents.annotate d [] e) [] []).length at longer
    simpa only [fromSource, matrix, List.length_map] using Nat.lt_of_lt_of_le before longer
  have history : BMS.HistoryCorrect later.source root cap (BMS.thresholds later.source root cap) :=
    BMS.thresholdPrefix_correct sound.valid sound.coherent root cap room later.source.length
  have historyLength : (BMS.thresholds later.source root cap).length = later.source.length :=
    BMS.thresholdPrefix_length later.source root cap later.source.length
  have equivalent : ∀ j,
      j < (BMS.thresholds (BMS.parentTable (d + 2) (fromSource d e)) earlier.state.length cap)[later.state.length]?.getD 0 ↔
      j < Keys.threshold cap root (BMS.thresholds later.source root cap)
        (Parents.label d later.source later.coordinates) := by
    intro j
    rw [BMS.thresholds_ancestry (d + 2) (fromSource d e) earlier.state.length cap (by omega)
      later.state.length targetBound j,
      Keys.threshold_at_label sound.coherent sound.valid history historyLength inside room later.coordinates j]
    constructor
    · rintro ⟨cut, path⟩
      exact ⟨cut, (standard_entry_ancestry_iff positive standard oldMember newMember origin fiber inside
        (by omega : j < d)).mp path⟩
    · rintro ⟨cut, path⟩
      exact ⟨cut, (standard_entry_ancestry_iff positive standard oldMember newMember origin fiber inside
        (by omega : j < d)).mpr path⟩
  apply Nat.le_antisymm
  · apply Nat.le_of_not_gt
    intro less
    have impossible := (equivalent _).mp less
    omega
  · apply Nat.le_of_not_gt
    intro less
    have impossible := (equivalent _).mpr less
    omega

/-- The exact threshold comparison applies to every actual intermediate
target pair, for any numerical cap. The root, origins and fibers are all
constructed, rather than required as additional source-side premises. -/
theorem standard_intermediate_pair_threshold {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {a b cut : Nat}
    (rowPositive : 0 < cut) (room : cut < d) (before : a < b) (inside : b < (fromSource d e).length)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e)) (cut - 1) a b)
    (same : Parents.parent (BMS.parentTable (d + 2) (fromSource d e)) cut a =
      Parents.parent (BMS.parentTable (d + 2) (fromSource d e)) cut b) :
    ∃ earlier later root, earlier ∈ entries d e [] [] [] [] [] ∧
      later ∈ entries d e [] [] [] [] [] ∧ root < later.source.length ∧
      earlier.OriginAt later.source later.visible later.owners later.materials later.state root ∧
      earlier.state.length = a ∧ later.state.length = b ∧
      ∀ cap, cap ≤ d →
        (BMS.thresholds (BMS.parentTable (d + 2) (fromSource d e)) a cap)[b]?.getD 0 =
          Keys.threshold cap root (BMS.thresholds later.source root cap)
            (Parents.label d later.source later.coordinates) := by
  obtain ⟨earlier, later, root, oldMember, newMember, bound, origin, fiber, oldPosition, newPosition, _, _⟩ :=
    standard_intermediate_pair_source positive standard rowPositive room before inside path same
  refine ⟨earlier, later, root, oldMember, newMember, bound, origin, oldPosition, newPosition, ?_⟩
  intro cap capBound
  simpa only [oldPosition, newPosition] using
    standard_entry_threshold positive standard oldMember newMember origin fiber bound capBound

end BTnSSBMS.Encoder
