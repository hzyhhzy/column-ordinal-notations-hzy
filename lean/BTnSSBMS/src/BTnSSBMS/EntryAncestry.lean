import BTnSSBMS.EntryOriginOrder

/-!
Reflection of actual numerical ancestry into the visible source context.
Auxiliary fibers are contracted first; recursion then follows the source
parent, whose index strictly decreases. This rules out a hidden source
head from a previously closed sibling forest. All entry origins come
from the actual execution trace, not from a chosen inverse to a view.
-/
namespace BTnSSBMS.Encoder

theorem NumericalClasses.intermediate_pair_numericalHeads {state : State d} {heads : List Nat}
    (classes : NumericalClasses state heads) {a b j : Nat}
    (positive : 0 < j) (room : j < d) (before : a < b) (inside : b < state.length)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) (j - 1) a b)
    (same : Parents.parent (BMS.parentTable (d + 2) (matrix state)) j a =
      Parents.parent (BMS.parentTable (d + 2) (matrix state)) j b) :
    NumericalHead state a ∧ NumericalHead state b := by
  rcases classes a (by omega) with ⟨_, aHead⟩ | aAux
  · rcases classes b inside with ⟨_, bHead⟩ | bAux
    · exact ⟨aHead, bHead⟩
    · exact False.elim (numericalHead_auxiliary_distinct_parent aHead bAux room same)
  · rcases classes b inside with ⟨_, bHead⟩ | bAux
    · exact False.elim (numericalHead_auxiliary_distinct_parent bHead aAux room same.symm)
    · exact False.elim
        (numericalAuxiliary_same_parent_not_ancestor aAux bAux positive room (by omega) same path)

theorem standard_visible_head_ancestor {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {later : Entry d}
    (laterMember : later ∈ entries d e [] [] [] [] []) {j p i : Nat}
    (room : j < d) (inside : i < later.source.length)
    (head : NumericalHead (encode d (Parents.annotate d [] e) [] []) p)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e)) j p
      (Parents.point later.visible i)) :
    ∃ root earlier, root < later.source.length ∧ earlier ∈ entries d e [] [] [] [] [] ∧
      earlier.OriginAt later.source later.visible later.owners later.materials later.state root ∧
      NumericalFiber later.state earlier.state.length (Parents.point later.visible root) ∧
      earlier.state.length = p ∧ Parents.Ancestor later.source j root i := by
  have laterSound := standard_entries_sound positive standard later laterMember
  have known := standard_entries_fibers positive standard later laterMember
  have extended := later.state_prefix_result.trans
    (entries_execution d e [] [] [] [] [] later laterMember).resultPrefix
  induction i using Nat.strongRecOn with
  | ind i ih =>
    obtain ⟨entry, member, origin, fiber⟩ := known.origins i inside
    have sound := standard_entries_sound positive standard entry member
    have reduced := (fiber.extends extended).head_ancestor room head path
    by_cases first : p = entry.state.length
    · exact ⟨i, entry, inside, member, origin, fiber, first.symm, .refl _⟩
    · obtain ⟨q, edge, prior⟩ := (Parents.Ancestor.iff_parent first).mp reduced
      have parentMap := (standard_entry_first_parent positive standard member room).trans
        (origin.parent_map sound inside)
      change Parents.parent (BMS.parentTable (d + 2) (fromSource d e)) j entry.state.length = some q at edge
      rw [parentMap] at edge
      cases selected : Parents.parent later.source j i with
      | none => simp only [selected, Option.map_none] at edge; cases edge
      | some k =>
        have previous : k < i := Parents.parent_earlier laterSound.valid selected
        have qEq : Parents.point later.visible k = q := by
          simpa only [selected, Option.map_some, Option.some.injEq] using edge
        rw [← qEq] at prior
        obtain ⟨root, earlier, bound, oldMember, oldOrigin, oldFiber, position, sourcePath⟩ :=
          ih k previous (by omega) prior
        exact ⟨root, earlier, bound, oldMember, oldOrigin, oldFiber, position, .up selected sourcePath⟩

theorem standard_first_head_ancestor {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {later : Entry d}
    (laterMember : later ∈ entries d e [] [] [] [] []) {j p : Nat}
    (room : j < d) (before : p < later.state.length)
    (head : NumericalHead (encode d (Parents.annotate d [] e) [] []) p)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e)) j p later.state.length) :
    ∃ root earlier, root < later.source.length ∧ earlier ∈ entries d e [] [] [] [] [] ∧
      earlier.OriginAt later.source later.visible later.owners later.materials later.state root ∧
      NumericalFiber later.state earlier.state.length (Parents.point later.visible root) ∧
      earlier.state.length = p ∧
      Parents.Ancestor (later.source ++ [Parents.label d later.source later.coordinates])
        j root later.source.length := by
  obtain ⟨q, edge, prior⟩ := (Parents.Ancestor.iff_parent (by omega : p ≠ later.state.length)).mp path
  rw [standard_entry_first_parent positive standard laterMember room] at edge
  cases selected : (Parents.label d later.source later.coordinates).parents[j]?.join with
  | none => simp only [selected, Option.map_none] at edge; cases edge
  | some k =>
    have bound := Parents.label_parent_bound d later.source later.coordinates j k selected
    have qEq : Parents.point later.visible k = q := by
      simpa only [selected, Option.map_some, Option.some.injEq] using edge
    rw [← qEq] at prior
    obtain ⟨root, earlier, inside, member, origin, fiber, position, sourcePath⟩ :=
      standard_visible_head_ancestor positive standard laterMember room bound head prior
    refine ⟨root, earlier, inside, member, origin, fiber, position, Parents.Ancestor.up (p := k) ?_ ?_⟩
    · simpa only [Parents.append_label_parent] using selected
    · exact sourcePath.prefix (List.prefix_append _ _)

/-- Every intermediate numerical SB pair has the required same-scope
source ancestor and shared cut parent. No source root is supplied by the
caller, and chronological precedence is not substituted for visibility. -/
theorem standard_intermediate_pair_source {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {a b j : Nat}
    (rowPositive : 0 < j) (room : j < d) (before : a < b) (inside : b < (fromSource d e).length)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e)) (j - 1) a b)
    (same : Parents.parent (BMS.parentTable (d + 2) (fromSource d e)) j a =
      Parents.parent (BMS.parentTable (d + 2) (fromSource d e)) j b) :
    ∃ earlier later root, earlier ∈ entries d e [] [] [] [] [] ∧
      later ∈ entries d e [] [] [] [] [] ∧ root < later.source.length ∧
      earlier.OriginAt later.source later.visible later.owners later.materials later.state root ∧
      NumericalFiber later.state earlier.state.length (Parents.point later.visible root) ∧
      earlier.state.length = a ∧ later.state.length = b ∧
      Parents.Ancestor (later.source ++ [Parents.label d later.source later.coordinates])
        (j - 1) root later.source.length ∧
      Parents.parent later.source j root = (Parents.label d later.source later.coordinates).parents[j]?.join := by
  have heads := standard_intermediate_pair_heads positive standard rowPositive room before inside path same
  have headTypes := (standard_numericalClasses positive standard).intermediate_pair_numericalHeads
    rowPositive room before (by simpa only [fromSource, matrix, List.length_map] using inside) path same
  obtain ⟨later, laterMember, laterPosition, _⟩ := standard_head_entry positive standard heads.2
  obtain ⟨root, earlier, bound, earlierMember, origin, fiber, earlierPosition, sourcePath⟩ :=
    standard_first_head_ancestor positive standard laterMember (by omega : j - 1 < d)
      (by omega) headTypes.1 (by simpa only [laterPosition] using path)
  have shared := standard_entry_shared_parent_reflect positive standard earlierMember laterMember
    origin bound room (by simpa only [earlierPosition, laterPosition] using same)
  exact ⟨earlier, later, root, earlierMember, laterMember, bound, origin, fiber,
    earlierPosition, laterPosition, sourcePath, shared⟩

end BTnSSBMS.Encoder
