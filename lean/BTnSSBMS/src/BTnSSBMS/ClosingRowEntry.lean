import BTnSSBMS.ClosingRootedEntry
import BTnSSBMS.RowRebaseValues

/-!
Numerical initialization for a real closing-root stretch. All old prefix
positions remain fixed. The final representative moves along its actual
key-row ancestor chain, so every lower-row natural subtraction is exact.
-/
namespace BTnSSBMS.Encoder

theorem fixed_prefix_root_row_values {d count : Nat} {visible nextVisible : List Nat}
    {original state next : State d} (visibleLength : visible.length = count)
    (visiblePrefix : visible <+: nextVisible) (oldExtended : original <+: state) (newExtended : original <+: next)
    (bounded : ∀ p, p < count → Parents.point visible p < original.length)
    (oldPoint newPoint j amount : Nat) (beforeRoot : original.length ≤ oldPoint)
    (rootValue : Parents.reading (BMS.parentTable (d + 2) (matrix next)) j newPoint =
      Parents.reading (BMS.parentTable (d + 2) (matrix state)) j oldPoint + amount) :
    RowRebaseValues j oldPoint amount (count + 1) (List.range count ++ [nextVisible.length])
      (visible ++ [oldPoint]) (nextVisible ++ [newPoint]) state next := by
  have fixed : RowRebaseValues j oldPoint amount count (List.range count) visible nextVisible state next := by
    intro p inside
    have vBound : p < visible.length := by omega
    have samePoint : Parents.point nextVisible p = Parents.point visible p := by
      obtain ⟨extra, rfl⟩ := visiblePrefix
      simp only [Parents.point, List.getElem?_append_left vBound]
    rw [Parents.point_range count p inside, samePoint,
      ← Parents.reading_prefix (table_prefix newExtended) j (Parents.point visible p)
        (by rw [table_length]; exact bounded p inside),
      ← Parents.reading_prefix (table_prefix oldExtended) j (Parents.point visible p)
        (by rw [table_length]; exact bounded p inside),
      rowBump_future state j oldPoint amount (Parents.point visible p) (by have := bounded p inside; omega)]
    omega
  exact fixed.append List.length_range visibleLength
    (fun p inside => by rw [Parents.point_range count p inside]; have := visiblePrefix.length_le; omega)
    oldPoint newPoint (by rw [rowBump_self]; exact rootValue)

theorem Entry.OriginAt.closing_row_values {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {earlier later : Entry d}
    (oldMember : earlier ∈ entries d e [] [] [] [] [])
    (newMember : later ∈ entries d e [] [] [] [] []) {sourceRoot : Nat}
    (origin : earlier.OriginAt later.source later.visible later.owners later.materials later.state sourceRoot)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e)) d earlier.closing later.closing)
    (j : Nat) (room : j ≤ d) :
    RowRebaseValues j earlier.closing
      (Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) j later.closing -
        Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) j earlier.closing)
      (earlier.source.length + 1) (List.range earlier.source.length ++ [later.source.length])
      (earlier.visible ++ [earlier.closing]) (later.visible ++ [later.closing]) earlier.headed later.headed := by
  have oldSound := standard_entries_sound positive standard earlier oldMember
  have newSound := standard_entries_sound positive standard later newMember
  have oldRun := earlier.headed_prefix_result.trans (entries_execution d e [] [] [] [] [] earlier oldMember).resultPrefix
  have newRun := later.headed_prefix_result.trans (entries_execution d e [] [] [] [] [] later newMember).resultPrefix
  have oldNonempty := headState_nonempty d (Parents.label d earlier.source earlier.coordinates)
    (Parents.annotateForests d (earlier.source ++ [Parents.label d earlier.source earlier.coordinates]) earlier.attachments)
    earlier.visible earlier.state
  have newNonempty := headState_nonempty d (Parents.label d later.source later.coordinates)
    (Parents.annotateForests d (later.source ++ [Parents.label d later.source later.coordinates]) later.attachments)
    later.visible later.state
  change 0 < earlier.headed.length at oldNonempty
  change 0 < later.headed.length at newNonempty
  have oldInside : earlier.closing < earlier.headed.length := by unfold Entry.closing; omega
  have newInside : later.closing < later.headed.length := by unfold Entry.closing; omega
  have rootValue : Parents.reading (BMS.parentTable (d + 2) (matrix later.headed)) j later.closing =
      Parents.reading (BMS.parentTable (d + 2) (matrix earlier.headed)) j earlier.closing +
        (Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) j later.closing -
          Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) j earlier.closing) := by
    have lower := (path.lower_row (BMS.parentTable_coherent _ _) (by omega) room).reading_le (BMS.parentTable_coherent _ _)
    rw [Parents.reading_prefix (table_prefix newRun) j later.closing (by rw [table_length]; exact newInside),
      Parents.reading_prefix (table_prefix oldRun) j earlier.closing (by rw [table_length]; exact oldInside)]
    simp only [fromSource] at lower ⊢
    omega
  have beforeRoot := headState_first_before_last d (Parents.label d earlier.source earlier.coordinates)
    (Parents.annotateForests d (earlier.source ++ [Parents.label d earlier.source earlier.coordinates]) earlier.attachments)
    earlier.visible earlier.state
  have values := fixed_prefix_root_row_values oldSound.view.length
    (by rw [origin.visibleEq]; exact List.take_prefix ..)
    (encode_extends ..) (origin.statePrefix.trans (encode_extends ..))
    (fun p inside => by simpa only [table_length] using oldSound.view.bounded p inside)
    earlier.closing later.closing j _ beforeRoot rootValue
  simpa only [newSound.view.length, Entry.headed, headState] using values

private theorem closing_saved_frame {d : Nat} {e : NumericalExpr} {entry : Entry d}
    (member : entry ∈ entries d e [] [] [] [] []) :
    frameAt (encode d (Parents.annotate d [] e) [] []) (some entry.closing) =
      frameAt entry.headed (some entry.closing) := by
  have initial := entry.headed_prefix_result.trans (entries_execution d e [] [] [] [] [] entry member).resultPrefix
  have nonempty := headState_nonempty d (Parents.label d entry.source entry.coordinates)
    (Parents.annotateForests d (entry.source ++ [Parents.label d entry.source entry.coordinates]) entry.attachments)
    entry.visible entry.state
  change 0 < entry.headed.length at nonempty
  have inside : entry.closing < entry.headed.length := by unfold Entry.closing; omega
  obtain ⟨extra, shape⟩ := initial
  rw [← shape]
  simp only [frameAt, Option.bind_some, List.getElem?_append_left inside]

theorem closing_extension_key_difference {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {earlier later : Entry d}
    (oldMember : earlier ∈ entries d e [] [] [] [] [])
    (newMember : later ∈ entries d e [] [] [] [] [])
    (before : earlier.closing < later.closing)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e)) d earlier.closing later.closing)
    {extra : List Binding}
    (shape : frameAt later.headed (some later.closing) = frameAt earlier.headed (some earlier.closing) ++ extra) :
    Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) d later.closing -
      Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) d earlier.closing = 2 * (extra.map Binding.key).length := by
  obtain ⟨other, _, otherShape, height⟩ :=
    standard_closing_frame_extension positive standard oldMember newMember before path
  rw [closing_saved_frame oldMember, closing_saved_frame newMember] at otherShape
  have lengths := congrArg List.length (otherShape.symm.trans shape)
  simp only [List.length_append, List.length_map] at lengths ⊢
  omega

/-- Both ingredients of the tail comparison are constructed together:
the root-gated pool and the actual BMS row-difference vector. Neither is
a supplied numerical coupling or an assumed globally uniform shift. -/
theorem standard_closing_rebased_entry {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {later : Entry d}
    (member : later ∈ entries d e [] [] [] [] []) {position : Nat}
    (self : SelfLatest (encode d (Parents.annotate d [] e) [] []) position)
    (before : position < later.closing)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e)) d position later.closing) :
    ∃ root earlier extra, root < later.source.length ∧ root ∉ later.owners ∧
      earlier ∈ entries d e [] [] [] [] [] ∧
      earlier.OriginAt later.source later.visible later.owners later.materials later.state root ∧
      earlier.closing = position ∧ 0 < extra.length ∧
      frameAt later.headed (some later.closing) = frameAt earlier.headed (some earlier.closing) ++ extra ∧
      Parents.NumericalView d (earlier.source ++ [Parents.label d earlier.source earlier.coordinates])
        (later.source ++ [Parents.label d later.source later.coordinates])
        (List.range earlier.source.length ++ [later.source.length]) ∧
      RootedFrames position d (earlier.source ++ [Parents.label d earlier.source earlier.coordinates])
        (later.source ++ [Parents.label d later.source later.coordinates])
        (List.range earlier.source.length ++ [later.source.length])
        (earlier.visible ++ [earlier.closing]) (later.visible ++ [later.closing])
        (earlier.materials ++ [earlier.attachments]) (extra.map Binding.key) earlier.headed later.headed ∧
      (let delta := fun j => Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) j later.closing -
        Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) j position
       delta d = 2 * (extra.map Binding.key).length ∧
       ∀ j, j < d → RowRebaseValues j position (delta j) (earlier.source.length + 1)
         (List.range earlier.source.length ++ [later.source.length])
         (earlier.visible ++ [earlier.closing]) (later.visible ++ [later.closing]) earlier.headed later.headed) := by
  obtain ⟨root, earlier, extra, inside, free, oldMember, origin, closes, nonempty, shape, view, frames⟩ :=
    standard_closing_rooted_entry positive standard member self before path
  refine ⟨root, earlier, extra, inside, free, oldMember, origin, closes, nonempty, shape, view, frames, ?_⟩
  dsimp only
  have actualPath : Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e)) d earlier.closing later.closing := by
    rwa [closes]
  constructor
  · simpa only [closes] using closing_extension_key_difference positive standard oldMember member
      (by rwa [closes]) actualPath shape
  · intro j room
    simpa only [closes] using origin.closing_row_values positive standard oldMember member actualPath j (by omega)

end BTnSSBMS.Encoder
