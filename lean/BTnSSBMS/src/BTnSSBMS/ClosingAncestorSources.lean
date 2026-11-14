import BTnSSBMS.FrameAncestorRecovery

/-!
Actual key-row ancestry between restored representatives reflects into
the active source scope. A source position inside a closed forest cannot
serve as the recovered origin. Open owners are excluded by the proved
saved-frame provenance, not by chronology or a chosen inverse mapping.
-/
namespace BTnSSBMS.Encoder

/-- Recover the genuinely visible, non-owner source ancestor of a
self-registered key ancestor of a completed source entry. -/
theorem standard_closing_ancestor_source {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {later : Entry d}
    (member : later ∈ entries d e [] [] [] [] []) {position : Nat}
    (self : SelfLatest (encode d (Parents.annotate d [] e) [] []) position)
    (before : position < later.closing)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e)) d position later.closing) :
    ∃ root, root < later.source.length ∧ root ∉ later.owners ∧
      position = Parents.point later.visible root ∧
      Parents.Ancestor (later.source ++ [Parents.label d later.source later.coordinates])
        (d - 1) root later.source.length := by
  let state := encode d (Parents.annotate d [] e) [] []
  have legal := Source.standard_finiteLegal positive standard
  have sound := standard_entries_sound positive standard later member
  have initial : later.headed <+: state := later.headed_prefix_result.trans
    (entries_execution d e [] [] [] [] [] later member).resultPrefix
  have rightSelf : SelfLatest state later.closing :=
    later.closing_selfLatest.extends (entries_execution d e [] [] [] [] [] later member).resultPrefix
  obtain ⟨saved, savedLookup, b, bMember, latest⟩ := selfLatest_ancestor_binding
    (source_framesDense d e) (source_framesRealized d e)
    (source_framesAncestral d e positive legal.separated (legal.parented positive)) self rightSelf path
  have sources := headState_sources sound.materials.sources sound.view later.coordinates later.attachments
  have closingPoint : Parents.point (later.visible ++ [later.closing]) later.source.length = later.closing := by
    rw [← sound.view.length, Parents.point_append_last]
  obtain ⟨col, lookup, provenance⟩ := sources.frames later.source.length
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  change later.headed[Parents.point (later.visible ++ [later.closing]) later.source.length]? = some col at lookup
  rw [closingPoint] at lookup
  have inside := (List.getElem?_eq_some_iff.mp lookup).choose
  have globalLookup : state[later.closing]? = some col := by
    obtain ⟨extra, shape⟩ := initial
    rw [← shape, List.getElem?_append_left inside]
    exact lookup
  have sameColumn : saved = col := Option.some.inj (savedLookup.symm.trans globalLookup)
  subst saved
  obtain ⟨root, bound, free, named, ancestry⟩ := provenance b bMember position latest
  change position = Parents.point (later.visible ++ [later.closing]) root at named
  have old : root < later.source.length := by
    have notLast : root ≠ later.source.length := by
      intro equal
      rw [equal, closingPoint] at named
      omega
    simp only [List.length_append, List.length_cons, List.length_nil] at bound
    omega
  rw [Parents.point_append_old later.visible root later.closing (by rw [sound.view.length]; exact old)] at named
  exact ⟨root, old, free, named, ancestry⟩

/-- Attach the actual historical entry snapshot to the recovered source
root. The source origin is not inferred from target chronological order. -/
theorem standard_closing_ancestor_origin {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {later : Entry d}
    (member : later ∈ entries d e [] [] [] [] []) {position : Nat}
    (self : SelfLatest (encode d (Parents.annotate d [] e) [] []) position)
    (before : position < later.closing)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e)) d position later.closing) :
    ∃ root earlier, root < later.source.length ∧ root ∉ later.owners ∧
      earlier ∈ entries d e [] [] [] [] [] ∧
      earlier.OriginAt later.source later.visible later.owners later.materials later.state root ∧
      position = Parents.point later.visible root ∧
      Parents.Ancestor (later.source ++ [Parents.label d later.source later.coordinates])
        (d - 1) root later.source.length := by
  obtain ⟨root, inside, free, named, ancestry⟩ :=
    standard_closing_ancestor_source positive standard member self before path
  obtain ⟨earlier, oldMember, _, origin⟩ :=
    standard_visible_entry_origin positive standard member inside
  exact ⟨root, earlier, inside, free, oldMember, origin, named, ancestry⟩

/-- The P/P case of an actual highest-row pair has a genuine non-owner
source root. No source block-order condition is required. -/
theorem standard_top_closing_pair_source {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {earlier later : Entry d}
    (oldMember : earlier ∈ entries d e [] [] [] [] [])
    (newMember : later ∈ entries d e [] [] [] [] [])
    (before : earlier.closing < later.closing)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e)) d earlier.closing later.closing) :
    ∃ root, root < later.source.length ∧ root ∉ later.owners ∧
      earlier.closing = Parents.point later.visible root ∧
      Parents.Ancestor (later.source ++ [Parents.label d later.source later.coordinates])
        (d - 1) root later.source.length :=
  standard_closing_ancestor_source positive standard newMember
    (earlier.closing_selfLatest.extends (entries_execution d e [] [] [] [] [] earlier oldMember).resultPrefix)
    before path

end BTnSSBMS.Encoder
