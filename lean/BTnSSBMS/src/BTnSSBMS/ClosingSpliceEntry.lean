import BTnSSBMS.ClosingRekey
import BTnSSBMS.EncoderSpliceTransport

/-!
Initialize the splice invariant at genuine closing representatives.
All earlier visible positions use their immutable original frames; only
the moved root gets the nonempty interval from the actual key-ancestor
chain. No initial frame pairing is assumed by the standard theorem.
-/
namespace BTnSSBMS.Encoder

private theorem frameAt_prefix_position {state next : State d} (initial : state <+: next)
    {p : Nat} (inside : p < state.length) : frameAt next (some p) = frameAt state (some p) := by
  obtain ⟨extra, rfl⟩ := initial
  simp only [frameAt, Option.bind_some, List.getElem?_append_left inside]

theorem fixed_prefix_spliced_frames {d : Nat} {source target oldOutput : ParentContext}
    {visible nextVisible owners : List Nat} {materials : List (Forests (List Nat))}
    {original state next : State d} {pool : List Key}
    (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (unit : Parents.UnitSteps d source) (initial : source <+: target)
    (known : VisibleMaterials d source visible owners materials original)
    (oldView : Parents.NumericalView d source oldOutput visible)
    (visiblePrefix : visible <+: nextVisible) (newLength : nextVisible.length = target.length)
    (oldExtended : original <+: state) (newExtended : original <+: next)
    (a newA : ParentLabel) (hs : Forests (List Nat)) (oldPoint newPoint : Nat)
    (oldInside : oldPoint < state.length) (newInside : newPoint < next.length)
    (added : Nonempty (RekeyedInsertion
      (fun b => (rekeyBinding d (source ++ [a]) (target ++ [newA]) (visible ++ [oldPoint])
        (List.range source.length ++ [target.length]) (materials ++ [hs]) b).key)
      (frameAt state (some oldPoint)) (frameAt next (some newPoint)) pool)) :
    SplicedFrames d (source ++ [a]) (target ++ [newA]) (List.range source.length ++ [target.length])
      (visible ++ [oldPoint]) (nextVisible ++ [newPoint]) (materials ++ [hs]) pool state next := by
  intro i inside
  by_cases old : i < source.length
  · obtain ⟨col, lookup, payload⟩ := known.frames i old
    have keys := fun b member => rekeyBinding_fixed_prefix coherent valid unit known.materialContext oldView
      (List.prefix_append source [a]) (initial.trans (List.prefix_append target [newA]))
      (List.prefix_append visible [oldPoint])
      (List.prefix_append (List.range source.length) [target.length]) (List.prefix_append materials [hs])
      b (payload b member)
    have pair : RekeyedInsertion
        (fun b => (rekeyBinding d (source ++ [a]) (target ++ [newA]) (visible ++ [oldPoint])
          (List.range source.length ++ [target.length]) (materials ++ [hs]) b).key) col.frame col.frame pool :=
      ⟨col.frame.map Binding.key, [], [], by rw [List.append_nil]; exact List.map_congr_left keys,
        by simp only [List.append_nil], List.nil_sublist pool⟩
    have visibleInside : i < visible.length := by rw [oldView.length]; exact old
    have nextInside : i < nextVisible.length := Nat.lt_of_lt_of_le visibleInside visiblePrefix.length_le
    have point : Parents.point nextVisible i = Parents.point visible i := by
      obtain ⟨extra, rfl⟩ := visiblePrefix
      simp only [Parents.point, List.getElem?_append_left visibleInside]
    have oldLookup : state[Parents.point visible i]? = some col := by
      obtain ⟨extra, rfl⟩ := oldExtended
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp lookup).choose]
      exact lookup
    have newLookup : next[Parents.point visible i]? = some col := by
      obtain ⟨extra, rfl⟩ := newExtended
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp lookup).choose]
      exact lookup
    refine ⟨col, col, ?_, ?_, ⟨pair⟩⟩
    · rw [Parents.point_append_old visible i oldPoint visibleInside]
      exact oldLookup
    · rw [Parents.point_append_old (List.range source.length) i target.length (by simpa using old),
        Parents.point_range source.length i old, Parents.point_append_old nextVisible i newPoint nextInside, point]
      exact newLookup
  · have last : i = source.length := by
      simp only [List.length_append, List.length_cons, List.length_nil] at inside
      omega
    subst i
    refine ⟨state[oldPoint], next[newPoint], ?_, ?_, ?_⟩
    · rw [← oldView.length, Parents.point_append_last, List.getElem?_eq_getElem oldInside]
    · have endpoint : Parents.point (List.range source.length ++ [target.length]) source.length = target.length := by
        simpa only [List.length_range] using Parents.point_append_last (List.range source.length) target.length
      rw [endpoint, ← newLength, Parents.point_append_last, List.getElem?_eq_getElem newInside]
    · simpa only [frameAt, Option.bind_some, List.getElem?_eq_getElem oldInside,
        List.getElem?_eq_getElem newInside] using added

/-- A strict actual P/P key-ancestor pair supplies the entry relation for
the subsequent full outer execution. The finite pool consists exactly of
the extra bindings in the later root's actual saved frame. -/
theorem standard_closing_spliced_entry {d : Nat} (positive : 0 < d) {e : NumericalExpr}
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
      SplicedFrames d (earlier.source ++ [Parents.label d earlier.source earlier.coordinates])
        (later.source ++ [Parents.label d later.source later.coordinates])
        (List.range earlier.source.length ++ [later.source.length])
        (earlier.visible ++ [earlier.closing]) (later.visible ++ [later.closing])
        (earlier.materials ++ [earlier.attachments]) (extra.map Binding.key) earlier.headed later.headed := by
  obtain ⟨root, earlier, insideRoot, free, oldMember, origin, closes, _, ancestry⟩ :=
    standard_closing_pair_origin positive standard member self before path
  have oldSound := standard_entries_sound positive standard earlier oldMember
  have newSound := standard_entries_sound positive standard later member
  have rootEq : earlier.source.length = root := by
    rw [origin.sourceEq, List.length_take, Nat.min_eq_left (by omega)]
  have oldPrefix : earlier.source <+: later.source := by rw [origin.sourceEq]; exact List.take_prefix ..
  have oldVisible : earlier.visible <+: later.visible := by rw [origin.visibleEq]; exact List.take_prefix ..
  let context := later.source ++ [Parents.label d later.source later.coordinates]
  have contextLength : context.length = later.source.length + 1 := by simp [context]
  have oldContext : earlier.source ++ [Parents.label d earlier.source earlier.coordinates] =
      context.take (root + 1) := by
    rw [origin.labelEq, origin.sourceEq]
    simp only [context, List.take_append_of_le_length (by omega : root + 1 ≤ later.source.length)]
    rw [List.getElem?_eq_getElem insideRoot, Option.getD_some, List.take_succ_eq_append_getElem insideRoot]
  have contextCoherent := Parents.coherent_append_label newSound.coherent later.coordinates
  have contextValid := Parents.context_valid_append_label d later.source newSound.valid later.coordinates
  have contextUnit := newSound.legal.2.1
  have rootBefore : root < context.length - 1 := by rw [contextLength, Nat.add_sub_cancel]; exact insideRoot
  have rootPath : Parents.Ancestor context (d - 1) root (context.length - 1) := by
    simpa only [contextLength, Nat.add_sub_cancel] using ancestry
  have lastWidth : (context[context.length - 1]?.getD default).coordinates.length = d := by
    rw [contextLength, Nat.add_sub_cancel]
    simp only [context, List.getElem?_concat_length, Option.getD_some, Parents.label]
    exact newSound.legal.1
  have oldHeadView := headState_view earlier.state positive oldSound.coherent oldSound.valid oldSound.view
    earlier.coordinates earlier.attachments oldSound.legal.2.2.2.1.separated
  have oldKnown := headState_materials oldSound.materials oldSound.view earlier.coordinates earlier.attachments
    oldSound.legal.1 oldSound.legal.2.2.2.1
  change VisibleMaterials d (earlier.source ++ [Parents.label d earlier.source earlier.coordinates])
    (earlier.visible ++ [earlier.closing]) earlier.owners (earlier.materials ++ [earlier.attachments]) earlier.headed at oldKnown
  have oldBound : earlier.closing < earlier.headed.length := by
    have nonempty := headState_nonempty d (Parents.label d earlier.source earlier.coordinates)
      (Parents.annotateForests d (earlier.source ++ [Parents.label d earlier.source earlier.coordinates]) earlier.attachments)
      earlier.visible earlier.state
    change 0 < earlier.headed.length at nonempty
    exact Nat.sub_lt nonempty (by decide)
  have newBound : later.closing < later.headed.length := by
    have nonempty := headState_nonempty d (Parents.label d later.source later.coordinates)
      (Parents.annotateForests d (later.source ++ [Parents.label d later.source later.coordinates]) later.attachments)
      later.visible later.state
    change 0 < later.headed.length at nonempty
    exact Nat.sub_lt nonempty (by decide)
  obtain ⟨extra, positiveExtra, frameShape, _⟩ := standard_closing_frame_extension positive standard oldMember member
    (by rwa [closes]) (by rwa [closes])
  have oldRun := earlier.headed_prefix_result.trans (entries_execution d e [] [] [] [] [] earlier oldMember).resultPrefix
  have newRun := later.headed_prefix_result.trans (entries_execution d e [] [] [] [] [] later member).resultPrefix
  rw [frameAt_prefix_position oldRun oldBound, frameAt_prefix_position newRun newBound] at frameShape
  obtain ⟨col, lookup, payload⟩ := oldKnown.frames earlier.source.length (by simp)
  rw [← oldSound.view.length, Parents.point_append_last] at lookup
  have payloadFrame : FrameMaterials d (earlier.source ++ [Parents.label d earlier.source earlier.coordinates])
      (earlier.visible ++ [earlier.closing]) (earlier.materials ++ [earlier.attachments])
      (frameAt earlier.headed (some earlier.closing)) := by
    simpa only [frameAt, Option.bind_some, lookup] using payload
  have stable : ∀ b ∈ frameAt earlier.headed (some earlier.closing),
      (rekeyBinding d (earlier.source ++ [Parents.label d earlier.source earlier.coordinates]) context
        (earlier.visible ++ [earlier.closing]) (List.range earlier.source.length ++ [later.source.length])
        (earlier.materials ++ [earlier.attachments]) b).key = b.key := by
    intro b retained
    have actualView : Parents.NumericalView d (context.take (root + 1))
        (BMS.parentTable (d + 2) (matrix earlier.headed)) (earlier.visible ++ [earlier.closing]) := by
      rw [← oldContext]
      exact oldHeadView
    have actualMaterial : Source.MaterialContext d (context.take (root + 1))
        (earlier.materials ++ [earlier.attachments]) := by rw [← oldContext]; exact oldKnown.materialContext
    have actualBinding : BindingMaterial d (context.take (root + 1)) (earlier.visible ++ [earlier.closing])
        (earlier.materials ++ [earlier.attachments]) b := by rw [← oldContext]; exact payloadFrame b retained
    have unchanged := rekeyBinding_stretched contextCoherent contextValid contextUnit positive rootBefore rootPath
      lastWidth actualMaterial actualView b actualBinding
    rw [← oldContext, contextLength, Nat.add_sub_cancel, ← rootEq] at unchanged
    exact unchanged
  have rootPair : Nonempty (RekeyedInsertion
      (fun b => (rekeyBinding d (earlier.source ++ [Parents.label d earlier.source earlier.coordinates]) context
        (earlier.visible ++ [earlier.closing]) (List.range earlier.source.length ++ [later.source.length])
        (earlier.materials ++ [earlier.attachments]) b).key)
      (frameAt earlier.headed (some earlier.closing)) (frameAt later.headed (some later.closing))
      (extra.map Binding.key)) := by
    refine ⟨⟨(frameAt earlier.headed (some earlier.closing)).map Binding.key, extra.map Binding.key, [], ?_, ?_,
      List.Sublist.refl _⟩⟩
    · rw [List.append_nil]
      exact List.map_congr_left stable
    · rw [List.append_nil, frameShape, List.map_append]
  have relocationView := Parents.ancestor_to_last_view contextCoherent contextValid positive rootBefore rootPath
  rw [← oldContext, contextLength, Nat.add_sub_cancel, ← rootEq] at relocationView
  refine ⟨root, earlier, extra, insideRoot, free, oldMember, origin, closes, positiveExtra, frameShape,
    relocationView, ?_⟩
  exact fixed_prefix_spliced_frames oldSound.coherent oldSound.valid oldSound.unit oldPrefix oldSound.materials
    oldSound.view oldVisible newSound.view.length (encode_extends ..)
    (origin.statePrefix.trans (encode_extends ..)) _ _ earlier.attachments earlier.closing later.closing
    oldBound newBound rootPair

end BTnSSBMS.Encoder
