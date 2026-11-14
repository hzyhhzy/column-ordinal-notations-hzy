import BTnSSBMS.ClosingRootedEntry

/-!
Run the root-gated splice invariant from an actual strict P/P pair through
the entire remaining outer source. Initial numerical views, saved-frame
pairing and the insertion pool all come from the real standard execution.
This still does not compare all intervening forest columns or prove the
activation-sensitive complete-block inequality.
-/
namespace BTnSSBMS.Encoder

theorem standard_closing_tail_rooted {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {later : Entry d}
    (member : later ∈ entries d e [] [] [] [] []) {position : Nat}
    (self : SelfLatest (encode d (Parents.annotate d [] e) [] []) position)
    (before : position < later.closing)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e)) d position later.closing) :
    ∃ earlier extra, earlier ∈ entries d e [] [] [] [] [] ∧ earlier.closing = position ∧
      0 < extra.length ∧
      frameAt later.headed (some later.closing) = frameAt earlier.headed (some earlier.closing) ++ extra ∧
      (let source := earlier.source ++ [Parents.label d earlier.source earlier.coordinates]
       let target := later.source ++ [Parents.label d later.source later.coordinates]
       let moved := List.range earlier.source.length ++ [later.source.length]
       let visible := earlier.visible ++ [earlier.closing]
       let nextVisible := later.visible ++ [later.closing]
       let transported := Source.relocate d source target moved earlier.tail
       let newResult := encode d (Parents.annotate d target transported) nextVisible later.headed
       let finalSource := BMS.parentTableAux d source (Source.labels earlier.tail)
       let finalTarget := BMS.parentTableAux d target (Source.labels transported)
       ∃ finalMoved finalVisible finalNextVisible,
         moved <+: finalMoved ∧ visible <+: finalVisible ∧ nextVisible <+: finalNextVisible ∧
         Parents.NumericalView d finalSource finalTarget finalMoved ∧
         Parents.NumericalView d finalSource (BMS.parentTable (d + 2) (matrix earlier.result)) finalVisible ∧
         Parents.NumericalView d finalTarget (BMS.parentTable (d + 2) (matrix newResult)) finalNextVisible ∧
         VisibleMaterials d finalSource finalVisible earlier.owners
           (earlier.materials ++ [earlier.attachments] ++ Source.outerMaterials earlier.tail) earlier.result ∧
         RootedFrames position d finalSource finalTarget finalMoved finalVisible finalNextVisible
           (earlier.materials ++ [earlier.attachments] ++ Source.outerMaterials earlier.tail)
           (extra.map Binding.key) earlier.result newResult) := by
  obtain ⟨_, earlier, extra, _, _, oldMember, _, closes, positiveExtra, shape, relocationView, related⟩ :=
    standard_closing_rooted_entry positive standard member self before path
  have oldSound := standard_entries_sound positive standard earlier oldMember
  have newSound := standard_entries_sound positive standard later member
  have oldHeadView := headState_view earlier.state positive oldSound.coherent oldSound.valid oldSound.view
    earlier.coordinates earlier.attachments oldSound.legal.2.2.2.1.separated
  have newHeadView := headState_view later.state positive newSound.coherent newSound.valid newSound.view
    later.coordinates later.attachments newSound.legal.2.2.2.1.separated
  have oldKnown := headState_materials oldSound.materials oldSound.view earlier.coordinates earlier.attachments
    oldSound.legal.1 oldSound.legal.2.2.2.1
  have newKnown := headState_materials newSound.materials newSound.view later.coordinates later.attachments
    newSound.legal.1 newSound.legal.2.2.2.1
  have transported := encode_rooted_view position d earlier.tail
    (earlier.source ++ [Parents.label d earlier.source earlier.coordinates])
    (later.source ++ [Parents.label d later.source later.coordinates])
    (List.range earlier.source.length ++ [later.source.length])
    (earlier.visible ++ [earlier.closing]) (later.visible ++ [later.closing]) earlier.owners
    (earlier.materials ++ [earlier.attachments]) (extra.map Binding.key) earlier.headed later.headed positive
    (Parents.coherent_append_label oldSound.coherent earlier.coordinates)
    (Parents.context_valid_append_label d earlier.source oldSound.valid earlier.coordinates)
    (Parents.coherent_append_label newSound.coherent later.coordinates)
    (Parents.context_valid_append_label d later.source newSound.valid later.coordinates)
    newSound.legal.2.1 relocationView oldHeadView newHeadView
    (fun i inside => (newKnown.materialContext.legal i inside).1) oldKnown related oldSound.legal.2.2.2.2
  refine ⟨earlier, extra, oldMember, closes, positiveExtra, shape, ?_⟩
  simpa only [Entry.result, Entry.remaining, Entry.closing, Entry.headed, Parents.annotate, encode_split_head] using transported

end BTnSSBMS.Encoder
