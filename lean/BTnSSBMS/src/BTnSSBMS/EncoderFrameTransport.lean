import BTnSSBMS.EncoderControlTransport

/-! Final outer environments of two actual encodings. The final source
maps, numerical views and saved-frame correspondence are constructed by
the proof, not assumed for the resulting executions. -/
namespace BTnSSBMS.Encoder

private theorem context_width_append {d : Nat} {source : ParentContext} {coordinates : List Nat}
    (width : ∀ i, i < source.length → (source[i]?.getD default).coordinates.length = d)
    (headWidth : coordinates.length = d) :
    ∀ i, i < (source ++ [Parents.label d source coordinates]).length →
      ((source ++ [Parents.label d source coordinates])[i]?.getD default).coordinates.length = d := by
  intro i inside
  by_cases old : i < source.length
  · simpa only [List.getElem?_append_left old] using width i old
  · have last : i = source.length := by simp only [List.length_append, List.length_cons, List.length_nil] at inside; omega
    subst i
    simpa only [List.getElem?_concat_length, Option.getD_some, Parents.label] using headWidth

theorem encode_coupled_view (d : Nat) (e : NumericalExpr) (source target : ParentContext)
    (moved visible nextVisible owners : List Nat) (materials : List (Forests (List Nat)))
    (state next : State d) (positive : 0 < d)
    (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (targetUnit : Parents.UnitSteps d target)
    (view : Parents.NumericalView d source target moved)
    (oldView : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (newView : Parents.NumericalView d target (BMS.parentTable (d + 2) (matrix next)) nextVisible)
    (targetWidth : ∀ i, i < target.length → (target[i]?.getD default).coordinates.length = d)
    (known : VisibleMaterials d source visible owners materials state)
    (related : CoupledFrames d source target moved visible nextVisible materials state next)
    (legal : Source.FiniteLegal d source e) :
    let relocated := Source.relocate d source target moved e
    let result := encode d (Parents.annotate d source e) visible state
    let newResult := encode d (Parents.annotate d target relocated) nextVisible next
    let finalSource := BMS.parentTableAux d source (Source.labels e)
    let finalTarget := BMS.parentTableAux d target (Source.labels relocated)
    ∃ finalMoved finalVisible finalNextVisible,
      moved <+: finalMoved ∧ visible <+: finalVisible ∧ nextVisible <+: finalNextVisible ∧
      Parents.NumericalView d finalSource finalTarget finalMoved ∧
      Parents.NumericalView d finalSource (BMS.parentTable (d + 2) (matrix result)) finalVisible ∧
      Parents.NumericalView d finalTarget (BMS.parentTable (d + 2) (matrix newResult)) finalNextVisible ∧
      VisibleMaterials d finalSource finalVisible owners (materials ++ Source.outerMaterials e) result ∧
      CoupledFrames d finalSource finalTarget finalMoved finalVisible finalNextVisible
        (materials ++ Source.outerMaterials e) result newResult := by
  cases e with
  | nil =>
    refine ⟨moved, visible, nextVisible, List.prefix_refl _, List.prefix_refl _, List.prefix_refl _,
      view, oldView, newView, ?_, ?_⟩
    · simpa only [Source.outerMaterials, List.append_nil, Source.labels, BMS.parentTableAux, Parents.annotate, encode] using known
    · simpa only [Source.outerMaterials, List.append_nil, Source.labels, BMS.parentTableAux, Parents.annotate, encode, Source.relocate] using related
  | cons coordinates hs tail =>
    let a := Parents.label d source coordinates
    let newCoordinates := Source.relocationHead d source target moved coordinates
    let newA := Parents.label d target newCoordinates
    let newHs := Source.relocateForests d (source ++ [a]) (target ++ [newA]) (moved ++ [target.length]) hs
    let headed := headState d a (Parents.annotateForests d (source ++ [a]) hs) visible state
    let newHeaded := headState d newA (Parents.annotateForests d (target ++ [newA]) newHs) nextVisible next
    have query : MaterialQuery d source coordinates visible owners materials state hs :=
      ⟨queried_frame_inheritedMaterials known oldView coordinates, sourceCoherent, sourceValid,
        oldView, legal.1, legal.2.1, legal.2.2.2.1⟩
    have newLegal := Source.relocate_finiteLegal d (.cons coordinates hs tail) source target moved
      sourceCoherent sourceValid targetCoherent targetValid targetUnit view positive legal
    obtain ⟨finalMoved, finalVisible, finalNextVisible, movedPrefix, visiblePrefix, nextPrefix,
        finalView, finalOldView, finalNewView, finalKnown, finalRelated⟩ :=
      encode_coupled_view d tail (source ++ [a]) (target ++ [newA]) (moved ++ [target.length])
        (visible ++ [headed.length - 1]) (nextVisible ++ [newHeaded.length - 1]) owners (materials ++ [hs])
        headed newHeaded positive (Parents.coherent_append_label sourceCoherent coordinates)
        (Parents.context_valid_append_label d source sourceValid coordinates)
        (Parents.coherent_append_label targetCoherent newCoordinates)
        (Parents.context_valid_append_label d target targetValid newCoordinates)
        (Source.relocationHead_unitSteps sourceCoherent sourceValid targetCoherent targetValid targetUnit view coordinates)
        (Source.relocation_view_append sourceCoherent sourceValid targetCoherent targetValid view coordinates)
        (headState_view state positive sourceCoherent sourceValid oldView coordinates hs legal.2.2.2.1.separated)
        (headState_view next positive targetCoherent targetValid newView newCoordinates newHs newLegal.2.2.2.1.separated)
        (context_width_append targetWidth (Source.relocationHead_width d source target moved coordinates))
        (headState_materials known oldView coordinates hs legal.1 legal.2.2.2.1)
        (related.head known query newView targetCoherent targetValid targetUnit view targetWidth positive) legal.2.2.2.2
    refine ⟨finalMoved, finalVisible, finalNextVisible, (List.prefix_append _ _).trans movedPrefix,
      (List.prefix_append _ _).trans visiblePrefix, (List.prefix_append _ _).trans nextPrefix, ?_, ?_, ?_, ?_, ?_⟩
    · exact finalView
    · simpa only [Parents.annotate, Source.labels, BMS.parentTableAux, encode_split_head] using finalOldView
    · simpa only [Parents.annotate, Source.labels, Source.relocate, BMS.parentTableAux, encode_split_head] using finalNewView
    · simpa only [Parents.annotate, Source.labels, Source.outerMaterials, BMS.parentTableAux, encode_split_head,
        List.append_assoc, List.singleton_append] using finalKnown
    · simpa only [Parents.annotate, Source.labels, Source.outerMaterials, Source.relocate, BMS.parentTableAux,
        encode_split_head, List.append_assoc, List.singleton_append] using finalRelated

end BTnSSBMS.Encoder
