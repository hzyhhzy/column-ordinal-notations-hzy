import BTnSSBMS.EntryExecution
import BTnSSBMS.SourceEncodingOrder

/-!
The comparison hypotheses at every actual execution entry are derived
from the real encoder, including its restored closing representatives.
The resulting local suffix comparison does not assume a block inequality.
-/
namespace BTnSSBMS.Encoder

mutual
  theorem entries_good (d : Nat) (e : NumericalExpr) (source : ParentContext)
      (visible owners : List Nat) (materials : List (Forests (List Nat))) (state : State d)
      (good : VisibleGood state visible) :
      ∀ entry ∈ entries d e source visible owners materials state,
        VisibleGood entry.state entry.visible := by
    cases e with
    | nil => intro entry member; simp only [entries, List.not_mem_nil] at member
    | cons coordinates hs tail =>
      let a := Parents.label d source coordinates
      let annotated := Parents.annotateForests d (source ++ [a]) hs
      let key := Keys.ofColumn d visible.length a annotated
      let frame := frameAt state (representative visible a (d - 1))
      let below := smaller frame key
      let c := (base below).height
      let u := vector state visible a
      let headed := headState d a annotated visible state
      let guarded := emit (emit state u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 []
      have innerGood : ∀ entry ∈ (match equal frame key with
          | some _ => []
          | none => forestEntries d hs source coordinates visible owners materials hs u c below guarded),
          VisibleGood entry.state entry.visible := by
        cases found : equal frame key with
        | some bound => intro entry member; simp only [List.not_mem_nil] at member
        | none =>
          exact forestEntries_good d hs source coordinates visible owners materials hs u c below guarded
            (visibleGood_extends ((emit_extends ..).trans (emit_extends ..)) good)
            (fresh_smaller_has_zero (queried_frame_has_zero state visible good a (d - 1)) key found)
      have tailGood := entries_good d tail (source ++ [a]) (visible ++ [headed.length - 1]) owners
        (materials ++ [hs]) headed (headState_good d a annotated visible state good)
      intro entry member
      simp only [entries, List.mem_cons, List.mem_append] at member
      rcases member with rfl | inner | later
      · exact good
      · exact innerGood entry inner
      · exact tailGood entry later

  theorem forestEntries_good (d : Nat) (hs : Forests (List Nat)) (source : ParentContext)
      (coordinates visible owners : List Nat) (materials : List (Forests (List Nat)))
      (ownerMaterial : Forests (List Nat)) (u : Nat → Nat) (c : Nat) (below : List Binding)
      (state : State d) (good : VisibleGood state visible) (belowGood : HasZero below) :
      ∀ entry ∈ forestEntries d hs source coordinates visible owners materials ownerMaterial u c below state,
        VisibleGood entry.state entry.visible := by
    cases hs with
    | nil => intro entry member; simp only [forestEntries, List.not_mem_nil] at member
    | cons h hs =>
      let a := Parents.label d source coordinates
      let withSlot := emit state (fun j => u j + 2) (c + 2) 0 below
      let withForest := encode d (Parents.annotate d (source ++ [a]) h) (visible ++ [state.length]) withSlot
      have innerGood := entries_good d h (source ++ [a]) (visible ++ [state.length])
        (owners ++ [source.length]) (materials ++ [ownerMaterial]) withSlot
        (visibleGood_emit state visible good _ _ _ below belowGood)
      have tailGood := forestEntries_good d hs source coordinates visible owners materials ownerMaterial
        u c below withForest
        (visibleGood_extends ((emit_extends ..).trans (encode_extends ..)) good) belowGood
      intro entry member
      simp only [forestEntries, List.mem_append] at member
      rcases member with inner | later
      · exact innerGood entry inner
      · exact tailGood entry later
end

theorem source_entries_good (d : Nat) (e : NumericalExpr) :
    ∀ entry ∈ entries d e [] [] [] [] [], VisibleGood entry.state entry.visible :=
  entries_good d e [] [] [] [] [] (by intro p member; simp at member)

theorem source_entry_framesOrdered {d : Nat} {e : NumericalExpr} {entry : Entry d}
    (member : entry ∈ entries d e [] [] [] [] []) : FramesOrdered entry.state := by
  have initial := entry.state_prefix_result.trans
    (entries_execution d e [] [] [] [] [] entry member).resultPrefix
  intro col found
  exact source_framesOrdered d e col (initial.subset found)

theorem source_entry_framesDense {d : Nat} {e : NumericalExpr} {entry : Entry d}
    (member : entry ∈ entries d e [] [] [] [] []) : FramesDense entry.state := by
  have initial := entry.state_prefix_result.trans
    (entries_execution d e [] [] [] [] [] entry member).resultPrefix
  intro col found
  exact source_framesDense d e col (initial.subset found)

theorem matrixCompare_drop_prefix {d : Nat} {state left right : State d}
    (leftPrefix : state <+: left) (rightPrefix : state <+: right) :
    matrixCompare ((matrix left).drop state.length) ((matrix right).drop state.length) =
      matrixCompare (matrix left) (matrix right) := by
  obtain ⟨xs, leftShape⟩ := matrix_extension leftPrefix
  obtain ⟨ys, rightShape⟩ := matrix_extension rightPrefix
  rw [leftShape, rightShape]
  have width : (matrix state).length = state.length := by simp only [matrix, List.length_map]
  rw [← width, List.drop_left, List.drop_left]
  exact (listCompare_common_prefix (listCompare Ord.compare) columnCompare_self _ _ _).symm

/-- The actual entering state, not a freely chosen comparison environment,
preserves all three outcomes when comparing newly encoded material. -/
theorem standard_entry_compare {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {entry : Entry d}
    (member : entry ∈ entries d e [] [] [] [] []) (left right : NumericalExpr)
    (leftLegal : Source.FiniteLegal d entry.source left)
    (rightLegal : Source.FiniteLegal d entry.source right) :
    matrixCompare
      ((matrix (encode d (Parents.annotate d entry.source left) entry.visible entry.state)).drop entry.state.length)
      ((matrix (encode d (Parents.annotate d entry.source right) entry.visible entry.state)).drop entry.state.length) =
      left.compare (listCompare Ord.compare) right := by
  rw [matrixCompare_drop_prefix (encode_extends ..) (encode_extends ..)]
  have sound := standard_entries_sound positive standard entry member
  exact encode_compare d left right entry.source entry.visible entry.state positive
    sound.coherent sound.valid sound.view (source_entry_framesOrdered member)
    (source_entry_framesDense member) (source_entries_good d e entry member) leftLegal rightLegal

end BTnSSBMS.Encoder
