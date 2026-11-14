import BTnSSBMS.HWSplice
import BTnSSBMS.RelocationOrder

/-! HW is preserved by the actual contextual numerical copying. The
comparison theorem is invoked with the real common entry of sibling forests. -/
namespace BTnSSBMS.Source

theorem relocateForests_bounded (d : Nat) (hs : Forests (List Nat)) (bound : NumericalExpr)
    (source target : ParentContext) (visible : List Nat)
    (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (view : Parents.NumericalView d source target visible) (owner : Nat)
    (legal : FiniteLegalForests d source owner hs) (boundLegal : FiniteLegal d source bound)
    (bounded : ForestsLE hs bound) :
    ForestsLE (relocateForests d source target visible hs) (relocate d source target visible bound) := by
  cases hs with
  | nil => rw [relocateForests]; trivial
  | cons h rest =>
    rw [relocateForests]
    refine ⟨?_, relocateForests_bounded d rest bound source target visible sourceCoherent sourceValid
      targetCoherent targetValid view owner legal.2.2 boundLegal bounded.2⟩
    unfold ExprLE
    rw [relocate_compare d h bound source target visible sourceCoherent sourceValid targetCoherent targetValid
      view legal.2.1 boundLegal]
    exact bounded.1

mutual
  theorem relocate_HW (d : Nat) (e : NumericalExpr) (source target : ParentContext) (visible : List Nat)
      (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
      (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
      (view : Parents.NumericalView d source target visible)
      (legal : FiniteLegal d source e) (ordered : HW e) : HW (relocate d source target visible e) := by
    cases e with
    | nil => rw [relocate]; trivial
    | cons a hs rest =>
      rw [relocate]
      have next := relocation_view_append sourceCoherent sourceValid targetCoherent targetValid view a
      exact ⟨relocateForests_HW d hs _ _ _ (Parents.coherent_append_label sourceCoherent a)
        (Parents.context_valid_append_label d source sourceValid a)
        (Parents.coherent_append_label targetCoherent _)
        (Parents.context_valid_append_label d target targetValid _) next (a[0]?.getD 0)
        legal.2.2.2.1 ordered.1,
        relocate_HW d rest _ _ _ (Parents.coherent_append_label sourceCoherent a)
          (Parents.context_valid_append_label d source sourceValid a)
          (Parents.coherent_append_label targetCoherent _)
          (Parents.context_valid_append_label d target targetValid _) next legal.2.2.2.2 ordered.2⟩
  theorem relocateForests_HW (d : Nat) (hs : Forests (List Nat))
      (source target : ParentContext) (visible : List Nat)
      (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
      (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
      (view : Parents.NumericalView d source target visible) (owner : Nat)
      (legal : FiniteLegalForests d source owner hs) (ordered : HWForests hs) :
      HWForests (relocateForests d source target visible hs) := by
    cases hs with
    | nil => rw [relocateForests]; trivial
    | cons h rest =>
      rw [relocateForests]
      exact ⟨relocate_HW d h source target visible sourceCoherent sourceValid targetCoherent targetValid
        view legal.2.1 ordered.1,
        relocateForests_bounded d rest h source target visible sourceCoherent sourceValid targetCoherent
          targetValid view owner legal.2.2 legal.2.1 ordered.2.1,
        relocateForests_HW d rest source target visible sourceCoherent sourceValid targetCoherent targetValid
          view owner legal.2.2 ordered.2.2⟩
end

theorem copied_HW {d : Nat} {source target : ParentContext} {visible history : List Nat}
    {root cap : Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d source target visible history root cap delta phase)
    (e : NumericalExpr) (legal : FiniteLegal d source e) (ordered : HW e) :
    HW (copied d root cap delta phase source history e) := by
  rw [← relocate_eq_copied scope e legal]
  exact relocate_HW d e source target visible scope.sourceCoherent scope.sourceValid
    scope.targetCoherent scope.targetValid scope.view legal ordered

theorem copiedForests_HW {d : Nat} {source target : ParentContext} {visible history : List Nat}
    {root cap : Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d source target visible history root cap delta phase)
    (owner : Nat) (hs : Forests (List Nat)) (legal : FiniteLegalForests d source owner hs)
    (ordered : HWForests hs) : HWForests (copiedForests d root cap delta phase source history hs) := by
  rw [← relocateForests_eq_copied scope owner hs legal]
  exact relocateForests_HW d hs source target visible scope.sourceCoherent scope.sourceValid
    scope.targetCoherent scope.targetValid scope.view owner legal ordered

theorem copied_root_HW {d : Nat} {context target : ParentContext} {a : List Nat}
    {visible : List Nat} {cap : Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d (context ++ [Parents.label d context a])
      (target ++ [Parents.label d target (shift a cap delta phase)]) visible
      (List.replicate context.length 0 ++ [cap]) context.length cap delta phase)
    (hs : Forests (List Nat)) (rest : NumericalExpr)
    (legal : FiniteLegal d context (.cons a hs rest)) (ordered : HW (.cons a hs rest)) :
    HW (copied d context.length cap delta phase context (List.replicate context.length 0) (.cons a hs rest)) := by
  rw [copied_at_root]
  exact ⟨copiedForests_HW scope (a[0]?.getD 0) hs legal.2.2.2.1 ordered.1,
    copied_HW scope rest legal.2.2.2.2 ordered.2⟩

theorem ShiftView.donationAt_HW {d root : Nat} {site : HoleSite} {target : ParentContext}
    {visible history : List Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d site.context target visible history root d delta phase)
    (legal : FiniteLegal d site.context (.cons site.terminal site.attached .nil))
    (ordered : HWForests site.attached)
    (threshold : Keys.threshold d root history (Parents.label d site.context site.terminal) = d) :
    HWForests (ascendForests (donationAt d root site) .nil none delta phase) := by
  rw [donationAt_shift scope.sourceCoherent scope.sourceValid scope.historyCorrect scope.historyLength]
  have next := scope.append site.terminal legal.1 legal.2.1
  rw [threshold] at next
  exact copiedForests_HW next (site.terminal[0]?.getD 0) _ legal.2.2.2.1.dropLast ordered.dropLast

end BTnSSBMS.Source
