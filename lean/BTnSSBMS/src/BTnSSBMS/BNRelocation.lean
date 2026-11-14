import BTnSSBMS.RelocationSuffix
import BTnSSBMS.SourceBN

/-! BN is preserved by a complete ordinary numerical transport,
including all nested forests. This does not cover an inserted hole,
donation, or a comparison crossing two different copy phases. -/
namespace BTnSSBMS.Source

theorem headBN_relocate {d : Nat} {source target : ParentContext} {visible : List Nat}
    (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (targetUnit : Parents.UnitSteps d target) (view : Parents.NumericalView d source target visible)
    (positive : 0 < d) (a : List Nat) (hs : Forests (List Nat)) (rest : NumericalExpr)
    (legal : FiniteLegal d source (.cons a hs rest)) (ordered : HeadBN d source a hs rest) :
    HeadBN d target (relocationHead d source target visible a)
      (relocateForests d (source ++ [Parents.label d source a])
        (target ++ [Parents.label d target (relocationHead d source target visible a)]) (visible ++ [target.length]) hs)
      (relocate d (source ++ [Parents.label d source a])
        (target ++ [Parents.label d target (relocationHead d source target visible a)]) (visible ++ [target.length]) rest) := by
  intro index bOut ksOut tailOut found parents
  have nextView := relocation_view_append sourceCoherent sourceValid targetCoherent targetValid view a
  have nextUnit := relocationHead_unitSteps sourceCoherent sourceValid targetCoherent targetValid targetUnit view a
  obtain ⟨nextVisible, visiblePrefix, laterCoherent, laterValid, laterTargetCoherent, laterTargetValid,
      laterUnit, laterView, output⟩ := relocate_drop_entry d index rest
    (source ++ [Parents.label d source a])
    (target ++ [Parents.label d target (relocationHead d source target visible a)]) (visible ++ [target.length])
    (Parents.coherent_append_label sourceCoherent a) (Parents.context_valid_append_label d source sourceValid a)
    (Parents.coherent_append_label targetCoherent _) (Parents.context_valid_append_label d target targetValid _) nextUnit nextView
  have sourcePrefix := (List.prefix_append source [Parents.label d source a]).trans (dropContext_prefix d _ index rest)
  have targetPrefix := (List.prefix_append target [Parents.label d target (relocationHead d source target visible a)]).trans
    (dropContext_prefix d _ index (relocate d (source ++ [Parents.label d source a])
      (target ++ [Parents.label d target (relocationHead d source target visible a)]) (visible ++ [target.length]) rest))
  have positionsPrefix := (List.prefix_append visible [target.length]).trans visiblePrefix
  cases selected : drop index rest with
  | nil => rw [output, selected, relocate] at found; cases found
  | cons b ks tail =>
    have laterLegal := legal.2.2.2.2.drop index
    rw [selected] at laterLegal
    have full := output.symm.trans found
    rw [selected] at full
    have head : relocationHead d _ _ nextVisible b = bOut := (Expr.cons.inj full).1
    rw [← head] at parents
    have same := relocated_zero_parent_reflect sourcePrefix positionsPrefix laterCoherent laterValid
      targetCoherent targetValid laterTargetCoherent laterTargetValid view laterView positive a b parents
    have original := ordered index b ks tail selected same
    have comparison := relocate_sibling_blocks_compare sourcePrefix targetPrefix positionsPrefix laterCoherent laterValid
      laterTargetCoherent laterTargetValid laterUnit view laterView positive a b hs ks rest tail legal laterLegal same
    unfold ExprLE
    change (rootBlock (.cons bOut ksOut tailOut)).compare (listCompare Ord.compare)
      (rootBlock (relocate d source target visible (.cons a hs rest))) ≠ .gt
    rw [← full, comparison]
    exact original

mutual
  theorem relocate_BN (d : Nat) (e : NumericalExpr) (source target : ParentContext) (visible : List Nat)
      (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
      (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
      (targetUnit : Parents.UnitSteps d target) (view : Parents.NumericalView d source target visible)
      (positive : 0 < d) (legal : FiniteLegal d source e) (ordered : BN d source e) :
      BN d target (relocate d source target visible e) := by
    cases e with
    | nil => trivial
    | cons a hs rest =>
      have nextView := relocation_view_append sourceCoherent sourceValid targetCoherent targetValid view a
      have nextUnit := relocationHead_unitSteps sourceCoherent sourceValid targetCoherent targetValid targetUnit view a
      refine ⟨headBN_relocate sourceCoherent sourceValid targetCoherent targetValid targetUnit view positive a hs rest legal ordered.1,
        relocateForests_BN d hs _ _ _ (Parents.coherent_append_label sourceCoherent a)
          (Parents.context_valid_append_label d source sourceValid a) (Parents.coherent_append_label targetCoherent _)
          (Parents.context_valid_append_label d target targetValid _) nextUnit nextView positive (a[0]?.getD 0)
          legal.2.2.2.1 ordered.2.1,
        relocate_BN d rest _ _ _ (Parents.coherent_append_label sourceCoherent a)
          (Parents.context_valid_append_label d source sourceValid a) (Parents.coherent_append_label targetCoherent _)
          (Parents.context_valid_append_label d target targetValid _) nextUnit nextView positive legal.2.2.2.2 ordered.2.2⟩

  theorem relocateForests_BN (d : Nat) (hs : Forests (List Nat)) (source target : ParentContext) (visible : List Nat)
      (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
      (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
      (targetUnit : Parents.UnitSteps d target) (view : Parents.NumericalView d source target visible)
      (positive : 0 < d) (owner : Nat) (legal : FiniteLegalForests d source owner hs)
      (ordered : BNForests d source hs) :
      BNForests d target (relocateForests d source target visible hs) := by
    cases hs with
    | nil => trivial
    | cons h hs =>
      exact ⟨relocate_BN d h source target visible sourceCoherent sourceValid targetCoherent targetValid targetUnit view
        positive legal.2.1 ordered.1,
        relocateForests_BN d hs source target visible sourceCoherent sourceValid targetCoherent targetValid targetUnit view
          positive owner legal.2.2 ordered.2⟩
end

theorem copied_BN {d : Nat} {source target : ParentContext} {visible history : List Nat}
    {root cap : Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d source target visible history root cap delta phase) (positive : 0 < d)
    (e : NumericalExpr) (legal : FiniteLegal d source e) (ordered : BN d source e) :
    BN d target (copied d root cap delta phase source history e) := by
  rw [← relocate_eq_copied scope e legal]
  exact relocate_BN d e source target visible scope.sourceCoherent scope.sourceValid scope.targetCoherent scope.targetValid
    scope.targetUnit scope.view positive legal ordered

theorem copiedForests_BN {d : Nat} {source target : ParentContext} {visible history : List Nat}
    {root cap : Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d source target visible history root cap delta phase) (positive : 0 < d)
    (owner : Nat) (hs : Forests (List Nat)) (legal : FiniteLegalForests d source owner hs)
    (ordered : BNForests d source hs) :
    BNForests d target (copiedForests d root cap delta phase source history hs) := by
  rw [← relocateForests_eq_copied scope owner hs legal]
  exact relocateForests_BN d hs source target visible scope.sourceCoherent scope.sourceValid scope.targetCoherent scope.targetValid
    scope.targetUnit scope.view positive owner legal ordered

end BTnSSBMS.Source
