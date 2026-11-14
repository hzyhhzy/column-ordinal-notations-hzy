import BTnSSBMS.CopyRoot
import BTnSSBMS.ExactNumericalPosition

/-!
Exact parent transport along the actual terminal-hole traversal, including
entry into nested forests. The already installed forced root is excluded;
every subsequent visible position has exact parents. This strengthens the
hole witness, not the frozen copying operation or standard domain.
-/
namespace BTnSSBMS.Source

theorem ShiftView.exact_after_append {d : Nat} {source target : ParentContext}
    {visible history : List Nat} {root cap : Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d source target visible history root cap delta phase)
    (exactAt : ∀ position, root < position → position < source.length →
      Parents.ExactPosition d source target visible position)
    (a : List Nat) (width : a.length = d)
    (unit : Parents.UnitSteps d (source ++ [Parents.label d source a])) :
    let threshold := Keys.threshold cap root history (Parents.label d source a)
    ∀ position, root < position → position < (source ++ [Parents.label d source a]).length →
      Parents.ExactPosition d (source ++ [Parents.label d source a])
        (target ++ [Parents.label d target (shift a threshold delta phase)])
        (visible ++ [target.length]) position := by
  dsimp only
  intro position after inside
  by_cases old : position < source.length
  · exact (exactAt position after old).extends scope.view scope.sourceValid old
      (List.prefix_append _ _) (List.prefix_append _ _) (List.prefix_append _ _)
  · have last : position = source.length := by
      simp only [List.length_append, List.length_cons, List.length_nil] at inside
      omega
    subst position
    simpa only [relocationHead_eq_shift scope a width unit] using
      Parents.exactPosition_append scope.sourceCoherent scope.sourceValid
        scope.targetCoherent scope.targetValid scope.view a

def ExactShiftedHole (d root cap : Nat) (delta : List Nat) (phase : Nat) (initialVisible : List Nat)
    (source target : HoleSite) : Prop :=
  ∃ visible history,
    initialVisible <+: visible ∧
    ShiftView d source.context target.context visible history root cap delta phase ∧
    (∀ position, root < position → position < source.context.length →
      Parents.ExactPosition d source.context target.context visible position) ∧
    let label := Parents.label d source.context source.terminal
    let threshold := Keys.threshold cap root history label
    target.terminal = shift source.terminal threshold delta phase ∧
    target.attached = copiedForests d root cap delta phase (source.context ++ [label])
      (history ++ [threshold]) source.attached

theorem ExactShiftedHole.toShiftedHole {d root cap phase : Nat} {delta initialVisible : List Nat}
    {source target : HoleSite} (hole : ExactShiftedHole d root cap delta phase initialVisible source target) :
    ShiftedHole d root cap delta phase source target := by
  obtain ⟨visible, history, _, scope, _, terminal, attached⟩ := hole
  exact ⟨visible, history, scope, terminal, attached⟩

theorem ExactShiftedHole.prefix {d root cap phase : Nat} {delta small large : List Nat}
    {source target : HoleSite} (hole : ExactShiftedHole d root cap delta phase large source target)
    (initial : small <+: large) : ExactShiftedHole d root cap delta phase small source target := by
  obtain ⟨visible, history, extended, scope, exactAt, terminal, attached⟩ := hole
  exact ⟨visible, history, initial.trans extended, scope, exactAt, terminal, attached⟩

mutual
  theorem copied_holeSite_exact {d : Nat} {source target : ParentContext}
      {visible history : List Nat} {root cap : Nat} {delta : List Nat} {phase : Nat}
      (scope : ShiftView d source target visible history root cap delta phase)
      (exactAt : ∀ position, root < position → position < source.length →
        Parents.ExactPosition d source target visible position)
      (sourceOwner targetOwner : Option Nat) (depth : Nat) (e : NumericalExpr)
      (legal : FiniteLegal d source e) {site : HoleSite}
      (found : holeSite d source sourceOwner depth e = some site) :
      ∃ targetSite, holeSite d target targetOwner depth
          (copied d root cap delta phase source history e) = some targetSite ∧
        ExactShiftedHole d root cap delta phase visible site targetSite := by
    cases e with
    | nil => simp [holeSite] at found
    | cons a hs rest =>
      have next := scope.append a legal.1 legal.2.1
      have nextExact := scope.exact_after_append exactAt a legal.1 legal.2.1
      let label := Parents.label d source a
      let threshold := Keys.threshold cap root history label
      let head := shift a threshold delta phase
      have after : root < history.length := by rw [scope.historyLength]; exact scope.afterRoot
      rw [copied_cons d root cap delta phase source history after]
      cases rest with
      | nil =>
        change ∃ targetSite, holeSite d target targetOwner depth
          (.cons head (copiedForests d root cap delta phase (source ++ [label])
            (history ++ [threshold]) hs) .nil) = some targetSite ∧
          ExactShiftedHole d root cap delta phase visible site targetSite
        cases depth with
        | zero =>
          have same : site = ⟨source, sourceOwner, a, hs⟩ := by
            simpa only [holeSite, Option.some.injEq] using found.symm
          subst site
          refine ⟨⟨target, targetOwner, head, copiedForests d root cap delta phase
            (source ++ [label]) (history ++ [threshold]) hs⟩, ?_, ?_⟩
          · rw [holeSite]
          · exact ⟨visible, history, List.prefix_refl _, scope, exactAt, rfl, rfl⟩
        | succ k =>
          rw [holeSite] at found ⊢
          obtain ⟨targetSite, targetFound, hole⟩ := copiedForests_holeSite_exact next nextExact
            (a[0]?.getD 0) (head[0]?.getD 0) k hs legal.2.2.2.1 found
          exact ⟨targetSite, targetFound, hole.prefix (List.prefix_append _ _)⟩
      | cons b ks t =>
        rw [holeSite] at found
        have nonempty : copied d root cap delta phase (source ++ [label])
            (history ++ [threshold]) (.cons b ks t) ≠ .nil := by
          intro impossible
          have empty := (copied_nil_iff ..).mp impossible
          cases empty
        rw [holeSite_cons_tail d target targetOwner depth _ _ _ nonempty]
        obtain ⟨targetSite, targetFound, hole⟩ := copied_holeSite_exact next nextExact sourceOwner
          targetOwner depth (.cons b ks t) legal.2.2.2.2 found
        exact ⟨targetSite, targetFound, hole.prefix (List.prefix_append _ _)⟩

  theorem copiedForests_holeSite_exact {d : Nat} {source target : ParentContext}
      {visible history : List Nat} {root cap : Nat} {delta : List Nat} {phase : Nat}
      (scope : ShiftView d source target visible history root cap delta phase)
      (exactAt : ∀ position, root < position → position < source.length →
        Parents.ExactPosition d source target visible position)
      (sourceOwner targetOwner depth : Nat) (hs : Forests (List Nat))
      (legal : FiniteLegalForests d source sourceOwner hs) {site : HoleSite}
      (found : holeSiteForests d source sourceOwner depth hs = some site) :
      ∃ targetSite, holeSiteForests d target targetOwner depth
          (copiedForests d root cap delta phase source history hs) = some targetSite ∧
        ExactShiftedHole d root cap delta phase visible site targetSite := by
    cases hs with
    | nil => simp [holeSiteForests] at found
    | cons h rest =>
      rw [copiedForests_cons]
      cases rest with
      | nil =>
        change ∃ targetSite, holeSiteForests d target targetOwner depth
          (.cons (copied d root cap delta phase source history h) .nil) = some targetSite ∧
          ExactShiftedHole d root cap delta phase visible site targetSite
        rw [holeSiteForests] at found ⊢
        exact copied_holeSite_exact scope exactAt (some sourceOwner) (some targetOwner)
          depth h legal.2.1 found
      | cons k ks =>
        rw [holeSiteForests] at found
        have nonempty : copiedForests d root cap delta phase source history (.cons k ks) ≠ .nil := by
          intro impossible
          have empty := (copiedForests_nil_iff ..).mp impossible
          cases empty
        rw [holeSiteForests_cons_tail d target targetOwner depth _ _ nonempty]
        exact copiedForests_holeSite_exact scope exactAt sourceOwner targetOwner depth
          (.cons k ks) legal.2.2 found
end

/-- Start at the real forced copy root. Exactness of all later positions
is obtained from the actual traversal; it is not an extra input. -/
theorem copied_root_holeSite_exact {d : Nat} {context target : ParentContext} {a : List Nat}
    {visible : List Nat} {cap : Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d (context ++ [Parents.label d context a])
      (target ++ [Parents.label d target (shift a cap delta phase)]) visible
      (List.replicate context.length 0 ++ [cap]) context.length cap delta phase)
    (hs : Forests (List Nat)) (rest : NumericalExpr)
    (legal : FiniteLegal d context (.cons a hs rest)) (depth : Nat) {site : HoleSite}
    (found : holeSite d context none depth (.cons a hs rest) = some site)
    (later : context.length < site.context.length) :
    ∃ targetSite, holeSite d target none depth
        (copied d context.length cap delta phase context (List.replicate context.length 0)
          (.cons a hs rest)) = some targetSite ∧
      ExactShiftedHole d context.length cap delta phase visible site targetSite := by
  have exactAt : ∀ position, context.length < position →
      position < (context ++ [Parents.label d context a]).length →
      Parents.ExactPosition d (context ++ [Parents.label d context a])
        (target ++ [Parents.label d target (shift a cap delta phase)]) visible position := by
    intro position after inside
    simp only [List.length_append, List.length_cons, List.length_nil] at inside
    omega
  rw [copied_at_root]
  cases rest with
  | nil =>
    cases depth with
    | zero =>
      have same : site = ⟨context, none, a, hs⟩ := by
        simpa only [holeSite, Option.some.injEq] using found.symm
      subst site
      exact False.elim (Nat.lt_irrefl _ later)
    | succ k =>
      change ∃ targetSite, holeSite d target none (k + 1)
        (.cons (shift a cap delta phase)
          (copiedForests d context.length cap delta phase (context ++ [Parents.label d context a])
            (List.replicate context.length 0 ++ [cap]) hs) .nil) = some targetSite ∧ _
      rw [holeSite] at found ⊢
      exact copiedForests_holeSite_exact scope exactAt (a[0]?.getD 0)
        ((shift a cap delta phase)[0]?.getD 0) k hs legal.2.2.2.1 found
  | cons b ks t =>
    rw [holeSite] at found
    rw [holeSite_cons_tail d target none depth _ _ _ (by
      intro empty
      have impossible := (copied_nil_iff ..).mp empty
      cases impossible)]
    exact copied_holeSite_exact scope exactAt none none depth (.cons b ks t) legal.2.2.2.2 found

end BTnSSBMS.Source
