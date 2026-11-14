import BTnSSBMS.CopyRoot

/-! A literal copy preserves the number of visible positions traversed
before a terminal hole. Closed sibling forests do not contribute to the
visible context. The result follows from the frozen copy equations. -/
namespace BTnSSBMS.Source

mutual
  theorem copied_holeSite_span (d root cap : Nat) (delta : List Nat) (phase : Nat)
      (source target : ParentContext) (history : List Nat) (after : root < history.length)
      (sourceOwner targetOwner : Option Nat) (depth : Nat) (e : NumericalExpr)
      {sourceSite targetSite : HoleSite}
      (found : holeSite d source sourceOwner depth e = some sourceSite)
      (targetFound : holeSite d target targetOwner depth
        (copied d root cap delta phase source history e) = some targetSite) :
      targetSite.context.length + source.length = sourceSite.context.length + target.length := by
    cases e with
    | nil => simp [holeSite] at found
    | cons a hs rest =>
      let label := Parents.label d source a
      let threshold := Keys.threshold cap root history label
      let head := shift a threshold delta phase
      have afterNext : root < (history ++ [threshold]).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      rw [copied_cons d root cap delta phase source history after] at targetFound
      cases rest with
      | nil =>
        change holeSite d target targetOwner depth
          (.cons head (copiedForests d root cap delta phase (source ++ [label])
            (history ++ [threshold]) hs) .nil) = some targetSite at targetFound
        cases depth with
        | zero =>
          have sourceEq : sourceSite = ⟨source, sourceOwner, a, hs⟩ := by
            simpa only [holeSite, Option.some.injEq] using found.symm
          have targetEq : targetSite = ⟨target, targetOwner, head,
              copiedForests d root cap delta phase (source ++ [label]) (history ++ [threshold]) hs⟩ := by
            simpa only [holeSite, Option.some.injEq] using targetFound.symm
          subst sourceSite
          subst targetSite
          exact Nat.add_comm _ _
        | succ k =>
          rw [holeSite] at found targetFound
          have sizes := copiedForests_holeSite_span d root cap delta phase
            (source ++ [label]) (target ++ [Parents.label d target head]) (history ++ [threshold]) afterNext
            (a[0]?.getD 0) (head[0]?.getD 0) k hs found targetFound
          simp only [List.length_append, List.length_cons, List.length_nil] at sizes
          omega
      | cons b ks tail =>
        rw [holeSite] at found
        have nonempty : copied d root cap delta phase (source ++ [label])
            (history ++ [threshold]) (.cons b ks tail) ≠ .nil := by
          intro empty
          have impossible := (copied_nil_iff ..).mp empty
          cases impossible
        rw [holeSite_cons_tail d target targetOwner depth _ _ _ nonempty] at targetFound
        have sizes := copied_holeSite_span d root cap delta phase
          (source ++ [label]) (target ++ [Parents.label d target head]) (history ++ [threshold]) afterNext
          sourceOwner targetOwner depth (.cons b ks tail) found targetFound
        simp only [List.length_append, List.length_cons, List.length_nil] at sizes
        omega

  theorem copiedForests_holeSite_span (d root cap : Nat) (delta : List Nat) (phase : Nat)
      (source target : ParentContext) (history : List Nat) (after : root < history.length)
      (sourceOwner targetOwner depth : Nat) (hs : Forests (List Nat))
      {sourceSite targetSite : HoleSite}
      (found : holeSiteForests d source sourceOwner depth hs = some sourceSite)
      (targetFound : holeSiteForests d target targetOwner depth
        (copiedForests d root cap delta phase source history hs) = some targetSite) :
      targetSite.context.length + source.length = sourceSite.context.length + target.length := by
    cases hs with
    | nil => simp [holeSiteForests] at found
    | cons h rest =>
      rw [copiedForests_cons] at targetFound
      cases rest with
      | nil =>
        change holeSiteForests d target targetOwner depth
          (.cons (copied d root cap delta phase source history h) .nil) = some targetSite at targetFound
        rw [holeSiteForests] at found targetFound
        exact copied_holeSite_span d root cap delta phase source target history after
          (some sourceOwner) (some targetOwner) depth h found targetFound
      | cons k ks =>
        rw [holeSiteForests] at found
        have nonempty : copiedForests d root cap delta phase source history (.cons k ks) ≠ .nil := by
          intro empty
          have impossible := (copiedForests_nil_iff ..).mp empty
          cases impossible
        rw [holeSiteForests_cons_tail d target targetOwner depth _ _ nonempty] at targetFound
        exact copiedForests_holeSite_span d root cap delta phase source target history after
          sourceOwner targetOwner depth (.cons k ks) found targetFound
end

theorem copied_root_holeSite_span (d cap : Nat) (delta : List Nat) (phase : Nat)
    (source target : ParentContext) (a : List Nat) (hs : Forests (List Nat)) (rest : NumericalExpr)
    (depth : Nat) {sourceSite targetSite : HoleSite}
    (found : holeSite d source none depth (.cons a hs rest) = some sourceSite)
    (targetFound : holeSite d target none depth
      (copied d source.length cap delta phase source (List.replicate source.length 0)
        (.cons a hs rest)) = some targetSite) :
    targetSite.context.length + source.length = sourceSite.context.length + target.length := by
  have after : source.length < (List.replicate source.length 0 ++ [cap]).length := by simp
  rw [copied_at_root] at targetFound
  cases rest with
  | nil =>
    change holeSite d target none depth
      (.cons (shift a cap delta phase)
        (copiedForests d source.length cap delta phase (source ++ [Parents.label d source a])
          (List.replicate source.length 0 ++ [cap]) hs) .nil) = some targetSite at targetFound
    cases depth with
    | zero =>
      have sourceEq : sourceSite = ⟨source, none, a, hs⟩ := by
        simpa only [holeSite, Option.some.injEq] using found.symm
      have targetEq : targetSite = ⟨target, none, shift a cap delta phase,
          copiedForests d source.length cap delta phase (source ++ [Parents.label d source a])
            (List.replicate source.length 0 ++ [cap]) hs⟩ := by
        simpa only [holeSite, Option.some.injEq] using targetFound.symm
      subst sourceSite
      subst targetSite
      exact Nat.add_comm _ _
    | succ k =>
      rw [holeSite] at found targetFound
      have sizes := copiedForests_holeSite_span d source.length cap delta phase
        (source ++ [Parents.label d source a]) (target ++ [Parents.label d target (shift a cap delta phase)])
        (List.replicate source.length 0 ++ [cap]) after (a[0]?.getD 0)
        ((shift a cap delta phase)[0]?.getD 0) k hs found targetFound
      simp only [List.length_append, List.length_cons, List.length_nil] at sizes
      omega
  | cons b ks tail =>
    rw [holeSite] at found
    rw [holeSite_cons_tail d target none depth _ _ _ (by
      intro empty
      have impossible := (copied_nil_iff ..).mp empty
      cases impossible)] at targetFound
    have sizes := copied_holeSite_span d source.length cap delta phase
      (source ++ [Parents.label d source a]) (target ++ [Parents.label d target (shift a cap delta phase)])
      (List.replicate source.length 0 ++ [cap]) after none none depth (.cons b ks tail) found targetFound
    simp only [List.length_append, List.length_cons, List.length_nil] at sizes
    omega

end BTnSSBMS.Source
