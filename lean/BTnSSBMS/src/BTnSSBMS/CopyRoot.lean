import BTnSSBMS.CopyHole

/-!
Rooted templates for repeated copies. The ordinary material is transported
from the actual root prefix. Its terminal path also controls every outer
column, so a later insertion cannot escape through the owner's row-zero
boundary merely because the template contains nested forests.
-/
namespace BTnSSBMS.Source

mutual
  theorem holeSite_contexts {d : Nat} {context : ParentContext} {owner : Option Nat}
      (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
      (depth : Nat) (e : NumericalExpr) {site : HoleSite}
      (found : holeSite d context owner depth e = some site) :
      Parents.Coherent d site.context ∧ Parents.ContextValid site.context := by
    cases e with
    | nil => simp [holeSite] at found
    | cons a hs rest =>
      cases rest with
      | nil =>
        cases depth with
        | zero =>
          have same : site = ⟨context, owner, a, hs⟩ := by
            simpa only [holeSite, Option.some.injEq] using found.symm
          subst site
          exact ⟨coherent, valid⟩
        | succ k =>
          rw [holeSite] at found
          exact holeSiteForests_contexts (Parents.coherent_append_label coherent a)
            (Parents.context_valid_append_label d context valid a) k hs found
      | cons b ks t =>
        rw [holeSite] at found
        exact holeSite_contexts (Parents.coherent_append_label coherent a)
          (Parents.context_valid_append_label d context valid a) depth (.cons b ks t) found
  theorem holeSiteForests_contexts {d : Nat} {context : ParentContext} {owner : Nat}
      (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
      (depth : Nat) (hs : Forests (List Nat)) {site : HoleSite}
      (found : holeSiteForests d context owner depth hs = some site) :
      Parents.Coherent d site.context ∧ Parents.ContextValid site.context := by
    cases hs with
    | nil => simp [holeSiteForests] at found
    | cons h rest =>
      cases rest with
      | nil =>
        rw [holeSiteForests] at found
        exact holeSite_contexts coherent valid depth h found
      | cons k ks =>
        rw [holeSiteForests] at found
        exact holeSiteForests_contexts coherent valid depth (.cons k ks) found
end

theorem holeSite_zero_owner {d : Nat} {context : ParentContext} {owner : Option Nat}
    (e : NumericalExpr) {site : HoleSite} (found : holeSite d context owner 0 e = some site) :
    site.owner = owner := by
  cases e with
  | nil => simp [holeSite] at found
  | cons a hs rest =>
    cases rest with
    | nil =>
      have same : site = ⟨context, owner, a, hs⟩ := by
        simpa only [holeSite, Option.some.injEq] using found.symm
      subst site
      rfl
    | cons b ks t =>
      rw [holeSite] at found
      exact holeSite_zero_owner (.cons b ks t) found

theorem holeSite_head_prefix {d : Nat} {context : ParentContext} {owner : Option Nat}
    {depth : Nat} {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr}
    {site : HoleSite} (found : holeSite d context owner depth (.cons a hs rest) = some site) :
    context ++ [Parents.label d context a] <+:
      site.context ++ [Parents.label d site.context site.terminal] := by
  cases rest with
  | nil =>
    cases depth with
    | zero =>
      have same : site = ⟨context, owner, a, hs⟩ := by
        simpa only [holeSite, Option.some.injEq] using found.symm
      subst site
      exact List.prefix_refl _
    | succ k =>
      rw [holeSite] at found
      exact (holeSiteForests_extends d _ _ k hs found).trans (List.prefix_append ..)
  | cons b ks t =>
    rw [holeSite] at found
    exact (holeSite_extends d _ owner depth (.cons b ks t) found).trans (List.prefix_append ..)

theorem holeSite_after_head {d : Nat} {context : ParentContext} {owner : Option Nat}
    {depth : Nat} {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr}
    {site : HoleSite} (found : holeSite d context owner depth (.cons a hs rest) = some site)
    (later : context.length < site.context.length) :
    context ++ [Parents.label d context a] <+: site.context := by
  cases rest with
  | nil =>
    cases depth with
    | zero =>
      have same : site = ⟨context, owner, a, hs⟩ := by
        simpa only [holeSite, Option.some.injEq] using found.symm
      subst site
      exact False.elim (Nat.lt_irrefl _ later)
    | succ k =>
      rw [holeSite] at found
      exact holeSiteForests_extends d _ _ k hs found
  | cons b ks t =>
    rw [holeSite] at found
    exact holeSite_extends d _ owner depth (.cons b ks t) found

/-- Every outer label occurs on the actual rightmost scoped path, at or
after the entering frontier. No flattening of closed sibling forests is used. -/
theorem holeSite_outer_labels {d : Nat} {context : ParentContext} {owner : Option Nat}
    (depth : Nat) (e : NumericalExpr) {site : HoleSite}
    (found : holeSite d context owner depth e = some site) :
    ∀ a ∈ labels e, ∃ i, context.length ≤ i ∧ i ≤ site.context.length ∧
      Parents.reading (site.context ++ [Parents.label d site.context site.terminal]) 0 i = a[0]?.getD 0 := by
  cases e with
  | nil => simp [labels]
  | cons a hs rest =>
    intro col member
    simp only [labels, List.mem_cons] at member
    rcases member with rfl | later
    · have initial := holeSite_head_prefix found
      refine ⟨context.length, Nat.le_refl _, ?_, ?_⟩
      · have bound := initial.length_le
        simp only [List.length_append, List.length_cons, List.length_nil] at bound
        omega
      · rw [← Parents.reading_prefix initial 0 context.length (by simp), Parents.reading_append_label]
    · cases rest with
      | nil => simp [labels] at later
      | cons b ks t =>
        rw [holeSite] at found
        obtain ⟨i, after, before, value⟩ := holeSite_outer_labels depth (.cons b ks t) found col later
        exact ⟨i, by simp only [List.length_append, List.length_cons, List.length_nil] at after; omega,
          before, value⟩

/-- A root ancestor of the terminal bounds the whole outer template,
not just the final leaf. This is the actual P0 interval theorem. -/
theorem holeSite_outer_above {d : Nat} {context : ParentContext} {owner : Option Nat}
    (depth : Nat) (e : NumericalExpr) {site : HoleSite}
    (found : holeSite d context owner depth e = some site)
    (coherent : Parents.Coherent d (site.context ++ [Parents.label d site.context site.terminal]))
    (valid : Parents.ContextValid (site.context ++ [Parents.label d site.context site.terminal]))
    (positive : 0 < d) {root : Nat} (before : root < context.length)
    (path : Parents.Ancestor (site.context ++ [Parents.label d site.context site.terminal]) 0 root site.context.length) :
    ∀ a ∈ labels e, Parents.reading context 0 root < a[0]?.getD 0 := by
  intro a member
  obtain ⟨i, after, last, value⟩ := holeSite_outer_labels depth e found a member
  have bound := (path.zero_interval coherent valid positive).2 i (by omega) last
  have initial := (holeSite_extends d context owner depth e found).trans
    (List.prefix_append site.context [Parents.label d site.context site.terminal])
  rw [← Parents.reading_prefix initial 0 root before, value] at bound
  exact bound

theorem holeSite_root_tail_above {d : Nat} {context : ParentContext} {owner : Option Nat}
    {a : List Nat} {hs : Forests (List Nat)} (depth : Nat) (rest : NumericalExpr) {site : HoleSite}
    (found : holeSite d context owner depth (.cons a hs rest) = some site)
    (coherent : Parents.Coherent d (site.context ++ [Parents.label d site.context site.terminal]))
    (valid : Parents.ContextValid (site.context ++ [Parents.label d site.context site.terminal]))
    (positive : 0 < d)
    (path : Parents.Ancestor (site.context ++ [Parents.label d site.context site.terminal]) 0 context.length site.context.length) :
    ∀ col ∈ labels rest, a[0]?.getD 0 < col[0]?.getD 0 := by
  cases rest with
  | nil => simp [labels]
  | cons b ks t =>
    rw [holeSite] at found
    have result := holeSite_outer_above depth (.cons b ks t) found coherent valid positive
      (by simp : context.length < (context ++ [Parents.label d context a]).length) path
    rw [Parents.reading_append_label] at result
    exact result

theorem holeSite_root_coordinates {d : Nat} {context : ParentContext} {owner : Option Nat}
    {depth : Nat} {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr} {site : HoleSite}
    (found : holeSite d context owner depth (.cons a hs rest) = some site)
    (later : context.length < site.context.length) :
    (site.context[context.length]?.getD default).coordinates = a := by
  have initial := holeSite_after_head found later
  have same := (List.prefix_iff_getElem?.mp initial) context.length (by simp)
  rw [same]
  simp only [Option.getD_some, List.getElem_append_right (Nat.le_refl context.length),
    Nat.sub_self, List.getElem_cons_zero, Parents.label]

theorem holeSite_root_take {d : Nat} {context : ParentContext} {owner : Option Nat}
    {depth : Nat} {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr} {site : HoleSite}
    (found : holeSite d context owner depth (.cons a hs rest) = some site)
    (later : context.length < site.context.length) :
    site.context.take (context.length + 1) = context ++ [Parents.label d context a] := by
  simpa only [List.length_append, List.length_cons, List.length_nil] using
    (List.prefix_iff_eq_take.mp (holeSite_after_head found later)).symm

theorem root_view_point {d : Nat} {context target : ParentContext} {a head : List Nat}
    {visible history : List Nat} {cap : Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d (context ++ [Parents.label d context a])
      (target ++ [Parents.label d target head]) visible history context.length cap delta phase) :
    Parents.point visible context.length = target.length := by
  have last := scope.view.frontier (by simp)
  simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel] at last
  omega

theorem copied_root_finiteLegal {d : Nat} {context target : ParentContext} {a : List Nat}
    {visible : List Nat} {cap : Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d (context ++ [Parents.label d context a])
      (target ++ [Parents.label d target (shift a cap delta phase)]) visible
      (List.replicate context.length 0 ++ [cap]) context.length cap delta phase)
    (positive : 0 < d) (hs : Forests (List Nat)) (rest : NumericalExpr)
    (legal : FiniteLegal d context (.cons a hs rest)) :
    FiniteLegal d target
      (copied d context.length cap delta phase context (List.replicate context.length 0) (.cons a hs rest)) := by
  rw [copied_at_root]
  refine ⟨(shift_width ..).trans legal.1, scope.targetUnit, ?_, ?_,
    copied_finiteLegal scope positive rest legal.2.2.2.2⟩
  · intro attached j room
    have nonempty : hs ≠ .nil := by intro empty; subst hs; exact attached rfl
    have old := legal.2.2.1 nonempty j room
    rw [shift_value _ _ _ _ j (by rw [legal.1]; exact room)]
    omega
  · have result := copiedForests_finiteLegal scope positive context.length (by simp)
      (by simpa only [List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel]
        using (Parents.Ancestor.refl context.length)) hs
      (by rw [Parents.reading_append_label]; exact legal.2.2.2.1)
    rw [root_view_point scope, Parents.reading_append_label] at result
    exact result

theorem copied_root_lower {d : Nat} {context target : ParentContext} {a : List Nat}
    {visible : List Nat} {cap : Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d (context ++ [Parents.label d context a])
      (target ++ [Parents.label d target (shift a cap delta phase)]) visible
      (List.replicate context.length 0 ++ [cap]) context.length cap delta phase)
    (positive : 0 < d) (hs : Forests (List Nat)) (rest : NumericalExpr)
    (legal : FiniteLegal d context (.cons a hs rest))
    (above : ∀ col ∈ labels rest, a[0]?.getD 0 < col[0]?.getD 0) :
    ∀ col ∈ labels (copied d context.length cap delta phase context (List.replicate context.length 0)
      (.cons a hs rest)), (shift a cap delta phase)[0]?.getD 0 ≤ col[0]?.getD 0 := by
  rw [copied_at_root]
  intro col member
  simp only [labels, List.mem_cons] at member
  rcases member with rfl | later
  · exact Nat.le_refl _
  · have result := copied_above scope positive (by simp : context.length < (context ++ [Parents.label d context a]).length)
      (by simpa only [List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel]
        using (Parents.Ancestor.refl context.length)) rest legal.2.2.2.2
      (by rw [Parents.reading_append_label]; exact above) col later
    rw [root_view_point scope, Parents.reading_append_label] at result
    exact Nat.le_of_lt result

theorem copied_root_holeSite {d : Nat} {context target : ParentContext} {a : List Nat}
    {visible : List Nat} {cap : Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d (context ++ [Parents.label d context a])
      (target ++ [Parents.label d target (shift a cap delta phase)]) visible
      (List.replicate context.length 0 ++ [cap]) context.length cap delta phase)
    (hs : Forests (List Nat)) (rest : NumericalExpr)
    (legal : FiniteLegal d context (.cons a hs rest)) (depth : Nat) {site : HoleSite}
    (found : holeSite d context none depth (.cons a hs rest) = some site)
    (later : context.length < site.context.length) :
    ∃ targetSite, holeSite d target none depth
        (copied d context.length cap delta phase context (List.replicate context.length 0) (.cons a hs rest)) = some targetSite ∧
      ShiftedHole d context.length cap delta phase site targetSite := by
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
      exact copiedForests_holeSite scope (a[0]?.getD 0) ((shift a cap delta phase)[0]?.getD 0)
        k hs legal.2.2.2.1 found
  | cons b ks t =>
    rw [holeSite] at found
    rw [holeSite_cons_tail d target none depth _ _ _ (by
      intro empty
      have impossible := (copied_nil_iff ..).mp empty
      cases impossible)]
    exact copied_holeSite scope none none depth (.cons b ks t) legal.2.2.2.2 found

end BTnSSBMS.Source
