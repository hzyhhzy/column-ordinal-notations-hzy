import BTnSSBMS.CopyHistory
import BTnSSBMS.SourceZero

/-!
Ordinary-copy interiors with arbitrary nested forests. These theorems
preserve an explicit entering ShiftView; supplying that view at the real
root and every later-copy/donation seam is a separate obligation.
-/
namespace BTnSSBMS.Parents

theorem append_above_fence {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context) (positive : 0 < d)
    {owner : Nat} (inside : owner < context.length)
    (fence : Ancestor context 0 owner (context.length - 1)) (a : List Nat)
    (above : reading context 0 owner < a[0]?.getD 0) :
    Ancestor (context ++ [label d context a]) 0 owner context.length := by
  apply ancestor_zero_of_interval (coherent_append_label coherent a)
    (context_valid_append_label d context valid a) positive (by simp) (by omega)
  intro p after before
  rw [← reading_prefix (List.prefix_append context [label d context a]) 0 owner inside]
  by_cases old : p < context.length
  · rw [← reading_prefix (List.prefix_append context [label d context a]) 0 p old]
    exact (fence.zero_interval coherent valid positive).2 p after (by omega)
  · have same : p = context.length := by omega
    subst p
    rw [reading_append_label]
    exact above

end BTnSSBMS.Parents

namespace BTnSSBMS.Source

mutual
  theorem ascendReplace_nohole (e : MarkedExpr) (tail : NumericalExpr) (delta : List Nat) (phase : Nat) :
      ascendReplace e tail none delta phase = e.map (fun a => shift a.1 a.2 delta phase) := by
    cases e with
    | nil => rfl
    | cons a hs rest =>
      unfold ascendReplace
      simp only [Option.none_beq_some, Bool.and_false, Bool.false_eq_true, if_false, Option.map_none,
        ite_self, Expr.map, ascendReplace_nohole, ascendForests_nohole]
  theorem ascendForests_nohole (hs : Forests (List Nat × Nat)) (tail : NumericalExpr) (delta : List Nat) (phase : Nat) :
      ascendForests hs tail none delta phase = hs.map (fun a => shift a.1 a.2 delta phase) := by
    cases hs with
    | nil => rfl
    | cons h rest =>
      unfold ascendForests
      simp only [ite_self, Forests.map, ascendReplace_nohole, ascendForests_nohole]
end

/-- This is a literal expression in the frozen annotation, activation,
and shift functions, not a new fundamental-sequence rule. -/
def copied (d root cap : Nat) (delta : List Nat) (phase : Nat)
    (source : ParentContext) (history : List Nat) (e : NumericalExpr) : NumericalExpr :=
  (mark cap root history (Parents.annotate d source e)).map (fun a => shift a.1 a.2 delta phase)

def copiedForests (d root cap : Nat) (delta : List Nat) (phase : Nat)
    (source : ParentContext) (history : List Nat) (hs : Forests (List Nat)) : Forests (List Nat) :=
  (markForests cap root history (Parents.annotateForests d source hs)).map (fun a => shift a.1 a.2 delta phase)

theorem copied_eq_ascend (d root cap : Nat) (delta : List Nat) (phase : Nat)
    (source : ParentContext) (history : List Nat) (e tail : NumericalExpr) :
    copied d root cap delta phase source history e =
      ascendReplace (mark cap root history (Parents.annotate d source e)) tail none delta phase :=
  (ascendReplace_nohole _ tail delta phase).symm

theorem copiedForests_eq_ascend (d root cap : Nat) (delta : List Nat) (phase : Nat)
    (source : ParentContext) (history : List Nat) (hs : Forests (List Nat)) (tail : NumericalExpr) :
    copiedForests d root cap delta phase source history hs =
      ascendForests (markForests cap root history (Parents.annotateForests d source hs)) tail none delta phase :=
  (ascendForests_nohole _ tail delta phase).symm

theorem copied_cons (d root cap : Nat) (delta : List Nat) (phase : Nat)
    (source : ParentContext) (history : List Nat) (afterRoot : root < history.length)
    (a : List Nat) (hs : Forests (List Nat)) (t : NumericalExpr) :
    let label := Parents.label d source a
    let threshold := Keys.threshold cap root history label
    copied d root cap delta phase source history (.cons a hs t) =
      .cons (shift a threshold delta phase)
        (copiedForests d root cap delta phase (source ++ [label]) (history ++ [threshold]) hs)
        (copied d root cap delta phase (source ++ [label]) (history ++ [threshold]) t) := by
  simp only [copied, Parents.annotate, mark, show ¬ history.length < root by omega,
    show ¬ history.length = root by omega, if_false, decide_false, Bool.false_and, Bool.false_eq_true,
    Expr.map, Parents.label, copiedForests]

theorem copiedForests_cons (d root cap : Nat) (delta : List Nat) (phase : Nat)
    (source : ParentContext) (history : List Nat) (h : NumericalExpr) (hs : Forests (List Nat)) :
    copiedForests d root cap delta phase source history (.cons h hs) =
      .cons (copied d root cap delta phase source history h)
        (copiedForests d root cap delta phase source history hs) := by
  rfl

theorem ShiftView.shifted_above {d : Nat} {source target : ParentContext} {visible history : List Nat}
    {root cap : Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d source target visible history root cap delta phase) (positive : 0 < d)
    {owner : Nat} (inside : owner < source.length)
    (fence : Parents.Ancestor source 0 owner (source.length - 1)) (a : List Nat)
    (above : Parents.reading source 0 owner < a[0]?.getD 0) (width : a.length = d)
    (unit : Parents.UnitSteps d (source ++ [Parents.label d source a])) :
    Parents.reading target 0 (Parents.point visible owner) <
      (shift a (Keys.threshold cap root history (Parents.label d source a)) delta phase)[0]?.getD 0 := by
  have next := scope.append a width unit
  have path := Parents.append_above_fence scope.sourceCoherent scope.sourceValid positive inside fence a above
  have lifted := next.view.lift 0 positive owner source.length (by simp; omega) (by simp) path
  rw [Parents.point_append_old visible owner target.length (by rw [scope.view.length]; exact inside),
    ← scope.view.length, Parents.point_append_last] at lifted
  have strict := lifted.reading_lt next.targetCoherent (by have bound := scope.view.bounded owner inside; omega)
  rw [Parents.reading_append_label,
    ← Parents.reading_prefix (List.prefix_append target _) 0 (Parents.point visible owner) (scope.view.bounded owner inside)] at strict
  exact strict

/-- An owner's row-zero separation survives an entire copied outer
sequence, not just its first column; nested forests restore the same scope. -/
theorem copied_above {d : Nat} {source target : ParentContext} {visible history : List Nat}
    {root cap : Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d source target visible history root cap delta phase) (positive : 0 < d)
    {owner : Nat} (inside : owner < source.length)
    (fence : Parents.Ancestor source 0 owner (source.length - 1))
    (e : NumericalExpr) (legal : FiniteLegal d source e)
    (above : ∀ a ∈ labels e, Parents.reading source 0 owner < a[0]?.getD 0) :
    ∀ a ∈ labels (copied d root cap delta phase source history e),
      Parents.reading target 0 (Parents.point visible owner) < a[0]?.getD 0 := by
  cases e with
  | nil => simp [copied, Parents.annotate, mark, Expr.map, labels]
  | cons a hs t =>
    rw [copied_cons d root cap delta phase source history (by rw [scope.historyLength]; exact scope.afterRoot)]
    intro col member
    simp only [labels, List.mem_cons] at member
    rcases member with rfl | later
    · exact scope.shifted_above positive inside fence a (above a (by simp [labels])) legal.1 legal.2.1
    · have next := scope.append a legal.1 legal.2.1
      have nextFence := Parents.append_above_fence scope.sourceCoherent scope.sourceValid positive inside
        fence a (above a (by simp [labels]))
      have tailAbove : ∀ col ∈ labels t,
          Parents.reading (source ++ [Parents.label d source a]) 0 owner < col[0]?.getD 0 := by
        intro col member
        rw [← Parents.reading_prefix (List.prefix_append source _) 0 owner inside]
        exact above col (by simp only [labels, List.mem_cons]; exact Or.inr member)
      have result := copied_above next positive (by simp; omega)
        (by simpa using nextFence) t legal.2.2.2.2 tailAbove col later
      rw [Parents.point_append_old visible owner target.length (by rw [scope.view.length]; exact inside),
        ← Parents.reading_prefix (List.prefix_append target _) 0 (Parents.point visible owner)
          (scope.view.bounded owner inside)] at result
      exact result

mutual
  theorem copied_finiteLegal {d : Nat} {source target : ParentContext} {visible history : List Nat}
      {root cap : Nat} {delta : List Nat} {phase : Nat}
      (scope : ShiftView d source target visible history root cap delta phase) (positive : 0 < d)
      (e : NumericalExpr) (legal : FiniteLegal d source e) :
      FiniteLegal d target (copied d root cap delta phase source history e) := by
    cases e with
    | nil => trivial
    | cons a hs t =>
      rw [copied_cons d root cap delta phase source history (by rw [scope.historyLength]; exact scope.afterRoot)]
      have next := scope.append a legal.1 legal.2.1
      refine ⟨(shift_width ..).trans legal.1, next.targetUnit, ?_, ?_,
        copied_finiteLegal next positive t legal.2.2.2.2⟩
      · intro attached j room
        have nonempty : hs ≠ .nil := by
          intro empty
          subst hs
          exact attached rfl
        have oldPositive := legal.2.2.1 nonempty j room
        rw [shift_value _ _ _ _ j (by rw [legal.1]; exact room)]
        omega
      · have input : FiniteLegalForests d (source ++ [Parents.label d source a])
            (Parents.reading (source ++ [Parents.label d source a]) 0 source.length) hs := by
          rw [Parents.reading_append_label]
          exact legal.2.2.2.1
        have forests := copiedForests_finiteLegal next positive source.length (by simp)
          (by simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel]; exact .refl _) hs input
        rw [← scope.view.length, Parents.point_append_last, Parents.reading_append_label] at forests
        exact forests
  theorem copiedForests_finiteLegal {d : Nat} {source target : ParentContext} {visible history : List Nat}
      {root cap : Nat} {delta : List Nat} {phase : Nat}
      (scope : ShiftView d source target visible history root cap delta phase) (positive : 0 < d)
      (owner : Nat) (inside : owner < source.length)
      (fence : Parents.Ancestor source 0 owner (source.length - 1))
      (hs : Forests (List Nat))
      (legal : FiniteLegalForests d source (Parents.reading source 0 owner) hs) :
      FiniteLegalForests d target (Parents.reading target 0 (Parents.point visible owner))
        (copiedForests d root cap delta phase source history hs) := by
    cases hs with
    | nil => trivial
    | cons h rest =>
      rw [copiedForests_cons]
      exact ⟨copied_above scope positive inside fence h legal.2.1 legal.1,
        copied_finiteLegal scope positive h legal.2.1,
        copiedForests_finiteLegal scope positive owner inside fence rest legal.2.2⟩
end

end BTnSSBMS.Source
