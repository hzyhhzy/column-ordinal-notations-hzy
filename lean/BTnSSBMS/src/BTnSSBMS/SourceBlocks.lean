import BTnSSBMS.SourceLegality

/-!
Complete source row-zero blocks retain whole attached forests. Only the
outer tail is cut, at its first coordinate no greater than the root.
These are finite auxiliary operations, not new fundamental sequences.
-/
namespace BTnSSBMS.Source

def takeAbove (floor : Nat) : NumericalExpr → NumericalExpr
  | .nil => .nil
  | .cons a hs tail =>
      if floor < a[0]?.getD 0 then .cons a hs (takeAbove floor tail) else .nil

def rootBlock : NumericalExpr → NumericalExpr
  | .nil => .nil
  | .cons a hs tail => .cons a hs (takeAbove (a[0]?.getD 0) tail)

theorem takeAbove_labels (floor : Nat) (e : NumericalExpr) :
    labels (takeAbove floor e) = (labels e).takeWhile (fun a => decide (floor < a[0]?.getD 0)) := by
  cases e with
  | nil => rfl
  | cons a hs tail =>
    simp only [takeAbove, labels, List.takeWhile_cons, decide_eq_true_eq]
    split
    · simp only [labels, takeAbove_labels]
    · rfl

theorem takeAbove_high (floor : Nat) (e : NumericalExpr) :
    ∀ a ∈ labels (takeAbove floor e), floor < a[0]?.getD 0 := by
  cases e with
  | nil => intro a member; simp only [takeAbove, labels, List.not_mem_nil] at member
  | cons a hs tail =>
    simp only [takeAbove]
    split
    next high =>
      intro col member
      simp only [labels, List.mem_cons] at member
      rcases member with rfl | later
      · exact high
      · exact takeAbove_high floor tail col later
    next low => intro col member; simp only [labels, List.not_mem_nil] at member

theorem takeAbove_separated {floor : Nat} {e : NumericalExpr} (separated : ForestSeparated e) :
    ForestSeparated (takeAbove floor e) := by
  cases e with
  | nil => trivial
  | cons a hs tail =>
    simp only [takeAbove]
    split
    · exact ⟨separated.1, takeAbove_separated separated.2⟩
    · trivial

theorem rootBlock_separated {e : NumericalExpr} (separated : ForestSeparated e) :
    ForestSeparated (rootBlock e) := by
  cases e with
  | nil => trivial
  | cons a hs tail => exact ⟨separated.1, takeAbove_separated separated.2⟩

theorem takeAbove_finiteLegal {d floor : Nat} {context : ParentContext} {e : NumericalExpr}
    (legal : FiniteLegal d context e) : FiniteLegal d context (takeAbove floor e) := by
  cases e with
  | nil => trivial
  | cons a hs tail =>
    simp only [takeAbove]
    split
    · exact ⟨legal.1, legal.2.1, legal.2.2.1, legal.2.2.2.1, takeAbove_finiteLegal legal.2.2.2.2⟩
    · trivial

theorem rootBlock_finiteLegal {d : Nat} {context : ParentContext} {e : NumericalExpr}
    (legal : FiniteLegal d context e) : FiniteLegal d context (rootBlock e) := by
  cases e with
  | nil => trivial
  | cons a hs tail =>
    exact ⟨legal.1, legal.2.1, legal.2.2.1, legal.2.2.2.1, takeAbove_finiteLegal legal.2.2.2.2⟩

end BTnSSBMS.Source
