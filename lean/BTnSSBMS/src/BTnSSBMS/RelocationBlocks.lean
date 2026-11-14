import BTnSSBMS.SourceBlocks
import BTnSSBMS.RelocationLegality

/-! Canonical numerical transport preserves complete zero-blocks, not
merely their first columns. The cutoff test is proved in both directions
using actual computed parents and the live zero-ancestor frontier. -/
namespace BTnSSBMS.Source

theorem relocationHead_above_iff {d : Nat} {source target : ParentContext} {visible : List Nat}
    (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (view : Parents.NumericalView d source target visible) (positive : 0 < d)
    {owner : Nat} (inside : owner < source.length)
    (fence : Parents.Ancestor source 0 owner (source.length - 1))
    (a : List Nat) (unit : Parents.UnitSteps d (source ++ [Parents.label d source a])) :
    Parents.reading target 0 (Parents.point visible owner) <
        (relocationHead d source target visible a)[0]?.getD 0 ↔
      Parents.reading source 0 owner < a[0]?.getD 0 := by
  constructor
  · intro above
    apply Classical.byContradiction
    intro low
    have low : a[0]?.getD 0 ≤ Parents.reading source 0 owner := by omega
    have sourceValue := Parents.label_unit_value a unit positive
    rw [relocationHead_value d source target visible a positive] at above
    cases found : (Parents.label d source a).parents[0]?.join with
    | none => simp only [Parents.representedValue, found, Option.map_none, Option.getD_none] at above; omega
    | some p =>
      have bound := Parents.label_parent_bound d source a 0 p found
      simp only [found, Option.map_some, Option.getD_some] at sourceValue
      have different : p ≠ owner := by intro same; subst p; omega
      have parentFront := Parents.label_zero_parent_frontier sourceCoherent sourceValid positive a found
      have path : Parents.Ancestor source 0 p owner := by
        rcases parentFront.comparable fence with direct | reverse
        · exact direct
        · have strict := reverse.reading_lt sourceCoherent (Ne.symm different)
          omega
      have before : p < owner := by have weak := path.le sourceValid; omega
      have lifted := view.lift 0 positive p owner bound inside path
      have unequal : Parents.point visible p ≠ Parents.point visible owner :=
        Nat.ne_of_lt (view.increasing p owner before inside)
      have strict := lifted.reading_lt targetCoherent unequal
      simp only [Parents.representedValue, found, Option.map_some, Option.getD_some] at above
      omega
  · exact relocationHead_above sourceCoherent sourceValid targetCoherent targetValid view positive inside fence a

theorem relocate_takeAbove (d : Nat) (e : NumericalExpr)
    (source target : ParentContext) (visible : List Nat)
    (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (view : Parents.NumericalView d source target visible) (positive : 0 < d)
    (owner : Nat) (inside : owner < source.length)
    (fence : Parents.Ancestor source 0 owner (source.length - 1))
    (legal : FiniteLegal d source e) :
    relocate d source target visible (takeAbove (Parents.reading source 0 owner) e) =
      takeAbove (Parents.reading target 0 (Parents.point visible owner)) (relocate d source target visible e) := by
  cases e with
  | nil => rfl
  | cons a hs rest =>
    have cutoff := relocationHead_above_iff sourceCoherent sourceValid targetCoherent targetValid view
      positive inside fence a legal.2.1
    by_cases high : Parents.reading source 0 owner < a[0]?.getD 0
    · have nextView := relocation_view_append sourceCoherent sourceValid targetCoherent targetValid view a
      have nextFence := Parents.append_above_fence sourceCoherent sourceValid positive inside fence a high
      have after := relocate_takeAbove d rest
        (source ++ [Parents.label d source a])
        (target ++ [Parents.label d target (relocationHead d source target visible a)]) (visible ++ [target.length])
        (Parents.coherent_append_label sourceCoherent a)
        (Parents.context_valid_append_label d source sourceValid a)
        (Parents.coherent_append_label targetCoherent _)
        (Parents.context_valid_append_label d target targetValid _) nextView positive owner
        (by simp; omega) (by simpa using nextFence) legal.2.2.2.2
      rw [← Parents.reading_prefix (List.prefix_append source _) 0 owner inside,
        Parents.point_append_old visible owner target.length (by rw [view.length]; exact inside),
        ← Parents.reading_prefix (List.prefix_append target _) 0 (Parents.point visible owner)
          (view.bounded owner inside)] at after
      simp only [takeAbove, if_pos high, relocate, if_pos (cutoff.mpr high)]
      exact congrArg (Expr.cons _ _) after
    · have targetLow := mt cutoff.mp high
      simp only [takeAbove, if_neg high, relocate, if_neg targetLow]

theorem relocate_rootBlock (d : Nat) (e : NumericalExpr)
    (source target : ParentContext) (visible : List Nat)
    (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (view : Parents.NumericalView d source target visible) (positive : 0 < d)
    (legal : FiniteLegal d source e) :
    relocate d source target visible (rootBlock e) = rootBlock (relocate d source target visible e) := by
  cases e with
  | nil => rfl
  | cons a hs rest =>
    have nextView := relocation_view_append sourceCoherent sourceValid targetCoherent targetValid view a
    have after := relocate_takeAbove d rest
      (source ++ [Parents.label d source a])
      (target ++ [Parents.label d target (relocationHead d source target visible a)]) (visible ++ [target.length])
      (Parents.coherent_append_label sourceCoherent a)
      (Parents.context_valid_append_label d source sourceValid a)
      (Parents.coherent_append_label targetCoherent _)
      (Parents.context_valid_append_label d target targetValid _) nextView positive source.length
      (by simp) (by simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel]; exact .refl _)
      legal.2.2.2.2
    rw [Parents.reading_append_label, ← view.length, Parents.point_append_last, Parents.reading_append_label] at after
    simpa only [rootBlock, relocate] using congrArg (Expr.cons _ _) after

theorem copied_rootBlock {d : Nat} {source target : ParentContext} {visible history : List Nat}
    {root cap : Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d source target visible history root cap delta phase) (positive : 0 < d)
    (e : NumericalExpr) (legal : FiniteLegal d source e) :
    copied d root cap delta phase source history (rootBlock e) =
      rootBlock (copied d root cap delta phase source history e) := by
  rw [← relocate_eq_copied scope (rootBlock e) (rootBlock_finiteLegal legal), ← relocate_eq_copied scope e legal]
  exact relocate_rootBlock d e source target visible scope.sourceCoherent scope.sourceValid
    scope.targetCoherent scope.targetValid scope.view positive legal

end BTnSSBMS.Source
