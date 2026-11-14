import BTnSSBMS.RelocationLegality
import BTnSSBMS.TransplantNaturality

/-! Exact parents at an actual transported position. A NumericalView
only preserves ancestry; it must not silently be strengthened to exact
parent preservation. These finite facts supply the extra information at
ordinary copied positions, including after their enclosing prefixes grow. -/
namespace BTnSSBMS.Parents

def ExactPosition (d : Nat) (source target : ParentContext) (visible : List Nat)
    (root : Nat) : Prop :=
  ∀ row, row < d → parent target row (point visible root) =
    (parent source row root).map (point visible)

theorem ExactPosition.extends {d root : Nat}
    {source sourceNext target targetNext : ParentContext} {visible nextVisible : List Nat}
    (exactAt : ExactPosition d source target visible root)
    (view : NumericalView d source target visible) (valid : ContextValid source)
    (inside : root < source.length)
    (sourcePrefix : source <+: sourceNext) (targetPrefix : target <+: targetNext)
    (visiblePrefix : visible <+: nextVisible) :
    ExactPosition d sourceNext targetNext nextVisible root := by
  intro row room
  rw [← point_prefix visiblePrefix root (by rw [view.length]; exact inside),
    ← parent_prefix_eq targetPrefix row (point visible root) (view.bounded root inside),
    ← parent_prefix_eq sourcePrefix row root inside, exactAt row room]
  cases selected : parent source row root with
  | none => rfl
  | some p =>
    simp only [Option.map_some]
    rw [← point_prefix visiblePrefix p (by
      rw [view.length]
      have earlier := parent_earlier valid selected
      omega)]

theorem exactPosition_append {d : Nat} {source target : ParentContext} {visible : List Nat}
    (sourceCoherent : Coherent d source) (sourceValid : ContextValid source)
    (targetCoherent : Coherent d target) (targetValid : ContextValid target)
    (view : NumericalView d source target visible) (a : List Nat) :
    ExactPosition d (source ++ [label d source a])
      (target ++ [label d target (Source.relocationHead d source target visible a)])
      (visible ++ [target.length]) source.length := by
  intro row room
  have last : point (visible ++ [target.length]) source.length = target.length := by
    rw [← view.length, point_append_last]
  rw [last, append_label_parent, append_label_parent,
    Source.relocationHead_parents sourceCoherent sourceValid targetCoherent targetValid view a row room]
  cases selected : (label d source a).parents[row]?.join with
  | none => rfl
  | some p =>
    simp only [Option.map_some]
    rw [point_append_old visible p target.length (by
      rw [view.length]
      exact label_parent_bound d source a row p selected)]

theorem exactPosition_identity (d : Nat) (context : ParentContext)
    (valid : ContextValid context) {root : Nat} (inside : root < context.length) :
    ExactPosition d context context (List.range context.length) root := by
  intro row room
  rw [point_range _ _ inside]
  cases selected : parent context row root with
  | none => rfl
  | some p =>
    simp only [Option.map_some]
    rw [point_range _ _ (by have before := parent_earlier valid selected; omega)]

theorem ExactPosition.positive_iff {d root row : Nat}
    {source target : ParentContext} {visible : List Nat}
    (exactAt : ExactPosition d source target visible root)
    (view : NumericalView d source target visible)
    (sourceUnit : UnitSteps d source) (targetUnit : UnitSteps d target)
    (inside : root < source.length) (room : row < d) :
    0 < reading target row (point visible root) ↔ 0 < reading source row root := by
  rw [sourceUnit root inside row room,
    targetUnit (point visible root) (view.bounded root inside) row room, exactAt row room]
  cases selected : parent source row root <;> simp

end BTnSSBMS.Parents
