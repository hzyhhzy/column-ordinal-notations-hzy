import BTnSSBMS.ExactNumericalPosition
import BTnSSBMS.PartialRebaseEntry

/-! Partial-rebase heads and their transport. All parents are the actual
frozen searches. No equality of independently rebased labels is assumed. -/
namespace BTnSSBMS.Source

def partialHead (context : ParentContext) (root cut : Nat) (position : List Nat) : List Nat :=
  let base := (context[root]?.getD default).coordinates
  shift base cut ((List.range cut).map (fun j => position[j]?.getD 0 - base[j]?.getD 0)) 1

theorem partialHead_width (context : ParentContext) (root cut : Nat) (position : List Nat) :
    (partialHead context root cut position).length = (context[root]?.getD default).coordinates.length :=
  shift_width ..

theorem partialHead_values {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (position : List Nat) {root cut : Nat}
    (positive : 0 < cut) (room : cut < d) (inside : root < context.length)
    (path : Parents.Ancestor (context ++ [Parents.label d context position]) (cut - 1) root context.length)
    (width : (context[root]?.getD default).coordinates.length = d) :
    (∀ j, j < cut → (partialHead context root cut position)[j]?.getD 0 = position[j]?.getD 0) ∧
    (∀ j, cut ≤ j → j < d → (partialHead context root cut position)[j]?.getD 0 = Parents.reading context j root) :=
  partial_rebase_head_values coherent position positive room inside path width

theorem partial_pair_transport {d : Nat} {source target : ParentContext} {visible : List Nat}
    (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (view : Parents.NumericalView d source target visible) (position : List Nat)
    {root cut : Nat} (positive : 0 < cut) (room : cut < d) (inside : root < source.length)
    (path : Parents.Ancestor (source ++ [Parents.label d source position]) (cut - 1) root source.length)
    (same : (Parents.label d source position).parents[cut]?.join = Parents.parent source cut root)
    (exactAt : Parents.ExactPosition d source target visible root) :
    let moved := relocationHead d source target visible position
    Parents.Ancestor (target ++ [Parents.label d target moved]) (cut - 1) (Parents.point visible root) target.length ∧
      (Parents.label d target moved).parents[cut]?.join = Parents.parent target cut (Parents.point visible root) := by
  dsimp only
  constructor
  · have extended := relocation_view_append sourceCoherent sourceValid targetCoherent targetValid view position
    have result := extended.lift (cut - 1) (by omega) root source.length (by simp; omega) (by simp) path
    rw [Parents.point_append_old visible root target.length (by rw [view.length]; exact inside),
      ← view.length, Parents.point_append_last] at result
    exact result
  · rw [relocationHead_parents sourceCoherent sourceValid targetCoherent targetValid view position cut room,
      same, exactAt cut room]

theorem partialHead_transport {d : Nat} {source target : ParentContext} {visible : List Nat}
    (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
    (sourceUnit : Parents.UnitSteps d source)
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (targetUnit : Parents.UnitSteps d target) (view : Parents.NumericalView d source target visible)
    (position : List Nat) (positionUnit : Parents.UnitSteps d (source ++ [Parents.label d source position]))
    {root cut : Nat} (positive : 0 < cut) (room : cut < d) (inside : root < source.length)
    (path : Parents.Ancestor (source ++ [Parents.label d source position]) (cut - 1) root source.length)
    (same : (Parents.label d source position).parents[cut]?.join = Parents.parent source cut root)
    (exactAt : Parents.ExactPosition d source target visible root)
    (sourceWidth : (source[root]?.getD default).coordinates.length = d)
    (targetWidth : (target[Parents.point visible root]?.getD default).coordinates.length = d) :
    relocationHead d source target visible (partialHead source root cut position) =
      partialHead target (Parents.point visible root) cut (relocationHead d source target visible position) := by
  have oldValues := partialHead_values sourceCoherent position positive room inside path sourceWidth
  have movedPair := partial_pair_transport sourceCoherent sourceValid targetCoherent targetValid view
    position positive room inside path same exactAt
  have newValues := partialHead_values targetCoherent (relocationHead d source target visible position)
    positive room (view.bounded root inside) movedPair.1 targetWidth
  apply List.ext_getElem
  · rw [relocationHead_width, partialHead_width, targetWidth]
  · intro row left right
    have bounded : row < d := by simpa only [relocationHead_width] using left
    have values : (relocationHead d source target visible (partialHead source root cut position))[row]?.getD 0 =
        (partialHead target (Parents.point visible root) cut
          (relocationHead d source target visible position))[row]?.getD 0 := by
      rw [relocationHead_value d source target visible _ bounded]
      unfold Parents.representedValue
      rw [Parents.partial_rebase_head_parents sourceCoherent sourceValid sourceUnit position
        (partialHead source root cut position) positionUnit room inside same oldValues.1 oldValues.2 row bounded]
      by_cases below : row < cut
      · rw [if_pos below, newValues.1 row below, relocationHead_value d source target visible position bounded]
        rfl
      · rw [if_neg below, newValues.2 row (by omega) bounded,
          targetUnit (Parents.point visible root) (view.bounded root inside) row bounded, exactAt row bounded]
        cases selected : Parents.parent source row root <;> rfl
    simpa only [List.getElem?_eq_getElem left, List.getElem?_eq_getElem right, Option.getD_some] using values

end BTnSSBMS.Source
