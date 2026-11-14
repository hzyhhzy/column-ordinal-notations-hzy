import BTnSSBMS.NumericalRelocation
import BTnSSBMS.SBCopyAncestry

/-! Naturality of the mixed head at an ordinary copy seam. Low rows come
from the removed terminal; high rows come from the previous forced root.
Only the high parents of that root must be exact. An ancestry-preserving
view is not silently treated as exact parent transport. -/
namespace BTnSSBMS.Source

theorem first_copy_head_relocation {d : Nat} {source target : ParentContext} {visible : List Nat}
    (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
    (view : Parents.NumericalView d source target visible) (targetUnit : Parents.UnitSteps d target)
    (terminal oldHead newHead : List Nat) (width : newHead.length = d) {cap root : Nat}
    (room : cap < d)
    (selected : (Parents.label d source terminal).parents[cap]?.join = some root)
    (highParents : ∀ row, cap ≤ row → row < d →
      Parents.parent target row (Parents.point visible root) =
        (Parents.parent source row root).map (Parents.point visible))
    (oldLow : ∀ row, row < cap → oldHead[row]?.getD 0 = terminal[row]?.getD 0)
    (oldHigh : ∀ row, cap ≤ row → row < d → oldHead[row]?.getD 0 = Parents.reading source row root)
    (newLow : ∀ row, row < cap → newHead[row]?.getD 0 =
      (relocationHead d source target visible terminal)[row]?.getD 0)
    (newHigh : ∀ row, cap ≤ row → row < d →
      newHead[row]?.getD 0 = Parents.reading target row (Parents.point visible root)) :
    relocationHead d source target visible oldHead = newHead := by
  have inside := Parents.label_parent_bound d source terminal cap root selected
  have parents := Parents.first_copy_head_parents sourceCoherent sourceValid terminal oldHead
    room selected oldLow oldHigh
  apply List.ext_getElem
  · rw [relocationHead_width, width]
  · intro row left right
    have rowRoom : row < d := by simpa only [relocationHead_width] using left
    have value : (relocationHead d source target visible oldHead)[row]?.getD 0 = newHead[row]?.getD 0 := by
      rw [relocationHead_value d source target visible oldHead rowRoom]
      unfold Parents.representedValue
      rw [parents row rowRoom]
      by_cases low : row < cap
      · rw [if_pos low, newLow row low, relocationHead_value d source target visible terminal rowRoom]
        rfl
      · rw [if_neg low, newHigh row (by omega) rowRoom,
          targetUnit (Parents.point visible root) (view.bounded root inside) row rowRoom,
          highParents row (by omega) rowRoom]
        cases edge : Parents.parent source row root <;> rfl
    simpa only [List.getElem?_eq_getElem left, List.getElem?_eq_getElem right, Option.getD_some] using value

end BTnSSBMS.Source
