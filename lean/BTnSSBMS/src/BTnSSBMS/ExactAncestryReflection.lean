import BTnSSBMS.ExactNumericalPosition

/-!
Ancestry reflection above a possibly exceptional copy root. Ordinary
positions need exact parents, not just an ancestry-preserving view.
The forced root itself is deliberately not required to be exact.
-/
namespace BTnSSBMS.Parents

theorem NumericalView.reflect_after {d : Nat}
    {source target : ParentContext} {visible : List Nat}
    (view : NumericalView d source target visible)
    (sourceValid : ContextValid source) (targetValid : ContextValid target)
    (cutoff : Nat)
    (exactAt : ∀ position, cutoff < position → position < source.length →
      ExactPosition d source target visible position)
    {row first last : Nat} (room : row < d) (after : cutoff < first)
    (firstInside : first < source.length) (lastInside : last < source.length)
    (path : Ancestor target row (point visible first) (point visible last)) :
    Ancestor source row first last := by
  induction last using Nat.strongRecOn with
  | ind last ih =>
    have ordered : first ≤ last := by
      by_cases forward : first ≤ last
      · exact forward
      · have reverse := view.increasing last first (by omega) firstInside
        have direction := path.le targetValid
        omega
    by_cases same : first = last
    · subst last
      exact .refl _
    · have earlier : first < last := by omega
      have different : point visible first ≠ point visible last := by
        have strict := view.increasing first last earlier lastInside
        omega
      obtain ⟨p, edge, previous⟩ := (Ancestor.iff_parent different).mp path
      rw [exactAt last (by omega) lastInside row room] at edge
      cases selected : parent source row last with
      | none => simp only [selected, Option.map_none] at edge; cases edge
      | some q =>
        have pointEq : point visible q = p := by
          simpa only [selected, Option.map_some, Option.some.injEq] using edge
        rw [← pointEq] at previous
        have before := parent_earlier sourceValid selected
        exact .up selected (ih q before (by omega) previous)

end BTnSSBMS.Parents
