import LaverLowerBounds.ControlAlignment
import LaverLowerBounds.SynchronousCopy

set_option autoImplicit false

namespace LaverLowerBounds.ParentBMS

theorem exists_last {s : Matrix} (hs : s ≠ []) : ∃ stem last, s = stem ++ [last] := by
  cases he : s.reverse with
  | nil =>
      have hh : s = [] := by simpa using congrArg List.reverse he
      exact False.elim (hs hh)
  | cons last rest =>
      exact ⟨rest.reverse, last, by simpa using congrArg List.reverse he⟩

theorem expand_graph {s : Matrix} (hl : Leftward s) (hn : Nested s) :
    Leftward (expand s 1) ∧ Nested (expand s 1) := by
  by_cases he : s = []
  · simpa only [he, expand_empty] using And.intro (he ▸ hl) (he ▸ hn)
  · obtain ⟨stem, last, rfl⟩ := exists_last he
    rw [expand_append]
    cases hc : last.getLast? with
    | none =>
        have hz : last = [] := List.getLast?_eq_none_iff.mp hc
        subst last
        rw [expandTail_empty]
        exact ⟨leftward_prefix ⟨[[]], rfl⟩ hl, nested_prefix ⟨[[]], rfl⟩ hl hn⟩
    | some root =>
        have hr : root < stem.length := hl (last.length - 1) stem.length root (by
          rw [parent_last, ← List.getLast?_eq_getElem?]; exact hc)
        let frame : CopyFrame := ⟨stem, last, root, hc, hr, hl, hn⟩
        exact ⟨frame.out_leftward, frame.out_nested⟩

namespace Cover

variable {s t : Matrix}

/-- One source step can be simulated by finitely many target preparations,
one synchronous copy, and a crop. Its target stopping budget strictly drops. -/
theorem step_simulation (f : Cover s t) (hs : s ≠ [])
    (hsl : Leftward s) (hsn : Nested s) (htl : Leftward t) (htn : Nested t)
    {n : Nat} (ht : PrefixDescent.Stops (fun a => expand a 1) t n) :
    ∃ t' : Matrix, ∃ _next : Cover (expand s 1) t',
      Leftward t' ∧ Nested t' ∧
      ∃ k, PrefixDescent.Stops (fun a => expand a 1) t' k ∧ k < n := by
  have tne : t ≠ [] := by
    have slen : 0 < s.length := by cases s <;> simp_all
    have hh := f.bounded 0 slen
    intro he
    simp only [he, List.length_nil] at hh
    omega
  obtain ⟨sstem, slast, rfl⟩ := exists_last hs
  cases hc : slast.getLast? with
  | none =>
      have hz := List.getLast?_eq_none_iff.mp hc
      subst slast
      let restricted := f.toEmbedding.restrict (show sstem.IsPrefix (sstem ++ [[]]) from ⟨[[]], rfl⟩)
      have hp : restricted.cropped.IsPrefix t.dropLast :=
        f.restrict_cropped_stem ⟨[[]], rfl⟩ (by intro he; have := congrArg List.length he; simp at this) hs
      obtain ⟨k, hk, hkn⟩ := PrefixDescent.stops_after_truncation
        (expand_preserves_stem 1) ht tne (hp.trans (expand_preserves_stem 1 t))
      refine ⟨restricted.cropped, ?_, leftward_prefix restricted.cropped_prefix htl,
        nested_prefix restricted.cropped_prefix htl htn, k, hk, hkn⟩
      simpa only [expand_append, expandTail_empty] using restricted.toCover htl
  | some root =>
      obtain ⟨tstem, tlast, rfl⟩ := exists_last tne
      obtain ⟨last', aligned, hheight, hcontrol, hleft, hnested,
        steps, remaining, hstops, _hrun, hbudget⟩ := align_control hc n tlast f htl htn ht
      have sr : root < sstem.length := hsl (slast.length - 1) sstem.length root (by
        rw [parent_last, ← List.getLast?_eq_getElem?]; exact hc)
      have tr : aligned.column root < tstem.length :=
        hleft (last'.length - 1) tstem.length (aligned.column root) (by
          rw [parent_last, ← List.getLast?_eq_getElem?]; exact hcontrol)
      let source : CopyFrame := ⟨sstem, slast, root, hc, sr, hsl, hsn⟩
      let target : CopyFrame := ⟨tstem, last', aligned.column root, hcontrol, tr, hleft, hnested⟩
      let pair : AlignedCopy source target := ⟨aligned, by dsimp [CopyFrame.row, source, target]; rw [hheight], rfl⟩
      have hp : pair.embedding.cropped.IsPrefix (expand (tstem ++ [last']) 1) := by
        rw [expand_append]
        exact pair.embedding.cropped_prefix
      obtain ⟨k, hk, hkr⟩ := PrefixDescent.stops_after_truncation
        (expand_preserves_stem 1) hstops (by simp) hp
      refine ⟨pair.embedding.cropped, ?_,
        leftward_prefix pair.embedding.cropped_prefix target.out_leftward,
        nested_prefix pair.embedding.cropped_prefix target.out_leftward target.out_nested,
        k, hk, by omega⟩
      rw [expand_append]
      exact pair.copiedCover

/-- Ancestor cover dominates the actual fixed-[1] stopping count. No global
well-ordering theorem or canonical numeric representation is assumed. -/
theorem stops {n : Nat} (ht : PrefixDescent.Stops (fun a => expand a 1) t n)
    (f : Cover s t) (hsl : Leftward s) (hsn : Nested s) (htl : Leftward t) (htn : Nested t) :
    ∃ k, PrefixDescent.Stops (fun a => expand a 1) s k ∧ k ≤ n := by
  induction n using Nat.strongRecOn generalizing s t with
  | ind n ih =>
      by_cases hs : s = []
      · subst s
        exact ⟨0, .done, Nat.zero_le _⟩
      · obtain ⟨t', next, nextLeft, nextNested, k, hk, hkn⟩ :=
          f.step_simulation hs hsl hsn htl htn ht
        have sourceNext := expand_graph hsl hsn
        obtain ⟨j, hj, hjk⟩ := ih k hkn hk next sourceNext.1 sourceNext.2 nextLeft nextNested
        exact ⟨j + 1, .step hs hj, by omega⟩

#print axioms step_simulation
#print axioms stops

end Cover
end LaverLowerBounds.ParentBMS
