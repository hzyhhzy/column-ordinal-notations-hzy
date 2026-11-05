import LaverLowerBounds.ParentPreparation

set_option autoImplicit false

namespace LaverLowerBounds.ParentBMS
namespace Cover

variable {s t : Matrix} {lastS lastT : Column}

theorem last_column (f : Cover (s ++ [lastS]) (t ++ [lastT])) : f.column s.length = t.length := by
  simpa only [List.length_append, List.length_singleton, Nat.add_sub_cancel] using f.last (by simp)

/-- Replace only the last target column after checking the source's last edges.
All earlier target paths remain in the unchanged prefix. -/
def replaceLast (f : Cover (s ++ [lastS]) (t ++ [lastT])) (newLast : Column)
    (ht : Leftward (t ++ [lastT]))
    (hnew : ∀ row p, lastS[row]? = some p → Ancestor (t ++ [newLast]) row (f.column p) t.length) :
    Cover (s ++ [lastS]) (t ++ [newLast]) where
  column := f.column
  bounded i hi := by simpa only [List.length_append, List.length_singleton] using f.bounded i hi
  strict := f.strict
  edge row p i he := by
    have hi := parent_column_lt he
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hilast : i = s.length
    · subst i
      rw [f.last_column]
      exact hnew row p (by rwa [parent_last] at he)
    · have hiold : i < s.length := by omega
      have hit : f.column i < t.length := by
        have hg := f.strict i s.length hiold (by simp)
        rwa [f.last_column] at hg
      have ha := (f.edge row p i he).of_prefix ⟨[lastT], rfl⟩ ht hit
      exact ha.to_prefix_extension ⟨[newLast], rfl⟩
  last hs := by simpa only [List.length_append, List.length_singleton] using f.last hs

theorem active_height (f : Cover (s ++ [lastS]) (t ++ [lastT])) : lastS.length ≤ lastT.length := by
  by_cases hz : lastS.length = 0
  · omega
  · have hs : lastS.length - 1 < lastS.length := by omega
    let p := lastS[lastS.length - 1]
    have hp : parent (s ++ [lastS]) (lastS.length - 1) s.length = some p := by
      rw [parent_last, List.getElem?_eq_getElem hs]
    have ha := f.edge _ _ _ hp
    rw [f.last_column] at ha
    have existsParent : ∃ q, parent (t ++ [lastT]) (lastS.length - 1) t.length = some q := by
      cases ha with
      | direct he => exact ⟨_, he⟩
      | step he _ => exact ⟨_, he⟩
    obtain ⟨q, hq⟩ := existsParent
    rw [parent_last] at hq
    have hlt := (List.getElem?_eq_some_iff.mp hq).1
    omega

/-- A nonaligned control pair can be prepared without losing any covered edge.
The same finite column map is retained. -/
def prepared (f : Cover (s ++ [lastS]) (t ++ [lastT])) {c root : Nat}
    (hs : lastS.getLast? = some c) (htop : lastT.getLast? = some root)
    (hr : root < t.length) (ht : Leftward (t ++ [lastT]))
    (hnot : lastS.length < lastT.length ∨
      (lastS.length = lastT.length ∧ f.column c ≠ root)) :
    Cover (s ++ [lastS]) (prepare t lastT (lastT.length - 1) root) := by
  apply f.replaceLast (lastT.take (lastT.length - 1) ++ (t[root]?.getD []).drop (lastT.length - 1)) ht
  intro row p hp
  have hrow : row < lastS.length := (List.getElem?_eq_some_iff.mp hp).1
  have covered := f.edge row p s.length (by rw [parent_last]; exact hp)
  rw [f.last_column] at covered
  by_cases hlo : row < lastT.length - 1
  · exact ancestry_prepare_low (Nat.sub_le _ _) hlo covered
  · have hsLen : 0 < lastS.length := by
      cases lastS with
      | nil => simp at hs
      | cons _ _ => simp
    have hlength : lastS.length = lastT.length := by rcases hnot with hh | ⟨hh, _⟩ <;> omega
    have hcontrol : row = lastT.length - 1 := by omega
    have heq : row = lastS.length - 1 := by omega
    have hsp : p = c := by
      rw [List.getLast?_eq_getElem?, ← heq, hp] at hs
      exact Option.some.inj hs
    subst p
    have htc : parent (t ++ [lastT]) row t.length = some root := by
      rw [parent_last, hcontrol, ← List.getLast?_eq_getElem?]
      exact htop
    have different : f.column c ≠ root := by rcases hnot with hh | ⟨_, hh⟩ <;> omega
    have hanc : Ancestor (t ++ [lastT]) row (f.column c) root :=
      (covered.strip htc).resolve_left different
    have hpref := hanc.of_prefix ⟨[lastT], rfl⟩ ht hr
    exact ancestry_prepare_from_root (Nat.sub_le _ _) (by omega) hr hpref

#print axioms prepared

end Cover
end LaverLowerBounds.ParentBMS
