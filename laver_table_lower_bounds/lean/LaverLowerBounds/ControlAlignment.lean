import LaverLowerBounds.CoverPreparation

set_option autoImplicit false

namespace LaverLowerBounds.ParentBMS

/-- Preparation reaches the source control pair. Termination is proved using
the concrete target stopping budget, avoiding a separate numeric lexicographic
ranking and avoiding any global well-foundedness assumption. -/
theorem align_control {s t : Matrix} {lastS : Column} {c : Nat}
    (hs : lastS.getLast? = some c) (n : Nat) :
    ∀ lastT (_f : Cover (s ++ [lastS]) (t ++ [lastT])),
      Leftward (t ++ [lastT]) → Nested (t ++ [lastT]) →
      PrefixDescent.Stops (fun a => expand a 1) (t ++ [lastT]) n →
      ∃ last' : Column, ∃ aligned : Cover (s ++ [lastS]) (t ++ [last']),
        last'.length = lastS.length ∧ last'.getLast? = some (aligned.column c) ∧
        Leftward (t ++ [last']) ∧ Nested (t ++ [last']) ∧
        ∃ steps remaining,
          PrefixDescent.Stops (fun a => expand a 1) (t ++ [last']) remaining ∧
          PrefixDescent.MixedRun (fun a => expand a 1) (t ++ [lastT]) (t ++ [last']) steps ∧
          steps + remaining ≤ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro lastT f hleft hnested hstops
      by_cases haligned : lastT.length = lastS.length ∧ lastT.getLast? = some (f.column c)
      · exact ⟨lastT, f, haligned.1, haligned.2, hleft, hnested,
          0, n, hstops, .refl _, by omega⟩
      · have hlen := f.active_height
        have hspos : 0 < lastS.length := by
          cases lastS with
          | nil => simp at hs
          | cons _ _ => simp
        have htpos : 0 < lastT.length := by omega
        cases htop : lastT.getLast? with
        | none =>
            have hlt : lastT.length - 1 < lastT.length := by omega
            rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hlt] at htop
            contradiction
        | some root =>
            have hcontrol : parent (t ++ [lastT]) (lastT.length - 1) t.length = some root := by
              rw [parent_last, ← List.getLast?_eq_getElem?]
              exact htop
            have hr : root < t.length := hleft _ _ _ hcontrol
            have hnot : lastS.length < lastT.length ∨
                (lastS.length = lastT.length ∧ f.column c ≠ root) := by
              by_cases hlt : lastS.length < lastT.length
              · exact Or.inl hlt
              · have he : lastS.length = lastT.length := by omega
                refine Or.inr ⟨he, ?_⟩
                intro hsame
                exact haligned ⟨he.symm, by rw [hsame]; exact htop⟩
            let nextLast := lastT.take (lastT.length - 1) ++ (t[root]?.getD []).drop (lastT.length - 1)
            let nextCover : Cover (s ++ [lastS]) (t ++ [nextLast]) := f.prepared hs htop hr hleft hnot
            have nextLeft : Leftward (t ++ [nextLast]) := prepare_leftward (Nat.sub_le _ _) hr hleft
            have nextNested : Nested (t ++ [nextLast]) :=
              prepare_nested (Nat.sub_le _ _) hr hcontrol hleft hnested
            obtain ⟨k, hk, hkn⟩ := prepare_spends_budget htop hr hstops
            obtain ⟨last', aligned, hheight, hparent, hleft', hnested', steps, remaining,
              hstop', hrun, hbudget⟩ := ih k hkn nextLast nextCover nextLeft nextNested hk
            refine ⟨last', aligned, hheight, hparent, hleft', hnested', steps + 1, remaining,
              hstop', ?_, by omega⟩
            exact .step (by simp) (by rw [expand_append]; exact prepare_prefix_one htop hr) hrun

#print axioms align_control

end LaverLowerBounds.ParentBMS
