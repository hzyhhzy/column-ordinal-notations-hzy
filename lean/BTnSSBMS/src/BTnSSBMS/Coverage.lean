import BTnSSBMS.Syntax

/-!
The standardness argument in section 6, separated from its finite hypotheses.

The target's expansion relation is required to be well-founded only on its
standard domain. Numerical legality and a lexicographic bound are NOT used
as substitutes for the missing finite coverage property.
-/
namespace BTnSSBMS
namespace Coverage

/-- A finite sequence of actual downward steps, including the empty path. -/
inductive Descends (step : α → α → Prop) (target : α) : α → Prop where
  | refl : Descends step target target
  | prepend {middle start : α} :
      step middle start → Descends step target middle → Descends step target start

theorem Descends.closed {step : α → α → Prop} {standard : α → Prop}
    (closed : ∀ {a b}, standard b → step a b → standard a)
    {target start : α} (path : Descends step target start) (hs : standard start) :
    standard target := by
  induction path with
  | refl => exact hs
  | prepend edge rest ih => exact ih (closed hs edge)

/-- Covering a fixed finite target below every larger standard term suffices.

This is a genuinely conditional lemma. Instantiating `covers` for the encoder
requires the still-unformalized BN/SB lemmas and finite last-hole argument.
-/
theorem reaches_of_coverage {α : Type} (step lt : α → α → Prop)
    (standard : α → Prop) (target start : α)
    (closed : ∀ {a b}, standard b → step a b → standard a)
    (wf : WellFounded (fun a b : {x // standard x} => step a.val b.val))
    (covers : ∀ h, standard h → lt target h →
      ∃ child, step child h ∧ (target = child ∨ lt target child))
    (hs : standard start) (bound : target = start ∨ lt target start) :
    Descends step target start := by
  have go : ∀ s : {x // standard x},
      Acc (fun a b : {x // standard x} => step a.val b.val) s →
      (target = s.val ∨ lt target s.val) → Descends step target s.val := by
    intro s accessible
    induction accessible with
    | intro s smaller ih =>
      intro hbound
      rcases hbound with same | strict
      · rw [← same]
        exact .refl
      · obtain ⟨child, edge, remaining⟩ := covers s.val s.property strict
        have child_standard : standard child := closed s.property edge
        exact .prepend edge (ih ⟨child, child_standard⟩ edge remaining)
  exact go ⟨start, hs⟩ (wf.apply ⟨start, hs⟩) bound

theorem standard_of_coverage {α : Type} (step lt : α → α → Prop)
    (standard : α → Prop) (target start : α)
    (closed : ∀ {a b}, standard b → step a b → standard a)
    (wf : WellFounded (fun a b : {x // standard x} => step a.val b.val))
    (covers : ∀ h, standard h → lt target h →
      ∃ child, step child h ∧ (target = child ∨ lt target child))
    (hs : standard start) (bound : target = start ∨ lt target start) :
    standard target :=
  Descends.closed (step := step) (standard := standard) (target := target) (start := start) closed
    (reaches_of_coverage step lt standard target start closed wf covers hs bound) hs

end Coverage
end BTnSSBMS
