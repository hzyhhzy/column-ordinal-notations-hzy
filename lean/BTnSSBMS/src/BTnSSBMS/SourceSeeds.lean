import BTnSSBMS.SourceCopyHead

/-! All diagonal source seeds satisfy the ordinary finite legality
conditions. There is no bound on dimension, seed index, or nesting. -/
namespace BTnSSBMS.Parents

theorem UnitSteps.append_successor {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context)
    (unit : UnitSteps d context) (nonempty : 0 < context.length) (a : List Nat)
    (values : ∀ j, j < d → a[j]?.getD 0 = reading context j (context.length - 1) + 1) :
    UnitSteps d (context ++ [label d context a]) := by
  apply unit.extend_one (context_valid_append_label d context valid a) (List.prefix_append _ _) (by simp)
  intro j room
  rw [reading_append_label, append_label_parent,
    constant_numerical_parents coherent valid (Nat.le_refl d) (context.length - 1) (context.length - 1)
      (by omega) (by omega) (.refl _) a values j room]
  simp only [Option.map_some, Option.getD_some]
  rw [← reading_prefix (List.prefix_append context [label d context a]) j (context.length - 1) (by omega)]
  exact values j room

theorem zero_context_unitSteps (d : Nat) : UnitSteps d [label d [] (List.replicate d 0)] := by
  rw [BMS.zero_seed_label]
  intro position inside j room
  have same : position = 0 := by simpa using inside
  subst position
  simp only [reading, parent, List.getElem?_cons_zero, Option.getD_some, Option.bind_some]
  simp [room]

end BTnSSBMS.Parents

namespace BTnSSBMS.Source

theorem diagonalTail_above (d k level owner : Nat) (positive : 0 < d) (above : owner < level) :
    ∀ a ∈ labels (diagonalTail d k level), owner < a[0]?.getD 0 := by
  cases k with
  | zero => simp [diagonalTail, labels]
  | succ k =>
    intro a member
    have same : a = List.replicate d level := by simpa [diagonalTail, labels] using member
    subst a
    simpa [List.getElem?_replicate, positive] using above

theorem diagonalTail_finiteLegal (d k level : Nat) (positive : 0 < d) (levelPositive : 0 < level)
    (context : ParentContext) (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (unit : Parents.UnitSteps d context) (nonempty : 0 < context.length)
    (frontier : ∀ j, j < d → Parents.reading context j (context.length - 1) + 1 = level) :
    FiniteLegal d context (diagonalTail d k level) := by
  induction k generalizing context level with
  | zero => trivial
  | succ k ih =>
    let a := List.replicate d level
    let next := context ++ [Parents.label d context a]
    have newUnit : Parents.UnitSteps d next := unit.append_successor coherent valid nonempty a (by
      intro j room
      simpa only [a, List.getElem?_replicate, if_pos room, Option.getD_some] using (frontier j room).symm)
    have newCoherent := Parents.coherent_append_label coherent a
    have newValid := Parents.context_valid_append_label d context valid a
    have tailLegal : FiniteLegal d next (diagonalTail d k (level + 1)) :=
      ih (level + 1) (by omega) next newCoherent newValid newUnit (by simp [next]) (by
        intro j room
        have endIndex : next.length - 1 = context.length := by simp [next]
        rw [endIndex, Parents.reading_append_label]
        simp [a, room])
    refine ⟨by simp, newUnit, ?_, ?_, trivial⟩
    · intro _ j room
      simpa only [List.getElem?_replicate, if_pos room, Option.getD_some] using levelPositive
    · refine ⟨?_, tailLegal, trivial⟩
      have headZero : (List.replicate d level)[0]?.getD 0 = level := by
        simp [positive]
      rw [headZero]
      exact diagonalTail_above d k (level + 1) level positive (by omega)

theorem seed_finiteLegal (d k : Nat) (positive : 0 < d) : FiniteLegal d [] (seed d k) := by
  have coherent := Parents.coherent_append_label (Parents.empty_coherent d) (List.replicate d 0)
  have valid := Parents.context_valid_append_label d [] Parents.empty_context_valid (List.replicate d 0)
  have unit := Parents.zero_context_unitSteps d
  refine ⟨by simp, unit, ?_, trivial, ?_⟩
  · intro impossible
    exact False.elim (impossible rfl)
  · apply diagonalTail_finiteLegal d k 1 positive (by omega) _ coherent valid unit (by simp)
    intro j room
    simp [Parents.reading, Parents.label, room]

end BTnSSBMS.Source

namespace BTnSSBMS.Encoder

theorem seed_numericallyLegal (d k : Nat) (positive : 0 < d) :
    BMS.NumericallyLegal (d + 2) (fromSource d (seed d k)) :=
  finiteLegal_source_numericallyLegal d _ positive (Source.seed_finiteLegal d k positive)

end BTnSSBMS.Encoder
