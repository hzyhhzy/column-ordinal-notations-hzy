import BTnSSBMS.NumericalLegality

/-!
The finite first-diagonal argument. Only the head consequences of BN and
SB below the requested row are used. The concrete whole-block conditions
are connected to these head consequences in `BMSBlocks`.
-/
namespace BTnSSBMS.Parents

/-- Lexicographic domination from `lower` onward, stated by the first
possible unequal coordinate. All compared coordinates are within width d. -/
def HeadDominates (d : Nat) (context : ParentContext) (lower a b : Nat) : Prop :=
  ∀ row, lower ≤ row → row < d →
    (∀ j, lower ≤ j → j < row → reading context j a = reading context j b) →
    reading context row b ≤ reading context row a

def HeadBN (d : Nat) (context : ParentContext) : Prop :=
  ∀ a b, a < b → b < context.length → parent context 0 a = parent context 0 b →
    HeadDominates d context 0 a b

def HeadSB (d : Nat) (context : ParentContext) (row : Nat) : Prop :=
  ∀ a b, a < b → b < context.length → Ancestor context (row - 1) a b →
    parent context row a = parent context row b → HeadDominates d context row a b

theorem HeadDominates.refl (d : Nat) (context : ParentContext) (lower a : Nat) :
    HeadDominates d context lower a a := by
  intro row _ _ _
  exact Nat.le_refl _

/-- If a sibling is already maximal in every remaining coordinate,
head domination forces the earlier sibling to be maximal as well. -/
theorem saturated_of_dominates {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context) (unit : UnitSteps d context)
    {lower top g a b : Nat} (room : top < d) (_rows : lower ≤ top)
    (edge : parent context lower a = some g) (dominates : HeadDominates d context lower a b)
    (saturated : ∀ j, lower ≤ j → j ≤ top → reading context j b = reading context j g + 1) :
    ∀ j, lower ≤ j → j ≤ top → reading context j a = reading context j g + 1 := by
  intro j hj hk
  induction j using Nat.strongRecOn with
  | ind j ih =>
    have previous : ∀ k, lower ≤ k → k < j → reading context k a = reading context k g + 1 := by
      intro k hLower hBefore
      exact ih k hBefore hLower (by omega)
    have upper := child_coordinate_ceiling coherent valid unit (by omega : j < d) hj edge previous
    have bottom := dominates j hj (by omega) (by
      intro k hLower hBefore
      rw [previous k hLower hBefore, saturated k hLower (by omega)])
    rw [saturated j hj hk] at bottom
    omega

/-- Descend the row index while keeping a child saturated through `top`.
Crucially the induction only asks for SB_j at j strictly below top. -/
theorem lower_saturated_child {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context) (unit : UnitSteps d context)
    {top g : Nat} (room : top < d)
    (side : ∀ j, 0 < j → j < top → HeadSB d context j)
    (row : Nat) (below : row < top) (q : Nat)
    (edge : parent context row q = some g)
    (saturated : ∀ j, row ≤ j → j ≤ top → reading context j q = reading context j g + 1) :
    ∃ child, parent context 0 child = some g ∧
      ∀ j, j ≤ top → reading context j child = reading context j g + 1 := by
  induction row generalizing q with
  | zero => exact ⟨q, edge, fun j hj => saturated j (Nat.zero_le _) hj⟩
  | succ row ih =>
    obtain ⟨child, first, higher, path⟩ :=
      lower_child_of_higher_parent coherent valid unit (by omega : row + 1 < d) edge
    have qBound : q < context.length := by
      obtain ⟨a, lookup, _⟩ := Option.bind_eq_some_iff.mp edge
      exact (List.getElem?_eq_some_iff.mp lookup).choose
    have dominates : HeadDominates d context (row + 1) child q := by
      by_cases same : child = q
      · subst child
        exact HeadDominates.refl d context (row + 1) q
      · have before : child < q := by have order := path.le valid; omega
        exact side (row + 1) (by omega) below child q before qBound
          (by simpa only [Nat.add_sub_cancel] using path) (higher.trans edge.symm)
    have recovered := saturated_of_dominates coherent valid unit room (by omega : row + 1 ≤ top)
      higher dominates saturated
    apply ih (by omega) child first
    intro j hj hk
    by_cases same : j = row
    · subst j
      exact unit.at_parent (by omega) first
    · exact recovered j (by omega) hk

/-- A strict row-top descendant forces a saturated direct row-zero
child. This does not yet say that it is the first child. -/
theorem saturated_zero_child {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context) (unit : UnitSteps d context)
    {top g endpoint : Nat} (positive : 0 < top) (room : top < d)
    (side : ∀ j, 0 < j → j < top → HeadSB d context j)
    (path : Ancestor context top g endpoint) (strict : g ≠ endpoint) :
    ∃ child, parent context 0 child = some g ∧
      ∀ j, j ≤ top → reading context j child = reading context j g + 1 := by
  obtain ⟨q, direct, _⟩ := path.first_child strict
  cases top with
  | zero => omega
  | succ top =>
    obtain ⟨child, first, higher, _⟩ := lower_child_of_higher_parent coherent valid unit room direct
    apply lower_saturated_child coherent valid unit room side top (by omega) child first
    intro j hj hk
    by_cases same : j = top
    · subst j
      exact unit.at_parent (by omega) first
    · have same : j = top + 1 := by omega
      subst j
      exact unit.at_parent room higher

/-- The first-diagonal theorem using explicit finite head conditions.
It needs BN and only SB_1,...,SB_(top-1), never SB_top. -/
theorem first_diagonal {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context) (unit : UnitSteps d context)
    {top g endpoint : Nat} (positive : 0 < top) (room : top < d)
    (siblings : HeadBN d context)
    (side : ∀ j, 0 < j → j < top → HeadSB d context j)
    (path : Ancestor context top g endpoint) (strict : g ≠ endpoint) :
    g + 1 < context.length ∧ parent context 0 (g + 1) = some g ∧
      ∀ j, j ≤ top → reading context j (g + 1) = reading context j g + 1 := by
  obtain ⟨child, edge, saturated⟩ := saturated_zero_child coherent valid unit positive room side path strict
  obtain ⟨before, first⟩ := immediate_zero_child coherent valid (by omega) edge
  have childBound : child < context.length := by
    obtain ⟨a, lookup, _⟩ := Option.bind_eq_some_iff.mp edge
    exact (List.getElem?_eq_some_iff.mp lookup).choose
  refine ⟨by omega, first, ?_⟩
  by_cases same : g + 1 = child
  · simpa only [same] using saturated
  · have dominates := siblings (g + 1) child (by omega) childBound (first.trans edge.symm)
    exact fun j hj => saturated_of_dominates coherent valid unit room (Nat.zero_le _)
      first dominates (fun k _ hk => saturated k hk) j (Nat.zero_le _) hj

end BTnSSBMS.Parents
