import BTnSSBMS.SourceCopyHead

/-!
Scoped ordinary-copy state. Activation histories are interpreted using
actual source ancestry. The invariant is preserved by recomputing target
parents, rather than installing the expected parent table by definition.
-/
namespace BTnSSBMS.BMS

theorem HistoryCorrect.extend_context {small large : ParentContext} {root cap : Nat} {history : List Nat}
    (correct : HistoryCorrect small root cap history) (initial : small <+: large)
    (valid : Parents.ContextValid large) (length : history.length ≤ small.length) :
    HistoryCorrect large root cap history := by
  intro i inside j
  rw [correct i inside j]
  constructor
  · rintro ⟨room, path⟩
    exact ⟨room, path.prefix initial⟩
  · rintro ⟨room, path⟩
    exact ⟨room, path.restrict initial valid (by omega)⟩

end BTnSSBMS.BMS

namespace BTnSSBMS.Keys

theorem threshold_at_label {d : Nat} {source : ParentContext} {history : List Nat} {root cap : Nat}
    (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (correct : BMS.HistoryCorrect source root cap history) (length : history.length = source.length)
    (afterRoot : root < source.length) (capBound : cap ≤ d) (a : List Nat) (j : Nat) :
    j < threshold cap root history (Parents.label d source a) ↔
      j < cap ∧ Parents.Ancestor (source ++ [Parents.label d source a]) j root source.length := by
  have nextValid := Parents.context_valid_append_label d source valid a
  have nextCorrect := correct.extend_context (List.prefix_append source [Parents.label d source a]) nextValid (by omega)
  have step := BMS.activation_correct nextValid (Parents.coherent_append_label coherent a)
    root cap capBound history source.length length nextCorrect j
  have same : BMS.activation (source ++ [Parents.label d source a]) root cap history source.length =
      threshold cap root history (Parents.label d source a) := by
    simp only [BMS.activation, show ¬ source.length < root by omega, if_false,
      show ¬ source.length = root by omega, List.getElem?_concat_length, Option.getD_some]
    rfl
  rw [same] at step
  exact step

theorem threshold_at_parent {d : Nat} {source : ParentContext} {history : List Nat} {root cap : Nat}
    (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (correct : BMS.HistoryCorrect source root cap history) (length : history.length = source.length)
    (afterRoot : root < source.length) (capBound : cap ≤ d) (a : List Nat) {j p : Nat}
    (selected : (Parents.label d source a).parents[j]?.join = some p) :
    j < threshold cap root history (Parents.label d source a) ↔ j < history[p]?.getD 0 := by
  rw [threshold_at_label coherent valid correct length afterRoot capBound a j]
  have bound := Parents.label_parent_bound d source a j p selected
  have nextCorrect := correct.extend_context (List.prefix_append source [Parents.label d source a])
    (Parents.context_valid_append_label d source valid a) (by omega)
  rw [Parents.Ancestor.iff_parent (by omega : root ≠ source.length), Parents.append_label_parent, selected]
  simp only [Option.some.injEq, exists_eq_left']
  exact (nextCorrect p (by omega) j).symm

theorem threshold_at_missing {d : Nat} {source : ParentContext} {history : List Nat} {root cap : Nat}
    (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (correct : BMS.HistoryCorrect source root cap history) (length : history.length = source.length)
    (afterRoot : root < source.length) (capBound : cap ≤ d) (a : List Nat) {j : Nat}
    (missing : (Parents.label d source a).parents[j]?.join = none) :
    ¬ j < threshold cap root history (Parents.label d source a) := by
  rw [threshold_at_label coherent valid correct length afterRoot capBound a j,
    Parents.Ancestor.iff_parent (by omega : root ≠ source.length), Parents.append_label_parent, missing]
  simp

theorem history_append_threshold {d : Nat} {source : ParentContext} {history : List Nat} {root cap : Nat}
    (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (correct : BMS.HistoryCorrect source root cap history) (length : history.length = source.length)
    (afterRoot : root < source.length) (capBound : cap ≤ d) (a : List Nat) :
    BMS.HistoryCorrect (source ++ [Parents.label d source a]) root cap
      (history ++ [threshold cap root history (Parents.label d source a)]) := by
  have previous := correct.extend_context (List.prefix_append source [Parents.label d source a])
    (Parents.context_valid_append_label d source valid a) (by omega)
  intro i inside j
  by_cases old : i < history.length
  · rw [List.getElem?_append_left old]
    exact previous i old j
  · have same : i = history.length := by simp only [List.length_append, List.length_cons, List.length_nil] at inside; omega
    subst i
    rw [List.getElem?_concat_length, Option.getD_some, length]
    exact threshold_at_label coherent valid correct length afterRoot capBound a j

end BTnSSBMS.Keys

namespace BTnSSBMS.Source

/-- The incoming finite state after the copy root has been installed.
All fields concern computable arrays or finite parent paths. -/
structure ShiftView (d : Nat) (source target : ParentContext) (visible history : List Nat)
    (root cap : Nat) (delta : List Nat) (phase : Nat) : Prop where
  sourceCoherent : Parents.Coherent d source
  sourceValid : Parents.ContextValid source
  targetCoherent : Parents.Coherent d target
  targetValid : Parents.ContextValid target
  targetUnit : Parents.UnitSteps d target
  view : Parents.NumericalView d source target visible
  historyLength : history.length = source.length
  historyCorrect : BMS.HistoryCorrect source root cap history
  afterRoot : root < source.length
  capBound : cap ≤ d
  values : ∀ p, p < source.length → ∀ j, j < d →
    Parents.reading target j (Parents.point visible p) = Parents.reading source j p +
      if j < history[p]?.getD 0 then delta[j]?.getD 0 * phase else 0

theorem ShiftView.head_values {d : Nat} {source target : ParentContext} {visible history : List Nat}
    {root cap : Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d source target visible history root cap delta phase) (a : List Nat)
    (width : a.length = d) (unit : Parents.UnitSteps d (source ++ [Parents.label d source a]))
    (j : Nat) (room : j < d) :
    (shift a (Keys.threshold cap root history (Parents.label d source a)) delta phase)[j]?.getD 0 =
      Parents.representedValue target visible (Parents.label d source a) j := by
  rw [shift_value _ _ _ _ j (by omega)]
  have equation := unit source.length (by simp) j room
  rw [Parents.reading_append_label, Parents.append_label_parent] at equation
  cases selected : (Parents.label d source a).parents[j]?.join with
  | none =>
    have inactive := Keys.threshold_at_missing scope.sourceCoherent scope.sourceValid scope.historyCorrect
      scope.historyLength scope.afterRoot scope.capBound a selected
    simp only [selected, Option.map_none, Option.getD_none] at equation
    simp only [Parents.representedValue, selected, Option.map_none, Option.getD_none, equation, inactive, if_false,
      Nat.add_zero]
  | some p =>
    have bound := Parents.label_parent_bound d source a j p selected
    have active := Keys.threshold_at_parent scope.sourceCoherent scope.sourceValid scope.historyCorrect
      scope.historyLength scope.afterRoot scope.capBound a selected
    simp only [selected, Option.map_some, Option.getD_some] at equation
    rw [← Parents.reading_prefix (List.prefix_append source [Parents.label d source a]) j p bound] at equation
    simp only [Parents.representedValue, selected, Option.map_some, Option.getD_some]
    rw [scope.values p bound j room, equation]
    simp only [active]
    omega

theorem ShiftView.head_parents {d : Nat} {source target : ParentContext} {visible history : List Nat}
    {root cap : Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d source target visible history root cap delta phase) (a : List Nat)
    (width : a.length = d) (unit : Parents.UnitSteps d (source ++ [Parents.label d source a]))
    (j : Nat) (room : j < d) :
    (Parents.label d target (shift a (Keys.threshold cap root history (Parents.label d source a)) delta phase)).parents[j]?.join =
      ((Parents.label d source a).parents[j]?.join).map (Parents.point visible) :=
  Parents.label_parent_transport scope.sourceCoherent scope.sourceValid scope.targetCoherent scope.targetValid
    (Nat.le_refl d) scope.view a _ (scope.head_values a width unit) j room

theorem ShiftView.head_unitSteps {d : Nat} {source target : ParentContext} {visible history : List Nat}
    {root cap : Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d source target visible history root cap delta phase) (a : List Nat)
    (width : a.length = d) (unit : Parents.UnitSteps d (source ++ [Parents.label d source a])) :
    Parents.UnitSteps d (target ++ [Parents.label d target
      (shift a (Keys.threshold cap root history (Parents.label d source a)) delta phase)]) := by
  apply scope.targetUnit.extend_one (Parents.context_valid_append_label d target scope.targetValid _)
    (List.prefix_append _ _) (by simp)
  intro j room
  rw [Parents.reading_append_label, Parents.append_label_parent, scope.head_parents a width unit j room,
    scope.head_values a width unit j room]
  cases selected : (Parents.label d source a).parents[j]?.join with
  | none => simp only [Parents.representedValue, selected, Option.map_none, Option.getD_none]
  | some p =>
    have bound := Parents.label_parent_bound d source a j p selected
    simp only [Parents.representedValue, selected, Option.map_some, Option.getD_some]
    exact congrArg (· + 1) (Parents.reading_prefix (List.prefix_append _ _) j (Parents.point visible p)
      (scope.view.bounded p bound))

theorem ShiftView.append {d : Nat} {source target : ParentContext} {visible history : List Nat}
    {root cap : Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d source target visible history root cap delta phase) (a : List Nat)
    (width : a.length = d) (unit : Parents.UnitSteps d (source ++ [Parents.label d source a])) :
    let threshold := Keys.threshold cap root history (Parents.label d source a)
    let shifted := shift a threshold delta phase
    ShiftView d (source ++ [Parents.label d source a]) (target ++ [Parents.label d target shifted])
      (visible ++ [target.length]) (history ++ [threshold]) root cap delta phase := by
  dsimp only
  refine ⟨Parents.coherent_append_label scope.sourceCoherent a,
    Parents.context_valid_append_label d source scope.sourceValid a,
    Parents.coherent_append_label scope.targetCoherent _,
    Parents.context_valid_append_label d target scope.targetValid _, scope.head_unitSteps a width unit,
    scope.view.append _ _ (Parents.context_valid_append_label d source scope.sourceValid a)
      (scope.head_parents a width unit), by simp [scope.historyLength],
    Keys.history_append_threshold scope.sourceCoherent scope.sourceValid scope.historyCorrect
      scope.historyLength scope.afterRoot scope.capBound a,
    by have bound := scope.afterRoot; simp only [List.length_append, List.length_cons, List.length_nil]; omega,
    scope.capBound, ?_⟩
  intro p inside j room
  by_cases old : p < source.length
  · rw [Parents.point_append_old visible p target.length (by rw [scope.view.length]; exact old),
      List.getElem?_append_left (by rw [scope.historyLength]; exact old),
      ← Parents.reading_prefix (List.prefix_append source [Parents.label d source a]) j p old,
      ← Parents.reading_prefix (List.prefix_append target _) j (Parents.point visible p) (scope.view.bounded p old)]
    exact scope.values p old j room
  · have same : p = source.length := by simp only [List.length_append, List.length_cons, List.length_nil] at inside; omega
    subst p
    rw [← scope.view.length, Parents.point_append_last, scope.view.length,
      ← scope.historyLength, List.getElem?_concat_length, Option.getD_some, scope.historyLength,
      Parents.reading_append_label, Parents.reading_append_label, shift_value _ _ _ _ j (by omega)]

end BTnSSBMS.Source
