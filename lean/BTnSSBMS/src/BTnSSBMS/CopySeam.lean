import BTnSSBMS.CopyEntry

/-!
The numerical seam between successive ordinary replicas. The next root
is computed with the original delta and the next phase; its parent paths
and the reset scoped view are derived from the actual previous replica.
-/
namespace BTnSSBMS.BMS

theorem HistoryCorrect.before {context : ParentContext} {root cap : Nat} {history : List Nat}
    (correct : HistoryCorrect context root cap history) (valid : Parents.ContextValid context)
    {i : Nat} (inside : i < history.length) (before : i < root) : history[i]?.getD 0 = 0 := by
  by_cases equal : history[i]?.getD 0 = 0
  · exact equal
  have active : 0 < history[i]?.getD 0 := by omega
  have path := ((correct i inside 0).mp active).2
  have earlier := path.le valid
  omega

theorem HistoryCorrect.root {context : ParentContext} {root cap : Nat} {history : List Nat}
    (correct : HistoryCorrect context root cap history) (inside : root < history.length) :
    history[root]?.getD 0 = cap := by
  apply Nat.le_antisymm
  · by_cases done : history[root]?.getD 0 ≤ cap
    · exact done
    have active : cap < history[root]?.getD 0 := by omega
    have impossible := ((correct root inside cap).mp active).1
    omega
  · by_cases done : cap ≤ history[root]?.getD 0
    · exact done
    have active : history[root]?.getD 0 < cap := by omega
    have impossible := (correct root inside (history[root]?.getD 0)).mpr ⟨active, .refl _⟩
    omega

end BTnSSBMS.BMS

namespace BTnSSBMS.Keys

theorem threshold_at_selected_root {d : Nat} {source : ParentContext} {history : List Nat}
    {root cap : Nat} (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (correct : BMS.HistoryCorrect source root cap history) (length : history.length = source.length)
    (afterRoot : root < source.length) (room : cap < d) (a : List Nat)
    (selected : (Parents.label d source a).parents[cap]?.join = some root) :
    threshold cap root history (Parents.label d source a) = cap := by
  have path : Parents.Ancestor (source ++ [Parents.label d source a]) cap root source.length :=
    .up (by rw [Parents.append_label_parent]; exact selected) (.refl _)
  have correctAt := threshold_at_label coherent valid correct length afterRoot (by omega : cap ≤ d) a
  apply Nat.le_antisymm
  · by_cases done : threshold cap root history (Parents.label d source a) ≤ cap
    · exact done
    have active : cap < threshold cap root history (Parents.label d source a) := by omega
    have impossible := ((correctAt cap).mp active).1
    omega
  · by_cases done : cap ≤ threshold cap root history (Parents.label d source a)
    · exact done
    have below : threshold cap root history (Parents.label d source a) < cap := by omega
    have lower := path.lower_row (Parents.coherent_append_label coherent a) room (Nat.le_of_lt below)
    have impossible := (correctAt _).mpr ⟨below, lower⟩
    omega

end BTnSSBMS.Keys

namespace BTnSSBMS.Parents

theorem point_take (visible : List Nat) (count p : Nat) (inside : p < count) :
    point (visible.take count) p = point visible p := by
  simp only [point, List.getElem?_take_of_lt inside]

/-- Reset the visible source to its root prefix while placing that root
at the new target frontier. All earlier positions retain their identity. -/
theorem NumericalView.reset_root {d : Nat} {source target next : ParentContext} {visible : List Nat}
    (view : NumericalView d source target visible) (valid : ContextValid source)
    {root position : Nat} (rootBound : root < source.length) (extended : target <+: next)
    (positionBound : position < next.length) (frontier : position + 1 = next.length)
    (paths : ∀ j, j < d → ∀ p, p < root → Ancestor source j p root →
      Ancestor next j (point visible p) position) :
    NumericalView d (source.take (root + 1)) next (visible.take root ++ [position]) := by
  have sourceLength : (source.take (root + 1)).length = root + 1 := by simp only [List.length_take]; omega
  have visibleLength : (visible.take root).length = root := by simp only [List.length_take, view.length]; omega
  have oldPoint : ∀ p, p < root → point (visible.take root ++ [position]) p = point visible p := by
    intro p before
    rw [point_append_old _ p position (by omega), point_take visible root p before]
  have rootPoint : point (visible.take root ++ [position]) root = position := by
    simpa only [visibleLength] using point_append_last (visible.take root) position
  refine ⟨by simp only [List.length_append, List.length_cons, List.length_nil, visibleLength, sourceLength], ?_, ?_, ?_, ?_⟩
  · intro p inside
    by_cases before : p < root
    · rw [oldPoint p before]
      have previous := view.bounded p (by omega)
      have longer := extended.length_le
      omega
    · have same : p = root := by omega
      subst p
      rw [rootPoint]
      exact positionBound
  · intro j room p q pBound qBound path
    have pBefore := path.le (valid.restrict (List.take_prefix ..))
    have oldPath := path.prefix (List.take_prefix (root + 1) source)
    by_cases before : q < root
    · rw [oldPoint p (by omega), oldPoint q before]
      exact (view.lift j room p q (by omega) (by omega) oldPath).prefix extended
    · have same : q = root := by omega
      subst q
      by_cases sameRoot : p = root
      · subst p
        exact .refl _
      · have earlier : p < root := by omega
        rw [oldPoint p earlier, rootPoint]
        exact paths j room p earlier oldPath
  · intro _
    rw [sourceLength, Nat.add_sub_cancel, rootPoint]
    exact frontier
  · intro p q earlier inside
    have pBefore : p < root := by omega
    rw [oldPoint p pBefore]
    by_cases qBefore : q < root
    · rw [oldPoint q qBefore]
      exact view.increasing p q earlier (by omega)
    · have same : q = root := by omega
      subst q
      rw [rootPoint]
      have below := view.increasing p root pBefore rootBound
      have bounded := view.bounded root rootBound
      have longer := extended.length_le
      omega

end BTnSSBMS.Parents

namespace BTnSSBMS.Source

/-- At a later-copy seam, the next phase's shifted root satisfies exactly
the low/high coordinate equations required by the real first-head search. -/
theorem ShiftView.next_head_values {d : Nat} {source target : ParentContext}
    {visible history : List Nat} {root cap : Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d source target visible history root cap delta phase)
    (terminal : List Nat) (width : terminal.length = d) (rootWidth : (source[root]?.getD default).coordinates.length = d)
    (room : cap < d)
    (difference : ∀ j, j < cap → terminal[j]?.getD 0 = Parents.reading source j root + delta[j]?.getD 0) :
    let rootCoordinates := (source[root]?.getD default).coordinates
    let currentTerminal := shift terminal cap delta phase
    let nextHead := shift rootCoordinates cap delta (phase + 1)
    (∀ j, j < cap → nextHead[j]?.getD 0 = currentTerminal[j]?.getD 0) ∧
    (∀ j, cap ≤ j → j < d → nextHead[j]?.getD 0 = Parents.reading target j (Parents.point visible root)) := by
  dsimp only
  have atRoot := scope.historyCorrect.root (by rw [scope.historyLength]; exact scope.afterRoot)
  constructor
  · intro j below
    rw [shift_value _ _ _ _ j (by omega), shift_value _ _ _ _ j (by omega), if_pos below,
      difference j below, Nat.mul_succ]
    simp only [if_pos below]
    change Parents.reading source j root + (delta[j]?.getD 0 * phase + delta[j]?.getD 0) = _
    omega
  · intro j above inside
    rw [shift_value _ _ _ _ j (by omega), if_neg (by omega), Nat.add_zero,
      scope.values root scope.afterRoot j inside, atRoot, if_neg (by omega), Nat.add_zero]
    rfl

/-- Complete repeated-copy numerical entry: the incoming copied body
constructs the reset view for phase+1, rather than assuming that next view. -/
theorem ShiftView.restart {d : Nat} {source target : ParentContext}
    {visible history : List Nat} {root cap : Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d source target visible history root cap delta phase)
    (terminal : List Nat) (width : terminal.length = d)
    (terminalUnit : Parents.UnitSteps d (source ++ [Parents.label d source terminal]))
    (rootWidth : (source[root]?.getD default).coordinates.length = d)
    (room : cap < d) (selected : (Parents.label d source terminal).parents[cap]?.join = some root)
    (difference : ∀ j, j < cap → terminal[j]?.getD 0 = Parents.reading source j root + delta[j]?.getD 0) :
    let rootCoordinates := (source[root]?.getD default).coordinates
    let nextHead := shift rootCoordinates cap delta (phase + 1)
    ShiftView d (source.take (root + 1)) (target ++ [Parents.label d target nextHead])
      (visible.take root ++ [target.length]) (List.replicate root 0 ++ [cap]) root cap delta (phase + 1) := by
  dsimp only
  let currentTerminal := shift terminal cap delta phase
  let nextHead := shift (source[root]?.getD default).coordinates cap delta (phase + 1)
  have threshold := Keys.threshold_at_selected_root scope.sourceCoherent scope.sourceValid
    scope.historyCorrect scope.historyLength scope.afterRoot room terminal selected
  have targetSelected : (Parents.label d target currentTerminal).parents[cap]?.join =
      some (Parents.point visible root) := by
    have result := scope.head_parents terminal width terminalUnit cap room
    rw [threshold, selected, Option.map_some] at result
    exact result
  have targetTerminalUnit : Parents.UnitSteps d (target ++ [Parents.label d target currentTerminal]) := by
    have result := scope.head_unitSteps terminal width terminalUnit
    rw [threshold] at result
    exact result
  have values := scope.next_head_values terminal width rootWidth room difference
  have targetTable := Parents.first_copy_head_parents scope.targetCoherent scope.targetValid currentTerminal nextHead
    room targetSelected values.1 values.2
  have targetUnit := Parents.first_copy_head_unitSteps scope.targetCoherent scope.targetValid scope.targetUnit
    currentTerminal nextHead targetTerminalUnit room targetSelected values.1 values.2
  have targetPrefix := List.prefix_append target [Parents.label d target nextHead]
  have sourceLength : (source.take (root + 1)).length = root + 1 := by
    simp only [List.length_take]; have bound := scope.afterRoot; omega
  have visibleLength : (visible.take root).length = root := by
    simp only [List.length_take, scope.view.length]; have bound := scope.afterRoot; omega
  have oldHistory : ∀ p, p < root → history[p]?.getD 0 = 0 := by
    intro p before
    exact scope.historyCorrect.before scope.sourceValid (by rw [scope.historyLength]; have bound := scope.afterRoot; omega) before
  have nextView : Parents.NumericalView d (source.take (root + 1))
      (target ++ [Parents.label d target nextHead]) (visible.take root ++ [target.length]) := by
    apply scope.view.reset_root scope.sourceValid scope.afterRoot targetPrefix (position := target.length) (by simp) (by simp)
    intro j inside p before path
    have pBound : p < source.length := by have bound := scope.afterRoot; omega
    have transported := scope.view.lift j inside p root pBound scope.afterRoot path
    have strict := path.reading_lt scope.sourceCoherent (by omega)
    have oldValues := scope.values p pBound j inside
    rw [oldHistory p before, if_neg (by omega), Nat.add_zero] at oldValues
    have rootValues := scope.values root scope.afterRoot j inside
    have different : Parents.point visible p ≠ Parents.point visible root := by
      intro equal
      rw [equal] at oldValues
      omega
    by_cases below : j < cap
    · have rootPath : Parents.Ancestor (target ++ [Parents.label d target currentTerminal]) cap
          (Parents.point visible root) target.length :=
        .up (by rw [Parents.append_label_parent]; exact targetSelected) (.refl _)
      have lowPath := rootPath.lower_row (Parents.coherent_append_label scope.targetCoherent currentTerminal)
        room (by omega : j ≤ cap)
      have full := (transported.prefix (List.prefix_append target [Parents.label d target currentTerminal])).trans lowPath
      exact full.replace_last scope.targetValid currentTerminal nextHead (scope.view.bounded p pBound)
        (by simpa only [below, if_true] using (targetTable j inside).symm)
    · obtain ⟨q, edge, previous⟩ := (Parents.Ancestor.iff_parent different).mp transported
      apply Parents.Ancestor.up ?_ (previous.prefix targetPrefix)
      rw [Parents.append_label_parent, targetTable j inside, if_neg below, edge]
  refine ⟨scope.sourceCoherent.restrict (List.take_prefix ..), scope.sourceValid.restrict (List.take_prefix ..),
    Parents.coherent_append_label scope.targetCoherent _, Parents.context_valid_append_label d target scope.targetValid _,
    targetUnit, nextView, by simp [sourceLength],
    BMS.HistoryCorrect.at_root (scope.sourceValid.restrict (List.take_prefix ..)) root cap,
    by omega, scope.capBound, ?_⟩
  intro p inside j row
  by_cases before : p < root
  · rw [Parents.point_append_old _ p target.length (by omega), Parents.point_take visible root p before,
      List.getElem?_append_left (show p < (List.replicate root 0).length by simpa using before),
      List.getElem?_replicate_of_lt before, Option.getD_some, if_neg (by omega), Nat.add_zero,
      ← Parents.reading_prefix targetPrefix j (Parents.point visible p) (scope.view.bounded p (by have bound := scope.afterRoot; omega)),
      scope.values p (by have bound := scope.afterRoot; omega) j row, oldHistory p before,
      if_neg (by omega), Nat.add_zero,
      Parents.reading_prefix (List.take_prefix (root + 1) source) j p inside]
    rfl
  · have same : p = root := by omega
    subst p
    have rootPoint : Parents.point (visible.take root ++ [target.length]) root = target.length := by
      simpa only [visibleLength] using Parents.point_append_last (visible.take root) target.length
    have marked : (List.replicate root 0 ++ [cap])[root]? = some cap := by
      simpa only [List.length_replicate] using
        (List.getElem?_concat_length (l := List.replicate root 0) (a := cap))
    rw [rootPoint, marked, Option.getD_some, Parents.reading_append_label,
      Parents.reading_prefix (List.take_prefix (root + 1) source) j root inside]
    exact shift_value _ _ _ _ j (by omega)

end BTnSSBMS.Source
