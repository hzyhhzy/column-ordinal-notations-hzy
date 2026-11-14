import BTnSSBMS.CrossEntryKeyTransport
import BTnSSBMS.CopyDonation

/-! Connect cross-entry key comparison back to the literal frozen
activation-and-shift operation, with the earlier entry constructed by
restricting the actual ongoing copy state. -/
namespace BTnSSBMS.BMS

theorem HistoryCorrect.take_context {context : ParentContext} {root cap : Nat} {history : List Nat}
    (correct : HistoryCorrect context root cap history) (valid : Parents.ContextValid context)
    (length : history.length = context.length) (count : Nat) :
    HistoryCorrect (context.take count) root cap (history.take count) := by
  intro i inside j
  have before : i < count := by simp only [List.length_take] at inside; omega
  have old : i < history.length := by simp only [List.length_take] at inside; omega
  rw [List.getElem?_take_of_lt before, correct i old j]
  constructor
  · rintro ⟨room, path⟩
    exact ⟨room, path.restrict (List.take_prefix ..) valid (by simp only [List.length_take]; omega)⟩
  · rintro ⟨room, path⟩
    exact ⟨room, path.prefix (List.take_prefix ..)⟩

end BTnSSBMS.BMS

namespace BTnSSBMS.Source

theorem ShiftView.prefix_at {d : Nat} {source target : ParentContext} {visible history : List Nat}
    {root cap : Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d source target visible history root cap delta phase)
    (endpoint : Nat) (inside : endpoint < source.length) (afterRoot : root ≤ endpoint) :
    ShiftView d (source.take (endpoint + 1)) (target.take (Parents.point visible endpoint + 1))
      (visible.take (endpoint + 1)) (history.take (endpoint + 1)) root cap delta phase := by
  have sourceLength : (source.take (endpoint + 1)).length = endpoint + 1 := by simp only [List.length_take]; omega
  have lastBound := scope.view.bounded endpoint inside
  have targetLength : (target.take (Parents.point visible endpoint + 1)).length = Parents.point visible endpoint + 1 := by
    simp only [List.length_take]; omega
  refine ⟨scope.sourceCoherent.restrict (List.take_prefix ..), scope.sourceValid.restrict (List.take_prefix ..),
    scope.targetCoherent.restrict (List.take_prefix ..), scope.targetValid.restrict (List.take_prefix ..),
    scope.targetUnit.restrict scope.targetValid (List.take_prefix ..), scope.view.prefix_at scope.targetValid endpoint inside,
    by simp only [List.length_take, scope.historyLength],
    scope.historyCorrect.take_context scope.sourceValid scope.historyLength (endpoint + 1),
    by omega, scope.capBound, ?_⟩
  intro p pBound j room
  have old : p < source.length := by omega
  have smaller := (scope.view.point_le_iff old inside).mpr (by omega : p ≤ endpoint)
  rw [Parents.point_take visible (endpoint + 1) p (by omega), List.getElem?_take_of_lt (by omega : p < endpoint + 1),
    Parents.reading_prefix (List.take_prefix (Parents.point visible endpoint + 1) target) j (Parents.point visible p)
      (by rw [targetLength]; omega),
    Parents.reading_prefix (List.take_prefix (endpoint + 1) source) j p pBound]
  exact scope.values p old j room

/-- Same-copy, cross-entry comparison of complete actual attachment keys.
The two attachment entries are different; their restricted copy states
are derived rather than supplied as an additional transport hypothesis.
This statement excludes a list replaced by a hole or by a donated list. -/
theorem copied_ancestor_key_compare {d : Nat} {source target : ParentContext} {visible history : List Nat}
    {copyRoot cap : Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d source target visible history copyRoot cap delta phase)
    (sourceUnit : Parents.UnitSteps d source) (positive : 0 < d)
    {ancestor : Nat} (afterRoot : copyRoot ≤ ancestor) (before : ancestor < source.length - 1)
    (path : Parents.Ancestor source (d - 1) ancestor (source.length - 1))
    (ancestorWidth : (source[ancestor]?.getD default).coordinates.length = d)
    (lastWidth : (source[source.length - 1]?.getD default).coordinates.length = d)
    (targetAncestorWidth : (target[Parents.point visible ancestor]?.getD default).coordinates.length = d)
    (targetLastWidth : (target[target.length - 1]?.getD default).coordinates.length = d)
    (hs ks : Forests (List Nat))
    (oldLegal : FiniteLegalForests d (source.take (ancestor + 1)) (Parents.reading source 0 ancestor) hs)
    (currentLegal : FiniteLegalForests d source (Parents.reading source 0 (source.length - 1)) ks) :
    Keys.compare
      (Keys.atContext d target (Parents.point visible ancestor)
        (copiedForests d copyRoot cap delta phase (source.take (ancestor + 1)) (history.take (ancestor + 1)) hs))
      (Keys.atContext d target (target.length - 1) (copiedForests d copyRoot cap delta phase source history ks)) =
      Keys.compare (Keys.atContext d source ancestor hs) (Keys.atContext d source (source.length - 1) ks) := by
  have restricted := scope.prefix_at ancestor (by omega) afterRoot
  have result := relocated_ancestor_key_compare scope.sourceCoherent scope.sourceValid sourceUnit
    scope.targetCoherent scope.targetValid scope.targetUnit scope.view positive before path
    ancestorWidth lastWidth targetAncestorWidth targetLastWidth hs ks oldLegal currentLegal
  rw [relocateForests_eq_copied restricted (Parents.reading source 0 ancestor) hs oldLegal,
    relocateForests_eq_copied scope (Parents.reading source 0 (source.length - 1)) ks currentLegal] at result
  exact result

theorem copiedForests_zero (d root cap : Nat) (delta : List Nat) (source : ParentContext)
    (history : List Nat) (hs : Forests (List Nat)) :
    copiedForests d root cap delta 0 source history hs = hs := by
  rw [copiedForests_eq_ascend d root cap delta 0 source history hs .nil,
    ascendForests_nohole_zero, markForests_erase, Parents.annotateForests_erase]

theorem relocateForests_same_context {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (unit : Parents.UnitSteps d context) (nonempty : 0 < context.length)
    (owner : Nat) (hs : Forests (List Nat)) (legal : FiniteLegalForests d context owner hs) :
    relocateForests d context context (List.range context.length) hs = hs := by
  have scope := ShiftView.zero coherent valid unit 0 0 [] nonempty (by omega)
  rw [relocateForests_eq_copied scope owner hs legal, copiedForests_zero]

/-- The other source of an old binding: its prefix and positions were
not copied at all. Its attachment stays literally unchanged while the
current one undergoes the actual copy. The finite fixed-prefix conditions
are explicit; no equality of the two endpoint keys is assumed. -/
theorem copied_external_ancestor_key_compare {d : Nat} {source target : ParentContext}
    {visible history : List Nat} {copyRoot cap : Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d source target visible history copyRoot cap delta phase)
    (sourceUnit : Parents.UnitSteps d source) (positive : 0 < d)
    {ancestor : Nat} (before : ancestor < source.length - 1)
    (path : Parents.Ancestor source (d - 1) ancestor (source.length - 1))
    (unchangedPrefix : target.take (ancestor + 1) = source.take (ancestor + 1))
    (unchangedPositions : visible.take (ancestor + 1) = List.range (ancestor + 1))
    (ancestorWidth : (source[ancestor]?.getD default).coordinates.length = d)
    (lastWidth : (source[source.length - 1]?.getD default).coordinates.length = d)
    (targetLastWidth : (target[target.length - 1]?.getD default).coordinates.length = d)
    (hs ks : Forests (List Nat))
    (oldLegal : FiniteLegalForests d (source.take (ancestor + 1)) (Parents.reading source 0 ancestor) hs)
    (currentLegal : FiniteLegalForests d source (Parents.reading source 0 (source.length - 1)) ks) :
    Keys.compare (Keys.atContext d source ancestor hs)
      (Keys.atContext d target (target.length - 1) (copiedForests d copyRoot cap delta phase source history ks)) =
      Keys.compare (Keys.atContext d source ancestor hs) (Keys.atContext d source (source.length - 1) ks) := by
  have point : Parents.point visible ancestor = ancestor := by
    rw [← Parents.point_take visible (ancestor + 1) ancestor (by omega), unchangedPositions,
      Parents.point_range (ancestor + 1) ancestor (by omega)]
  have label : target[ancestor]?.getD default = source[ancestor]?.getD default := by
    have lookup := congrArg (fun context : ParentContext => context[ancestor]?.getD default) unchangedPrefix
    simpa only [List.getElem?_take_of_lt (by omega : ancestor < ancestor + 1)] using lookup
  have sameKey : Keys.atContext d target ancestor hs = Keys.atContext d source ancestor hs := by
    simp only [Keys.atContext, label, unchangedPrefix]
  have result := relocated_ancestor_key_compare scope.sourceCoherent scope.sourceValid sourceUnit
    scope.targetCoherent scope.targetValid scope.targetUnit scope.view positive before path
    ancestorWidth lastWidth (by rw [point, label]; exact ancestorWidth) targetLastWidth hs ks oldLegal currentLegal
  have length : (source.take (ancestor + 1)).length = ancestor + 1 := by simp only [List.length_take]; omega
  have identity := relocateForests_same_context (scope.sourceCoherent.restrict (List.take_prefix ..))
    (scope.sourceValid.restrict (List.take_prefix ..)) (sourceUnit.restrict scope.sourceValid (List.take_prefix ..))
    (by omega) (Parents.reading source 0 ancestor) hs oldLegal
  rw [length] at identity
  rw [point, unchangedPrefix, unchangedPositions, identity, sameKey,
    relocateForests_eq_copied scope (Parents.reading source 0 (source.length - 1)) ks currentLegal] at result
  exact result

end BTnSSBMS.Source
