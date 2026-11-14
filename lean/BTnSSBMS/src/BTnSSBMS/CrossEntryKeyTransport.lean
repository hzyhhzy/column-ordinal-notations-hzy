import BTnSSBMS.TransplantNaturality

/-!
Cross-entry comparison of an ancestor attachment and a current attachment.
The comparison is reduced to one common entry by actual transplantation;
the numerical-transport commuting square then preserves that comparison.
-/
namespace BTnSSBMS.Keys

def atContext (d : Nat) (context : ParentContext) (position : Nat) (hs : Forests (List Nat)) : Key :=
  ofColumn d position (context[position]?.getD default)
    (Parents.annotateForests d (context.take (position + 1)) hs)

end BTnSSBMS.Keys

namespace BTnSSBMS.Source

private theorem context_label_at {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) {position : Nat} (inside : position < context.length) :
    Parents.label d (context.take position) (context[position]?.getD default).coordinates =
      context[position]?.getD default := by
  rw [List.getElem?_eq_getElem inside, Option.getD_some]
  have parents := coherent position context[position] (List.getElem?_eq_getElem inside)
  cases value : context[position] with
  | mk coordinates stored =>
    simp only [value, Parents.label] at parents ⊢
    rw [parents]

/-- Both endpoint keys are computed in their own actual prefixes. The
right-hand comparison is of two whole lists in the final common entry. -/
theorem ancestor_key_compare_atContext {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (unit : Parents.UnitSteps d context) (positive : 0 < d)
    {root : Nat} (before : root < context.length - 1)
    (path : Parents.Ancestor context (d - 1) root (context.length - 1))
    (rootWidth : (context[root]?.getD default).coordinates.length = d)
    (lastWidth : (context[context.length - 1]?.getD default).coordinates.length = d)
    (hs ks : Forests (List Nat))
    (oldLegal : FiniteLegalForests d (context.take (root + 1)) (Parents.reading context 0 root) hs)
    (currentLegal : FiniteLegalForests d context (Parents.reading context 0 (context.length - 1)) ks) :
    Keys.compare (Keys.atContext d context root hs) (Keys.atContext d context (context.length - 1) ks) =
      (relocateForests d (context.take (root + 1)) context (List.range root ++ [context.length - 1]) hs).compare
        (listCompare Ord.compare) ks := by
  let entry := context.take (context.length - 1)
  let position := (context[context.length - 1]?.getD default).coordinates
  have lastInside : context.length - 1 < context.length := by omega
  have lastSuccessor : context.length - 1 + 1 = context.length := by omega
  have entryLength : entry.length = context.length - 1 := by
    simp only [entry, List.length_take]; omega
  have lastLabel := context_label_at coherent lastInside
  have divided : context = entry ++ [Parents.label d entry position] := by
    have result := coherent.take_succ_label lastInside
    rw [lastSuccessor, List.take_length] at result
    exact result
  have oldPrefix : entry.take (root + 1) = context.take (root + 1) := by
    simp only [entry, List.take_take, Nat.min_eq_left (by omega : root + 1 ≤ context.length - 1)]
  have oldRoot : entry[root]?.getD default = context[root]?.getD default := by
    simp only [entry, List.getElem?_take_of_lt before]
  have rootReading : Parents.reading entry 0 root = Parents.reading context 0 root :=
    Parents.reading_prefix (List.take_prefix ..) 0 root (by change root < entry.length; omega)
  have newUnit : Parents.UnitSteps d (entry ++ [Parents.label d entry position]) := divided ▸ unit
  have newPath : Parents.Ancestor (entry ++ [Parents.label d entry position]) (d - 1) root entry.length := by
    rw [← divided, entryLength]
    exact path
  have old := oldLegal
  rw [← oldPrefix, ← rootReading] at old
  have current : FiniteLegalForests d (entry ++ [Parents.label d entry position]) (position[0]?.getD 0) ks := by
    rw [← divided]
    exact currentLegal
  have compared := transplanted_key_compare
    (coherent.restrict (List.take_prefix ..)) (valid.restrict (List.take_prefix ..)) positive position lastWidth
    newUnit (by change root < entry.length; omega) newPath (by rw [oldRoot]; exact rootWidth) hs ks old current
  rw [transplantedForests_eq_relocate (coherent.restrict (List.take_prefix ..))
    (valid.restrict (List.take_prefix ..)) positive position newUnit
    (by change root < entry.length; omega) newPath hs old] at compared
  rw [oldRoot, oldPrefix, entryLength, ← divided] at compared
  change Keys.compare (Keys.atContext d context root hs)
    (Keys.ofColumn d (context.length - 1) (Parents.label d entry position)
      (Parents.annotateForests d context ks)) = _ at compared
  rw [lastLabel] at compared
  simpa only [Keys.atContext, lastSuccessor, List.take_length] using compared

private theorem relocateForests_last_legal {d : Nat} {source target : ParentContext} {visible : List Nat}
    (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (targetUnit : Parents.UnitSteps d target) (view : Parents.NumericalView d source target visible)
    (positive : 0 < d) (nonempty : 0 < source.length) (hs : Forests (List Nat))
    (legal : FiniteLegalForests d source (Parents.reading source 0 (source.length - 1)) hs) :
    FiniteLegalForests d target (Parents.reading target 0 (target.length - 1))
      (relocateForests d source target visible hs) := by
  have result := relocateForests_finiteLegal d hs source target visible sourceCoherent sourceValid
    targetCoherent targetValid targetUnit view positive (source.length - 1) (by omega) (.refl _) legal
  have frontier := view.frontier (by intro empty; simp only [empty, List.length_nil] at nonempty; omega)
  have point : Parents.point visible (source.length - 1) = target.length - 1 := by omega
  rw [point] at result
  exact result

/-- A complete cross-entry key comparison is invariant under numerical
relocation along one actual increasing ancestry view. The earlier key is
read in its own prefix and the current key in the full prefix. Their
attachments may be arbitrary finite-legal forests of unbounded depth.
This is not yet a trace theorem identifying all saved encoder bindings. -/
theorem relocated_ancestor_key_compare {d : Nat} {source target : ParentContext} {visible : List Nat}
    (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
    (sourceUnit : Parents.UnitSteps d source)
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (targetUnit : Parents.UnitSteps d target) (view : Parents.NumericalView d source target visible)
    (positive : 0 < d) {root : Nat} (before : root < source.length - 1)
    (path : Parents.Ancestor source (d - 1) root (source.length - 1))
    (rootWidth : (source[root]?.getD default).coordinates.length = d)
    (lastWidth : (source[source.length - 1]?.getD default).coordinates.length = d)
    (targetRootWidth : (target[Parents.point visible root]?.getD default).coordinates.length = d)
    (targetLastWidth : (target[target.length - 1]?.getD default).coordinates.length = d)
    (hs ks : Forests (List Nat))
    (oldLegal : FiniteLegalForests d (source.take (root + 1)) (Parents.reading source 0 root) hs)
    (currentLegal : FiniteLegalForests d source (Parents.reading source 0 (source.length - 1)) ks) :
    Keys.compare
      (Keys.atContext d target (Parents.point visible root)
        (relocateForests d (source.take (root + 1)) (target.take (Parents.point visible root + 1))
          (visible.take (root + 1)) hs))
      (Keys.atContext d target (target.length - 1) (relocateForests d source target visible ks)) =
      Keys.compare (Keys.atContext d source root hs) (Keys.atContext d source (source.length - 1) ks) := by
  have insideRoot : root < source.length := by omega
  have lastInside : source.length - 1 < source.length := by omega
  have sourceLength : (source.take (root + 1)).length = root + 1 := by simp only [List.length_take]; omega
  have targetRootBound := view.bounded root insideRoot
  have targetLength : (target.take (Parents.point visible root + 1)).length = Parents.point visible root + 1 := by
    simp only [List.length_take]; omega
  have frontier := view.frontier (by intro empty; simp only [empty, List.length_nil] at insideRoot; omega)
  have final : Parents.point visible (source.length - 1) = target.length - 1 := by omega
  have targetBefore := view.increasing root (source.length - 1) before lastInside
  rw [final] at targetBefore
  have targetPath := view.lift (d - 1) (by omega) root (source.length - 1) insideRoot lastInside path
  rw [final] at targetPath
  have restricted := view.prefix_at targetValid root insideRoot
  have prefixLegal : FiniteLegalForests d (source.take (root + 1))
      (Parents.reading (source.take (root + 1)) 0 ((source.take (root + 1)).length - 1)) hs := by
    rw [sourceLength, Nat.add_sub_cancel,
      Parents.reading_prefix (List.take_prefix (root + 1) source) 0 root (by omega)]
    exact oldLegal
  have targetOld := relocateForests_last_legal (sourceCoherent.restrict (List.take_prefix ..))
    (sourceValid.restrict (List.take_prefix ..)) (targetCoherent.restrict (List.take_prefix ..))
    (targetValid.restrict (List.take_prefix ..)) (targetUnit.restrict targetValid (List.take_prefix ..))
    restricted positive (by omega) hs prefixLegal
  rw [targetLength, Nat.add_sub_cancel,
    Parents.reading_prefix (List.take_prefix (Parents.point visible root + 1) target) 0
      (Parents.point visible root) (by omega)] at targetOld
  have targetCurrent := relocateForests_last_legal sourceCoherent sourceValid targetCoherent targetValid targetUnit
    view positive (by omega) ks currentLegal
  have targetCompare := ancestor_key_compare_atContext targetCoherent targetValid targetUnit positive targetBefore
    targetPath targetRootWidth targetLastWidth _ _ targetOld targetCurrent
  have sourceCompare := ancestor_key_compare_atContext sourceCoherent sourceValid sourceUnit positive before path
    rootWidth lastWidth hs ks oldLegal currentLegal
  have rootView := Parents.ancestor_to_last_view sourceCoherent sourceValid positive before path
  have commonLegal := relocateForests_last_legal (sourceCoherent.restrict (List.take_prefix ..))
    (sourceValid.restrict (List.take_prefix ..)) sourceCoherent sourceValid sourceUnit rootView positive
    (by omega) hs prefixLegal
  have commonCompare := relocateForests_compare d _ ks source target visible sourceCoherent sourceValid
    targetCoherent targetValid view (Parents.reading source 0 (source.length - 1)) commonLegal currentLegal
  rw [targetCompare, ← relocateForests_transplant_naturality sourceCoherent sourceValid targetCoherent targetValid
    view positive before path hs, commonCompare, ← sourceCompare]

end BTnSSBMS.Source
