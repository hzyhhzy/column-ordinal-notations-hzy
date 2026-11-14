import BTnSSBMS.PartialRebaseComparison

/-!
Transplant a complete finite attachment from a highest-row ancestor to
the current column. The new numerical entry is constructed from the real
ancestor path. All forests are reannotated, and their complete relative key
is preserved. No standardness of the transplanted expression is asserted.
This supplies the common-entry reduction needed for cross-entry key comparison;
commutation with a second, independently rooted rebase is a further step.
-/
namespace BTnSSBMS.Parents

theorem transplant_numericalView {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context) (positive : 0 < d)
    (position : List Nat) {root : Nat} (insideRoot : root < context.length)
    (path : Ancestor (context ++ [label d context position]) (d - 1) root context.length) :
    NumericalView d (context.take (root + 1)) (context ++ [label d context position])
      (List.range root ++ [context.length]) := by
  have length : (context.take root).length = root := by simp only [List.length_take]; omega
  have divided := List.take_succ_eq_append_getElem insideRoot
  have view := numericalView_identity d (context.take root)
  rw [length] at view
  rw [divided]
  apply view.append_stretched context[root]
    (by rw [← divided]; exact valid.restrict (List.take_prefix ..))
    ((List.take_prefix root context).trans (List.prefix_append context [label d context position]))
    context.length (by simp) (by simp) (by simp only [length]; omega)
  intro j room p edge
  have actual : parent context j root = some p := by
    simpa only [parent, List.getElem?_eq_getElem insideRoot, Option.bind_some] using edge
  have earlier := parent_earlier valid actual
  rw [point_range root p earlier]
  have toRoot : Ancestor (context ++ [label d context position]) j p root :=
    (Ancestor.up actual (.refl _)).prefix (List.prefix_append context [label d context position])
  exact toRoot.trans (path.lower_row (coherent_append_label coherent position)
    (by omega : d - 1 < d) (by omega : j ≤ d - 1))

end BTnSSBMS.Parents

namespace BTnSSBMS.Source

def transplantDelta (d : Nat) (context : ParentContext) (root : Nat) (position : List Nat) : List Nat :=
  (List.range d).map (fun j => position[j]?.getD 0 - Parents.reading context j root)

/-- The explicit transplant, using only the frozen finite annotation,
activation and shift operations. This does not change any FS rule. -/
def transplantedForests (d : Nat) (context : ParentContext) (root : Nat)
    (position : List Nat) (hs : Forests (List Nat)) : Forests (List Nat) :=
  copiedForests d root d (transplantDelta d context root position) 1
    (context.take (root + 1)) (List.replicate root 0 ++ [d]) hs

theorem transplant_delta_values {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (positive : 0 < d)
    (position : List Nat) {root : Nat} (insideRoot : root < context.length)
    (path : Parents.Ancestor (context ++ [Parents.label d context position]) (d - 1) root context.length)
    (j : Nat) (room : j < d) :
    Parents.reading context j root + (transplantDelta d context root position)[j]?.getD 0 =
      position[j]?.getD 0 := by
  have lower := path.lower_row (Parents.coherent_append_label coherent position)
    (by omega : d - 1 < d) (by omega : j ≤ d - 1)
  have strict := lower.reading_lt (Parents.coherent_append_label coherent position)
    (by omega : root ≠ context.length)
  rw [Parents.reading_append_label,
    ← Parents.reading_prefix (List.prefix_append context _) j root insideRoot] at strict
  simp only [transplantDelta, List.getElem?_map, List.getElem?_range room,
    Option.map_some, Option.getD_some]
  omega

theorem transplant_head {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (positive : 0 < d)
    (position : List Nat) (positionWidth : position.length = d)
    {root : Nat} (insideRoot : root < context.length)
    (path : Parents.Ancestor (context ++ [Parents.label d context position]) (d - 1) root context.length)
    (width : (context[root]?.getD default).coordinates.length = d) :
    shift (context[root]?.getD default).coordinates d (transplantDelta d context root position) 1 =
      position := by
  apply List.ext_getElem
  · simp only [shift_width, width, positionWidth]
  · intro j left right
    have room : j < d := by simpa only [shift_width, width] using left
    have result := transplant_delta_values coherent positive position insideRoot path j room
    have value : (shift (context[root]?.getD default).coordinates d
        (transplantDelta d context root position) 1)[j]?.getD 0 = position[j]?.getD 0 := by
      rw [shift_value _ _ _ _ j (by omega), if_pos room, Nat.mul_one]
      exact result
    simpa only [List.getElem?_eq_getElem left, List.getElem?_eq_getElem right,
      Option.getD_some] using value

/-- The actual ancestor-to-current-column entry, including the complete
numerical view and actual nonnegative coordinate differences. -/
theorem transplant_shiftView {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context) (positive : 0 < d)
    (position : List Nat)
    (positionUnit : Parents.UnitSteps d (context ++ [Parents.label d context position]))
    {root : Nat} (insideRoot : root < context.length)
    (path : Parents.Ancestor (context ++ [Parents.label d context position]) (d - 1) root context.length) :
    ShiftView d (context.take (root + 1)) (context ++ [Parents.label d context position])
      (List.range root ++ [context.length]) (List.replicate root 0 ++ [d]) root d
      (transplantDelta d context root position) 1 := by
  have length : (context.take (root + 1)).length = root + 1 := by simp only [List.length_take]; omega
  refine ⟨coherent.restrict (List.take_prefix ..), valid.restrict (List.take_prefix ..),
    Parents.coherent_append_label coherent _, Parents.context_valid_append_label d context valid _,
    positionUnit, Parents.transplant_numericalView coherent valid positive position insideRoot path,
    by simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil, length],
    BMS.HistoryCorrect.at_root (valid.restrict (List.take_prefix ..)) root d,
    by omega, Nat.le_refl d, ?_⟩
  intro p inside j room
  by_cases old : p < root
  · rw [Parents.point_append_old _ p context.length (by simpa only [List.length_range] using old),
      Parents.point_range root p old, List.getElem?_append_left (by simpa only [List.length_replicate] using old),
      List.getElem?_replicate_of_lt old, Option.getD_some, if_neg (by omega), Nat.add_zero,
      ← Parents.reading_prefix (List.prefix_append context _) j p (by omega),
      Parents.reading_prefix (List.take_prefix (root + 1) context) j p inside]
  · have same : p = root := by omega
    subst p
    have point : Parents.point (List.range root ++ [context.length]) root = context.length := by
      simpa only [List.length_range] using Parents.point_append_last (List.range root) context.length
    have marked : (List.replicate root 0 ++ [d])[root]? = some d := by
      simpa only [List.length_replicate] using
        (show (List.replicate root 0 ++ [d])[(List.replicate root 0).length]? = some d from
          List.getElem?_concat_length)
    rw [point, marked, Option.getD_some, if_pos room, Nat.mul_one, Parents.reading_append_label,
      Parents.reading_prefix (List.take_prefix (root + 1) context) j root inside]
    exact (transplant_delta_values coherent positive position insideRoot path j room).symm

theorem transplant_keyShiftView {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context) (positive : 0 < d)
    (position : List Nat)
    (positionUnit : Parents.UnitSteps d (context ++ [Parents.label d context position]))
    {root : Nat} (insideRoot : root < context.length)
    (path : Parents.Ancestor (context ++ [Parents.label d context position]) (d - 1) root context.length) :
    KeyShiftView (transplant_shiftView coherent valid positive position positionUnit insideRoot path)
      (List.replicate root 0 ++ [d]) (List.replicate context.length 0 ++ [d]) := by
  have length : (context.take (root + 1)).length = root + 1 := by simp only [List.length_take]; omega
  refine ⟨BMS.HistoryCorrect.at_root (valid.restrict (List.take_prefix ..)) root d,
    by simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil, length],
    by simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil], ?_⟩
  intro p bound
  by_cases old : p < root
  · rw [Parents.point_append_old _ p context.length (by simpa only [List.length_range] using old),
      Parents.point_range root p old,
      List.getElem?_append_left (by simp only [List.length_replicate]; omega),
      List.getElem?_replicate_of_lt (by omega : p < context.length),
      List.getElem?_append_left (by simpa only [List.length_replicate] using old),
      List.getElem?_replicate_of_lt old]
  · have same : p = root := by omega
    subst p
    have point : Parents.point (List.range root ++ [context.length]) root = context.length := by
      simpa only [List.length_range] using Parents.point_append_last (List.range root) context.length
    rw [point]
    have left : (List.replicate context.length 0 ++ [d])[context.length]? = some d := by
      simpa only [List.length_replicate] using
        (show (List.replicate context.length 0 ++ [d])[(List.replicate context.length 0).length]? = some d from
          List.getElem?_concat_length)
    have right : (List.replicate root 0 ++ [d])[root]? = some d := by
      simpa only [List.length_replicate] using
        (show (List.replicate root 0 ++ [d])[(List.replicate root 0).length]? = some d from
          List.getElem?_concat_length)
    rw [left, right]

theorem transplantedForests_finiteLegal {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context) (positive : 0 < d)
    (position : List Nat)
    (positionUnit : Parents.UnitSteps d (context ++ [Parents.label d context position]))
    {root : Nat} (insideRoot : root < context.length)
    (path : Parents.Ancestor (context ++ [Parents.label d context position]) (d - 1) root context.length)
    (hs : Forests (List Nat))
    (legal : FiniteLegalForests d (context.take (root + 1)) (Parents.reading context 0 root) hs) :
    FiniteLegalForests d (context ++ [Parents.label d context position]) (position[0]?.getD 0)
      (transplantedForests d context root position hs) := by
  have scope := transplant_shiftView coherent valid positive position positionUnit insideRoot path
  have input : FiniteLegalForests d (context.take (root + 1))
      (Parents.reading (context.take (root + 1)) 0 root) hs := by
    rw [Parents.reading_prefix (List.take_prefix (root + 1) context) 0 root scope.afterRoot]
    exact legal
  have result := copiedForests_finiteLegal scope positive root scope.afterRoot
    (by simp only [List.length_take, Nat.min_eq_left (by omega : root + 1 ≤ context.length),
      Nat.add_sub_cancel]; exact .refl _) hs input
  have point : Parents.point (List.range root ++ [context.length]) root = context.length := by
    simpa only [List.length_range] using Parents.point_append_last (List.range root) context.length
  rw [point, Parents.reading_append_label] at result
  exact result

/-- The whole attachment's recomputed key is preserved, including all
nested forests. An actual standard-domain occurrence is not an input. -/
theorem transplantedForests_key {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context) (positive : 0 < d)
    (position : List Nat) (positionWidth : position.length = d)
    (positionUnit : Parents.UnitSteps d (context ++ [Parents.label d context position]))
    {root : Nat} (insideRoot : root < context.length)
    (path : Parents.Ancestor (context ++ [Parents.label d context position]) (d - 1) root context.length)
    (width : (context[root]?.getD default).coordinates.length = d)
    (hs : Forests (List Nat))
    (legal : FiniteLegalForests d (context.take (root + 1)) (Parents.reading context 0 root) hs) :
    Keys.ofColumn d context.length (Parents.label d context position)
      (Parents.annotateForests d (context ++ [Parents.label d context position])
        (transplantedForests d context root position hs)) =
      Keys.ofColumn d root (context[root]?.getD default)
        (Parents.annotateForests d (context.take (root + 1)) hs) := by
  have scope := transplant_shiftView coherent valid positive position positionUnit insideRoot path
  have keys := transplant_keyShiftView coherent valid positive position positionUnit insideRoot path
  have result := copied_forests_key d hs _ _ _ _ _ _ root d _ 1 scope keys
    (context[root]?.getD default).coordinates width (Parents.reading context 0 root) legal
  have point : Parents.point (List.range root ++ [context.length]) root = context.length := by
    simpa only [List.length_range] using Parents.point_append_last (List.range root) context.length
  rw [point, transplant_head coherent positive position positionWidth insideRoot path width] at result
  exact result

/-- Compare a closed ancestor key with the current key by a literal
comparison of two finite-legal forests at the current common entry. -/
theorem transplanted_key_compare {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context) (positive : 0 < d)
    (position : List Nat) (positionWidth : position.length = d)
    (positionUnit : Parents.UnitSteps d (context ++ [Parents.label d context position]))
    {root : Nat} (insideRoot : root < context.length)
    (path : Parents.Ancestor (context ++ [Parents.label d context position]) (d - 1) root context.length)
    (width : (context[root]?.getD default).coordinates.length = d)
    (hs ks : Forests (List Nat))
    (oldLegal : FiniteLegalForests d (context.take (root + 1)) (Parents.reading context 0 root) hs)
    (currentLegal : FiniteLegalForests d (context ++ [Parents.label d context position])
      (position[0]?.getD 0) ks) :
    Keys.compare
      (Keys.ofColumn d root (context[root]?.getD default)
        (Parents.annotateForests d (context.take (root + 1)) hs))
      (Keys.ofColumn d context.length (Parents.label d context position)
        (Parents.annotateForests d (context ++ [Parents.label d context position]) ks)) =
      (transplantedForests d context root position hs).compare (listCompare Ord.compare) ks := by
  rw [← transplantedForests_key coherent valid positive position positionWidth positionUnit insideRoot path width hs oldLegal]
  exact Keys.ofColumn_annotate_compare coherent valid position _ ks
    (transplantedForests_finiteLegal coherent valid positive position positionUnit insideRoot path hs oldLegal)
    currentLegal

end BTnSSBMS.Source
