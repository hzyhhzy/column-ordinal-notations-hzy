import BTnSSBMS.CopyEntry
import BTnSSBMS.NumericalOrder

/-!
The real entering state of an intermediate-row partial rebase. This is
not an ordinary fundamental-sequence copy: the old root and new position
have the same cut-row parent. All new parents are recomputed by the fixed
search. No source block-order inequality or key comparison is assumed.
-/
namespace BTnSSBMS.Parents

theorem label_value_eq_of_same_parent {d : Nat} {context : ParentContext}
    (unit : UnitSteps d context) (coordinates : List Nat)
    (nextUnit : UnitSteps d (context ++ [label d context coordinates]))
    {row root : Nat} (room : row < d) (inside : root < context.length)
    (same : (label d context coordinates).parents[row]?.join = parent context row root) :
    coordinates[row]?.getD 0 = reading context row root := by
  rw [label_unit_value coordinates nextUnit room, same, unit root inside row room]

theorem partial_rebase_head_parents {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context)
    (unit : UnitSteps d context) (position head : List Nat)
    (positionUnit : UnitSteps d (context ++ [label d context position]))
    {cut root : Nat} (room : cut < d) (insideRoot : root < context.length)
    (same : (label d context position).parents[cut]?.join = parent context cut root)
    (low : ∀ j, j < cut → head[j]?.getD 0 = position[j]?.getD 0)
    (high : ∀ j, cut ≤ j → j < d → head[j]?.getD 0 = reading context j root)
    (row : Nat) (inside : row < d) :
    (label d context head).parents[row]?.join =
      if row < cut then (label d context position).parents[row]?.join else parent context row root := by
  by_cases below : row < cut
  · simp only [below, if_true]
    exact label_parents_congr_through d context head position row inside
      (fun j hj => low j (by omega))
  · simp only [below, if_false]
    have value := label_value_eq_of_same_parent unit position positionUnit room insideRoot same
    have boundary : (label d context head).parents[cut]?.join = parent context cut root := by
      apply Eq.trans (label_parents_congr_through d context head position cut room ?_) same
      intro j before
      by_cases strictly : j < cut
      · exact low j strictly
      · have atCut : j = cut := by omega
        subst j
        exact (high cut (Nat.le_refl _) room).trans value.symm
    induction row with
    | zero =>
      have zero : cut = 0 := by omega
      subst cut
      exact boundary
    | succ row ih =>
      by_cases atCut : cut = row + 1
      · subst cut; exact boundary
      · rw [label_next d context head row inside, ih (by omega) (by omega),
          high (row + 1) (by omega) inside]
        exact (parent_next_search coherent valid inside insideRoot).symm

theorem partial_rebase_head_unitSteps {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context)
    (unit : UnitSteps d context) (position head : List Nat)
    (positionUnit : UnitSteps d (context ++ [label d context position]))
    {cut root : Nat} (room : cut < d) (insideRoot : root < context.length)
    (same : (label d context position).parents[cut]?.join = parent context cut root)
    (low : ∀ j, j < cut → head[j]?.getD 0 = position[j]?.getD 0)
    (high : ∀ j, cut ≤ j → j < d → head[j]?.getD 0 = reading context j root) :
    UnitSteps d (context ++ [label d context head]) := by
  apply unit.extend_one (context_valid_append_label d context valid head) (List.prefix_append _ _)
    (by simp)
  intro j inside
  rw [reading_append_label, append_label_parent,
    partial_rebase_head_parents coherent valid unit position head positionUnit room insideRoot same low high j inside]
  by_cases below : j < cut
  · rw [if_pos below, low j below, label_unit_value position positionUnit inside]
    cases edge : (label d context position).parents[j]?.join with
    | none => rfl
    | some p =>
      simp only [Option.map_some, Option.getD_some]
      have bounded := label_parent_bound d context position j p edge
      exact congrArg (· + 1) (reading_prefix (List.prefix_append _ _) j p bounded)
  · rw [if_neg below, high j (by omega) inside, unit root insideRoot j inside]
    cases edge : parent context j root with
    | none => rfl
    | some p =>
      simp only [Option.map_some, Option.getD_some]
      have before := parent_earlier valid edge
      exact congrArg (· + 1) (reading_prefix (List.prefix_append _ _) j p (by omega))

theorem partial_rebase_head_ancestors {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context)
    (unit : UnitSteps d context) (position head : List Nat)
    (positionUnit : UnitSteps d (context ++ [label d context position]))
    {cut root : Nat} (positive : 0 < cut) (room : cut < d) (insideRoot : root < context.length)
    (path : Ancestor (context ++ [label d context position]) (cut - 1) root context.length)
    (same : (label d context position).parents[cut]?.join = parent context cut root)
    (low : ∀ j, j < cut → head[j]?.getD 0 = position[j]?.getD 0)
    (high : ∀ j, cut ≤ j → j < d → head[j]?.getD 0 = reading context j root)
    {j p : Nat} (inside : j < d) (oldParent : parent context j root = some p) :
    Ancestor (context ++ [label d context head]) j p context.length := by
  have before := parent_earlier valid oldParent
  have table := partial_rebase_head_parents coherent valid unit position head positionUnit
    room insideRoot same low high j inside
  by_cases below : j < cut
  · have lower := path.lower_row (coherent_append_label coherent position)
      (by omega : cut - 1 < d) (by omega : j ≤ cut - 1)
    have toRoot : Ancestor (context ++ [label d context position]) j p root :=
      (Ancestor.up oldParent (.refl _)).prefix (List.prefix_append _ _)
    exact (toRoot.trans lower).replace_last valid position head (by omega)
      (by simpa only [below, if_true] using table.symm)
  · apply Ancestor.up ?_ (.refl _)
    rw [append_label_parent, table, if_neg below, oldParent]

theorem partial_rebase_numericalView {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context)
    (unit : UnitSteps d context) (position head : List Nat)
    (positionUnit : UnitSteps d (context ++ [label d context position]))
    {cut root : Nat} (positive : 0 < cut) (room : cut < d) (insideRoot : root < context.length)
    (path : Ancestor (context ++ [label d context position]) (cut - 1) root context.length)
    (same : (label d context position).parents[cut]?.join = parent context cut root)
    (low : ∀ j, j < cut → head[j]?.getD 0 = position[j]?.getD 0)
    (high : ∀ j, cut ≤ j → j < d → head[j]?.getD 0 = reading context j root) :
    NumericalView d (context.take (root + 1)) (context ++ [label d context head])
      (List.range root ++ [context.length]) := by
  have length : (context.take root).length = root := by simp only [List.length_take]; omega
  have divided := List.take_succ_eq_append_getElem insideRoot
  have view := numericalView_identity d (context.take root)
  rw [length] at view
  rw [divided]
  apply view.append_stretched context[root]
    (by rw [← divided]; exact valid.restrict (List.take_prefix ..))
    ((List.take_prefix root context).trans (List.prefix_append context [label d context head]))
    context.length (by simp) (by simp) (by simp only [length]; omega)
  intro j inside p edge
  have actual : parent context j root = some p := by
    simpa only [parent, List.getElem?_eq_getElem insideRoot, Option.bind_some] using edge
  have earlier := parent_earlier valid actual
  rw [point_range root p earlier]
  exact partial_rebase_head_ancestors coherent valid unit position head positionUnit
    positive room insideRoot path same low high inside actual

end BTnSSBMS.Parents

namespace BTnSSBMS.Source

theorem partial_rebase_head_values {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context)
    (position : List Nat) {cut root : Nat} (positive : 0 < cut) (room : cut < d)
    (insideRoot : root < context.length)
    (path : Parents.Ancestor (context ++ [Parents.label d context position]) (cut - 1) root context.length)
    (width : (context[root]?.getD default).coordinates.length = d) :
    let rootCoordinates := (context[root]?.getD default).coordinates
    let delta := (List.range cut).map (fun j => position[j]?.getD 0 - rootCoordinates[j]?.getD 0)
    let head := shift rootCoordinates cut delta 1
    (∀ j, j < cut → head[j]?.getD 0 = position[j]?.getD 0) ∧
    (∀ j, cut ≤ j → j < d → head[j]?.getD 0 = Parents.reading context j root) := by
  dsimp only
  constructor
  · intro j below
    have lower := path.lower_row (Parents.coherent_append_label coherent position)
      (by omega : cut - 1 < d) (by omega : j ≤ cut - 1)
    have strict := lower.reading_lt (Parents.coherent_append_label coherent position)
      (by omega : root ≠ context.length)
    rw [Parents.reading_append_label,
      ← Parents.reading_prefix (List.prefix_append context [Parents.label d context position]) j root insideRoot] at strict
    rw [shift_value _ _ cut 1 j (by omega), if_pos below]
    simp only [List.getElem?_map, List.getElem?_range below, Option.map_some, Option.getD_some, Nat.mul_one]
    change (context[root]?.getD default).coordinates[j]?.getD 0 < position[j]?.getD 0 at strict
    omega
  · intro j above inside
    rw [shift_value _ _ cut 1 j (by omega), if_neg (by omega), Nat.add_zero]
    rfl

/-- The partial rebase constructs its shift invariant from the real SB
pair's finite geometry, rather than requiring an incoming invariant. -/
theorem partial_rebase_shiftView {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (unit : Parents.UnitSteps d context) (position : List Nat)
    (positionUnit : Parents.UnitSteps d (context ++ [Parents.label d context position]))
    {cut root : Nat} (positive : 0 < cut) (room : cut < d) (insideRoot : root < context.length)
    (path : Parents.Ancestor (context ++ [Parents.label d context position]) (cut - 1) root context.length)
    (same : (Parents.label d context position).parents[cut]?.join = Parents.parent context cut root)
    (width : (context[root]?.getD default).coordinates.length = d) :
    let rootCoordinates := (context[root]?.getD default).coordinates
    let delta := (List.range cut).map (fun j => position[j]?.getD 0 - rootCoordinates[j]?.getD 0)
    let head := shift rootCoordinates cut delta 1
    ShiftView d (context.take (root + 1)) (context ++ [Parents.label d context head])
      (List.range root ++ [context.length]) (List.replicate root 0 ++ [cut]) root cut delta 1 := by
  dsimp only
  have length : (context.take (root + 1)).length = root + 1 := by simp only [List.length_take]; omega
  have values := partial_rebase_head_values coherent position positive room insideRoot path width
  refine ⟨coherent.restrict (List.take_prefix ..), valid.restrict (List.take_prefix ..),
    Parents.coherent_append_label coherent _, Parents.context_valid_append_label d context valid _,
    Parents.partial_rebase_head_unitSteps coherent valid unit position _ positionUnit
      room insideRoot same values.1 values.2,
    Parents.partial_rebase_numericalView coherent valid unit position _ positionUnit
      positive room insideRoot path same values.1 values.2,
    by simp [length], BMS.HistoryCorrect.at_root (valid.restrict (List.take_prefix ..)) root cut,
    by omega, by omega, ?_⟩
  intro p inside j row
  by_cases old : p < root
  · rw [Parents.point_append_old _ p context.length (by simpa using old), Parents.point_range root p old,
      List.getElem?_append_left (by simpa using old), List.getElem?_replicate_of_lt old,
      Option.getD_some, if_neg (by omega), Nat.add_zero,
      ← Parents.reading_prefix (List.prefix_append context _) j p (by omega),
      Parents.reading_prefix (List.take_prefix (root + 1) context) j p inside]
  · have atRoot : p = root := by omega
    subst p
    have point : Parents.point (List.range root ++ [context.length]) root = context.length := by
      simpa only [List.length_range] using Parents.point_append_last (List.range root) context.length
    have marked : (List.replicate root 0 ++ [cut])[root]? = some cut := by
      simpa only [List.length_replicate] using
        (show (List.replicate root 0 ++ [cut])[(List.replicate root 0).length]? = some cut from
          List.getElem?_concat_length)
    rw [point, marked, Option.getD_some, Parents.reading_append_label,
      Parents.reading_prefix (List.take_prefix (root + 1) context) j root inside,
      shift_value _ _ cut 1 j (by omega)]
    rfl

/-- All finite material rooted at the old column, with its complete
attachments retained, is legal after the actual intermediate-row rebase.
This does not assert any block inequality or equality of normalized keys. -/
theorem partial_rebase_finiteLegal {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (unit : Parents.UnitSteps d context) (position : List Nat)
    (positionUnit : Parents.UnitSteps d (context ++ [Parents.label d context position]))
    {cut root : Nat} (positive : 0 < cut) (room : cut < d) (insideRoot : root < context.length)
    (path : Parents.Ancestor (context ++ [Parents.label d context position]) (cut - 1) root context.length)
    (same : (Parents.label d context position).parents[cut]?.join = Parents.parent context cut root)
    (hs : Forests (List Nat)) (rest : NumericalExpr)
    (legal : FiniteLegal d (context.take root)
      (.cons (context[root]?.getD default).coordinates hs rest)) :
    let rootCoordinates := (context[root]?.getD default).coordinates
    let delta := (List.range cut).map (fun j => position[j]?.getD 0 - rootCoordinates[j]?.getD 0)
    FiniteLegal d context
      (copied d root cut delta 1 (context.take root) (List.replicate root 0)
        (.cons rootCoordinates hs rest)) := by
  dsimp only
  have divided := coherent.take_succ_label insideRoot
  have scope := partial_rebase_shiftView coherent valid unit position positionUnit
    positive room insideRoot path same legal.1
  rw [copied_at_root]
  have nextLegal := legal
  simp only [FiniteLegal] at nextLegal
  rw [← divided] at nextLegal
  refine ⟨(shift_width ..).trans legal.1, scope.targetUnit, ?_, ?_, ?_⟩
  · intro attached j inside
    have nonempty : hs ≠ .nil := by
      intro empty
      subst hs
      exact attached rfl
    have nonzero := legal.2.2.1 nonempty j inside
    rw [shift_value _ _ _ _ j (by rw [legal.1]; exact inside)]
    omega
  · rw [← divided]
    have rootReading : Parents.reading (context.take (root + 1)) 0 root =
        (context[root]?.getD default).coordinates[0]?.getD 0 := by
      rw [Parents.reading_prefix (List.take_prefix (root + 1) context) 0 root
        (by simp only [List.length_take]; omega)]
      rfl
    have forests := copiedForests_finiteLegal scope (by omega) root scope.afterRoot
      (by simp only [List.length_take, Nat.min_eq_left (by omega : root + 1 ≤ context.length),
        Nat.add_sub_cancel]; exact .refl _) hs (by rw [rootReading]; exact nextLegal.2.2.2.1)
    have point : Parents.point (List.range root ++ [context.length]) root = context.length := by
      simpa only [List.length_range] using Parents.point_append_last (List.range root) context.length
    rw [point, Parents.reading_append_label] at forests
    exact forests
  · rw [← divided]
    exact copied_finiteLegal scope (by omega) rest nextLegal.2.2.2.2

end BTnSSBMS.Source
