import BTnSSBMS.CopyBody

/-!
Constructing the first ordinary-copy entering state from the actual
selected numerical root. The copied root replaces a terminal column;
the old prefix is retained and the root's lower edges are stretched.
-/
namespace BTnSSBMS.Parents

theorem ContextValid.restrict {small large : ParentContext}
    (valid : ContextValid large) (initial : small <+: large) : ContextValid small := by
  obtain ⟨tail, rfl⟩ := initial
  intro i a lookup p member
  have bound := (List.getElem?_eq_some_iff.mp lookup).choose
  exact valid i a (by rw [List.getElem?_append_left bound]; exact lookup) p member

theorem Coherent.restrict {d : Nat} {small large : ParentContext}
    (coherent : Coherent d large) (initial : small <+: large) : Coherent d small := by
  obtain ⟨tail, rfl⟩ := initial
  intro i a lookup
  have bound := (List.getElem?_eq_some_iff.mp lookup).choose
  have result := coherent i a (by rw [List.getElem?_append_left bound]; exact lookup)
  rw [List.take_append_of_le_length (by omega)] at result
  exact result

theorem UnitSteps.restrict {d : Nat} {small large : ParentContext}
    (unit : UnitSteps d large) (valid : ContextValid large)
    (initial : small <+: large) : UnitSteps d small := by
  intro i inside j room
  have result := unit i (Nat.lt_of_lt_of_le inside initial.length_le) j room
  rw [← reading_prefix initial j i inside, ← parent_prefix_eq initial j i inside] at result
  cases selected : parent small j i with
  | none => simpa only [selected, Option.map_none, Option.getD_none] using result
  | some p =>
    have earlier := parent_earlier (valid.restrict initial) selected
    simpa only [selected, Option.map_some, Option.getD_some,
      ← reading_prefix initial j p (by omega)] using result

theorem point_range (count p : Nat) (inside : p < count) : point (List.range count) p = p := by
  simp only [point, List.getElem?_range inside, Option.getD_some]

theorem numericalView_identity (d : Nat) (context : ParentContext) :
    NumericalView d context context (List.range context.length) := by
  refine ⟨List.length_range, ?_, ?_, ?_, ?_⟩
  · intro p inside
    rw [point_range _ p inside]
    exact inside
  · intro j room p q pBound qBound path
    simpa only [point_range _ p pBound, point_range _ q qBound] using path
  · intro nonempty
    have positive : 0 < context.length := List.length_pos_iff.mpr nonempty
    rw [point_range _ _ (by omega)]
    omega
  · intro p q earlier inside
    rw [point_range _ p (by omega), point_range _ q inside]
    exact earlier

theorem Coherent.take_succ_label {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) {root : Nat} (inside : root < context.length) :
    context.take (root + 1) = context.take root ++
      [label d (context.take root) (context[root]?.getD default).coordinates] := by
  rw [List.take_succ_eq_append_getElem inside, List.getElem?_eq_getElem inside, Option.getD_some]
  have parents := coherent root context[root] (List.getElem?_eq_getElem inside)
  have same : context[root] = label d (context.take root) context[root].coordinates := by
    cases value : context[root] with
    | mk coordinates stored =>
      simp only [value, label] at parents ⊢
      rw [parents]
  exact congrArg (fun a => context.take root ++ [a]) same

/-- Changing the last column while keeping its row parent preserves
every old ancestor of that last column in that row. -/
theorem Ancestor.replace_last {d : Nat} {context : ParentContext}
    (valid : ContextValid context) (a b : List Nat) {row root : Nat}
    (old : root < context.length)
    (same : (label d context a).parents[row]?.join = (label d context b).parents[row]?.join)
    (path : Ancestor (context ++ [label d context a]) row root context.length) :
    Ancestor (context ++ [label d context b]) row root context.length := by
  obtain ⟨p, edge, previous⟩ := (Ancestor.iff_parent (by omega : root ≠ context.length)).mp path
  have nextValid := context_valid_append_label d context valid a
  have before := parent_earlier nextValid edge
  have previousOld := previous.restrict (List.prefix_append context [label d context a]) nextValid before
  apply Ancestor.up ?_ (previousOld.prefix (List.prefix_append context [label d context b]))
  rw [append_label_parent] at edge ⊢
  exact same ▸ edge

/-- Every old parent of the copied root is an actual ancestor of its
replacement. The lower-row paths may pass through the retained corridor. -/
theorem first_copy_head_ancestors {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context)
    (terminal head : List Nat) {branch root : Nat} (room : branch < d)
    (selected : (label d context terminal).parents[branch]?.join = some root)
    (low : ∀ j, j < branch → head[j]?.getD 0 = terminal[j]?.getD 0)
    (high : ∀ j, branch ≤ j → j < d → head[j]?.getD 0 = reading context j root)
    {j p : Nat} (inside : j < d) (oldParent : parent context j root = some p) :
    Ancestor (context ++ [label d context head]) j p context.length := by
  have rootBound := label_parent_bound d context terminal branch root selected
  have before := parent_earlier valid oldParent
  have table := first_copy_head_parents coherent valid terminal head room selected low high j inside
  by_cases below : j < branch
  · have rootPath : Ancestor (context ++ [label d context terminal]) branch root context.length :=
      .up (by rw [append_label_parent]; exact selected) (.refl _)
    have lowerPath := rootPath.lower_row (coherent_append_label coherent terminal) room (by omega : j ≤ branch)
    have parentPath : Ancestor (context ++ [label d context terminal]) j p root :=
      (Ancestor.up oldParent (.refl _)).prefix (List.prefix_append context [label d context terminal])
    exact (parentPath.trans lowerPath).replace_last valid terminal head (by omega)
      (by simpa only [below, if_true] using table.symm)
  · apply Ancestor.up ?_ (.refl _)
    rw [append_label_parent, table, if_neg below, oldParent]

theorem first_copy_numericalView {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context)
    (terminal head : List Nat) {branch root : Nat} (room : branch < d)
    (selected : (label d context terminal).parents[branch]?.join = some root)
    (low : ∀ j, j < branch → head[j]?.getD 0 = terminal[j]?.getD 0)
    (high : ∀ j, branch ≤ j → j < d → head[j]?.getD 0 = reading context j root) :
    NumericalView d (context.take (root + 1)) (context ++ [label d context head])
      (List.range root ++ [context.length]) := by
  have rootBound := label_parent_bound d context terminal branch root selected
  have length : (context.take root).length = root := by simp only [List.length_take]; omega
  have divided := List.take_succ_eq_append_getElem rootBound
  have view := numericalView_identity d (context.take root)
  rw [length] at view
  rw [divided]
  apply view.append_stretched context[root]
    (by rw [← divided]; exact valid.restrict (List.take_prefix ..))
    ((List.take_prefix root context).trans (List.prefix_append context [label d context head]))
    context.length (by simp) (by simp) (by simp only [length]; omega)
  intro j inside p edge
  have actual : parent context j root = some p := by
    simpa only [parent, List.getElem?_eq_getElem rootBound, Option.bind_some] using edge
  have earlier := parent_earlier valid actual
  rw [point_range root p earlier]
  exact first_copy_head_ancestors coherent valid terminal head room selected low high inside actual

end BTnSSBMS.Parents

namespace BTnSSBMS.BMS

theorem HistoryCorrect.at_root {context : ParentContext} (valid : Parents.ContextValid context)
    (root cap : Nat) : HistoryCorrect context root cap (List.replicate root 0 ++ [cap]) := by
  intro i inside j
  by_cases before : i < root
  · rw [List.getElem?_append_left (show i < (List.replicate root 0).length by simpa using before)]
    simp only [List.getElem?_replicate_of_lt before,
      Option.getD_some, Nat.not_lt_zero, false_iff, not_and]
    intro room path
    have earlier := path.le valid
    omega
  · have same : i = root := by
      simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil] at inside
      omega
    subst i
    have rootLookup : (List.replicate root 0 ++ [cap])[root]? = some cap := by
      simpa only [List.length_replicate] using (show (List.replicate root 0 ++ [cap])[(List.replicate root 0).length]? = some cap from
        List.getElem?_concat_length)
    simp only [rootLookup, Option.getD_some]
    exact ⟨fun h => ⟨h, .refl _⟩, fun h => h.1⟩

end BTnSSBMS.BMS

namespace BTnSSBMS.Source

/-- No entering transport premise is assumed: the first actual low-class
copy constructs it from the original finite coherent, unit-step context. -/
theorem first_copy_shiftView {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (unit : Parents.UnitSteps d context) (terminal : List Nat)
    (terminalUnit : Parents.UnitSteps d (context ++ [Parents.label d context terminal]))
    {branch root : Nat} (room : branch < d)
    (selected : (Parents.label d context terminal).parents[branch]?.join = some root)
    (width : (context[root]?.getD default).coordinates.length = d) :
    let rootCoordinates := (context[root]?.getD default).coordinates
    let delta := (List.range branch).map (fun j => terminal[j]?.getD 0 - rootCoordinates[j]?.getD 0)
    let head := shift rootCoordinates branch delta 1
    ShiftView d (context.take (root + 1)) (context ++ [Parents.label d context head])
      (List.range root ++ [context.length]) (List.replicate root 0 ++ [branch]) root branch delta 1 := by
  dsimp only
  have rootBound := Parents.label_parent_bound d context terminal branch root selected
  have length : (context.take (root + 1)).length = root + 1 := by simp only [List.length_take]; omega
  have values := shifted_copy_head_values coherent valid terminal room selected width
  refine ⟨coherent.restrict (List.take_prefix ..), valid.restrict (List.take_prefix ..),
    Parents.coherent_append_label coherent _, Parents.context_valid_append_label d context valid _,
    shifted_copy_head_unitSteps coherent valid unit terminal terminalUnit room selected width,
    Parents.first_copy_numericalView coherent valid terminal _ room selected values.1 values.2,
    by simp [length], BMS.HistoryCorrect.at_root (valid.restrict (List.take_prefix ..)) root branch,
    by omega, by omega, ?_⟩
  intro p inside j row
  by_cases old : p < root
  · rw [Parents.point_append_old _ p context.length (by simpa using old), Parents.point_range root p old,
      List.getElem?_append_left (by simpa using old), List.getElem?_replicate_of_lt old,
      Option.getD_some, if_neg (by omega), Nat.add_zero,
      ← Parents.reading_prefix (List.prefix_append context _) j p (by omega),
      Parents.reading_prefix (List.take_prefix (root + 1) context) j p inside]
  · have same : p = root := by omega
    subst p
    have atRoot : Parents.point (List.range root ++ [context.length]) root = context.length := by
      simpa only [List.length_range] using Parents.point_append_last (List.range root) context.length
    have marked : (List.replicate root 0 ++ [branch])[root]? = some branch := by
      simpa only [List.length_replicate] using (show (List.replicate root 0 ++ [branch])[(List.replicate root 0).length]? = some branch from
        List.getElem?_concat_length)
    rw [atRoot, marked, Option.getD_some, Parents.reading_append_label,
      Parents.reading_prefix (List.take_prefix (root + 1) context) j root inside,
      shift_value _ _ branch 1 j (by omega)]
    rfl

theorem copied_at_root (d root cap : Nat) (delta : List Nat) (phase : Nat)
    (source : ParentContext) (a : List Nat) (hs : Forests (List Nat)) (t : NumericalExpr) :
    copied d root cap delta phase source (List.replicate root 0) (.cons a hs t) =
      .cons (shift a cap delta phase)
        (copiedForests d root cap delta phase (source ++ [Parents.label d source a])
          (List.replicate root 0 ++ [cap]) hs)
        (copied d root cap delta phase (source ++ [Parents.label d source a])
          (List.replicate root 0 ++ [cap]) t) := by
  simp only [copied, Parents.annotate, mark, List.length_replicate, Nat.lt_irrefl,
    if_false, if_true, decide_false, Bool.false_and, Bool.false_eq_true,
    Expr.map, copiedForests]
  rfl

/-- A complete root and its arbitrary nested ordinary-copy material are
legal in the actual new context, with no transport-state premise left. -/
theorem first_copy_finiteLegal {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (unit : Parents.UnitSteps d context) (terminal : List Nat)
    (terminalUnit : Parents.UnitSteps d (context ++ [Parents.label d context terminal]))
    {branch root : Nat} (room : branch < d)
    (selected : (Parents.label d context terminal).parents[branch]?.join = some root)
    (hs : Forests (List Nat)) (rest : NumericalExpr)
    (legal : FiniteLegal d (context.take root)
      (.cons (context[root]?.getD default).coordinates hs rest)) :
    let rootCoordinates := (context[root]?.getD default).coordinates
    let delta := (List.range branch).map (fun j => terminal[j]?.getD 0 - rootCoordinates[j]?.getD 0)
    FiniteLegal d context
      (copied d root branch delta 1 (context.take root) (List.replicate root 0)
        (.cons rootCoordinates hs rest)) := by
  dsimp only
  have rootBound := Parents.label_parent_bound d context terminal branch root selected
  have divided := coherent.take_succ_label rootBound
  have scope := first_copy_shiftView coherent valid unit terminal terminalUnit room selected legal.1
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
    have positive := legal.2.2.1 nonempty j inside
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
