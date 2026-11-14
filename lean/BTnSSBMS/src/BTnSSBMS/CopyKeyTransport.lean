import BTnSSBMS.PartialRebaseEntry
import BTnSSBMS.KeyNormalizationOrder

/-!
Complete root-key preservation under an ancestry-sensitive copy. The
activation histories are run at two different caps: the copy cap and the
full key dimension. Actual recomputed parents transport the key history;
signed normalization then cancels precisely the active shifts.
-/
namespace BTnSSBMS.Parents

theorem NumericalView.point_le_iff {d : Nat} {source target : ParentContext} {visible : List Nat}
    (view : NumericalView d source target visible) {a b : Nat}
    (left : a < source.length) (right : b < source.length) :
    point visible a ≤ point visible b ↔ a ≤ b := by
  constructor
  · intro ordered
    by_cases forward : a ≤ b
    · exact forward
    · have reverse := view.increasing b a (by omega) left
      omega
  · intro ordered
    by_cases same : a = b
    · subst b; exact Nat.le_refl _
    · exact Nat.le_of_lt (view.increasing a b (by omega) right)

end BTnSSBMS.Parents

namespace BTnSSBMS.Keys

private theorem takeWhile_congr_on (xs : List α) (p q : α → Bool)
    (same : ∀ x ∈ xs, p x = q x) : xs.takeWhile p = xs.takeWhile q := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.takeWhile_cons, List.takeWhile_cons, same x (by simp)]
    rw [ih (fun a member => same a (by simp; exact Or.inr member))]

theorem threshold_transport {d : Nat} {source target : ParentContext} {visible : List Nat}
    (view : Parents.NumericalView d source target visible)
    (root : Nat) (insideRoot : root < source.length) (oldHistory newHistory : List Nat)
    (history : ∀ p, p < source.length →
      newHistory[Parents.point visible p]?.getD 0 = oldHistory[p]?.getD 0)
    (a b : List Nat)
    (parents : ∀ j, j < d → (Parents.label d target b).parents[j]?.join =
      ((Parents.label d source a).parents[j]?.join).map (Parents.point visible)) :
    threshold d (Parents.point visible root) newHistory (Parents.label d target b) =
      threshold d root oldHistory (Parents.label d source a) := by
  unfold threshold
  apply congrArg List.length
  apply takeWhile_congr_on
  intro j member
  rw [parents j (List.mem_range.mp member)]
  cases selected : (Parents.label d source a).parents[j]?.join with
  | none => rfl
  | some p =>
    have inside := Parents.label_parent_bound d source a j p selected
    simp only [Option.map_some, history p inside, view.point_le_iff insideRoot inside]

end BTnSSBMS.Keys

namespace BTnSSBMS.Source

private theorem label_coordinates (d : Nat) (context : ParentContext) (a : List Nat) :
    (Parents.label d context a).coordinates = a := rfl

structure KeyShiftView {d : Nat} {source target : ParentContext} {visible history : List Nat}
    {root cap : Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d source target visible history root cap delta phase)
    (keyHistory targetHistory : List Nat) : Prop where
  correct : BMS.HistoryCorrect source root d keyHistory
  sourceLength : keyHistory.length = source.length
  targetLength : targetHistory.length = target.length
  history : ∀ p, p < source.length →
    targetHistory[Parents.point visible p]?.getD 0 = keyHistory[p]?.getD 0

theorem KeyShiftView.head_threshold {d : Nat} {source target : ParentContext} {visible history : List Nat}
    {root cap : Nat} {delta : List Nat} {phase : Nat}
    {scope : ShiftView d source target visible history root cap delta phase}
    {keyHistory targetHistory : List Nat} (keys : KeyShiftView scope keyHistory targetHistory)
    (a : List Nat) (width : a.length = d)
    (unit : Parents.UnitSteps d (source ++ [Parents.label d source a])) :
    Keys.threshold d (Parents.point visible root) targetHistory
      (Parents.label d target (shift a (Keys.threshold cap root history (Parents.label d source a)) delta phase)) =
      Keys.threshold d root keyHistory (Parents.label d source a) :=
  Keys.threshold_transport scope.view root scope.afterRoot keyHistory targetHistory keys.history
    a _ (scope.head_parents a width unit)

theorem KeyShiftView.copy_flag {d : Nat} {source target : ParentContext} {visible history : List Nat}
    {root cap : Nat} {delta : List Nat} {phase : Nat}
    {scope : ShiftView d source target visible history root cap delta phase}
    {keyHistory targetHistory : List Nat} (keys : KeyShiftView scope keyHistory targetHistory)
    (a : List Nat) (j : Nat) :
    j < Keys.threshold cap root history (Parents.label d source a) ↔
      j < cap ∧ j < Keys.threshold d root keyHistory (Parents.label d source a) := by
  rw [Keys.threshold_at_label scope.sourceCoherent scope.sourceValid scope.historyCorrect
    scope.historyLength scope.afterRoot scope.capBound a j,
    Keys.threshold_at_label scope.sourceCoherent scope.sourceValid keys.correct
    keys.sourceLength scope.afterRoot (Nat.le_refl d) a j]
  constructor
  · rintro ⟨room, path⟩
    exact ⟨room, by have bounded := scope.capBound; omega, path⟩
  · rintro ⟨room, _, path⟩
    exact ⟨room, path⟩

theorem KeyShiftView.head_normalize {d : Nat} {source target : ParentContext} {visible history : List Nat}
    {root cap : Nat} {delta : List Nat} {phase : Nat}
    {scope : ShiftView d source target visible history root cap delta phase}
    {keyHistory targetHistory : List Nat} (keys : KeyShiftView scope keyHistory targetHistory)
    (base a : List Nat) (baseWidth : base.length = d) (width : a.length = d) :
    Keys.normalize d (Keys.threshold d root keyHistory (Parents.label d source a))
      (shift base cap delta phase)
      (shift a (Keys.threshold cap root history (Parents.label d source a)) delta phase) =
    Keys.normalize d (Keys.threshold d root keyHistory (Parents.label d source a)) base a := by
  unfold Keys.normalize
  apply List.map_congr_left
  intro j member
  have room : j < d := List.mem_range.mp member
  rw [shift_value _ _ _ _ j (by omega), shift_value _ _ _ _ j (by omega)]
  have flags := keys.copy_flag a j
  by_cases active : j < Keys.threshold d root keyHistory (Parents.label d source a)
  · by_cases moved : j < cap
    · have shiftActive := flags.mpr ⟨moved, active⟩
      simp only [active, decide_true, moved, shiftActive, if_true, Keys.atom]
      apply congrArg (fun x : Int => (true, x))
      simp only [Int.ofNat_eq_natCast, Int.natCast_add]
      omega
    · have shiftInactive : ¬ j < Keys.threshold cap root history (Parents.label d source a) :=
        fun bad => moved (flags.mp bad).1
      simp only [active, decide_true, moved, shiftInactive, if_true, if_false, Nat.add_zero, Keys.atom]
  · have shiftInactive : ¬ j < Keys.threshold cap root history (Parents.label d source a) :=
      fun bad => active (flags.mp bad).2
    simp only [active, decide_false, shiftInactive, if_false, Nat.add_zero, Keys.atom, Bool.false_eq_true]

theorem KeyShiftView.append {d : Nat} {source target : ParentContext} {visible history : List Nat}
    {root cap : Nat} {delta : List Nat} {phase : Nat}
    {scope : ShiftView d source target visible history root cap delta phase}
    {keyHistory targetHistory : List Nat} (keys : KeyShiftView scope keyHistory targetHistory)
    (a : List Nat) (width : a.length = d)
    (unit : Parents.UnitSteps d (source ++ [Parents.label d source a])) :
    KeyShiftView (scope.append a width unit)
      (keyHistory ++ [Keys.threshold d root keyHistory (Parents.label d source a)])
      (targetHistory ++ [Keys.threshold d root keyHistory (Parents.label d source a)]) := by
  refine ⟨Keys.history_append_threshold scope.sourceCoherent scope.sourceValid keys.correct
      keys.sourceLength scope.afterRoot (Nat.le_refl d) a,
    by simp only [List.length_append, List.length_cons, List.length_nil, keys.sourceLength],
    by simp only [List.length_append, List.length_cons, List.length_nil, keys.targetLength], ?_⟩
  intro p bound
  by_cases old : p < source.length
  · rw [Parents.point_append_old visible p target.length (by rw [scope.view.length]; exact old),
      List.getElem?_append_left (by rw [keys.targetLength]; exact scope.view.bounded p old),
      List.getElem?_append_left (by rw [keys.sourceLength]; exact old)]
    exact keys.history p old
  · have same : p = source.length := by
      simp only [List.length_append, List.length_cons, List.length_nil] at bound
      omega
    subst p
    rw [← scope.view.length, Parents.point_append_last, scope.view.length,
      ← keys.targetLength, List.getElem?_concat_length, ← keys.sourceLength, List.getElem?_concat_length]

mutual
  theorem copied_forest_key (d : Nat) (e : NumericalExpr)
      (source target : ParentContext) (visible history keyHistory targetHistory : List Nat)
      (root cap : Nat) (delta : List Nat) (phase : Nat)
      (scope : ShiftView d source target visible history root cap delta phase)
      (keys : KeyShiftView scope keyHistory targetHistory)
      (base : List Nat) (baseWidth : base.length = d) (legal : FiniteLegal d source e) :
      Keys.forest d (Parents.point visible root) (shift base cap delta phase) targetHistory
        (Parents.annotate d target (copied d root cap delta phase source history e)) =
      Keys.forest d root base keyHistory (Parents.annotate d source e) := by
    cases e with
    | nil => rfl
    | cons a hs tail =>
      have nextScope := scope.append a legal.1 legal.2.1
      have nextKeys := keys.append a legal.1 legal.2.1
      have headThreshold := keys.head_threshold a legal.1 legal.2.1
      have headNormalize := keys.head_normalize base a baseWidth legal.1
      have inner := copied_forests_key d hs _ _ _ _ _ _ root cap delta phase nextScope nextKeys
        base baseWidth (a[0]?.getD 0) legal.2.2.2.1
      have outer := copied_forest_key d tail _ _ _ _ _ _ root cap delta phase nextScope nextKeys
        base baseWidth legal.2.2.2.2
      rw [Parents.point_append_old visible root target.length
        (by rw [scope.view.length]; exact scope.afterRoot)] at inner outer
      rw [copied_cons d root cap delta phase source history (by rw [scope.historyLength]; exact scope.afterRoot)]
      simp only [Parents.annotate, Keys.forest, headThreshold, label_coordinates]
      rw [headNormalize]
      rw [inner, outer]

  theorem copied_forests_key (d : Nat) (hs : Forests (List Nat))
      (source target : ParentContext) (visible history keyHistory targetHistory : List Nat)
      (root cap : Nat) (delta : List Nat) (phase : Nat)
      (scope : ShiftView d source target visible history root cap delta phase)
      (keys : KeyShiftView scope keyHistory targetHistory)
      (base : List Nat) (baseWidth : base.length = d) (owner : Nat)
      (legal : FiniteLegalForests d source owner hs) :
      Keys.forests d (Parents.point visible root) (shift base cap delta phase) targetHistory
        (Parents.annotateForests d target (copiedForests d root cap delta phase source history hs)) =
      Keys.forests d root base keyHistory (Parents.annotateForests d source hs) := by
    cases hs with
    | nil => rfl
    | cons h hs =>
      have first := copied_forest_key d h source target visible history keyHistory targetHistory
        root cap delta phase scope keys base baseWidth legal.2.1
      have rest := copied_forests_key d hs source target visible history keyHistory targetHistory
        root cap delta phase scope keys base baseWidth owner legal.2.2
      simp only [copiedForests_cons, Parents.annotateForests, Keys.forests, first, rest]
end

/-- The two full-dimension key histories at the real rebase entry match,
even though the intervening target corridor has additional positions. -/
theorem partial_rebase_keyShiftView {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (unit : Parents.UnitSteps d context) (position : List Nat)
    (positionUnit : Parents.UnitSteps d (context ++ [Parents.label d context position]))
    {cut root : Nat} (positive : 0 < cut) (room : cut < d) (insideRoot : root < context.length)
    (path : Parents.Ancestor (context ++ [Parents.label d context position]) (cut - 1) root context.length)
    (same : (Parents.label d context position).parents[cut]?.join = Parents.parent context cut root)
    (width : (context[root]?.getD default).coordinates.length = d) :
    KeyShiftView (partial_rebase_shiftView coherent valid unit position positionUnit
      positive room insideRoot path same width)
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
  · have samePosition : p = root := by omega
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

/-- The complete key of the rebased root is exactly its original key.
All its nested forests are recomputed in the new context. This does not
claim that the keys of other columns in the copied block stay unchanged. -/
theorem partial_rebase_root_key {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (unit : Parents.UnitSteps d context) (position : List Nat)
    (positionUnit : Parents.UnitSteps d (context ++ [Parents.label d context position]))
    {cut root : Nat} (positive : 0 < cut) (room : cut < d) (insideRoot : root < context.length)
    (path : Parents.Ancestor (context ++ [Parents.label d context position]) (cut - 1) root context.length)
    (same : (Parents.label d context position).parents[cut]?.join = Parents.parent context cut root)
    (hs : Forests (List Nat))
    (width : (context[root]?.getD default).coordinates.length = d)
    (legal : FiniteLegalForests d (context.take (root + 1))
      ((context[root]?.getD default).coordinates[0]?.getD 0) hs) :
    let base := (context[root]?.getD default).coordinates
    let delta := (List.range cut).map (fun j => position[j]?.getD 0 - base[j]?.getD 0)
    let head := shift base cut delta 1
    Keys.ofColumn d context.length (Parents.label d context head)
      (Parents.annotateForests d (context ++ [Parents.label d context head])
        (copiedForests d root cut delta 1 (context.take (root + 1)) (List.replicate root 0 ++ [cut]) hs)) =
      Keys.ofColumn d root (context[root]?.getD default)
        (Parents.annotateForests d (context.take (root + 1)) hs) := by
  dsimp only
  have scope := partial_rebase_shiftView coherent valid unit position positionUnit
    positive room insideRoot path same width
  have keys := partial_rebase_keyShiftView coherent valid unit position positionUnit
    positive room insideRoot path same width
  have result := copied_forests_key d hs _ _ _ _ _ _ root cut _ 1 scope keys
    (context[root]?.getD default).coordinates width
    ((context[root]?.getD default).coordinates[0]?.getD 0) legal
  have point : Parents.point (List.range root ++ [context.length]) root = context.length := by
    simpa only [List.length_range] using Parents.point_append_last (List.range root) context.length
  simpa only [point, Keys.ofColumn, label_coordinates] using result

end BTnSSBMS.Source
