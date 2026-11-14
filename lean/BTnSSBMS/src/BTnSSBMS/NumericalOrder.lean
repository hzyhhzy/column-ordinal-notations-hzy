import BTnSSBMS.SourceCopyHead
import BTnSSBMS.KeyLevels

/-!
Strict comparison at the first different numerical coordinate. The
selected source parents lie on a common record chain; their strictly
ordered representatives cannot collapse under the actual scoped view.
This does not yet handle equal numerical heads with different forests.
-/
namespace BTnSSBMS.Parents

theorem label_unit_value {d : Nat} {context : ParentContext} (a : List Nat)
    (unit : UnitSteps d (context ++ [label d context a])) {row : Nat} (room : row < d) :
    a[row]?.getD 0 =
      (((label d context a).parents[row]?.join).map fun p => reading context row p + 1).getD 0 := by
  have value := unit context.length (by simp) row room
  rw [reading_append_label, append_label_parent] at value
  cases edge : (label d context a).parents[row]?.join with
  | none => simpa only [edge, Option.map_none, Option.getD_none] using value
  | some p =>
    have inside := label_parent_bound d context a row p edge
    simpa only [edge, Option.map_some, Option.getD_some,
      ← reading_prefix (List.prefix_append context [label d context a]) row p inside] using value

/-- At a first numerical difference, the two selected parents belong to
one row record chain. The conclusion is about computed parents, not an
assumed monotonicity of the input coordinate labels. -/
theorem label_parents_comparable {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context)
    (a b : List Nat) {row p q : Nat} (room : row < d)
    (common : ∀ j, j < row → a[j]?.getD 0 = b[j]?.getD 0)
    (left : (label d context a).parents[row]?.join = some p)
    (right : (label d context b).parents[row]?.join = some q) :
    Ancestor context row p q ∨ Ancestor context row q p := by
  cases row with
  | zero =>
    exact (label_zero_parent_frontier coherent valid room a left).comparable
      (label_zero_parent_frontier coherent valid room b right)
  | succ row =>
    obtain ⟨u, first, pathA⟩ := label_higher_parent_frontier coherent valid a room left
    obtain ⟨v, second, pathB⟩ := label_higher_parent_frontier coherent valid b room right
    have same := label_parents_congr_through d context a b row (by omega)
      (fun j hj => common j (by omega))
    rw [first, second] at same
    have equal : u = v := Option.some.inj same
    subst v
    exact pathA.comparable pathB

theorem label_parents_strict_at_difference {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context)
    (a b : List Nat)
    (leftUnit : UnitSteps d (context ++ [label d context a]))
    (rightUnit : UnitSteps d (context ++ [label d context b]))
    {row p q : Nat} (room : row < d)
    (common : ∀ j, j < row → a[j]?.getD 0 = b[j]?.getD 0)
    (strict : a[row]?.getD 0 < b[row]?.getD 0)
    (left : (label d context a).parents[row]?.join = some p)
    (right : (label d context b).parents[row]?.join = some q) :
    Ancestor context row p q ∧ p < q := by
  have leftValue := label_unit_value a leftUnit room
  have rightValue := label_unit_value b rightUnit room
  simp only [left, right, Option.map_some, Option.getD_some] at leftValue rightValue
  have lower : reading context row p < reading context row q := by omega
  have different : p ≠ q := by intro same; simp only [same] at lower; omega
  rcases label_parents_comparable coherent valid a b room common left right with path | reverse
  · exact ⟨path, by have before := path.le valid; omega⟩
  · have impossible := reverse.reading_le coherent
    omega

/-- Strictness uses the proved ordering of position representatives in
NumericalView. An ancestry-preserving map alone could identify them. -/
theorem representedValue_strict_at_difference {d rows : Nat}
    {source target : ParentContext} {visible : List Nat}
    (sourceCoherent : Coherent d source) (sourceValid : ContextValid source)
    (targetCoherent : Coherent rows target) (view : NumericalView d source target visible)
    (a b : List Nat)
    (leftUnit : UnitSteps d (source ++ [label d source a]))
    (rightUnit : UnitSteps d (source ++ [label d source b]))
    {row : Nat} (room : row < d)
    (common : ∀ j, j < row → a[j]?.getD 0 = b[j]?.getD 0)
    (strict : a[row]?.getD 0 < b[row]?.getD 0) :
    representedValue target visible (label d source a) row <
      representedValue target visible (label d source b) row := by
  have rightValue := label_unit_value b rightUnit room
  cases right : (label d source b).parents[row]?.join with
  | none =>
    simp only [right, Option.map_none, Option.getD_none] at rightValue
    omega
  | some q =>
    cases left : (label d source a).parents[row]?.join with
    | none => simp only [representedValue, left, right, Option.map_none, Option.map_some,
        Option.getD_none, Option.getD_some]; omega
    | some p =>
      obtain ⟨path, earlier⟩ := label_parents_strict_at_difference sourceCoherent sourceValid
        a b leftUnit rightUnit room common strict left right
      have pBound := label_parent_bound d source a row p left
      have qBound := label_parent_bound d source b row q right
      have lifted := view.lift row room p q pBound qBound path
      have separated := view.increasing p q earlier qBound
      have lower := lifted.reading_lt targetCoherent (by omega)
      simpa only [representedValue, left, right, Option.map_some, Option.getD_some,
        Nat.add_lt_add_iff_right] using lower

end BTnSSBMS.Parents

namespace BTnSSBMS

theorem columnCompare_lt_exists_difference (a b : List Nat) (width : a.length = b.length)
    (lower : listCompare compare a b = .lt) :
    ∃ j, j < a.length ∧ (∀ i, i < j → a[i]?.getD 0 = b[i]?.getD 0) ∧
      a[j]?.getD 0 < b[j]?.getD 0 := by
  induction a generalizing b with
  | nil =>
    have empty : b = [] := by simpa using width.symm
    subst b
    simp [listCompare] at lower
  | cons x xs ih =>
    cases b with
    | nil => simp at width
    | cons y ys =>
      cases head : compare x y with
      | lt =>
        exact ⟨0, by simp, by intro i hi; omega, by
          simpa only [List.getElem?_cons_zero, Option.getD_some] using Nat.compare_eq_lt.mp head⟩
      | gt => simp [listCompare, head] at lower
      | eq =>
        have same : x = y := Nat.compare_eq_eq.mp head
        have tails : listCompare compare xs ys = .lt := by simpa only [listCompare, head] using lower
        obtain ⟨j, room, common, strict⟩ := ih ys (by simpa using width) tails
        refine ⟨j + 1, by simpa using room, ?_, ?_⟩
        · intro i before
          cases i with
          | zero => simpa only [List.getElem?_cons_zero, Option.getD_some] using same
          | succ i => simpa only [List.getElem?_cons_succ] using common i (by omega)
        · simpa only [List.getElem?_cons_succ] using strict

end BTnSSBMS

namespace BTnSSBMS.Encoder

theorem vector_first_difference {d : Nat} {source : ParentContext} {visible : List Nat}
    (state : State d) (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (a b : List Nat)
    (leftUnit : Parents.UnitSteps d (source ++ [Parents.label d source a]))
    (rightUnit : Parents.UnitSteps d (source ++ [Parents.label d source b]))
    {j : Nat} (room : j < d)
    (common : ∀ i, i < j → a[i]?.getD 0 = b[i]?.getD 0)
    (strict : a[j]?.getD 0 < b[j]?.getD 0) :
    (∀ i, i < j → vector state visible (Parents.label d source a) i =
      vector state visible (Parents.label d source b) i) ∧
    vector state visible (Parents.label d source a) j <
      vector state visible (Parents.label d source b) j := by
  constructor
  · intro i before
    simp only [vector, representative,
      Parents.label_parents_congr_through d source a b i (by omega)
        (fun k hk => common k (by omega))]
  · rw [vector_eq_represented view, vector_eq_represented view]
    exact Parents.representedValue_strict_at_difference coherent valid
      (BMS.parentTable_coherent (d + 2) (matrix state)) view a b leftUnit rightUnit room common strict

theorem head_row_lt_at_numerical_difference {d : Nat} {source : ParentContext} {visible : List Nat}
    (state : State d) (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (a b : List Nat)
    (leftUnit : Parents.UnitSteps d (source ++ [Parents.label d source a]))
    (rightUnit : Parents.UnitSteps d (source ++ [Parents.label d source b]))
    {j : Nat} (room : j < d)
    (common : ∀ i, i < j → a[i]?.getD 0 = b[i]?.getD 0)
    (strict : a[j]?.getD 0 < b[j]?.getD 0) (ha ta hb tb : Nat) :
    listCompare compare (row d (vector state visible (Parents.label d source a)) ha ta)
      (row d (vector state visible (Parents.label d source b)) hb tb) = .lt := by
  obtain ⟨prior, lower⟩ := vector_first_difference state coherent valid view a b
    leftUnit rightUnit room common strict
  apply columnCompare_lt_at _ _ j (by rw [row_width]; omega) (by rw [row_width]; omega)
  · intro i before
    rw [row_numerical_reading d _ ha ta i (by omega), row_numerical_reading d _ hb tb i (by omega)]
    exact prior i before
  · rw [row_numerical_reading d _ ha ta j room, row_numerical_reading d _ hb tb j room]
    exact lower

/-- Every branch of the actual mutual encoder retains its first emitted
numerical head, even when it subsequently expands arbitrarily many forests. -/
theorem encode_cons_first_row (d : Nat) (a : ParentLabel) (hs : Forests ParentLabel)
    (tail : ParentExpr) (visible : List Nat) (state : State d) :
    ∃ height tag rest,
      height = firstHeight (frameAt state (representative visible a (d - 1)))
        (Keys.ofColumn d visible.length a hs) ∧
      matrix (encode d (.cons a hs tail) visible state) =
      matrix state ++ row d (vector state visible a) height tag :: rest := by
  simp only [encode]
  split
  next bound same =>
    obtain ⟨extra, extension⟩ := encode_extends d tail (visible ++ [state.length])
      (emit state (vector state visible a) bound.height 0
        (smaller (frameAt state (representative visible a (d - 1))) (Keys.ofColumn d visible.length a hs) ++
          [{bound with latest := some state.length}]))
    refine ⟨bound.height, 0, matrix extra, by simp only [firstHeight, same], ?_⟩
    rw [← extension]
    simp only [matrix, List.map_append, emit, List.map_cons,
      List.append_assoc, List.cons_append, List.nil_append]
  next fresh =>
    let u := vector state visible a
    let key := Keys.ofColumn d visible.length a hs
    let below := smaller (frameAt state (representative visible a (d - 1))) key
    let c := (base below).height
    let first := emit state u (c + 1) 1 []
    let guarded := emit first (fun j => u j + 1) (c + 2) 2 []
    let forests := encodeForests d hs visible u c below guarded
    let closed := emit forests (fun j => u j + 1) (c + 2) 0
      (below ++ [⟨key, c + 2, some forests.length, some state.length⟩])
    have initial : first <+: encode d tail (visible ++ [forests.length]) closed :=
      (emit_extends first _ _ _ _).trans
        ((encodeForests_extends d hs visible u c below guarded).trans
          ((emit_extends forests _ _ _ _).trans (encode_extends d tail _ closed)))
    obtain ⟨extra, extension⟩ := initial
    refine ⟨c + 1, 1, matrix extra, by simp only [firstHeight, fresh]; rfl, ?_⟩
    change matrix (encode d tail (visible ++ [forests.length]) closed) = _
    rw [← extension]
    simp only [first, u, matrix, emit, List.map_append, List.map_cons,
      List.append_assoc, List.cons_append, List.nil_append]

/-- The full source-to-matrix comparison when the first columns differ
numerically. Attached lists and all continuation columns are unrestricted:
the decision is already strict in the first emitted row. -/
theorem encode_lt_of_numerical_heads {d : Nat} {source : ParentContext} {visible : List Nat}
    (state : State d) (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (a b : List Nat) (ha : a.length = d) (hb : b.length = d)
    (leftUnit : Parents.UnitSteps d (source ++ [Parents.label d source a]))
    (rightUnit : Parents.UnitSteps d (source ++ [Parents.label d source b]))
    (lower : listCompare compare a b = .lt)
    (hs ks : Forests (List Nat)) (tail rest : NumericalExpr) :
    matrixCompare
      (matrix (encode d (Parents.annotate d source (.cons a hs tail)) visible state))
      (matrix (encode d (Parents.annotate d source (.cons b ks rest)) visible state)) = .lt := by
  obtain ⟨j, inside, common, strict⟩ := columnCompare_lt_exists_difference a b (ha.trans hb.symm) lower
  obtain ⟨heightA, tagA, extraA, _, shapeA⟩ := encode_cons_first_row d (Parents.label d source a)
    (Parents.annotateForests d (source ++ [Parents.label d source a]) hs)
    (Parents.annotate d (source ++ [Parents.label d source a]) tail) visible state
  obtain ⟨heightB, tagB, extraB, _, shapeB⟩ := encode_cons_first_row d (Parents.label d source b)
    (Parents.annotateForests d (source ++ [Parents.label d source b]) ks)
    (Parents.annotate d (source ++ [Parents.label d source b]) rest) visible state
  have first := head_row_lt_at_numerical_difference state coherent valid view a b
    leftUnit rightUnit (by omega : j < d) common strict heightA tagA heightB tagB
  simp only [Parents.annotate, shapeA, shapeB, matrixCompare,
    listCompare_common_prefix (listCompare compare) columnCompare_self, listCompare, first]

end BTnSSBMS.Encoder
