import BTnSSBMS.Order
import BTnSSBMS.BMS
import BTnSSBMS.SourceHead

/-!
The uniform raw ceiling for the concrete encoder. The hypothesis is just a
leading zero leaf. Standardness and order preservation are not inferred from
this raw comparison; those are different parts of the upper-bound theorem.
-/
namespace BTnSSBMS.Encoder

def initialState (d : Nat) : State d :=
  [⟨List.replicate (d + 2) 0, by simp,
    [⟨.nil, 0, some 0, none⟩]⟩]

theorem row_zero (d : Nat) : row d (fun _ => 0) 0 0 = List.replicate (d + 2) 0 := by
  simp only [row, List.map_const', List.length_range]
  exact List.replicate_append_replicate (n := d) (m := 2) (a := 0)

theorem representative_single (a : ParentLabel) (j : Nat) :
    representative [0] a j = none ∨ representative [0] a j = some 0 := by
  unfold representative
  cases h : a.parents[j]?.join with
  | none => exact Or.inl rfl
  | some p =>
    cases p with
    | zero => exact Or.inr rfl
    | succ p => exact Or.inl (by simp)

theorem initial_vector_le_one (d : Nat) (a : ParentLabel) (j : Nat) :
    vector (initialState d) [0] a j ≤ 1 := by
  rcases representative_single a j with no | yes
  · simp [vector, no]
  · simp [vector, yes, initialState]
    simp only [List.getElem?_replicate]
    split <;> rfl

theorem initial_frame (d : Nat) (a : ParentLabel) :
    ∃ z, frameAt (initialState d) (representative [0] a (d - 1)) = [z] ∧
      z.key = .nil ∧ z.height = 0 := by
  rcases representative_single a (d - 1) with no | yes
  · exact ⟨zeroBinding, by simp [frameAt, no, virtualFrame], rfl, rfl⟩
  · exact ⟨⟨.nil, 0, some 0, none⟩, by simp [frameAt, yes, initialState], rfl, rfl⟩

private theorem bounded_prefix_below (xs : List Nat) (bounded : ∀ x ∈ xs, x ≤ 1)
    (a b : List Nat) (tailBelow : listCompare compare a b = .lt) :
    listCompare compare (xs ++ a) (List.replicate xs.length 1 ++ b) = .lt := by
  induction xs with
  | nil => exact tailBelow
  | cons x xs ih =>
    have hx := bounded x (by simp)
    have rest := ih (fun y hy => bounded y (by simp [hy]))
    cases x with
    | zero => rfl
    | succ x =>
      have same : x = 0 := by omega
      subst x
      simpa only [List.cons_append, List.length_cons, List.replicate_succ, listCompare,
        natCompare_self] using rest

private theorem bounded_prefix_choice (xs : List Nat) (bounded : ∀ x ∈ xs, x ≤ 1) :
    listCompare compare (xs ++ [1, 1]) (List.replicate (xs.length + 2) 1) = .lt ∨
      xs = List.replicate xs.length 1 := by
  induction xs with
  | nil => exact Or.inr rfl
  | cons x xs ih =>
    have hx := bounded x (by simp)
    cases x with
    | zero => exact Or.inl rfl
    | succ x =>
      have same : x = 0 := by omega
      subst x
      rcases ih (fun y hy => bounded y (by simp [hy])) with strict | same
      · left
        simpa only [List.cons_append, List.length_cons, Nat.succ_add,
          List.replicate_succ, listCompare, natCompare_self] using strict
      · right
        simpa only [List.length_cons, List.replicate_succ] using congrArg (1 :: ·) same

private theorem zero_column_below (d : Nat) (col : List Nat) (rest : Matrix)
    (h : listCompare compare col (List.replicate (d + 2) 1) = .lt) :
    matrixCompare (List.replicate (d + 2) 0 :: col :: rest) (ceiling d) = .lt := by
  change listCompare (listCompare compare)
    (List.replicate (d + 2) 0 :: col :: rest)
    [List.replicate (d + 2) 0, List.replicate (d + 2) 1,
     List.replicate (d + 2) 2, List.replicate (d + 2) 3] = .lt
  simp only [listCompare, columnCompare_self, h]

private theorem raw_below_of_initial_emit {d : Nat} (state : State d)
    (u : Nat → Nat) (height tag : Nat) (frame : List Binding)
    (head : emit (initialState d) u height tag frame <+: state)
    (strict : listCompare compare (row d u height tag) (List.replicate (d + 2) 1) = .lt) :
    matrixCompare (matrix state) (ceiling d) = .lt := by
  obtain ⟨tail, same⟩ := head
  rw [← same]
  exact zero_column_below d (row d u height tag) (matrix tail) strict

private theorem raw_below_of_slot {d : Nat} (state : State d)
    (u : Nat → Nat) (below : List Binding)
    (ones : (List.range d).map u = List.replicate d 1)
    (head : emit (emit (emit (initialState d) u 1 1)
      (fun j => u j + 1) 2 2) (fun j => u j + 2) 2 0 below <+: state) :
    matrixCompare (matrix state) (ceiling d) = .lt := by
  have shifted (q : Nat) : (List.range d).map (fun j => u j + q) =
      List.replicate d (1 + q) := by
    calc
      _ = ((List.range d).map u).map (fun x => x + q) := by
        simp only [List.map_map, Function.comp_def]
      _ = _ := by rw [ones]; simp
  have oneRow : row d u 1 1 = List.replicate (d + 2) 1 := by
    simp only [row, ones]
    exact List.replicate_append_replicate (n := d) (m := 2) (a := 1)
  have twoRow : row d (fun j => u j + 1) 2 2 = List.replicate (d + 2) 2 := by
    simp only [row, shifted]
    exact List.replicate_append_replicate (n := d) (m := 2) (a := 2)
  have slotRow : row d (fun j => u j + 2) 2 0 = row d (fun _ => 3) 2 0 := by
    simp [row, shifted, List.map_const', List.length_range]
  obtain ⟨tail, same⟩ := head
  rw [← same]
  change matrixCompare
    (List.replicate (d + 2) 0 :: row d u 1 1 :: row d (fun j => u j + 1) 2 2 ::
      row d (fun j => u j + 2) 2 0 :: matrix tail) (ceiling d) = .lt
  rw [oneRow, twoRow, slotRow]
  exact four_column_head_below_ceiling d (matrix tail)

/-- After the leading zero leaf, every finite remaining annotated source
lies below the same raw ceiling, without assuming source block invariants. -/
theorem encode_initial_below_ceiling (d : Nat) (e : ParentExpr) :
    matrixCompare (matrix (encode d e [0] (initialState d))) (ceiling d) = .lt := by
  cases e with
  | nil =>
    change listCompare (listCompare compare) [List.replicate (d + 2) 0]
      [List.replicate (d + 2) 0, List.replicate (d + 2) 1,
       List.replicate (d + 2) 2, List.replicate (d + 2) 3] = .lt
    simp only [listCompare, columnCompare_self]
  | cons a hs t =>
    obtain ⟨z, frame, zeroKey, zeroHeight⟩ := initial_frame d a
    let u := vector (initialState d) [0] a
    have ub : ∀ x ∈ (List.range d).map u, x ≤ 1 := by
      intro x hx
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
      exact initial_vector_le_one d a j
    cases hs with
    | nil =>
      simp only [encode, Keys.leaf_key, frame, equal, smaller, List.find?_cons,
        zeroKey, Keys.compare, Forests.compare, List.filter_cons, List.filter_nil,
        beq_self_eq_true, zeroHeight]
      apply raw_below_of_initial_emit
      · exact encode_extends d t _ _
      · have h := bounded_prefix_below ((List.range d).map u) ub [0, 0] [1, 1] rfl
        have onesAppend : List.replicate d 1 ++ [1, 1] = List.replicate (d + 2) 1 :=
          List.replicate_append_replicate (n := d) (m := 2) (a := 1)
        simpa only [List.length_map, List.length_range, onesAppend, row, u] using h
    | cons h hs =>
      have keyNonempty : Keys.compare z.key (Keys.ofColumn d 1 a (.cons h hs)) = .lt := by
        simp [zeroKey, Keys.compare, Keys.ofColumn, Keys.forests, Forests.compare]
      simp only [encode, frame, equal, smaller, keyNonempty, List.find?_cons,
        List.find?_nil, List.filter_cons, List.filter_nil,
        beq_self_eq_true, if_true, base, List.getLast?_singleton,
        Option.getD_some, zeroHeight, Nat.zero_add, List.length_cons, List.length_nil]
      rcases bounded_prefix_choice ((List.range d).map u) ub with strict | ones
      · apply raw_below_of_initial_emit (frame := [])
        · exact (emit_extends ..).trans ((encodeForests_extends d (.cons h hs) _ _ _ _ _).trans
            ((emit_extends ..).trans (encode_extends d t _ _)))
        · simpa [row] using strict
      · have ho : (List.range d).map u = List.replicate d 1 := by simpa using ones
        apply raw_below_of_slot _ u [z] ho
        exact (encode_extends d h _ _).trans ((encodeForests_extends d hs _ _ _ _ _).trans
          ((emit_extends ..).trans (encode_extends d t _ _)))

theorem empty_representative (a : ParentLabel) (j : Nat) :
    representative [] a j = none := by
  unfold representative
  cases a.parents[j]?.join <;> rfl

theorem encode_first_leaf (d : Nat) (a : ParentLabel) (t : ParentExpr) :
    encode d (.cons a .nil t) [] [] = encode d t [0] (initialState d) := by
  have u : vector ([] : State d) [] a = (fun _ => 0) := by
    funext j
    simp [vector, empty_representative]
  simp only [encode, Keys.leaf_key, frameAt, empty_representative, Option.bind_none,
    virtualFrame, equal, smaller, zeroBinding, Keys.compare, Forests.compare,
    List.find?_cons, List.filter_cons, List.filter_nil, beq_self_eq_true, u]
  congr 1
  change [⟨row d (fun _ => 0) 0 0, _, _⟩] = initialState d
  simp only [row_zero, initialState]
  rfl

/-- This is a raw matrix comparison, not an assertion of BMS standardness.
It applies in particular to every source with its prescribed leading zero leaf. -/
theorem source_leading_leaf_below_ceiling (d : Nat) (a : List Nat) (t : NumericalExpr) :
    matrixCompare (fromSource d (.cons a .nil t)) (ceiling d) = .lt := by
  unfold fromSource
  simp only [Parents.annotate, Parents.annotateForests, encode_first_leaf]
  exact encode_initial_below_ceiling d _

theorem source_seed_below_ceiling (d k : Nat) :
    matrixCompare (fromSource d (seed d k)) (ceiling d) = .lt :=
  source_leading_leaf_below_ceiling d _ _

/-- Uniform raw bound on the actual finite-path source standard domain.
The proof does not yet establish that these matrices are standard BMS terms. -/
theorem standard_source_below_ceiling (d : Nat) (e : NumericalExpr)
    (standard : Source.Standard d e) :
    matrixCompare (fromSource d e) (ceiling d) = .lt := by
  rcases Source.standard_leading_zero d e standard with rfl | ⟨t, rfl⟩
  · rfl
  · exact source_leading_leaf_below_ceiling d _ t

end BTnSSBMS.Encoder
