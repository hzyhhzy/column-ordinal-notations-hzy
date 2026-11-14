import LaverLowerBounds.NumericFGH

set_option autoImplicit false
namespace LaverLowerBounds.ParentBMS

theorem FastRun.split_prefix {stack : List Matrix} {x y : Nat} (run : FastRun stack x y) :
    ∀ front tail, stack = front ++ tail → ∃ z, FastRun front x z ∧ FastRun tail z y := by
  induction run with
  | done x =>
    intro front tail he
    have hlen := congrArg List.length he
    simp only [List.length_nil, List.length_append] at hlen
    have hf : front = [] := List.eq_nil_of_length_eq_zero (by omega)
    have ht : tail = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst front; subst tail
    exact ⟨x, .done x, .done x⟩
  | @zero rest x y run ih =>
    intro front tail he
    cases front with
    | nil =>
      refine ⟨x, .done x, ?_⟩
      have he' : [] :: rest = tail := by simpa using he
      rw [← he']
      exact .zero run
    | cons first front =>
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨z, hf, ht⟩ := ih front tail he.2
      have hfirst := he.1
      subst first
      exact ⟨z, .zero hf, ht⟩
  | @successor s rest x y run ih =>
    intro front tail he
    cases front with
    | nil =>
      refine ⟨x, .done x, ?_⟩
      have he' : (s ++ [[]]) :: rest = tail := by simpa using he
      rw [← he']
      exact .successor run
    | cons first front =>
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨z, hf, ht⟩ := ih (List.replicate (x + 1) s ++ front) tail (by rw [he.2, List.append_assoc])
      have hfirst := he.1
      subst first
      exact ⟨z, .successor hf, ht⟩
  | @limit s rest x y hs run ih =>
    intro front tail he
    cases front with
    | nil =>
      refine ⟨x, .done x, ?_⟩
      have he' : s :: rest = tail := by simpa using he
      rw [← he']
      exact .limit hs run
    | cons first front =>
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨z, hf, ht⟩ := ih (expand s x :: front) tail (by rw [he.2]; rfl)
      have hfirst := he.1
      subst first
      exact ⟨z, .limit hs hf, ht⟩

theorem zeros_fast (n x : Nat) : FastRun (List.replicate n []) x (x + n) := by
  induction n generalizing x with
  | zero => simpa using FastRun.done x
  | succ n ih =>
    simpa only [List.replicate_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      FastRun.zero (ih (x + 1))

theorem one_fast (x : Nat) : FastEval [[]] x (2 * x + 1) := by
  have he : FastRun [[[]]] x (x + (x + 1)) :=
    FastRun.successor (s := []) (rest := [])
      (by simpa only [List.append_nil] using zeros_fast (x + 1) x)
  simpa only [FastEval, Nat.two_mul, Nat.add_assoc] using he

/-- Two finite successor postprocessors amplify the OUTPUT, without relying
on monotonicity of FGH in the ordinal or in the input. -/
theorem postprocess_extract {s : Matrix} {x z : Nat} (run : FastRun [s, [[]], [[]]] x z) :
    ∃ y, FastEval s x y ∧ z = 4 * y + 3 := by
  obtain ⟨y, hy, tail⟩ := run.split_prefix [s] [[[]], [[]]] rfl
  obtain ⟨v, hv, last⟩ := tail.split_prefix [[[]]] [[[]]] rfl
  have vval := FastEval.unique hv (one_fast y)
  have zval := FastEval.unique last (one_fast v)
  exact ⟨y, hy, by omega⟩

def postCode (r : Nat) : Matrix := [[], [0], [], [2], [], [4], List.replicate r 5]

theorem postCode_eq {r : Nat} (hr : 1 ≤ r) :
    postCode r = stackCode [seed r, [[]], [[]]] := by
  have ne : List.replicate r (0 : Nat) ≠ [] := by
    intro he
    have := congrArg List.length he
    simp at this
    omega
  simp [postCode, stackCode, liftW, seed, raiseColumn, ne, attached, translated]

theorem constant_columns_nested {s : Matrix}
    (hs : ∀ c ∈ s, ∃ n p, c = List.replicate n p) : Nested s := by
  intro q i p hp
  obtain ⟨c, hc, hcp⟩ := parent_some_iff.mp hp
  obtain ⟨n, a, rfl⟩ := hs c (List.mem_of_getElem? hc)
  have hq : q + 1 < n := by
    have hh := (List.getElem?_eq_some_iff.mp hcp).1
    simpa using hh
  have he : a = p := by simpa [List.getElem?_replicate, hq] using hcp
  subst p
  apply Ancestor.direct
  exact parent_some_iff.mpr ⟨List.replicate n a, hc, by simp [show q < n by omega]⟩

theorem postCode_nested (r : Nat) : Nested (postCode r) := by
  apply constant_columns_nested
  intro c hc
  simp only [postCode, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 0, rfl⟩
  · exact ⟨1, 0, rfl⟩
  · exact ⟨0, 0, rfl⟩
  · exact ⟨1, 2, rfl⟩
  · exact ⟨0, 0, rfl⟩
  · exact ⟨1, 4, rfl⟩
  · exact ⟨r, 5, rfl⟩

theorem postCode_shape {r : Nat} (hr : 1 ≤ r) : Shape r 0 (postCode r) := by
  intro i c hc
  have hi : i < 7 := by
    have := (List.getElem?_eq_some_iff.mp hc).1
    simpa [postCode] using this
  match i with
  | 0 | 2 | 4 => simp [postCode] at hc; subst c; simp
  | 1 => simp [postCode] at hc; subst c; simp; omega
  | 3 => simp [postCode] at hc; subst c; simp; omega
  | 5 => simp [postCode] at hc; subst c; simp; omega
  | 6 =>
    have he : c = List.replicate r 5 := by simpa [postCode] using hc.symm
    subst c
    constructor
    · simp
    · intro p hp
      have he : p = 5 := (List.mem_replicate.mp hp).2
      omega
  | n + 7 => omega

#print axioms postprocess_extract
#print axioms postCode_eq
#print axioms postCode_shape
end LaverLowerBounds.ParentBMS
