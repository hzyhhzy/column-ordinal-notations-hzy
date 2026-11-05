import LaverLowerBounds.ParentShape

set_option autoImplicit false

namespace LaverLowerBounds.ParentBMS

def parent (s : Matrix) (row column : Nat) : Option Nat :=
  s[column]?.bind fun c => c[row]?

theorem parent_some_iff {s : Matrix} {row column p : Nat} :
    parent s row column = some p ↔ ∃ c, s[column]? = some c ∧ c[row]? = some p := by
  unfold parent
  cases hc : s[column]? with
  | none => simp
  | some c => simp

def Leftward (s : Matrix) : Prop := ∀ row column p, parent s row column = some p → p < column

theorem leftward_of_shape {s : Matrix} {h : Nat} (hs : Shape h 0 s) : Leftward s := by
  intro row column p hp
  obtain ⟨c, hc, hcp⟩ := parent_some_iff.mp hp
  have he := (hs column c hc).2 p (List.mem_of_getElem? hcp)
  omega

theorem parent_column_lt {s : Matrix} {row column p : Nat} (hp : parent s row column = some p) :
    column < s.length := by
  obtain ⟨c, hc, _⟩ := parent_some_iff.mp hp
  exact (List.getElem?_eq_some_iff.mp hc).1

theorem parent_append_left {s tail : Matrix} {row column : Nat} (hi : column < s.length) :
    parent (s ++ tail) row column = parent s row column := by
  simp only [parent, List.getElem?_append_left hi]

theorem parent_prefix {s t : Matrix} (hst : s.IsPrefix t) {row column : Nat} (hi : column < s.length) :
    parent t row column = parent s row column := by
  obtain ⟨tail, rfl⟩ := hst
  exact parent_append_left hi

inductive Ancestor (s : Matrix) (row : Nat) : Nat → Nat → Prop
  | direct {p i} : parent s row i = some p → Ancestor s row p i
  | step {p q i} : parent s row i = some q → Ancestor s row p q → Ancestor s row p i

namespace Ancestor

variable {s t : Matrix} {row p q i : Nat}

theorem lt (ha : Ancestor s row p i) (hs : Leftward s) : p < i := by
  induction ha with
  | direct he => exact hs _ _ _ he
  | step he _ ih => exact Nat.lt_trans ih (hs _ _ _ he)

theorem target_lt (ha : Ancestor s row p i) : i < s.length := by
  cases ha with
  | direct he => exact parent_column_lt he
  | step he _ => exact parent_column_lt he

theorem trans (hpq : Ancestor s row p q) (hqi : Ancestor s row q i) : Ancestor s row p i := by
  induction hqi with
  | direct he => exact .step he hpq
  | step he _ ih => exact .step he ih

theorem strip (ha : Ancestor s row p i) (he : parent s row i = some q) :
    p = q ∨ Ancestor s row p q := by
  cases ha with
  | direct hp =>
      have eq : p = q := by simpa only [hp, Option.some.injEq] using he
      exact Or.inl eq
  | step hq htail =>
      have eq := hq.symm.trans he
      have eq' := Option.some.inj eq
      exact Or.inr (eq' ▸ htail)

theorem to_prefix_extension (ha : Ancestor s row p i) (hst : s.IsPrefix t) : Ancestor t row p i := by
  induction ha with
  | direct he => exact .direct (by rw [parent_prefix hst (parent_column_lt he)]; exact he)
  | step he _ ih => exact .step (by rw [parent_prefix hst (parent_column_lt he)]; exact he) ih

theorem of_prefix (ha : Ancestor t row p i) (hst : s.IsPrefix t) (ht : Leftward t)
    (hi : i < s.length) : Ancestor s row p i := by
  induction ha with
  | direct he => exact .direct (by rw [parent_prefix hst hi] at he; exact he)
  | @step q i he htail ih =>
      have hq : q < s.length := Nat.lt_trans (ht _ _ _ he) hi
      exact .step (by rw [parent_prefix hst hi] at he; exact he) (ih hq)

theorem map_edges {f : Nat → Nat} (ha : Ancestor s row p i)
    (hf : ∀ q j, parent s row j = some q → Ancestor t row (f q) (f j)) :
    Ancestor t row (f p) (f i) := by
  induction ha with
  | direct he => exact hf _ _ he
  | step he _ ih => exact ih.trans (hf _ _ he)

end Ancestor

/-- Higher parents are ancestors in the preceding row. Lists already encode
the no-hole support convention. This is weaker than numeric BM4 canonicity. -/
def Nested (s : Matrix) : Prop :=
  ∀ row column p, parent s (row + 1) column = some p → Ancestor s row p column

theorem Ancestor.lower_one {s : Matrix} {row p i : Nat} (hn : Nested s)
    (ha : Ancestor s (row + 1) p i) : Ancestor s row p i := by
  induction ha with
  | direct he => exact hn _ _ _ he
  | step he _ ih => exact ih.trans (hn _ _ _ he)

theorem Ancestor.lower {s : Matrix} {lower upper p i : Nat} (hn : Nested s)
    (ha : Ancestor s upper p i) (hrow : lower ≤ upper) : Ancestor s lower p i := by
  induction upper with
  | zero =>
      have he : lower = 0 := by omega
      subst lower
      exact ha
  | succ upper ih =>
      by_cases he : lower = upper + 1
      · exact he ▸ ha
      · exact ih (ha.lower_one hn) (by omega)

theorem nested_prefix {s t : Matrix} (hst : s.IsPrefix t) (ht : Leftward t) (hn : Nested t) : Nested s := by
  intro row column p hp
  have hi := parent_column_lt hp
  have he : parent t (row + 1) column = some p := by rw [parent_prefix hst hi]; exact hp
  exact (hn row column p he).of_prefix hst ht hi

/-- A finite increasing column map preserving each source parent as a target
ancestor. The last source column is aligned with the last target column. -/
structure Cover (s t : Matrix) where
  column : Nat → Nat
  bounded : ∀ i, i < s.length → column i < t.length
  strict : ∀ i j, i < j → j < s.length → column i < column j
  edge : ∀ row p i, parent s row i = some p → Ancestor t row (column p) (column i)
  last : s ≠ [] → column (s.length - 1) = t.length - 1

namespace Cover

variable {s t u : Matrix}

theorem ancestry (f : Cover s t) {row p i : Nat} (ha : Ancestor s row p i) :
    Ancestor t row (f.column p) (f.column i) := ha.map_edges (f.edge row)

def identity (s : Matrix) : Cover s s where
  column := id
  bounded := fun _ hi => hi
  strict := fun _ _ hij _ => hij
  edge := fun _ _ _ he => .direct he
  last := fun _ => rfl

def comp (g : Cover t u) (f : Cover s t) : Cover s u where
  column i := g.column (f.column i)
  bounded i hi := g.bounded _ (f.bounded i hi)
  strict i j hij hj := g.strict _ _ (f.strict i j hij hj) (f.bounded j hj)
  edge row p i he := g.ancestry (f.edge row p i he)
  last hs := by
    have ht : t ≠ [] := by
      have hi : 0 < s.length := by cases s <;> simp_all
      have hb := f.bounded 0 hi
      intro he
      simp only [he, List.length_nil] at hb
      omega
    rw [f.last hs, g.last ht]

end Cover

#print axioms Ancestor.lower
#print axioms Cover.comp

end LaverLowerBounds.ParentBMS
