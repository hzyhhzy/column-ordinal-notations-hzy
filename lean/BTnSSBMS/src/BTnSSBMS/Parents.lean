import BTnSSBMS.Syntax

namespace BTnSSBMS

structure ParentLabel where
  coordinates : List Nat
  parents : List (Option Nat)
  deriving Repr, DecidableEq, Inhabited

abbrev ParentExpr := Expr ParentLabel
abbrev ParentContext := List ParentLabel

namespace Parents

/-- Search below the one-past-candidate index `cursor`.

The guard `q < p` makes this total even on malformed external annotations.
On contexts constructed by `annotate` each stored parent is strictly earlier;
the guard then accepts every source parent edge. It is not an iteration budget.
-/
def search (context : ParentContext) (row value : Nat) : (cursor : Nat) → Option Nat
  | 0 => none
  | p + 1 =>
    match context[p]? with
    | none => none
    | some a =>
      if a.coordinates[row]?.getD 0 < value then some p
      else match row with
      | 0 => search context 0 value p
      | j + 1 => match a.parents[j]?.join with
          | none => none
          | some q => if q < p then search context (j + 1) value (q + 1) else none
termination_by cursor => cursor

def rows (context : ParentContext) (coordinates : List Nat)
    (row : Nat) : Nat → Nat → List (Option Nat)
  | 0, _ => []
  | remaining + 1, cursor =>
    let p := search context row (coordinates[row]?.getD 0) cursor
    p :: rows context coordinates (row + 1) remaining (p.map (· + 1) |>.getD 0)

def label (d : Nat) (context : ParentContext) (coordinates : List Nat) : ParentLabel :=
  ⟨coordinates, rows context coordinates 0 d context.length⟩

theorem search_bounds (context : ParentContext) (row value cursor p : Nat)
    (found : search context row value cursor = some p) :
    p < cursor ∧ p < context.length := by
  induction cursor using Nat.strongRecOn with
  | ind cursor ih =>
    cases cursor with
    | zero => simp only [search] at found; contradiction
    | succ k =>
      rw [search] at found
      cases lookup : context[k]? with
      | none => simp only [lookup] at found; contradiction
      | some a =>
        have hk := (List.getElem?_eq_some_iff.mp lookup).choose
        by_cases smaller : a.coordinates[row]?.getD 0 < value
        · simp only [lookup, smaller, if_true, Option.some.injEq] at found
          subst p
          omega
        · simp only [lookup, smaller, if_false] at found
          cases row with
          | zero =>
            have h := ih k (by omega) found
            omega
          | succ j =>
            cases parent : a.parents[j]?.join with
            | none => simp only [parent] at found; contradiction
            | some q =>
              by_cases earlier : q < k
              · simp only [parent, earlier, if_true] at found
                have h := ih (q + 1) (by omega) found
                omega
              · simp only [parent, earlier, if_false] at found
                contradiction

theorem rows_bounds (context : ParentContext) (coordinates : List Nat)
    (row remaining cursor : Nat) :
    ∀ p, some p ∈ rows context coordinates row remaining cursor → p < context.length := by
  induction remaining generalizing row cursor with
  | zero => simp only [rows, List.not_mem_nil, false_implies, implies_true]
  | succ k ih =>
    intro p hp
    simp only [rows, List.mem_cons] at hp
    rcases hp with first | later
    · exact (search_bounds context row _ cursor p first.symm).2
    · exact ih (row + 1) _ p later

/-- Every stored parent of a newly annotated column is an earlier context index. -/
theorem label_parents_earlier (d : Nat) (context : ParentContext) (coordinates : List Nat)
    (p : Nat) (hp : some p ∈ (label d context coordinates).parents) :
    p < context.length := rows_bounds context coordinates 0 d context.length p hp

def ContextValid (context : ParentContext) : Prop :=
  ∀ (i : Nat) (a : ParentLabel), context[i]? = some a → ∀ p, some p ∈ a.parents → p < i

theorem empty_context_valid : ContextValid [] := by
  intro i a lookup
  simp at lookup

/-- Appending the actually computed annotation preserves the legality of
every stored pointer; this is not an assumed entering-context invariant. -/
theorem context_valid_append_label (d : Nat) (context : ParentContext)
    (valid : ContextValid context) (coordinates : List Nat) :
    ContextValid (context ++ [label d context coordinates]) := by
  intro i a lookup p member
  by_cases old : i < context.length
  · rw [List.getElem?_append_left old] at lookup
    exact valid i a lookup p member
  · have bound : i < (context ++ [label d context coordinates]).length :=
      (List.getElem?_eq_some_iff.mp lookup).choose
    rw [List.getElem?_append_right (by omega)] at lookup
    have same : i = context.length := by
      simp only [List.length_append, List.length_cons, List.length_nil] at bound
      omega
    subst i
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at lookup
    subst a
    exact label_parents_earlier d context coordinates p member

theorem search_follows_parent (context : ParentContext) (valid : ContextValid context)
    (j value k q : Nat) (a : ParentLabel) (lookup : context[k]? = some a)
    (not_smaller : ¬ a.coordinates[j + 1]?.getD 0 < value)
    (parent : a.parents[j]?.join = some q) :
    search context (j + 1) value (k + 1) = search context (j + 1) value (q + 1) := by
  have member : some q ∈ a.parents := by
    cases hp : a.parents[j]? with
    | none => simp [hp, Option.join] at parent
    | some p =>
      have same : p = some q := by simpa [hp, Option.join] using parent
      exact same ▸ List.mem_of_getElem? hp
  have earlier : q < k := valid k a lookup q member
  rw [search]
  simp only [lookup, not_smaller, if_false, parent, earlier, if_true]

mutual
  def annotate (d : Nat) (context : ParentContext) : NumericalExpr → ParentExpr
    | .nil => .nil
    | .cons a hs t =>
      let l := label d context a
      let context' := context ++ [l]
      .cons l (annotateForests d context' hs) (annotate d context' t)
  def annotateForests (d : Nat) (context : ParentContext) :
      Forests (List Nat) → Forests ParentLabel
    | .nil => .nil
    | .cons h hs => .cons (annotate d context h) (annotateForests d context hs)
end

mutual
  def Scoped (index : Nat) : ParentExpr → Prop
    | .nil => True
    | .cons a hs t =>
      (∀ p, some p ∈ a.parents → p < index) ∧
      ScopedForests (index + 1) hs ∧ Scoped (index + 1) t
  def ScopedForests (index : Nat) : Forests ParentLabel → Prop
    | .nil => True
    | .cons h hs => Scoped index h ∧ ScopedForests index hs
end

mutual
  theorem annotate_scoped (d : Nat) (context : ParentContext) (e : NumericalExpr) :
      Scoped context.length (annotate d context e) := by
    cases e with
    | nil => trivial
    | cons a hs t =>
      refine ⟨label_parents_earlier d context a, ?_, ?_⟩
      · simpa only [List.length_append, List.length_cons, List.length_nil] using
          annotateForests_scoped d (context ++ [label d context a]) hs
      · simpa only [List.length_append, List.length_cons, List.length_nil] using
          annotate_scoped d (context ++ [label d context a]) t
  theorem annotateForests_scoped (d : Nat) (context : ParentContext)
      (hs : Forests (List Nat)) : ScopedForests context.length (annotateForests d context hs) := by
    cases hs with
    | nil => trivial
    | cons h hs => exact ⟨annotate_scoped d context h, annotateForests_scoped d context hs⟩
end

theorem rows_length (context : ParentContext) (coordinates : List Nat)
    (row remaining cursor : Nat) :
    (rows context coordinates row remaining cursor).length = remaining := by
  induction remaining generalizing row cursor with
  | zero => rfl
  | succ k ih => simp only [rows, List.length_cons, ih]

theorem label_width (d : Nat) (context : ParentContext) (coordinates : List Nat) :
    (label d context coordinates).parents.length = d :=
  rows_length context coordinates 0 d context.length

mutual
  theorem annotate_erase (d : Nat) (context : ParentContext) (e : NumericalExpr) :
      (annotate d context e).map ParentLabel.coordinates = e := by
    cases e with
    | nil => rfl
    | cons a hs t =>
      simp only [annotate, Expr.map, label,
        annotateForests_erase, annotate_erase]
  theorem annotateForests_erase (d : Nat) (context : ParentContext)
      (hs : Forests (List Nat)) :
      (annotateForests d context hs).map ParentLabel.coordinates = hs := by
    cases hs with
    | nil => rfl
    | cons h hs =>
      simp only [annotateForests, Forests.map, annotate_erase, annotateForests_erase]
end

theorem annotate_nodes (d : Nat) (context : ParentContext) (e : NumericalExpr) :
    (annotate d context e).nodes = e.nodes := by
  rw [← Expr.map_nodes ParentLabel.coordinates, annotate_erase]

theorem annotate_slots (d : Nat) (context : ParentContext) (e : NumericalExpr) :
    (annotate d context e).slots = e.slots := by
  rw [← Expr.map_slots ParentLabel.coordinates, annotate_erase]

end Parents
end BTnSSBMS
