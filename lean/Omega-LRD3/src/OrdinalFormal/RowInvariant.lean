import OrdinalFormal.ExpansionValidity

/-!
Actual expansion preserves predicates on row labels, provided its generated
package preserves them. Sorting, root closure and moving coordinates never
introduce a different row. This is a syntactic invariant, not accessibility.
-/

namespace OrdinalFormal.RowInvariant
open Columns
set_option autoImplicit false
set_option maxHeartbeats 500000
universe u
variable {Row : Type u}

def AllRows (P : Row → Prop) (g : Graph Row) : Prop :=
  ∀ c ∈ g, ∀ e ∈ c, P e.row

theorem getD_rows {P : Row → Prop} {g : Graph Row} (hg : AllRows P g)
    (j : Nat) : ∀ e ∈ g[j]?.getD [], P e.row := by
  cases h : g[j]? with
  | none => simp
  | some c =>
    simp only [Option.getD_some]
    exact hg c (List.mem_of_getElem? h)

theorem last_rows {P : Row → Prop} {g : Graph Row} (hg : AllRows P g) :
    ∀ e ∈ g.getLast?.getD [], P e.row := by
  rw [List.getLast?_eq_getElem?]
  exact getD_rows hg _

theorem take {P : Row → Prop} {g : Graph Row} (hg : AllRows P g) (n : Nat) :
    AllRows P (g.take n) := by
  intro c hc
  exact hg c (List.mem_of_mem_take hc)

theorem normalizeColumn_rows (cmp : Row → Row → Ordering) (P : Row → Prop)
    (c : Column Row) (hc : ∀ e ∈ c, P e.row) :
    ∀ e ∈ normalizeColumn cmp c, P e.row :=
  ExpansionValidity.normalizeColumn_preserves cmp (fun e => P e.row) c hc
    (fun _ h _ _ => h)

theorem ordinary_rows (cmp : Row → Row → Ordering) (P : Row → Prop)
    (last : Column Row) (hl : ∀ a ∈ last, P a.row)
    (e : Entry Row) (len b : Nat) :
    ∀ a ∈ ordinarySeam cmp last e len b, P a.row := by
  intro a ha
  obtain ⟨s, hs, hm⟩ := List.mem_flatMap.mp ha
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hm
  exact hl s hs

theorem generated_rows (package : Package Row) (P : Row → Prop)
    (e : Entry Row) (len b : Nat)
    (hp : ∀ row ∈ package e.row b, P row) :
    ∀ a ∈ generatedSeam package e len b, P a.row := by
  intro a ha
  obtain ⟨row, hr, hm⟩ := List.mem_flatMap.mp ha
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hm
  exact hp row hr

theorem block_rows (cmp : Row → Row → Ordering) (package : Package Row)
    (P : Row → Prop) (g : Graph Row) (hg : AllRows P g)
    (e : Entry Row) (b : Nat) (hp : ∀ row ∈ package e.row b, P row) :
    AllRows P (block cmp package g e b) := by
  intro c hc a ha
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
  apply normalizeColumn_rows cmp P _ ?_ a ha
  intro s hs
  rcases List.mem_append.mp hs with hs | hs
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
    exact getD_rows hg _ t ht
  · split at hs
    · rcases List.mem_append.mp hs with hs | hs
      · exact ordinary_rows cmp P _ (last_rows hg) _ _ _ s hs
      · exact generated_rows package P e _ b hp s hs
    · simp at hs

/-- Only packages for the actual controller need to obey the invariant. -/
theorem expand_rows_of_control (cmp : Row → Row → Ordering) (package : Package Row)
    (P : Row → Prop) (g : Graph Row) (hg : AllRows P g)
    (hp : ∀ e, control cmp (g.getLast?.getD []) = some e →
      ∀ b row, row ∈ package e.row b → P row) (n : Nat) :
    AllRows P (expand cmp package g n) := by
  unfold expand
  split
  · exact take hg _
  · rename_i e he
    intro c hc a ha
    rcases List.mem_append.mp hc with hc | hc
    · exact take hg _ c hc a ha
    · obtain ⟨b, _, hb⟩ := List.mem_flatMap.mp hc
      exact block_rows cmp package P g hg e b (hp e he b) c hb a ha

theorem expand_rows (cmp : Row → Row → Ordering) (package : Package Row)
    (P : Row → Prop) (g : Graph Row) (hg : AllRows P g)
    (hp : ∀ high, P high → ∀ b low, low ∈ package high b → P low) (n : Nat) :
    AllRows P (expand cmp package g n) := by
  apply expand_rows_of_control cmp package P g hg ?_ n
  intro e he b row hr
  exact hp e.row (last_rows hg e (ExpansionValidity.control_mem cmp he)) b row hr

#print axioms expand_rows_of_control
#print axioms expand_rows

end OrdinalFormal.RowInvariant
