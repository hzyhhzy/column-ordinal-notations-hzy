import OrdinalFormal.LRDStructure
import OrdinalFormal.ColumnRepresentation

/-!
# Canonical rows in the actual LRD domain

All executable operations preserve predicates on old rows, provided generated
packages satisfy the predicate. Specializing to normalized LRD rows proves
that every `LRD.Standard` graph uses the equality-correct row carrier.
This is an invariant theorem, not a well-ordering assertion.
-/

namespace OrdinalFormal.LRDCanonical

set_option autoImplicit false
set_option maxHeartbeats 600000

universe u
open Columns
variable {Row : Type u}

def ColRowsIn (P : Row → Prop) (c : Column Row) : Prop := ∀ e ∈ c, P e.row

def RowsIn (P : Row → Prop) (g : Graph Row) : Prop := ∀ c ∈ g, ColRowsIn P c

theorem colRowsIn_nil (P : Row → Prop) : ColRowsIn P [] := by
  intro e h
  simp at h

theorem colRowsIn_append (P : Row → Prop) {a b : Column Row}
    (ha : ColRowsIn P a) (hb : ColRowsIn P b) : ColRowsIn P (a ++ b) := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact ha e he
  · exact hb e he

theorem colRowsIn_normalize (P : Row → Prop) (cmp : Row → Row → Ordering)
    {c : Column Row} (hc : ColRowsIn P c) : ColRowsIn P (normalizeColumn cmp c) := by
  intro e he
  obtain ⟨s, hs, hrow, _, _⟩ := ColumnRepresentation.mem_normalizeColumn_source cmp he
  rw [hrow]
  exact hc s hs

theorem rowsIn_normalize (P : Row → Prop) (cmp : Row → Row → Ordering)
    {g : Graph Row} (hg : RowsIn P g) : RowsIn P (normalize cmp g) := by
  intro c hc
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc
  exact colRowsIn_normalize P cmp (hg s hs)

theorem rowsIn_lookup (P : Row → Prop) {g : Graph Row}
    (hg : RowsIn P g) (j : Nat) : ColRowsIn P (g[j]?.getD []) := by
  cases hj : g[j]? with
  | none => exact colRowsIn_nil P
  | some c => exact hg c (List.mem_of_getElem? hj)

theorem rowsIn_last (P : Row → Prop) {g : Graph Row}
    (hg : RowsIn P g) : ColRowsIn P (g.getLast?.getD []) := by
  cases hl : g.getLast? with
  | none => exact colRowsIn_nil P
  | some c => exact hg c (List.mem_of_getLast? hl)

theorem colRowsIn_move (P : Row → Prop) {c : Column Row}
    (hc : ColRowsIn P c) (cut len b : Nat) :
    ColRowsIn P (c.map (moveEntry cut len b)) := by
  intro e he
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp he
  exact hc s hs

theorem colRowsIn_ordinarySeam (P : Row → Prop) (cmp : Row → Row → Ordering)
    {last : Column Row} (hl : ColRowsIn P last) (e : Entry Row) (len b : Nat) :
    ColRowsIn P (ordinarySeam cmp last e len b) := by
  intro a ha
  obtain ⟨s, hs, hm⟩ := List.mem_flatMap.mp ha
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hm
  exact hl s hs

theorem colRowsIn_generatedSeam (P : Row → Prop) (package : Package Row)
    (hp : ∀ row b r, r ∈ package row b → P r) (e : Entry Row) (len b : Nat) :
    ColRowsIn P (generatedSeam package e len b) := by
  intro a ha
  obtain ⟨row, hr, hm⟩ := List.mem_flatMap.mp ha
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hm
  exact hp e.row b row hr

theorem rowsIn_block (P : Row → Prop) (cmp : Row → Row → Ordering)
    (package : Package Row) (hp : ∀ row b r, r ∈ package row b → P r)
    {g : Graph Row} (hg : RowsIn P g) (e : Entry Row) (b : Nat) :
    RowsIn P (block cmp package g e b) := by
  intro c hc
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
  apply colRowsIn_normalize P cmp
  apply colRowsIn_append P
  · exact colRowsIn_move P (rowsIn_lookup P hg (e.parent + i)) _ _ _
  · split
    · exact colRowsIn_append P
        (colRowsIn_ordinarySeam P cmp (rowsIn_last P hg) _ _ _)
        (colRowsIn_generatedSeam P package hp _ _ _)
    · exact colRowsIn_nil P

theorem rowsIn_expand (P : Row → Prop) (cmp : Row → Row → Ordering)
    (package : Package Row) (hp : ∀ row b r, r ∈ package row b → P r)
    {g : Graph Row} (hg : RowsIn P g) (n : Nat) :
    RowsIn P (expand cmp package g n) := by
  unfold expand
  split
  · intro c hc
    exact hg c (List.mem_of_mem_take hc)
  · rename_i e he
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hg c (List.mem_of_mem_take hc)
    · obtain ⟨b, _, hb⟩ := List.mem_flatMap.mp hc
      exact rowsIn_block P cmp package hp hg e b c hb

def Canonical (g : LRD.Diagram) : Prop := RowsIn (fun row => row.normal = row) g

theorem seed_canonical : Canonical LRD.seed := by
  simp [Canonical, RowsIn, ColRowsIn, LRD.seed, LRD.Row.normal]

theorem fs_canonical {g : LRD.Diagram} (hg : Canonical g) (n : Nat) :
    Canonical (LRD.fs g n) :=
  rowsIn_expand _ _ _ (fun _ _ _ h => LRDStructure.package_normal h) hg n

theorem standard_canonical {g : LRD.Diagram} (hg : LRD.Standard g) : Canonical g := by
  induction hg with
  | seed => exact seed_canonical
  | child h n ih => exact fs_canonical ih n

/-- Equality correctness needs only the predicate on the two actual lists,
not on every raw element of the ambient type. -/
theorem listCompare_eq_iff_on {α : Type u} (cmp : α → α → Ordering)
    (P : α → Prop) (hEq : ∀ a b, P a → P b → (cmp a b = .eq ↔ a = b))
    {as bs : List α} (ha : ∀ a ∈ as, P a) (hb : ∀ b ∈ bs, P b) :
    listCompare cmp as bs = .eq ↔ as = bs := by
  induction as generalizing bs with
  | nil => cases bs <;> simp [listCompare]
  | cons a as ih =>
      cases bs with
      | nil => simp [listCompare]
      | cons b bs =>
          have hhead := hEq a b (ha a List.mem_cons_self) (hb b List.mem_cons_self)
          have htail := ih (fun x hx => ha x (List.mem_cons_of_mem a hx))
            (fun x hx => hb x (List.mem_cons_of_mem b hx))
          simp only [listCompare, Comparison.thenCompare_eq_iff, hhead, htail,
            List.cons.injEq]

theorem entryCompare_eq_iff_canonical (a b : Entry LRD.Row)
    (ha : a.row.normal = a.row) (hb : b.row.normal = b.row) :
    entryCompare LRD.Row.cmp a b = .eq ↔ a = b := by
  cases a
  cases b
  simp only [entryCompare, Comparison.thenCompare_eq_iff, Nat.compare_eq_eq,
    LRDStructure.row_cmp_eq_iff_of_normal ha hb]
  simp [and_left_comm]

theorem columnCompare_eq_iff_canonical (a b : Column LRD.Row)
    (ha : ColRowsIn (fun r => r.normal = r) a)
    (hb : ColRowsIn (fun r => r.normal = r) b) :
    listCompare (entryCompare LRD.Row.cmp) a b = .eq ↔ a = b :=
  listCompare_eq_iff_on _ (fun e : Entry LRD.Row => e.row.normal = e.row)
    entryCompare_eq_iff_canonical ha hb

theorem cmp_eq_iff_canonical {a b : LRD.Diagram}
    (ha : Canonical a) (hb : Canonical b) : LRD.cmp a b = .eq ↔ a = b :=
  listCompare_eq_iff_on _ (ColRowsIn (fun r : LRD.Row => r.normal = r))
    columnCompare_eq_iff_canonical ha hb

theorem cmp_eq_iff_standard {a b : LRD.Diagram}
    (ha : LRD.Standard a) (hb : LRD.Standard b) : LRD.cmp a b = .eq ↔ a = b :=
  cmp_eq_iff_canonical (standard_canonical ha) (standard_canonical hb)

#print axioms rowsIn_expand
#print axioms standard_canonical
#print axioms cmp_eq_iff_standard

end OrdinalFormal.LRDCanonical
