import OrdinalFormal.LRD
import OrdinalFormal.Comparison

/-!
# Normalized LRD row structure

Raw polynomial coefficient lists can differ only by trailing zeros. Thus the
row comparator detects equality of normal forms, not equality of raw syntax.
These lemmas supply that distinction explicitly; none asserts well-ordering.
-/

namespace OrdinalFormal.LRDStructure

set_option autoImplicit false
set_option maxHeartbeats 600000

open LRD

theorem dropWhile_idempotent {α : Type} (p : α → Bool) (xs : List α) :
    (xs.dropWhile p).dropWhile p = xs.dropWhile p := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      by_cases h : p a = true
      · simpa [List.dropWhile_cons, h] using ih
      · simp [h]

@[simp] theorem trim_idempotent (cs : List Nat) : trim (trim cs) = trim cs := by
  simp only [trim, List.reverse_reverse, dropWhile_idempotent]

@[simp] theorem normal_idempotent (a : Row) : a.normal.normal = a.normal := by
  cases a <;> simp [Row.normal]

theorem row_cmp_eq_iff_normal_eq (a b : Row) :
    Row.cmp a b = .eq ↔ a.normal = b.normal := by
  cases a with
  | limit => cases b <;> simp [Row.cmp, Row.normal]
  | poly as =>
      cases b with
      | limit => simp [Row.cmp, Row.normal]
      | poly bs =>
          simp only [Row.cmp, Row.normal, Comparison.thenCompare_eq_iff,
            Nat.compare_eq_eq,
            Comparison.listCompare_eq_iff compare (fun _ _ => Nat.compare_eq_eq),
            List.reverse_inj, Row.poly.injEq]
          exact ⟨fun h => h.2, fun h => ⟨congrArg List.length h, h⟩⟩

theorem row_cmp_eq_iff_of_normal {a b : Row}
    (ha : a.normal = a) (hb : b.normal = b) :
    Row.cmp a b = .eq ↔ a = b := by
  rw [row_cmp_eq_iff_normal_eq, ha, hb]

@[simp] theorem row_cmp_normal (a b : Row) :
    Row.cmp a.normal b.normal = Row.cmp a b := by
  cases a <;> cases b <;> simp [Row.normal, Row.cmp]

@[simp] theorem trim_append_one (cs : List Nat) : trim (cs ++ [1]) = cs ++ [1] := by
  simp [trim, List.reverse_append]

@[simp] theorem approx_normal (a : Row) (t : Nat) :
    (a.approx t).normal = a.approx t := by
  cases a <;> simp [Row.approx, Row.normal]

theorem package_normal {a : Row} {b : Nat} {r : Row} (h : r ∈ package a b) :
    r.normal = r := by
  unfold package at h
  split at h
  · simp at h
  · simp only [List.mem_cons, List.mem_map] at h
    rcases h with h | ⟨t, _, h⟩
    · subst r
      rfl
    · subst r
      exact approx_normal a t

theorem poly_cmp_lt_iff (as bs : List Nat) :
    Row.cmp (.poly as) (.poly bs) = .lt ↔
      (trim as).length < (trim bs).length ∨
      ((trim as).length = (trim bs).length ∧
        Columns.listCompare compare (trim as).reverse (trim bs).reverse = .lt) := by
  simp only [Row.cmp, Comparison.thenCompare_lt_iff, Nat.compare_eq_lt,
    Nat.compare_eq_eq]

theorem poly_cmp_lt_trans {as bs cs : List Nat}
    (hab : Row.cmp (.poly as) (.poly bs) = .lt)
    (hbc : Row.cmp (.poly bs) (.poly cs) = .lt) :
    Row.cmp (.poly as) (.poly cs) = .lt := by
  apply (poly_cmp_lt_iff as cs).mpr
  rcases (poly_cmp_lt_iff as bs).mp hab with hab | ⟨hab, hab'⟩
  · rcases (poly_cmp_lt_iff bs cs).mp hbc with hbc | ⟨hbc, _⟩
    · exact Or.inl (Nat.lt_trans hab hbc)
    · exact Or.inl (by omega)
  · rcases (poly_cmp_lt_iff bs cs).mp hbc with hbc | ⟨hbc, hbc'⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨hab.trans hbc,
        Comparison.listCompare_lt_trans compare (fun _ _ => Nat.compare_eq_eq)
          Comparison.nat_compare_lt_trans hab' hbc'⟩

/-- Strict transitivity is valid even on raw rows, despite equality identifying
different trailing-zero presentations. -/
theorem row_cmp_lt_trans {a b c : Row}
    (hab : Row.cmp a b = .lt) (hbc : Row.cmp b c = .lt) :
    Row.cmp a c = .lt := by
  cases a with
  | limit => cases b <;> simp [Row.cmp] at hab
  | poly as =>
      cases b with
      | limit => cases c <;> simp [Row.cmp] at hbc
      | poly bs =>
          cases c with
          | limit => rfl
          | poly cs => exact poly_cmp_lt_trans hab hbc

theorem row_cmp_lt_irrefl (a : Row) : Row.cmp a a ≠ .lt := by
  rw [(row_cmp_eq_iff_normal_eq a a).mpr rfl]
  decide

/-- The actual equality-correct carrier for the generic comparison interfaces. -/
abbrev NormalRow := {a : Row // a.normal = a}

def normalRowCmp (a b : NormalRow) : Ordering := Row.cmp a.val b.val

theorem normalRowCmp_eq_iff (a b : NormalRow) :
    normalRowCmp a b = .eq ↔ a = b := by
  rw [normalRowCmp, row_cmp_eq_iff_of_normal a.property b.property]
  exact ⟨Subtype.ext, fun h => congrArg Subtype.val h⟩

theorem normalRowCmp_lt_trans {a b c : NormalRow}
    (hab : normalRowCmp a b = .lt) (hbc : normalRowCmp b c = .lt) :
    normalRowCmp a c = .lt := row_cmp_lt_trans hab hbc

#print axioms row_cmp_eq_iff_normal_eq
#print axioms approx_normal
#print axioms package_normal
#print axioms row_cmp_lt_trans
#print axioms normalRowCmp_eq_iff

end OrdinalFormal.LRDStructure
