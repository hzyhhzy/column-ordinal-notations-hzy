import OrdinalFormal.LRDStructure

/-!
# Strict decrease of actual LRD row approximations

The proof uses only the executable trimmed shortlex/colex comparison, not an
assumed ordinal interpretation or a postulated package-decrease interface.
-/

namespace OrdinalFormal.LRDRowDecrease

set_option autoImplicit false
set_option maxHeartbeats 600000

open LRD Columns

theorem natListCompare_append_left (pre as bs : List Nat) :
    listCompare compare (pre ++ as) (pre ++ bs) = listCompare compare as bs := by
  induction pre with
  | nil => rfl
  | cons p ps ih => simp [listCompare, thenCompare, ih]

theorem natListCompare_append_right {as bs : List Nat} (h : as.length = bs.length)
    (tail : List Nat) :
    listCompare compare (as ++ tail) (bs ++ tail) = listCompare compare as bs := by
  induction as generalizing bs with
  | nil =>
      have hb : bs = [] := by simpa using h.symm
      subst bs
      simp only [List.nil_append, listCompare]
      exact (Comparison.listCompare_eq_iff compare (fun _ _ => Nat.compare_eq_eq) tail tail).mpr rfl
  | cons a as ih =>
      cases bs with
      | nil => simp at h
      | cons b bs =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at h
          simp only [List.cons_append, listCompare, ih h]

def RawBelow (as bs : List Nat) : Prop :=
  as.length < bs.length ∨
    (as.length = bs.length ∧ listCompare compare as.reverse bs.reverse = .lt)

theorem rawBelow_cons {as bs : List Nat} (h : RawBelow as bs) (a : Nat) :
    RawBelow (a :: as) (a :: bs) := by
  rcases h with h | ⟨hl, hc⟩
  · exact Or.inl (by simpa using h)
  · apply Or.inr
    refine ⟨by simpa using hl, ?_⟩
    rw [List.reverse_cons, List.reverse_cons,
      natListCompare_append_right (by simpa using hl)]
    exact hc

theorem approximatePoly_rawBelow (cs : List Nat) (t : Nat) (hne : cs ≠ []) :
    RawBelow (approximatePoly cs t) cs := by
  induction cs with
  | nil => exact False.elim (hne rfl)
  | cons a rest ih =>
      by_cases ha : 0 < a
      · rw [approximatePoly.eq_def]
        simp only [if_pos ha]
        apply Or.inr
        refine ⟨rfl, ?_⟩
        rw [List.reverse_cons, List.reverse_cons, natListCompare_append_left]
        have hlt : a - 1 < a := by omega
        simp [listCompare, thenCompare, Nat.compare_eq_lt.mpr hlt]
      · cases rest with
        | nil => simp [approximatePoly, ha, RawBelow]
        | cons b tail =>
            by_cases hb : 0 < b
            · rw [approximatePoly.eq_def]
              simp only [if_neg ha, if_pos hb]
              apply Or.inr
              refine ⟨rfl, ?_⟩
              have hlt : b - 1 < b := by omega
              simp only [List.reverse_cons, List.append_assoc]
              rw [natListCompare_append_left]
              simp [listCompare, thenCompare, Nat.compare_eq_lt.mpr hlt]
            · have ha0 : a = 0 := by omega
              subst a
              rw [approximatePoly.eq_def]
              simp only [Nat.lt_irrefl, if_false, if_neg hb]
              exact rawBelow_cons (ih (by simp)) 0

theorem trim_sublist (cs : List Nat) : List.Sublist (trim cs) cs := by
  have h := (List.dropWhile_sublist (l := cs.reverse) (fun a => a == 0)).reverse
  simpa only [trim, List.reverse_reverse] using h

theorem trim_length_le (cs : List Nat) : (trim cs).length ≤ cs.length :=
  (trim_sublist cs).length_le

theorem trim_eq_of_length_eq {cs : List Nat} (h : (trim cs).length = cs.length) :
    trim cs = cs := (trim_sublist cs).length_eq.mp h

theorem trim_rawBelow_left {as bs : List Nat} (h : RawBelow as bs) :
    RawBelow (trim as) bs := by
  have hle := trim_length_le as
  rcases h with h | ⟨hl, hc⟩
  · exact Or.inl (Nat.lt_of_le_of_lt hle h)
  · by_cases he : (trim as).length = as.length
    · rw [trim_eq_of_length_eq he]
      exact Or.inr ⟨hl, hc⟩
    · exact Or.inl (by omega)

theorem poly_approx_lt {cs : List Nat} (hne : trim cs ≠ []) (t : Nat) :
    Row.cmp ((Row.poly cs).approx t) (.poly cs) = .lt := by
  apply (LRDStructure.poly_cmp_lt_iff _ _).mpr
  simp only [LRDStructure.trim_idempotent]
  exact trim_rawBelow_left (approximatePoly_rawBelow (trim cs) t hne)

theorem row_approx_lt {a : Row} (hne : a.normal ≠ .poly []) (t : Nat) :
    Row.cmp (a.approx t) a = .lt := by
  cases a with
  | limit => rfl
  | poly cs =>
      apply poly_approx_lt (t := t)
      intro h
      exact hne (by simp [Row.normal, h])

theorem zero_row_lt {a : Row} (hne : a.normal ≠ .poly []) :
    Row.cmp (.poly []) a = .lt := by
  cases a with
  | limit => rfl
  | poly cs =>
      apply (LRDStructure.poly_cmp_lt_iff [] cs).mpr
      apply Or.inl
      have hh : trim cs ≠ [] := by
        intro h
        exact hne (by simp [Row.normal, h])
      simpa [trim] using List.length_pos_iff.mpr hh

theorem nonfinite_nonzero {a : Row} (h : a.isFinite = false) : a.normal ≠ .poly [] := by
  cases a with
  | limit => simp [Row.normal]
  | poly cs =>
      intro he
      have ht : trim cs = [] := Row.poly.inj he
      simp [Row.isFinite, ht] at h

theorem package_lt {a r : Row} {b : Nat} (hr : r ∈ package a b) :
    Row.cmp r a = .lt := by
  unfold package at hr
  split at hr
  · simp at hr
  · rename_i hn
    have hn' : a.isFinite = false := by simpa using hn
    have hne := nonfinite_nonzero hn'
    simp only [List.mem_cons, List.mem_map] at hr
    rcases hr with h | ⟨t, _, h⟩
    · subst r
      exact zero_row_lt hne
    · subst r
      exact row_approx_lt hne t

#print axioms row_approx_lt
#print axioms package_lt

end OrdinalFormal.LRDRowDecrease
