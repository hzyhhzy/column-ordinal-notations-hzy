import OrdinalFormal.GeneratedColumnDecrease
import OrdinalFormal.LRDNormalLift
import OrdinalFormal.StandardValidity

/-!
# Strict comparison decrease on the actual LRD standard domain

LRD has one finite seed, included in `Standard`; no external top is adjoined.
The proof lifts its actual operations to normalized rows and erases back without
changing any standard expression or comparator result. This proves comparison
and canonical-column invariants, not a semantic well-ordering theorem.
-/

namespace OrdinalFormal.LRDColumnDecrease

open Columns LRDStructure LRDNormalLift GenericSortedColumns
set_option autoImplicit false
set_option maxHeartbeats 700000

theorem natListCompare_trichotomy (as bs : List Nat) :
    listCompare compare as bs = .lt ∨ as = bs ∨ listCompare compare bs as = .lt := by
  induction as generalizing bs with
  | nil => cases bs <;> simp [listCompare]
  | cons a as ih =>
      cases bs with
      | nil => exact Or.inr (Or.inr rfl)
      | cons b bs =>
          by_cases hab : a < b
          · exact Or.inl (by simp [listCompare, thenCompare, Nat.compare_eq_lt.mpr hab])
          by_cases hba : b < a
          · exact Or.inr (Or.inr (by simp [listCompare, thenCompare, Nat.compare_eq_lt.mpr hba]))
          have he : a = b := by omega
          subst b
          rcases ih bs with h | h | h
          · exact Or.inl (by simpa [listCompare, thenCompare] using h)
          · exact Or.inr (Or.inl (congrArg (List.cons a) h))
          · exact Or.inr (Or.inr (by simpa [listCompare, thenCompare] using h))

theorem row_cmp_trichotomy (a b : LRD.Row) :
    LRD.Row.cmp a b = .lt ∨ a.normal = b.normal ∨ LRD.Row.cmp b a = .lt := by
  cases a with
  | limit => cases b <;> simp [LRD.Row.cmp, LRD.Row.normal]
  | poly as =>
      cases b with
      | limit => exact Or.inl rfl
      | poly bs =>
          by_cases hl : (LRD.trim as).length < (LRD.trim bs).length
          · exact Or.inl ((poly_cmp_lt_iff as bs).mpr (Or.inl hl))
          by_cases hr : (LRD.trim bs).length < (LRD.trim as).length
          · exact Or.inr (Or.inr ((poly_cmp_lt_iff bs as).mpr (Or.inl hr)))
          have he : (LRD.trim as).length = (LRD.trim bs).length := by omega
          rcases natListCompare_trichotomy (LRD.trim as).reverse (LRD.trim bs).reverse with h | h | h
          · exact Or.inl ((poly_cmp_lt_iff as bs).mpr (Or.inr ⟨he, h⟩))
          · exact Or.inr (Or.inl (congrArg LRD.Row.poly (List.reverse_inj.mp h)))
          · exact Or.inr (Or.inr ((poly_cmp_lt_iff bs as).mpr (Or.inr ⟨he.symm, h⟩)))

theorem normal_compare_laws : CompareLaws normalRowCmp where
  eq_iff := normalRowCmp_eq_iff
  lt_trans := normalRowCmp_lt_trans
  trichotomy := by
    intro a b
    rcases row_cmp_trichotomy a.val b.val with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (Subtype.ext (by simpa only [a.property, b.property] using h)))
    · exact Or.inr (Or.inr h)

theorem lifted_seed_canonical : GenericSortedColumns.Canonical normalRowCmp (liftGraph LRD.seed) := by
  intro c hc
  simp only [LRD.seed, liftGraph, ColumnMap.mapGraph_cons, ColumnMap.mapGraph_nil,
    ColumnMap.mapColumn_nil, ColumnMap.mapColumn_cons, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with rfl | rfl
  · exact ⟨.nil, by simp⟩
  · refine ⟨by simp [GenericSortedColumns.Sorted], ?_⟩
    intro e he q hq
    have he' := List.mem_singleton.mp he
    subst e
    have hq0 : q = 0 := by simpa using Nat.eq_zero_of_le_zero hq
    subst q
    exact List.mem_singleton.mpr rfl

theorem lifted_standard_canonical {g : LRD.Diagram} (hg : LRD.Standard g) :
    GenericSortedColumns.Canonical normalRowCmp (liftGraph g) := by
  induction hg with
  | seed => exact lifted_seed_canonical
  | child h n ih =>
      rw [fs_lift]
      exact expand_canonical normalRowCmp normal_compare_laws normalPackage ih n

theorem canonical_map {A B : Type} (f : A → B)
    (cmpA : A → A → Ordering) (cmpB : B → B → Ordering)
    (hc : ∀ a b, cmpB (f a) (f b) = cmpA a b)
    {g : Graph A} (hg : GenericSortedColumns.Canonical cmpA g) :
    GenericSortedColumns.Canonical cmpB (ColumnMap.mapGraph f g) := by
  intro c hcm
  obtain ⟨source, hs, rfl⟩ := List.mem_map.mp hcm
  obtain ⟨hSorted, hClosed⟩ := hg source hs
  constructor
  · change (source.map (ColumnMap.mapEntry f)).Pairwise _
    rw [List.pairwise_map]
    simpa only [GenericSortedColumns.Sorted, GenericSortedColumns.Lt,
      ColumnMap.entryCompare_map f cmpA cmpB hc] using hSorted
  · intro e he q hq
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp he
    apply List.mem_map.mpr
    refine ⟨{s with root := q}, hClosed s hs q hq, ?_⟩
    rfl

theorem standard_canonical {g : LRD.Diagram} (hg : LRD.Standard g) :
    GenericSortedColumns.Canonical LRD.Row.cmp g := by
  have h := canonical_map (Subtype.val : NormalRow → LRD.Row) normalRowCmp LRD.Row.cmp
    (fun _ _ => rfl) (lifted_standard_canonical hg)
  change GenericSortedColumns.Canonical LRD.Row.cmp (eraseGraph (liftGraph g)) at h
  rwa [erase_lift_standard hg] at h

theorem standard_rootClosed {g : LRD.Diagram} (hg : LRD.Standard g) : RootClosed g :=
  GenericSortedColumns.canonical_rootClosed _ (standard_canonical hg)

theorem fs_lt {g : LRD.Diagram} (hg : LRD.Standard g) (hn : g ≠ []) (n : Nat) :
    LRD.cmp (LRD.fs g n) g = .lt := by
  rw [← compare_lift, fs_lift]
  apply GeneratedColumnDecrease.expand_lt normalRowCmp normal_compare_laws normalPackage
    (fun _ _ _ h => normalPackage_lt h)
    ((valid_lift_iff g).mpr (StandardValidity.lrd_standard_valid hg))
    (lifted_standard_canonical hg) ?_ n
  intro h
  have he := congrArg eraseGraph h
  rw [erase_lift_standard hg] at he
  have : g = [] := he
  exact hn this

theorem standard_step_lt {a b : LRD.Diagram} (hb : LRD.Standard b)
    (hstep : LRD.Step a b) : LRD.cmp a b = .lt := by
  obtain ⟨hn, n, rfl⟩ := hstep
  exact fs_lt hb hn n

theorem cmp_lt_trans {a b c : LRD.Diagram}
    (hab : LRD.cmp a b = .lt) (hbc : LRD.cmp b c = .lt) : LRD.cmp a c = .lt := by
  rw [← compare_lift] at hab hbc ⊢
  exact Comparison.graphCompare_lt_trans normalRowCmp normal_compare_laws.eq_iff
    normal_compare_laws.lt_trans hab hbc

theorem cmp_lt_irrefl (a : LRD.Diagram) : LRD.cmp a a ≠ .lt := by
  rw [← compare_lift]
  exact Comparison.graphCompare_lt_irrefl normalRowCmp normal_compare_laws.eq_iff _

#print axioms standard_canonical
#print axioms fs_lt
#print axioms cmp_lt_trans

end OrdinalFormal.LRDColumnDecrease
