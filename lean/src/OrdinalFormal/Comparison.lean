import OrdinalFormal.Columns
import OrdinalFormal.RPD

/-!
# Correctness of the column comparator

These are order-theoretic facts about the executable comparison functions,
not well-ordering assertions. In particular transitivity of the RPD comparison
holds on all raw finite column lists, although that whole domain is not a
well-order. For LRD, equality-correctness of the row comparator requires a
canonical row domain; it is false for arbitrary untrimmed polynomial syntax.
-/

namespace OrdinalFormal.Comparison

set_option autoImplicit false
set_option maxHeartbeats 600000

universe u

variable {α : Type u}

theorem thenCompare_eq_iff (a : Ordering) (b : Unit → Ordering) :
    Columns.thenCompare a b = .eq ↔ a = .eq ∧ b () = .eq := by
  cases a <;> simp [Columns.thenCompare]

theorem thenCompare_lt_iff (a : Ordering) (b : Unit → Ordering) :
    Columns.thenCompare a b = .lt ↔ a = .lt ∨ (a = .eq ∧ b () = .lt) := by
  cases a <;> simp [Columns.thenCompare]

theorem listCompare_eq_iff (cmp : α → α → Ordering)
    (hEq : ∀ a b, cmp a b = .eq ↔ a = b) (as bs : List α) :
    Columns.listCompare cmp as bs = .eq ↔ as = bs := by
  induction as generalizing bs with
  | nil => cases bs <;> simp [Columns.listCompare]
  | cons a as ih =>
      cases bs with
      | nil => simp [Columns.listCompare]
      | cons b bs => simp [Columns.listCompare, thenCompare_eq_iff, hEq, ih]

/-- The concrete three-way comparison induces exactly `List.Lex` of its
elementwise strict relation. -/
theorem listCompare_lt_iff_lex (cmp : α → α → Ordering)
    (hEq : ∀ a b, cmp a b = .eq ↔ a = b) (as bs : List α) :
    Columns.listCompare cmp as bs = .lt ↔
      List.Lex (fun a b => cmp a b = .lt) as bs := by
  induction as generalizing bs with
  | nil => cases bs <;> simp [Columns.listCompare]
  | cons a as ih =>
      cases bs with
      | nil => simp [Columns.listCompare]
      | cons b bs =>
          simp only [Columns.listCompare, thenCompare_lt_iff, hEq, ih,
            List.cons_lex_cons_iff]

theorem listCompare_lt_trans (cmp : α → α → Ordering)
    (hEq : ∀ a b, cmp a b = .eq ↔ a = b)
    (hTrans : ∀ {a b c}, cmp a b = .lt → cmp b c = .lt → cmp a c = .lt)
    {as bs cs : List α} (hab : Columns.listCompare cmp as bs = .lt)
    (hbc : Columns.listCompare cmp bs cs = .lt) :
    Columns.listCompare cmp as cs = .lt := by
  apply (listCompare_lt_iff_lex cmp hEq as cs).mpr
  exact List.lex_trans hTrans
    ((listCompare_lt_iff_lex cmp hEq as bs).mp hab)
    ((listCompare_lt_iff_lex cmp hEq bs cs).mp hbc)

theorem listCompare_lt_irrefl (cmp : α → α → Ordering)
    (hEq : ∀ a b, cmp a b = .eq ↔ a = b) (as : List α) :
    Columns.listCompare cmp as as ≠ .lt := by
  rw [(listCompare_eq_iff cmp hEq as as).mpr rfl]
  decide

theorem entryCompare_eq_iff (cmp : α → α → Ordering)
    (hEq : ∀ a b, cmp a b = .eq ↔ a = b) (a b : Columns.Entry α) :
    Columns.entryCompare cmp a b = .eq ↔ a = b := by
  cases a
  cases b
  simp [Columns.entryCompare, thenCompare_eq_iff, hEq, and_left_comm]

theorem entryCompare_lt_iff (cmp : α → α → Ordering)
    (hEq : ∀ a b, cmp a b = .eq ↔ a = b) (a b : Columns.Entry α) :
    Columns.entryCompare cmp a b = .lt ↔
      a.parent < b.parent ∨ (a.parent = b.parent ∧
        (cmp a.row b.row = .lt ∨ (a.row = b.row ∧ a.root < b.root))) := by
  simp only [Columns.entryCompare, thenCompare_lt_iff, Nat.compare_eq_lt,
    Nat.compare_eq_eq, hEq]

theorem entryCompare_lt_trans (cmp : α → α → Ordering)
    (hEq : ∀ a b, cmp a b = .eq ↔ a = b)
    (hTrans : ∀ {a b c}, cmp a b = .lt → cmp b c = .lt → cmp a c = .lt)
    {a b c : Columns.Entry α} (hab : Columns.entryCompare cmp a b = .lt)
    (hbc : Columns.entryCompare cmp b c = .lt) :
    Columns.entryCompare cmp a c = .lt := by
  apply (entryCompare_lt_iff cmp hEq a c).mpr
  have hab' := (entryCompare_lt_iff cmp hEq a b).mp hab
  have hbc' := (entryCompare_lt_iff cmp hEq b c).mp hbc
  rcases hab' with hpab | ⟨hpab, hrab | ⟨hrab, hqab⟩⟩
  · rcases hbc' with hpbc | ⟨hpbc, _⟩
    · exact Or.inl (Nat.lt_trans hpab hpbc)
    · exact Or.inl (by omega)
  · rcases hbc' with hpbc | ⟨hpbc, hrbc | ⟨hrbc, _⟩⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨hpab.trans hpbc, Or.inl (hTrans hrab hrbc)⟩
    · exact Or.inr ⟨hpab.trans hpbc, Or.inl (by simpa [← hrbc] using hrab)⟩
  · rcases hbc' with hpbc | ⟨hpbc, hrbc | ⟨hrbc, hqbc⟩⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨hpab.trans hpbc, Or.inl (by simpa [hrab] using hrbc)⟩
    · exact Or.inr ⟨hpab.trans hpbc, Or.inr ⟨hrab.trans hrbc, Nat.lt_trans hqab hqbc⟩⟩

theorem graphCompare_eq_iff (cmp : α → α → Ordering)
    (hEq : ∀ a b, cmp a b = .eq ↔ a = b) (a b : Columns.Graph α) :
    Columns.graphCompare cmp a b = .eq ↔ a = b :=
  listCompare_eq_iff _ (listCompare_eq_iff _ (entryCompare_eq_iff cmp hEq)) a b

theorem graphCompare_lt_trans (cmp : α → α → Ordering)
    (hEq : ∀ a b, cmp a b = .eq ↔ a = b)
    (hTrans : ∀ {a b c}, cmp a b = .lt → cmp b c = .lt → cmp a c = .lt)
    {a b c : Columns.Graph α} (hab : Columns.graphCompare cmp a b = .lt)
    (hbc : Columns.graphCompare cmp b c = .lt) :
    Columns.graphCompare cmp a c = .lt :=
  listCompare_lt_trans _ (listCompare_eq_iff _ (entryCompare_eq_iff cmp hEq))
    (listCompare_lt_trans _ (entryCompare_eq_iff cmp hEq)
      (entryCompare_lt_trans cmp hEq hTrans)) hab hbc

theorem graphCompare_lt_irrefl (cmp : α → α → Ordering)
    (hEq : ∀ a b, cmp a b = .eq ↔ a = b) (a : Columns.Graph α) :
    Columns.graphCompare cmp a a ≠ .lt := by
  rw [(graphCompare_eq_iff cmp hEq a a).mpr rfl]
  decide

theorem nat_compare_lt_trans {a b c : Nat}
    (hab : compare a b = .lt) (hbc : compare b c = .lt) : compare a c = .lt :=
  Nat.compare_eq_lt.mpr (Nat.lt_trans (Nat.compare_eq_lt.mp hab) (Nat.compare_eq_lt.mp hbc))

theorem rpd_cmp_eq_iff (a b : RPD.Diagram) : RPD.cmp a b = .eq ↔ a = b :=
  graphCompare_eq_iff compare (fun _ _ => Nat.compare_eq_eq) a b

theorem rpd_cmp_lt_trans {a b c : RPD.Diagram}
    (hab : RPD.cmp a b = .lt) (hbc : RPD.cmp b c = .lt) : RPD.cmp a c = .lt :=
  graphCompare_lt_trans compare (fun _ _ => Nat.compare_eq_eq) nat_compare_lt_trans hab hbc

theorem rpd_cmp_lt_irrefl (a : RPD.Diagram) : RPD.cmp a a ≠ .lt :=
  graphCompare_lt_irrefl compare (fun _ _ => Nat.compare_eq_eq) a

#print axioms listCompare_lt_iff_lex
#print axioms graphCompare_lt_trans
#print axioms rpd_cmp_lt_trans
#print axioms rpd_cmp_lt_irrefl

end OrdinalFormal.Comparison
