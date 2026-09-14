import OrdinalFormal.Omega3Structure
import OrdinalFormal.Comparison
import OrdinalFormal.GenericSortedColumns

/-!
# Actual recursive Omega-LRD3 comparison

Finite structural-depth induction, independent of expansion and standardness.
Insufficient-fuel equality is never treated as equality of raw syntax.
-/

namespace OrdinalFormal.Omega3Comparison

open Columns OmegaLRD3
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 4096

universe u

structure LawsOn {A : Type u} (P : A → Prop) (cmp : A → A → Ordering) : Prop where
  eq_iff : ∀ a b, P a → P b → (cmp a b = .eq ↔ a = b)
  trans : ∀ {a b c}, P a → P b → P c → cmp a b = .lt → cmp b c = .lt → cmp a c = .lt
  tri : ∀ a b, P a → P b → cmp a b = .lt ∨ a = b ∨ cmp b a = .lt

def All {A : Type u} (P : A → Prop) (as : List A) : Prop := ∀ a ∈ as, P a

theorem list_laws {A : Type u} (P : A → Prop) (cmp : A → A → Ordering) (h : LawsOn P cmp) :
    LawsOn (All P) (listCompare cmp) := by
  constructor
  · intro as bs ha hb
    induction as generalizing bs with
    | nil => cases bs <;> simp [listCompare]
    | cons a as ih =>
      cases bs with
      | nil => simp [listCompare]
      | cons b bs =>
        have hh := h.eq_iff a b (ha a List.mem_cons_self) (hb b List.mem_cons_self)
        have ht := ih bs (fun x hx => ha x (List.mem_cons_of_mem a hx))
          (fun x hx => hb x (List.mem_cons_of_mem b hx))
        simp only [listCompare, Comparison.thenCompare_eq_iff, hh, ht, List.cons.injEq]
  · intro as bs cs ha hb hc hab hbc
    induction as generalizing bs cs with
    | nil => cases bs <;> cases cs <;> simp [listCompare] at *
    | cons a as ih =>
      cases bs with
      | nil => simp [listCompare] at hab
      | cons b bs =>
        cases cs with
        | nil => simp [listCompare] at hbc
        | cons c cs =>
          have pa := ha a List.mem_cons_self
          have pb := hb b List.mem_cons_self
          have pc := hc c List.mem_cons_self
          have hab' := (Comparison.thenCompare_lt_iff _ _).mp hab
          have hbc' := (Comparison.thenCompare_lt_iff _ _).mp hbc
          apply (Comparison.thenCompare_lt_iff _ _).mpr
          rcases hab' with hab' | ⟨heab, hab'⟩
          · rcases hbc' with hbc' | ⟨hebc, _⟩
            · exact Or.inl (h.trans pa pb pc hab' hbc')
            · have he := (h.eq_iff b c pb pc).mp hebc
              exact Or.inl (he ▸ hab')
          · have he := (h.eq_iff a b pa pb).mp heab
            subst b
            rcases hbc' with hbc' | ⟨heac, hbc'⟩
            · exact Or.inl hbc'
            · exact Or.inr ⟨heac, ih (fun x hx => ha x (List.mem_cons_of_mem a hx))
                (fun x hx => hb x (List.mem_cons_of_mem a hx))
                (fun x hx => hc x (List.mem_cons_of_mem c hx)) hab' hbc'⟩
  · intro as bs ha hb
    induction as generalizing bs with
    | nil => cases bs <;> simp [listCompare]
    | cons a as ih =>
      cases bs with
      | nil => exact Or.inr (Or.inr rfl)
      | cons b bs =>
        rcases h.tri a b (ha a List.mem_cons_self) (hb b List.mem_cons_self) with hl | he | hr
        · exact Or.inl (by simp only [listCompare, hl, thenCompare])
        · subst b
          have hs := (h.eq_iff a a (ha a List.mem_cons_self) (ha a List.mem_cons_self)).mpr rfl
          rcases ih bs (fun x hx => ha x (List.mem_cons_of_mem a hx))
            (fun x hx => hb x (List.mem_cons_of_mem a hx)) with hl | he | hr
          · exact Or.inl (by simpa only [listCompare, hs, thenCompare] using hl)
          · exact Or.inr (Or.inl (congrArg (List.cons a) he))
          · exact Or.inr (Or.inr (by simpa only [listCompare, hs, thenCompare] using hr))
        · exact Or.inr (Or.inr (by simp only [listCompare, hr, thenCompare]))

theorem entry_laws {A : Type u} (P : A → Prop) (cmp : A → A → Ordering) (h : LawsOn P cmp) :
    LawsOn (fun e : Entry A => P e.row) (entryCompare cmp) := by
  constructor
  · intro a b ha hb
    cases a
    cases b
    simp only [entryCompare, Comparison.thenCompare_eq_iff, Nat.compare_eq_eq,
      h.eq_iff _ _ ha hb]
    simp [and_left_comm]
  · intro a b c ha hb hc hab hbc
    have expand (x y : Entry A) : entryCompare cmp x y = .lt ↔
      x.parent < y.parent ∨ (x.parent = y.parent ∧
        (cmp x.row y.row = .lt ∨ (cmp x.row y.row = .eq ∧ x.root < y.root))) := by
      simp only [entryCompare, Comparison.thenCompare_lt_iff, Nat.compare_eq_lt, Nat.compare_eq_eq]
    have hab' := (expand a b).mp hab
    have hbc' := (expand b c).mp hbc
    apply (expand a c).mpr
    rcases hab' with hp | ⟨hp, hr | ⟨hr, hq⟩⟩
    · rcases hbc' with hp' | ⟨hp', _⟩ <;> exact Or.inl (by omega)
    · rcases hbc' with hp' | ⟨hp', hr' | ⟨hr', _⟩⟩
      · exact Or.inl (by omega)
      · exact Or.inr ⟨hp.trans hp', Or.inl (h.trans ha hb hc hr hr')⟩
      · have he := (h.eq_iff _ _ hb hc).mp hr'
        exact Or.inr ⟨hp.trans hp', Or.inl (he ▸ hr)⟩
    · rcases hbc' with hp' | ⟨hp', hr' | ⟨hr', hq'⟩⟩
      · exact Or.inl (by omega)
      · have he := (h.eq_iff _ _ ha hb).mp hr
        exact Or.inr ⟨hp.trans hp', Or.inl (he.symm ▸ hr')⟩
      · have he := (h.eq_iff _ _ ha hb).mp hr
        have he' := (h.eq_iff _ _ hb hc).mp hr'
        exact Or.inr ⟨hp.trans hp', Or.inr ⟨(h.eq_iff _ _ ha hc).mpr (he.trans he'), by omega⟩⟩
  · intro a b ha hb
    have expand (x y : Entry A) : entryCompare cmp x y = .lt ↔
      x.parent < y.parent ∨ (x.parent = y.parent ∧
        (cmp x.row y.row = .lt ∨ (cmp x.row y.row = .eq ∧ x.root < y.root))) := by
      simp only [entryCompare, Comparison.thenCompare_lt_iff, Nat.compare_eq_lt, Nat.compare_eq_eq]
    by_cases hp : a.parent < b.parent
    · exact Or.inl ((expand a b).mpr (Or.inl hp))
    by_cases hp' : b.parent < a.parent
    · exact Or.inr (Or.inr ((expand b a).mpr (Or.inl hp')))
    have he : a.parent = b.parent := by omega
    rcases h.tri a.row b.row ha hb with hr | hr | hr
    · exact Or.inl ((expand a b).mpr (Or.inr ⟨he, Or.inl hr⟩))
    · by_cases hq : a.root < b.root
      · exact Or.inl ((expand a b).mpr (Or.inr ⟨he, Or.inr ⟨(h.eq_iff _ _ ha hb).mpr hr, hq⟩⟩))
      by_cases hq' : b.root < a.root
      · exact Or.inr (Or.inr ((expand b a).mpr (Or.inr ⟨he.symm,
          Or.inr ⟨(h.eq_iff _ _ hb ha).mpr hr.symm, hq'⟩⟩)))
      apply Or.inr ∘ Or.inl
      have hqeq : a.root = b.root := by omega
      cases a
      cases b
      simp_all
    · exact Or.inr (Or.inr ((expand b a).mpr (Or.inr ⟨he.symm, Or.inl hr⟩)))

def RowsIn (P : Diagram → Prop) (g : Graph Diagram) : Prop := All (All (fun e => P e.row)) g

theorem graph_laws (P : Diagram → Prop) (cmp : Diagram → Diagram → Ordering) (h : LawsOn P cmp) :
    LawsOn (RowsIn P) (graphCompare cmp) := list_laws _ _ (list_laws _ _ (entry_laws P cmp h))

theorem diagram_laws (P Q : Diagram → Prop) (cmp : Diagram → Diagram → Ordering)
    (h : LawsOn P cmp) (hRows : ∀ a, Q a → RowsIn P a.toGraph) :
    LawsOn Q (fun a b => graphCompare cmp a.toGraph b.toGraph) := by
  have hg := graph_laws P cmp h
  constructor
  · intro a b ha hb
    rw [hg.eq_iff _ _ (hRows a ha) (hRows b hb)]
    exact ⟨fun he => by simpa using congrArg Diagram.ofGraph he, fun he => congrArg Diagram.toGraph he⟩
  · intro a b c ha hb hc hab hbc
    exact hg.trans (hRows a ha) (hRows b hb) (hRows c hc) hab hbc
  · intro a b ha hb
    rcases hg.tri _ _ (hRows a ha) (hRows b hb) with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (by simpa using congrArg Diagram.ofGraph h))
    · exact Or.inr (Or.inr h)

theorem compareAt_laws (d : Nat) : LawsOn (fun a : Diagram => a.depth ≤ d) (compareAt d) := by
  induction d with
  | zero =>
    apply diagram_laws (fun _ => False)
    · exact ⟨fun _ _ h => False.elim h, fun h => False.elim h, fun _ _ h => False.elim h⟩
    · intro a ha c hc e he
      have hlt := Diagram.row_depth_lt hc he
      omega
  | succ d ih =>
    apply diagram_laws (fun a => a.depth ≤ d) _ _ ih
    intro a ha c hc e he
    have hlt := Diagram.row_depth_lt hc he
    omega

theorem compareAt_eq_cmp (d : Nat) (a b : Diagram) (ha : a.depth ≤ d) (hb : b.depth ≤ d) :
    compareAt d a b = cmp a b := by
  have h1 := compareAt_add d (a.depth + b.depth + 1) a b ha hb
  have h2 := cmp_fuel_stable a b d
  have hsum : d + (a.depth + b.depth + 1) = a.depth + b.depth + 1 + d := by omega
  rw [hsum, h2] at h1
  exact h1.symm

theorem cmp_eq_iff (a b : Diagram) : cmp a b = .eq ↔ a = b := by
  rw [← compareAt_eq_cmp (a.depth + b.depth + 1) a b (by omega) (by omega)]
  exact (compareAt_laws _).eq_iff _ _ (by omega) (by omega)

theorem cmp_lt_trans {a b c : Diagram} (hab : cmp a b = .lt) (hbc : cmp b c = .lt) :
    cmp a c = .lt := by
  let d := a.depth + b.depth + c.depth + 1
  rw [← compareAt_eq_cmp d a b (by dsimp [d]; omega) (by dsimp [d]; omega)] at hab
  rw [← compareAt_eq_cmp d b c (by dsimp [d]; omega) (by dsimp [d]; omega)] at hbc
  rw [← compareAt_eq_cmp d a c (by dsimp [d]; omega) (by dsimp [d]; omega)]
  exact (compareAt_laws d).trans (by dsimp [d]; omega) (by dsimp [d]; omega)
    (by dsimp [d]; omega) hab hbc

theorem cmp_trichotomy (a b : Diagram) : cmp a b = .lt ∨ a = b ∨ cmp b a = .lt := by
  let d := a.depth + b.depth + 1
  have h := (compareAt_laws d).tri a b (by dsimp [d]; omega) (by dsimp [d]; omega)
  rwa [compareAt_eq_cmp d a b (by dsimp [d]; omega) (by dsimp [d]; omega),
    compareAt_eq_cmp d b a (by dsimp [d]; omega) (by dsimp [d]; omega)] at h

theorem cmp_irrefl (a : Diagram) : cmp a a ≠ .lt := by
  rw [(cmp_eq_iff a a).mpr rfl]
  decide

theorem compareLaws : GenericSortedColumns.CompareLaws cmp :=
  ⟨cmp_eq_iff, cmp_lt_trans, cmp_trichotomy⟩

theorem listCompare_congr_on {A : Type u} (f g : A → A → Ordering)
    (as bs : List A) (h : ∀ a ∈ as, ∀ b ∈ bs, f a b = g a b) :
    listCompare f as bs = listCompare g as bs := by
  induction as generalizing bs with
  | nil => cases bs <;> rfl
  | cons a as ih =>
    cases bs with
    | nil => rfl
    | cons b bs =>
      simp only [listCompare]
      rw [h a List.mem_cons_self b List.mem_cons_self]
      have ht := ih bs (fun x hx y hy =>
        h x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem b hy))
      rw [ht]

theorem graphCompare_congr_on (f g : Diagram → Diagram → Ordering)
    (as bs : Graph Diagram)
    (h : ∀ c ∈ as, ∀ e ∈ c, ∀ d ∈ bs, ∀ k ∈ d, f e.row k.row = g e.row k.row) :
    graphCompare f as bs = graphCompare g as bs := by
  apply listCompare_congr_on
  intro c hc d hd
  apply listCompare_congr_on
  intro e he k hk
  simp only [entryCompare, h c hc e he d hd k hk]

/-- The public recursive comparator is exactly column comparison using itself
on row labels. Fuel is structural bookkeeping, not a change of ordering. -/
theorem cmp_eq_graphCompare (a b : Diagram) :
    cmp a b = graphCompare cmp a.toGraph b.toGraph := by
  change graphCompare (compareAt (a.depth + b.depth)) a.toGraph b.toGraph = _
  apply graphCompare_congr_on
  intro c hc e he d hd k hk
  have heDepth := Diagram.row_depth_lt hc he
  have hkDepth := Diagram.row_depth_lt hd hk
  exact compareAt_eq_cmp _ _ _ (by omega) (by omega)

theorem rowCompareSound :
    ColumnRepresentation.RowCompareSound cmp (fun a b => cmp a b = .lt) :=
  ⟨fun h => (cmp_eq_iff _ _).mp h, fun h => h⟩

#print axioms cmp_eq_iff
#print axioms cmp_lt_trans
#print axioms cmp_trichotomy
#print axioms cmp_eq_graphCompare

end OrdinalFormal.Omega3Comparison
