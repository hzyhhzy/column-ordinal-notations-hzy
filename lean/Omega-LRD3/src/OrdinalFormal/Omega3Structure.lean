import OrdinalFormal.OmegaLRD3

/-!
Structural nesting audit, independent of fundamental-sequence well-foundedness.
All theorems in this module concern finite syntax trees and the comparison fuel.
-/

set_option maxHeartbeats 500000
set_option maxRecDepth 2048

namespace OrdinalFormal.OmegaLRD3
open Columns

theorem Edges.row_depth_lt {es : Edges} {e : Entry Diagram}
    (he : e ∈ es.toList) : e.row.depth < es.depth := by
  cases es with
  | nil => simp [Edges.toList] at he
  | cons row p q tail =>
    simp only [Edges.toList, List.mem_cons] at he
    cases he with
    | inl he =>
      subst e
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
        (Nat.le_max_left _ _)
    | inr he =>
      exact Nat.lt_of_lt_of_le (Edges.row_depth_lt he)
        (Nat.le_max_right _ _)
termination_by sizeOf es

theorem Diagram.row_depth_lt {a : Diagram} {c : Column Diagram} {e : Entry Diagram}
    (hc : c ∈ a.toGraph) (he : e ∈ c) : e.row.depth < a.depth := by
  cases a with
  | nil => simp [Diagram.toGraph] at hc
  | col previous incoming =>
    simp only [Diagram.toGraph, List.mem_append, List.mem_singleton] at hc
    cases hc with
    | inl hc =>
      exact Nat.lt_of_lt_of_le (Diagram.row_depth_lt hc he)
        (Nat.le_max_left _ _)
    | inr hc =>
      subst c
      exact Nat.lt_of_lt_of_le (Edges.row_depth_lt he)
        (Nat.le_max_right _ _)
termination_by sizeOf a

private theorem listCompare_congr {α : Type} (f g : α → α → Ordering)
    (as bs : List α) (h : ∀ a ∈ as, ∀ b ∈ bs, f a b = g a b) :
    listCompare f as bs = listCompare g as bs := by
  induction as generalizing bs with
  | nil => cases bs <;> rfl
  | cons a as ih =>
    cases bs with
    | nil => rfl
    | cons b bs =>
      simp only [listCompare]
      rw [h a (List.mem_cons_self) b (List.mem_cons_self)]
      have ht := ih bs (fun x hx y hy =>
        h x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))
      simp only [ht]

private theorem graphCompare_congr (f g : Diagram → Diagram → Ordering)
    (as bs : Graph Diagram)
    (h : ∀ c ∈ as, ∀ e ∈ c, ∀ d ∈ bs, ∀ k ∈ d, f e.row k.row = g e.row k.row) :
    graphCompare f as bs = graphCompare g as bs := by
  apply listCompare_congr
  intro c hc d hd
  apply listCompare_congr
  intro e he k hk
  simp only [entryCompare, h c hc e he d hd k hk]

/-- Once the two syntax depths are covered, further comparison fuel is inert. -/
theorem compareAt_add (d extra : Nat) (a b : Diagram)
    (ha : a.depth ≤ d) (hb : b.depth ≤ d) :
    compareAt (d + extra) a b = compareAt d a b := by
  induction d generalizing a b with
  | zero =>
    cases extra with
    | zero => rfl
    | succ extra =>
      apply graphCompare_congr
      intro c hc e he f hf k hk
      have hlt := Diagram.row_depth_lt hc he
      omega
  | succ d ih =>
    rw [show d + 1 + extra = d + extra + 1 by omega]
    change graphCompare (compareAt (d + extra)) a.toGraph b.toGraph =
      graphCompare (compareAt d) a.toGraph b.toGraph
    apply graphCompare_congr
    intro c hc e he f hf k hk
    apply ih
    · have hlt := Diagram.row_depth_lt hc he; omega
    · have hlt := Diagram.row_depth_lt hf hk; omega

/-- In particular the public comparison's chosen depth can be increased arbitrarily. -/
theorem cmp_fuel_stable (a b : Diagram) (extra : Nat) :
    compareAt (a.depth + b.depth + 1 + extra) a b = cmp a b := by
  apply compareAt_add <;> omega

private theorem controlFold_mem (cmp : Diagram → Diagram → Ordering)
    (es : Column Diagram) (a : Entry Diagram) :
    es.foldl (fun a b => if controlCompare cmp a b == .lt then b else a) a ∈ a :: es := by
  induction es generalizing a with
  | nil => simp
  | cons b bs ih =>
    simp only [List.foldl_cons]
    split
    · have hm := ih b
      simp only [List.mem_cons] at hm ⊢
      exact hm.elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr h))
    · have hm := ih a
      simp only [List.mem_cons] at hm ⊢
      exact hm.elim Or.inl (fun h => Or.inr (Or.inr h))

theorem control_mem (cmp : Diagram → Diagram → Ordering)
    {c : Column Diagram} {e : Entry Diagram} (h : control cmp c = some e) : e ∈ c := by
  cases c with
  | nil => simp [Columns.control] at h
  | cons a es =>
    simp only [Columns.control, Option.some.injEq] at h
    rw [← h]
    exact controlFold_mem cmp es a

/-- Recursive packages are only requested for an actual row of the input. -/
theorem Diagram.control_row_depth_lt {a : Diagram} {e : Entry Diagram}
    (h : control cmp (a.toGraph.getLast?.getD []) = some e) : e.row.depth < a.depth := by
  have he := control_mem cmp h
  cases hl : a.toGraph.getLast? with
  | none => simp [hl] at he
  | some c =>
    simp only [hl, Option.getD_some] at he
    exact Diagram.row_depth_lt (List.mem_of_getLast? hl) he

private theorem expand_congr_package (p q : Package Diagram)
    (a : Diagram) (n : Nat)
    (h : ∀ e, control cmp (a.toGraph.getLast?.getD []) = some e →
      ∀ b, p e.row b = q e.row b) :
    expand cmp p a.toGraph n = expand cmp q a.toGraph n := by
  unfold expand
  split
  · rfl
  · rename_i e he
    have heq : ∀ b, block cmp p a.toGraph e b = block cmp q a.toGraph e b := by
      intro b
      simp only [block, generatedSeam, h e he b]
    rw [funext heq]

/-- Once input nesting is covered, increasing expansion fuel cannot change its result.
This is structural recursion on row syntax, not a claim about iterated expansion. -/
theorem expandAt_add (d extra : Nat) (a : Diagram) (n : Nat)
    (ha : a.depth ≤ d) : expandAt (d + extra) a n = expandAt d a n := by
  induction d generalizing a n with
  | zero =>
    cases extra with
    | zero => rfl
    | succ extra =>
      simp only [expandAt]
      congr 1
      apply expand_congr_package
      intro e he b
      have hlt := Diagram.control_row_depth_lt he
      omega
  | succ d ih =>
    rw [show d + 1 + extra = d + extra + 1 by omega]
    simp only [expandAt]
    congr 1
    apply expand_congr_package
    intro e he b
    have hd : e.row.depth ≤ d := by
      have hlt := Diagram.control_row_depth_lt he
      omega
    have hrow : expandAt (d + extra) e.row = expandAt d e.row :=
      funext (fun n => ih e.row n hd)
    rw [hrow]

theorem fs_fuel_stable (a : Diagram) (n extra : Nat) :
    expandAt (a.depth + extra) a n = fs a n :=
  expandAt_add a.depth extra a n (Nat.le_refl _)

end OrdinalFormal.OmegaLRD3
