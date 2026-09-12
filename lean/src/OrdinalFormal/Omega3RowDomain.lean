import OrdinalFormal.Omega3Structure
import OrdinalFormal.Omega3Domains
import OrdinalFormal.RowInvariant

/-!
The public Omega-LRD3 operations, without auxiliary fuel in the statement.
Actual standard expressions have actual standard row labels. No row or diagram
well-foundedness is assumed or concluded by these syntactic closure results.
-/

namespace OrdinalFormal.OmegaLRD3
open Columns RowInvariant
set_option autoImplicit false
set_option maxHeartbeats 600000

def rowPackage (row : Diagram) (b : Nat) : List Diagram :=
  if row.isFinite then [] else Diagram.nil :: (List.range (b + 1)).map (fs row)

theorem expand_package_congr (p q : Package Diagram) (a : Diagram) (n : Nat)
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

theorem expandAt_eq_fs (d : Nat) (a : Diagram) (n : Nat) (ha : a.depth ≤ d) :
    expandAt d a n = fs a n := by
  have hd : d = a.depth + (d - a.depth) := by omega
  rw [hd]
  exact fs_fuel_stable a n _

/-- This is the exact actual rule, not a new definition of expansion. -/
theorem fs_toGraph (a : Diagram) (n : Nat) :
    (fs a n).toGraph = expand cmp rowPackage a.toGraph n := by
  unfold fs
  cases hd : a.depth with
  | zero =>
    simp only [expandAt, Diagram.toGraph_ofGraph]
    apply expand_package_congr
    intro e he b
    have hl := Diagram.control_row_depth_lt he
    omega
  | succ d =>
    simp only [expandAt, Diagram.toGraph_ofGraph]
    apply expand_package_congr
    intro e he b
    have hl : e.row.depth ≤ d := by
      have hh := Diagram.control_row_depth_lt he
      omega
    have hfs : expandAt d e.row = fs e.row :=
      funext (fun n => expandAt_eq_fs d e.row n hl)
    simp only [rowPackage, hfs]

theorem fs_ofGraph (a : Diagram) (n : Nat) :
    fs a n = Diagram.ofGraph (expand cmp rowPackage a.toGraph n) := by
  have h := congrArg Diagram.ofGraph (fs_toGraph a n)
  simpa only [Diagram.ofGraph_toGraph] using h

theorem standard_nil : Standard (.finite Diagram.nil) :=
  Standard.child Standard.top 0

theorem rowPackage_standard {row : Diagram} (hr : Standard (.finite row))
    (b : Nat) : ∀ low ∈ rowPackage row b, Standard (.finite low) := by
  intro low hl
  unfold rowPackage at hl
  split at hl
  · simp at hl
  · rcases List.mem_cons.mp hl with h | h
    · subst low
      exact standard_nil
    · obtain ⟨n, _, rfl⟩ := List.mem_map.mp h
      exact Standard.child hr n

theorem seed_rows_standard (d : Nat) :
    AllRows (fun row => Standard (.finite row)) (seed d).toGraph := by
  induction d with
  | zero => simp [seed, Diagram.toGraph, AllRows]
  | succ d ih =>
    intro c hc e he
    simp only [seed, Diagram.toGraph, Edges.toList_ofList,
      List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact ih c hc e he
    · by_cases hd : d = 0
      · simp [hd] at he
      · simp only [hd, ↓reduceIte] at he
        apply normalizeColumn_rows cmp (fun row => Standard (.finite row)) _ ?_ e he
        intro s hs
        obtain rfl := List.mem_singleton.mp hs
        exact Standard.child Standard.top d

theorem fs_rows_standard {a : Diagram}
    (ha : AllRows (fun row => Standard (.finite row)) a.toGraph) (n : Nat) :
    AllRows (fun row => Standard (.finite row)) (fs a n).toGraph := by
  rw [fs_toGraph]
  exact expand_rows cmp rowPackage _ a.toGraph ha
    (fun _ h b _ hm => rowPackage_standard h b _ hm) n

/-- No arbitrary parsed row is admitted: all rows of a standard finite term
belong to the same actual generated standard domain. -/
theorem standard_rows {a : Diagram} (ha : Standard (.finite a)) :
    AllRows (fun row => Standard (.finite row)) a.toGraph := by
  have hall : ∀ t, Standard t → match t with
      | .top => True
      | .finite a => AllRows (fun row => Standard (.finite row)) a.toGraph := by
    intro t ht
    induction ht with
    | top => trivial
    | @child t ht n ih =>
      cases t with
      | top => exact seed_rows_standard n
      | finite a => exact fs_rows_standard ih n
  exact hall (.finite a) ha

theorem Edges.depth_le_of_rows (es : Edges) (d : Nat)
    (h : ∀ e ∈ es.toList, e.row.depth < d) : es.depth ≤ d := by
  cases es with
  | nil => exact Nat.zero_le d
  | cons row p q tail =>
    apply Nat.max_le.mpr
    constructor
    · have hh := h ⟨row, p, q⟩ List.mem_cons_self
      change row.depth < d at hh
      omega
    · exact Edges.depth_le_of_rows tail d
        (fun e he => h e (List.mem_cons_of_mem _ he))
termination_by sizeOf es

theorem Diagram.depth_le_of_rows (a : Diagram) (d : Nat)
    (h : AllRows (fun row => row.depth < d) a.toGraph) : a.depth ≤ d := by
  cases a with
  | nil => exact Nat.zero_le d
  | col previous incoming =>
    apply Nat.max_le.mpr
    constructor
    · exact Diagram.depth_le_of_rows previous d
        (fun c hc e he => h c (List.mem_append_left _ hc) e he)
    · apply Edges.depth_le_of_rows incoming d
      intro e he
      exact h incoming.toList (List.mem_append_right _ List.mem_cons_self) e he
termination_by sizeOf a

theorem Diagram.depth_le_iff_rows (a : Diagram) (d : Nat) :
    a.depth ≤ d ↔ AllRows (fun row => row.depth < d) a.toGraph := by
  constructor
  · intro ha c hc e he
    exact Nat.lt_of_lt_of_le (Diagram.row_depth_lt hc he) ha
  · exact Diagram.depth_le_of_rows a d

/-- Even the auxiliary implementation at arbitrary fuel never increases input
nesting. The proof is induction on finite computation, not an infinite-chain
argument. In particular fuel zero is not used to assert termination. -/
theorem expandAt_depth_le (fuel : Nat) (a : Diagram) (n : Nat) :
    (expandAt fuel a n).depth ≤ a.depth := by
  induction fuel generalizing a n with
  | zero =>
    apply Diagram.depth_le_of_rows
    simp only [expandAt, Diagram.toGraph_ofGraph]
    exact expand_rows cmp (fun _ _ => []) _ a.toGraph
      (fun _ hc _ he => Diagram.row_depth_lt hc he)
      (fun _ _ _ _ h => False.elim (List.not_mem_nil h)) n
  | succ fuel ih =>
    apply Diagram.depth_le_of_rows
    simp only [expandAt, Diagram.toGraph_ofGraph]
    apply expand_rows_of_control cmp
      (fun row b => if row.isFinite then [] else
        Diagram.nil :: (List.range (b + 1)).map (expandAt fuel row))
      (fun row => row.depth < a.depth) a.toGraph
      (fun _ hc _ he => Diagram.row_depth_lt hc he) ?_ n
    intro e he b low hl
    have hedepth := Diagram.control_row_depth_lt he
    split at hl
    · simp at hl
    · rcases List.mem_cons.mp hl with h | h
      · subst low
        change 0 < a.depth
        omega
      · obtain ⟨t, _, rfl⟩ := List.mem_map.mp h
        exact Nat.lt_of_le_of_lt (ih e.row t) hedepth

theorem fs_depth_le (a : Diagram) (n : Nat) : (fs a n).depth ≤ a.depth :=
  expandAt_depth_le a.depth a n

theorem seed_depth_le (d : Nat) : (seed d).depth ≤ d := by
  induction d with
  | zero => exact Nat.zero_le 0
  | succ d ih =>
    apply Diagram.depth_le_of_rows
    intro c hc e he
    simp only [seed, Diagram.toGraph, Edges.toList_ofList,
      List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact Nat.lt_of_lt_of_le (Diagram.row_depth_lt hc he) (Nat.le_succ_of_le ih)
    · by_cases hd : d = 0
      · simp [hd] at he
      · simp only [hd, ↓reduceIte] at he
        apply normalizeColumn_rows cmp (fun row => row.depth < d + 1) _ ?_ e he
        intro s hs
        obtain rfl := List.mem_singleton.mp hs
        exact Nat.lt_succ_of_le ih

#print axioms fs_toGraph
#print axioms seed_rows_standard
#print axioms standard_rows
#print axioms expandAt_depth_le
#print axioms fs_depth_le
#print axioms seed_depth_le

end OrdinalFormal.OmegaLRD3
