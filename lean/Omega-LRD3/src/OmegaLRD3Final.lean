import FiniteDemandColumnWellFounded
import OrdinalFormal.Omega3Countable
import OrdinalFormal.ColumnMap

/-! Unconditional ordinary-Lean well-ordering of the actual Omega-LRD3 standard
domain. The only well-founded induction is on finite syntax depth. For each
diagram, its row pool is fixed once and consists of finitely many descendant
cones. No global row order, seed accessibility, or reflection is postulated. -/

namespace OrdinalFormal.Omega3Final
open Columns OmegaLRD3 Omega3RowPool Omega3WellOrderingReduction
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

abbrev PoolRow (a : Diagram) := {r : Diagram // Pool a r}

def poolCmp (a : Diagram) (r s : PoolRow a) : Ordering := cmp r.val s.val
def poolLt (a : Diagram) (r s : PoolRow a) : Prop := cmp r.val s.val = .lt

def poolPackage (a : Diagram) (r : PoolRow a) (b : Nat) : List (PoolRow a) :=
  (rowPackage r.val b).attach.map (fun low =>
    ⟨low.val, package_mem r.property b low.property⟩)

theorem poolPackage_values (a : Diagram) (r : PoolRow a) (b : Nat) :
    (poolPackage a r b).map Subtype.val = rowPackage r.val b := by
  simp [poolPackage, List.map_map]

def erase (a : Diagram) (g : Graph (PoolRow a)) : Graph Diagram :=
  ColumnMap.mapGraph Subtype.val g

theorem erase_expand (a : Diagram) (g : Graph (PoolRow a)) (n : Nat) :
    erase a (expand (poolCmp a) (poolPackage a) g n) =
      expand cmp rowPackage (erase a g) n := by
  exact (ColumnMap.expand_map Subtype.val (poolCmp a) cmp (fun _ _ => rfl)
    (poolPackage a) rowPackage (fun r b => (poolPackage_values a r b).symm) g n).symm

theorem exists_lift_column (a : Diagram) (c : Column Diagram)
    (hc : ∀ e ∈ c, Pool a e.row) :
    ∃ d : Column (PoolRow a), ColumnMap.mapColumn Subtype.val d = c := by
  induction c with
  | nil => exact ⟨[], rfl⟩
  | cons e es ih =>
    obtain ⟨ds, hds⟩ := ih (fun x hx => hc x (List.mem_cons_of_mem _ hx))
    refine ⟨⟨⟨e.row, hc e List.mem_cons_self⟩, e.parent, e.root⟩ :: ds, ?_⟩
    cases e
    simp [ColumnMap.mapColumn_cons, ColumnMap.mapEntry, hds]

theorem exists_lift (a : Diagram) (g : Graph Diagram) (hg : RowInvariant.AllRows (Pool a) g) :
    ∃ h : Graph (PoolRow a), erase a h = g := by
  induction g with
  | nil => exact ⟨[], rfl⟩
  | cons c cs ih =>
    obtain ⟨d, hd⟩ := exists_lift_column a c (hg c List.mem_cons_self)
    obtain ⟨ds, hds⟩ := ih (fun x hx => hg x (List.mem_cons_of_mem _ hx))
    refine ⟨d :: ds, ?_⟩
    change ColumnMap.mapColumn Subtype.val d :: erase a ds = c :: cs
    rw [hd, hds]

abbrev PoolStep (a : Diagram) := GeneratedSemanticWellFounded.Step (poolCmp a) (poolPackage a)

theorem erase_accessible (a : Diagram) (g : Graph (PoolRow a)) (hg : Acc (PoolStep a) g) :
    Acc Step (Diagram.ofGraph (erase a g)) := by
  induction hg with
  | intro g _ ih =>
    apply Acc.intro
    intro b hb
    obtain ⟨hn, n, rfl⟩ := hb
    have hg0 : g ≠ [] := by
      intro hz
      subst g
      exact hn rfl
    have h := ih (expand (poolCmp a) (poolPackage a) g n) ⟨hg0, n, rfl⟩
    rw [fs_ofGraph, Diagram.toGraph_ofGraph]
    simpa only [erase_expand] using h

/-- The only hypotheses are standardness and accessibility of the finitely
many direct rows, each of strictly smaller finite nesting depth. -/
theorem accessible_of_rows (a : Diagram) (ha : Standard (.finite a))
    (rowAcc : ∀ old ∈ directRows a, Acc Step old) : Acc Step a := by
  have hw : WellFounded (poolLt a) := pool_wellFounded ha rowAcc
  have hp : ∀ high b low, low ∈ poolPackage a high b → poolLt a low high := by
    intro high b low hl
    have hv : low.val ∈ rowPackage high.val b := by
      rw [← poolPackage_values a high b]
      exact List.mem_map.mpr ⟨low, hl, rfl⟩
    exact package_lt ha high.property hv
  have hlaws : ColumnRepresentation.RowCompareSound (poolCmp a) (poolLt a) :=
    ⟨fun h => Subtype.ext ((Omega3Comparison.cmp_eq_iff _ _).mp h), fun h => h⟩
  obtain ⟨g, hg⟩ := exists_lift a a.toGraph (initial_rows a)
  have hvalid : Valid g := by
    apply (ColumnMap.valid_map_iff Subtype.val g).mp
    change Valid (erase a g)
    rw [hg]
    exact Omega3Validity.standard_valid ha
  have hacc : Acc (PoolStep a) g :=
    FiniteDemand.valid_accessible (poolCmp a) (poolPackage a) (poolLt a) hw
      (fun h₁ h₂ => Omega3Comparison.cmp_lt_trans h₁ h₂) hp hlaws g hvalid
  have h := erase_accessible a g hacc
  simpa only [hg, Diagram.ofGraph_toGraph] using h

theorem standard_accessible (a : Diagram) (ha : Standard (.finite a)) : Acc Step a := by
  have go : ∀ d, ∀ a : Diagram, a.depth = d → Standard (.finite a) → Acc Step a := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro a hd ha
      apply accessible_of_rows a ha
      intro old ho
      exact ih old.depth (hd ▸ directRow_depth_lt ho) old rfl (directRow_standard ha ho)
  exact go a.depth a rfl ha

theorem seed_accessible (n : Nat) : Acc Step (seed n) :=
  standard_accessible _ (Standard.child Standard.top n)

theorem standard_wellFounded : WellFounded StandardLt :=
  standard_wellFounded_of_seed_accessible seed_accessible

theorem with_top_wellFounded : WellFounded TermLt :=
  with_top_wellFounded_of_seed_accessible seed_accessible

theorem standard_isWellOrder : IsWellOrder StandardDiagram StandardLt where
  wf := standard_wellFounded
  trichotomous := by
    intro a b hab hba
    rcases standard_total a b with h | h | h
    · exact h
    · exact False.elim (hab h)
    · exact False.elim (hba h)

theorem with_top_isWellOrder : IsWellOrder StandardTerm TermLt where
  wf := with_top_wellFounded
  trichotomous := by
    intro a b hab hba
    rcases with_top_total a b with h | h | h
    · exact h
    · exact False.elim (hab h)
    · exact False.elim (hba h)

theorem standard_step_wellFounded :
    WellFounded (fun a b : StandardDiagram => Step a.val b.val) :=
  standard_step_wellFounded_of_seed_accessible seed_accessible

#print axioms erase_expand
#print axioms accessible_of_rows
#print axioms standard_accessible
#print axioms seed_accessible
#print axioms standard_isWellOrder
#print axioms with_top_isWellOrder
#print axioms standard_step_wellFounded
end OrdinalFormal.Omega3Final
