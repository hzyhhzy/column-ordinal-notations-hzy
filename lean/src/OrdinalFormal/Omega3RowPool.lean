import OrdinalFormal.Omega3WellOrderingReduction
import OrdinalFormal.FiniteUnionWellFounded

/-!
# A fixed finite-origin row pool for actual Omega-LRD3 expansion

The pool is nil plus the descendant cones of the finitely many direct rows
of one fixed initial diagram. Each cone can be infinite. No countable-union
argument and no global standard-domain well-foundedness premise is used.

The final pool well-foundedness theorem explicitly assumes accessibility of
the initial direct rows. It is intended for induction on finite syntax depth,
not as an unconditional well-ordering theorem for Omega-LRD3.
-/

namespace OrdinalFormal.Omega3RowPool
open Columns OmegaLRD3 RowInvariant
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 4096

def directRows (a : Diagram) : List Diagram := a.toGraph.flatten.map Entry.row

theorem mem_directRows (a r : Diagram) : r ∈ directRows a ↔
    ∃ c ∈ a.toGraph, ∃ e ∈ c, e.row = r := by
  constructor
  · intro hr
    obtain ⟨e, he, her⟩ := List.mem_map.mp hr
    obtain ⟨c, hc, he⟩ := List.mem_flatten.mp he
    exact ⟨c, hc, e, he, her⟩
  · rintro ⟨c, hc, e, he, rfl⟩
    exact List.mem_map.mpr ⟨e, List.mem_flatten.mpr ⟨c, hc, he⟩, rfl⟩

theorem directRow_depth_lt {a r : Diagram} (hr : r ∈ directRows a) : r.depth < a.depth := by
  obtain ⟨c, hc, e, he, rfl⟩ := (mem_directRows a r).mp hr
  exact Diagram.row_depth_lt hc he

theorem directRow_standard {a r : Diagram} (ha : Standard (.finite a))
    (hr : r ∈ directRows a) : Standard (.finite r) := by
  obtain ⟨c, hc, e, he, rfl⟩ := (mem_directRows a r).mp hr
  exact standard_rows ha c hc e he

def Pool (a r : Diagram) : Prop :=
  r = .nil ∨ ∃ old ∈ directRows a, Reach Step old r

theorem nil_mem (a : Diagram) : Pool a .nil := Or.inl rfl

theorem directRow_mem {a r : Diagram} (hr : r ∈ directRows a) : Pool a r :=
  Or.inr ⟨r, hr, .refl r⟩

theorem fs_mem {a r : Diagram} (hr : Pool a r) (n : Nat) : Pool a (fs r n) := by
  rcases hr with h | ⟨old, ho, hor⟩
  · subst r
    exact nil_mem a
  · exact Or.inr ⟨old, ho, hor.trans (reach_fs .nil fs fs_nil r n)⟩

theorem reach_mem {a r s : Diagram} (hr : Pool a r) (hrs : Reach Step r s) : Pool a s :=
  reach_preserves .nil fs (Pool a) (fun _ h n => fs_mem h n) hrs hr

theorem package_mem {a row : Diagram} (hr : Pool a row) (b : Nat)
    {low : Diagram} (hl : low ∈ rowPackage row b) : Pool a low := by
  unfold rowPackage at hl
  split at hl
  · simp at hl
  · rcases List.mem_cons.mp hl with h | h
    · subst low
      exact nil_mem a
    · obtain ⟨n, _, rfl⟩ := List.mem_map.mp h
      exact fs_mem hr n

theorem initial_rows (a : Diagram) : AllRows (Pool a) a.toGraph := by
  intro c hc e he
  exact directRow_mem ((mem_directRows a e.row).mpr ⟨c, hc, e, he, rfl⟩)

theorem fs_rows {a b : Diagram} (hb : AllRows (Pool a) b.toGraph) (n : Nat) :
    AllRows (Pool a) (fs b n).toGraph := by
  rw [fs_toGraph]
  exact expand_rows cmp rowPackage (Pool a) b.toGraph hb
    (fun _ h n _ hm => package_mem h n hm) n

/-- Every row appearing anywhere along an actual finite expansion path stays
in the pool fixed by its initial diagram, even on raw nonstandard inputs. -/
theorem descendant_rows {a b : Diagram} (hab : Reach Step a b) :
    AllRows (Pool a) b.toGraph :=
  reach_preserves .nil fs (fun b => AllRows (Pool a) b.toGraph)
    (fun _ h n => fs_rows h n) hab (initial_rows a)

theorem reach_depth_le {a b : Diagram} (hab : Reach Step a b) : b.depth ≤ a.depth := by
  induction hab with
  | refl => exact Nat.le_refl _
  | cons h _ ih =>
    obtain ⟨_, n, rfl⟩ := h
    exact Nat.le_trans ih (fs_depth_le _ n)

/-- Nil is deliberately adjoined even when the initial depth is zero. -/
theorem pool_depth {a r : Diagram} (hr : Pool a r) : r = .nil ∨ r.depth < a.depth := by
  rcases hr with h | ⟨old, ho, hor⟩
  · exact Or.inl h
  · exact Or.inr (Nat.lt_of_le_of_lt (reach_depth_le hor) (directRow_depth_lt ho))

theorem pool_depth_lt_of_ne_nil {a r : Diagram} (hr : Pool a r) (hn : r ≠ .nil) :
    r.depth < a.depth := (pool_depth hr).resolve_left hn

theorem pool_depth_lt_of_pos {a r : Diagram} (ha : 0 < a.depth) (hr : Pool a r) :
    r.depth < a.depth := by
  rcases pool_depth hr with h | h
  · subst r
    exact ha
  · exact h

theorem pool_iff_nil_of_depth_zero {a r : Diagram} (ha : a.depth = 0) :
    Pool a r ↔ r = .nil := by
  constructor
  · intro hr
    rcases pool_depth hr with h | h
    · exact h
    · omega
  · intro h
    subst r
    exact nil_mem a

/-- At depth zero not even a nil-labelled edge occurs in an actual descendant:
the extra nil member of the abstract pool must not be confused with an edge. -/
theorem descendant_rows_false_of_depth_zero {a b : Diagram}
    (ha : a.depth = 0) (hab : Reach Step a b) : AllRows (fun _ => False) b.toGraph := by
  intro c hc e he
  have hh := Diagram.row_depth_lt hc he
  have hd := reach_depth_le hab
  omega

theorem reach_standard {a b : Diagram} (ha : Standard (.finite a))
    (hab : Reach Step a b) : Standard (.finite b) :=
  reach_preserves .nil fs (fun b => Standard (.finite b))
    (fun _ hb n => Standard.child hb n) hab ha

theorem pool_standard {a r : Diagram} (ha : Standard (.finite a)) (hr : Pool a r) :
    Standard (.finite r) := by
  rcases hr with h | ⟨old, ho, hor⟩
  · subst r
    exact standard_nil
  · exact reach_standard (directRow_standard ha ho) hor

theorem package_lt {a row low : Diagram} (ha : Standard (.finite a)) (hr : Pool a row)
    {b : Nat} (hl : low ∈ rowPackage row b) : cmp low row = .lt :=
  Omega3ColumnDecrease.rowPackage_lt (pool_standard ha hr) hl

abbrev RowLt (a b : Diagram) : Prop := cmp a b = .lt

/-- An accessible standard ancestor gives a well-founded comparison on its
own actual descendant cone. No other seed is required to be accessible. -/
theorem descendants_wellFounded {old : Diagram} (ho : Standard (.finite old))
    (hAcc : Acc Step old) :
    WellFounded (FiniteUnionWellFounded.Restricted RowLt (Reach Step old)) := by
  let P : Graph Diagram → Prop := fun g => Reach Step old (Diagram.ofGraph g)
  have closed : ∀ {g h}, P g → Omega3WellOrderingReduction.GraphStep h g → P h :=
    fun {_ _} hg hgh => hg.trans (.single (Omega3WellOrderingReduction.step_ofGraph hgh))
  have hw : WellFounded (fun g h : {g : Graph Diagram // P g} =>
      graphCompare cmp g.val h.val = .lt) := by
    apply ColumnReachability.covered_domain_wellFounded cmp rowPackage @closed
      (fun _ => old.toGraph)
    · intro n
      change Reach Step old (Diagram.ofGraph old.toGraph)
      rw [Diagram.ofGraph_toGraph]
      exact .refl _
    · intro g hg
      exact ⟨0, by simpa only [Diagram.toGraph_ofGraph] using
        Omega3WellOrderingReduction.reach_toGraph hg⟩
    · exact fun _ => Omega3WellOrderingReduction.graph_accessible hAcc
    · exact fun _ => Reach.refl _
    · exact fun _ _ _ hab hbc => Comparison.graphCompare_lt_trans cmp
        Omega3Comparison.cmp_eq_iff Omega3Comparison.cmp_lt_trans hab hbc
    · exact fun g _ => Comparison.graphCompare_lt_irrefl cmp Omega3Comparison.cmp_eq_iff g
    · intro g h hg hgh
      exact Omega3WellOrderingReduction.graph_standard_step_lt (reach_standard ho hg) hgh
  let f : {r : Diagram // Reach Step old r} → {g : Graph Diagram // P g} :=
    fun r => ⟨r.val.toGraph, by
      change Reach Step old (Diagram.ofGraph r.val.toGraph)
      rw [Diagram.ofGraph_toGraph]
      exact r.property⟩
  refine ⟨fun r => ?_⟩
  apply Subrelation.accessible (r := fun r s : {r : Diagram // Reach Step old r} =>
    graphCompare cmp (f r).val (f s).val = .lt)
  · intro r s hrs
    exact (Omega3Comparison.cmp_eq_graphCompare r.val s.val) ▸ hrs
  · exact InvImage.accessible f (hw.apply (f r))

/-- The pool is a finite union of individually well-founded cones plus nil.
The assumptions are accessibility of the finitely many direct rows only. -/
theorem pool_wellFounded {a : Diagram} (ha : Standard (.finite a))
    (rowAcc : ∀ old ∈ directRows a, Acc Step old) :
    WellFounded (FiniteUnionWellFounded.Restricted RowLt (Pool a)) := by
  have hcones : WellFounded (FiniteUnionWellFounded.Restricted RowLt
      (fun r => ∃ old ∈ directRows a, Reach Step old r)) :=
    FiniteUnionWellFounded.indexed_list_union RowLt (@Omega3Comparison.cmp_lt_trans)
      (directRows a) (Reach Step)
      (fun old ho => descendants_wellFounded (directRow_standard ha ho) (rowAcc old ho))
  exact FiniteUnionWellFounded.union RowLt (@Omega3Comparison.cmp_lt_trans)
    (fun r => r = .nil) (fun r => ∃ old ∈ directRows a, Reach Step old r)
    (FiniteUnionWellFounded.singleton RowLt Omega3Comparison.cmp_irrefl .nil) hcones

#print axioms descendant_rows
#print axioms pool_depth
#print axioms descendants_wellFounded
#print axioms pool_wellFounded

end OrdinalFormal.Omega3RowPool
