import OrdinalFormal.Columns
import OrdinalFormal.Reachability

/-!
# Actual column expansion: structural reachability and conditional order bridge

Unconditionally proved: zero has no strict outgoing step, every full prefix is
reachable by last-column deletion, and the actual `Columns.expand` has ChildJoin.

The well-founded comparison theorems are CONDITIONAL. They still require seed
accessibility (the semantic part), reachable seed nesting, and strict comparison
laws including decrease on the generated domain. In particular, they do not
assume decrease on all malformed hand-written graphs, nor assert final RPD/LRD WO.
-/

set_option maxHeartbeats 500000
set_option maxRecDepth 2048

namespace OrdinalFormal.ColumnReachability

open Columns
universe u
variable {Row : Type u}

abbrev Step (cmp : Row → Row → Ordering) (package : Package Row) :
    Graph Row → Graph Row → Prop := FSStep [] (expand cmp package)

def CompareLt (cmp : Row → Row → Ordering) (a b : Graph Row) : Prop :=
  graphCompare cmp a b = .lt

theorem zero_no_step (cmp : Row → Row → Ordering) (package : Package Row)
    (g : Graph Row) : ¬ Step cmp package g [] := fun h => h.1 rfl

theorem delete_step (cmp : Row → Row → Ordering) (package : Package Row)
    (g : Graph Row) (hg : g ≠ []) : Step cmp package g.dropLast g := by
  refine ⟨hg, 0, ?_⟩
  rw [expand_zero, List.dropLast_eq_take]

theorem prefix_reachable (cmp : Row → Row → Ordering) (package : Package Row)
    {a b : Graph Row} (hab : a.IsPrefix b) : Reach (Step cmp package) b a :=
  reach_of_list_prefix (delete_step cmp package) hab

theorem childJoin (cmp : Row → Row → Ordering) (package : Package Row) :
    ChildJoin (Step cmp package) := by
  apply childJoin_of_list_fs (expand cmp package)
  · intro g
    rw [expand_zero, List.dropLast_eq_take]
  · intro g i j hij
    exact expand_prefix cmp package g hij

section Restricted
variable (cmp : Row → Row → Ordering) (package : Package Row)
variable {P : Graph Row → Prop}
variable (closed : ∀ {a b}, P a → Step cmp package b a → P b)
include closed

/-- Lift an actual path into any expansion-closed domain. -/
theorem lift_reach {a b : Graph Row} (h : Reach (Step cmp package) a b)
    (ha : P a) (hb : P b) :
    Reach (fun y x : {g : Graph Row // P g} => Step cmp package y.val x.val)
      ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction h with
  | refl => exact .refl _
  | cons h _ ih => exact .cons h (ih (closed ha h) hb)

theorem restricted_childJoin :
    ChildJoin (fun y x : {g : Graph Row // P g} => Step cmp package y.val x.val) := by
  intro a b c hab hac
  obtain ⟨d, hda, hdb, hdc⟩ := childJoin cmp package hab hac
  have hd := closed a.property hda
  exact ⟨⟨d, hd⟩, hda,
    lift_reach cmp package @closed hdb hd b.property,
    lift_reach cmp package @closed hdc hd c.property⟩

/-- The same closed, covered domain has a total comparison once steps decrease. -/
theorem covered_domain_total
    (seed : Nat → Graph Row)
    (seedIn : ∀ n, P (seed n))
    (covered : ∀ g, P g → SeedDomain (Step := Step cmp package) seed g)
    (seedAcc : ∀ n, Acc (Step cmp package) (seed n))
    (seedNested : ∀ n, Reach (Step cmp package) (seed (n + 1)) (seed n))
    (orderTrans : ∀ {a b c}, P a → P b → P c →
      CompareLt cmp a b → CompareLt cmp b c → CompareLt cmp a c)
    (decreases : ∀ {a b}, P a → Step cmp package b a → CompareLt cmp b a)
    {a b : Graph Row} (ha : P a) (hb : P b) :
    a = b ∨ CompareLt cmp a b ∨ CompareLt cmp b a := by
  obtain ⟨n, hna, hnb⟩ := seed_domain_common_ancestor seed seedNested
    (covered a ha) (covered b hb)
  have hacc : Acc
      (fun y x : {g : Graph Row // P g} => Step cmp package y.val x.val)
      ⟨seed n, seedIn n⟩ :=
    InvImage.accessible
      (a := (⟨seed n, seedIn n⟩ : {g : Graph Row // P g})) (r := Step cmp package)
      (fun g : {g : Graph Row // P g} => g.val) (seedAcc n)
  have transRestricted : ∀ {a b c : {g : Graph Row // P g}},
      CompareLt cmp a.val b.val → CompareLt cmp b.val c.val → CompareLt cmp a.val c.val :=
    fun {a b c} => orderTrans a.property b.property c.property
  have decreaseRestricted : ∀ {a b : {g : Graph Row // P g}},
      Step cmp package b.val a.val → CompareLt cmp b.val a.val :=
    fun {a _} h => decreases a.property h
  have h := descendants_lt_total @transRestricted @decreaseRestricted
    (restricted_childJoin cmp package @closed) hacc
    (lift_reach cmp package @closed hna (seedIn n) ha)
    (lift_reach cmp package @closed hnb (seedIn n) hb)
  cases h with
  | inl heq => exact .inl (congrArg Subtype.val heq)
  | inr hlt => exact .inr hlt

/-- A domain version whose order/decrease hypotheses are needed only inside P.
`covered` prevents accidentally claiming that all syntactically valid graphs are WO. -/
theorem covered_domain_wellFounded
    (seed : Nat → Graph Row)
    (seedIn : ∀ n, P (seed n))
    (covered : ∀ g, P g → SeedDomain (Step := Step cmp package) seed g)
    (seedAcc : ∀ n, Acc (Step cmp package) (seed n))
    (seedNested : ∀ n, Reach (Step cmp package) (seed (n + 1)) (seed n))
    (orderTrans : ∀ {a b c}, P a → P b → P c →
      CompareLt cmp a b → CompareLt cmp b c → CompareLt cmp a c)
    (orderIrrefl : ∀ a, P a → ¬ CompareLt cmp a a)
    (decreases : ∀ {a b}, P a → Step cmp package b a → CompareLt cmp b a) :
    WellFounded (fun x y : {g : Graph Row // P g} => CompareLt cmp x.val y.val) := by
  let r := fun y x : {g : Graph Row // P g} => Step cmp package y.val x.val
  have transRestricted : ∀ {a b c : {g : Graph Row // P g}},
      CompareLt cmp a.val b.val → CompareLt cmp b.val c.val → CompareLt cmp a.val c.val :=
    fun {a b c} => orderTrans a.property b.property c.property
  have decreaseRestricted : ∀ {a b : {g : Graph Row // P g}},
      r b a → CompareLt cmp b.val a.val := fun {a _} h => decreases a.property h
  have irreflRestricted : ∀ a : {g : Graph Row // P g}, ¬ CompareLt cmp a.val a.val :=
    fun a => orderIrrefl a.val a.property
  have hjoin : ChildJoin r := restricted_childJoin cmp package @closed
  refine ⟨fun x => ?_⟩
  apply Subrelation.accessible (r := Relation.TransGen r)
  · intro a b hab
    obtain ⟨n, hna, hnb⟩ := seed_domain_common_ancestor seed seedNested
      (covered a.val a.property) (covered b.val b.property)
    have hacc : Acc r ⟨seed n, seedIn n⟩ :=
      InvImage.accessible
        (a := (⟨seed n, seedIn n⟩ : {g : Graph Row // P g})) (r := Step cmp package)
        (fun g : {g : Graph Row // P g} => g.val) (seedAcc n)
    exact descendants_lt_implies_transGen @transRestricted @decreaseRestricted
      irreflRestricted hjoin hacc
      (lift_reach cmp package @closed hna (seedIn n) a.property)
      (lift_reach cmp package @closed hnb (seedIn n) b.property) hab
  · obtain ⟨n, hnx⟩ := covered x.val x.property
    exact (InvImage.accessible (fun g : {g : Graph Row // P g} => g.val)
      (Reach.accessible (seedAcc n) hnx)).transGen

end Restricted

/-- The generated seed union is automatically expansion-closed. -/
theorem seed_domain_closed (cmp : Row → Row → Ordering) (package : Package Row)
    (seed : Nat → Graph Row) {a b : Graph Row}
    (ha : SeedDomain (Step := Step cmp package) seed a) (hab : Step cmp package b a) :
    SeedDomain (Step := Step cmp package) seed b := by
  obtain ⟨n, hna⟩ := ha
  exact ⟨n, hna.trans (.single hab)⟩

theorem standard_total
    (cmp : Row → Row → Ordering) (package : Package Row) (seed : Nat → Graph Row)
    (seedAcc : ∀ n, Acc (Step cmp package) (seed n))
    (seedNested : ∀ n, Reach (Step cmp package) (seed (n + 1)) (seed n))
    (orderTrans : ∀ {a b c},
      SeedDomain (Step := Step cmp package) seed a →
      SeedDomain (Step := Step cmp package) seed b →
      SeedDomain (Step := Step cmp package) seed c →
      CompareLt cmp a b → CompareLt cmp b c → CompareLt cmp a c)
    (decreases : ∀ {a b}, SeedDomain (Step := Step cmp package) seed a →
      Step cmp package b a → CompareLt cmp b a)
    {a b : Graph Row}
    (ha : SeedDomain (Step := Step cmp package) seed a)
    (hb : SeedDomain (Step := Step cmp package) seed b) :
    a = b ∨ CompareLt cmp a b ∨ CompareLt cmp b a :=
  covered_domain_total cmp package (@seed_domain_closed _ cmp package seed) seed
    (fun n => ⟨n, .refl _⟩) (fun _ h => h) seedAcc seedNested @orderTrans @decreases ha hb

/-- Conditional bridge for the actual expansion and actual comparison.
Remaining substantive hypotheses are displayed explicitly, not bundled as WO. -/
theorem standard_wellFounded
    (cmp : Row → Row → Ordering) (package : Package Row) (seed : Nat → Graph Row)
    (seedAcc : ∀ n, Acc (Step cmp package) (seed n))
    (seedNested : ∀ n, Reach (Step cmp package) (seed (n + 1)) (seed n))
    (orderTrans : ∀ {a b c},
      SeedDomain (Step := Step cmp package) seed a →
      SeedDomain (Step := Step cmp package) seed b →
      SeedDomain (Step := Step cmp package) seed c →
      CompareLt cmp a b → CompareLt cmp b c → CompareLt cmp a c)
    (orderIrrefl : ∀ a, SeedDomain (Step := Step cmp package) seed a → ¬ CompareLt cmp a a)
    (decreases : ∀ {a b}, SeedDomain (Step := Step cmp package) seed a →
      Step cmp package b a → CompareLt cmp b a) :
    WellFounded (fun x y : {g : Graph Row // SeedDomain (Step := Step cmp package) seed g} =>
      CompareLt cmp x.val y.val) :=
  covered_domain_wellFounded cmp package (@seed_domain_closed _ cmp package seed) seed
    (fun n => ⟨n, .refl _⟩) (fun _ h => h) seedAcc seedNested
    @orderTrans orderIrrefl @decreases

end OrdinalFormal.ColumnReachability
