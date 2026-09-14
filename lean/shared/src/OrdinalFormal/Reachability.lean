import Std

/-!
# Common-ancestor comparison, independently of ordinal semantics

`Step small large` is a strict fundamental-sequence step. `Reach Step large small`
is a finite, possibly empty, path in the downward direction. The only branching
hypothesis says that two children have a common ancestor which is itself a child
of their parent. Fundamental sequences with nested prefix values supply it.

This module does NOT supply accessibility or verify any concrete notation's rules.
-/

set_option maxHeartbeats 500000
set_option maxRecDepth 2048

namespace OrdinalFormal

universe u
variable {α : Type u}

/-- Finite downward reachability; the first argument is the ancestor. -/
inductive Reach (Step : α → α → Prop) : α → α → Prop where
  | refl (a : α) : Reach Step a a
  | cons {a b c : α} : Step b a → Reach Step b c → Reach Step a c

namespace Reach
variable {Step : α → α → Prop} {a b c : α}

theorem single (h : Step b a) : Reach Step a b := .cons h (.refl b)

theorem trans (hab : Reach Step a b) (hbc : Reach Step b c) : Reach Step a c := by
  induction hab with
  | refl => exact hbc
  | cons h _ ih => exact .cons h (ih hbc)

theorem accessible (ha : Acc Step a) (hab : Reach Step a b) : Acc Step b := by
  induction hab with
  | refl => exact ha
  | cons h _ ih => exact ih (ha.inv h)

/-- A nonempty reachability path is in Lean's transitive closure, with reversed arguments. -/
theorem eq_or_transGen (hab : Reach Step a b) : a = b ∨ Relation.TransGen Step b a := by
  induction hab with
  | refl => exact .inl rfl
  | @cons a d b h _ ih =>
    cases ih with
    | inl heq => subst b; exact .inr (.single h)
    | inr hp => exact .inr (.tail hp h)

end Reach

/-- Two children are descendants of another child of their parent. -/
def ChildJoin (Step : α → α → Prop) : Prop :=
  ∀ {a b c}, Step b a → Step c a →
    ∃ d, Step d a ∧ Reach Step d b ∧ Reach Step d c

/-- Accessibility plus the child-join property makes every descendant cone comparable by reachability. -/
theorem descendants_reach_comparable {Step : α → α → Prop}
    (join : ChildJoin Step) {a : α} (ha : Acc Step a) :
    ∀ {b c}, Reach Step a b → Reach Step a c →
      Reach Step b c ∨ Reach Step c b := by
  induction ha with
  | intro a _ ih =>
    intro b c hab hac
    cases hab with
    | refl => exact .inl hac
    | @cons _ d _ had hdb =>
      cases hac with
      | refl => exact .inr (.cons had hdb)
      | @cons _ e _ hae hec =>
        obtain ⟨f, haf, hfd, hfe⟩ := join had hae
        exact ih f haf (hfd.trans hdb) (hfe.trans hec)

section Ordered
variable {Step lt : α → α → Prop}
variable (transLt : ∀ {a b c}, lt a b → lt b c → lt a c)
variable (decreases : ∀ {a b}, Step b a → lt b a)
include transLt decreases

theorem Reach.eq_or_lt {a b : α} (hab : Reach Step a b) : a = b ∨ lt b a := by
  induction hab with
  | refl => exact .inl rfl
  | @cons a d b h _ ih =>
    cases ih with
    | inl heq => subst b; exact .inr (decreases h)
    | inr hbd => exact .inr (transLt hbd (decreases h))

/-- Totality is derived on the cone; no global total-order hypothesis is needed. -/
theorem descendants_lt_total (join : ChildJoin Step) {a : α} (ha : Acc Step a)
    {b c : α} (hab : Reach Step a b) (hac : Reach Step a c) :
    b = c ∨ lt b c ∨ lt c b := by
  cases descendants_reach_comparable join ha hab hac with
  | inl hbc =>
    cases hbc.eq_or_lt @transLt @decreases with
    | inl heq => exact .inl heq
    | inr hlt => exact .inr (.inr hlt)
  | inr hcb =>
    cases hcb.eq_or_lt @transLt @decreases with
    | inl heq => exact .inl heq.symm
    | inr hlt => exact .inr (.inl hlt)

variable (irreflLt : ∀ a, ¬ lt a a)
include irreflLt

theorem descendants_lt_implies_reach (join : ChildJoin Step) {a : α} (ha : Acc Step a)
    {b c : α} (hab : Reach Step a b) (hac : Reach Step a c) (hbc : lt b c) :
    Reach Step c b := by
  cases descendants_reach_comparable join ha hab hac with
  | inr hcb => exact hcb
  | inl hcb =>
    cases hcb.eq_or_lt @transLt @decreases with
    | inl heq => subst c; exact False.elim (irreflLt b hbc)
    | inr hcb => exact False.elim (irreflLt b (transLt hbc hcb))

theorem descendants_lt_implies_transGen (join : ChildJoin Step) {a : α} (ha : Acc Step a)
    {b c : α} (hab : Reach Step a b) (hac : Reach Step a c) (hbc : lt b c) :
    Relation.TransGen Step b c := by
  have hp := descendants_lt_implies_reach @transLt @decreases irreflLt join ha hab hac hbc
  cases hp.eq_or_transGen with
  | inr ht => exact ht
  | inl heq => subst c; exact False.elim (irreflLt b hbc)

/-- The actual comparison, restricted to one accessible ancestor's descendants, is well-founded. -/
theorem descendants_lt_wellFounded (join : ChildJoin Step) {a : α} (ha : Acc Step a) :
    WellFounded (fun b c : {x : α // Reach Step a x} => lt b.val c.val) := by
  refine ⟨fun b => ?_⟩
  apply Subrelation.accessible (r := fun b c : {x : α // Reach Step a x} =>
    Relation.TransGen Step b.val c.val)
  · intro x y hxy
    exact descendants_lt_implies_transGen @transLt @decreases irreflLt join ha
      x.property y.property hxy
  · exact InvImage.accessible (fun x : {x : α // Reach Step a x} => x.val)
      (Reach.accessible ha b.property).transGen

/-- A reachable smaller ancestor's cone is an initial segment of the larger cone. -/
theorem descendant_cone_initial (join : ChildJoin Step) {a d : α}
    (ha : Acc Step a) (had : Reach Step a d)
    {b c : α} (hab : Reach Step a b) (hdc : Reach Step d c) (hbc : lt b c) :
    Reach Step d b :=
  hdc.trans (descendants_lt_implies_reach @transLt @decreases irreflLt join ha
    hab (had.trans hdc) hbc)

end Ordered

/-- The zero self-loop is explicitly excluded. -/
def FSStep (zero : α) (fs : α → Nat → α) (b a : α) : Prop :=
  a ≠ zero ∧ ∃ n, fs a n = b

/-- Prefix reachability of fundamental-sequence values yields the precise branching hypothesis. -/
theorem childJoin_of_nested_fs (zero : α) (fs : α → Nat → α)
    (nested : ∀ a i j, i ≤ j → Reach (FSStep zero fs) (fs a j) (fs a i)) :
    ChildJoin (FSStep zero fs) := by
  intro a b c hb hc
  obtain ⟨ha, i, hi⟩ := hb
  obtain ⟨_, j, hj⟩ := hc
  refine ⟨fs a (max i j), ⟨ha, max i j, rfl⟩, ?_, ?_⟩
  · simpa [hi] using nested a i (max i j) (Nat.le_max_left i j)
  · simpa [hj] using nested a j (max i j) (Nat.le_max_right i j)

/-- Repeated last-column deletion reaches every full list prefix. -/
theorem reach_of_list_prefix {Column : Type u}
    {Step : List Column → List Column → Prop}
    (delete : ∀ xs, xs ≠ [] → Step xs.dropLast xs)
    {xs ys : List Column} (hprefix : xs.IsPrefix ys) : Reach Step ys xs := by
  obtain ⟨suffix, rfl⟩ := hprefix
  have go : ∀ tail left : List Column, Reach Step (left ++ tail) left := by
    intro tail
    induction tail with
    | nil =>
      intro left
      simpa using (Reach.refl left : Reach Step left left)
    | cons c tail ih =>
      intro left
      have htail : Reach Step (left ++ c :: tail) (left ++ [c]) := by
        simpa [List.append_assoc] using ih (left ++ [c])
      have hlast : Step left (left ++ [c]) := by
        simpa using delete (left ++ [c]) (by simp)
      exact htail.trans (.single hlast)
  exact go suffix xs

/-- A direct adapter for column-list fundamental sequences with deletion at zero and full prefixes. -/
theorem childJoin_of_list_fs {Column : Type u}
    (fs : List Column → Nat → List Column)
    (zeroIndex : ∀ xs, fs xs 0 = xs.dropLast)
    (prefixes : ∀ xs i j, i ≤ j → (fs xs i).IsPrefix (fs xs j)) :
    ChildJoin (FSStep [] fs) := by
  apply childJoin_of_nested_fs [] fs
  intro xs i j hij
  apply reach_of_list_prefix (hprefix := prefixes xs i j hij)
  intro ys hys
  exact ⟨hys, 0, zeroIndex ys⟩

section Seeds
variable {Step : α → α → Prop} (seed : Nat → α)

/-- The union of the finite descendant cones of the seeds. -/
def SeedDomain (x : α) : Prop := ∃ n, Reach Step (seed n) x

theorem seed_reach_of_le
    (nested : ∀ n, Reach Step (seed (n + 1)) (seed n))
    {i j : Nat} (hij : i ≤ j) : Reach Step (seed j) (seed i) := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hij
  induction d with
  | zero => simpa using (Reach.refl (seed i) : Reach Step (seed i) (seed i))
  | succ d ih =>
    exact (nested (i + d)).trans (ih (Nat.le_add_right i d))

theorem seed_domain_common_ancestor
    (nested : ∀ n, Reach Step (seed (n + 1)) (seed n))
    {x y : α} (hx : SeedDomain (Step := Step) seed x)
    (hy : SeedDomain (Step := Step) seed y) :
    ∃ n, Reach Step (seed n) x ∧ Reach Step (seed n) y := by
  obtain ⟨i, hix⟩ := hx
  obtain ⟨j, hjy⟩ := hy
  exact ⟨max i j,
    (seed_reach_of_le seed nested (Nat.le_max_left i j)).trans hix,
    (seed_reach_of_le seed nested (Nat.le_max_right i j)).trans hjy⟩

variable {lt : α → α → Prop}
variable (transLt : ∀ {a b c}, lt a b → lt b c → lt a c)
variable (decreases : ∀ {a b}, Step b a → lt b a)
variable (irreflLt : ∀ a, ¬ lt a a)
variable (join : ChildJoin Step)
variable (accessible : ∀ n, Acc Step (seed n))
variable (nested : ∀ n, Reach Step (seed (n + 1)) (seed n))
include transLt decreases join accessible nested

/-- Comparability on the entire union is derived from reachable seed nesting. -/
theorem seed_domain_lt_total
    {x y : α} (hx : SeedDomain (Step := Step) seed x)
    (hy : SeedDomain (Step := Step) seed y) :
    x = y ∨ lt x y ∨ lt y x := by
  obtain ⟨n, hnx, hny⟩ := seed_domain_common_ancestor seed nested hx hy
  exact descendants_lt_total @transLt @decreases join (accessible n) hnx hny

include irreflLt

theorem seed_domain_lt_implies_transGen
    {x y : α} (hx : SeedDomain (Step := Step) seed x)
    (hy : SeedDomain (Step := Step) seed y) (hxy : lt x y) :
    Relation.TransGen Step x y := by
  obtain ⟨n, hnx, hny⟩ := seed_domain_common_ancestor seed nested hx hy
  exact descendants_lt_implies_transGen @transLt @decreases irreflLt join
    (accessible n) hnx hny hxy

/-- No global step-WF premise: accessibility of each seed is enough for the union. -/
theorem seed_domain_lt_wellFounded :
    WellFounded (fun x y : {x : α // SeedDomain (Step := Step) seed x} =>
      lt x.val y.val) := by
  refine ⟨fun x => ?_⟩
  apply Subrelation.accessible
    (r := fun x y : {x : α // SeedDomain (Step := Step) seed x} =>
      Relation.TransGen Step x.val y.val)
  · intro a b hab
    exact seed_domain_lt_implies_transGen seed @transLt @decreases irreflLt join
      accessible nested a.property b.property hab
  · obtain ⟨n, hnx⟩ := x.property
    exact InvImage.accessible
      (fun x : {x : α // SeedDomain (Step := Step) seed x} => x.val)
      (Reach.accessible (accessible n) hnx).transGen

/-- Earlier seed cones are genuinely initial segments, not merely nested subsets. -/
theorem seed_cones_initial {i j : Nat} (hij : i ≤ j)
    {x y : α} (hjx : Reach Step (seed j) x)
    (hiy : Reach Step (seed i) y) (hxy : lt x y) :
    Reach Step (seed i) x :=
  descendant_cone_initial @transLt @decreases irreflLt join (accessible j)
    (seed_reach_of_le seed nested hij) hjx hiy hxy

end Seeds

/-- `none` is an adjoined maximum; `some x` is an old element. -/
def AdjoinTopLt (lt : α → α → Prop) : Option α → Option α → Prop
  | some a, some b => lt a b
  | some _, none => True
  | none, _ => False

theorem acc_adjoinTop_some {lt : α → α → Prop} {a : α} (ha : Acc lt a) :
    Acc (AdjoinTopLt lt) (some a) := by
  induction ha with
  | intro a _ ih =>
    refine Acc.intro (some a) ?_
    intro b hba
    cases b with
    | none => exact False.elim hba
    | some b => exact ih b hba

theorem wellFounded_adjoinTop {lt : α → α → Prop} (hwf : WellFounded lt) :
    WellFounded (AdjoinTopLt lt) := by
  refine ⟨fun a => ?_⟩
  cases a with
  | some a => exact acc_adjoinTop_some (hwf.apply a)
  | none =>
    refine Acc.intro none ?_
    intro b hba
    cases b with
    | none => exact False.elim hba
    | some b => exact acc_adjoinTop_some (hwf.apply b)

end OrdinalFormal
