import IPDSemanticWellFounded
import IPDDecrease
import IPDSeeds
import ARDPrefixOrder

/-! Final actual standard-domain column-order theorem. ARDPrefixOrder contains
only the generic reachability/column-prefix bridge, not any ARD semantics.
Every premise of that bridge is instantiated by proved IPD results here. -/

namespace IPD
set_option autoImplicit false
open OrdinalFormal

def Standard (G : Graph) : Prop := SeedDomain (Step := Step) seed G
abbrev StandardDiagram := {G : Graph // Standard G}
def StandardLt (a b : StandardDiagram) : Prop := GraphLt a.val b.val

theorem standard_seed (n : Nat) : Standard (seed n) := ⟨n,Reach.refl _⟩

theorem standard_closed {G H : Graph} (hg : Standard G) (hs : Step H G) : Standard H := by
  obtain ⟨n,hn⟩ := hg
  exact ⟨n,hn.trans (Reach.single hs)⟩

theorem standard_invariant (P : Graph → Prop) (hseed : ∀ n, P (seed n))
    (hstep : ∀ {G H}, P G → Step H G → P H) {G : Graph} (hg : Standard G) : P G := by
  obtain ⟨n,hn⟩ := hg
  have hall : ∀ {a b}, Reach Step a b → P a → P b := by
    intro a b h
    induction h with
    | refl => exact id
    | cons h _ ih => exact fun ha => ih (hstep ha h)
  exact hall hn (hseed n)

theorem standard_valid {G : Graph} (h : Standard G) : Valid G :=
  standard_invariant Valid seed_valid (fun hv hs => by
    obtain ⟨_,n,rfl⟩ := hs
    exact expand_valid hv n) h

theorem standard_canonical {G : Graph} (h : Standard G) : Canonical G :=
  standard_invariant Canonical seed_canonical (fun hc hs => by
    obtain ⟨_,n,rfl⟩ := hs
    exact expand_canonical _ hc n) h

theorem standard_step_lt {G H : Graph} (hg : Standard G) (hs : Step H G) : GraphLt H G := by
  obtain ⟨hn,n,rfl⟩ := hs
  exact expand_lt (standard_valid hg) (standard_canonical hg) hn n

theorem childJoin : ChildJoin Step := by
  apply childJoin_of_list_fs expand
  · intro G
    rw [expand_zero,List.dropLast_eq_take]
  · exact fun G _ _ h => expand_prefix G h

theorem seed_reachable (n : Nat) : Reach Step (seed (n+1)) (seed n) :=
  Reach.single ⟨seed_nonempty (n+1),1,seed_succ_one n⟩

/-- No well-ordering, accessibility, reflection, supply or large-cardinal
premise remains in this theorem. It uses the actual parent-first column order. -/
theorem standard_wellFounded : WellFounded StandardLt :=
  PrefixOrder.covered_wellFounded @standard_closed seed standard_seed
    (fun _ hg => hg) childJoin (fun n => Semantics.valid_accessible _ (seed_valid n)) seed_reachable
    (fun _ _ _ hab hbc => graphLt_trans hab hbc)
    (fun G _ => graphLt_irrefl G) @standard_step_lt

theorem standard_total (a b : StandardDiagram) : a = b ∨ StandardLt a b ∨ StandardLt b a := by
  have h := PrefixOrder.covered_total (lt := GraphLt) @standard_closed seed standard_seed
    (fun _ hg => hg) childJoin (fun n => Semantics.valid_accessible _ (seed_valid n)) seed_reachable
    (fun _ _ _ hab hbc => graphLt_trans hab hbc) @standard_step_lt a.property b.property
  rcases h with h | h | h
  · exact .inl (Subtype.ext h)
  · exact .inr (.inl h)
  · exact .inr (.inr h)

/-- `none` is the external greatest TOP; `some G` is a standard finite diagram. -/
abbrev StandardTerm := Option StandardDiagram
def TermLt : StandardTerm → StandardTerm → Prop := AdjoinTopLt StandardLt

theorem term_wellFounded : WellFounded TermLt := wellFounded_adjoinTop standard_wellFounded

theorem term_total (a b : StandardTerm) : a = b ∨ TermLt a b ∨ TermLt b a := by
  cases a with
  | none =>
    cases b with
    | none => exact .inl rfl
    | some b => exact .inr (.inr True.intro)
  | some a =>
    cases b with
    | none => exact .inr (.inl True.intro)
    | some b =>
      rcases standard_total a b with h | h | h
      · exact .inl (congrArg some h)
      · exact .inr (.inl h)
      · exact .inr (.inr h)

end IPD

#print axioms IPD.standard_wellFounded
#print axioms IPD.standard_total
#print axioms IPD.term_wellFounded
