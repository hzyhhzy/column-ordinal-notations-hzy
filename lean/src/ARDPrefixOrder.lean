import OrdinalFormal.Reachability

/-! The standard-domain order bridge, independent of frozen-row column rules.
These are structural theorems: accessibility and strict decrease are explicit
inputs, supplied by the ARD semantic and executable-rule proofs in the final file. -/

namespace OrdinalFormal.PrefixOrder

universe u
variable {α : Type u} {step lt : α → α → Prop} {P : α → Prop}
set_option autoImplicit false

theorem lift_reach
    (closed : ∀ {a b}, P a → step b a → P b)
    {a b : α} (h : Reach step a b) (ha : P a) (hb : P b) :
    Reach (fun y x : {v : α // P v} => step y.val x.val) ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction h with
  | refl => exact .refl _
  | cons h _ ih => exact .cons h (ih (closed ha h) hb)

theorem restricted_childJoin
    (closed : ∀ {a b}, P a → step b a → P b) (join : ChildJoin step) :
    ChildJoin (fun y x : {v : α // P v} => step y.val x.val) := by
  intro a b c hab hac
  obtain ⟨d, hda, hdb, hdc⟩ := join hab hac
  have hd := closed a.property hda
  exact ⟨⟨d, hd⟩, hda, lift_reach @closed hdb hd b.property,
    lift_reach @closed hdc hd c.property⟩

theorem covered_total
    (closed : ∀ {a b}, P a → step b a → P b)
    (seed : Nat → α) (seedIn : ∀ n, P (seed n))
    (covered : ∀ g, P g → SeedDomain (Step := step) seed g)
    (join : ChildJoin step)
    (seedAcc : ∀ n, Acc step (seed n))
    (seedNested : ∀ n, Reach step (seed (n + 1)) (seed n))
    (orderTrans : ∀ {a b c}, P a → P b → P c → lt a b → lt b c → lt a c)
    (decreases : ∀ {a b}, P a → step b a → lt b a)
    {a b : α} (ha : P a) (hb : P b) : a = b ∨ lt a b ∨ lt b a := by
  obtain ⟨n, hna, hnb⟩ := seed_domain_common_ancestor seed seedNested
    (covered a ha) (covered b hb)
  have hacc : Acc (fun y x : {v : α // P v} => step y.val x.val)
      ⟨seed n, seedIn n⟩ :=
    InvImage.accessible
      (a := (⟨seed n, seedIn n⟩ : {v : α // P v})) (r := step)
      (fun g : {v : α // P v} => g.val) (seedAcc n)
  have transRestricted : ∀ {a b c : {v : α // P v}},
      lt a.val b.val → lt b.val c.val → lt a.val c.val :=
    fun {a b c} => orderTrans a.property b.property c.property
  have decreaseRestricted : ∀ {a b : {v : α // P v}},
      step b.val a.val → lt b.val a.val := fun {a _} h => decreases a.property h
  have h := descendants_lt_total @transRestricted @decreaseRestricted
    (restricted_childJoin @closed join) hacc
    (lift_reach @closed hna (seedIn n) ha) (lift_reach @closed hnb (seedIn n) hb)
  cases h with
  | inl heq => exact .inl (congrArg Subtype.val heq)
  | inr hlt => exact .inr hlt

theorem covered_wellFounded
    (closed : ∀ {a b}, P a → step b a → P b)
    (seed : Nat → α) (seedIn : ∀ n, P (seed n))
    (covered : ∀ g, P g → SeedDomain (Step := step) seed g)
    (join : ChildJoin step)
    (seedAcc : ∀ n, Acc step (seed n))
    (seedNested : ∀ n, Reach step (seed (n + 1)) (seed n))
    (orderTrans : ∀ {a b c}, P a → P b → P c → lt a b → lt b c → lt a c)
    (orderIrrefl : ∀ a, P a → ¬ lt a a)
    (decreases : ∀ {a b}, P a → step b a → lt b a) :
    WellFounded (fun x y : {v : α // P v} => lt x.val y.val) := by
  let r := fun y x : {v : α // P v} => step y.val x.val
  have transRestricted : ∀ {a b c : {v : α // P v}},
      lt a.val b.val → lt b.val c.val → lt a.val c.val :=
    fun {a b c} => orderTrans a.property b.property c.property
  have decreaseRestricted : ∀ {a b : {v : α // P v}},
      r b a → lt b.val a.val := fun {a _} h => decreases a.property h
  have irreflRestricted : ∀ a : {v : α // P v}, ¬ lt a.val a.val :=
    fun a => orderIrrefl a.val a.property
  have hjoin : ChildJoin r := restricted_childJoin @closed join
  refine ⟨fun x => ?_⟩
  apply Subrelation.accessible (r := Relation.TransGen r)
  · intro a b hab
    obtain ⟨n, hna, hnb⟩ := seed_domain_common_ancestor seed seedNested
      (covered a.val a.property) (covered b.val b.property)
    have hacc : Acc r ⟨seed n, seedIn n⟩ :=
      InvImage.accessible
        (a := (⟨seed n, seedIn n⟩ : {v : α // P v})) (r := step)
        (fun g : {v : α // P v} => g.val) (seedAcc n)
    exact descendants_lt_implies_transGen @transRestricted @decreaseRestricted
      irreflRestricted hjoin hacc
      (lift_reach @closed hna (seedIn n) a.property)
      (lift_reach @closed hnb (seedIn n) b.property) hab
  · obtain ⟨n, hnx⟩ := covered x.val x.property
    exact (InvImage.accessible (fun g : {v : α // P v} => g.val)
      (Reach.accessible (seedAcc n) hnx)).transGen

#print axioms covered_total
#print axioms covered_wellFounded

end OrdinalFormal.PrefixOrder
