import ARD2DemandCore
/-! The dynamic four-ordinal relation is constructed by well-founded recursion. -/
namespace ARD2Demand
universe u
noncomputable def read (s : Stage.{u})
    (previous : ∀ t, Earlier t s → Label.{u} → Prop) : Rel.{u} := by
  classical
  exact fun k theta a b => if h : Earlier (b,k,theta) s then previous (b,k,theta) h a else False
noncomputable def step (s : Stage.{u})
    (previous : ∀ t, Earlier t s → Label.{u} → Prop) : Label.{u} → Prop := Rule (read s previous) s
noncomputable def value : Stage.{u} → Label.{u} → Prop := earlier_wellFounded.fix step
noncomputable def relation : Rel.{u} := fun k theta a b => value (b,k,theta) a
theorem value_eq (s : Stage.{u}) : value s = step s (fun t _ => value t) :=
  WellFounded.fix_eq earlier_wellFounded step s
theorem read_agrees (s : Stage.{u}) : AgreeEarlier s (read s (fun t _ => value t)) relation := by
  intro k theta a b h
  simp [read,h,relation]
theorem relation_iff (k theta a b : Label.{u}) :
    relation k theta a b ↔ Rule relation (b,k,theta) a := by
  change value (b,k,theta) a ↔ _
  rw [value_eq]
  exact rule_congr (read_agrees (b,k,theta)) a
end ARD2Demand
#print axioms ARD2Demand.relation_iff


