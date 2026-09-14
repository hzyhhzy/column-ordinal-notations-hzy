import FiniteDemandCore

/-!
# The actual canonical finite-demand relation

Well-founded recursion constructs the relation. Its complete defining equation
and uniqueness are proved, rather than required of a supplied semantic oracle.
The stage output is a predicate on all parent labels simultaneously.

This is a host-Lean construction. Bounded set coding and weak-object-theory
recursion remain separate obligations. Initial supply is not claimed here.
-/

namespace FiniteDemand

universe u v
variable {Row : Type v}

noncomputable def read (rowLt : Row → Row → Prop) (s : Stage.{u} Row)
    (previous : ∀ t, Earlier rowLt t s → Label.{u} → Prop) : Rel.{u} Row := by
  classical
  exact fun k theta a b => if h : Earlier rowLt (b, k, theta) s
    then previous (b, k, theta) h a else False

noncomputable def step (rowLt : Row → Row → Prop) (s : Stage.{u} Row)
    (previous : ∀ t, Earlier rowLt t s → Label.{u} → Prop) : Label.{u} → Prop :=
  Rule rowLt (read rowLt s previous) s

noncomputable def value (rowLt : Row → Row → Prop) (hw : WellFounded rowLt) :
    Stage.{u} Row → Label.{u} → Prop :=
  (earlier_wellFounded rowLt hw).fix (step rowLt)

noncomputable def relation (rowLt : Row → Row → Prop) (hw : WellFounded rowLt) : Rel.{u} Row :=
  fun k theta a b => value rowLt hw (b, k, theta) a

theorem value_eq (rowLt : Row → Row → Prop) (hw : WellFounded rowLt) (s : Stage.{u} Row) :
    value rowLt hw s = step rowLt s (fun t _ => value rowLt hw t) :=
  WellFounded.fix_eq (earlier_wellFounded rowLt hw) (step rowLt) s

/-- The canonical reader agrees with the actual relation at every permitted query. -/
theorem read_agrees (rowLt : Row → Row → Prop) (hw : WellFounded rowLt) (s : Stage.{u} Row) :
    AgreeEarlier rowLt s (read rowLt s (fun t _ => value rowLt hw t)) (relation rowLt hw) := by
  intro k theta a b h
  simp [read, h, relation]

/-- Complete equation of the recursively constructed relation, with no history reader left. -/
theorem relation_iff (rowLt : Row → Row → Prop) (hw : WellFounded rowLt)
    (k : Row) (theta a b : Label.{u}) :
    relation rowLt hw k theta a b ↔ Rule rowLt (relation rowLt hw) (b, k, theta) a := by
  change value rowLt hw (b, k, theta) a ↔ _
  rw [value_eq]
  exact rule_congr (read_agrees rowLt hw (b, k, theta)) a

/-- The full demand equations determine a unique relation; none can be chosen ad hoc. -/
theorem value_unique (rowLt : Row → Row → Prop) (hw : WellFounded rowLt)
    (F : Stage.{u} Row → Label.{u} → Prop)
    (hF : ∀ s a, F s a ↔ Rule rowLt (fun k theta a b => F (b, k, theta) a) s a) :
    F = value rowLt hw := by
  funext s
  induction s using (earlier_wellFounded rowLt hw).induction with
  | h s ih =>
    funext a
    apply propext
    calc
      F s a ↔ Rule rowLt (fun k theta a b => F (b, k, theta) a) s a := hF s a
      _ ↔ Rule rowLt (relation rowLt hw) s a := by
        apply rule_congr
        intro k theta p b ht
        change F (b, k, theta) p ↔ value rowLt hw (b, k, theta) p
        rw [ih (b, k, theta) ht]
      _ ↔ value rowLt hw s a := (relation_iff rowLt hw s.2.1 s.2.2 a s.1).symm

theorem relation_unique (rowLt : Row → Row → Prop) (hw : WellFounded rowLt)
    (R : Rel.{u} Row)
    (hR : ∀ k theta a b, R k theta a b ↔ Rule rowLt R (b, k, theta) a) :
    R = relation rowLt hw := by
  have h := value_unique rowLt hw (fun s a => R s.2.1 s.2.2 a s.1)
    (fun s a => hR s.2.1 s.2.2 a s.1)
  funext k theta a b
  exact congrFun (congrFun h (b, k, theta)) a

end FiniteDemand

#print axioms FiniteDemand.relation_iff
#print axioms FiniteDemand.relation_unique
