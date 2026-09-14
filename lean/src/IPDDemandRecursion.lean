import IPDDemandCore

/-! The finite-demand relation is actually constructed. Reading future stages
is filled by False; causality proves that these fillers cannot affect a rule. -/

namespace IPD.Semantics
set_option autoImplicit false
universe u

noncomputable def read (s : Stage.{u}) (previous : ∀ t, Earlier t s → Prop) : Rel.{u} := by
  classical
  exact fun t a b => if h : Earlier (b,t,a) s then previous (b,t,a) h else False

noncomputable def step (s : Stage.{u}) (previous : ∀ t, Earlier t s → Prop) : Prop :=
  Rule (read s previous) s

noncomputable def value : Stage.{u} → Prop := earlier_wellFounded.fix step
noncomputable def relation : Rel.{u} := fun t a b => value (b,t,a)

theorem value_eq (s : Stage.{u}) : value s = step s (fun t _ => value t) :=
  WellFounded.fix_eq earlier_wellFounded step s

theorem read_agrees (s : Stage.{u}) : AgreeEarlier s (read s (fun t _ => value t)) relation := by
  intro t a b h
  simp [read, h, relation]

theorem relation_iff (t : Profile Label.{u}) (a b : Label.{u}) :
    relation t a b ↔ Rule relation (b,t,a) := by
  change value (b,t,a) ↔ _
  rw [value_eq]
  exact rule_congr (read_agrees (b,t,a))

theorem strict {t : Profile Label.{u}} {a b : Label.{u}} (h : relation t a b) : a < b :=
  ((relation_iff t a b).mp h).1.2.1

theorem parent_domain {t : Profile Label.{u}} {a b : Label.{u}} (h : relation t a b) : domain a :=
  ((relation_iff t a b).mp h).1.1

theorem profile_valid {t : Profile Label.{u}} {a b : Label.{u}} (h : relation t a b) :
    ProfileAtoms (fun x => x ≤ a ∨ x = b) t := ((relation_iff t a b).mp h).1.2.2

theorem profile_weaken {small large : Profile Label.{u}} {a b : Label.{u}}
    (hle : small ≤ large) (hv : ProfileAtoms (fun x => x ≤ a ∨ x = b) small)
    (h : relation large a b) : relation small a b := by
  have hh := (relation_iff large a b).mp h
  apply (relation_iff small a b).mpr
  refine ⟨⟨hh.1.1, hh.1.2.1, hv⟩, ?_⟩
  intro A f hf
  apply hh.2 A f
  refine ⟨hf.1, hf.2.1, hf.2.2.1, ?_, hf.2.2.2.2⟩
  intro e he
  have had := hf.2.2.2.1 e he
  rcases lt_or_eq_of_le hle with hl | rfl
  · rcases Prod.lex_def.mp had with hearlier | ⟨heq, _⟩
    · exact Prod.Lex.left _ _ (lt_trans hearlier hl)
    · exact Prod.Lex.left _ _ (lt_of_le_of_lt (le_of_eq heq) hl)
  · exact had

/-- The precise finite reflection rule follows from the constructed relation.
It is not an independent assumption. -/
theorem finite_reflection (t : Profile Label.{u}) (a b : Label.{u})
    (hr : relation t a b) (A : Shape) (f : Fin A.graph.length → Label.{u})
    (hf : Input relation (b,t,a) A f) : ∃ g, Output relation a A f g :=
  ((relation_iff t a b).mp hr).2 A f hf

end IPD.Semantics

#print axioms IPD.Semantics.relation_iff
#print axioms IPD.Semantics.profile_weaken
#print axioms IPD.Semantics.finite_reflection
