import OrdinalFormal.RPDWellOrderingReduction

/-! The actual RPD term type, including its specified external top. -/

namespace OrdinalFormal.RPDTermOrder
set_option autoImplicit false
set_option maxHeartbeats 500000

def cmp : RPD.Term → RPD.Term → Ordering
  | .finite a, .finite b => RPD.cmp a b
  | .finite _, .top => .lt
  | .top, .finite _ => .gt
  | .top, .top => .eq

abbrev StandardTerm := {a : RPD.Term // RPD.Standard a}
def Lt (a b : StandardTerm) : Prop := cmp a.val b.val = .lt

def forgetTop (a : StandardTerm) : Option RPDWellOrderingReduction.StandardDiagram :=
  match a with
  | ⟨.top, _⟩ => none
  | ⟨.finite g, hg⟩ => some ⟨g, hg⟩

theorem lt_iff_adjoined (a b : StandardTerm) : Lt a b ↔
    AdjoinTopLt RPDWellOrderingReduction.StandardLt (forgetTop a) (forgetTop b) := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  cases a <;> cases b <;> simp [Lt, cmp, forgetTop, AdjoinTopLt, RPDWellOrderingReduction.StandardLt]

theorem wellFounded_of_finite
    (h : WellFounded RPDWellOrderingReduction.StandardLt) : WellFounded Lt := by
  have hi := InvImage.wf forgetTop (wellFounded_adjoinTop h)
  exact Subrelation.wf (fun {a b} hab => (lt_iff_adjoined a b).mp hab) hi

theorem lt_trans {a b c : StandardTerm} (hab : Lt a b) (hbc : Lt b c) : Lt a c := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  obtain ⟨c, hc⟩ := c
  cases a <;> cases b <;> cases c <;> simp only [Lt, cmp] at hab hbc ⊢
  all_goals first | contradiction | rfl | exact Comparison.rpd_cmp_lt_trans hab hbc

theorem total_of_finite
    (ht : ∀ a b : RPDWellOrderingReduction.StandardDiagram,
      a = b ∨ RPDWellOrderingReduction.StandardLt a b ∨ RPDWellOrderingReduction.StandardLt b a)
    (a b : StandardTerm) : a = b ∨ Lt a b ∨ Lt b a := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  cases a with
  | top =>
    cases b with
    | top => exact Or.inl rfl
    | finite b => exact Or.inr (Or.inr rfl)
  | finite a =>
    cases b with
    | top => exact Or.inr (Or.inl rfl)
    | finite b =>
      rcases ht ⟨a, ha⟩ ⟨b, hb⟩ with heq | hl | hr
      · exact Or.inl (Subtype.ext (congrArg RPD.Term.finite (congrArg Subtype.val heq)))
      · exact Or.inr (Or.inl hl)
      · exact Or.inr (Or.inr hr)

end OrdinalFormal.RPDTermOrder
