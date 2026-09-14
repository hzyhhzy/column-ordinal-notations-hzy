import IPDInitialRepresentation
import IPDStageSplice
import OrdinalFormal.Reachability

/-! Unconditional well-foundedness of actual expansion steps on valid IPD
graphs. The standard column-order theorem is a further, separate obligation.
The proof is induction on an actual last ordinal label, equivalent to using
the least such label, and has no supply or reflection premises. -/

namespace IPD
abbrev Step : Graph → Graph → Prop := OrdinalFormal.FSStep [] expand
end IPD

namespace IPD.Semantics
set_option autoImplicit false
universe u

theorem expand_bounded {G : Graph} (hv : Valid G) (hn : G ≠ [])
    (f : Nat → Label.{u}) (hf : Rep relation G f) (n : Nat) :
    ∃ g : Nat → Label.{u}, Rep relation (expand G n) g ∧
      Bounded (expand G n).length g (f (G.length-1)) := by
  have hl : 0 < G.length := by cases G <;> simp_all
  cases he : controller (G.getLast?.getD []) with
  | none =>
    refine ⟨f,?_,?_⟩
    · simpa only [expand,he] using representation_take hf (G.length-1)
    · intro i hi
      have hi' : i < G.length-1 := by
        simpa only [expand,he,List.length_take,Nat.min_eq_left (Nat.sub_le G.length 1)] using hi
      exact hf.ordered i (G.length-1) hi' (by omega)
  | some e =>
    obtain ⟨g,hg⟩ := stages_represented hv he f hf n
    refine ⟨g,?_,?_⟩
    · simpa only [expand,he,stage] using hg.rep
    · have heq : expand G n = stage G e n := by simp only [expand,he,stage]
      rw [heq,stage_length]
      exact hg.bounded

theorem empty_accessible : Acc Step [] := Acc.intro [] (fun _ h => (h.1 rfl).elim)

theorem accessible_with_last (beta : Label.{u}) :
    ∀ G : Graph, Valid G → ∀ f : Nat → Label.{u}, Rep relation G f →
      f (G.length-1) = beta → Acc Step G := by
  induction beta using Ordinal.lt_wf.induction with
  | h beta ih =>
    intro G hv f hf hlast
    apply Acc.intro G
    intro H hstep
    obtain ⟨hn,n,rfl⟩ := hstep
    by_cases hz : expand G n = []
    · rw [hz]
      exact empty_accessible
    · obtain ⟨g,hg,hb⟩ := expand_bounded hv hn f hf n
      have hl : 0 < (expand G n).length := by cases h : expand G n <;> simp_all
      have hlt := hb ((expand G n).length-1) (by omega)
      rw [hlast] at hlt
      exact ih _ hlt (expand G n) (expand_valid hv n) g hg rfl

theorem valid_accessible (G : Graph) (hv : Valid G) : Acc Step G := by
  obtain ⟨f,hf,_⟩ := initial.{0} G hv
  exact accessible_with_last (f (G.length-1)) G hv f hf rfl

theorem valid_step_wellFounded :
    WellFounded (fun a b : {G : Graph // Valid G} => Step a.val b.val) := by
  refine ⟨fun G => ?_⟩
  exact InvImage.accessible (fun G : {G : Graph // Valid G} => G.val)
    (valid_accessible G.val G.property)

end IPD.Semantics

#print axioms IPD.Semantics.expand_bounded
#print axioms IPD.Semantics.valid_accessible
#print axioms IPD.Semantics.valid_step_wellFounded
