import FiniteDemandRecursion

/-!
# Reflection and weakening for the constructed relation

These are consequences of the actual recursion equation, not hypotheses on a
user-supplied relation. The final theorem has exactly the finite reflection
interface used by the existing diagram transport proofs. Initial supply is
still a separate obligation: reflection by itself does not prove well-ordering.
-/

namespace FiniteDemand

open OrdinalFormal.ReflectionTransport

universe u v
variable {Row : Type v}

theorem strict {rowLt : Row → Row → Prop} {hw : WellFounded rowLt}
    {k : Row} {theta a b : Label.{u}} (h : relation rowLt hw k theta a b) : a < b :=
  ((relation_iff rowLt hw k theta a b).mp h).1.2.1

theorem parent_domain {rowLt : Row → Row → Prop} {hw : WellFounded rowLt}
    {k : Row} {theta a b : Label.{u}} (h : relation rowLt hw k theta a b) : domain a :=
  ((relation_iff rowLt hw k theta a b).mp h).1.2.2

theorem root_le {rowLt : Row → Row → Prop} {hw : WellFounded rowLt}
    {k : Row} {theta a b : Label.{u}} (h : relation rowLt hw k theta a b) : theta ≤ a :=
  ((relation_iff rowLt hw k theta a b).mp h).1.1

/-- Enlarging the root enlarges the family of demands; hence a true relation
at the larger root entails the relation at every smaller root. -/
theorem root_weaken {rowLt : Row → Row → Prop} {hw : WellFounded rowLt}
    {k : Row} {small large a b : Label.{u}} (hle : small ≤ large)
    (h : relation rowLt hw k large a b) : relation rowLt hw k small a b := by
  have hfull := (relation_iff rowLt hw k large a b).mp h
  apply (relation_iff rowLt hw k small a b).mpr
  refine ⟨⟨le_trans hle hfull.1.1, hfull.1.2⟩, ?_⟩
  intro A f hf
  apply hfull.2 A f
  refine ⟨hf.1, hf.2.1, hf.2.2.1, ?_, hf.2.2.2.2⟩
  intro d hd
  rcases hf.2.2.2.1 d hd with hlow | ⟨heq, hcut, hroot⟩
  · exact Or.inl hlow
  · exact Or.inr ⟨heq, hcut, lt_of_lt_of_le hroot hle⟩

/-- All lower-row demand families are included in the higher-row family. -/
theorem lower_rows (rowLt : Row → Row → Prop) (hw : WellFounded rowLt)
    (htrans : Transitive rowLt) : LowerRows rowLt (· < ·) (relation.{u} rowLt hw) := by
  intro low high theta eta a b hl heta h
  have hfull := (relation_iff rowLt hw high theta a b).mp h
  apply (relation_iff rowLt hw low eta a b).mpr
  have he : eta ≤ a := heta.elim (fun h => h.le) (fun h => h.le)
  refine ⟨⟨he, hfull.1.2⟩, ?_⟩
  intro A f hf
  apply hfull.2 A f
  refine ⟨hf.1, hf.2.1, hf.2.2.1, ?_, hf.2.2.2.2⟩
  intro d hd
  apply Or.inl
  rcases hf.2.2.2.1 d hd with hlow | ⟨heq, _, _⟩
  · exact htrans hlow hl
  · exact heq ▸ hl

theorem representation_labels {R : Rel.{u} Row} {G : Diagram Row}
    {f g : Nat → Label.{u}} (hfg : ∀ i, i < G.size → g i = f i)
    (hf : Representation (· < ·) domain R G f) :
    Representation (· < ·) domain R G g := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [hfg i hi]
    exact hf.domain i hi
  · intro i j hij hj
    rw [hfg i (lt_trans hij hj), hfg j hj]
    exact hf.ordered i j hij hj
  · intro e he
    rcases G.valid e he with ⟨hr, hp, hc⟩
    unfold Atom.Holds
    rw [hfg e.root (by omega), hfg e.parent (by omega), hfg e.child hc]
    exact hf.relations e he

theorem ends_labels {R : Rel.{u} Row} {n : Nat} {needs : List (TopAtom Row)}
    {f g : Nat → Label.{u}} {b : Label.{u}}
    (hfg : ∀ i, i < n → g i = f i) (hv : ∀ d ∈ needs, d.Valid n)
    (hf : Ends R needs f b) : Ends R needs g b := by
  intro d hd
  rcases hv d hd with ⟨hr, hp⟩
  unfold TopAtom.Holds
  rw [hfg d.root (by omega), hfg d.parent hp]
  exact hf d hd

/-- The established Nat-indexed geometric interface is implemented using
finite labelings in both quantifiers of the new semantics. -/
theorem finite_reflection (rowLt : Row → Row → Prop) (hw : WellFounded rowLt) :
    FiniteReflection rowLt (· < ·) domain (relation.{u} rowLt hw) := by
  intro G cut K theta beta f needs hcut hf _hBeta hbound hcontrol hvalid hadmiss hends
  let A : Shape Row := ⟨G, cut, hcut, needs, hvalid⟩
  let F : Fin G.size → Label.{u} := fun i => f i.val
  have hF : ∀ i, i < G.size → labels F i = f i := by
    intro i hi
    exact labels_apply F hi
  have hin : Input rowLt (relation rowLt hw) (beta, K, theta) (f cut) A F := by
    refine ⟨representation_labels hF hf, ?_, hF cut hcut, ?_,
      ends_labels hF hvalid hends⟩
    · intro i hi
      rw [hF i hi]
      exact hbound i hi
    · intro d hd
      rcases hadmiss d hd with hl | ⟨heq, hr, ht⟩
      · exact Or.inl hl
      · exact Or.inr ⟨heq, hr, by rw [hF d.root (lt_trans hr hcut)]; exact ht⟩
  obtain ⟨g, hg, hfixed, hbelow, hnew⟩ :=
    ((relation_iff rowLt hw K theta (f cut) beta).mp hcontrol).2 A F hin
  refine ⟨labels g, hg, ?_, hbelow, hnew⟩
  intro i hi
  exact (hfixed i hi).trans (hF i (lt_trans hi hcut))

end FiniteDemand

#print axioms FiniteDemand.strict
#print axioms FiniteDemand.root_weaken
#print axioms FiniteDemand.lower_rows
#print axioms FiniteDemand.finite_reflection
