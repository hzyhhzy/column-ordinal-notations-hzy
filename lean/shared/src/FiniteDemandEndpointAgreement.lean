import FiniteDemandWitnesses

/-!
# Endpoint agreement and reflection at a closed height

These theorems use closure under the actual least-witness operations, not an
assumption of semantic endpoint agreement. Existence of such closed heights
will be supplied separately by a countable finitary closure construction.
-/

namespace FiniteDemand
open OrdinalFormal.ReflectionTransport

universe u v
variable {Row : Type v} [Countable Row]

def RootEarlier (rowLt : Row → Row → Prop) : (Row × Label.{u}) → (Row × Label.{u}) → Prop :=
  Prod.Lex rowLt (· < ·)

theorem rootEarlier_wellFounded (rowLt : Row → Row → Prop) (hw : WellFounded rowLt) :
    WellFounded (RootEarlier.{u} rowLt) := hw.prod_lex Ordinal.lt_wf

def BadClosed (rowLt : Row → Row → Prop) (hw : WellFounded rowLt)
    (kappa delta : Label.{u}) : Prop :=
  ∀ k i theta a, theta < delta → a < delta → badOp rowLt hw k i theta a kappa < delta

def ExtClosed (R : Rel.{u} Row) (kappa delta : Label.{u}) : Prop :=
  ∀ (A : Shape Row) i (pref : Fin A.cut → Label.{u}),
    (∀ j, pref j < delta) → extOp R kappa A i pref < delta

theorem admissible_rootEarlier {rowLt : Row → Row → Prop}
    {s : Row × Label.{u}} {cut : Nat} {f : Nat → Label.{u}} {d : TopAtom Row}
    (h : Admissible rowLt (· < ·) s.1 cut s.2 f d) :
    RootEarlier rowLt (d.layer, f d.root) s := by
  rcases h with hl | ⟨heq, _, hr⟩
  · exact Prod.Lex.left _ _ hl
  · have hs : s = (s.1, s.2) := rfl
    rw [hs, heq]
    exact Prod.Lex.right _ hr

theorem ends_endpoint_iff {rowLt : Row → Row → Prop} {hw : WellFounded rowLt}
    {kappa delta : Label.{u}} {s : Row × Label.{u}}
    (ih : ∀ t, RootEarlier rowLt t s → ∀ a, a < delta →
      (relation rowLt hw t.1 t.2 a kappa ↔ relation rowLt hw t.1 t.2 a delta))
    {A : Shape Row} {f : Nat → Label.{u}}
    (hb : Bounded (· < ·) A.diagram.size f delta)
    (ha : ∀ d ∈ A.needs, Admissible rowLt (· < ·) s.1 A.cut s.2 f d) :
    Ends (relation rowLt hw) A.needs f kappa ↔ Ends (relation rowLt hw) A.needs f delta := by
  have he : ∀ d ∈ A.needs,
      d.Holds (relation rowLt hw) f kappa ↔ d.Holds (relation rowLt hw) f delta := by
    intro d hd
    exact ih (d.layer, f d.root) (admissible_rootEarlier (ha d hd)) (f d.parent)
      (hb d.parent (A.needs_valid d hd).2)
  exact ⟨fun h d hd => (he d hd).mp (h d hd), fun h d hd => (he d hd).mpr (h d hd)⟩

/-- Agreement is proved by induction on (row, root), simultaneously for all
parent labels below delta. No bound on the rows of internal edges is used. -/
theorem endpoint_agreement (rowLt : Row → Row → Prop) (hw : WellFounded rowLt)
    {kappa delta : Label.{u}} (hdk : delta < kappa) (hclosed : BadClosed rowLt hw kappa delta)
    (k : Row) (theta a : Label.{u}) (ha : a < delta) :
    relation rowLt hw k theta a kappa ↔ relation rowLt hw k theta a delta := by
  have hall : ∀ s : Row × Label.{u}, ∀ a, a < delta →
      (relation rowLt hw s.1 s.2 a kappa ↔ relation rowLt hw s.1 s.2 a delta) := by
    intro s
    induction s using (rootEarlier_wellFounded rowLt hw).induction with
    | h s ih =>
      intro a ha
      constructor
      · intro hr
        have hrule := (relation_iff rowLt hw s.1 s.2 a kappa).mp hr
        apply (relation_iff rowLt hw s.1 s.2 a delta).mpr
        refine ⟨⟨hrule.1.1, ha, hrule.1.2.2⟩, ?_⟩
        intro A f hf
        apply hrule.2 A f
        refine ⟨hf.1, (fun i hi => lt_trans (hf.2.1 i hi) hdk), hf.2.2.1,
          hf.2.2.2.1, ?_⟩
        exact (ends_endpoint_iff ih hf.2.1 hf.2.2.2.1).mpr hf.2.2.2.2
      · intro hr
        classical
        by_contra hn
        have hg : Guard (kappa, s.1, s.2) a :=
          ⟨root_le hr, lt_trans ha hdk, parent_domain hr⟩
        have hex := exists_bad hg hn
        let p := leastBad rowLt hw s.1 s.2 a kappa hex
        have hp : Bad rowLt hw s.1 s.2 a kappa p := leastBad_spec rowLt hw s.1 s.2 a kappa hex
        have hbp : Bounded (· < ·) p.1.diagram.size (labels p.2) delta := by
          intro i _hi
          rw [← badOp_eq rowLt hw s.1 i s.2 a kappa hex]
          exact hclosed s.1 i s.2 a (lt_of_le_of_lt (root_le hr) ha) ha
        have hin : Input rowLt (relation rowLt hw) (delta, s.1, s.2) a p.1 p.2 :=
          ⟨hp.1.1, hbp, hp.1.2.2.1, hp.1.2.2.2.1,
            (ends_endpoint_iff ih hbp hp.1.2.2.2.1).mp hp.1.2.2.2.2⟩
        exact hp.2 (((relation_iff rowLt hw s.1 s.2 a delta).mp hr).2 p.1 p.2 hin)
  exact hall (k, theta) a ha

/-- Extension closure moves the entire demand below delta, retaining only its
prefix. Endpoint agreement then changes the extension's endpoint to delta. -/
theorem closed_reflects (rowLt : Row → Row → Prop) (hw : WellFounded rowLt)
    {kappa delta : Label.{u}} (hdk : delta < kappa) (hd : domain delta)
    (hbad : BadClosed rowLt hw kappa delta) (hext : ExtClosed (relation rowLt hw) kappa delta)
    (k : Row) (theta : Label.{u}) (htheta : theta ≤ delta) :
    relation rowLt hw k theta delta kappa := by
  apply (relation_iff rowLt hw k theta delta kappa).mpr
  refine ⟨⟨htheta, hdk, hd⟩, ?_⟩
  intro A f hf
  let pref : Fin A.cut → Label.{u} := fun i => labels f i
  have hpref : ∀ i, pref i < delta := by
    intro i
    change labels f i < delta
    rw [← hf.2.2.1]
    exact hf.1.ordered i A.cut i.isLt A.cut_lt
  have hex : ∃ g, Extends (relation rowLt hw) kappa A pref g :=
    ⟨f, hf.1, hf.2.1, (fun _ => rfl), hf.2.2.2.2⟩
  let g := leastExtension (relation rowLt hw) kappa A pref hex
  have hg : Extends (relation rowLt hw) kappa A pref g :=
    leastExtension_spec (relation rowLt hw) kappa A pref hex
  have hgb : Bounded (· < ·) A.diagram.size (labels g) delta := by
    intro i _hi
    rw [← extOp_eq (relation rowLt hw) kappa A i pref hex]
    exact hext A i pref hpref
  refine ⟨g, hg.1, ?_, hgb, ?_⟩
  · intro i hi
    exact hg.2.2.1 ⟨i, hi⟩
  · intro d hd
    exact (endpoint_agreement rowLt hw hdk hbad d.layer (labels g d.root) (labels g d.parent)
      (hgb d.parent (A.needs_valid d hd).2)).mp (hg.2.2.2 d hd)

theorem closed_heights_related (rowLt : Row → Row → Prop) (hw : WellFounded rowLt)
    {kappa alpha beta : Label.{u}} (hab : alpha < beta) (hbk : beta < kappa)
    (ha : domain alpha) (hbadA : BadClosed rowLt hw kappa alpha)
    (hextA : ExtClosed (relation rowLt hw) kappa alpha) (hbadB : BadClosed rowLt hw kappa beta)
    (k : Row) (theta : Label.{u}) (ht : theta ≤ alpha) :
    relation rowLt hw k theta alpha beta :=
  (endpoint_agreement rowLt hw hbk hbadB k theta alpha hab).mp
    (closed_reflects rowLt hw (lt_trans hab hbk) ha hbadA hextA k theta ht)

end FiniteDemand

#print axioms FiniteDemand.endpoint_agreement
#print axioms FiniteDemand.closed_reflects
#print axioms FiniteDemand.closed_heights_related
