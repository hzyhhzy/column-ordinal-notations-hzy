import ARDStageDemands

/-! Actual dynamic ARD splicing, arbitrarily many blocks, and the bounded
representation theorem. The semantic relation remains an explicit parameter. -/

namespace OrdinalFormal.ARD
open Columns
set_option autoImplicit false
set_option maxHeartbeats 900000
universe u
variable {Label : Type u}

theorem splice_actual_stage
    (lt : Label → Label → Prop) (D : Label → Prop)
    (R : Label → Label → Label → Label → Prop)
    (hTrans : ∀ {a b c}, lt a b → lt b c → lt a c)
    (hWeak : ∀ {k small large p c}, lt small large → R k large p c → R k small p c)
    {g : Graph} (hg : Valid g) (e : Entry)
    (he : e.parent < g.length - 1) (hk : e.row < g.length - 1) (b : Nat)
    (f reflected : Nat → Label) (beta : Label)
    (hF : Holds lt D R (stage g e b) f)
    (hRef : Holds lt D R (stage g e b) reflected)
    (hFixed : ∀ i, i < cut g e b → reflected i = f i)
    (hBelow : ReflectionTransport.Bounded lt (width g e b) reflected (f (cut g e b)))
    (hBound : ReflectionTransport.Bounded lt (width g e b) f beta)
    (hFacts : Facts R g e b f) (hTemplates : Templates R g e b f beta)
    (hNeeds : Ends R (seam g e b) reflected (f (cut g e b))) :
    let next := ReflectionTransport.spliceLabel (width g e b) (cut g e b) f reflected
    Holds lt D R (stage g e (b + 1)) next ∧
      ReflectionTransport.Bounded lt (width g e (b + 1)) next beta ∧
      Facts R g e (b + 1) next ∧ Templates R g e (b + 1) next beta := by
  let next := ReflectionTransport.spliceLabel (width g e b) (cut g e b) f reflected
  change Holds lt D R (stage g e (b + 1)) next ∧ _
  have hcut := cut_lt he b
  have hOrderF : ∀ i j, i < j → j < width g e b → lt (f i) (f j) := by
    intro i j hij hj
    exact hF.ordered i j hij (by rwa [stage_length])
  have hOrderRef : ∀ i j, i < j → j < width g e b → lt (reflected i) (reflected j) := by
    intro i j hij hj
    exact hRef.ordered i j hij (by rwa [stage_length])
  have hOrder : ∀ i j, i < j → j < width g e (b + 1) → lt (next i) (next j) := by
    rw [width_succ he]
    exact ReflectionTransport.spliceLabel_ordered lt hTrans f reflected hcut hOrderF hOrderRef hBelow
  have hBoundNext : ReflectionTransport.Bounded lt (width g e (b + 1)) next beta := by
    rw [width_succ he]
    exact ReflectionTransport.spliceLabel_bounded lt hTrans f reflected beta (hBound _ hcut) hBound hBelow
  have hReuse : ∀ i, i < g.length - 1 → next (shift g e (b + 1) i) = f (shift g e b i) := by
    intro i hi
    have h := ReflectionTransport.spliceLabel_move (n := width g e b) (cut := cut g e b)
      f reflected (Nat.le_of_lt hcut) (shift_lt hi b) hFixed
    rw [shift_succ he] at h
    exact h
  have hFactsNext : Facts R g e (b + 1) next := by
    intro j hj a ha
    have hv := hg j a ha
    rw [hReuse a.row (by omega), hReuse a.root (by have := hv.2; omega),
      hReuse a.parent (by have := hv.2; omega), hReuse j hj]
    exact hFacts j hj a ha
  have hTemplatesNext : Templates R g e (b + 1) next beta := by
    intro a ha
    have hv : a.row < g.length - 1 ∧ a.root ≤ a.parent ∧ a.parent < g.length - 1 := by
      rw [List.getLast?_eq_getElem?] at ha
      exact hg _ a ha
    rw [hReuse a.row hv.1, hReuse a.root (by have := hv.2; omega), hReuse a.parent hv.2.2]
    exact hTemplates a ha
  refine ⟨⟨?_, ?_, ?_⟩, hBoundNext, hFactsNext, hTemplatesNext⟩
  · intro i hi
    rw [stage_length, width_succ he] at hi
    by_cases hold : i < width g e b
    · change D (ReflectionTransport.spliceLabel _ _ f reflected i)
      rw [ReflectionTransport.spliceLabel_old f reflected hold]
      exact hRef.domain i (by rwa [stage_length])
    · change D (ReflectionTransport.spliceLabel _ _ f reflected i)
      simp only [ReflectionTransport.spliceLabel, if_neg hold]
      apply hF.domain
      rw [stage_length]
      omega
  · intro i j hij hj
    exact hOrder i j hij (by rwa [stage_length] at hj)
  · intro j a ha
    rcases stage_step_origin g e b j ha with hold | ⟨i, hi, hj, horigin⟩
    · have hValidOld := stage_valid hg e he hk b
      have hv := hValidOld j a hold
      have hj' := ColumnRepresentation.index_lt_of_entry_mem hold
      rw [stage_length] at hj'
      have hrow : a.row < width g e b := by omega
      have hroot : a.root < width g e b := by have := hv.2; omega
      have hparent : a.parent < width g e b := by have := hv.2; omega
      change R (ReflectionTransport.spliceLabel _ _ f reflected a.row)
        (ReflectionTransport.spliceLabel _ _ f reflected a.root)
        (ReflectionTransport.spliceLabel _ _ f reflected a.parent)
        (ReflectionTransport.spliceLabel _ _ f reflected j)
      rw [ReflectionTransport.spliceLabel_old f reflected hrow,
        ReflectionTransport.spliceLabel_old f reflected hroot,
        ReflectionTransport.spliceLabel_old f reflected hparent,
        ReflectionTransport.spliceLabel_old f reflected hj']
      exact hRef.relations j a hold
    · rcases horigin with ⟨s, hs, hw⟩ | ⟨hi0, s, hs, hw⟩
      · have hsource : e.parent + i < g.length - 1 := by omega
        have hv := hg (e.parent + i) s hs
        have hchild : shift g e (b + 1) (e.parent + i) = j := by
          unfold shift move
          rw [if_neg (by omega)]
          simp only [Nat.add_mul, Nat.one_mul]
          unfold width at hj
          omega
        have hRaw := hFactsNext (e.parent + i) hsource s hs
        rw [hchild] at hRaw
        apply weaken_relation lt R hWeak next (width g e (b + 1)) j hOrder a
          (ARD.moveEntry e.parent (g.length - 1 - e.parent) (b + 1) s)
          hw.1 hw.2.1 hw.2.2 (shift_lt (by have := hv.2; omega) (b + 1)) hRaw
      · subst i
        change j = width g e b + 0 at hj
        simp only [Nat.add_zero] at hj
        subst j
        have hv := seam_valid hg e he hk b s hs
        have hRawNext : R (next s.row) (next s.root) (next s.parent) (next (width g e b)) :=
          splice_seam R f reflected s hv (hNeeds s hs)
        apply weaken_relation lt R hWeak next (width g e (b + 1)) (width g e b)
          hOrder a s hw.1 hw.2.1 hw.2.2 ?_ hRawNext
        rw [width_succ he]
        have := hv.2
        omega

theorem all_stages
    (lt : Label → Label → Prop) (D : Label → Prop)
    (R : Label → Label → Label → Label → Prop)
    (hTrans : ∀ {a b c}, lt a b → lt b c → lt a c)
    (hWeak : ∀ {k small large p c}, lt small large → R k large p c → R k small p c)
    (hLower : ReflectionTransport.LowerRows lt lt R)
    (reflection : FiniteReflection lt D R)
    {g : Graph} (hg : Valid g) (e : Entry)
    (he : Columns.control compare (g.getLast?.getD []) = some e)
    (initial : Nat → Label) (hInitial : Holds lt D R g initial) :
    ∀ n, ∃ f : Nat → Label,
      Holds lt D R (stage g e n) f ∧
      ReflectionTransport.Bounded lt (width g e n) f (initial (g.length - 1)) ∧
      Facts R g e n f ∧ Templates R g e n f (initial (g.length - 1)) := by
  have hv := semantic_control_valid hg he
  have hx : g.length - 1 < g.length := by omega
  intro n
  induction n with
  | zero =>
    refine ⟨initial, ?_, ?_, ?_, ?_⟩
    · simpa [stage] using holds_take lt D R hInitial (g.length - 1)
    · intro i hi
      have hi' : i < g.length - 1 := by simpa [width] using hi
      exact hInitial.ordered i (g.length - 1) hi' hx
    · intro j hj a ha
      simpa [shift, move] using hInitial.relations j a ha
    · intro a ha
      rw [List.getLast?_eq_getElem?] at ha
      simpa [shift, move] using hInitial.relations (g.length - 1) a ha
  | succ n ih =>
    obtain ⟨f, hF, hBound, hFacts, hTemplates⟩ := ih
    obtain ⟨reflected, hRef, hFixed, hBelow, hNeeds⟩ :=
      reflect_actual_stage lt D R hWeak hLower reflection hg e he n f
        (initial (g.length - 1)) hF hBound hTemplates
    exact ⟨_, splice_actual_stage lt D R hTrans hWeak hg e hv.2.2 hv.1 n f reflected _
      hF hRef hFixed hBelow hBound hFacts hTemplates hNeeds⟩

/-- Every actual finite output is represented strictly below the old last
label. The index and the dynamically generated row addresses are unbounded. -/
theorem expand_bounded
    (lt : Label → Label → Prop) (D : Label → Prop)
    (R : Label → Label → Label → Label → Prop)
    (hTrans : ∀ {a b c}, lt a b → lt b c → lt a c)
    (hWeak : ∀ {k small large p c}, lt small large → R k large p c → R k small p c)
    (hLower : ReflectionTransport.LowerRows lt lt R)
    (reflection : FiniteReflection lt D R)
    {g : Graph} (hg : Valid g) (hn : g ≠ [])
    (initial : Nat → Label) (hInitial : Holds lt D R g initial) (n : Nat) :
    ∃ f : Nat → Label,
      Holds lt D R (expand g n) f ∧
      ReflectionTransport.Bounded lt (expand g n).length f (initial (g.length - 1)) := by
  cases he : Columns.control compare (g.getLast?.getD []) with
  | none =>
    have hfs : expand g n = g.take (g.length - 1) := by simp [expand, he]
    rw [hfs]
    refine ⟨initial, holds_take lt D R hInitial _, ?_⟩
    intro i hi
    have hpos : 0 < g.length := by cases g <;> simp_all
    have hi' : i < g.length - 1 := by
      simpa only [List.length_take, Nat.min_eq_left (Nat.sub_le g.length 1)] using hi
    exact hInitial.ordered i (g.length - 1) hi' (by omega)
  | some e =>
    obtain ⟨f, hF, hBound, _, _⟩ :=
      all_stages lt D R hTrans hWeak hLower reflection hg e he initial hInitial n
    rw [expand_eq_stage g he]
    exact ⟨f, hF, by rwa [stage_length]⟩

#print axioms splice_actual_stage
#print axioms all_stages
#print axioms expand_bounded

end OrdinalFormal.ARD
