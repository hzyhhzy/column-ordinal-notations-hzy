import ARDStructure
import ARDSplice

/-! The actual ARD seams are finite dynamic reflection demands. -/

namespace OrdinalFormal.ARD
open Columns
set_option autoImplicit false
set_option maxHeartbeats 700000
universe u
variable {Label : Type u}

def Templates (R : Label → Label → Label → Label → Prop)
    (g : Graph) (e : Entry) (b : Nat) (f : Nat → Label) (beta : Label) : Prop :=
  ∀ a ∈ g.getLast?.getD [],
    R (f (shift g e b a.row)) (f (shift g e b a.root))
      (f (shift g e b a.parent)) beta

def Facts (R : Label → Label → Label → Label → Prop)
    (g : Graph) (e : Entry) (b : Nat) (f : Nat → Label) : Prop :=
  ∀ j, j < g.length - 1 → ∀ a ∈ g[j]?.getD [],
    R (f (shift g e b a.row)) (f (shift g e b a.root))
      (f (shift g e b a.parent)) (f (shift g e b j))

theorem shift_strict_semantic (g : Graph) (e : Entry) (b : Nat)
    {i j : Nat} (h : i < j) : shift g e b i < shift g e b j := by
  unfold shift move
  split <;> split <;> omega

theorem semantic_control_valid {g : Graph} (hg : Valid g) {e : Entry}
    (he : Columns.control compare (g.getLast?.getD []) = some e) :
    e.row < g.length - 1 ∧ e.root ≤ e.parent ∧ e.parent < g.length - 1 := by
  have hm := ExpansionValidity.control_mem compare he
  rw [List.getLast?_eq_getElem?] at hm
  exact hg _ e hm

theorem needs_hold
    (lt : Label → Label → Prop) (D : Label → Prop)
    (R : Label → Label → Label → Label → Prop)
    (hWeak : ∀ {k small large p c}, lt small large → R k large p c → R k small p c)
    (hLower : ReflectionTransport.LowerRows lt lt R)
    {g : Graph} (hg : Valid g) (e : Entry)
    (he : Columns.control compare (g.getLast?.getD []) = some e) (b : Nat)
    (f : Nat → Label) (beta : Label)
    (hF : Holds lt D R (stage g e b) f)
    (hTemplates : Templates R g e b f beta) :
    Ends R (seam g e b) f beta := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨s, hs, hm⟩ := List.mem_flatMap.mp ha
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    have hqle : q ≤ shift g e b s.root := by
      have := List.mem_range.mp (List.mem_filter.mp hq).1
      change q < shift g e b s.root + 1 at this
      omega
    have hsBounds : s.row < g.length - 1 ∧ s.root ≤ s.parent ∧ s.parent < g.length - 1 := by
      rw [List.getLast?_eq_getElem?] at hs
      exact hg _ s hs
    change R (f (shift g e b s.row)) (f q) (f (shift g e b s.parent)) beta
    by_cases heq : q = shift g e b s.root
    · rw [heq]
      exact hTemplates s hs
    · apply hWeak (hF.ordered q (shift g e b s.root) (by omega) ?_) (hTemplates s hs)
      rw [stage_length]
      exact shift_lt (by have := hsBounds.2; omega) b
  · obtain ⟨low, hlow, hm⟩ := List.mem_flatMap.mp ha
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    have hv := semantic_control_valid hg he
    have hcontrol := hTemplates e (ExpansionValidity.control_mem compare he)
    have hqle : q ≤ cut g e b := by
      have hq' := List.mem_range.mp hq
      change q < shift g e b e.parent + 1 at hq'
      rw [shift_cut] at hq'
      omega
    have hlow' : low < shift g e b e.row := List.mem_range.mp hlow
    change R (f low) (f q) (f (shift g e b e.parent)) beta
    rw [shift_cut] at hcontrol ⊢
    apply hLower (hF.ordered low _ hlow' ?_) ?_ hcontrol
    · rw [stage_length]
      exact shift_lt hv.1 b
    · by_cases hqeq : q = cut g e b
      · exact Or.inl (congrArg f hqeq)
      · apply Or.inr
        apply hF.ordered _ _ (by omega)
        rw [stage_length]
        exact cut_lt hv.2.2 b

theorem needs_admissible
    (lt : Label → Label → Prop) (D : Label → Prop)
    (R : Label → Label → Label → Label → Prop)
    {g : Graph} (e : Entry)
    (hk : e.row < g.length - 1) (he : e.parent < g.length - 1)
    (hr : e.root ≤ e.parent) (b : Nat)
    (f : Nat → Label) (hF : Holds lt D R (stage g e b) f) :
    ∀ a ∈ seam g e b,
      Admissible lt (f (shift g e b e.row)) (cut g e b)
        (f (shift g e b e.root)) f a := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨s, hs, hm⟩ := List.mem_flatMap.mp ha
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    have hguard : s.row < e.row ∨ (s.row = e.row ∧ q < shift g e b e.root) := by
      simpa only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, shift]
        using (List.mem_filter.mp hq).2
    rcases hguard with hLow | ⟨hSame, hRoot⟩
    · apply Or.inl
      apply hF.ordered _ _ (shift_strict_semantic g e b hLow)
      rw [stage_length]
      exact shift_lt hk b
    · refine Or.inr ⟨?_, ?_, ?_⟩
      · change f (shift g e b s.row) = f (shift g e b e.row)
        rw [hSame]
      · have := root_le_cut (g := g) hr b
        change q < cut g e b
        omega
      · apply hF.ordered _ _ hRoot
        rw [stage_length]
        exact shift_lt (by omega) b
  · obtain ⟨low, hlow, hm⟩ := List.mem_flatMap.mp ha
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hm
    apply Or.inl
    apply hF.ordered _ _ (List.mem_range.mp hlow)
    rw [stage_length]
    exact shift_lt hk b

theorem reflect_actual_stage
    (lt : Label → Label → Prop) (D : Label → Prop)
    (R : Label → Label → Label → Label → Prop)
    (hWeak : ∀ {k small large p c}, lt small large → R k large p c → R k small p c)
    (hLower : ReflectionTransport.LowerRows lt lt R)
    (reflection : FiniteReflection lt D R)
    {g : Graph} (hg : Valid g) (e : Entry)
    (he : Columns.control compare (g.getLast?.getD []) = some e) (b : Nat)
    (f : Nat → Label) (beta : Label)
    (hF : Holds lt D R (stage g e b) f)
    (hBound : ReflectionTransport.Bounded lt (width g e b) f beta)
    (hTemplates : Templates R g e b f beta) :
    ∃ reflected : Nat → Label,
      Holds lt D R (stage g e b) reflected ∧
      (∀ i, i < cut g e b → reflected i = f i) ∧
      ReflectionTransport.Bounded lt (width g e b) reflected (f (cut g e b)) ∧
      Ends R (seam g e b) reflected (f (cut g e b)) := by
  have hv := semantic_control_valid hg he
  have hstate : Valid (stage g e b) := stage_valid hg e hv.2.2 hv.1 b
  have hcontrol := hTemplates e (ExpansionValidity.control_mem compare he)
  rw [shift_cut] at hcontrol
  obtain ⟨reflected, hrep, hfixed, hbelow, hneeds⟩ :=
    reflection (stage g e b) (cut g e b) (f (shift g e b e.row))
      (f (shift g e b e.root)) beta f (seam g e b)
      hstate (by rw [stage_length]; exact cut_lt hv.2.2 b) hF
      (by rwa [stage_length]) hcontrol
      (by rw [stage_length]; exact seam_valid hg e hv.2.2 hv.1 b)
      (needs_admissible lt D R e hv.1 hv.2.2 hv.2.1 b f hF)
      (needs_hold lt D R hWeak hLower hg e he b f beta hF hTemplates)
  refine ⟨reflected, hrep, hfixed, ?_, hneeds⟩
  rwa [stage_length] at hbelow

#print axioms needs_hold
#print axioms needs_admissible
#print axioms reflect_actual_stage

end OrdinalFormal.ARD
