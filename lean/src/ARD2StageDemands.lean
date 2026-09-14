import ARD2Structure
import ARD2Splice

/-! Actual seams with pointed row and root coordinates are admissible demands.
The two SELF coordinates are evaluated at the virtual endpoint, not through
an out-of-range array lookup. -/

namespace OrdinalFormal.ARD2
open Columns
set_option autoImplicit false
set_option maxHeartbeats 900000
universe u
variable {Label : Type u}

def Templates (R : Label → Label → Label → Label → Prop)
    (g : Graph) (e : Entry) (b : Nat) (f : Nat → Label) (beta : Label) : Prop :=
  ∀ a ∈ g.getLast?.getD [],
    R (atEnd (width g e b) f beta (shift g e b a.row))
      (atEnd (width g e b) f beta (shift g e b a.root))
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
    (he : control compare (g.getLast?.getD []) = some e) :
    e.row ≤ g.length - 1 ∧ e.root ≤ g.length - 1 ∧ e.parent < g.length - 1 :=
  control_valid hg he

theorem needs_hold
    (lt : Label → Label → Prop) (D : Label → Prop)
    (R : Label → Label → Label → Label → Prop)
    (hWeak : ∀ {k small large p c}, lt small large → R k large p c → R k small p c)
    (hLower : LowerRows lt R)
    {g : Graph} (hg : Valid g) (e : Entry)
    (he : control compare (g.getLast?.getD []) = some e) (b : Nat)
    (f : Nat → Label) (beta : Label)
    (hF : Holds lt D R (stage g e b) f)
    (hBound : ReflectionTransport.Bounded lt (width g e b) f beta)
    (hTemplates : Templates R g e b f beta) :
    Ends R (width g e b) (seam g e b) f beta := by
  have hOrdered : ∀ i j, i < j → j < width g e b → lt (f i) (f j) := by
    intro i j hij hj
    exact hF.ordered i j hij (by rwa [stage_length])
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨s, hs, hm⟩ := List.mem_flatMap.mp ha
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    have hqle : q ≤ shift g e b s.root := by
      have := List.mem_range.mp (List.mem_filter.mp hq).1
      change q < shift g e b s.root + 1 at this
      omega
    have hsBounds : s.row ≤ g.length - 1 ∧ s.root ≤ g.length - 1 ∧
        s.parent < g.length - 1 := by
      rw [List.getLast?_eq_getElem?] at hs
      exact hg _ s hs
    change R (atEnd (width g e b) f beta (shift g e b s.row))
      (atEnd (width g e b) f beta q) (f (shift g e b s.parent)) beta
    by_cases heq : q = shift g e b s.root
    · rw [heq]
      exact hTemplates s hs
    · exact hWeak
        (atEnd_strict lt _ f beta hOrdered hBound (by omega) (shift_le hsBounds.2.1 b))
        (hTemplates s hs)
  · obtain ⟨low, hlow, hm⟩ := List.mem_flatMap.mp ha
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    have hv := semantic_control_valid hg he
    have hcontrol := hTemplates e (ExpansionValidity.control_mem compare he)
    have hqle : q ≤ width g e b := by
      have hq' := List.mem_range.mp hq
      rw [generated_bound (g := g) hv.2.2 b] at hq'
      omega
    have hlow' : low < shift g e b e.row := List.mem_range.mp hlow
    change R (atEnd (width g e b) f beta low) (atEnd (width g e b) f beta q)
      (f (shift g e b e.parent)) beta
    exact hLower (atEnd_strict lt _ f beta hOrdered hBound hlow' (shift_le hv.1 b))
      (atEnd_bounded lt _ f beta hBound hqle) hcontrol

theorem needs_admissible
    (lt : Label → Label → Prop) (D : Label → Prop)
    (R : Label → Label → Label → Label → Prop)
    {g : Graph} (e : Entry)
    (hk : e.row ≤ g.length - 1) (hr : e.root ≤ g.length - 1) (b : Nat)
    (f : Nat → Label) (beta : Label)
    (hF : Holds lt D R (stage g e b) f)
    (hBound : ReflectionTransport.Bounded lt (width g e b) f beta) :
    ∀ a ∈ seam g e b,
      Admissible lt (atEnd (width g e b) f beta (shift g e b e.row))
        (atEnd (width g e b) f beta (shift g e b e.root))
        (width g e b) f beta a := by
  have hOrdered : ∀ i j, i < j → j < width g e b → lt (f i) (f j) := by
    intro i j hij hj
    exact hF.ordered i j hij (by rwa [stage_length])
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨s, hs, hm⟩ := List.mem_flatMap.mp ha
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    have hguard : s.row < e.row ∨ (s.row = e.row ∧ q < shift g e b e.root) := by
      simpa only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, shift]
        using (List.mem_filter.mp hq).2
    rcases hguard with hLow | ⟨hSame, hRoot⟩
    · exact Or.inl (atEnd_strict lt _ f beta hOrdered hBound
        (shift_strict_semantic g e b hLow) (shift_le hk b))
    · refine Or.inr ⟨?_, ?_⟩
      · change atEnd (width g e b) f beta (shift g e b s.row) =
          atEnd (width g e b) f beta (shift g e b e.row)
        rw [hSame]
      · exact atEnd_strict lt _ f beta hOrdered hBound hRoot (shift_le hr b)
  · obtain ⟨low, hlow, hm⟩ := List.mem_flatMap.mp ha
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hm
    exact Or.inl (atEnd_strict lt _ f beta hOrdered hBound
      (List.mem_range.mp hlow) (shift_le hk b))

theorem reflect_actual_stage
    (lt : Label → Label → Prop) (D : Label → Prop)
    (R : Label → Label → Label → Label → Prop)
    (hWeak : ∀ {k small large p c}, lt small large → R k large p c → R k small p c)
    (hLower : LowerRows lt R)
    (reflection : FiniteReflection lt D R)
    {g : Graph} (hg : Valid g) (e : Entry)
    (he : control compare (g.getLast?.getD []) = some e) (b : Nat)
    (f : Nat → Label) (beta : Label)
    (hF : Holds lt D R (stage g e b) f)
    (hBound : ReflectionTransport.Bounded lt (width g e b) f beta)
    (hTemplates : Templates R g e b f beta) :
    ∃ reflected : Nat → Label,
      Holds lt D R (stage g e b) reflected ∧
      (∀ i, i < cut g e b → reflected i = f i) ∧
      ReflectionTransport.Bounded lt (width g e b) reflected (f (cut g e b)) ∧
      Ends R (width g e b) (seam g e b) reflected (f (cut g e b)) := by
  have hv := semantic_control_valid hg he
  have hstate : Valid (stage g e b) := stage_valid hg e hv.2.2 hv.1 b
  have hcontrol := hTemplates e (ExpansionValidity.control_mem compare he)
  rw [shift_cut] at hcontrol
  obtain ⟨reflected, hrep, hfixed, hbelow, hneeds⟩ :=
    reflection (stage g e b) (cut g e b)
      (atEnd (width g e b) f beta (shift g e b e.row))
      (atEnd (width g e b) f beta (shift g e b e.root))
      beta f (seam g e b)
      hstate (by rw [stage_length]; exact cut_lt hv.2.2 b) hF
      (by rwa [stage_length]) hcontrol
      (by rw [stage_length]; exact seam_valid hg e hv.2.2 hv.1 b)
      (by rw [stage_length]; exact needs_admissible lt D R e hv.1 hv.2.1 b f beta hF hBound)
      (by rw [stage_length]; exact needs_hold lt D R hWeak hLower hg e he b f beta hF hBound hTemplates)
  exact ⟨reflected, hrep, hfixed, by simpa only [stage_length] using hbelow,
    by simpa only [stage_length] using hneeds⟩

#print axioms needs_hold
#print axioms needs_admissible
#print axioms reflect_actual_stage

end OrdinalFormal.ARD2
