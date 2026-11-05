import LaverLowerBounds.TripleCompilerEnvelope

set_option autoImplicit false

namespace LaverLowerBounds.ParentBMS

def raiseColumn (c : Column) : Column := if c = [] then [0] else c.map Nat.succ

/-- FGH-to-Hardy transform, in parent coordinates. -/
def liftW (s : Matrix) : Matrix := [] :: s.map raiseColumn

/-- Add a bottom predecessor chain and shift the old rows up one. -/
def sigma (s : Matrix) : Matrix := [] :: s.mapIdx (fun i c => i :: c.map Nat.succ)

@[simp] theorem liftW_length (s : Matrix) : (liftW s).length = s.length + 1 := by simp [liftW]
@[simp] theorem sigma_length (s : Matrix) : (sigma s).length = s.length + 1 := by simp [sigma]

theorem sigma_column {s : Matrix} {i : Nat} {c : Column} (hc : s[i]? = some c) :
    (sigma s)[i + 1]? = some (i :: c.map Nat.succ) := by simp [sigma, hc]

theorem sigma_parent_zero {s : Matrix} {i : Nat} (hi : i < s.length) :
    parent (sigma s) 0 (i + 1) = some i := by
  simp [parent, sigma, List.getElem?_eq_getElem hi]

theorem sigma_parent_succ (s : Matrix) (q i : Nat) :
    parent (sigma s) (q + 1) (i + 1) = (parent s q i).map Nat.succ := by
  unfold parent
  cases hc : s[i]? <;> simp [sigma, hc]

theorem sigma_ancestry {s : Matrix} {q p i : Nat} (ha : Ancestor s q p i) :
    Ancestor (sigma s) (q + 1) (p + 1) (i + 1) := by
  induction ha with
  | direct he => exact .direct (by rw [sigma_parent_succ, he]; rfl)
  | step he _ ih => exact .step (by rw [sigma_parent_succ, he]; rfl) ih

theorem sigma_chain {s : Matrix} {p i : Nat} (hpi : p < i) (hi : i < (sigma s).length) :
    Ancestor (sigma s) 0 p i := by
  induction i using Nat.strongRecOn with
  | ind i ih =>
      have hpos : 0 < i := by omega
      have he : parent (sigma s) 0 i = some (i - 1) := by
        have hh := sigma_parent_zero (s := s) (i := i - 1) (by rw [sigma_length] at hi; omega)
        rwa [Nat.sub_add_cancel hpos] at hh
      by_cases hp : p = i - 1
      · rw [hp]; exact .direct he
      · exact .step he (ih (i - 1) (by omega) (by omega) (by omega))

theorem sigma_leftward {s : Matrix} (hs : Leftward s) : Leftward (sigma s) := by
  intro q i p hp
  cases i with
  | zero => simp [parent, sigma] at hp
  | succ i =>
      cases q with
      | zero =>
          have hi : i < s.length := by have := parent_column_lt hp; simpa using this
          rw [sigma_parent_zero hi, Option.some.injEq] at hp
          omega
      | succ q =>
          rw [sigma_parent_succ] at hp
          cases he : parent s q i with
          | none => simp [he] at hp
          | some a =>
              have hh : a + 1 = p := by simpa [he] using hp
              have := hs q i a he
              omega

theorem sigma_nested {s : Matrix} (hl : Leftward s) (hn : Nested s) : Nested (sigma s) := by
  intro q i p hp
  cases i with
  | zero => simp [parent, sigma] at hp
  | succ i =>
      rw [sigma_parent_succ] at hp
      cases he : parent s q i with
      | none => simp [he] at hp
      | some a =>
          have hh : a + 1 = p := by simpa [he] using hp
          subst p
          cases q with
          | zero =>
              apply sigma_chain (by have := hl 0 i a he; omega)
              rw [sigma_length]
              have := parent_column_lt he
              omega
          | succ q => exact sigma_ancestry (hn q i a he)

theorem sigma_shape {s : Matrix} {h : Nat} (hs : Shape h 0 s) : Shape (h + 1) 0 (sigma s) := by
  intro i c hc
  cases i with
  | zero => simp [sigma] at hc; subst c; simp
  | succ i =>
      cases he : s[i]? with
      | none => simp [sigma, he] at hc
      | some old =>
          have hh : i :: old.map Nat.succ = c := by simpa [sigma, he] using hc
          subst c
          obtain ⟨hh, hp⟩ := hs i old he
          constructor
          · simp only [List.length_cons, List.length_map]; omega
          · intro p hmem
            rcases List.mem_cons.mp hmem with hmem | hmem
            · omega
            · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hmem
              have := hp a ha
              omega

theorem raiseColumn_map_parent {c : Column} {q p : Nat} (hp : c[q]? = some p) :
    (raiseColumn c)[q]? = some (p + 1) := by
  have hc : c ≠ [] := by intro he; simp [he] at hp
  simp [raiseColumn, hc, hp]

theorem liftW_parent {s : Matrix} {q p i : Nat} (hp : parent s q i = some p) :
    parent (liftW s) q (i + 1) = some (p + 1) := by
  obtain ⟨c, hc, hcp⟩ := parent_some_iff.mp hp
  simp only [parent, liftW, List.getElem?_cons_succ, List.getElem?_map, hc, Option.map_some, Option.bind_some]
  exact raiseColumn_map_parent hcp

theorem liftW_ancestry {s : Matrix} {q p i : Nat} (ha : Ancestor s q p i) :
    Ancestor (liftW s) q (p + 1) (i + 1) :=
  ha.map_edges (fun _ _ he => .direct (liftW_parent he))

theorem liftW_shape {s : Matrix} {h : Nat} (hs : Shape h 0 s) (hh : 1 ≤ h) : Shape h 0 (liftW s) := by
  intro i c hc
  cases i with
  | zero => simp [liftW] at hc; subst c; simp
  | succ i =>
      cases he : s[i]? with
      | none => simp [liftW, he] at hc
      | some old =>
          have hcol : raiseColumn old = c := by simpa [liftW, he] using hc
          subst c
          obtain ⟨hheight, hparents⟩ := hs i old he
          by_cases hz : old = []
          · simp only [raiseColumn, if_pos hz, List.length_cons, List.length_nil]
            exact ⟨hh, by intro p hp; simp only [List.mem_singleton] at hp; omega⟩
          · simp only [raiseColumn, if_neg hz, List.length_map]
            refine ⟨hheight, ?_⟩
            intro p hp
            obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
            have := hparents a ha
            omega

theorem liftW_nested {s : Matrix} (hn : Nested s) : Nested (liftW s) := by
  intro q i p hp
  cases i with
  | zero => simp [parent, liftW] at hp
  | succ i =>
      cases he : s[i]? with
      | none => simp [parent, liftW, he] at hp
      | some old =>
          simp only [parent, liftW, List.getElem?_cons_succ, List.getElem?_map, he,
            Option.map_some, Option.bind_some] at hp
          by_cases hz : old = []
          · simp [raiseColumn, hz] at hp
          · simp only [raiseColumn, if_neg hz, List.getElem?_map] at hp
            cases hq : old[q + 1]? with
            | none => simp [hq] at hp
            | some a =>
                have ha : a + 1 = p := by simpa [hq] using hp
                subst p
                apply liftW_ancestry
                exact hn q i a (by simp [parent, he, hq])

/-- Both transforms stay in the broad graph domain used by the rectangle
compiler. Numeric BM4 fidelity is proved in NumericExpansionFidelity.lean. -/
theorem transformed_shape {s : Matrix} {h : Nat} (hs : Shape h 0 s) (hh : 1 ≤ h) :
    Shape (h + 1) 0 (sigma (liftW s)) := sigma_shape (liftW_shape hs hh)

#print axioms sigma_nested
#print axioms liftW_nested
#print axioms transformed_shape

end LaverLowerBounds.ParentBMS
