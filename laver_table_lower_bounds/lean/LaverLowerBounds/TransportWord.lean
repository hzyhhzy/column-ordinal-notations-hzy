import LaverLowerBounds.InsertionLowData

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable

def wordAct (family : BinaryFamily) (m : Nat) : List Nat → Nat → Nat
  | [], x => x
  | a :: rest, x => act family m a (wordAct family m rest x)

def wordTerm (family : BinaryFamily) (m : Nat) : List Nat → Nat → Nat
  | [], b => b
  | a :: rest, b => (family m).mul a (wordTerm family m rest b)

theorem wordAct_append (family : BinaryFamily) (m : Nat) (w v : List Nat) (x : Nat) :
    wordAct family m (w ++ v) x = wordAct family m w (wordAct family m v x) := by
  induction w with
  | nil => rfl
  | cons a rest ih => simp only [List.cons_append, wordAct, ih]

theorem wordTerm_append (family : BinaryFamily) (m : Nat) (w v : List Nat) (x : Nat) :
    wordTerm family m (w ++ v) x = wordTerm family m w (wordTerm family m v x) := by
  induction w with
  | nil => rfl
  | cons a rest ih => simp only [List.cons_append, wordTerm, ih]

theorem word_bounds (family : BinaryFamily) (m : Nat) (w : List Nat) {x : Nat} (hx : x ≤ m) :
    x ≤ wordAct family m w x ∧ wordAct family m w x ≤ m := by
  induction w with
  | nil => exact ⟨Nat.le_refl _, hx⟩
  | cons a rest ih =>
      exact ⟨Nat.le_trans ih.1 (le_act family m a _ ih.2), act_le family m a _⟩

theorem word_mono (family : BinaryFamily) (m : Nat) (w : List Nat) {x y : Nat} (hxy : x ≤ y) :
    wordAct family m w x ≤ wordAct family m w y := by
  induction w with
  | nil => exact hxy
  | cons a rest ih => exact act_mono family m a ih

theorem word_strict (family : BinaryFamily) (m : Nat) (w : List Nat) {x y : Nat}
    (hxy : x < y) (hy : y ≤ m) (hcap : wordAct family m w y < m) :
    wordAct family m w x < wordAct family m w y := by
  induction w with
  | nil => exact hxy
  | cons a rest ih =>
      have hb := word_bounds family m rest hy
      have hlow := le_act family m a _ hb.2
      have hc : wordAct family m rest y < m := Nat.lt_of_le_of_lt hlow hcap
      exact act_strict_below_cap family m a _ _ (ih hc) hcap

theorem word_signature (family : BinaryFamily) (m : Nat) (w : List Nat) (b : Nat) :
    signature m (wordTerm family m w b) = wordAct family m w (signature m b) := by
  induction w with
  | nil => rfl
  | cons a rest ih => simp only [wordTerm, wordAct, signature_mul, ih]

theorem word_action (family : BinaryFamily) (m : Nat) (w : List Nat) (b x : Nat) :
    act family m (wordTerm family m w b) (wordAct family m w x) =
      wordAct family m w (act family m b x) := by
  induction w with
  | nil => rfl
  | cons a rest ih => simp only [wordTerm, wordAct, act_application, ih]

theorem word_application (family : BinaryFamily) (m : Nat) (w : List Nat) (b c : Nat) :
    wordTerm family m w ((family m).mul b c) =
      (family m).mul (wordTerm family m w b) (wordTerm family m w c) := by
  induction w with
  | nil => rfl
  | cons a rest ih =>
      simp only [wordTerm, ih]
      exact (family m).mul_distrib a _ _

theorem word_congruent (family : BinaryFamily) (m : Nat) (w : List Nat) {r a b : Nat}
    (hab : congruent m r a b) :
    congruent m (wordAct family m w r) (wordTerm family m w a) (wordTerm family m w b) := by
  induction w with
  | nil => exact hab
  | cons e rest ih => exact congruent_transport family m ih e

def WordAboveOne (m : Nat) (w : List Nat) : Prop := ∀ a ∈ w, 1 < signature m a

theorem word_fixes_low (family : BinaryFamily) (m : Nat) {w : List Nat}
    (hw : WordAboveOne m w) {x : Nat} (hx : x ≤ 1) : wordAct family m w x = x := by
  induction w with
  | nil => rfl
  | cons a rest ih =>
      have ha := hw a (by simp)
      have hr : WordAboveOne m rest := fun b hb => hw b (by simp [hb])
      simp only [wordAct, ih hr]
      exact fixes_below_signature family m a x (by omega)

/-- Conjugating each factor is an actual finite list operation. -/
def pushWord (family : BinaryFamily) (m e : Nat) (w : List Nat) : List Nat := w.map ((family m).mul e)

theorem pushWord_term (family : BinaryFamily) (m e : Nat) (w : List Nat) (b : Nat) :
    wordTerm family m (pushWord family m e w) ((family m).mul e b) =
      (family m).mul e (wordTerm family m w b) := by
  induction w with
  | nil => rfl
  | cons a rest ih =>
      change (family m).mul ((family m).mul e a)
        (wordTerm family m (pushWord family m e rest) ((family m).mul e b)) = _
      rw [ih, ← (family m).mul_distrib]
      rfl

theorem pushWord_above (family : BinaryFamily) (m e : Nat) {w : List Nat}
    (hw : WordAboveOne m w) : WordAboveOne m (pushWord family m e w) := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  rw [signature_mul]
  exact Nat.lt_of_lt_of_le (hw b hb) (le_act family m e _ (signature_le _ _))

#print axioms word_strict
#print axioms word_action
#print axioms word_congruent
#print axioms pushWord_term

end LaverLowerBounds.FiniteTable
