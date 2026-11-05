import LaverLowerBounds.FiniteCapped

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable

theorem fixes_below_signature (family : BinaryFamily) (m a x : Nat)
    (hx : x < signature m a) : act family m a x = x := by
  have hs := signature_le m a
  have hxm : x + 1 ≤ m := by omega
  have hz : a % 2 ^ (x + 1) = 0 := (le_signature m a (x + 1) hxm).mp (by omega)
  have he : (family (x + 1)).mul a (2 ^ x) = 2 ^ x := by
    rw [← (family (x + 1)).mul_mod_left a, hz, (family (x + 1)).zero_mul]
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_succ (by decide : 1 < 2))
  have hlo := le_act family m a x (by omega)
  have hnot : ¬ x + 1 ≤ act family m a x := by
    intro h
    have hbad := (le_act_iff family m a x (x + 1) hxm).mp h
    rw [he] at hbad
    have := Nat.two_pow_pos x
    omega
  omega

/-- A finite line consists of actual table actors, not just ordered endpoints.
The root is each actor's signature. All endpoints lie below the finite cap. -/
inductive Lined (family : BinaryFamily) (m root : Nat) : Nat → Nat → Nat → Prop
  | nil {a} : a < m → Lined family m root 0 a a
  | cons {n a b c} (owner : Nat) :
      signature m owner = root → act family m owner root = a →
      act family m owner a = b → a < b →
      Lined family m root n b c → Lined family m root (n + 1) a c

namespace Lined

variable {family : BinaryFamily} {m root n a b : Nat}

theorem endpoints (line : Lined family m root n a b) : a ≤ b ∧ b < m := by
  induction line with
  | nil h => exact ⟨Nat.le_refl _, h⟩
  | cons _ _ _ _ hab _ ih => exact ⟨Nat.le_trans (Nat.le_of_lt hab) ih.1, ih.2⟩

theorem append {n k a b c : Nat} (first : Lined family m root n a b)
    (second : Lined family m root k b c) : Lined family m root (n + k) a c := by
  induction first with
  | nil _ => simpa using second
  | cons owner hsig hroot hnext hlt _ ih =>
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Lined.cons owner hsig hroot hnext hlt (ih second)

theorem map (line : Lined family m root n a b) (e : Nat)
    (hcap : act family m e b < m) :
    Lined family m (act family m e root) n (act family m e a) (act family m e b) := by
  induction line with
  | nil _ => exact .nil hcap
  | @cons n a b c owner hsig hroot hnext hab tail ih =>
      have ht := tail.endpoints
      have hb : act family m e b < m :=
        Nat.lt_of_le_of_lt (act_mono family m e ht.1) hcap
      apply Lined.cons ((family m).mul e owner)
      · rw [signature_mul, hsig]
      · rw [act_application, hroot]
      · rw [act_application, hnext]
      · exact act_strict_below_cap family m e a b hab hb
      · exact ih hcap

/-- One higher-root segment doubles an existing line. -/
theorem double {c owner : Nat} (line : Lined family m root n a b)
    (hroot : root < a) (hsig : signature m owner = a)
    (ha : act family m owner a = b) (hb : act family m owner b = c) (hc : c < m) :
    Lined family m root (n + n) a c := by
  have hr : act family m owner root = root :=
    fixes_below_signature family m owner root (hsig ▸ hroot)
  have mapped := line.map owner (by omega : act family m owner b < m)
  rw [hr, ha, hb] at mapped
  exact line.append mapped

/-- The finite line multiplication rule, with every image guarded below m. -/
theorem multiply {a b c t u : Nat} (base : Lined family m root t a b)
    (higher : Lined family m a u b c) (hroot : root < a) :
    Lined family m root (t * 2 ^ u) a c := by
  induction higher generalizing t with
  | nil _ => simpa using base
  | @cons n b d c owner hsig hstart hnext hlt tail ih =>
      have hd : d < m := Nat.lt_of_le_of_lt tail.endpoints.1 tail.endpoints.2
      have doubled := base.double hroot hsig hstart hnext hd
      have result := ih doubled
      have he : (t + t) * 2 ^ n = t * 2 ^ (n + 1) := by
        rw [Nat.pow_succ, Nat.add_mul, ← Nat.mul_assoc]
        omega
      rw [he] at result
      exact result

#print axioms map
#print axioms multiply

end Lined
end LaverLowerBounds.FiniteTable
