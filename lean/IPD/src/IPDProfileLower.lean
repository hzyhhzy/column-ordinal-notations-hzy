import IPDProfileOrder
import IPDTreeLower

/-! The current zero-start IPD seeds and lowering operation, with natural
ROOT addresses and SELF=child. Parent<child is the only premise of strictness.
The full profile operation drops a level at an internal minimum and deletes
only the minimum of level zero. -/

namespace IPD
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Layer

def seed (parent child index : Nat) : (d : Nat) → Layer Nat d
  | 0 => if index = 0 then parent else child
  | d+1 => if index = 0 then Tree.zero else
      Tree.node (⊤ : WithTop (Layer Nat d)) (List.replicate (index-1) Tree.zero)

noncomputable def lower (parent child index : Nat) :
    (d : Nat) → Layer Nat d → Option (Layer Nat d)
  | 0 => fun (a : Nat) => if a = 0 then none else if a = child then some parent else some (a-1)
  | d+1 => Tree.lower index (fun h => match h with
      | none => some (seed parent child index d : WithTop (Layer Nat d))
      | some a => Option.map (fun b : Layer Nat d => (b : WithTop (Layer Nat d)))
          (lower parent child index d a))

theorem lower_lt (parent child index : Nat) (hpc : parent < child) (d : Nat) :
    ∀ a b : Layer Nat d, lower parent child index d a = some b → b < a := by
  induction d with
  | zero =>
    change ∀ a b : Nat,
      (if a = 0 then none else if a = child then some parent else some (a-1)) = some b → b < a
    intro a b hab
    split at hab
    · cases hab
    · rename_i ha
      split at hab
      · rename_i hac
        have hb := Option.some.inj hab
        omega
      · have hb := Option.some.inj hab
        omega
  | succ d ih =>
    intro a b hab
    apply Tree.lower_lt index _ ?_ a b hab
    intro h g hhg
    cases h with
    | top =>
      have heq : (seed parent child index d : WithTop (Layer Nat d)) = g := Option.some.inj hhg
      rw [← heq]
      exact WithTop.coe_lt_top _
    | coe h =>
      change Option.map (fun b : Layer Nat d => (b : WithTop (Layer Nat d)))
        (lower parent child index d h) = some g at hhg
      cases heq : lower parent child index d h with
      | none => simp [heq] at hhg
      | some h' =>
        have hval : (h' : WithTop (Layer Nat d)) = g := by simpa [heq] using hhg
        rw [← hval]
        exact WithTop.coe_lt_coe.mpr (ih h h' heq)

end Layer

noncomputable def lowerProfile (parent child index : Nat) (p : Profile Nat) : Option (Profile Nat) :=
  match p with
  | ⟨d, a⟩ => match Layer.lower parent child index d a with
    | some b => some ⟨d, b⟩
    | none => match d with
      | 0 => none
      | k+1 => some ⟨k, Layer.seed parent child index k⟩

theorem lowerProfile_lt (parent child index : Nat) (hpc : parent < child)
    (p q : Profile Nat) (h : lowerProfile parent child index p = some q) : q < p := by
  rcases p with ⟨d, a⟩
  dsimp only [lowerProfile] at h
  cases heq : Layer.lower parent child index d a with
  | some b =>
    rw [heq] at h
    have hq := Option.some.inj h
    rw [← hq]
    exact profile_lt_same_level (Layer.lower_lt parent child index hpc d a b heq)
  | none =>
    rw [heq] at h
    cases d with
    | zero => cases h
    | succ k =>
      have hq := Option.some.inj h
      rw [← hq]
      exact profile_lt_of_level_lt _ _ (Nat.lt_succ_self k)

end IPD

#print axioms IPD.Layer.lower_lt
#print axioms IPD.lowerProfile_lt
