import IPDProfileAtoms
import IPDProfileLower
import IPDTreeSupport

/-! Every operation preserves the specified ROOT/SELF alphabet. -/

namespace IPD.Layer
set_option autoImplicit false
set_option maxHeartbeats 1000000
universe u v
variable {X : Type u} {Y : Type v}

theorem rename_all (P : X → Prop) (Q : Y → Prop) (f : X → Y)
    (hf : ∀ x, P x → Q (f x)) (d : Nat) :
    ∀ t, AllAtoms P d t → AllAtoms Q d (rename f d t) := by
  induction d with
  | zero => exact hf
  | succ d ih =>
    intro t ht
    apply Tree.all_rename
      (fun h : WithTop (Layer X d) => match h with | none => True | some a => AllAtoms P d a)
      (fun h : WithTop (Layer Y d) => match h with | none => True | some a => AllAtoms Q d a)
      (WithTop.map (rename f d)) ?_ t ht
    intro h hh
    cases h with
    | top => trivial
    | coe h => exact ih h hh

theorem seed_all (P : Nat → Prop) (parent child index : Nat)
    (hp : P parent) (hc : P child) (d : Nat) :
    AllAtoms P d (seed parent child index d) := by
  cases d with
  | zero =>
    change P (if index = 0 then parent else child)
    split <;> assumption
  | succ d =>
    change Tree.All _ (if index = 0 then Tree.zero else
      Tree.node (⊤ : WithTop (Layer Nat d)) (List.replicate (index-1) Tree.zero))
    split
    · exact Tree.all_zero _
    · apply (Tree.all_node_iff _ _ _).mpr
      refine ⟨True.intro, ?_⟩
      intro t ht
      have he : t = Tree.zero := (List.mem_replicate.mp ht).2
      rw [he]
      exact Tree.all_zero _

def Allowed (parent child : Nat) (i : Nat) : Prop := i ≤ parent ∨ i = child

theorem lower_valid (parent child index d : Nat) :
    ∀ a, AllAtoms (Allowed parent child) d a →
      ∀ b, lower parent child index d a = some b → AllAtoms (Allowed parent child) d b := by
  induction d with
  | zero =>
    change ∀ a : Nat, (a ≤ parent ∨ a = child) → ∀ b : Nat,
      (if a = 0 then none else if a = child then some parent else some (a-1)) = some b →
      b ≤ parent ∨ b = child
    intro a ha b hab
    split at hab
    · cases hab
    · split at hab
      · have hb := Option.some.inj hab
        omega
      · have hb := Option.some.inj hab
        omega
  | succ d ih =>
    intro a ha b hab
    rw [AllAtoms] at ha ⊢
    apply Tree.lower_all _ index _ ?_ a ha b hab
    intro h hh g hhg
    cases h with
    | top =>
      have he : (seed parent child index d : WithTop (Layer Nat d)) = g := Option.some.inj hhg
      rw [← he]
      exact seed_all (Allowed parent child) parent child index (.inl le_rfl) (.inr rfl) d
    | coe h =>
      change Option.map (fun b : Layer Nat d => (b : WithTop (Layer Nat d)))
        (lower parent child index d h) = some g at hhg
      cases he : lower parent child index d h with
      | none => simp [he] at hhg
      | some h' =>
        have hval : (h' : WithTop (Layer Nat d)) = g := by simpa [he] using hhg
        rw [← hval]
        exact ih h hh h' he

end IPD.Layer

namespace IPD
universe u v
variable {X : Type u} {Y : Type v}

theorem profileAtoms_rename (P : X → Prop) (Q : Y → Prop) (f : X → Y)
    (hf : ∀ x, P x → Q (f x)) (p : Profile X) (hp : ProfileAtoms P p) :
    ProfileAtoms Q (renameProfile f p) := Layer.rename_all P Q f hf p.1 p.2 hp

theorem lowerProfile_valid (parent child index : Nat) (p q : Profile Nat)
    (hp : ProfileAtoms (Layer.Allowed parent child) p)
    (h : lowerProfile parent child index p = some q) :
    ProfileAtoms (Layer.Allowed parent child) q := by
  rcases p with ⟨d, a⟩
  dsimp only [lowerProfile] at h
  cases he : Layer.lower parent child index d a with
  | some b =>
    rw [he] at h
    have hq := Option.some.inj h
    rw [← hq]
    exact Layer.lower_valid parent child index d a hp b he
  | none =>
    rw [he] at h
    cases d with
    | zero => cases h
    | succ k =>
      have hq := Option.some.inj h
      rw [← hq]
      exact Layer.seed_all (Layer.Allowed parent child) parent child index (.inl le_rfl) (.inr rfl) k

end IPD

#print axioms IPD.Layer.rename_all
#print axioms IPD.Layer.lower_valid
#print axioms IPD.lowerProfile_valid
