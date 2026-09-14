import IPDProfileOrder
import Mathlib.Logic.Encodable.Basic
import Mathlib.Data.Countable.Basic
import Mathlib.Logic.Equiv.List

/-! Explicit finite syntax coding, used to keep the later closure language
countable. This is independent of the ordinal size of the tree order. -/

namespace IPD.Tree
set_option autoImplicit false
set_option maxHeartbeats 800000
universe u
variable {H : Type u}

def code [Encodable H] : Tree H → Nat
  | .zero => Encodable.encode (none : Option (H × List Nat))
  | .node h xs => Encodable.encode (some (h, xs.map code) : Option (H × List Nat))

private theorem map_inj_left {α β : Type*} (f : α → β) :
    ∀ xs : List α, (∀ x ∈ xs, ∀ y, f x = f y → x = y) →
      ∀ ys, xs.map f = ys.map f → xs = ys := by
  intro xs
  induction xs with
  | nil =>
    intro _ ys hy
    cases ys with
    | nil => rfl
    | cons y ys => simp at hy
  | cons x xs ih =>
    intro h ys hy
    cases ys with
    | nil => simp at hy
    | cons y ys =>
      have hh := List.cons.inj hy
      have hxy : x = y := h x (by simp) y hh.1
      subst y
      exact congrArg (List.cons x) (ih (fun a ha b hb => h a (by simp [ha]) b hb) ys hh.2)

theorem code_injective [Encodable H] : Function.Injective (code : Tree H → Nat) := by
  intro a
  induction a using IPD.Tree.inductionOn with
  | hz =>
    intro b hab
    cases b with
    | zero => rfl
    | node h xs =>
      have hc : (none : Option (H × List Nat)) = some (h, xs.map code) :=
        Encodable.encode_injective (by simpa only [code] using hab)
      cases hc
  | hn h xs ih =>
    intro b hab
    cases b with
    | zero =>
      have hc : some (h, xs.map code) = (none : Option (H × List Nat)) :=
        Encodable.encode_injective (by simpa only [code] using hab)
      cases hc
    | node g ys =>
      have hc : (some (h, xs.map code) : Option (H × List Nat)) = some (g, ys.map code) :=
        Encodable.encode_injective (by simpa only [code] using hab)
      have hfields : h = g ∧ xs.map code = ys.map code := by simpa using hc
      rcases hfields with ⟨rfl, hmap⟩
      exact congrArg (Tree.node h) (map_inj_left code xs ih ys hmap)

instance countable [Countable H] : Countable (Tree H) := by
  letI := Encodable.ofCountable H
  exact Function.Injective.countable code_injective

end IPD.Tree

namespace IPD
universe u

instance layerCountable (X : Type u) [Countable X] (n : Nat) : Countable (Layer X n) := by
  induction n with
  | zero => change Countable X; infer_instance
  | succ n ih =>
    change Countable (Tree (WithTop (Layer X n)))
    letI : Countable (Layer X n) := ih
    infer_instance

instance profileCountable (X : Type u) [Countable X] : Countable (Profile X) := by
  infer_instance

end IPD

#print axioms IPD.Tree.code_injective
#print axioms IPD.profileCountable
