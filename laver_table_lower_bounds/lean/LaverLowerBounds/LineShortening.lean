import LaverLowerBounds.FiniteLines
import LaverLowerBounds.SignatureMovement

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable.Lined

variable {family : BinaryFamily} {m root n a b : Nat}

/-- Merge the first two actual segments, preserving both endpoints and root. -/
theorem contract {n a b : Nat} (line : Lined family m root (n + 2) a b)
    (hra : root < a) : Lined family m root (n + 1) a b := by
  cases line with
  | @cons _ a y b U hU hUa hUy hay tail =>
      cases tail with
      | @cons _ y z b V hV hVy hVz hyz rest =>
          let W := (family m).mul V V
          have wsig : signature m W = y := by dsimp [W]; rw [signature_mul, hV, hVy]
          have wr : act family m W root = root :=
            fixes_below_signature family m W root (by rw [wsig]; omega)
          have wa : act family m W a = a :=
            fixes_below_signature family m W a (by rw [wsig]; exact hay)
          have wy : act family m W y = z := by
            have he := act_application family m V V root
            rw [hVy, hVz] at he
            exact he
          refine Lined.cons ((family m).mul W U) ?_ ?_ ?_ (by omega) rest
          · rw [signature_mul, hU, wr]
          · have he := act_application family m W U root
            rw [wr, hUa, wa] at he
            exact he
          · have he := act_application family m W U a
            rw [wa, hUy, wy] at he
            exact he

/-- Any positive shorter length is attainable, with both endpoints retained. -/
theorem shorten (line : Lined family m root n a b) (hra : root < a)
    {k : Nat} (hk : 0 < k) (hkn : k ≤ n) : Lined family m root k a b := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      by_cases he : k = n
      · exact he ▸ line
      · have hn : 2 ≤ n := by omega
        have heq : n = (n - 2) + 2 := by omega
        have shorter := (heq ▸ line).contract hra
        exact ih ((n - 2) + 1) (by omega) shorter (by omega)

#print axioms contract
#print axioms shorten

end LaverLowerBounds.FiniteTable.Lined
