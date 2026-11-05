import LaverLowerBounds.SigmaPadding

set_option autoImplicit false

namespace LaverLowerBounds.ParentBMS

theorem two_mul_le_pow {x : Nat} (hx : 0 < x) : 2 * x ≤ 2 ^ x := by
  induction x with
  | zero => omega
  | succ x ih =>
      by_cases hz : x = 0
      · subst x; decide
      · have hh := ih (by omega)
        rw [Nat.pow_succ]
        omega

theorem CopyFrame.advance_length (f : CopyFrame) (n : Nat) :
    (f.advance n).stem.length = f.stem.length + n * f.width := by
  induction n generalizing f with
  | zero => simp [CopyFrame.advance]
  | succ n ih =>
      change (f.next.advance n).stem.length = _
      rw [ih, f.next_width]
      change f.out.length + n * f.width = _
      rw [f.out_length, Nat.add_mul]
      simp only [Nat.one_mul]
      omega

theorem CopyFrame.expand_length (f : CopyFrame) (n : Nat) :
    (expandTail f.stem f.last n).length = f.stem.length + n * f.width := by
  rw [← f.advance_stem]
  exact f.advance_length n

theorem CopyFrame.parameter_room (f : CopyFrame) {x : Nat} (hx : 0 < x) :
    (expandTail f.stem f.last x).length + x ≤ (expandTail f.stem f.last (2 ^ x)).length := by
  rw [f.expand_length, f.expand_length]
  have hpow := Nat.mul_le_mul_right f.width (two_mul_le_pow hx)
  have hxd : x ≤ x * f.width := by
    have hh := Nat.mul_le_mul_left x (Nat.succ_le_of_lt f.width_pos)
    simpa only [Nat.mul_one] using hh
  rw [Nat.mul_assoc] at hpow
  omega

/-- The actual fixed-[1] count of Sigma(M Z^x) strictly controls that of
Sigma(M[x] Z^x). Binary sprouts suffice; no tower-valued forest oracle is used. -/
theorem sigma_limit_budget {s : Matrix} {x n : Nat} (hpos : PositiveTail s)
    (hl : Leftward s) (hn : Nested s) (hx : 0 < x)
    (ht : PrefixDescent.Stops (fun a => expand a 1) (sigma (s ++ List.replicate x [])) n) :
    ∃ k, PrefixDescent.Stops (fun a => expand a 1)
        (sigma (expand s x ++ List.replicate x [])) k ∧
      (2 ^ (x + 1) - 1) + k ≤ n ∧ k < n := by
  obtain ⟨stem, last, rfl, hlast⟩ := hpos
  cases hc : last.getLast? with
  | none => exact False.elim (hlast (List.getLast?_eq_none_iff.mp hc))
  | some root =>
      have hr : root < stem.length := hl (last.length - 1) stem.length root (by
        rw [parent_last, ← List.getLast?_eq_getElem?]; exact hc)
      let f : CopyFrame := ⟨stem, last, root, hc, hr, hl, hn⟩
      have hg := append_zeros_graph hl hn x
      have hcover : Cover (sprout f.sigmaFrame.stem f.sigmaFrame.last x)
          (sigma ((stem ++ [last]) ++ List.replicate x [])) := by
        have hh := sigma_sprout_cover hl hn hx
        rw [sigma_append_last] at hh
        simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel] at hh
        exact hh
      have hbush := f.sigmaFrame.sprout_graph x
      obtain ⟨j, hj, hjn⟩ := hcover.stops ht hbush.1 hbush.2 (sigma_leftward hg.1) (sigma_nested hg.1 hg.2)
      obtain ⟨remaining, hremaining, hbudget⟩ := f.sigmaFrame.sprout_index_budget hj
      rw [f.sigma_expand] at hremaining
      have hlarge : PrefixDescent.Stops (fun a => expand a 1)
          (sigma (expand (stem ++ [last]) (2 ^ x))) remaining := by
        rw [expand_append]
        exact hremaining
      have hsmallg := expand_graph_all hl hn x
      have hlargeg := expand_graph_all hl hn (2 ^ x)
      have hexp : x ≤ 2 ^ x := by have := two_mul_le_pow hx; omega
      have hroom : (expand (stem ++ [last]) x).length + x ≤ (expand (stem ++ [last]) (2 ^ x)).length := by
        simp only [expand_append]
        exact f.parameter_room hx
      let coverNext := sigma_padding_cover (expand_prefix (stem ++ [last]) hexp) hsmallg.1 hsmallg.2 hx hroom
      have hsmallpad := append_zeros_graph hsmallg.1 hsmallg.2 x
      obtain ⟨k, hk, hkr⟩ := coverNext.stops hlarge
        (sigma_leftward hsmallpad.1) (sigma_nested hsmallpad.1 hsmallpad.2)
        (sigma_leftward hlargeg.1) (sigma_nested hlargeg.1 hlargeg.2)
      have hcost : 0 < 2 ^ (x + 1) - 1 := by
        rw [Nat.pow_succ]
        have := Nat.two_pow_pos x
        omega
      exact ⟨k, hk, by omega, by omega⟩

#print axioms sigma_limit_budget

end LaverLowerBounds.ParentBMS
