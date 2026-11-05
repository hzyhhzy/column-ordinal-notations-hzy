import LaverLowerBounds.ParentShape

set_option autoImplicit false

namespace LaverLowerBounds.ParentBMS

/-- Every positive port after [1] has one of three concrete origins. -/
inductive PortOrigin (stem : Matrix) (last : Column) (root j r p : Nat) : Prop
  | kept (c : Column) : j < stem.length → stem[j]? = some c → c[r]? = some p →
      PortOrigin stem last root j r p
  | low : j = stem.length → r < last.length - 1 → last[r]? = some p →
      PortOrigin stem last root j r p
  | copied (q : Nat) (c : Column) (oldParent : Nat) :
      root ≤ q → q < stem.length → stem[q]? = some c → c[r]? = some oldParent →
      j = q + (stem.length - root) → p = shift root (stem.length - root) oldParent →
      PortOrigin stem last root j r p

theorem getD_some {s : Matrix} {i : Nat} (hi : i < s.length) :
    s[i]? = some (s[i]?.getD []) := by simp [List.getElem?_eq_getElem hi]

theorem expandTail_port_origin {h : Nat} {stem : Matrix} {last : Column} {root j r p : Nat}
    (hs : Shape h 0 (stem ++ [last])) (hl : last.getLast? = some root)
    {c : Column} (hj : (expandTail stem last 1)[j]? = some c) (hp : c[r]? = some p) :
    PortOrigin stem last root j r p := by
  obtain ⟨hlh, hlp⟩ := shape_last hs
  have hr : root < stem.length := by simpa using hlp root (List.mem_of_getLast? hl)
  rw [expandTail_one_positive hl] at hj
  by_cases hjold : j < stem.length
  · rw [List.getElem?_append_left hjold] at hj
    exact .kept c hjold hj hp
  · rw [List.getElem?_append_right (by omega), copy_zero] at hj
    obtain ⟨hi, hci⟩ := List.getElem?_eq_some_iff.mp hj
    have hi' : j - stem.length < stem.length - root := by simpa using hi
    simp only [List.getElem_map, List.getElem_range] at hci
    by_cases hiz : j - stem.length = 0
    · rw [if_pos hiz] at hci
      subst c
      have htlen : (last.take (last.length - 1)).length = last.length - 1 :=
        List.length_take_of_le (by omega)
      by_cases hrlo : r < last.length - 1
      · rw [List.getElem?_append_left (by omega), List.getElem?_take_of_lt hrlo] at hp
        exact .low (by omega) hrlo hp
      · rw [List.getElem?_append_right (by omega), htlen, List.getElem?_drop] at hp
        have he : last.length - 1 + (r - (last.length - 1)) = r := by omega
        rw [he] at hp
        have hb := (shape_get (shape_stem hs) hr).2 p (List.mem_of_getElem? hp)
        refine .copied root (stem[root]?.getD []) p (Nat.le_refl _) hr (getD_some hr) hp
          (by omega) ?_
        simp only [shift, if_pos (show p < root by omega)]
    · rw [if_neg hiz] at hci
      subst c
      rw [List.getElem?_map] at hp
      cases hrow : (stem[root + (j - stem.length)]?.getD [])[r]? with
      | none => simp [hrow] at hp
      | some oldParent =>
          have he : shift root (stem.length - root) oldParent = p := by simpa [hrow] using hp
          have hsource : root + (j - stem.length) < stem.length := by omega
          exact .copied (root + (j - stem.length))
            (stem[root + (j - stem.length)]?.getD []) oldParent (by omega) hsource
            (getD_some hsource) hrow (by omega) he.symm

#print axioms expandTail_port_origin

end LaverLowerBounds.ParentBMS
