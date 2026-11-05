import LaverLowerBounds.ParentTransforms

set_option autoImplicit false

namespace LaverLowerBounds.ParentBMS

theorem liftW_append (s t : Matrix) : liftW (s ++ t) = liftW s ++ t.map raiseColumn := by
  simp [liftW]

theorem liftW_lookup {s : Matrix} {i : Nat} (hi : i < s.length) :
    (liftW s)[i + 1]?.getD [] = raiseColumn (s[i]?.getD []) := by
  simp [liftW, List.getElem?_eq_getElem hi]

theorem raiseColumn_length {c : Column} (hc : c ≠ []) : (raiseColumn c).length = c.length := by
  simp [raiseColumn, hc]

theorem raiseColumn_drop {c : Column} {r : Nat} (hr : 0 < r) :
    (raiseColumn c).drop r = (c.drop r).map Nat.succ := by
  by_cases hc : c = []
  · subst c
    cases r with
    | zero => omega
    | succ r => simp [raiseColumn]
  · simp [raiseColumn, hc, ← List.map_drop]

theorem succ_shift (root offset p : Nat) :
    Nat.succ (shift root offset p) = shift (root + 1) offset (Nat.succ p) := by
  unfold shift
  split <;> split <;> omega

theorem raiseColumn_shift (root offset : Nat) (c : Column) :
    raiseColumn (c.map (shift root offset)) =
      (raiseColumn c).map (shift (root + 1) offset) := by
  by_cases hc : c = []
  · simp [hc, raiseColumn, shift]
  · have hm : c.map (shift root offset) ≠ [] := by simpa using hc
    simp only [raiseColumn, if_neg hc, if_neg hm, List.map_map]
    apply congrArg (fun g => c.map g)
    funext p
    exact succ_shift root offset p

theorem raiseColumn_head (last c : Column) {r : Nat} (hr : r < last.length)
    (root offset : Nat) :
    raiseColumn ((last.take r).map (shift root offset) ++ c.drop r) =
      ((raiseColumn last).take r).map (shift (root + 1) offset) ++ (raiseColumn c).drop r := by
  by_cases hz : r = 0
  · simp [hz]
  · have hlast : last ≠ [] := by intro he; simp [he] at hr
    have htake : last.take r ≠ [] := by
      intro he
      have hh := congrArg List.length he
      simp only [List.length_take, List.length_nil] at hh
      omega
    have hmap : (last.take r).map (shift root offset) ++ c.drop r ≠ [] := by
      intro he
      exact htake (List.map_eq_nil_iff.mp (List.append_eq_nil_iff.mp he).1)
    rw [raiseColumn_drop (by omega : 0 < r)]
    simp only [raiseColumn, if_neg hmap, if_neg hlast, ← List.map_take, List.map_append, List.map_map]
    congr 1
    apply congrArg (fun g => (last.take r).map g)
    funext p
    exact succ_shift root offset p

theorem copy_liftW {stem : Matrix} {last : Column} {root : Nat}
    (hr : root < stem.length) (hl : last ≠ []) (b : Nat) :
    copy (liftW stem) (raiseColumn last) (last.length - 1) (root + 1) (stem.length - root) b =
      (copy stem last (last.length - 1) root (stem.length - root) b).map raiseColumn := by
  simp only [copy, List.map_map]
  apply List.map_congr_left
  intro i hi
  dsimp only [Function.comp_def]
  have hiw := List.mem_range.mp hi
  by_cases hz : i = 0
  · rw [if_pos hz, if_pos hz, liftW_lookup hr]
    have hp : 0 < last.length := by cases last <;> simp_all
    exact (raiseColumn_head last (stem[root]?.getD []) (by omega)
      root (b * (stem.length - root))).symm
  · rw [if_neg hz, if_neg hz]
    have hib : root + i < stem.length := by omega
    have he : root + 1 + i = (root + i) + 1 := by omega
    rw [he, liftW_lookup hib]
    exact (raiseColumn_shift root ((b + 1) * (stem.length - root)) (stem[root + i]?.getD [])).symm

/-- Exact commutation at a nonzero last column, for every expansion index. -/
theorem liftW_expandTail {stem : Matrix} {last : Column} {root : Nat}
    (hc : last.getLast? = some root) (hr : root < stem.length) (n : Nat) :
    liftW (expandTail stem last n) = expandTail (liftW stem) (raiseColumn last) n := by
  have hl : last ≠ [] := by intro he; simp [he] at hc
  have hcontrol : (raiseColumn last).getLast? = some (root + 1) := by
    simp [raiseColumn, hl, List.getLast?_map, hc]
  have hlen := raiseColumn_length hl
  have hwidth : (liftW stem).length - (root + 1) = stem.length - root := by
    rw [liftW_length]
    omega
  simp only [expandTail, hc, hcontrol, liftW_append, hlen, hwidth, List.map_flatMap]
  apply congrArg (fun tail => liftW stem ++ tail)
  apply congrArg (fun g => (List.range n).flatMap g)
  funext b
  exact (copy_liftW hr hl b).symm

theorem liftW_expand_nonzero {stem : Matrix} {last : Column}
    (hl : last ≠ []) (hs : Leftward (stem ++ [last])) (n : Nat) :
    expand (liftW (stem ++ [last])) n = liftW (expand (stem ++ [last]) n) := by
  cases hc : last.getLast? with
  | none => exact False.elim (hl (List.getLast?_eq_none_iff.mp hc))
  | some root =>
      have hr : root < stem.length := hs (last.length - 1) stem.length root (by
        rw [parent_last, ← List.getLast?_eq_getElem?]; exact hc)
      rw [liftW_append]
      simp only [List.map_cons, List.map_nil, expand_append]
      exact (liftW_expandTail hc hr n).symm

/-- Independent translated blocks; parents never cross from one block to an
earlier block. Used to express the successor case of the W compiler. -/
def translated (offset : Nat) (s : Matrix) : Matrix :=
  s.map (fun c => c.map (fun p => p + offset))

def blockCopies (s : Matrix) (n : Nat) : Matrix :=
  (List.range n).flatMap (fun b => translated (b * s.length) s)

theorem translated_zero (s : Matrix) : translated 0 s = s := by simp [translated]

theorem blockCopies_unfold (s : Matrix) (n : Nat) :
    blockCopies s (n + 1) = s ++ (List.range n).flatMap (fun b => translated ((b + 1) * s.length) s) := by
  rw [blockCopies, List.range_succ_eq_map]
  simp only [List.flatMap_cons, List.flatMap_map, Nat.zero_mul, translated_zero, Nat.succ_eq_add_one]

theorem copy_root_zero (s : Matrix) (hs : s[0]? = some []) (b : Nat) :
    copy s [0] 0 0 s.length b = translated ((b + 1) * s.length) s := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < s.length
  · simp only [copy, List.getElem?_map, List.getElem?_range hi, Option.map_some]
    by_cases hz : i = 0
    · subst i
      simp [hs, translated]
    · rw [if_neg hz]
      simp only [Nat.zero_add, translated, List.getElem?_map, List.getElem?_eq_getElem hi,
        Option.getD_some, Option.map_some]
      simp [shift]
  · rw [List.getElem?_eq_none (by rw [copy_length]; omega),
      List.getElem?_eq_none (by simp only [translated, List.length_map]; omega)]

theorem liftW_expand_successor (s : Matrix) (n : Nat) :
    expand (liftW (s ++ [[]])) n = blockCopies (liftW s) (n + 1) := by
  rw [liftW_append]
  simp only [List.map_cons, List.map_nil, raiseColumn, ↓reduceIte, expand_append]
  simp only [expandTail, List.getLast?_singleton, List.length_cons, List.length_nil,
    Nat.add_sub_cancel, Nat.sub_zero]
  rw [blockCopies_unfold]
  apply congrArg (fun tail => liftW s ++ tail)
  apply congrArg (fun g => (List.range n).flatMap g)
  funext b
  exact copy_root_zero (liftW s) (by simp [liftW]) b

#print axioms liftW_expand_nonzero
#print axioms liftW_expand_successor

end LaverLowerBounds.ParentBMS
