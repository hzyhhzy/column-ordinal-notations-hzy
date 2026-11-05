import LaverLowerBounds.ParentBMS

set_option autoImplicit false

namespace LaverLowerBounds.ParentBMS

/-- Only the elementary shape conditions, not the stronger canonical-parent
condition needed to identify the algorithm with numerical BM4. -/
def Shape (h start : Nat) (s : Matrix) : Prop :=
  ∀ i c, s[i]? = some c → c.length ≤ h ∧ ∀ p ∈ c, p < start + i

theorem shape_get {h start : Nat} {s : Matrix} (hs : Shape h start s)
    {i : Nat} (hi : i < s.length) :
    (s[i]?.getD []).length ≤ h ∧ ∀ p ∈ s[i]?.getD [], p < start + i := by
  simpa only [List.getElem?_eq_getElem hi, Option.getD_some] using
    hs i s[i] (List.getElem?_eq_getElem hi)

theorem shape_append {h start : Nat} {a b : Matrix} (ha : Shape h start a)
    (hb : Shape h (start + a.length) b) : Shape h start (a ++ b) := by
  intro i c hi
  by_cases hit : i < a.length
  · rw [List.getElem?_append_left hit] at hi
    exact ha i c hi
  · rw [List.getElem?_append_right (by omega)] at hi
    obtain ⟨hc, hp⟩ := hb (i - a.length) c hi
    exact ⟨hc, fun p hm => by have := hp p hm; omega⟩

theorem shape_stem {h start : Nat} {stem : Matrix} {last : Column}
    (hs : Shape h start (stem ++ [last])) : Shape h start stem := by
  intro i c hi
  have hit := (List.getElem?_eq_some_iff.mp hi).1
  exact hs i c (by rw [List.getElem?_append_left hit]; exact hi)

theorem shape_last {h start : Nat} {stem : Matrix} {last : Column}
    (hs : Shape h start (stem ++ [last])) :
    last.length ≤ h ∧ ∀ p ∈ last, p < start + stem.length := by
  exact hs stem.length last (by simp)

theorem shift_zero (root p : Nat) : shift root 0 p = p := by
  unfold shift
  split <;> omega

theorem copy_zero (stem : Matrix) (last : Column) (row root width : Nat) :
    copy stem last row root width 0 =
      (List.range width).map (fun i => if i = 0 then
        last.take row ++ (stem[root]?.getD []).drop row
        else (stem[root + i]?.getD []).map (shift root width)) := by
  have hz : shift root 0 = id := funext (shift_zero root)
  simp [copy, hz]

theorem copy_length (stem : Matrix) (last : Column) (row root width b : Nat) :
    (copy stem last row root width b).length = width := by simp [copy]

theorem copy_zero_shape {h : Nat} {stem : Matrix} {last : Column} {root : Nat}
    (hs : Shape h 0 stem) (hl : last.length ≤ h)
    (hp : ∀ p ∈ last, p < stem.length) (hr : root < stem.length) :
    Shape h stem.length (copy stem last (last.length - 1) root (stem.length - root) 0) := by
  intro i c hc
  rw [copy_zero] at hc
  obtain ⟨hi, hci⟩ := List.getElem?_eq_some_iff.mp hc
  have hi' : i < stem.length - root := by simpa using hi
  simp only [List.getElem_map, List.getElem_range] at hci
  by_cases hiz : i = 0
  · subst i
    simp only [↓reduceIte] at hci
    subst c
    obtain ⟨hrh, hrp⟩ := shape_get hs hr
    constructor
    · simp only [List.length_append, List.length_take, List.length_drop]
      omega
    · intro p hm
      rcases List.mem_append.mp hm with hm | hm
      · have hm' : p ∈ last := List.mem_of_mem_take hm
        have := hp p hm'
        omega
      · have hm' : p ∈ stem[root]?.getD [] := List.mem_of_mem_drop hm
        have := hrp p hm'
        omega
  · rw [if_neg hiz] at hci
    subst c
    obtain ⟨hch, hcp⟩ := shape_get hs (show root + i < stem.length by omega)
    constructor
    · simpa using hch
    · intro p hm
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
      have hq' := hcp q hq
      unfold shift
      split <;> omega

theorem expandTail_one_positive {stem : Matrix} {last : Column} {root : Nat}
    (hl : last.getLast? = some root) :
    expandTail stem last 1 =
      stem ++ copy stem last (last.length - 1) root (stem.length - root) 0 := by
  simp [expandTail, hl, List.range_succ]

theorem expandTail_one_shape {h : Nat} {stem : Matrix} {last : Column}
    (hs : Shape h 0 (stem ++ [last])) : Shape h 0 (expandTail stem last 1) := by
  obtain ⟨hl, hp⟩ := shape_last hs
  have hstem := shape_stem hs
  cases he : last.getLast? with
  | none => simpa [expandTail, he] using hstem
  | some root =>
      have hr : root < stem.length := by
        simpa using hp root (List.mem_of_getLast? he)
      rw [expandTail_one_positive he]
      exact shape_append hstem (by simpa using copy_zero_shape hstem hl (by simpa using hp) hr)

theorem expand_one_shape {h : Nat} {s : Matrix} (hs : Shape h 0 s) :
    Shape h 0 (expand s 1) := by
  cases he : s.reverse with
  | nil =>
      have hz : s = [] := by simpa using congrArg List.reverse he
      subst s
      simpa using hs
  | cons last rest =>
      have hz : s = rest.reverse ++ [last] := by simpa using congrArg List.reverse he
      subst s
      rw [expand_append]
      exact expandTail_one_shape hs

def ready (h : Nat) (s : Matrix) : Bool :=
  match s.getLast? with
  | none => false
  | some last => decide (last.length = h ∧ last.getLast? = some (s.length - 2))

theorem ready_append (h : Nat) (stem : Matrix) (last : Column) :
    ready h (stem ++ [last]) =
      decide (last.length = h ∧ last.getLast? = some (stem.length - 1)) := by
  simp [ready]

/-- A narrow copy cannot retain the full-height, width-one exceptional state.
If the result is full height, its top parent comes from the root column and
therefore lies strictly to the left of that root. -/
theorem splice_not_ready {h row root : Nat} {last base : Column}
    (hrh : row < h) (hp : ∀ p ∈ base, p < root) :
    ¬ ((last.take row ++ base.drop row).length = h ∧
      (last.take row ++ base.drop row).getLast? = some root) := by
  intro ⟨hlen, hlast⟩
  have hn : base.drop row ≠ [] := by
    intro he
    rw [he, List.append_nil, List.length_take] at hlen
    omega
  have he : (base.drop row).getLast? = some root := by
    simpa [List.getLast?_append, List.getLast?_eq_some_getLast hn] using hlast
  have hm : root ∈ base := List.mem_of_mem_drop (List.mem_of_getLast? he)
  have := hp root hm
  omega

theorem narrow_clears_ready {h : Nat} {stem : Matrix} {last : Column} {root : Nat}
    (hs : Shape h 0 (stem ++ [last])) (he : last.getLast? = some root)
    (hw : stem.length - root = 1) : ready h (expandTail stem last 1) = false := by
  obtain ⟨hlh, hlp⟩ := shape_last hs
  have hr : root < stem.length := by simpa using hlp root (List.mem_of_getLast? he)
  have hroot : root = stem.length - 1 := by omega
  have hlen : 0 < last.length := by
    have hn : last ≠ [] := fun hz => by simp [hz] at he
    exact List.length_pos_iff.mpr hn
  obtain ⟨_, hp⟩ := shape_get (shape_stem hs) hr
  rw [expandTail_one_positive he, hw, copy_zero]
  simp only [List.range_one, List.map_cons, List.map_nil, ↓reduceIte]
  rw [ready_append]
  apply decide_eq_false
  rw [← hroot]
  exact splice_not_ready (by omega) (by simpa using hp)

#print axioms expand_one_shape
#print axioms narrow_clears_ready

end LaverLowerBounds.ParentBMS
