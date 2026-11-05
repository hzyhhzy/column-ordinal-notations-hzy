import LaverLowerBounds.SigmaExpansion

set_option autoImplicit false

namespace LaverLowerBounds.ParentBMS

theorem expand_graph_all {s : Matrix} (hl : Leftward s) (hn : Nested s) (n : Nat) :
    Leftward (expand s n) ∧ Nested (expand s n) := by
  by_cases he : s = []
  · simpa only [he, expand_empty] using And.intro (he ▸ hl) (he ▸ hn)
  · obtain ⟨stem, last, rfl⟩ := exists_last he
    rw [expand_append]
    cases hc : last.getLast? with
    | none =>
        have hz := List.getLast?_eq_none_iff.mp hc
        subst last
        rw [expandTail_empty]
        exact ⟨leftward_prefix ⟨[[]], rfl⟩ hl, nested_prefix ⟨[[]], rfl⟩ hl hn⟩
    | some root =>
        have hr : root < stem.length := hl (last.length - 1) stem.length root (by
          rw [parent_last, ← List.getLast?_eq_getElem?]; exact hc)
        let f : CopyFrame := ⟨stem, last, root, hc, hr, hl, hn⟩
        have hf := f.advance_stem n
        change (f.advance n).stem = expandTail stem last n at hf
        rw [← hf]
        exact ⟨leftward_prefix ⟨[(f.advance n).last], rfl⟩ (f.advance n).leftward,
          nested_prefix ⟨[(f.advance n).last], rfl⟩ (f.advance n).leftward (f.advance n).nested⟩

theorem sigma_prefix {s t : Matrix} (hp : s.IsPrefix t) : (sigma s).IsPrefix (sigma t) := by
  obtain ⟨tail, rfl⟩ := hp
  rw [sigma_append]
  exact ⟨_, rfl⟩

theorem zeros_tail_no_parent {s : Matrix} {n q i p : Nat} (hi : s.length ≤ i) :
    parent (s ++ List.replicate n []) q i ≠ some p := by
  intro hp
  obtain ⟨c, hc, hcp⟩ := parent_some_iff.mp hp
  rw [List.getElem?_append_right hi] at hc
  have he : c = [] := List.eq_of_mem_replicate (List.mem_of_getElem? hc)
  simp [he] at hcp

theorem append_zeros_graph {s : Matrix} (hl : Leftward s) (hn : Nested s) (n : Nat) :
    Leftward (s ++ List.replicate n []) ∧ Nested (s ++ List.replicate n []) := by
  constructor
  · intro q i p hp
    by_cases hi : i < s.length
    · rw [parent_append_left hi] at hp; exact hl q i p hp
    · exact False.elim (zeros_tail_no_parent (by omega) hp)
  · intro q i p hp
    by_cases hi : i < s.length
    · rw [parent_append_left hi] at hp
      exact (hn q i p hp).to_prefix_extension ⟨List.replicate n [], rfl⟩
    · exact False.elim (zeros_tail_no_parent (by omega) hp)

theorem leaves_tail_row_zero {s : Matrix} {n root q p i : Nat} (hi : s.length ≤ i)
    (hp : parent (s ++ List.replicate n [root]) q i = some p) : q = 0 := by
  obtain ⟨c, hc, hcp⟩ := parent_some_iff.mp hp
  rw [List.getElem?_append_right hi] at hc
  have he : c = [root] := List.eq_of_mem_replicate (List.mem_of_getElem? hc)
  have hq := (List.getElem?_eq_some_iff.mp hcp).1
  simp only [he, List.length_singleton] at hq
  omega

theorem sigma_zeros_tail_row_zero {s : Matrix} {n q p i : Nat} (hi : (sigma s).length ≤ i)
    (hp : parent (sigma (s ++ List.replicate n [])) q i = some p) : q = 0 := by
  cases i with
  | zero => rw [sigma_length] at hi; omega
  | succ i =>
      cases q with
      | zero => rfl
      | succ q =>
          rw [sigma_parent_succ] at hp
          cases he : parent (s ++ List.replicate n []) q i with
          | none => simp [he] at hp
          | some a =>
              exact False.elim (zeros_tail_no_parent (by rw [sigma_length] at hi; omega) he)

def padColumn (base source target : Matrix) (i : Nat) :=
  if i < base.length then i else i + (target.length - source.length)

theorem padColumn_strict {base source target : Matrix} {i j : Nat} (hij : i < j) :
    padColumn base source target i < padColumn base source target j := by
  unfold padColumn
  split <;> split <;> omega

theorem padColumn_bounded {base source target : Matrix} (hbase : base.length ≤ source.length)
    (hsize : source.length ≤ target.length) {i : Nat} (hi : i < source.length) :
    padColumn base source target i < target.length := by
  unfold padColumn
  split <;> omega

/-- Preserve a common prefix and move a one-row tail to the final target
columns. The target's complete bottom chain supplies the skipped edges. -/
def paddingCover {base source target : Matrix} (hsrc : base.IsPrefix source) (htgt : base.IsPrefix target)
    (hl : Leftward source) (hsize : source.length ≤ target.length) (htail : base.length < source.length)
    (hrow : ∀ q p i, parent source q i = some p → base.length ≤ i → q = 0)
    (hchain : ∀ p i, p < i → i < target.length → Ancestor target 0 p i) : Cover source target where
  column := padColumn base source target
  bounded _ hi := padColumn_bounded hsrc.length_le hsize hi
  strict _ _ hij _ := padColumn_strict hij
  edge q p i hp := by
    have hi := parent_column_lt hp
    have hpi := hl q i p hp
    by_cases hold : i < base.length
    · simp only [padColumn, if_pos hold, if_pos (by omega : p < base.length)]
      apply Ancestor.direct
      rw [parent_prefix htgt hold, ← parent_prefix hsrc hold]
      exact hp
    · have hq := hrow q p i hp (by omega)
      subst q
      exact hchain _ _ (padColumn_strict hpi) (padColumn_bounded hsrc.length_le hsize hi)
  last _ := by
    simp only [padColumn, if_neg (by omega : ¬ source.length - 1 < base.length)]
    omega

def sigma_sprout_cover {s : Matrix} (hl : Leftward s) (hn : Nested s) {x : Nat} (hx : 0 < x) :
    Cover (sigma s ++ List.replicate x [(sigma s).length - 1]) (sigma (s ++ List.replicate x [])) := by
  have hg := append_leaves_graph (s := sigma s) (root := (sigma s).length - 1)
    (by rw [sigma_length]; omega) (sigma_leftward hl) (sigma_nested hl hn) x
  refine paddingCover ⟨_, rfl⟩ (sigma_prefix ⟨_, rfl⟩) hg.1 ?_ ?_
    (fun _ _ _ hp hi => leaves_tail_row_zero hi hp) (fun _ _ hpi hi => sigma_chain hpi hi)
  · simp only [sigma_length, List.length_append, List.length_replicate]; omega
  · simp only [List.length_append, List.length_replicate]; omega

def sigma_padding_cover {s t : Matrix} (hp : s.IsPrefix t) (hl : Leftward s) (hn : Nested s)
    {x : Nat} (hx : 0 < x) (hwidth : s.length + x ≤ t.length) :
    Cover (sigma (s ++ List.replicate x [])) (sigma t) := by
  have hg := append_zeros_graph hl hn x
  refine paddingCover (sigma_prefix ⟨_, rfl⟩) (sigma_prefix hp) (sigma_leftward hg.1) ?_ ?_
    (fun _ _ _ hp hi => sigma_zeros_tail_row_zero hi hp) (fun _ _ hpi hi => sigma_chain hpi hi)
  · simp only [sigma_length, List.length_append, List.length_replicate]; omega
  · simp only [sigma_length, List.length_append, List.length_replicate]; omega

#print axioms expand_graph_all
#print axioms sigma_sprout_cover
#print axioms sigma_padding_cover

end LaverLowerBounds.ParentBMS
