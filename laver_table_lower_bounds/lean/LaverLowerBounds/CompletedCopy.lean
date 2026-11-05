import LaverLowerBounds.SproutForest

set_option autoImplicit false

namespace LaverLowerBounds.ParentBMS
namespace CopyFrame

theorem control_edge (f : CopyFrame) :
    parent (f.stem ++ [f.last]) f.row f.stem.length = some f.root := by
  rw [parent_last, row, ← List.getLast?_eq_getElem?]
  exact f.control

/-- Every parent of the last column is inside its bad block. This follows
from nesting, rather than being an extra numeric-matrix assumption. -/
theorem last_lower (f : CopyFrame) {p : Nat} (hp : p ∈ f.last) : f.root ≤ p := by
  obtain ⟨q, hq, hvalue⟩ := List.getElem_of_mem hp
  have hparent : parent (f.stem ++ [f.last]) q f.stem.length = some p := by
    rw [parent_last, List.getElem?_eq_getElem hq, hvalue]
  have ha := (Ancestor.direct f.control_edge).lower f.nested (by dsimp [row]; omega : q ≤ f.row)
  rcases ha.strip hparent with he | he
  · omega
  · exact Nat.le_of_lt (he.lt f.leftward)

theorem last_upper (f : CopyFrame) {p : Nat} (hp : p ∈ f.last) : p < f.stem.length := by
  obtain ⟨q, hq, hvalue⟩ := List.getElem_of_mem hp
  exact f.leftward q f.stem.length p (by rw [parent_last, List.getElem?_eq_getElem hq, hvalue])

def completed (f : CopyFrame) := f.out ++ [f.last.map f.move]

theorem completed_map_edge (f : CopyFrame) {q p i : Nat}
    (hp : parent (f.stem ++ [f.last]) q i = some p) :
    Ancestor f.completed q (f.move p) (f.move i) := by
  have hi := parent_column_lt hp
  simp only [List.length_append, List.length_singleton] at hi
  by_cases hold : i < f.stem.length
  · rw [parent_append_left hold] at hp
    exact (f.lift_edge hp).to_prefix_extension ⟨[f.last.map f.move], rfl⟩
  · have he : i = f.stem.length := by omega
    subst i
    rw [f.move_high (Nat.le_of_lt f.root_lt), ← f.out_length]
    apply Ancestor.direct
    rw [parent_last] at hp
    rw [completed, parent_last, List.getElem?_map]
    simp only [hp, Option.map_some]

theorem completed_leftward (f : CopyFrame) : Leftward f.completed := by
  intro q i p hp
  have hi := parent_column_lt hp
  change i < (f.out ++ [f.last.map f.move]).length at hi
  simp only [List.length_append, List.length_singleton] at hi
  by_cases hold : i < f.out.length
  · rw [completed, parent_append_left hold] at hp
    exact f.out_leftward q i p hp
  · have he : i = f.out.length := by omega
    subst i
    rw [completed, parent_last, List.getElem?_map] at hp
    cases hq : f.last[q]? with
    | none => simp [hq] at hp
    | some a =>
        have hmap : f.move a = p := by simpa [hq] using hp
        have ha := f.last_upper (List.mem_of_getElem? hq)
        rw [← hmap, f.out_length]
        dsimp [move, shift]
        split <;> omega

theorem completed_nested (f : CopyFrame) : Nested f.completed := by
  intro q i p hp
  have hi := parent_column_lt hp
  change i < (f.out ++ [f.last.map f.move]).length at hi
  simp only [List.length_append, List.length_singleton] at hi
  by_cases hold : i < f.out.length
  · rw [completed, parent_append_left hold] at hp
    exact (f.out_nested q i p hp).to_prefix_extension ⟨[f.last.map f.move], rfl⟩
  · have he : i = f.out.length := by omega
    subst i
    rw [completed, parent_last, List.getElem?_map] at hp
    cases hq : f.last[q + 1]? with
    | none => simp [hq] at hp
    | some a =>
        have hmap : f.move a = p := by simpa [hq] using hp
        have hsource : parent (f.stem ++ [f.last]) (q + 1) f.stem.length = some a := by
          rw [parent_last]; exact hq
        have ha := (f.nested q f.stem.length a hsource).map_edges (fun _ _ he => f.completed_map_edge he)
        rwa [hmap, f.move_high (Nat.le_of_lt f.root_lt), ← f.out_length] at ha

/-- A complete copied block with a translated live control column appended.
It can be used again as the source frame for the next root event. -/
def next (f : CopyFrame) : CopyFrame where
  stem := f.out
  last := f.last.map f.move
  root := f.stem.length
  control := by simp only [List.getLast?_map, f.control, Option.map_some, f.move_root]
  root_lt := by
    rw [f.out_length]
    have hw : 0 < f.width := by have := f.root_lt; dsimp [width]; omega
    omega
  leftward := f.completed_leftward
  nested := f.completed_nested

theorem next_width (f : CopyFrame) : f.next.width = f.width := by
  simp only [next, width, out_length]
  omega

theorem next_row (f : CopyFrame) : f.next.row = f.row := by simp [next, row]

theorem last_move_translate (f : CopyFrame) :
    f.last.map f.move = f.last.map (fun p => p + f.width) :=
  map_shift_of_lower (fun _ hp => f.last_lower hp)

/-- Any valid positive frame supplies the finite template invariants required
by the two-level forest runner. -/
def toSproutState (f : CopyFrame) : SproutState where
  front := f.stem.take f.root
  block := f.stem.drop f.root
  template := f.last
  block_nonempty := by
    intro he
    have hlen := congrArg List.length he
    simp only [List.length_drop, List.length_nil] at hlen
    have := f.root_lt
    omega
  control := by rw [List.length_take_of_le (Nat.le_of_lt f.root_lt)]; exact f.control
  lower p hp := by rw [List.length_take_of_le (Nat.le_of_lt f.root_lt)]; exact f.last_lower hp
  upper p hp := by
    rw [List.length_take_of_le (Nat.le_of_lt f.root_lt), List.length_drop]
    have := f.last_upper hp
    have := f.root_lt
    omega

theorem toSproutState_base (f : CopyFrame) : f.toSproutState.base = f.stem := by
  exact List.take_append_drop f.root f.stem

#print axioms next
#print axioms toSproutState

end CopyFrame
end LaverLowerBounds.ParentBMS
