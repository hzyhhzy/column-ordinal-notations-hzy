import BTnSSBMS.BMSBlocks
import BTnSSBMS.EncoderOrderScope

/-!
A genuine row-zero block cannot cross an exit whose first column is no
higher than its root. This only identifies block boundaries; it asserts
no block inequality and no target standardness.
-/
namespace BTnSSBMS.BMS

theorem block_append_of_exit (m exit : Matrix) (root : Nat)
    (inside : root < m.length)
    (low : ∀ col tail, exit = col :: tail →
      col[0]?.getD 0 ≤ (m[root]?.getD [])[0]?.getD 0) :
    block (m ++ exit) root = block m root := by
  have stop : exit.takeWhile (fun col =>
      decide ((m[root]?.getD [])[0]?.getD 0 < col[0]?.getD 0)) = [] := by
    cases exit with
    | nil => rfl
    | cons col tail =>
      have value := low col tail rfl
      simp only [List.takeWhile_cons, decide_eq_true_eq, Nat.not_lt_of_ge value, ↓reduceIte]
  simp only [block, List.getElem?_append_left inside, List.getElem?_eq_getElem inside]
  rw [List.drop_append_of_le_length (by omega : root + 1 ≤ m.length), List.takeWhile_append]
  simp only [List.getElem?_eq_getElem inside, Option.getD_some] at stop
  rw [stop]
  split
  next same =>
    rw [(List.takeWhile_prefix _).eq_of_length same, List.append_nil]
  next => rfl

end BTnSSBMS.BMS

namespace BTnSSBMS.Encoder

theorem block_append_of_low_exit (state : State d) (root bound : Nat)
    (inside : root < state.length) (exit : Matrix)
    (low : ExitBelow (some bound) exit)
    (height : bound ≤ Parents.reading (BMS.parentTable (d + 2) (matrix state)) 0 root) :
    BMS.block (matrix state ++ exit) root = BMS.block (matrix state) root := by
  apply BMS.block_append_of_exit (matrix state) exit root
    (by simpa only [matrix, List.length_map] using inside)
  intro col tail shape
  subst exit
  obtain ⟨t, equal, _, value⟩ := low
  have same : bound = t := Option.some.inj equal
  simp only [BMS.parentTable_reading] at height
  omega

theorem head_block_closed (d : Nat) (source : ParentContext) (visible : List Nat)
    (state : State d) (positive : 0 < d)
    (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (a : List Nat) (hs : Forests (List Nat)) (tail : NumericalExpr)
    (floor : Option (Nat × Nat)) (fence : OrderFence source visible state floor)
    (above : ∀ s t, floor = some (s, t) → s < a[0]?.getD 0)
    (exit : Matrix) (low : ExitBelow (floor.map Prod.snd) exit) :
    let result := encode d (Parents.annotate d source (.cons a hs tail)) visible state
    BMS.block (matrix result ++ exit) state.length = BMS.block (matrix result) state.length := by
  dsimp only
  cases exit with
  | nil => simp only [List.append_nil]
  | cons col rest =>
    obtain ⟨bound, selected, _, value⟩ := low
    cases floor with
    | none => simp at selected
    | some pair =>
      obtain ⟨s, t⟩ := pair
      have equal : t = bound := by simpa using selected
      obtain ⟨root, inside, sourceValue, path, rootValue⟩ := fence
      obtain ⟨head, extra, shape, high⟩ := encode_cons_above_fence state positive coherent valid view
        inside path a hs tail (by rw [sourceValue]; exact above s t rfl)
      rw [rootValue] at high
      apply BMS.block_append_of_exit
      · rw [shape, List.length_append, matrix, List.length_map, List.length_cons]
        omega
      · intro first remaining same
        cases same
        have length : (matrix state).length = state.length := by simp only [matrix, List.length_map]
        have lookup : (matrix (encode d (Parents.annotate d source (.cons a hs tail)) visible state))[state.length]? =
            some head := by
          rw [shape, ← length, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
          rfl
        rw [lookup]
        simp only [Option.getD_some]
        omega

end BTnSSBMS.Encoder
