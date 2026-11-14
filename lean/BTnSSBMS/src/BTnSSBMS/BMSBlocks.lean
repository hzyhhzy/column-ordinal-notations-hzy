import BTnSSBMS.FirstDiagonal

/-!
Concrete row-zero blocks and ancestor-sensitive partial rebasing. Their
whole-word BN/SB inequalities imply the head conditions of FirstDiagonal.
No target standardness or well-foundedness is assumed here.
-/
namespace BTnSSBMS.BMS

def block (m : Matrix) (root : Nat) : Matrix :=
  match m[root]? with
  | none => []
  | some col => col :: (m.drop (root + 1)).takeWhile
      (fun next => decide (col[0]?.getD 0 < next[0]?.getD 0))

def rebase (d : Nat) (m : Matrix) (cut root destination : Nat) : Matrix :=
  (block m root).mapIdx fun offset col => col.mapIdx fun j v =>
    if j < (thresholds (parentTable d m) root cut)[root + offset]?.getD 0 then
      v + ((m[destination]?.getD [])[j]?.getD 0 - (m[root]?.getD [])[j]?.getD 0)
    else v

/-- Non-increasing complete blocks of row-zero siblings. -/
def BN (d : Nat) (m : Matrix) : Prop :=
  ∀ a b, a < b → b < m.length →
    Parents.parent (parentTable d m) 0 a = Parents.parent (parentTable d m) 0 b →
    matrixCompare (block m a) (block m b) ≠ .lt

/-- Complete-block partial-rebase condition at row `cut`. -/
def SB (d : Nat) (m : Matrix) (cut : Nat) : Prop :=
  ∀ a b, a < b → b < m.length →
    Parents.Ancestor (parentTable d m) (cut - 1) a b →
    Parents.parent (parentTable d m) cut a = Parents.parent (parentTable d m) cut b →
    matrixCompare (rebase d m cut a b) (block m b) ≠ .lt

theorem block_head (m : Matrix) (root : Nat) (inside : root < m.length) :
    ∃ tail, block m root = m[root] :: tail := by
  simp only [block, List.getElem?_eq_getElem inside]
  exact ⟨_, rfl⟩

theorem block_prefix (m : Matrix) (root : Nat) : block m root <+: m.drop root := by
  cases lookup : m[root]? with
  | none => simp only [block, lookup]; exact List.nil_prefix
  | some col =>
    have inside := (List.getElem?_eq_some_iff.mp lookup).choose
    have drop : m.drop root = col :: m.drop (root + 1) := by
      have same : m[root] = col := by simpa only [List.getElem?_eq_getElem inside, Option.some.injEq] using lookup
      rw [List.drop_eq_getElem_cons inside, same]
    rw [drop, block, lookup]
    exact List.cons_prefix_cons.mpr ⟨rfl, List.takeWhile_prefix _⟩

/-- The concrete consecutive block is exactly the row-zero ancestor cone,
not merely a convenient list with the right head. -/
theorem block_length_iff_ancestor (d : Nat) (m : Matrix) (positive : 0 < d)
    (root offset : Nat) (inside : root + offset < m.length) :
    offset < (block m root).length ↔
      Parents.Ancestor (parentTable d m) 0 root (root + offset) := by
  have rootBound : root < m.length := by omega
  have tableBound : root + offset < (parentTable d m).length := by
    simpa only [parentTable_length] using inside
  cases offset with
  | zero =>
    obtain ⟨tail, shape⟩ := block_head m root rootBound
    simp only [shape, List.length_cons, Nat.zero_lt_succ, Nat.add_zero, true_iff]
    exact .refl _
  | succ offset =>
    simp only [block, List.getElem?_eq_getElem rootBound, List.length_cons, Nat.succ_lt_succ_iff]
    rw [takeWhile_long]
    constructor
    · intro all
      apply Parents.ancestor_zero_of_interval (parentTable_coherent d m) (parentTable_valid d m)
        positive tableBound (by omega)
      intro position after before
      have kBound : position - (root + 1) ≤ offset := by omega
      obtain ⟨col, lookup, taller⟩ := all (position - (root + 1)) kBound
      have positionEq : root + 1 + (position - (root + 1)) = position := by omega
      rw [List.getElem?_drop, positionEq] at lookup
      simpa only [parentTable_reading, List.getElem?_eq_getElem rootBound, lookup,
        Option.getD_some, decide_eq_true_eq] using taller
    · intro path k before
      have bound : root + 1 + k < m.length := by omega
      refine ⟨m[root + 1 + k], ?_, ?_⟩
      · rw [List.getElem?_drop, List.getElem?_eq_getElem bound]
      · have taller := (path.zero_interval (parentTable_coherent d m) (parentTable_valid d m)
          positive).2 (root + 1 + k) (by omega) (by omega)
        simpa only [parentTable_reading, List.getElem?_eq_getElem rootBound,
          List.getElem?_eq_getElem bound, Option.getD_some, decide_eq_true_eq] using taller

theorem block_column (m : Matrix) (root offset : Nat) (inside : offset < (block m root).length) :
    (block m root)[offset]? = m[root + offset]? := by
  obtain ⟨tail, shape⟩ := block_prefix m root
  rw [← List.getElem?_drop, ← shape, List.getElem?_append_left inside]

/-- Any strict descendant guarantees a second column in the complete
block, independently of numerical legality or block inequalities. -/
theorem block_nontrivial_of_descendant {d : Nat} {m : Matrix}
    {top g endpoint : Nat} (room : top < d)
    (path : Parents.Ancestor (parentTable d m) top g endpoint) (strict : g ≠ endpoint) :
    1 < (block m g).length := by
  obtain ⟨child, edge, _⟩ :=
    (path.lower_row (parentTable_coherent d m) room (Nat.zero_le _)).first_child strict
  obtain ⟨bound, first⟩ := Parents.immediate_zero_child (parentTable_coherent d m)
    (parentTable_valid d m) (by omega) edge
  have childBound : child < m.length := by
    obtain ⟨a, lookup, _⟩ := Option.bind_eq_some_iff.mp edge
    have inside := (List.getElem?_eq_some_iff.mp lookup).choose
    simpa only [parentTable_length] using inside
  exact (block_length_iff_ancestor d m (by omega) g 1 (by omega)).mpr (.up first (.refl _))

theorem rebase_head (d : Nat) (m : Matrix) (cut root destination : Nat)
    (inside : root < m.length) (room : cut ≤ d) :
    ∃ tail, rebase d m cut root destination =
      (m[root].mapIdx fun j v => if j < cut then
        v + ((m[destination]?.getD [])[j]?.getD 0 - (m[root]?.getD [])[j]?.getD 0)
        else v) :: tail := by
  obtain ⟨tail, shape⟩ := block_head m root inside
  have atRoot := thresholds_at_root d m root cut inside room
  simp only [rebase, shape, List.mapIdx_cons, Nat.add_zero, atRoot]
  exact ⟨_, rfl⟩

theorem BN.heads {d : Nat} {m : Matrix} (legal : NumericallyLegal d m) (sorted : BN d m) :
    Parents.HeadBN d (parentTable d m) := by
  intro a b before inside shared row _ room common
  have bBound : b < m.length := by simpa only [parentTable_length] using inside
  have aBound : a < m.length := by omega
  have aWidth := legal.1 m[a] (List.getElem_mem aBound)
  have bWidth := legal.1 m[b] (List.getElem_mem bBound)
  apply Nat.le_of_not_gt
  intro fail
  have smaller : (m[a])[row]?.getD 0 < (m[b])[row]?.getD 0 := by
    have strict : Parents.reading (parentTable d m) row a < Parents.reading (parentTable d m) row b := by omega
    simpa only [parentTable_reading, List.getElem?_eq_getElem aBound,
      List.getElem?_eq_getElem bBound, Option.getD_some] using strict
  have first : listCompare compare m[a] m[b] = .lt := by
    apply columnCompare_lt_at _ _ row (by omega) (by omega) ?_ smaller
    intro j hj
    simpa only [parentTable_reading, List.getElem?_eq_getElem aBound,
      List.getElem?_eq_getElem bBound, Option.getD_some] using common j (Nat.zero_le _) hj
  obtain ⟨aTail, aShape⟩ := block_head m a aBound
  obtain ⟨bTail, bShape⟩ := block_head m b bBound
  apply sorted a b before bBound shared
  simp only [aShape, bShape, matrixCompare, listCompare, first]

private theorem rebase_head_reading {d : Nat} {m : Matrix}
    (legal : NumericallyLegal d m) {cut a b row : Nat} (positive : 0 < cut)
    (room : cut < d) (aBound : a < m.length) (bBound : b < m.length)
    (ancestry : Parents.Ancestor (parentTable d m) (cut - 1) a b) (rowBound : row < d) :
    ((m[a]).mapIdx fun j v => if j < cut then
      v + ((m[b]?.getD [])[j]?.getD 0 - (m[a]?.getD [])[j]?.getD 0)
      else v)[row]?.getD 0 =
      if row < cut then Parents.reading (parentTable d m) row b
      else Parents.reading (parentTable d m) row a := by
  have width := legal.1 m[a] (List.getElem_mem aBound)
  have atRow : row < (m[a]).length := by omega
  rw [List.getElem?_mapIdx, List.getElem?_eq_getElem atRow]
  simp only [Option.map_some, Option.getD_some, parentTable_reading,
    List.getElem?_eq_getElem aBound, List.getElem?_eq_getElem bBound]
  by_cases lower : row < cut
  · simp only [lower, if_true, List.getElem?_eq_getElem atRow, Option.getD_some]
    have path : Parents.Ancestor (parentTable d m) row a b :=
      ancestry.lower_row (parentTable_coherent d m) (by omega : cut - 1 < d) (by omega)
    have ordered := path.reading_le (parentTable_coherent d m)
    simp only [parentTable_reading, List.getElem?_eq_getElem aBound,
      List.getElem?_eq_getElem bBound, Option.getD_some, List.getElem?_eq_getElem atRow] at ordered
    omega
  · simp only [lower, if_false, List.getElem?_eq_getElem atRow, Option.getD_some]

theorem SB.heads {d : Nat} {m : Matrix} (legal : NumericallyLegal d m)
    {cut : Nat} (positive : 0 < cut) (room : cut < d) (sorted : SB d m cut) :
    Parents.HeadSB d (parentTable d m) cut := by
  intro a b before inside ancestry shared row rowLower rowBound common
  have bBound : b < m.length := by simpa only [parentTable_length] using inside
  have aBound : a < m.length := by omega
  have aWidth := legal.1 m[a] (List.getElem_mem aBound)
  have bWidth := legal.1 m[b] (List.getElem_mem bBound)
  apply Nat.le_of_not_gt
  intro fail
  have strict : Parents.reading (parentTable d m) row a < Parents.reading (parentTable d m) row b := by omega
  obtain ⟨tail, shape⟩ := rebase_head d m cut a b aBound (by omega)
  let head := (m[a]).mapIdx fun j v => if j < cut then
      v + ((m[b]?.getD [])[j]?.getD 0 - (m[a]?.getD [])[j]?.getD 0) else v
  have first : listCompare compare head m[b] = .lt := by
    apply columnCompare_lt_at _ _ row (by simpa [head, List.length_mapIdx, aWidth] using rowBound) (by omega)
    · intro j hj
      have reading := rebase_head_reading legal positive room aBound bBound ancestry (by omega : j < d)
      change head[j]?.getD 0 = _ at reading
      rw [reading]
      by_cases low : j < cut
      · simp only [low, if_true, parentTable_reading, List.getElem?_eq_getElem bBound, Option.getD_some]
      · simp only [low, if_false]
        rw [common j (by omega) hj, parentTable_reading,
          List.getElem?_eq_getElem bBound, Option.getD_some]
    · have reading := rebase_head_reading legal positive room aBound bBound ancestry rowBound
      change head[row]?.getD 0 = _ at reading
      rw [reading, if_neg (by omega)]
      simpa only [parentTable_reading, List.getElem?_eq_getElem bBound, Option.getD_some] using strict
  obtain ⟨bTail, bShape⟩ := block_head m b bBound
  apply sorted a b before bBound ancestry shared
  simp only [shape, bShape, matrixCompare, listCompare, head, first]

/-- The paper's first-diagonal lemma for the actual computed BMS parents
and concrete whole-block inequalities. There is no SB_top premise. -/
theorem first_diagonal {d : Nat} {m : Matrix} (legal : NumericallyLegal d m)
    {top g endpoint : Nat} (positive : 0 < top) (room : top < d)
    (siblings : BN d m) (side : ∀ j, 0 < j → j < top → SB d m j)
    (path : Parents.Ancestor (parentTable d m) top g endpoint) (strict : g ≠ endpoint) :
    g + 1 < m.length ∧ Parents.parent (parentTable d m) 0 (g + 1) = some g ∧
      ∀ j, j ≤ top → (m[g + 1]?.getD [])[j]?.getD 0 = (m[g]?.getD [])[j]?.getD 0 + 1 := by
  have result := Parents.first_diagonal (parentTable_coherent d m) (parentTable_valid d m)
    legal.2 positive room (siblings.heads legal)
    (fun j pos small => (side j pos small).heads legal pos (by omega)) path strict
  simpa only [parentTable_length, parentTable_reading] using result

end BTnSSBMS.BMS
