import BTnSSBMS.SBCrossPhase

/-!
The numerical exclusion used when the copy class equals the tested SB
row. The literal next-phase root is used. For an earlier ordinary entry
on the source root-to-terminal path, the strict coordinate barrier is
derived from the selected parent and actual activation history.
Locating every possible cross-copy pair on that path is still required
by the full SB closure proof.
-/
namespace BTnSSBMS.Source

theorem shift_unshifted_row (a delta : List Nat) (cap phase row : Nat)
    (above : cap ≤ row) (inside : row < a.length) :
    (shift a cap delta phase)[row]?.getD 0 = a[row]?.getD 0 := by
  rw [shift_value a delta cap phase row inside, if_neg (by omega), Nat.add_zero]

theorem ShiftView.unshifted_row {d root cap phase : Nat}
    {source target : ParentContext} {visible history delta : List Nat}
    (scope : ShiftView d source target visible history root cap delta phase)
    {position row : Nat} (inside : position < source.length) (room : row < d)
    (above : cap ≤ row) :
    Parents.reading target row (Parents.point visible position) = Parents.reading source row position := by
  have inactive : ¬ row < history[position]?.getD 0 := by
    intro active
    have below := ((scope.historyCorrect position (by rw [scope.historyLength]; exact inside) row).mp active).1
    omega
  rw [scope.values position inside row room, if_neg inactive, Nat.add_zero]

/-- An earlier ordinary path entry and an endpoint below the next
copy root cannot share the tested-row parent. The earlier entry's
strictly higher coordinate is proved, not an extra premise. -/
theorem ShiftView.next_root_shared_parent_excluded {d root cap phase : Nat}
    {source target later : ParentContext} {visible history delta : List Nat}
    (scope : ShiftView d source target visible history root cap delta phase)
    (terminal : List Nat) (positive : 0 < cap) (room : cap < d)
    (rootWidth : (source[root]?.getD default).coordinates.length = d)
    (selected : (Parents.label d source terminal).parents[cap]?.join = some root)
    {position : Nat} (after : root < position) (inside : position < source.length)
    (sourcePath : Parents.Ancestor (source ++ [Parents.label d source terminal])
      (cap - 1) position source.length)
    (initial : target ++ [Parents.label d target
      (shift (source[root]?.getD default).coordinates cap delta (phase + 1))] <+: later)
    (laterCoherent : Parents.Coherent d later) (laterValid : Parents.ContextValid later)
    (a : List Nat) (laterUnit : Parents.UnitSteps d (later ++ [Parents.label d later a]))
    (targetPath : Parents.Ancestor (later ++ [Parents.label d later a])
      (cap - 1) target.length later.length) :
    (Parents.label d later a).parents[cap]?.join ≠
      Parents.parent later cap (Parents.point visible position) := by
  intro shared
  have rowEq : cap - 1 + 1 = cap := by omega
  have sourceCoherent := Parents.coherent_append_label scope.sourceCoherent terminal
  have sourceValid := Parents.context_valid_append_label d source scope.sourceValid terminal
  have sourceEdge : Parents.parent (source ++ [Parents.label d source terminal]) cap source.length = some root := by
    rw [Parents.append_label_parent]
    exact selected
  have terminalHigher := Parents.parent_reading_lt sourceCoherent sourceEdge
  have pathFloor := Parents.parent_chain_barrier sourceCoherent sourceValid
    (row := cap - 1) (by omega) (by simpa only [rowEq] using sourceEdge) sourcePath after
  rw [rowEq] at pathFloor
  have rootInside := scope.afterRoot
  have sourceHigher : Parents.reading source cap root < Parents.reading source cap position := by
    rw [← Parents.reading_prefix (List.prefix_append source [Parents.label d source terminal]) cap root rootInside] at terminalHigher
    rw [← Parents.reading_prefix (List.prefix_append source [Parents.label d source terminal]) cap position inside] at pathFloor
    omega
  have oldInside := scope.view.bounded position inside
  have barrierInside : target.length < later.length := by
    have sizes := initial.length_le
    simp only [List.length_append, List.length_cons, List.length_nil] at sizes
    omega
  have targetInitial : target <+: later := (List.prefix_append _ _).trans initial
  have oldValue : Parents.reading later cap (Parents.point visible position) =
      Parents.reading source cap position := by
    rw [← Parents.reading_prefix targetInitial cap (Parents.point visible position) oldInside]
    exact scope.unshifted_row inside room (Nat.le_refl cap)
  have barrierValue : Parents.reading later cap target.length = Parents.reading source cap root := by
    rw [← Parents.reading_prefix initial cap target.length (by simp), Parents.reading_append_label,
      shift_unshifted_row _ _ cap (phase + 1) cap (Nat.le_refl cap) (by rw [rootWidth]; exact room)]
    rfl
  have impossible := sb_shared_parent_barrier_floor laterCoherent laterValid a laterUnit
    positive room oldInside barrierInside targetPath shared
  rw [oldValue, barrierValue] at impossible
  omega

end BTnSSBMS.Source
