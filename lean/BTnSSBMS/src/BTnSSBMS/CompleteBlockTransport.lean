import BTnSSBMS.RebaseMatrixTransport
import BTnSSBMS.RebaseBlockBoundary
import BTnSSBMS.EntryBlockClosure

/-!
The intermediate-row transport now identifies complete actual BMS blocks,
not entire lexical suffixes. Their boundaries are proved separately from
the columnwise copy equations. Source block inequalities and the highest
two target-row classes are still separate obligations.
-/
namespace BTnSSBMS.BMS

theorem block_eq_take (m : Matrix) (root : Nat) :
    block m root = (m.drop root).take (block m root).length := by
  obtain ⟨rest, shape⟩ := block_prefix m root
  rw [← shape, List.take_append_length]

private theorem copy_take (m : Matrix) (active delta : List Nat) (root endIndex phase count : Nat)
    (inside : count ≤ endIndex - root) :
    (copy m active delta root endIndex phase).take count =
      copy m active delta root (root + count) phase := by
  apply List.ext_getElem
  · simp only [List.length_take, copy_length, Nat.add_sub_cancel_left, Nat.min_eq_left inside]
  · intro k left right
    have short : k < count := by simpa only [copy_length, Nat.add_sub_cancel_left] using right
    have long : k < endIndex - root := by omega
    have same : ((copy m active delta root endIndex phase).take count)[k]? =
        (copy m active delta root (root + count) phase)[k]? := by
      rw [List.getElem?_take_of_lt short, copy_column m active delta root endIndex phase k long,
        copy_column m active delta root (root + count) phase k (by omega)]
    simpa only [List.getElem?_eq_getElem left, List.getElem?_eq_getElem right, Option.some.injEq] using same

theorem rebase_eq_take_copy (d : Nat) (m : Matrix) (cut root destination endIndex : Nat)
    (width : ∀ col ∈ m, col.length = d)
    (rootBound : root < m.length) (destinationBound : destination < m.length)
    (contained : root + (block m root).length ≤ endIndex) :
    rebase d m cut root destination =
      (copy m (thresholds (parentTable d m) root cut)
        ((m[destination]?.getD []).zipWith (· - ·) (m[root]?.getD [])) root endIndex 1).take
        (block m root).length := by
  rw [copy_take m _ _ root endIndex 1 _ (by omega)]
  have same := first_copy_eq_rebase_take d m cut root destination (root + (block m root).length)
    width rootBound destinationBound (by omega)
  simp only [List.getElem?_eq_getElem rootBound, List.getElem?_eq_getElem destinationBound, Option.getD_some]
  rw [same]
  simp only [Nat.add_sub_cancel_left, ← rebase_length d m cut root destination, List.take_length]

end BTnSSBMS.BMS

namespace BTnSSBMS.Encoder

theorem full_block_eq_rebase {state next result newResult global : State d} {cut destination : Nat}
    (positive : 0 < d) (initial : result <+: global) (destinationBound : destination < global.length)
    (cutBound : cut ≤ d)
    (control : SharedTrace state next result newResult)
    (numerical : ∀ j, j < d →
      RowRebaseTrace j state.length
        (if j < cut then Parents.reading (BMS.parentTable (d + 2) (matrix global)) j destination -
          Parents.reading (BMS.parentTable (d + 2) (matrix global)) j state.length else 0)
        state next result newResult) (nonempty : state.length < result.length)
    (closed : BMS.block (matrix global) state.length = BMS.block (matrix result) state.length) :
    BMS.block (matrix newResult) next.length = BMS.rebase (d + 2) (matrix global) cut state.length destination := by
  have zero := numerical 0 positive
  have sameLength := zero.block_length
  rw [← closed] at sameLength
  have globalLength := initial.length_le
  have rootBound : state.length < global.length := by omega
  have blockBound := (BMS.block_prefix (matrix result) state.length).length_le
  have matrixLength : (matrix result).length = result.length := by simp only [matrix, List.length_map]
  simp only [List.length_drop, matrixLength] at blockBound
  rw [← closed] at blockBound
  have copySame := full_rows_eq_copy initial destinationBound cutBound control numerical nonempty
  rw [BMS.block_eq_take (matrix newResult) next.length, sameLength, copySame]
  exact (BMS.rebase_eq_take_copy (d + 2) (matrix global) cut state.length destination result.length
    (matrix_width global) (by simpa only [matrix, List.length_map] using rootBound)
    (by simpa only [matrix, List.length_map] using destinationBound) (by omega)).symm

/-- Every actual intermediate target pair has exact complete-block
transport for the frozen source copy. No caller-supplied lexical cutoff,
source root, or block-transport hypothesis is used. -/
theorem standard_intermediate_pair_block {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {a b cut : Nat}
    (rowPositive : 0 < cut) (room : cut < d) (before : a < b) (inside : b < (fromSource d e).length)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e)) (cut - 1) a b)
    (same : Parents.parent (BMS.parentTable (d + 2) (fromSource d e)) cut a =
      Parents.parent (BMS.parentTable (d + 2) (fromSource d e)) cut b) :
    ∃ earlier later root, earlier ∈ entries d e [] [] [] [] [] ∧
      later ∈ entries d e [] [] [] [] [] ∧ root < later.source.length ∧
      earlier.OriginAt later.source later.visible later.owners later.materials later.state root ∧
      earlier.state.length = a ∧ later.state.length = b ∧
      (let delta := (List.range cut).map
        (fun k => later.coordinates[k]?.getD 0 - earlier.coordinates[k]?.getD 0)
      let shifted := encode d (Parents.annotate d later.source
        (Source.copied d root cut delta 1 earlier.source (List.replicate root 0) earlier.remaining))
        later.visible later.state
      BMS.block (matrix shifted) b = BMS.rebase (d + 2) (fromSource d e) cut a b) := by
  obtain ⟨earlier, later, root, oldMember, newMember, bound, origin, oldPosition, newPosition, rows⟩ :=
    standard_intermediate_pair_rows positive standard rowPositive room before inside path same
  refine ⟨earlier, later, root, oldMember, newMember, bound, origin, oldPosition, newPosition, ?_⟩
  have sourcePath := standard_entry_ancestor_reflect positive standard oldMember newMember origin bound
    (by omega : cut - 1 < d) (by simpa only [oldPosition, newPosition] using path)
  have shared := standard_entry_shared_parent_reflect positive standard oldMember newMember origin bound room
    (by simpa only [oldPosition, newPosition] using same)
  have control := origin.partial_rebase_control (standard_entries_sound positive standard earlier oldMember)
    (standard_entries_sound positive standard later newMember) rowPositive room bound sourcePath shared.symm
  have result := full_block_eq_rebase positive
    (entries_execution d e [] [] [] [] [] earlier oldMember).resultPrefix
    (destination := b) (cut := cut) (by simpa only [fromSource, matrix, List.length_map] using inside)
    (by omega) control (by simpa only [oldPosition, fromSource] using rows)
    earlier.first_lt_result (standard_entry_block_closed positive standard oldMember)
  simpa only [fromSource, oldPosition, newPosition] using result

end BTnSSBMS.Encoder
