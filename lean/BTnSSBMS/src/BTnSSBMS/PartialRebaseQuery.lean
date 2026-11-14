import BTnSSBMS.FixedPrefixMaterials

/-!
The old rebase root is queried in its original short context, while the
new root is queried after an intervening corridor. At an intermediate
row the highest numerical parent stays fixed, so the two real queries
read the same saved frame. The full root key is also unchanged.
-/
namespace BTnSSBMS.Parents

theorem Coherent.label_at {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) {i : Nat} (inside : i < context.length) :
    label d (context.take i) (context[i]?.getD default).coordinates = context[i]?.getD default := by
  rw [List.getElem?_eq_getElem inside, Option.getD_some]
  have parents := coherent i context[i] (List.getElem?_eq_getElem inside)
  cases value : context[i] with
  | mk coordinates stored =>
    simp only [value, label] at parents ⊢
    rw [parents]

end BTnSSBMS.Parents

namespace BTnSSBMS.Encoder

theorem queried_frame_shared_prefix {d : Nat} {source : ParentContext}
    {visible nextVisible : List Nat} {state next : State d}
    (oldView : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (visiblePrefix : visible <+: nextVisible) (statePrefix : state <+: next)
    (coordinates : List Nat) (newA : ParentLabel)
    (same : newA.parents[d - 1]?.join = (Parents.label d source coordinates).parents[d - 1]?.join) :
    frameAt next (representative nextVisible newA (d - 1)) =
      frameAt state (representative visible (Parents.label d source coordinates) (d - 1)) := by
  obtain ⟨visibleExtra, rfl⟩ := visiblePrefix
  obtain ⟨stateExtra, rfl⟩ := statePrefix
  simp only [representative, same]
  cases parent : (Parents.label d source coordinates).parents[d - 1]?.join with
  | none => rfl
  | some p =>
    have inside := Parents.label_parent_bound d source coordinates (d - 1) p parent
    have visibleInside : p < visible.length := by rw [oldView.length]; exact inside
    have bounded : Parents.point visible p < state.length := by
      simpa only [BMS.parentTable_length, matrix, List.length_map] using oldView.bounded p inside
    have lookup : visible[p]? = some (Parents.point visible p) := by
      simp only [Parents.point, List.getElem?_eq_getElem visibleInside, Option.getD_some]
    simp only [Option.bind_some, List.getElem?_append_left visibleInside, lookup]
    simp only [frameAt, Option.bind_some, List.getElem?_append_left bounded]

theorem partial_rebase_queried_frame {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (unit : Parents.UnitSteps d context) (position : List Nat)
    (positionUnit : Parents.UnitSteps d (context ++ [Parents.label d context position]))
    {cut root : Nat} (positive : 0 < cut) (room : cut < d) (insideRoot : root < context.length)
    (path : Parents.Ancestor (context ++ [Parents.label d context position]) (cut - 1) root context.length)
    (same : (Parents.label d context position).parents[cut]?.join = Parents.parent context cut root)
    (width : (context[root]?.getD default).coordinates.length = d)
    {visible nextVisible : List Nat} {state next : State d}
    (oldView : Parents.NumericalView d (context.take root) (BMS.parentTable (d + 2) (matrix state)) visible)
    (visiblePrefix : visible <+: nextVisible) (statePrefix : state <+: next) :
    let coordinates := (context[root]?.getD default).coordinates
    let delta := (List.range cut).map (fun j => position[j]?.getD 0 - coordinates[j]?.getD 0)
    let head := Source.shift coordinates cut delta 1
    frameAt next (representative nextVisible (Parents.label d context head) (d - 1)) =
      frameAt state (representative visible (Parents.label d (context.take root) coordinates) (d - 1)) := by
  dsimp only
  have values := Source.partial_rebase_head_values coherent position positive room insideRoot path width
  have parents := Parents.partial_rebase_head_parents coherent valid unit position _ positionUnit
    room insideRoot same values.1 values.2 (d - 1) (by omega)
  apply queried_frame_shared_prefix oldView visiblePrefix statePrefix _ _
  rw [parents, if_neg (by omega), coherent.label_at insideRoot]
  simp only [Parents.parent, List.getElem?_eq_getElem insideRoot, Option.bind_some, Option.getD_some]

/-- Canonical relocation is the already frozen activation copy. The
key equality here is the real old/new query, not an extra assumption. -/
theorem partial_rebase_queryKey {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (unit : Parents.UnitSteps d context) (position : List Nat)
    (positionUnit : Parents.UnitSteps d (context ++ [Parents.label d context position]))
    {cut root : Nat} (positive : 0 < cut) (room : cut < d) (insideRoot : root < context.length)
    (path : Parents.Ancestor (context ++ [Parents.label d context position]) (cut - 1) root context.length)
    (same : (Parents.label d context position).parents[cut]?.join = Parents.parent context cut root)
    (hs : Forests (List Nat)) (width : (context[root]?.getD default).coordinates.length = d)
    (legal : Source.FiniteLegalForests d (context.take (root + 1))
      ((context[root]?.getD default).coordinates[0]?.getD 0) hs) :
    let coordinates := (context[root]?.getD default).coordinates
    let delta := (List.range cut).map (fun j => position[j]?.getD 0 - coordinates[j]?.getD 0)
    let head := Source.shift coordinates cut delta 1
    queryKey d context head
      (Source.relocateForests d (context.take (root + 1)) (context ++ [Parents.label d context head])
        (List.range root ++ [context.length]) hs) =
      queryKey d (context.take root) coordinates hs := by
  dsimp only
  have scope := Source.partial_rebase_shiftView coherent valid unit position positionUnit
    positive room insideRoot path same width
  rw [Source.relocateForests_eq_copied scope _ hs legal]
  have key := Source.partial_rebase_root_key coherent valid unit position positionUnit
    positive room insideRoot path same hs width legal
  have length : (context.take root).length = root := by simp only [List.length_take]; omega
  simp only [queryKey]
  rw [length, ← coherent.take_succ_label insideRoot, coherent.label_at insideRoot]
  exact key

end BTnSSBMS.Encoder
