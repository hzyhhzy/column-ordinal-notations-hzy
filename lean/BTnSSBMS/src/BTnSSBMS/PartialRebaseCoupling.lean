import BTnSSBMS.FixedPrefixCoupling

/-!
Discharge root entry coupling for an actual intermediate-row partial
rebase. Only numerical geometry and historical prefix snapshots are
inputs. Root query equality, full key equality, branch agreement, and
the resulting saved-frame correspondence are proved, not assumed.
-/
namespace BTnSSBMS.Encoder

theorem partial_rebase_head_coupled {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (unit : Parents.UnitSteps d context) (position : List Nat)
    (positionUnit : Parents.UnitSteps d (context ++ [Parents.label d context position]))
    {cut root : Nat} (positive : 0 < cut) (room : cut < d) (insideRoot : root < context.length)
    (path : Parents.Ancestor (context ++ [Parents.label d context position]) (cut - 1) root context.length)
    (same : (Parents.label d context position).parents[cut]?.join = Parents.parent context cut root)
    (hs : Forests (List Nat)) (width : (context[root]?.getD default).coordinates.length = d)
    (legal : Source.FiniteLegalForests d (context.take (root + 1))
      ((context[root]?.getD default).coordinates[0]?.getD 0) hs)
    {visible nextVisible owners : List Nat} {materials : List (Forests (List Nat))}
    {state next : State d}
    (known : VisibleMaterials d (context.take root) visible owners materials state)
    (oldView : Parents.NumericalView d (context.take root) (BMS.parentTable (d + 2) (matrix state)) visible)
    (visiblePrefix : visible <+: nextVisible) (newLength : nextVisible.length = context.length)
    (statePrefix : state <+: next) :
    let coordinates := (context[root]?.getD default).coordinates
    let delta := (List.range cut).map (fun j => position[j]?.getD 0 - coordinates[j]?.getD 0)
    let head := Source.shift coordinates cut delta 1
    let newA := Parents.label d context head
    let newHs := Source.relocateForests d (context.take (root + 1)) (context ++ [newA])
      (List.range root ++ [context.length]) hs
    let headed := headState d (Parents.label d (context.take root) coordinates)
      (Parents.annotateForests d (context.take (root + 1)) hs) visible state
    let newHeaded := headState d newA (Parents.annotateForests d (context ++ [newA]) newHs) nextVisible next
    CoupledFrames d (context.take (root + 1)) (context ++ [newA]) (List.range root ++ [context.length])
      (visible ++ [headed.length - 1]) (nextVisible ++ [newHeaded.length - 1]) (materials ++ [hs]) headed newHeaded := by
  let coordinates := (context[root]?.getD default).coordinates
  let delta := (List.range cut).map (fun j => position[j]?.getD 0 - coordinates[j]?.getD 0)
  let head := Source.shift coordinates cut delta 1
  have length : (context.take root).length = root := by simp only [List.length_take]; omega
  have divided := coherent.take_succ_label insideRoot
  have frameSame := partial_rebase_queried_frame coherent valid unit position positionUnit
    positive room insideRoot path same width oldView visiblePrefix statePrefix
  have keySame := partial_rebase_queryKey coherent valid unit position positionUnit
    positive room insideRoot path same hs width legal
  have result := prefix_rebase_head_coupled
    (coherent.restrict (List.take_prefix root context)) (valid.restrict (List.take_prefix root context))
    (unit.restrict valid (List.take_prefix root context)) (List.take_prefix root context)
    known oldView visiblePrefix newLength statePrefix coordinates head hs frameSame
    (by simpa only [coordinates, head, delta, length, ← divided] using keySame)
  simpa only [coordinates, head, delta, length, ← divided] using result

end BTnSSBMS.Encoder
