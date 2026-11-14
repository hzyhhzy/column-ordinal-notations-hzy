import BTnSSBMS.SourceBNHigh
import BTnSSBMS.SourceBNZero

/-! Unconditional BN preservation for the frozen source expansion on
finite-legal BN inputs, and hence BN on its entire standard domain.
This is a source invariant, not target BMS standardness or coverage. -/
namespace BTnSSBMS.Source

theorem ordinary_expand_BN
    {d cap root rootDepth stopDepth index : Nat} {e stop : NumericalExpr}
    (positive : 0 < d) (legal : FiniteLegal d [] e) (ordered : BN d [] e)
    (first : stopDepth = (spine e).findIdx stopping)
    (stopSelected : (spine e)[stopDepth]? = some stop)
    {terminal : List Nat} {attached : Forests (List Nat)}
    (stopLast : last? stop = some (terminal, attached))
    {parentStop : ParentExpr} {parentTerminal : ParentLabel} {parentAttached : Forests ParentLabel}
    (parentSelected : (spine (parents d e))[stopDepth]? = some parentStop)
    (parentLast : last? parentStop = some (parentTerminal, parentAttached))
    (chosen : highestParent 0 parentTerminal.parents = some (cap, root))
    (location : locateRoot (spine e) root = some (rootDepth, index))
    {rootColumn : List Nat}
    (rootRead : ((((spine e).take (stopDepth + 1)).flatMap labels)[root]?) = some rootColumn)
    {rootPart tailPart : MarkedExpr}
    (partSelected : (spine (mark cap root [] (parents d e)))[rootDepth]? = some rootPart)
    (tailSelected : (spine (mark cap root [] (parents d e)))[stopDepth]? = some tailPart)
    {tailColumn : List Nat × Nat} {tailForests : Forests (List Nat × Nat)}
    (tailLast : last? tailPart = some (tailColumn, tailForests)) (count : Nat) :
    let delta := (List.range cap).map (fun j => terminal[j]?.getD 0 - rootColumn[j]?.getD 0)
    let donation := if cap = d then some (dropLastForest tailForests) else none
    BN d [] (ascendReplace (mark cap root [] (parents d e))
      (copies (drop index rootPart) (stopDepth - rootDepth) delta donation count 1)
      (some stopDepth) delta 0) := by
  have width := selected_parent_width stopSelected stopLast parentSelected parentLast
  have bounded : cap ≤ d := by
    have bound := (highestParent_found parentTerminal.parents 0 cap root chosen).2.1
    rw [width] at bound
    omega
  by_cases top : cap = d
  · subst cap
    dsimp only
    rw [if_pos rfl]
    exact ordinary_high_expand_BN positive legal ordered stopSelected stopLast parentSelected parentLast
      chosen location rootRead partSelected tailSelected tailLast count
  · by_cases zero : cap = 0
    · subst cap
      dsimp only
      rw [if_neg top]
      simpa only [List.range_zero, List.map_nil] using
        ordinary_zero_expand_BN positive legal ordered first stopSelected stopLast parentSelected parentLast
          chosen location rootRead partSelected tailSelected tailLast count
    · exact ordinary_positive_expand_BN (by omega) (by omega) legal ordered stopSelected stopLast
        parentSelected parentLast chosen location rootRead partSelected tailSelected tailLast count

theorem expand_BN {d : Nat} (positive : 0 < d) {e f : NumericalExpr}
    (legal : FiniteLegal d [] e) (ordered : BN d [] e) (count : Nat)
    (edge : expand? d e count = some f) : BN d [] f := by
  cases outer : last? e with
  | none =>
    have same : f = .nil := by simpa only [expand?, outer, Option.pure_def, Option.some.injEq] using edge.symm
    subst f
    trivial
  | some outerColumn =>
    by_cases zero : zeroColumn outerColumn = true
    · have same : f = dropLast e := by
        simpa only [expand?, outer, zero, if_true, Option.pure_def, Option.some.injEq] using edge.symm
      rw [same]
      exact ordered.dropLast positive legal
    · simp only [expand?, outer] at edge
      rw [if_neg zero] at edge
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at edge
      obtain ⟨stop, stopSelected, stopColumn, stopLast, edge⟩ := edge
      obtain ⟨terminal, attached⟩ := stopColumn
      split at edge
      next specialCase =>
        have same : f = special count ((spine e).findIdx stopping) e := by
          simpa only [Option.pure_def, Option.some.injEq] using edge.symm
        obtain ⟨h, child, nonempty⟩ := specialColumn_last_nonempty specialCase
        rw [same]
        exact special_spine_BN count _ ordered positive legal stopSelected stopLast child nonempty
      next ordinary =>
        simp only [Option.bind_eq_some_iff] at edge
        obtain ⟨parentStop, parentSelected, parentColumn, parentLast, pair, chosen,
          locationPair, location, rootColumn, rootRead, rootPart, partSelected,
          tailPart, tailSelected, tailColumn, tailLast, result⟩ := edge
        obtain ⟨parentTerminal, parentAttached⟩ := parentColumn
        obtain ⟨cap, root⟩ := pair
        obtain ⟨rootDepth, index⟩ := locationPair
        obtain ⟨lastVector, lastForests⟩ := tailColumn
        have preserved := ordinary_expand_BN positive legal ordered rfl stopSelected stopLast parentSelected parentLast
          chosen location rootRead partSelected tailSelected tailLast count
        simp only [Option.pure_def, Option.some.injEq] at result
        rw [← result]
        exact preserved

theorem Reachable.BN {d : Nat} (positive : 0 < d) {start e : NumericalExpr}
    (path : Reachable d start e) (legal : FiniteLegal d [] start) (ordered : Source.BN d [] start) :
    Source.BN d [] e := by
  induction path with
  | refl => exact ordered
  | step path edge ih => exact expand_BN positive (path.finiteLegal positive legal) ih _ edge

theorem standard_BN {d : Nat} (positive : 0 < d) {e : NumericalExpr} (standard : Standard d e) : BN d [] e := by
  obtain ⟨k, path⟩ := standard
  exact path.BN positive (seed_finiteLegal d k positive) (seed_BN d k positive)

end BTnSSBMS.Source
