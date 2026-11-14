import BTnSSBMS.SourceZeroAssembly
import BTnSSBMS.SourceSeeds

/-! All successful branches of the frozen source expansion preserve the
ordinary finite legality conditions. This closes that invariant on the
actual seed-reachable domain; totality and block-order invariants are
separate statements. -/
namespace BTnSSBMS.Source

mutual
  theorem fillTop_annotate_width (d : Nat) (context : ParentContext) (keyContext : KeyContext)
      (owners : List Nat) (e : NumericalExpr) :
      (fillTop d keyContext owners (Parents.annotate d context e)).map (fun a => a.parents.length) =
        e.map (fun _ => d + 1) := by
    cases e with
    | nil => rfl
    | cons a hs rest =>
      simp only [Parents.annotate, fillTop, Expr.map, List.length_append, List.length_cons,
        List.length_nil, Parents.label_width, fillTopForests_annotate_width, fillTop_annotate_width]
  theorem fillTopForests_annotate_width (d : Nat) (context : ParentContext) (keyContext : KeyContext)
      (owners : List Nat) (hs : Forests (List Nat)) :
      (fillTopForests d keyContext owners (Parents.annotateForests d context hs)).map (fun a => a.parents.length) =
        hs.map (fun _ => d + 1) := by
    cases hs with
    | nil => rfl
    | cons h rest =>
      simp only [Parents.annotateForests, fillTopForests, Forests.map,
        fillTop_annotate_width, fillTopForests_annotate_width]
end

theorem parents_width (d : Nat) (e : NumericalExpr) :
    (parents d e).map (fun a => a.parents.length) = e.map (fun _ => d + 1) :=
  fillTop_annotate_width d [] [] [] e

theorem selected_parent_width {d depth : Nat} {e stop : NumericalExpr}
    (stopSelected : (spine e)[depth]? = some stop)
    {terminal : List Nat} {attached : Forests (List Nat)}
    (stopLast : last? stop = some (terminal, attached))
    {parentStop : ParentExpr} {parentTerminal : ParentLabel} {parentAttached : Forests ParentLabel}
    (parentSelected : (spine (parents d e))[depth]? = some parentStop)
    (parentLast : last? parentStop = some (parentTerminal, parentAttached)) :
    parentTerminal.parents.length = d + 1 := by
  have equation := congrArg (fun term : Expr Nat => (spine term)[depth]?) (parents_width d e)
  simp only [spine_map, List.getElem?_map, parentSelected, stopSelected, Option.map_some] at equation
  have last := congrArg last? (Option.some.inj equation)
  simp only [last_map, parentLast, stopLast, Option.map_some, Option.some.injEq, Prod.mk.injEq] at last
  exact last.1

theorem expand_finiteLegal {d : Nat} {e f : NumericalExpr}
    (positive : 0 < d) (legal : FiniteLegal d [] e)
    (count : Nat) (edge : expand? d e count = some f) : FiniteLegal d [] f := by
  cases atLast : last? e with
  | none =>
    have empty := (last_none_iff e).mp atLast
    subst e
    have same : f = .nil := by simpa only [expand_empty, Option.some.injEq] using edge.symm
    subst f
    trivial
  | some column =>
    by_cases zero : zeroColumn column = true
    · have result := expand_zero_finiteLegal d count legal atLast zero
      have same : f = dropLast e := Option.some.inj (edge.symm.trans result.1)
      subst f
      exact result.2
    · cases stopSelected : (spine e)[(spine e).findIdx stopping]? with
      | none => simp [expand?, atLast, zero, stopSelected] at edge
      | some stop =>
        cases stopLast : last? stop with
        | none => simp [expand?, atLast, zero, stopSelected, stopLast] at edge
        | some stopColumn =>
          obtain ⟨terminal, attached⟩ := stopColumn
          by_cases specialCase : specialColumn (terminal, attached) = true
          · have same : f = special count ((spine e).findIdx stopping) e := by
              simpa [expand?, atLast, zero, stopSelected, stopLast, specialCase] using edge.symm
            subst f
            exact special_spine_finiteLegal count _ legal stopSelected stopLast specialCase
          · cases parentSelected : (spine (parents d e))[(spine e).findIdx stopping]? with
            | none => simp [expand?, atLast, zero, stopSelected, stopLast, specialCase, parentSelected] at edge
            | some parentStop =>
              cases parentLast : last? parentStop with
              | none =>
                simp [expand?, atLast, zero, stopSelected, stopLast, specialCase, parentSelected, parentLast] at edge
              | some parentColumn =>
                obtain ⟨parentTerminal, parentAttached⟩ := parentColumn
                cases chosen : highestParent 0 parentTerminal.parents with
                | none =>
                  simp [expand?, atLast, zero, stopSelected, stopLast, specialCase,
                    parentSelected, parentLast, chosen] at edge
                | some pair =>
                  obtain ⟨cap, root⟩ := pair
                  have width := selected_parent_width stopSelected stopLast parentSelected parentLast
                  have bound := (highestParent_found parentTerminal.parents 0 cap root chosen).2.1
                  rw [width] at bound
                  by_cases top : cap = d
                  · subst cap
                    exact expand_high_finiteLegal legal positive parentSelected parentLast chosen count edge
                  · have low : cap < d := by omega
                    by_cases zeroClass : cap = 0
                    · subst cap
                      exact expand_zero_class_finiteLegal legal positive parentSelected parentLast chosen count edge
                    · exact expand_positive_low_finiteLegal legal (by omega) low
                        parentSelected parentLast chosen count edge

theorem Reachable.finiteLegal {d : Nat} (positive : 0 < d) {start e : NumericalExpr}
    (path : Reachable d start e) (legal : FiniteLegal d [] start) : FiniteLegal d [] e := by
  induction path with
  | refl => exact legal
  | step path edge ih => exact expand_finiteLegal positive ih _ edge

theorem standard_finiteLegal {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Standard d e) : FiniteLegal d [] e := by
  obtain ⟨k, path⟩ := standard
  exact path.finiteLegal positive (seed_finiteLegal d k positive)

end BTnSSBMS.Source

namespace BTnSSBMS.Encoder

theorem standard_numericallyLegal {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) : BMS.NumericallyLegal (d + 2) (fromSource d e) :=
  finiteLegal_source_numericallyLegal d e positive (Source.standard_finiteLegal positive standard)

end BTnSSBMS.Encoder
