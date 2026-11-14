import BTnSSBMS.EncoderStrictOrder
import BTnSSBMS.SourceFiniteClosure

/-!
Connect strict comparison to the actual seed-reachable source domain.
This is an order-faithful injection into raw fixed-width BMS matrices;
target standardness and the ordinal upper bound are not concluded here.
-/
namespace BTnSSBMS.Encoder

theorem encode_compare (d : Nat) (e f : NumericalExpr)
    (source : ParentContext) (visible : List Nat) (state : State d)
    (positive : 0 < d) (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (ordered : FramesOrdered state) (dense : FramesDense state) (good : VisibleGood state visible)
    (leftLegal : Source.FiniteLegal d source e) (rightLegal : Source.FiniteLegal d source f) :
    matrixCompare (matrix (encode d (Parents.annotate d source e) visible state))
      (matrix (encode d (Parents.annotate d source f) visible state)) =
      e.compare (listCompare Ord.compare) f := by
  have columnFlip := listCompare_oriented Ord.compare
    (fun a b : Nat => Std.OrientedOrd.eq_swap (a := a) (b := b))
  cases compared : e.compare (listCompare Ord.compare) f with
  | lt =>
    exact encode_strict_order d e f source visible state positive coherent valid view
      ordered dense good leftLegal rightLegal compared
  | eq =>
    have same := Expr.compare_eq_imp (listCompare Ord.compare)
      (fun x y h => listCompare_eq_imp Ord.compare (fun _ _ h => Nat.compare_eq_eq.mp h) x y h) e f compared
    subst f
    exact Ordering.eq_eq_of_eq_swap (listCompare_oriented (listCompare Ord.compare) columnFlip _ _)
  | gt =>
    have reverse := Expr.compare_oriented (listCompare Ord.compare) columnFlip f e
    simp only [compared, Ordering.swap] at reverse
    have encoded := encode_strict_order d f e source visible state positive coherent valid view
      ordered dense good rightLegal leftLegal reverse
    have flip := listCompare_oriented (listCompare Ord.compare) columnFlip
      (matrix (encode d (Parents.annotate d source e) visible state))
      (matrix (encode d (Parents.annotate d source f) visible state))
    change matrixCompare _ _ = (matrixCompare _ _).swap at flip
    simpa only [encoded, Ordering.swap] using flip

theorem source_compare (d : Nat) (e f : NumericalExpr) (positive : 0 < d)
    (leftLegal : Source.FiniteLegal d [] e) (rightLegal : Source.FiniteLegal d [] f) :
    matrixCompare (fromSource d e) (fromSource d f) = e.compare (listCompare Ord.compare) f :=
  encode_compare d e f [] [] [] positive (Parents.empty_coherent d) Parents.empty_context_valid
    (Parents.empty_numerical_view d) (by intro col member; simp at member)
    (by intro col member; simp at member) (by intro p member; simp at member) leftLegal rightLegal

theorem source_injective (d : Nat) (e f : NumericalExpr) (positive : 0 < d)
    (leftLegal : Source.FiniteLegal d [] e) (rightLegal : Source.FiniteLegal d [] f)
    (same : fromSource d e = fromSource d f) : e = f := by
  have comparison := source_compare d e f positive leftLegal rightLegal
  rw [same] at comparison
  have selfCompare : matrixCompare (fromSource d f) (fromSource d f) = .eq := by
    exact Ordering.eq_eq_of_eq_swap (listCompare_oriented (listCompare Ord.compare)
      (listCompare_oriented Ord.compare (fun a b : Nat => Std.OrientedOrd.eq_swap (a := a) (b := b))) _ _)
  exact Expr.compare_eq_imp (listCompare Ord.compare)
    (fun x y h => listCompare_eq_imp Ord.compare (fun _ _ h => Nat.compare_eq_eq.mp h) x y h)
    e f (comparison.symm.trans selfCompare)

theorem standard_compare {d : Nat} (positive : 0 < d) {e f : NumericalExpr}
    (leftStandard : Source.Standard d e) (rightStandard : Source.Standard d f) :
    matrixCompare (fromSource d e) (fromSource d f) = e.compare (listCompare Ord.compare) f :=
  source_compare d e f positive (Source.standard_finiteLegal positive leftStandard)
    (Source.standard_finiteLegal positive rightStandard)

theorem standard_injective {d : Nat} (positive : 0 < d) {e f : NumericalExpr}
    (leftStandard : Source.Standard d e) (rightStandard : Source.Standard d f)
    (same : fromSource d e = fromSource d f) : e = f :=
  source_injective d e f positive (Source.standard_finiteLegal positive leftStandard)
    (Source.standard_finiteLegal positive rightStandard) same

end BTnSSBMS.Encoder
