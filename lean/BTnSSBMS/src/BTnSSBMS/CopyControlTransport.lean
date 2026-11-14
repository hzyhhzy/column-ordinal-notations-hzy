import BTnSSBMS.EncoderFrameTransport

/-! The full control-transport result applied to the frozen literal
activation/shift copy, including all unmodified nested attachments.
The entry-frame relation remains an explicit finite premise; it is not
claimed here for every block comparison or replacement seam. -/
namespace BTnSSBMS.Encoder

theorem encode_copied_control {d : Nat} {source target : ParentContext}
    {moved history visible nextVisible owners : List Nat}
    {materials : List (Forests (List Nat))} {state next : State d}
    {root cap phase : Nat} {delta : List Nat}
    (scope : Source.ShiftView d source target moved history root cap delta phase)
    (oldView : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (newView : Parents.NumericalView d target (BMS.parentTable (d + 2) (matrix next)) nextVisible)
    (targetWidth : ∀ i, i < target.length → (target[i]?.getD default).coordinates.length = d)
    (known : VisibleMaterials d source visible owners materials state)
    (related : CoupledFrames d source target moved visible nextVisible materials state next)
    (positive : 0 < d) (e : NumericalExpr) (legal : Source.FiniteLegal d source e) :
    SharedTrace state next (encode d (Parents.annotate d source e) visible state)
      (encode d (Parents.annotate d target (Source.copied d root cap delta phase source history e)) nextVisible next) := by
  rw [← Source.relocate_eq_copied scope e legal]
  exact encode_relocation_control d e source target moved visible nextVisible owners materials state next positive
    scope.sourceCoherent scope.sourceValid scope.targetCoherent scope.targetValid scope.targetUnit scope.view
    oldView newView targetWidth known related legal

end BTnSSBMS.Encoder
