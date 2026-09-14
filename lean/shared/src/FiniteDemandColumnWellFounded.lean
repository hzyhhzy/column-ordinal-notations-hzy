import FiniteDemandHostAmbient
import OrdinalFormal.GeneratedSemanticWellFounded

/-!
All semantic inputs of the actual generated-column transport are now supplied.
Only the concrete row order/comparator/package obligations remain parameters.
The unconditional exit uses the explicitly constructed host ambient; no claim
of weak-object-theory certification is made in this module.
-/

namespace FiniteDemand
open OrdinalFormal

universe v
variable {Row : Type v} [Countable Row]

theorem valid_accessible_in_ambient
    (cmp : Row → Row → Ordering) (package : Columns.Package Row)
    (rowLt : Row → Row → Prop) (hw : WellFounded rowLt)
    (htrans : ∀ {a b c}, rowLt a b → rowLt b c → rowLt a c)
    (hpackage : ∀ high b low, low ∈ package high b → rowLt low high)
    (laws : ColumnRepresentation.RowCompareSound cmp rowLt) (E : Ambient.{0})
    (g : Columns.Graph Row) (hg : Columns.Valid g) :
    Acc (GeneratedSemanticWellFounded.Step cmp package) g :=
  GeneratedSemanticWellFounded.valid_accessible_of_semantics cmp package rowLt
    (· < ·) domain (relation.{0} rowLt hw) Ordinal.lt_wf
    (fun h₁ h₂ => lt_trans h₁ h₂) (fun h => strict h)
    (fun h₁ h₂ => root_weaken h₁.le h₂) (lower_rows rowLt hw (@htrans))
    hpackage laws (finite_reflection rowLt hw) (initial_columns rowLt hw E) g hg

theorem valid_accessible
    (cmp : Row → Row → Ordering) (package : Columns.Package Row)
    (rowLt : Row → Row → Prop) (hw : WellFounded rowLt)
    (htrans : ∀ {a b c}, rowLt a b → rowLt b c → rowLt a c)
    (hpackage : ∀ high b low, low ∈ package high b → rowLt low high)
    (laws : ColumnRepresentation.RowCompareSound cmp rowLt)
    (g : Columns.Graph Row) (hg : Columns.Valid g) :
    Acc (GeneratedSemanticWellFounded.Step cmp package) g :=
  valid_accessible_in_ambient cmp package rowLt hw htrans hpackage laws HostAmbient.actual g hg

end FiniteDemand

#print axioms FiniteDemand.valid_accessible_in_ambient
#print axioms FiniteDemand.valid_accessible
