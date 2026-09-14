import FiveNotationFinalAudit
import IPDStandardOrder
import IPDTreeCompare

/-! Six-system ordinary-Lean acceptance. The five-system audit is unchanged.
IPD adds its actual standard column order, external TOP and expansion relation.
The extra comparison import checks the reference algorithm's branch equation.
This is not an encoded derivation inside KP or an order-type comparison. -/

#print axioms OrdinalFormal.YFiniteDemand.with_top_isWellOrder
#print axioms OrdinalFormal.RPDFiniteDemand.standard_with_top_strictWellOrder
#print axioms OrdinalFormal.LRDFinal.standard_isWellOrder
#print axioms OrdinalFormal.Omega3Final.with_top_isWellOrder
#print axioms OrdinalFormal.ARD.paper_standard_with_top_strictWellOrder
#print axioms IPD.standard_wellFounded
#print axioms IPD.standard_total
#print axioms IPD.term_wellFounded
#print axioms IPD.Semantics.valid_step_wellFounded
#print axioms IPD.Tree.cmp_node_rule
