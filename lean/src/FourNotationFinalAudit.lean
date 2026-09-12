import FiniteDemandYFinal
import FiniteDemandRPDFinal
import FiniteDemandLRDFinal
import OmegaLRD3Final

/-! Final ordinary-Lean acceptance: actual Y, RPD, LRD, and Omega-LRD3.
None of these theorem statements takes a semantic reflection, initial supply,
seed accessibility, or row-well-foundedness assumption from the caller.
The restricted-KP justification is the separate paper, not this axiom report. -/

#check OrdinalFormal.YFiniteDemand.expansion_wellFounded
#check OrdinalFormal.YFiniteDemand.generated_strictWellOrder
#check OrdinalFormal.YFiniteDemand.with_top_isWellOrder
#check OrdinalFormal.RPDFiniteDemand.standard_strictWellOrder
#check OrdinalFormal.RPDFiniteDemand.standard_with_top_strictWellOrder
#check OrdinalFormal.LRDFinal.standard_isWellOrder
#check OrdinalFormal.Omega3Final.standard_isWellOrder
#check OrdinalFormal.Omega3Final.with_top_isWellOrder

#print axioms OrdinalFormal.YFiniteDemand.expansion_wellFounded
#print axioms OrdinalFormal.YFiniteDemand.generated_strictWellOrder
#print axioms OrdinalFormal.YFiniteDemand.with_top_isWellOrder
#print axioms OrdinalFormal.RPDFiniteDemand.standard_with_top_strictWellOrder
#print axioms OrdinalFormal.LRDFinal.standard_isWellOrder
#print axioms OrdinalFormal.Omega3Final.standard_isWellOrder
#print axioms OrdinalFormal.Omega3Final.with_top_isWellOrder
