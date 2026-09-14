import SixNotationFinalAudit
import ARD2Final
import ARD2Compression

/-! Seven-system ordinary-Lean acceptance. Earlier audits remain unchanged.
ARD2 adds two endpoint SELF coordinates, full-context root packages, the actual
staged splice, and the independent paper-rule and compressed-root bridges.
No object-theory derivability or comparison between order types is asserted. -/

#print axioms OrdinalFormal.YFiniteDemand.with_top_isWellOrder
#print axioms OrdinalFormal.RPDFiniteDemand.standard_with_top_strictWellOrder
#print axioms OrdinalFormal.LRDFinal.standard_isWellOrder
#print axioms OrdinalFormal.Omega3Final.with_top_isWellOrder
#print axioms OrdinalFormal.ARD.paper_standard_with_top_strictWellOrder
#print axioms IPD.term_wellFounded
#print axioms OrdinalFormal.ARD2.valid_step_wellFounded
#print axioms OrdinalFormal.ARD2.standard_strictWellOrder
#print axioms OrdinalFormal.ARD2.paper_standard_with_top_strictWellOrder
