import FourNotationFinalAudit
import ARDFinal
import ARDCompression

/-! Five-system ordinary-Lean acceptance. The original four-system audit is
preserved verbatim. ARD adds the actual dynamic-row finite-demand construction,
the independent paper-standard-domain bridge, and compressed/full-root fidelity.
These are host-Lean proofs, not encoded derivations in a restricted set theory. -/

#print axioms OrdinalFormal.YFiniteDemand.with_top_isWellOrder
#print axioms OrdinalFormal.RPDFiniteDemand.standard_with_top_strictWellOrder
#print axioms OrdinalFormal.LRDFinal.standard_isWellOrder
#print axioms OrdinalFormal.Omega3Final.with_top_isWellOrder
#print axioms OrdinalFormal.ARD.standard_with_top_strictWellOrder
#print axioms OrdinalFormal.ARD.paper_standard_with_top_strictWellOrder
#print axioms OrdinalFormal.ARD.valid_step_wellFounded
#print axioms OrdinalFormal.ARD.Fidelity.standard_paper_fs_iff
#print axioms OrdinalFormal.ARD.Fidelity.paper_standard_iff
#print axioms OrdinalFormal.ARD.Compression.normalize_eq_fullRoots
#print axioms OrdinalFormal.ARD.Compression.normalize_graphCompare
#print axioms OrdinalFormal.ARD.Compression.control_normalize
