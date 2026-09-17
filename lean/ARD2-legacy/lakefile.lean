import Lake
open Lake DSL

package ordinalnotations_ard2_legacy

require ordinalnotations_shared from "../shared"

/-- Exact module ownership lets sibling projects share Lean namespaces without overlap. -/
@[default_target]
lean_lib OrdinalNotationsARD2 where
  srcDir := "src"
  roots := #[]
  globs := #[
    .one `ARD2ClosedSupply,
    .one `ARD2Compression,
    .one `ARD2Core,
    .one `ARD2Decrease,
    .one `ARD2DefinitionFidelity,
    .one `ARD2DemandCore,
    .one `ARD2DemandRecursion,
    .one `ARD2DemandReflection,
    .one `ARD2Domain,
    .one `ARD2EndpointAgreement,
    .one `ARD2Final,
    .one `ARD2FiniteUnion,
    .one `ARD2InitialRepresentation,
    .one `ARD2OrderReduction,
    .one `ARD2SemanticWellFounded,
    .one `ARD2Splice,
    .one `ARD2StageDemands,
    .one `ARD2StageProof,
    .one `ARD2Structure,
    .one `ARD2Templates,
    .one `ARD2Witnesses
  ]
  moreLeanArgs := #["-M", "2048", "-j", "1"]
