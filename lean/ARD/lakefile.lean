import Lake
open Lake DSL

package ordinalnotations_ard

require ordinalnotations_shared from "../shared"

/-- Exact module ownership lets sibling projects share Lean namespaces without overlap. -/
@[default_target]
lean_lib OrdinalNotationsARD where
  srcDir := "src"
  roots := #[]
  globs := #[
    .one `ARDClosedSupply,
    .one `ARDCompression,
    .one `ARDCore,
    .one `ARDDecrease,
    .one `ARDDefinitionFidelity,
    .one `ARDDemandCore,
    .one `ARDDemandRecursion,
    .one `ARDDemandReflection,
    .one `ARDDomain,
    .one `ARDEndpointAgreement,
    .one `ARDFinal,
    .one `ARDFiniteUnion,
    .one `ARDInitialRepresentation,
    .one `ARDOrderReduction,
    .one `ARDSemanticWellFounded,
    .one `ARDSplice,
    .one `ARDStageDemands,
    .one `ARDStageProof,
    .one `ARDStructure,
    .one `ARDWitnesses
  ]
  moreLeanArgs := #["-M", "2048", "-j", "1"]
