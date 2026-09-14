import Lake
open Lake DSL

package ordinalnotations_ipd

require ordinalnotations_shared from "../shared"

/-- Exact module ownership lets sibling projects share Lean namespaces without overlap. -/
@[default_target]
lean_lib OrdinalNotationsIPD where
  srcDir := "src"
  roots := #[]
  globs := #[
    .one `IPDClosedSupply,
    .one `IPDColumnOrder,
    .one `IPDDecrease,
    .one `IPDDemandCore,
    .one `IPDDemandRecursion,
    .one `IPDEndpointAgreement,
    .one `IPDFiniteLabels,
    .one `IPDGraphController,
    .one `IPDGraphCore,
    .one `IPDGraphGeometry,
    .one `IPDGraphNormalization,
    .one `IPDGraphValidity,
    .one `IPDInitialRepresentation,
    .one `IPDProfileAtoms,
    .one `IPDProfileCountable,
    .one `IPDProfileIdentity,
    .one `IPDProfileLower,
    .one `IPDProfileOrder,
    .one `IPDProfileRename,
    .one `IPDProfileSubstitution,
    .one `IPDProfileValidity,
    .one `IPDSeeds,
    .one `IPDSemanticEdges,
    .one `IPDSemanticWellFounded,
    .one `IPDSpliceLabels,
    .one `IPDStageFacts,
    .one `IPDStageSplice,
    .one `IPDStandardOrder,
    .one `IPDTemplates,
    .one `IPDTree,
    .one `IPDTreeCompare,
    .one `IPDTreeLinearOrder,
    .one `IPDTreeLocalRename,
    .one `IPDTreeLower,
    .one `IPDTreeLowerClosure,
    .one `IPDTreeOrder,
    .one `IPDTreeRename,
    .one `IPDTreeSupport,
    .one `IPDTreeWellFounded,
    .one `IPDWitnesses
  ]
  moreLeanArgs := #["-M", "2048", "-j", "1"]
