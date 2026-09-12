import Lake
open Lake DSL

package ordinalnotations

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "eba3d887fc52c98627f4b81507c0efc3096e91b9"
require YesMetaZFC from git
  "https://github.com/EgoFakeFantasy/BMS-Well-Ordering-Lean" @ "bae7e3d741f24a56d80da9b99c1345562cd10c2d"

@[default_target]
lean_lib OrdinalNotations where
  srcDir := "src"
  roots := #[`FiniteDemandClosedSupply, `FiniteDemandColumnWellFounded, `FiniteDemandCore, `FiniteDemandEndpointAgreement, `FiniteDemandFinitaryClosure, `FiniteDemandHostAmbient, `FiniteDemandInitialRepresentation, `FiniteDemandLRDFinal, `FiniteDemandOrdinalHeight, `FiniteDemandRPDFinal, `FiniteDemandRecursion, `FiniteDemandReflection, `FiniteDemandWitnesses, `FiniteDemandYFinal, `FourNotationFinalAudit, `LRDOrdinalRows, `NatSemanticTransport, `OmegaLRD3Final, `OneY, `OrdinalFormal, `OrdinalRowLanguage, `ZeroY]
  globs := #[.one `FourNotationFinalAudit]
  moreLeanArgs := #["-M", "2048", "-j", "1"]
