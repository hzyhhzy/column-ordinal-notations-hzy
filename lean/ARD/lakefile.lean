import Lake
open Lake DSL

package ordinalnotations_ard

require ordinalnotations_shared from "../shared"
require ordinalnotations_ard_legacy from "../ARD-legacy"

@[default_target]
lean_lib OrdinalNotationsARDSkyline where
  srcDir := "src"
  roots := #[]
  globs := #[
    .one `ARDSkylineBridge,
    .one `ARDSkylineCore,
    .one `ARDSkylineDomain,
    .one `ARDSkylineFinal,
    .one `ARDSkylineOrderReduction,
    .one `ARDSkylineSemanticWellFounded,
    .one `ARDSkylineStructure
  ]
  moreLeanArgs := #["-M", "2048", "-j", "1"]
