import Lake
open Lake DSL

package ordinalnotations_ard2

require ordinalnotations_shared from "../shared"
require ordinalnotations_ard2_legacy from "../ARD2-legacy"

/-- Exact module ownership lets sibling projects share Lean namespaces without overlap. -/
@[default_target]
lean_lib OrdinalNotationsARD2Skyline where
  srcDir := "src"
  roots := #[]
  globs := #[
    .one `ARD2SkylineBridge,
    .one `ARD2SkylineCore,
    .one `ARD2SkylineDomain,
    .one `ARD2SkylineFinal,
    .one `ARD2SkylineOrderReduction,
    .one `ARD2SkylineSemanticWellFounded,
    .one `ARD2SkylineStructure
  ]
  moreLeanArgs := #["-M", "2048", "-j", "1"]
