import Lake
open Lake DSL

package ordinalnotations

require ordinalnotations_y from "Y"
require ordinalnotations_rpd from "RPD"
require ordinalnotations_lrd from "LRD"
require ordinalnotations_omega3 from "Omega-LRD3"
require ordinalnotations_ard from "ARD"
require ordinalnotations_ard_legacy from "ARD-legacy"
require ordinalnotations_ipd from "IPD"
require ordinalnotations_ard2 from "ARD2"
require ordinalnotations_ard2_legacy from "ARD2-legacy"

/-- Exact module ownership lets sibling projects share Lean namespaces without overlap. -/
@[default_target]
lean_lib OrdinalNotations where
  srcDir := "src"
  roots := #[]
  globs := #[
    .one `ARD2RevisionFinalAudit,
    .one `ARDRevisionFinalAudit,
    .one `FiveNotationFinalAudit,
    .one `FourNotationFinalAudit,
    .one `SevenNotationFinalAudit,
    .one `SixNotationFinalAudit
  ]
  moreLeanArgs := #["-M", "2048", "-j", "1"]
