import Lake
open Lake DSL

package ordinalnotations_rpd

require ordinalnotations_shared from "../shared"

/-- Exact module ownership lets sibling projects share Lean namespaces without overlap. -/
@[default_target]
lean_lib OrdinalNotationsRPD where
  srcDir := "src"
  roots := #[]
  globs := #[
    .one `FiniteDemandRPDFinal,
    .one `OrdinalFormal.RPDDefinitionFidelity,
    .one `OrdinalFormal.RPDTermOrder,
    .one `OrdinalFormal.RPDWellOrderingReduction
  ]
  moreLeanArgs := #["-M", "2048", "-j", "1"]
