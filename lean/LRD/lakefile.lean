import Lake
open Lake DSL

package ordinalnotations_lrd

require ordinalnotations_shared from "../shared"

/-- Exact module ownership lets sibling projects share Lean namespaces without overlap. -/
@[default_target]
lean_lib OrdinalNotationsLRD where
  srcDir := "src"
  roots := #[]
  globs := #[
    .one `FiniteDemandLRDFinal,
    .one `LRDOrdinalRows,
    .one `OrdinalFormal.LRDCanonical,
    .one `OrdinalFormal.LRDColumnDecrease,
    .one `OrdinalFormal.LRDNormalLift,
    .one `OrdinalFormal.LRDRowDecrease,
    .one `OrdinalFormal.LRDRowWellFounded,
    .one `OrdinalFormal.LRDStructure,
    .one `OrdinalFormal.LRDWellOrderingReduction,
    .one `OrdinalRowLanguage
  ]
  moreLeanArgs := #["-M", "2048", "-j", "1"]
