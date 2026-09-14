import Lake
open Lake DSL

package ordinalnotations_omega3

require ordinalnotations_shared from "../shared"

/-- Exact module ownership lets sibling projects share Lean namespaces without overlap. -/
@[default_target]
lean_lib OrdinalNotationsOmega3 where
  srcDir := "src"
  roots := #[]
  globs := #[
    .one `OmegaLRD3Final,
    .one `OrdinalFormal.FiniteUnionWellFounded,
    .one `OrdinalFormal.Omega3ColumnDecrease,
    .one `OrdinalFormal.Omega3Comparison,
    .one `OrdinalFormal.Omega3Countable,
    .one `OrdinalFormal.Omega3Domains,
    .one `OrdinalFormal.Omega3RowDomain,
    .one `OrdinalFormal.Omega3RowPool,
    .one `OrdinalFormal.Omega3Structure,
    .one `OrdinalFormal.Omega3Validity,
    .one `OrdinalFormal.Omega3WellOrderingReduction,
    .one `OrdinalFormal.OmegaLRD3,
    .one `OrdinalFormal.RowInvariant
  ]
  moreLeanArgs := #["-M", "2048", "-j", "1"]
