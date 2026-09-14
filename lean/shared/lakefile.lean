import Lake
open Lake DSL

package ordinalnotations_shared

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "eba3d887fc52c98627f4b81507c0efc3096e91b9"

/-- Exact module ownership lets sibling projects share Lean namespaces without overlap. -/
@[default_target]
lean_lib OrdinalNotationsShared where
  srcDir := "src"
  roots := #[]
  globs := #[
    .one `ARDPrefixOrder,
    .one `FiniteDemandClosedSupply,
    .one `FiniteDemandColumnWellFounded,
    .one `FiniteDemandCore,
    .one `FiniteDemandEndpointAgreement,
    .one `FiniteDemandFinitaryClosure,
    .one `FiniteDemandHostAmbient,
    .one `FiniteDemandInitialRepresentation,
    .one `FiniteDemandOrdinalHeight,
    .one `FiniteDemandRecursion,
    .one `FiniteDemandReflection,
    .one `FiniteDemandWitnesses,
    .one `OrdinalFormal.ActualBlockGeometry,
    .one `OrdinalFormal.BlockFiniteUnion,
    .one `OrdinalFormal.ColumnMap,
    .one `OrdinalFormal.ColumnReachability,
    .one `OrdinalFormal.ColumnRepresentation,
    .one `OrdinalFormal.Columns,
    .one `OrdinalFormal.Comparison,
    .one `OrdinalFormal.Domains,
    .one `OrdinalFormal.ExpansionValidity,
    .one `OrdinalFormal.GeneratedColumnDecrease,
    .one `OrdinalFormal.GeneratedSemanticWellFounded,
    .one `OrdinalFormal.GeneratedStagedReflection,
    .one `OrdinalFormal.GenericSortedColumns,
    .one `OrdinalFormal.LRD,
    .one `OrdinalFormal.RPD,
    .one `OrdinalFormal.RPDDecrease,
    .one `OrdinalFormal.RPDFiniteUnion,
    .one `OrdinalFormal.RPDGeometry,
    .one `OrdinalFormal.RPDSortedColumns,
    .one `OrdinalFormal.Reachability,
    .one `OrdinalFormal.ReflectionTransport,
    .one `OrdinalFormal.SpliceConstruction,
    .one `OrdinalFormal.StandardValidity
  ]
  moreLeanArgs := #["-M", "2048", "-j", "1"]
