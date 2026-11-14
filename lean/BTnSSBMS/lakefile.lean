import Lake
open Lake DSL

package btnss_bms

@[default_target]
lean_lib BTnSSBMS where
  srcDir := "src"
  roots := #[`BTnSSBMS.Audit]
  moreLeanArgs := #["-M", "2048", "-j", "1"]
