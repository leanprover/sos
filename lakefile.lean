import Lake
open Lake DSL

package sos where
  leanOptions := #[⟨`autoImplicit, false⟩]

-- TODO: re-enable once https://github.com/kim-em/lean-csdp lakefile uses
-- pkg-relative paths for the static-lib link arg (currently
-- `defaultBuildDir / lib / libleancsdp.a` resolves to consumer cwd, not
-- the lean-csdp package dir, breaking the dynlib link from a downstream
-- consumer). For v0, the SDP search backend in Sos/Search.lean is a stub.
-- require leanCsdp from git
--   "https://github.com/kim-em/lean-csdp" @ "main"

require «CompPoly» from git
  "https://github.com/Verified-zkEVM/CompPoly" @ "master"

@[default_target]
lean_lib Sos where
  precompileModules := true

lean_exe «sos-example» where
  root := `Sos.Examples
