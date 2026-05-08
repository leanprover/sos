import Lake
open Lake DSL

package sos where
  leanOptions := #[⟨`autoImplicit, false⟩]

require leanCsdp from git
  "https://github.com/kim-em/lean-csdp" @ "main"

require «CompPoly» from git
  "https://github.com/Verified-zkEVM/CompPoly" @ "master"

@[default_target]
lean_lib Sos where
  precompileModules := true

lean_exe «sos-example» where
  root := `Sos.Examples
