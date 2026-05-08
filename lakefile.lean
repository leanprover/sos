import Lake
open Lake DSL

package sos where
  -- Disabling warningAsError to keep iteration friction low; will tighten
  -- once the implementation stabilises.
  leanOptions := #[⟨`autoImplicit, false⟩]

require leanCsdp from git
  "https://github.com/kim-em/lean-csdp" @ "main"

require «CompPoly» from git
  "https://github.com/Verified-zkEVM/CompPoly" @ "master"

-- Pin Mathlib explicitly. Lake requires this require to come AFTER any
-- other `require`s that themselves depend on Mathlib (e.g. CompPoly), so
-- that Mathlib's transitive-dep pins win.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

@[default_target]
lean_lib Sos where
  precompileModules := true

lean_exe «sos-example» where
  root := `Sos.Examples
