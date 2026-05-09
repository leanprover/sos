import Lake
open System Lake DSL

/-! Per-platform BLAS / LAPACK link arguments. Lake does not propagate
native-link arguments from a dependency to a downstream package's
link step, so consumers of `lean-csdp` must replicate these. -/
def blasLapackLinkArgs : Array String :=
  if System.Platform.isOSX then
    #["-Wl,-syslibroot,/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk",
      "-framework", "Accelerate"]
  else if System.Platform.isWindows then
    #["-Lvendor/mingw-libs", "-LC:/msys64/mingw64/lib",
      "-lopenblas", "-lgfortran", "-lquadmath", "-lm"]
  else
    #["-L/usr/lib/x86_64-linux-gnu", "-L/usr/lib/aarch64-linux-gnu",
      "-L/usr/lib64", "-L/usr/lib",
      "-llapack", "-lblas", "-l:libgfortran.so.5", "-lm"]

package sos where
  leanOptions := #[⟨`autoImplicit, false⟩]

require leanCsdp from git
  "https://github.com/kim-em/lean-csdp" @ "main"

require «CompPoly» from git
  "https://github.com/Verified-zkEVM/CompPoly" @ "master"

-- We don't set `precompileModules := true` on Sos itself: the FFI
-- (`@[extern]` declarations) lives in `LeanCsdp.Basic`, which has
-- `precompileModules := true` upstream. Setting it here too triggers a
-- runtime-linker failure on Linux during sos's own dynlib loading
-- (libLake_shared.so isn't on LD_LIBRARY_PATH at compile time).
@[default_target]
lean_lib Sos where
  moreLinkArgs := blasLapackLinkArgs

lean_exe «sos-example» where
  root := `Sos.Examples
  moreLinkArgs := blasLapackLinkArgs
