import Lake
open System Lake DSL

/-! Per-platform BLAS / LAPACK link arguments for this package's own
native link steps.

`csdp-ffi` already carries these arguments for its own artifacts.
We repeat them here because `SOS.Search` imports and calls `CSDP`,
so the `SOS` and `SOSTest` shared-library link steps also need to
resolve the CSDP runtime dependencies.

Normal downstream packages that depend on `sos`, import `SOS`, and use
`by sos` do not need to copy these arguments into their lakefiles; they
only need the system BLAS/LAPACK runtime installed. A downstream package
that links directly against `CSDP` in its own native target may
still need equivalent arguments there. -/
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
  version := v!"0.1.0"
  description := "A Lean 4 sum-of-squares tactic for nonlinear real arithmetic."
  keywords := #["math", "software-verification", "tactic", "real-arithmetic", "sos", "sdp"]
  license := "Apache-2.0"
  leanOptions := #[⟨`autoImplicit, false⟩]

require CSDP from git
  "https://github.com/leanprover/csdp-ffi" @ "main"

require «CompPoly» from git
  "https://github.com/Verified-zkEVM/CompPoly" @ "master"

-- We don't set `precompileModules := true` on SOS itself: the FFI
-- (`@[extern]` declarations) lives in `CSDP.Basic`, which has
-- `precompileModules := true` upstream. Setting it here too triggers a
-- runtime-linker failure on Linux during sos's own dynlib loading
-- (libLake_shared.so isn't on LD_LIBRARY_PATH at compile time).
@[default_target]
lean_lib SOS where
  moreLinkArgs := blasLapackLinkArgs

@[test_driver]
lean_lib SOSTest where
  moreLinkArgs := blasLapackLinkArgs
