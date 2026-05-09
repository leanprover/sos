# sos

[![CI](https://github.com/kim-em/sos/actions/workflows/ci.yml/badge.svg)](https://github.com/kim-em/sos/actions/workflows/ci.yml)

Harrison's sum-of-squares decision procedure for nonlinear real
arithmetic, in Lean 4. Based on the design from
[Harrison 2007 (TPHOLs)](https://link.springer.com/chapter/10.1007/978-3-540-74591-4_9).

## Status

The `by sos` tactic closes nonlinear-real-arithmetic goals end-to-end:
reify the goal, encode an SDP, call CSDP, round the float Gram matrix
to rationals, decompose via LDLᵀ + Lagrange four-square, and dispatch
the matching verifier-soundness lemma. All five end-state goals
close automatically:

```lean
import Sos
example : ∀ x : Fin 1 → ℝ, 0 ≤ (x 0)^2 + 1 := by sos
example : ∀ x : Fin 2 → ℝ, 0 ≤ (x 0)^2 + 2*(x 0)*(x 1) + (x 1)^2 := by sos
example : ∀ x : Fin 1 → ℝ, 0 < (x 0)^2 + 1 := by sos
example : ∀ x : Fin 1 → ℝ, ¬ ((x 0)^2 + 1 ≤ 0) := by sos
example : ∀ x : Fin 1 → ℝ, 0 ≤ x 0 → 0 ≤ (x 0)^2 - x 0 + 1/4 := by sos
```

The Motzkin polynomial `x⁴y² + x²y⁴ + 1 - 3x²y²` is non-negative but
not a sum of squares (Hilbert 1888 / Motzkin 1967); `by sos`
correctly fails to find a certificate, caught here by
`fail_if_success`:

```lean
example : True := by
  fail_if_success
    (have : ∀ x : Fin 2 → ℝ,
        0 ≤ (x 0)^4 * (x 1)^2 + (x 0)^2 * (x 1)^4 + 1
            - 3*(x 0)^2*(x 1)^2 := by sos)
  trivial
```

`by sos_witness <cert>` is also available for cases where the user
wants to supply a hand-built certificate directly.

The library is sorry-free and axiom-free. Soundness factors through
`IsSumSq.nonneg` (Mathlib) and the `aeval` ring-hom structure on
CompPoly's `CMvPolynomial n ℚ`. Two design points worth flagging,
both following Harrison's [TPHOLs 2007 paper]
(https://link.springer.com/chapter/10.1007/978-3-540-74591-4_9):

- **`min tr(X)` cost matrix.** CSDP's interior-point step has no
  preferred direction on a singleton boundary feasible set, so we
  give it the trace objective Harrison reports works empirically.
- **Zero-pivot LDLᵀ.** Rank-deficient SOS Grams (`(x + y)²` has
  Gram `[[1,1],[1,1]]`, rank 1) require the "completing the square"
  routine to accept a zero pivot when the residual column is also
  zero. Our `Sos.LDL.decompose` does this; `LDL.reconstruct` already
  drops the zero-D contributions.

## Smoke test

```
git clone https://github.com/kim-em/sos
cd sos
lake exe cache get
lake build sos-example
.lake/build/bin/sos-example
```

Expected output (last few lines):

```
Success: SDP solved
Primal objective value: 0.0000000e+00
Dual objective value: 0.0000000e+00
Relative primal infeasibility: 0.00e+00
Relative dual infeasibility: 5.00e-11
✓ runSearch produced cert with 2 σ₀-squares, 0 σᵢ blocks.
✓ cert.checks smokeGoal [] = true
```

## Architecture

```
goal expression  ── Sos.Reify.parseGoalFull ──▶  ParsedGoal
                                                       │
                                                       ▼
                                              Sos.Search.runSearch
                                                       │
                                                       │  builds SDP, calls CSDP,
                                                       │  rounds rationals, runs LDL,
                                                       │  reconstructs squares
                                                       │
                                                       ▼
                                              Sos.Certificate n  (validated)
                                                       │
                                                       ▼
                                          Sos.Tactic.closeClosedSos /
                                          closeStrictSos /
                                          closeInfeasibleSos
                                                       │
                                                       ▼
                                                ℝ-level proof
```

| Module | What it provides |
|---|---|
| `Sos.Atoms` | Atom-table type for the reifier. |
| `Sos.Raw` | `Poly.Raw` and typed `Poly n` ASTs + reflection theorem. |
| `Sos.Certificate` | `Goal n`, `SOSDecomp`, `Certificate n`, `checks` predicate. |
| `Sos.Verifier` | `sos_sound`, `sos_strict_sound`, `sos_infeasible_sound`, plus `aeval_*` and `evalReal_eq_aeval` bridge lemmas. |
| `Sos.LDL` | Rational LDLᵀ, Lagrange 4-square, Gram→SOS reconstruction. |
| `Sos.Search` | Putinar-form SDP encoding, CSDP integration, rounding loop, ε-schedule for strict positivity. |
| `Sos.Reify` | Lean-`Expr` walker → `ParsedGoal` (typed AST + abstracted-over-`x` original Expr per polynomial). |
| `Sos.Tactic` | `by sos` (search-driven) and `by sos_witness <cert>` elaborators. |
| `Sos.Examples` | Worked examples invoking the tactic. |
| `Sos.Smoke` | Programmatic smoke test built as the `sos-example` lean_exe. |

## Dependencies

| Package | Purpose |
|---|---|
| [`leanprover-community/mathlib4`](https://github.com/leanprover-community/mathlib4) | `IsSumSq.nonneg`, `ℝ`, `algebraMap ℚ ℝ`, `ring`, `push_cast`. |
| [`Verified-zkEVM/CompPoly`](https://github.com/Verified-zkEVM/CompPoly) | Computational `CMvPolynomial n R` substrate; sorry/axiom-free. |
| [`kim-em/lean-csdp`](https://github.com/kim-em/lean-csdp) | FFI wrapper around CSDP 6.2.0. Vendored CSDP source. |

System dependencies (BLAS/LAPACK, transitively via lean-csdp):

| Platform | Packages |
|----------|---|
| Linux    | `liblapack-dev libblas-dev gfortran` |
| macOS    | Apple Command Line Tools (Accelerate framework) |
| Windows  | MSYS2 mingw-w64 with `mingw-w64-x86_64-openblas` |

CI runs Linux-only.

## Out of scope (intentionally)

- Univariate polynomial inequalities — already complete via root
  isolation in real-closed-field decision procedures (e.g.
  `hex-rcf` once it exists).
- Schmüdgen form (`2ᵐ` SOS multipliers per subset of constraints).
  Putinar handles every practical bounded constraint set.
- Counter-example generation. SOS only emits "yes" answers; `by sos`
  falls through silently on out-of-fragment goals.

## Licence

Apache License 2.0 (see [LICENSE](LICENSE)). Transitively, CSDP is
distributed under the
[Eclipse Public License 1.0](https://github.com/coin-or/Csdp/blob/master/LICENSE).

## References

- John Harrison, "Verifying Nonlinear Real Formulas Via Sums of Squares" (TPHOLs 2007).
- Pablo Parrilo, *Structured Semidefinite Programs and Semialgebraic Geometry* (Caltech PhD, 2000).
- Helena Peyrl & Pablo Parrilo, "Computing sum of squares decompositions with rational coefficients" (Theor. Comput. Sci. 2008).
- Brian Borchers, [CSDP](https://github.com/coin-or/Csdp).
- [Coq Micromega `psatz`](https://coq.inria.fr/refman/addendum/micromega.html) — design template.
