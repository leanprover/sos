# sos

[![CI](https://github.com/kim-em/sos/actions/workflows/ci.yml/badge.svg)](https://github.com/kim-em/sos/actions/workflows/ci.yml)

Harrison's sum-of-squares decision procedure for nonlinear real
arithmetic, in Lean 4. Based on the design from
[Harrison 2007 (TPHOLs)](https://link.springer.com/chapter/10.1007/978-3-540-74591-4_9).

## Status — v0.1

**Verifier core (complete, no holes):**

- `Sos.sos_sound`: a validated SOS certificate proves `p ≥ 0` over a
  Putinar-form constraint set.
- `Sos.sos_strict_sound`, `Sos.sos_infeasible_sound`: analogues for
  `p > 0` and infeasibility refutation.
- Soundness factors through `IsSumSq.nonneg` (Mathlib) plus the
  `aeval` ring-hom structure on CompPoly's `CMvPolynomial n ℚ`.

**Search engine (end-to-end working):**

- `Sos.Search.runSearch goal gs : IO (Option (Certificate n))` builds
  a Putinar-form SDP from `(goal, gs)`, invokes
  [CSDP](https://github.com/coin-or/Csdp) via
  [`kim-em/lean-csdp`](https://github.com/kim-em/lean-csdp), rounds
  the float Gram matrices over a denominator schedule, reconstructs
  explicit polynomial squares via rational LDLᵀ and Lagrange
  four-square decomposition, and checks the resulting `Certificate`
  exactly via `Lawful.instDecidableEq` polynomial equality.
- v0.1 supports closed positivity (`Goal.closed p`) and infeasibility
  (`Goal.infeasible`). Strict positivity (`Goal.strict p ε hε`) is
  scaffolded but the SDP slack-maximisation encoding is deferred to
  v0.2.

**User-facing tactic surface (deferred to v0.2):**

- `by sos` and `by sos_witness <cert>` are declared at the syntax
  level but their elaborators raise an explanatory error in v0.1.
- v0.2 will add a `Lean.ToExpr (Certificate n)` instance plus the
  `simp`-driven goal rewrite needed to bridge from `0 ≤ <expr>` to
  `0 ≤ aeval x p_reified`.

For now, users can apply `Sos.sos_sound` (or its strict /
infeasibility variants) directly with a hand-constructed
`Certificate`, or invoke `Sos.Search.runSearch` programmatically (as
in `Sos/Examples.lean`).

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

This demonstrates the full pipeline: SDP encoding from a CompPoly
polynomial, CSDP invocation, rational rounding, LDL reconstruction,
and certificate validation.

## Architecture

```
goal expression  ── Sos.Reify.parseGoal ──▶  (Sos.Goal n, gs : List (CMvPolynomial n ℚ))
                                                       │
                                                       ▼
                                               Sos.Search.runSearch
                                                       │
                                                       │   builds SDP, calls CSDP,
                                                       │   rounds rationals, runs LDL,
                                                       │   verifies certificate
                                                       │
                                                       ▼
                                              Sos.Certificate n  (validated)
                                                       │
                                                       ▼
                                          Sos.sos_sound / sos_strict_sound /
                                              sos_infeasible_sound
                                                       │
                                                       ▼
                                                ℝ-level proof
```

| Module | What it provides |
|---|---|
| `Sos.Atoms` | Atom-table type for the reifier. |
| `Sos.Raw` | `Poly.Raw` and typed `Poly n` ASTs + reflection theorem. |
| `Sos.Certificate` | `Goal n`, `SOSDecomp`, `Certificate n`, `checks` predicate via `Lawful.instDecidableEq`. |
| `Sos.Verifier` | `sos_sound`, `sos_strict_sound`, `sos_infeasible_sound` (proved). |
| `Sos.LDL` | Rational LDLᵀ, Lagrange 4-square, Gram→SOS reconstruction. |
| `Sos.Search` | Putinar-form SDP encoding, CSDP integration, rounding loop. |
| `Sos.Reify` | Lean-`Expr` walker → `(Goal n, gs)`. |
| `Sos.Tactic` | `sos` / `sos_witness` syntax (v0.1 stubs). |
| `Sos.Examples` | Worked smoke test invoking the full pipeline. |

## Dependencies

| Package | Purpose |
|---|---|
| [`leanprover-community/mathlib4`](https://github.com/leanprover-community/mathlib4) | `IsSumSq.nonneg`, `ℝ`, `algebraMap ℚ ℝ`. |
| [`Verified-zkEVM/CompPoly`](https://github.com/Verified-zkEVM/CompPoly) | Computational `CMvPolynomial n R` substrate; sorry/axiom-free. |
| [`kim-em/lean-csdp`](https://github.com/kim-em/lean-csdp) | FFI wrapper around CSDP 6.2.0. Vendored CSDP source. |

System dependencies (BLAS/LAPACK, transitively via lean-csdp):

| Platform | Packages |
|----------|---|
| Linux    | `liblapack-dev libblas-dev gfortran` |
| macOS    | Apple Command Line Tools (Accelerate framework) |
| Windows  | MSYS2 mingw-w64 with `mingw-w64-x86_64-openblas` |

CI runs Linux-only for v0.1. macOS / Windows are deferred to v0.2.

## Roadmap to v0.2

In order of priority:

1. `Lean.ToExpr (Certificate n)` instance + `by sos` / `by sos_witness <cert>` elaborators.
2. Strict-positivity SDP encoding (LP-slack-maximisation block).
3. macOS + Windows CI (mirror lean-csdp's per-platform setup).
4. Richer goal language: `1/x`-style preprocessing, Mathlib `Polynomial`-typed goals.

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
