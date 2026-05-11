# sos

[![CI](https://github.com/kim-em/sos/actions/workflows/ci.yml/badge.svg)](https://github.com/kim-em/sos/actions/workflows/ci.yml)

Harrison's sum-of-squares decision procedure for nonlinear real
arithmetic, in Lean 4. Based on the design from
[Harrison 2007 (TPHOLs)](https://link.springer.com/chapter/10.1007/978-3-540-74591-4_9).

This tactic depends on
[`Verified-zkEVM/CompPoly`](https://github.com/Verified-zkEVM/CompPoly)
for a kernel-decidable computational multivariate-polynomial type
(`CMvPolynomial n ℚ`), which is what the verifier reduces certificate
checks against. CompPoly itself depends on Mathlib. As a consequence,
`sos` is a downstream library and cannot be migrated into Mathlib
itself unless CompPoly is upstreamed first.

## Status

The `by sos` tactic closes nonlinear-real-arithmetic goals end-to-end:
reify the goal, encode an SDP, call CSDP, round the float Gram matrix
to rationals, decompose via LDLᵀ + Lagrange four-square, and dispatch
the matching verifier-soundness lemma. A representative sample from
[`SOSTest/Examples.lean`](SOSTest/Examples.lean):

```lean
import SOS

-- Cauchy–Schwarz (rank 1, deg 4, 4 vars)
example (a b c d : ℝ) :
    0 ≤ (a^2 + b^2) * (c^2 + d^2) - (a*c + b*d)^2 := by sos

-- Cyclic Schur, 3 vars
example (a b c : ℝ) : 0 ≤ a^2 + b^2 + c^2 - a*b - b*c - a*c := by sos

-- AM ≥ GM squared
example (x y : ℝ) : 0 ≤ (x^2 + y^2)^2 - 4*x^2*y^2 := by sos

-- Strict positivity, multivariate
example (x y : ℝ) : 0 < x^2 + y^2 + 1 := by sos

-- Infeasibility
example (x : ℝ) : ¬ (x^4 + 1 ≤ 0) := by sos

-- Constrained
example (x : ℝ) (_h : 0 ≤ x) : 0 ≤ x^3 + x := by sos
example (x y : ℝ) (_hx : 0 ≤ x) (_hy : 0 ≤ y) :
    0 ≤ x^2 + 2*x*y + y^2 := by sos

-- Strict-inequality hypothesis (promoted to `0 ≤ x` via `le_of_lt`)
example (x : ℝ) (_h : 0 < x) : 0 ≤ x^3 + x := by sos
```

`by sos?` reports the witness it found as a `Try this:` suggestion
that you can paste back as a `sos_witness …` invocation, freezing the
proof so it no longer depends on calling CSDP at compile time:

```lean
example (x : ℝ) : 0 ≤ x^2 + 1 := by sos?
-- Try this:
--   [apply] sos_witness
--     { sigma0 := { squares := [CMvPolynomial.C (1 : ℚ), CMvPolynomial.X 0] }, sigmas := [] }
```

Atoms are recovered as arbitrary `ℝ`-typed subterms (free variables,
function applications, projections — anything the reifier doesn't
recognise as a known operator). Constraint hypotheses can come from
the local context or from `→`-introduced binders.

The Motzkin polynomial `x⁴y² + x²y⁴ + 1 - 3x²y²` is non-negative but
not a sum of squares (Hilbert 1888 / Motzkin 1967); `by sos`
correctly fails to find a certificate, caught here by
`fail_if_success`:

```lean
example : True := by
  fail_if_success
    (have : ∀ x y : ℝ,
        0 ≤ x^4 * y^2 + x^2 * y^4 + 1 - 3*x^2*y^2 := by sos)
  trivial
```

The soundness lemmas reduce to `IsSumSq.nonneg` (Mathlib) once the
goal has been transported through the `aeval` ring-hom on CompPoly's
`CMvPolynomial n ℚ`. Two design points worth flagging, both following
Harrison's [TPHOLs 2007 paper]
(https://link.springer.com/chapter/10.1007/978-3-540-74591-4_9):

- **`min tr(X)` cost matrix.** CSDP's interior-point step has no
  preferred direction on a singleton boundary feasible set, so we
  give it the trace objective Harrison reports works empirically.
- **Zero-pivot LDLᵀ.** Rank-deficient SOS Grams (`(x + y)²` has
  Gram `[[1,1],[1,1]]`, rank 1) require the "completing the square"
  routine to accept a zero pivot when the residual column is also
  zero. Our `SOS.LDL.decompose` does this; `LDL.reconstruct` already
  drops the zero-D contributions.

## Scope and limits

- **Rational certificates only.** Witnesses live in
  `CMvPolynomial n ℚ` throughout. CSDP returns floats, which we round
  against a denominator schedule (small ints, then powers of two up to
  `2^20`) and decompose via rational LDLᵀ + Lagrange four-square.
  There is no support for algebraic-extension coefficients — a goal
  whose only SOS witness involves `√2` (or any other irrational) is
  out of reach by construction.

- **Putinar form, with hypotheses as multipliers.** A certificate is
  `target = σ₀ + Σᵢ σᵢ · gᵢ` with each `σᵢ` an SOS, where the `gᵢ`
  are non-negativity hypotheses pulled from `intro`-binders and the
  local context. Recognised constraint shapes are `0 ≤ g`, `g ≤ 0`
  (encoded as `0 ≤ −g`), and `0 < g` (used via `le_of_lt`).
  Unconstrained goals reduce to `target = σ₀`. Strict positivity
  `0 < p` is handled by an LP-slack maximisation: one extra
  decision variable `λ ≥ 0` enters the SDP via the constant-monomial
  equality, CSDP maximises it to discover the largest admissible
  slack `λ*`, and then `ε = 2^-k` near `λ*` is fed to the standard
  feasibility pipeline to produce the verifiable certificate.
  Infeasibility uses `target = −1`.

- **Single fixed relaxation level.** Multiplier basis sizes are set
  once from a degree bound `D = max(deg(target), maxᵢ deg(gᵢ))`: the
  σ₀ basis is monomials up to `⌈D/2⌉`, and each σᵢ basis is monomials
  up to `⌈max(0, D − deg(gᵢ))/2⌉`. There is no hierarchy walk that
  bumps the relaxation order on failure. Failures cover both
  genuinely non-SOS non-negative polynomials (Motzkin
  `x⁴y² + x²y⁴ + 1 − 3x²y²` is the canonical example) and goals that
  would only succeed at a larger relaxation order than this fixed
  search uses.

- **Search failure is not a soundness failure.** When CSDP returns an
  unusable status, when no rounding denominator validates, or when
  LDLᵀ / four-square reconstruction can't close the certificate,
  `by sos` reports "no certificate found" and leaves the goal open.
  The `Certificate.checks` predicate that closes the goal is
  `cbv_decide`-checked against `Certificate n` data, so a proof that
  goes through is independent of CSDP correctness.

## Building and testing

```
git clone https://github.com/kim-em/sos
cd sos
lake exe cache get
lake test
```

`lake test` elaborates `SOSTest`, which runs `by sos` against every
example in [`SOSTest/Examples.lean`](SOSTest/Examples.lean) — each
invocation calls CSDP, rounds the Gram matrix, reconstructs the
certificate, and checks it. A passing `lake test` is end-to-end
verification of the search/round/reconstruct/verify pipeline.

## Architecture

The tactic runs three stages on a `by sos` goal:

1. `SOS.Reify.parseGoalAtomic` walks the goal expression, collecting
   atomic ℝ-typed subterms into an array and producing untyped
   `SOS.Poly.Raw` ASTs for the conclusion and each constraint
   hypothesis (drawn from `intro`-binders and the local context).
2. `SOS.Search.runSearch` builds the Putinar-form SDP, calls CSDP,
   rounds the float Gram matrix to rationals, runs LDLᵀ, and
   reconstructs squares — yielding a validated `SOS.Certificate n`.
3. `SOS.Tactic.closeSos` consumes the certificate and discharges the
   real-arithmetic goal via the matching soundness lemma in
   `SOS.Verifier`.

| Module | What it provides |
|---|---|
| `SOS.Raw` | `Poly.Raw` and typed `Poly n` ASTs + reflection theorem. |
| `SOS.Certificate` | `Goal n`, `SOSDecomp`, `Certificate n`, `checks` predicate. |
| `SOS.Verifier` | `sos_sound`, `sos_strict_sound`, `sos_infeasible_sound`, plus `aeval_*` and `evalReal_eq_aeval` bridge lemmas. |
| `SOS.LDL` | Rational LDLᵀ, Lagrange 4-square, Gram→SOS reconstruction. |
| `SOS.Search` | Putinar-form SDP encoding, CSDP integration, rounding loop, ε-schedule for strict positivity. |
| `SOS.Reify` | Atom-collecting Lean-`Expr` walker → `ParsedGoal` (atom array, untyped `SOS.Poly.Raw` for conclusion + constraints, hypothesis FVars). |
| `SOS.Tactic` | `by sos` (search-driven) and `by sos_witness <cert>` elaborators. |
| `SOSTest.Examples` | Worked examples invoking the tactic; serves as the `lake test` driver. |

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
