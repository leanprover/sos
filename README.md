# sos

Harrison's sum-of-squares decision procedure for nonlinear real
arithmetic, in Lean 4. Based on the design from
[Harrison 2007 (TPHOLs)](https://link.springer.com/chapter/10.1007/978-3-540-74591-4_9).

## What it does

Given a goal of one of the forms

```
∀ x : Fin n → ℝ, (g₁ x ≥ 0) → … → (gₘ x ≥ 0) → p x ≥ 0
∀ x : Fin n → ℝ, (g₁ x ≥ 0) → … → (gₘ x ≥ 0) → p x > 0
∀ x : Fin n → ℝ, (g₁ x ≥ 0) → … → (gₘ x ≥ 0) → False
```

with `p` and `gᵢ` polynomial in the bound variables and rational
coefficients, the `sos` tactic searches for a Positivstellensatz
certificate via [CSDP](https://github.com/coin-or/Csdp) and verifies it
inside Lean.

```lean
import Sos

example : ∀ x : Fin 2 → ℝ, 0 ≤ (x 0)^2 + 2*(x 0)*(x 1) + (x 1)^2 := by sos
example : ∀ x : Fin 1 → ℝ, 0 < (x 0)^2 + 1 := by sos
```

## How it works

External CSDP solver returns a floating-point Gram matrix. A
denominator-schedule rounder produces a candidate rational matrix,
then rational LDLᵀ decomposition (with Lagrange 4-square decomposition
of the diagonal entries) reconstructs explicit polynomial squares
`σ₀ = Σⱼ qⱼ²` and `σᵢ = Σⱼ qᵢⱼ²` such that `p = σ₀ + Σᵢ σᵢ · gᵢ`.
Polynomial equality is verified by `cbv_decide` against the
[CompPoly](https://github.com/Verified-zkEVM/CompPoly) computational
substrate. Soundness reduces to `Mathlib.IsSumSq.nonneg` plus
algebraic-map preservation under `ℚ → ℝ`.

`sos` is incomplete on principle (e.g. doesn't close the Motzkin
polynomial, which is non-negative but not SOS); failures fall through
without producing wrong proofs.

## Status

Early. v0.1 is an in-progress Lean-side implementation atop
`Verified-zkEVM/CompPoly` and `kim-em/lean-csdp`. See `PLAN.md` for
the full design and implementation roadmap.

## Out of scope (for v1)

- Strict hypotheses (`g > 0`).
- Non-`Fin n → ℝ` quantification.
- Non-rational atoms (`Real.sqrt 2`, etc.).
- Goals using Mathlib `Polynomial` (the polynomial substrate is
  CompPoly's `CMvPolynomial`).
- Preprocessing of `1/x`-style rational-function goals.

## Dependencies

System libraries needed at build time (CSDP requires BLAS/LAPACK):

| Platform | Packages |
|----------|---|
| Linux    | `liblapack-dev libblas-dev gfortran` |
| macOS    | Apple Command Line Tools (Accelerate framework) |
| Windows  | MSYS2 mingw-w64 with `mingw-w64-x86_64-openblas` |

## Licence

Apache License 2.0. CSDP is bundled (via `kim-em/lean-csdp`) under the
[Eclipse Public License 1.0](https://github.com/coin-or/Csdp/blob/master/LICENSE).
