/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Unit tests for the exact-rational Phase-1 simplex (`SOS.RatSimplex`)
and the half-Newton-polytope membership predicate (`SOS.Search.isInHalfNewton`).
-/
import SOS

open SOS Search RatSimplex CPoly

/-! ### Phase-1 simplex feasibility -/

/-- Empty system is vacuously feasible. -/
example : isFeasibleEqLP #[] #[] = true := by native_decide

/-- `x + y = 1, x, y ≥ 0` is feasible. -/
example : isFeasibleEqLP #[#[1, 1]] #[(1 : ℚ)] = true := by native_decide

/-- `x = 1, x = 2` is infeasible. -/
example : isFeasibleEqLP #[#[1], #[1]] #[(1 : ℚ), 2] = false := by native_decide

/-- `x + y = 1, 2x + 2y = 2` (redundant) is feasible. -/
example :
    isFeasibleEqLP #[#[1, 1], #[2, 2]] #[(1 : ℚ), 2] = true := by native_decide

/-- `x + y = 1, 2x + 2y = 3` (inconsistent) is infeasible. -/
example :
    isFeasibleEqLP #[#[1, 1], #[2, 2]] #[(1 : ℚ), 3] = false := by native_decide

/-- `x − y = 0, x + y = 2` ⇒ `x = y = 1`. Feasible (negative b is
flipped during normalisation). -/
example :
    isFeasibleEqLP #[#[1, -1], #[1, 1]] #[(0 : ℚ), 2] = true := by native_decide

/-- Larger feasible LP: `x₀ + x₁ + x₂ = 1, x₀ + 2·x₁ + 4·x₂ = 2,
x₀ + 3·x₁ + 9·x₂ = 7/2`. Vandermonde-style; unique solution
`(1/2, 1/4, 1/4)`. -/
example :
    isFeasibleEqLP
      #[#[1, 1, 1], #[1, 2, 4], #[1, 3, 9]]
      #[(1 : ℚ), 2, 7/2] = true := by native_decide

/-- Degenerate: target on the boundary (`x + y = 0`, b = 0). Trivially
`x = y = 0`. -/
example : isFeasibleEqLP #[#[1, 1]] #[(0 : ℚ)] = true := by native_decide

/-- Mismatched row size returns `false`. -/
example : isFeasibleEqLP #[#[1, 1], #[1]] #[(1 : ℚ), 1] = false := by native_decide

/-- Beale-style degenerate tableau: same `b` across multiple rows
forces ratio ties in the first pivots. Bland's tie-break (smallest
basis index) keeps the rule cycle-free. Feasible by `(1, 0, 0, 0, 0)`. -/
example :
    isFeasibleEqLP
      #[#[1, 1, 1, 0, 0], #[1, 0, 0, 1, 0], #[1, 0, 0, 0, 1]]
      #[(1 : ℚ), 1, 1] = true := by native_decide

/-- A row that's a linear combination of the others, with inconsistent
RHS, is infeasible. -/
example :
    isFeasibleEqLP
      #[#[1, 1], #[1, 0], #[2, 1]]
      #[(1 : ℚ), 1, 3] = false := by native_decide

/-- All-zero `b` (homogeneous): `x = 0` always works. -/
example : isFeasibleEqLP #[#[3, -2], #[1, 4]] #[(0 : ℚ), 0] = true := by
  native_decide

/-- Equality with negative `b` is normalised away. `−x + y = 1` is
feasible at `(0, 1)`. -/
example :
    isFeasibleEqLP #[#[-1, 1]] #[(1 : ℚ)] = true := by native_decide

/-- `x + y = 2, x − y = 4 ⇒ x = 3, y = −1`. Infeasible under `λ ≥ 0`. -/
example :
    isFeasibleEqLP #[#[1, 1], #[1, -1]] #[(2 : ℚ), 4] = false := by
  native_decide

/-! ### Half-Newton-polytope membership

These are the three motivating examples from issue #23. -/

/-- `target = x⁴ + y⁴`, candidate `α = (1, 1)`: `2α = (2, 2)` is the
Newton midpoint of the segment from `(4, 0)` to `(0, 4)`. -/
example :
    isInHalfNewton
        ((CMvPolynomial.X 0 : CMvPolynomial 2 ℚ)^4 + (CMvPolynomial.X 1)^4)
        ⟨#[1, 1], rfl⟩ = true := by
  native_decide

/-- `target = x²` in 2 vars, candidate `α = (0, 0)`: `2α = (0, 0)` is
not in the singleton Newton polytope `{(2, 0)}`. Newton rejects. -/
example :
    isInHalfNewton ((CMvPolynomial.X 0 : CMvPolynomial 2 ℚ)^2)
        ⟨#[0, 0], rfl⟩ = false := by
  native_decide

/-- `target = x⁴ + x²y² + y⁴`, `α = (1, 1)`: `2α = (2, 2)` is itself a
support exponent, so trivially in Newton. -/
example :
    isInHalfNewton
        ((CMvPolynomial.X 0 : CMvPolynomial 2 ℚ)^4 +
         (CMvPolynomial.X 0)^2 * (CMvPolynomial.X 1)^2 +
         (CMvPolynomial.X 1)^4)
        ⟨#[1, 1], rfl⟩ = true := by
  native_decide

/-! ### Newton basis is a strict subset of dense for sparse targets

Demonstrates that on at least one target Newton actually shrinks the
basis from `monomialsUpTo`, which is the only thing that justifies
the LP cost. -/

/-- `target = x⁴ + y⁴` at basis degree 2: dense basis has 6 monomials
`{1, x, x², y, xy, y²}`; Newton admits only those `m` with
`2·exp(m) ∈ ConvexHull{(4,0), (0,4)}`, i.e. on or below the segment.
Inspection: only `(1, 1)`, `(2, 0)`, `(0, 2)` qualify. -/
example :
    (newtonBasis
        ((CMvPolynomial.X 0 : CMvPolynomial 2 ℚ)^4 +
         (CMvPolynomial.X 1)^4) 2).size = 3 := by
  native_decide
