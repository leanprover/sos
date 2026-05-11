/-
Speed-test candidate set. Build target is wall-clock < 10s for the
whole file on the kim-em/sos main toolchain.
-/
import SOS

open SOS CPoly

/-! ### Pure invariant checks for search/round/reconstruct helpers -/

#guard (SOS.Search.monomialsUpTo 2 2).size = 6
#guard
  match (SOS.Search.monomialsUpTo 2 2)[1]? with
  | some m =>
    let a := CMvMonomial.degreeOf m ⟨0, by decide⟩
    let b := CMvMonomial.degreeOf m ⟨1, by decide⟩
    a = 1 ∧ b = 0
  | none => False

#guard
  match SOS.Search.decodeSdpBlock (1 : ℚ) 2 FloatArray.empty with
  | none => true
  | some _ => false

#guard
  match SOS.LDL.reconstruct 2 (#[] : Array ℚ)
      (#[] : Array (CMvPolynomial 1 ℚ)) with
  | none => true
  | some _ => false

-- 1. closed positivity, 1 var, deg 2
example (x : ℝ) : 0 ≤ x^2 + 1 := by sos

-- 2. closed positivity, 1 var, deg 4
example (x : ℝ) : 0 ≤ x^4 + 1 := by sos

-- 3. perfect square (rank-1 boundary)
example (x : ℝ) : 0 ≤ x^2 + 2*x + 1 := by sos

-- 4. perfect square, multivariate, sign-mixed
example (x y : ℝ) : 0 ≤ x^2 - 2*x*y + y^2 := by sos

-- 5. perfect square, multivariate
example (x y : ℝ) : 0 ≤ x^2 + 2*x*y + y^2 := by sos

-- 6. (x²-1)² as deg-4 single-var
example (x : ℝ) : 0 ≤ x^4 - 2*x^2 + 1 := by sos

-- 7. cyclic Schur, 3 vars
example (a b c : ℝ) :
    0 ≤ a^2 + b^2 + c^2 - a*b - b*c - a*c := by sos

-- 8. AM ≥ GM squared, 2 vars deg 4
example (x y : ℝ) : 0 ≤ (x^2 + y^2)^2 - 4*x^2*y^2 := by sos

-- 9. strict positivity, 1 var deg 2
example (x : ℝ) : 0 < x^2 + 1 := by sos

-- 10. strict positivity, 1 var deg 4
example (x : ℝ) : 0 < x^4 + 1 := by sos

-- 11. strict positivity, 2 vars deg 2
example (x y : ℝ) : 0 < x^2 + y^2 + 1 := by sos

-- 12. infeasibility, 1 var deg 2
example (x : ℝ) : ¬ (x^2 + 1 ≤ 0) := by sos

-- 13. infeasibility, 1 var deg 4
example (x : ℝ) : ¬ (x^4 + 1 ≤ 0) := by sos

-- 14. constrained, cubic
example (x : ℝ) (_h : 0 ≤ x) : 0 ≤ x^3 + x := by sos

-- 15. constrained, perfect-square modulo
example (x : ℝ) (_h : 0 ≤ x) : 0 ≤ x^2 - x + 1/4 := by sos

-- 16. constrained, multivariate
example (x y : ℝ) (_hx : 0 ≤ x) (_hy : 0 ≤ y) :
    0 ≤ x^2 + 2*x*y + y^2 := by sos

-- 17. Cauchy–Schwarz: (a²+b²)(c²+d²) − (ac+bd)² ≥ 0  (rank 1, deg 4, 4 vars)
example (a b c d : ℝ) :
    0 ≤ (a^2 + b^2) * (c^2 + d^2) - (a*c + b*d)^2 := by sos

-- 18b. Strict-inequality constraint hypothesis. Promoted to `0 ≤`
-- in the elaborator via `le_of_lt`.
example (x : ℝ) (_h : 0 < x) : 0 ≤ x^3 + x := by sos

-- 18. Motzkin fall-through (NOT SOS)
example : True := by
  fail_if_success
    (have : ∀ x y : ℝ, 0 ≤ x^4*y^2 + x^2*y^4 + 1 - 3*x^2*y^2 := by sos)
  trivial

/-! ### Strict positivity with tight or unfriendly bounds

LP-slack discovers `λ*` and descends through `ε = 2^-k` from there.
Including `polyDenom target` in the rounding schedule lets residuals
with non-power-of-two denominators land on the natural rational grid,
and `decide +kernel` verifies the certificate. -/

-- 19. non-power-of-two denominator (the residual ends up at denom 3200
-- after ε = 1/128 against `1/100`, requiring polyDenom-aware rounding).
example (x : ℝ) : 0 < x^2 + 1/100 := by sos

-- 20. multivariate, non-power-of-two denominator
example (x y : ℝ) : 0 < x^2 + y^2 + 1/500 := by sos

-- 21. tight strict positivity at the four-squares cap. `fourSquaresNat`
-- caps at `n ≤ 2^20`, which puts a floor of `ε ≥ 1/(2^20)` on what we
-- can certify by this pipeline.
example (x : ℝ) : 0 < x^2 + 1/1048576 := by sos

-- 22. infimum-0 strict positivity must fail gracefully.
-- p = (x*y − 1)² + x² is strictly positive everywhere on ℝ² (would need
-- x*y = 1 and x = 0 simultaneously) but its infimum is 0 along x → 0,
-- y = 1/x. No positive ε admits a Putinar certificate.
example : True := by
  fail_if_success
    (have : ∀ x y : ℝ, 0 < (x*y - 1)^2 + x^2 := by sos)
  trivial

/-! ### `sos?` produces a `Try this:` suggestion of `sos_witness …` -/

/--
info: Try this:
  [apply] sos_witness { sigma0 := { squares := [CMvPolynomial.C (1 : ℚ), CMvPolynomial.X 0] }, sigmas := [] }
-/
#guard_msgs in
example (x : ℝ) : 0 ≤ x^2 + 1 := by sos?

-- And the suggested replacement compiles:
example (x : ℝ) : 0 ≤ x^2 + 1 := by
  sos_witness { sigma0 := { squares := [CMvPolynomial.C (1 : ℚ), CMvPolynomial.X 0] }, sigmas := [] }

/-! ### Strict positivity: `sos?` suggestion includes `with ε := …` -/

/--
info: Try this:
  [apply] sos_witness { sigma0 := { squares := [CMvPolynomial.X 0] }, sigmas := [] } with ε := (1 : ℚ)
-/
#guard_msgs in
example (x : ℝ) : 0 < x^2 + 1 := by sos?

-- And the suggested replacement compiles:
example (x : ℝ) : 0 < x^2 + 1 := by
  sos_witness { sigma0 := { squares := [CMvPolynomial.X 0] }, sigmas := [] } with ε := (1 : ℚ)

/-! ### Coverage: orphan code paths

The cases below exercise paths that aren't otherwise reached by the
search-driven examples above:

* `nonpos` constraint hypothesis (`h : x ≤ 0`), driving the
  `aeval_nonneg_of_orig_neg` bridge in `SOS/Verifier.lean`.
* `sos_witness` with a constraint — the existing `sos_witness` smoke-
  test above is unconstrained.
* `sos_witness` for an infeasibility goal (`¬ p ≤ 0`) — exercises
  the `.infeasible` arm of the witness elaborator. -/

-- nonpos hypothesis: search-driven path closes via the .neg-wrapping
-- in `recogniseConstraint` and the `aeval_nonneg_of_orig_neg` bridge.
example (x : ℝ) (_h : x ≤ 0) : 0 ≤ -x := by sos

-- sos_witness with a constraint. (The witness here is the trivial
-- σ₀ = x^2, σ₁ = 0 — `x^2 ≥ 0` doesn't need the `0 ≤ x` hypothesis,
-- but the cert structure must still carry a sigmas entry per
-- constraint to match `cert.checks`'s length check.)
example (x : ℝ) (_h : 0 ≤ x) : 0 ≤ x^2 := by
  sos_witness
    { sigma0 := { squares := [CMvPolynomial.X 0] },
      sigmas := [{ squares := [] }] }

-- sos_witness for infeasibility. `-1 = x^2 + 1·(-x^2 - 1)` proves
-- the constraint set `{x^2 + 1 ≤ 0}` is infeasible.
example (x : ℝ) : ¬ (x^2 + 1 ≤ 0) := by
  sos_witness
    { sigma0 := { squares := [CMvPolynomial.X 0] },
      sigmas := [{ squares := [CMvPolynomial.C (1 : ℚ)] }] }
