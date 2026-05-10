/-
Speed-test candidate set. Build target is wall-clock < 10s for the
whole file on the kim-em/sos main toolchain.
-/
import SOS

open SOS CPoly

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
