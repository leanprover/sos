/-
Speed-test candidate set. Build target is wall-clock < 10s for the
whole file on the kim-em/sos main toolchain.
-/
import Sos

open Sos CPoly

-- 1. closed positivity, 1 var, deg 2 (smoke)
example : ∀ x : Fin 1 → ℝ, 0 ≤ (x 0)^2 + 1 := by sos

-- 2. closed positivity, 1 var, deg 4
example : ∀ x : Fin 1 → ℝ, 0 ≤ (x 0)^4 + 1 := by sos

-- 3. perfect square (rank-1 boundary)
example : ∀ x : Fin 1 → ℝ, 0 ≤ (x 0)^2 + 2*(x 0) + 1 := by sos

-- 4. perfect square, multivariate, sign-mixed
example : ∀ x : Fin 2 → ℝ, 0 ≤ (x 0)^2 - 2*(x 0)*(x 1) + (x 1)^2 := by sos

-- 5. perfect square, multivariate
example : ∀ x : Fin 2 → ℝ, 0 ≤ (x 0)^2 + 2*(x 0)*(x 1) + (x 1)^2 := by sos

-- 6. (x²-1)² as deg-4 single-var
example : ∀ x : Fin 1 → ℝ, 0 ≤ (x 0)^4 - 2*(x 0)^2 + 1 := by sos

-- 7. cyclic Schur, 3 vars
example : ∀ x : Fin 3 → ℝ,
    0 ≤ (x 0)^2 + (x 1)^2 + (x 2)^2 - (x 0)*(x 1) - (x 1)*(x 2) - (x 0)*(x 2) := by sos

-- 8. AM ≥ GM squared, 2 vars deg 4
example : ∀ x : Fin 2 → ℝ, 0 ≤ ((x 0)^2 + (x 1)^2)^2 - 4*(x 0)^2*(x 1)^2 := by sos

-- 9. strict positivity, 1 var deg 2
example : ∀ x : Fin 1 → ℝ, 0 < (x 0)^2 + 1 := by sos

-- 10. strict positivity, 1 var deg 4
example : ∀ x : Fin 1 → ℝ, 0 < (x 0)^4 + 1 := by sos

-- 11. strict positivity, 2 vars deg 2
example : ∀ x : Fin 2 → ℝ, 0 < (x 0)^2 + (x 1)^2 + 1 := by sos

-- 12. infeasibility, 1 var deg 2
example : ∀ x : Fin 1 → ℝ, ¬ ((x 0)^2 + 1 ≤ 0) := by sos

-- 13. infeasibility, 1 var deg 4
example : ∀ x : Fin 1 → ℝ, ¬ ((x 0)^4 + 1 ≤ 0) := by sos

-- 14. constrained, cubic
example : ∀ x : Fin 1 → ℝ, 0 ≤ x 0 → 0 ≤ (x 0)^3 + (x 0) := by sos

-- 15. constrained, perfect-square modulo
example : ∀ x : Fin 1 → ℝ, 0 ≤ x 0 → 0 ≤ (x 0)^2 - x 0 + 1/4 := by sos

-- 16. constrained, multivariate
example : ∀ x : Fin 2 → ℝ, 0 ≤ x 0 → 0 ≤ x 1 →
    0 ≤ (x 0)^2 + 2*(x 0)*(x 1) + (x 1)^2 := by sos

-- 17. Cauchy–Schwarz: (a²+b²)(c²+d²) − (ac+bd)² ≥ 0  (rank 1, deg 4, 4 vars)
example : ∀ x : Fin 4 → ℝ,
    0 ≤ ((x 0)^2 + (x 1)^2) * ((x 2)^2 + (x 3)^2)
        - ((x 0)*(x 2) + (x 1)*(x 3))^2 := by sos

-- 18. Motzkin fall-through (NOT SOS)
example : True := by
  fail_if_success
    (have : ∀ x : Fin 2 → ℝ,
        0 ≤ (x 0)^4*(x 1)^2 + (x 0)^2*(x 1)^4 + 1 - 3*(x 0)^2*(x 1)^2 := by sos)
  trivial

/-! ### `sos?` produces a `Try this:` suggestion of `sos_witness …` -/

/--
info: Try this:
  [apply] sos_witness { sigma0 := { squares := [CMvPolynomial.C (1 : ℚ), CMvPolynomial.X 0] }, sigmas := [] }
---
error: sos?: see Try this suggestion
-/
#guard_msgs in
example : ∀ x : Fin 1 → ℝ, 0 ≤ (x 0)^2 + 1 := by sos?

-- And the suggested replacement compiles:
example : ∀ x : Fin 1 → ℝ, 0 ≤ (x 0)^2 + 1 := by
  sos_witness { sigma0 := { squares := [CMvPolynomial.C (1 : ℚ), CMvPolynomial.X 0] }, sigmas := [] }
