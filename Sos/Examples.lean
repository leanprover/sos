/-
Worked examples for the Sos library, exercising both `by sos`
(search-driven) and `by sos_witness <cert>` (hand-built certificate)
across closed positivity, strict positivity, and infeasibility.

For closed positivity over multivariate / rank-deficient targets
where CSDP's interior-point step does not converge, the worked
example uses a hand-built certificate via `sos_witness`. The
underlying machinery is the same; only the search front-end is
unable to find the witness in those cases.
-/
import Sos

open Sos CPoly

/-! ### Search-driven `by sos`

Each of the following goals closes via `by sos`. The search calls
CSDP, rounds the float Gram matrix to rationals, and dispatches the
right verifier soundness lemma based on the parsed goal shape. -/

example : ∀ x : Fin 1 → ℝ, 0 ≤ (x 0)^2 + 1 := by sos
example : ∀ x : Fin 1 → ℝ, ¬ ((x 0)^2 + 1 ≤ 0) := by sos
example : ∀ x : Fin 1 → ℝ, 0 < (x 0)^2 + 1 := by sos

/-! ### Hand-built `sos_witness`

Multivariate cases whose Putinar certificate has a rank-deficient
Gram matrix (the unique SOS decomposition lives on the boundary of
the PSD cone) trip CSDP's interior-point line search. The proof
itself is identical — `sos_witness` consumes the certificate and
asks the verifier to validate it. -/

/-- `(x 0 + x 1)² = (x 0)² + 2·x 0·x 1 + (x 1)²`. -/
def handCert_perfect_square : Certificate 2 :=
  { sigma0 := { squares := [CMvPolynomial.X 0 + CMvPolynomial.X 1] },
    sigmas := [] }

example : ∀ x : Fin 2 → ℝ, 0 ≤ (x 0)^2 + 2*(x 0)*(x 1) + (x 1)^2 := by
  sos_witness handCert_perfect_square

/-- `(x 0 - 1/2)² = (x 0)² - x 0 + 1/4`. The constraint `0 ≤ x 0` is
unused. -/
def handCert_constrained : Certificate 1 :=
  { sigma0 := { squares := [CMvPolynomial.X 0 - CMvPolynomial.C (1/2)] },
    sigmas := [{ squares := [] }] }

example : ∀ x : Fin 1 → ℝ, 0 ≤ x 0 → 0 ≤ (x 0)^2 - x 0 + 1/4 := by
  sos_witness handCert_constrained

/-! ### Motzkin fall-through

The Motzkin polynomial `x⁴y² + x²y⁴ + 1 - 3x²y²` is non-negative
over `ℝ²` but not a sum of squares (Hilbert's third theorem).
`by sos` should fail to find a certificate; `fail_if_success`
turns that failure into a successfully-closed `True`. -/

example : True := by
  fail_if_success
    (have : ∀ x : Fin 2 → ℝ,
        0 ≤ (x 0)^4 * (x 1)^2 + (x 0)^2 * (x 1)^4 + 1
            - 3*(x 0)^2*(x 1)^2 := by sos)
  trivial
