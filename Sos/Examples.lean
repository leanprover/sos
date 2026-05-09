/-
Worked examples for the Sos library. Each end-state goal closes
via `by sos` (search-driven): the elaborator parses the goal, calls
CSDP via `Sos.Search.runSearch`, rounds the float Gram matrix to
rationals via the LDLᵀ + Lagrange four-square pipeline, and
dispatches the matching verifier soundness lemma. `by sos_witness
<cert>` is also available for cases where the user wants to supply
a hand-built certificate directly.
-/
import Sos

open Sos CPoly

/-! ### `by sos`: closed positivity, strict positivity, infeasibility,
multivariate, and constrained. -/

example : ∀ x : Fin 1 → ℝ, 0 ≤ (x 0)^2 + 1 := by sos
example : ∀ x : Fin 2 → ℝ, 0 ≤ (x 0)^2 + 2*(x 0)*(x 1) + (x 1)^2 := by sos
example : ∀ x : Fin 1 → ℝ, 0 < (x 0)^2 + 1 := by sos
example : ∀ x : Fin 1 → ℝ, ¬ ((x 0)^2 + 1 ≤ 0) := by sos
example : ∀ x : Fin 1 → ℝ, 0 ≤ x 0 → 0 ≤ (x 0)^2 - x 0 + 1/4 := by sos

/-! ### Motzkin fall-through

The Motzkin polynomial `x⁴y² + x²y⁴ + 1 - 3x²y²` is non-negative
over `ℝ²` but not a sum of squares (Hilbert 1888 / Motzkin 1967).
`by sos` correctly fails to find a certificate; `fail_if_success`
catches the failure so we close the outer `True`. -/

example : True := by
  fail_if_success
    (have : ∀ x : Fin 2 → ℝ,
        0 ≤ (x 0)^4 * (x 1)^2 + (x 0)^2 * (x 1)^4 + 1
            - 3*(x 0)^2*(x 1)^2 := by sos)
  trivial

/-! ### `by sos_witness` is still available for direct cert supply. -/

/-- The cert search produces this on its own; included as a sanity
example of the witness path. -/
def handCert_x2_plus_1 : Certificate 1 :=
  { sigma0 := { squares := [CMvPolynomial.X 0, CMvPolynomial.C 1] },
    sigmas := [] }

example : ∀ x : Fin 1 → ℝ, 0 ≤ (x 0)^2 + 1 := by
  sos_witness handCert_x2_plus_1
