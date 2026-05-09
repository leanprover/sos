/-
Worked examples and smoke tests for the Sos library.

The verifier core (`Sos.sos_sound`, `sos_strict_sound`,
`sos_infeasible_sound`) is fully operational. The search engine
(`Sos.Search.runSearch`) is end-to-end working. The user-facing
`sos` tactic is v0.2 work — for v0.1 these are programmatic
demonstrations showing the architecture from goal to verified
certificate.
-/
import Sos

open Sos CPoly

/-! ### Smoke test: `(x 0)² + 1 ≥ 0` -/

/-- Polynomial `(x 0)² + 1` in 1 variable over ℚ. -/
def smokeTarget : CMvPolynomial 1 ℚ :=
  let x0 : CMvPolynomial 1 ℚ := CMvPolynomial.X 0
  x0 * x0 + CMvPolynomial.C 1

/-- The corresponding goal in `Sos.Goal` form. -/
def smokeGoal : Goal 1 := Goal.closed smokeTarget

def runSmoke : IO Unit := do
  IO.println "=== sos: smoke test for (x 0)² + 1 ≥ 0 ==="
  IO.println s!"target totalDegree: {smokeTarget.totalDegree}"
  match (← Sos.Search.runSearch smokeGoal []) with
  | some cert =>
    IO.println s!"✓ runSearch produced cert with \
      {cert.sigma0.squares.length} σ₀-squares, \
      {cert.sigmas.length} σᵢ blocks."
    IO.println s!"✓ cert.checks smokeGoal [] = {cert.checks smokeGoal []}"
  | none =>
    IO.println "✗ no cert found"

/-! ### Soundness statement (manually applied)

The verifier soundness theorem `Sos.sos_sound` discharges any
constructed certificate. Below we wrap it in a small lemma showing
the architecture: given a `Certificate n` value, the conclusion
`∀ φ, 0 ≤ aeval φ p` follows when `cert.checks (.closed p) [] = true`.
-/

/-- For any `cert : Certificate 1`, if `cert.checks (.closed
smokeTarget) [] = true`, then `(x 0)² + 1 ≥ 0` over the reals. -/
example
    (cert : Certificate 1)
    (hcheck : cert.checks (.closed smokeTarget) [] = true) :
    ∀ φ : Fin 1 → ℝ, 0 ≤ CMvPolynomial.aeval φ smokeTarget := by
  intro φ
  exact sos_sound smokeTarget [] cert hcheck φ
    (fun g hg => by simp [List.not_mem_nil] at hg)

def main : IO Unit := runSmoke
