/-
Programmatic smoke test for the Sos library, exercised by the
`sos-example` Lake target. Builds a CMvPolynomial, runs the search,
and prints whether the verifier accepts the produced certificate.
-/
import Sos

open Sos CPoly

/-- Polynomial `(x 0)² + 1` in 1 variable over ℚ. -/
def smokeTarget : CMvPolynomial 1 ℚ :=
  let x0 : CMvPolynomial 1 ℚ := CMvPolynomial.X 0
  x0 * x0 + CMvPolynomial.C 1

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

def main : IO Unit := runSmoke
