/-
Worked examples and smoke test for the `sos` tactic.
-/
import Sos

open Sos CPoly

/-- Smoke test target: `(x 0)² + 1` over `Fin 1`. -/
def smokeTarget : CMvPolynomial 1 ℚ :=
  let x0 : CMvPolynomial 1 ℚ := CMvPolynomial.X 0
  x0 * x0 + CMvPolynomial.C 1

def main : IO Unit := do
  IO.println s!"target totalDegree: {smokeTarget.totalDegree}"
  match (← Sos.Search.runSearch (Goal.closed (n := 1) smokeTarget) []) with
  | some cert =>
    IO.println s!"found cert: {cert.sigma0.squares.length} σ₀-squares, {cert.sigmas.length} σᵢ blocks"
  | none =>
    IO.println "no cert found"
