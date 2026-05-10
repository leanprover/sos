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

/-! ### Stalling-case probes (Plan B‴ Task A measurement)

Two end-state goals previously stalled CSDP because the unique
Putinar SOS Gram is rank-1 on the PSD boundary. Run both through
the (now trace-minimising) search and report whether a valid
certificate is produced. -/

/-- `(x 0 + x 1)² = (X 0)² + 2·X 0·X 1 + (X 1)²`. Closed positivity. -/
def perfectSquareTarget : CMvPolynomial 2 ℚ :=
  let x0 : CMvPolynomial 2 ℚ := CMvPolynomial.X 0
  let x1 : CMvPolynomial 2 ℚ := CMvPolynomial.X 1
  x0 * x0 + CMvPolynomial.C 2 * x0 * x1 + x1 * x1

def runProbePerfectSquare : IO Unit := do
  IO.println "=== probe: 0 ≤ (x 0 + x 1)² ==="
  let goal : Goal 2 := .closed perfectSquareTarget
  let t0 ← IO.monoMsNow
  match (← Sos.Search.runSearch goal []) with
  | some cert =>
    let t1 ← IO.monoMsNow
    IO.println s!"✓ ({t1 - t0} ms) cert: {cert.sigma0.squares.length} σ₀-squares, \
      {cert.sigmas.length} σᵢ blocks; checks = {cert.checks goal []}"
  | none =>
    let t1 ← IO.monoMsNow
    IO.println s!"✗ ({t1 - t0} ms) no cert"

/-- Constrained `0 ≤ x 0 → 0 ≤ (x 0)² - x 0 + 1/4`. The reified
constraint is `g₀ = X 0`. -/
def constrainedTarget : CMvPolynomial 1 ℚ :=
  let x0 : CMvPolynomial 1 ℚ := CMvPolynomial.X 0
  x0 * x0 - x0 + CMvPolynomial.C (1/4)

def runProbeConstrained : IO Unit := do
  IO.println "=== probe: 0 ≤ x 0 → 0 ≤ (x 0)² - x 0 + 1/4 ==="
  let g0 : CMvPolynomial 1 ℚ := CMvPolynomial.X 0
  let goal : Goal 1 := .closed constrainedTarget
  let t0 ← IO.monoMsNow
  match (← Sos.Search.runSearch goal [g0]) with
  | some cert =>
    let t1 ← IO.monoMsNow
    IO.println s!"✓ ({t1 - t0} ms) cert: {cert.sigma0.squares.length} σ₀-squares, \
      {cert.sigmas.length} σᵢ blocks; checks = {cert.checks goal [g0]}"
  | none =>
    let t1 ← IO.monoMsNow
    IO.println s!"✗ ({t1 - t0} ms) no cert"

def runProbeInfeasible : IO Unit := do
  IO.println "=== probe: ¬ ((x 0)² + 1 ≤ 0) (infeasibility) ==="
  -- gs = [-(X 0)² - 1] (the reified `(x 0)² + 1 ≤ 0` constraint).
  let x0 : CMvPolynomial 1 ℚ := CMvPolynomial.X 0
  let g0 : CMvPolynomial 1 ℚ := -(x0 * x0) - CMvPolynomial.C 1
  let goal : Goal 1 := .infeasible
  let t0 ← IO.monoMsNow
  match (← Sos.Search.runSearch goal [g0]) with
  | some cert =>
    let t1 ← IO.monoMsNow
    IO.println s!"✓ ({t1 - t0} ms) cert: {cert.sigma0.squares.length} σ₀-squares, \
      {cert.sigmas.length} σᵢ blocks; checks = {cert.checks goal [g0]}"
  | none =>
    let t1 ← IO.monoMsNow
    IO.println s!"✗ ({t1 - t0} ms) no cert"

def runProbeMinusSquare : IO Unit := do
  IO.println "=== probe: 0 ≤ (x 0 - x 1)² ==="
  let x0 : CMvPolynomial 2 ℚ := CMvPolynomial.X 0
  let x1 : CMvPolynomial 2 ℚ := CMvPolynomial.X 1
  let p : CMvPolynomial 2 ℚ := x0*x0 - CMvPolynomial.C 2 * x0 * x1 + x1*x1
  let goal : Goal 2 := .closed p
  let t0 ← IO.monoMsNow
  match (← Sos.Search.runSearch goal []) with
  | some cert =>
    let t1 ← IO.monoMsNow
    IO.println s!"✓ ({t1 - t0} ms) cert: {cert.sigma0.squares.length} σ₀-squares; \
      checks = {cert.checks goal []}"
  | none =>
    let t1 ← IO.monoMsNow
    IO.println s!"✗ ({t1 - t0} ms) no cert"

def main : IO Unit := do
  runSmoke
  runProbePerfectSquare
  runProbeConstrained
  runProbeInfeasible
  runProbeMinusSquare
