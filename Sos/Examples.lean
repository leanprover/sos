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

/-! ### Round-trip test: `Sos.Poly` ToExpr is faithful.

The pipeline that consumes a search-produced certificate eventually
quotes it back as a Lean expression via the `ToExpr (Sos.Poly n)`
instance. The test below builds a fixed `Sos.Poly 2`, ToExpr-quotes
it, evaluates the resulting expression back in `MetaM`, and
confirms it round-trips definitionally.
-/

-- Round-trip Sos.Poly through ToExpr / Meta.evalExpr.
run_meta do
  let p : Sos.Poly 2 :=
    Sos.Poly.add
      (Sos.Poly.mul (Sos.Poly.var ⟨0, by decide⟩) (Sos.Poly.var ⟨0, by decide⟩))
      (Sos.Poly.add
        (Sos.Poly.mul (Sos.Poly.var ⟨1, by decide⟩) (Sos.Poly.const 3))
        (Sos.Poly.const (-2 : Rat)))
  let typeE := Lean.mkApp (Lean.Expr.const ``Sos.Poly []) (Lean.mkNatLit 2)
  let e := Sos.Poly.toExprImpl p
  let p' ← Lean.Meta.evalExpr (Sos.Poly 2) typeE e
  unless decide (p = p') do
    throwError "Sos.Poly ToExpr round-trip failed"
  IO.println "✓ Sos.Poly ToExpr round-trip ok"

-- Round-trip CMvPolynomial → Sos.Poly → CMvPolynomial via decompile + toCMv.
run_meta do
  -- p = 3*x0² + 2*x0*x1 + 5
  let x0 : CMvPolynomial 2 ℚ := CMvPolynomial.X 0
  let x1 : CMvPolynomial 2 ℚ := CMvPolynomial.X 1
  let p : CMvPolynomial 2 ℚ :=
    CMvPolynomial.C 3 * x0 * x0 + CMvPolynomial.C 2 * x0 * x1 + CMvPolynomial.C 5
  let q := (Sos.Poly.decompile p).toCMv
  unless decide (p = q) do
    throwError "Sos.Poly.decompile round-trip failed"
  IO.println "✓ Sos.Poly.decompile round-trip ok"

/-! ### `sos_witness` end-to-end on a hand-built certificate. -/

/-- Hand-crafted certificate for `(x 0)² + 1 ≥ 0`: `σ₀ = (X 0)² + 1²`. -/
def handCert_x2_plus_1 : Certificate 1 :=
  { sigma0 := { squares := [CMvPolynomial.X 0, CMvPolynomial.C 1] },
    sigmas := [] }

-- Sanity check: the cert validates `(Poly.var 0)² + 1`.
example :
    handCert_x2_plus_1.checks
      (.closed ((Sos.Poly.add (Sos.Poly.pow (Sos.Poly.var 0) 2)
                              (Sos.Poly.const 1)).toCMv : CMvPolynomial 1 ℚ)) [] = true := by
  with_unfolding_all decide

example : ∀ x : Fin 1 → ℝ, 0 ≤ (x 0)^2 + 1 := by
  sos_witness handCert_x2_plus_1

/-- `(x 0 + x 1)² = (x 0)² + 2·x 0·x 1 + (x 1)²`. -/
def handCert_perfect_square : Certificate 2 :=
  { sigma0 :=
      { squares := [CMvPolynomial.X 0 + CMvPolynomial.X 1] },
    sigmas := [] }

example : ∀ x : Fin 2 → ℝ, 0 ≤ (x 0)^2 + 2*(x 0)*(x 1) + (x 1)^2 := by
  sos_witness handCert_perfect_square

/-- For `0 ≤ x 0 → 0 ≤ (x 0)² - x 0 + 1/4`: `(x 0 - 1/2)²` decomposes
the conclusion; the constraint plays no part. -/
def handCert_constrained : Certificate 1 :=
  { sigma0 :=
      { squares := [CMvPolynomial.X 0 - CMvPolynomial.C (1/2)] },
    sigmas := [{ squares := [] }] }

example : ∀ x : Fin 1 → ℝ, 0 ≤ x 0 → 0 ≤ (x 0)^2 - x 0 + 1/4 := by
  sos_witness handCert_constrained

/-! ### Infeasibility: `(x 0)² + 1 ≤ 0` is impossible. -/

/-- Cert for `¬ ((x 0)² + 1 ≤ 0)`: with `g₀ = -(X 0)² - 1` we have
`σ₀ = (X 0)²` and `σ₁ = 1`, giving `σ₀ + σ₁ · g₀ = -1`. -/
def handCert_infeasible : Certificate 1 :=
  { sigma0 := { squares := [CMvPolynomial.X 0] },
    sigmas := [{ squares := [CMvPolynomial.C 1] }] }

example : ∀ x : Fin 1 → ℝ, ¬ ((x 0)^2 + 1 ≤ 0) := by
  sos_witness handCert_infeasible

/-! ### Search-driven `by sos` end-to-end. -/

example : ∀ x : Fin 1 → ℝ, 0 ≤ (x 0)^2 + 1 := by sos
example : ∀ x : Fin 1 → ℝ, ¬ ((x 0)^2 + 1 ≤ 0) := by sos

def main : IO Unit := runSmoke
