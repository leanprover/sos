/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

`by sos` showcase — the primary entry point for evaluating this
package. The tactic discharges polynomial (in)equality goals over
ℝ (and ℤ / ℚ / ℕ, lifted automatically) by finding a Positivstellensatz
certificate: it shells out to CSDP, rounds the floating-point Gram
matrix to ℚ, then verifies the resulting sum-of-squares identity
inside the kernel.

Layout:

* §1–§7 walk through the supported fragment by capability, starting
  with one-line positivity goals and building up through constrained,
  strict, equality-hypothesis, infeasibility, and ℕ/ℤ/ℚ-lifted forms.
* §8 demonstrates the `sos?` → `sos_witness` workflow for inspecting
  and pinning certificates.
* §9 covers graceful failure (Motzkin, infimum-0 strict positivity)
  and the out-of-scope-input error messages.

The full Harrison `Examples/sos.ml` port (including known
limitations) lives in `SOSTest.Harrison`. Internal-helper invariant
checks live in `SOSTest.Internal`. Exact-rational simplex tests live
in `SOSTest.RatSimplexTests`.

Speed contract: this file builds in under 60s wall-clock.
-/
import SOS

open SOS CPoly

/-! ## §1. Positivity over ℝ -/

example (x : ℝ) : 0 ≤ x^2 + 1 := by sos
example (x : ℝ) : 0 ≤ x^4 + 1 := by sos

-- Perfect squares, single-variable and multivariate.
example (x : ℝ) : 0 ≤ x^2 + 2*x + 1 := by sos
example (x y : ℝ) : 0 ≤ x^2 - 2*x*y + y^2 := by sos
example (x y : ℝ) : 0 ≤ x^2 + 2*x*y + y^2 := by sos
example (x : ℝ) : 0 ≤ x^4 - 2*x^2 + 1 := by sos

-- Cyclic Schur, 3 variables.
example (a b c : ℝ) :
    0 ≤ a^2 + b^2 + c^2 - a*b - b*c - a*c := by sos

-- AM ≥ GM squared, 2 variables, degree 4.
example (x y : ℝ) : 0 ≤ (x^2 + y^2)^2 - 4*x^2*y^2 := by sos

-- Cauchy–Schwarz: `(a²+b²)(c²+d²) ≥ (ac+bd)²` — rank-1, degree-4, 4 variables.
example (a b c d : ℝ) :
    0 ≤ (a^2 + b^2) * (c^2 + d^2) - (a*c + b*d)^2 := by sos

/-! ## §2. General inequalities (`a ≤ b` / `a < b` form)

`by sos` reifies arbitrary (in)equality conclusions, not just the
`0 ≤ p` normal form — no manual rewrite required. -/

example (x : ℝ) : x ≤ x^2 + x + 1 := by sos
example (x : ℝ) : x < x^2 + x + 2 := by sos
example (x : ℝ) : -(x^2 + 1) ≤ 0 := by sos

/-! ## §3. Strict positivity

The strict-inequality path discovers a Putinar slack `λ*` via an LP
solve and descends through `ε = 2^-k` from there. Including
`polyDenom target` in the rounding schedule lets residuals with
non-power-of-two denominators land on the natural rational grid. -/

example (x : ℝ) : 0 < x^2 + 1 := by sos
example (x : ℝ) : 0 < x^4 + 1 := by sos
example (x y : ℝ) : 0 < x^2 + y^2 + 1 := by sos

-- Non-power-of-two denominator: the residual ends up at denom 3200
-- after ε = 1/128 against `1/100`, requiring polyDenom-aware rounding.
example (x : ℝ) : 0 < x^2 + 1/100 := by sos

-- Multivariate, non-power-of-two denominator.
example (x y : ℝ) : 0 < x^2 + y^2 + 1/500 := by sos

-- Tight strict positivity at the four-squares cap. `fourSquaresNat`
-- caps at `n ≤ 2^20`, putting a floor of `ε ≥ 1/2^20` on what we can
-- certify by this pipeline.
example (x : ℝ) : 0 < x^2 + 1/1048576 := by sos

/-! ## §4. Constrained goals (Putinar quadratic module) -/

example (x : ℝ) (_h : 0 ≤ x) : 0 ≤ x^3 + x := by sos
example (x : ℝ) (_h : 0 ≤ x) : 0 ≤ x^2 - x + 1/4 := by sos

example (x y : ℝ) (_hx : 0 ≤ x) (_hy : 0 ≤ y) :
    0 ≤ x^2 + 2*x*y + y^2 := by sos

-- Strict-inequality constraint hypothesis: promoted to `0 ≤` in the
-- elaborator via `le_of_lt`.
example (x : ℝ) (_h : 0 < x) : 0 ≤ x^3 + x := by sos

-- Nonpos hypothesis (`h : x ≤ 0`), driving the `.neg`-wrapping in
-- `recogniseConstraint` and the `aeval_nonneg_of_orig_neg` bridge in
-- `SOS/Verifier.lean`.
example (x : ℝ) (_h : x ≤ 0) : 0 ≤ -x := by sos

/-! ## §5. Equality hypotheses

The certificate gains a free polynomial cofactor `qⱼ` per equality
`pⱼ = 0`. The verified identity becomes
`target = σ₀ + Σᵢ σᵢ · gᵢ + Σⱼ qⱼ · pⱼ`. The reifier maps `a = b` to
`pⱼ := a − b`; downstream the cofactor search is free to discover any
sign for `qⱼ`. -/

-- From `x*y = 1` conclude `0 ≤ x*y − 1`. Cofactor `q := 1`.
example (x y : ℝ) (_h : x*y = 1) : 0 ≤ x*y - 1 := by sos

-- Degree-1 cofactor: `x = 1 → 0 ≤ x² − 1`. Search must discover
-- `q := x + 1`. Load-bearing: the conclusion is false at `x := 0`
-- without the equality.
example (x : ℝ) (_h : x = 1) : 0 ≤ x^2 - 1 := by sos

-- Strict positivity with equality, exercising `runStrict`'s cofactor
-- path (both the λ-solve and the feasibility re-solve include cofactor
-- blocks). Load-bearing: `0 < x²` is false at `x := 0`.
example (x : ℝ) (_h : x = 1) : 0 < x^2 := by sos

/-! ## §6. Infeasibility (`¬ p ≤ 0` conclusions) -/

example (x : ℝ) : ¬ (x^2 + 1 ≤ 0) := by sos
example (x : ℝ) : ¬ (x^4 + 1 ≤ 0) := by sos

/-! ## §7. Lifting ℕ / ℤ / ℚ goals to ℝ

The lift pre-pass in `SOS/Lift.lean` runs before `parseGoalAtomic`.
It intros leading ℕ / ℤ / ℚ / ℝ universal binders, splits equality
conclusions via `le_antisymm`, rewrites ℕ / ℤ strict inequalities via
`lt_iff_add_one_le`, applies the cast bridge (`Nat.cast_le.mp`, etc.)
on the conclusion, runs `rify at *` to lift hypotheses, and adds a
`0 ≤ (↑a : ℝ)` hypothesis for every ℕ-typed cast atom now in the goal.

The user-visible tactic name does not change — `by sos` auto-dispatches
on the (in)equality type. Goals already over ℝ pay no overhead. -/

-- ℤ: `(a − b)² ≥ 0`.
example (a b : ℤ) : 2*a*b ≤ a^2 + b^2 := by sos

-- ℤ Schur: `(a−b)² + (b−c)² + (a−c)² ≥ 0` divided by two.
example (a b c : ℤ) : a*b + b*c + a*c ≤ a^2 + b^2 + c^2 := by sos

-- ℚ strict: routed through `Rat.cast_lt.mp` to the ℝ strict-positivity path.
example (x : ℚ) : 0 < x^2 + 1 := by sos

-- ℚ: `(x² − y²)² ≥ 0`.
example (x y : ℚ) : 4*x^2*y^2 ≤ (x^2 + y^2)^2 := by sos

-- Mixed ℕ + ℝ — ℕ binder lifted, ℝ atom preserved.
example : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x^2 + n := by sos

-- ℕ-cast atom appears only in a hypothesis (conclusion is over ℝ with
-- no ℕ casts). The lift pre-pass must scan local hypothesis types too,
-- otherwise the `0 ≤ ↑n` fact never reaches the SOS reifier.
example (n : ℕ) (x : ℝ) (_h : (n : ℝ) = x) : 0 ≤ x := by sos

-- Strict ℕ via `Nat.lt_iff_add_one_le`. `n < n+1` rewrites to
-- `n+1 ≤ n+1`, which the rewrite step closes reflexively before the
-- cast bridge is needed.
example : ∀ n : ℕ, n < n + 1 := by sos

-- ℕ equality via `le_antisymm` split (Harrison `sos.ml:1725`). After
-- the antisymmetric split both subgoals reduce to `0 ≤ 0`.
example : ∀ m n : ℕ, 2*m + n = (n + m) + m := by sos

-- ℕ-discreteness via the negate-and-refute path (Harrison's `INT_SOS`,
-- `sos.ml:1728`). At `n := 0.5`, `n*n − n = −0.25 < 0`, so this is not
-- in the quadratic module of `{n ≥ 0}` over `ℝ[n]` and the direct
-- Putinar path fails. `runSosWithLift` then negates the conclusion,
-- applies `Nat.lt_iff_add_one_le`, and finds the infeasibility cert
-- `(5↑n − 3)²/16 + (5/16)·↑n + (25/16)·(↑n − ↑n² − 1) = −1`.
example : ∀ n : ℕ, n ≤ n * n := by sos

/-! ## §8. `sos?` — inspect, then pin the witness

`sos?` runs the search and prints a `Try this:` suggestion of an
explicit `sos_witness`. The witness is then statically checked at
elaboration time, with no CSDP call — useful for committing a
certificate that you don't want re-derived on every build. -/

/-- info: Try this:
  [apply] sos_witness { sigma0 := { squares := [CMvPolynomial.C (1 : ℚ), CMvPolynomial.X 0] }, sigmas := [] }
-/
#guard_msgs in
example (x : ℝ) : 0 ≤ x^2 + 1 := by sos?

-- And the suggested replacement compiles:
example (x : ℝ) : 0 ≤ x^2 + 1 := by
  sos_witness { sigma0 := { squares := [CMvPolynomial.C (1 : ℚ), CMvPolynomial.X 0] }, sigmas := [] }

-- For strict positivity, the `Try this:` suggestion includes `with ε := …`.
/-- info: Try this:
  [apply] sos_witness { sigma0 := { squares := [CMvPolynomial.X 0] }, sigmas := [] } with ε := (1 : ℚ)
-/
#guard_msgs in
example (x : ℝ) : 0 < x^2 + 1 := by sos?

example (x : ℝ) : 0 < x^2 + 1 := by
  sos_witness { sigma0 := { squares := [CMvPolynomial.X 0] }, sigmas := [] } with ε := (1 : ℚ)

-- For equality goals the suggestion includes `eqCofs := …`.
/-- info: Try this:
  [apply] sos_witness { sigma0 := { squares := [] }, sigmas := [], eqCofs := [CMvPolynomial.C (1 : ℚ)] }
-/
#guard_msgs in
example (x y : ℝ) (_h : x*y = 1) : 0 ≤ x*y - 1 := by sos?

/-! ### `sos_witness` direct use

The witness elaborator also accepts certificates for constrained and
infeasibility goals. (The cert structure must carry a `sigmas` entry
per constraint to match `cert.checks`'s length check, even when the
constraint isn't load-bearing.) -/

-- Constrained — trivial witness, exercising the constraint structural check.
example (x : ℝ) (_h : 0 ≤ x) : 0 ≤ x^2 := by
  sos_witness
    { sigma0 := { squares := [CMvPolynomial.X 0] },
      sigmas := [{ squares := [] }] }

-- Infeasibility — `-1 = x² + 1·(-x² - 1)` proves the constraint set
-- `{x² + 1 ≤ 0}` is infeasible.
example (x : ℝ) : ¬ (x^2 + 1 ≤ 0) := by
  sos_witness
    { sigma0 := { squares := [CMvPolynomial.X 0] },
      sigmas := [{ squares := [CMvPolynomial.C (1 : ℚ)] }] }

-- Combined inequality + equality: from `0 ≤ x − 1` and `x = 0` derive
-- `False`. Certificate: `−1 = 0 + 1·(x − 1) + (−1)·x`.
example (x : ℝ) (_hx : 0 ≤ x - 1) (_hxz : x = 0) : False := by
  sos_witness
    { sigma0 := { squares := [] },
      sigmas := [{ squares := [CMvPolynomial.C (1 : ℚ)] }],
      eqCofs := [-CMvPolynomial.C (1 : ℚ)] }

/-! ## §9. Graceful failure & out-of-scope guards -/

-- Motzkin is nonneg but not SOS, so search must fail gracefully.
example : True := by
  fail_if_success
    (have : ∀ x y : ℝ, 0 ≤ x^4*y^2 + x^2*y^4 + 1 - 3*x^2*y^2 := by sos)
  trivial

-- Infimum-0 strict positivity must also fail gracefully. `p = (x*y −
-- 1)² + x²` is strictly positive everywhere on ℝ² but its infimum is
-- 0 along `x → 0, y = 1/x`. No positive ε admits a Putinar certificate.
example : True := by
  fail_if_success
    (have : ∀ x y : ℝ, 0 < (x*y - 1)^2 + x^2 := by sos)
  trivial

-- Controls for the equality-hypothesis examples in §5: same conclusion
-- without the equality must fail, confirming the equality path was
-- genuinely exercised above.
example : True := by
  fail_if_success
    (have : ∀ x : ℝ, 0 ≤ x^2 - 1 := by sos)
  trivial

example : True := by
  fail_if_success
    (have : ∀ x : ℝ, 0 < x^2 := by sos)
  trivial

-- Truncated ℕ subtraction is refused with a hint.
/-- error: sos: `by sos` does not handle truncated ℕ subtraction in goals; cast to `Int.sub`, or rewrite via `Nat.sub_eq` with `m ≤ n` in context.
-/
#guard_msgs in
example : ∀ n : ℕ, n - 1 ≤ n := by sos

-- ℕ / ℤ DIV/MOD with positive literal divisor is supported via the
-- enrichment witnesses introduced by the lift pre-pass (issue #24).
-- A non-literal divisor (here `b`) skips the enrichment, leaving the
-- reifier to treat `a / b` as an opaque atom; without the witness
-- constraints the search has nothing to certify against and fails.
/-- error: sos: search failed to find an infeasibility certificate
-/
#guard_msgs in
example : ∀ a b : ℕ, b ≠ 0 → a / b * b ≤ a := by sos
