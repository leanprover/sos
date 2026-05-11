/-
Speed-test candidate set. Build target is wall-clock < 60s for the
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

/-! ### Strict positivity with tight or unfriendly bounds

LP-slack discovers `λ*` and descends through `ε = 2^-k` from there.
Including `polyDenom target` in the rounding schedule lets residuals
with non-power-of-two denominators land on the natural rational grid,
and `decide +kernel` verifies the certificate. -/

-- 19. non-power-of-two denominator (the residual ends up at denom 3200
-- after ε = 1/128 against `1/100`, requiring polyDenom-aware rounding).
example (x : ℝ) : 0 < x^2 + 1/100 := by sos

-- 20. multivariate, non-power-of-two denominator
example (x y : ℝ) : 0 < x^2 + y^2 + 1/500 := by sos

-- 21. tight strict positivity at the four-squares cap. `fourSquaresNat`
-- caps at `n ≤ 2^20`, which puts a floor of `ε ≥ 1/(2^20)` on what we
-- can certify by this pipeline.
example (x : ℝ) : 0 < x^2 + 1/1048576 := by sos

-- 22. infimum-0 strict positivity must fail gracefully.
-- p = (x*y − 1)² + x² is strictly positive everywhere on ℝ² (would need
-- x*y = 1 and x = 0 simultaneously) but its infimum is 0 along x → 0,
-- y = 1/x. No positive ε admits a Putinar certificate.
example : True := by
  fail_if_success
    (have : ∀ x y : ℝ, 0 < (x*y - 1)^2 + x^2 := by sos)
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

/-! ### Strict positivity: `sos?` suggestion includes `with ε := …` -/

/--
info: Try this:
  [apply] sos_witness { sigma0 := { squares := [CMvPolynomial.X 0] }, sigmas := [] } with ε := (1 : ℚ)
-/
#guard_msgs in
example (x : ℝ) : 0 < x^2 + 1 := by sos?

-- And the suggested replacement compiles:
example (x : ℝ) : 0 < x^2 + 1 := by
  sos_witness { sigma0 := { squares := [CMvPolynomial.X 0] }, sigmas := [] } with ε := (1 : ℚ)

/-! ### Coverage: orphan code paths

The cases below exercise paths that aren't otherwise reached by the
search-driven examples above:

* `nonpos` constraint hypothesis (`h : x ≤ 0`), driving the
  `aeval_nonneg_of_orig_neg` bridge in `SOS/Verifier.lean`.
* `sos_witness` with a constraint — the existing `sos_witness` smoke-
  test above is unconstrained.
* `sos_witness` for an infeasibility goal (`¬ p ≤ 0`) — exercises
  the `.infeasible` arm of the witness elaborator. -/

-- nonpos hypothesis: search-driven path closes via the .neg-wrapping
-- in `recogniseConstraint` and the `aeval_nonneg_of_orig_neg` bridge.
example (x : ℝ) (_h : x ≤ 0) : 0 ≤ -x := by sos

-- sos_witness with a constraint. (The witness here is the trivial
-- σ₀ = x^2, σ₁ = 0 — `x^2 ≥ 0` doesn't need the `0 ≤ x` hypothesis,
-- but the cert structure must still carry a sigmas entry per
-- constraint to match `cert.checks`'s length check.)
example (x : ℝ) (_h : 0 ≤ x) : 0 ≤ x^2 := by
  sos_witness
    { sigma0 := { squares := [CMvPolynomial.X 0] },
      sigmas := [{ squares := [] }] }

-- sos_witness for infeasibility. `-1 = x^2 + 1·(-x^2 - 1)` proves
-- the constraint set `{x^2 + 1 ≤ 0}` is infeasible.
example (x : ℝ) : ¬ (x^2 + 1 ≤ 0) := by
  sos_witness
    { sigma0 := { squares := [CMvPolynomial.X 0] },
      sigmas := [{ squares := [CMvPolynomial.C (1 : ℚ)] }] }

/-! ### Examples ported from Harrison's HOL Light `Examples/sos.ml`

Test cases lifted from John Harrison's TPHOLs 2007 implementation
(`Examples/sos.ml` in jrh13/hol-light, lines 1611–1894). Restricted
to the fragment our tactic supports: closed `0 ≤ p` / `0 < p` /
`¬ p ≤ 0` conclusions with Putinar-style `0 ≤ g`, `g ≤ 0`, `0 < g`
hypotheses. Examples involving equality hypotheses, disequalities,
disjunctive conclusions, `abs`, division, integer/natural arithmetic,
or Boolean combinations are out of the supported fragment and not
ported here.

Examples flagged with `-- FIXME` were verified by hand-running each
through `by sos` in isolation; they're within the supported fragment
but don't currently produce a certificate. The cause is almost always
the absence of iterative deepening (README "Single fixed relaxation
level"): the multiplier basis is fixed at `⌈D/2⌉` from the polynomial
degrees, and Harrison's REAL_SOS bumps this on failure. A few of the
multivariate direct-SOS failures (1819, 1805, 1832, …) likely also
need Newton-polytope monomial pruning to land on a Gram matrix that
rounds back to PSD. -/

/-! #### Direct SOS, no hypotheses (Harrison's `SOS_CONV` / `PURE_SOS`) -/

-- sos.ml:1789 — 2-variable degree-4
example (x y : ℝ) :
    0 ≤ 2*x^4 + 2*x^3*y - x^2*y^2 + 5*y^4 := by sos

-- sos.ml:1792 — 3-variable degree-4
example (x y z : ℝ) :
    0 ≤ x^4 - (2*y*z + 1)*x^2 + (y^2*z^2 + 2*y*z + 2) := by sos

-- sos.ml:1796 — 2-variable degree-4
example (x y : ℝ) :
    0 ≤ 4*x^4 + 4*x^3*y - 7*x^2*y^2 - 2*x*y^3 + 10*y^4 := by sos

-- sos.ml:1809 — 3-variable degree-6
example (x y z : ℝ) :
    0 ≤ 9*x^2*y^4 + 9*x^2*z^4 + 36*x^2*y^3 + 36*x^2*y^2
        - 48*x*y*z^2 + 4*y^4 + 4*z^4 - 16*y^3 + 16*y^2 := by sos

-- sos.ml:1814 — Motzkin × `(x²+y²+z²)` is SOS (Hilbert-17 style witness)
example (x y z : ℝ) :
    0 ≤ (x^2 + y^2 + z^2) *
        (x^4*y^2 + x^2*y^4 + z^6 - 3*x^2*y^2*z^2) := by sos

-- FIXME sos.ml:1800 — 2-variable degree-10. Needs Newton-polytope
-- pruning; the dense `monomialsUpTo 2 5` basis blows the SDP into
-- a non-roundable Gram region.
-- example (x y : ℝ) :
--     0 ≤ 4*x^4*y^6 + x^2 - x*y^2 + y^2 := by sos

-- FIXME sos.ml:1802 — 2-variable degree-6, Motzkin-like form. Likely
-- needs iterative deepening to bump the multiplier basis past
-- `⌈6/2⌉ = 3`.
-- example (x z : ℝ) :
--     0 ≤ 4096 * (x^4 + x^2 + z^6 - 3*x^2*z^2) + 729 := by sos

-- FIXME sos.ml:1805 — 2-variable degree-6 with linear `30*x*y` and
-- constants. Rounding miss at the fixed relaxation level.
-- example (x y : ℝ) :
--     0 ≤ 120*x^2 - 63*x^4 + 10*x^6 + 30*x*y - 120*y^2 + 120*y^4 + 31 := by sos

-- FIXME sos.ml:1819 — 3-variable degree-4 with linear+constant tail.
-- Surprising failure given the modest degree; likely a rounding miss
-- on the Gram matrix (the polynomial is bounded below by ≈ 1.59).
-- example (x y z : ℝ) :
--     0 ≤ x^4 + y^4 + z^4 - 4*x*y*z + x + y + z + 3 := by sos

-- FIXME sos.ml:1829 — 100·sum-of-squares − 588. The unsubtracted form
-- is trivially SOS; subtracting 588 forces the search to find a
-- non-trivial decomposition that survives rounding.
-- example (x : ℝ) :
--     0 ≤ 100*((2*x - 2)^2 + (x^3 - 8*x - 2)^2) - 588 := by sos

-- FIXME sos.ml:1832 — Rearranged form of the 1805 polynomial, fails
-- for the same reason.
-- example (x y : ℝ) :
--     0 ≤ x^2*(120 - 63*x^2 + 10*x^4) + 30*x*y
--         + 30*y^2*(4*y^2 - 4) + 31 := by sos

/-! #### Hard univariate `PURE_SOS` examples -/

-- sos.ml:1844 — degree-12 univariate
example (x : ℝ) :
    0 ≤ 98*x^12 - 980*x^10 + 3038*x^8 - 2968*x^6
        + 1022*x^4 - 84*x^2 + 2 := by sos

-- sos.ml:1853 — degree-14 univariate
example (x : ℝ) :
    0 ≤ 2*x^14 - 84*x^12 + 1022*x^10 - 2968*x^8
        + 3038*x^6 - 980*x^4 + 98*x^2 := by sos

-- FIXME sos.ml:1840 — strict `≥ 1/7` bound on the 1819 polynomial.
-- Fails for the same reason as 1819.
-- example (x y z : ℝ) :
--     0 ≤ x^4 + y^4 + z^4 - 4*x*y*z + x + y + z + 3 - 1/7 := by sos

/-! #### Zeng et al. (JSC 37, 2004) — Harrison's PURE_SOS battery -/

-- sos.ml:1867 — 3-var degree-6 Schur-style
example (x y z : ℝ) :
    0 ≤ x^6 + y^6 + z^6 - 3*x^2*y^2*z^2 := by sos

-- sos.ml:1870
example (x y z : ℝ) :
    0 ≤ x^4 + y^4 + z^4 + 1 - 4*x*y*z := by sos

-- sos.ml:1872
example (x y z : ℝ) :
    0 ≤ x^4 + 2*x^2*z + x^2 - 2*x*y*z + 2*y^2*z^2
        + 2*y*z^2 + 2*z^2 - 2*x + 2*y*z + 1 := by sos

-- sos.ml:1891 — 4-variable degree-6
example (x y z w : ℝ) :
    0 ≤ w^6 + 2*z^2*w^3 + x^4 + y^4 + z^4 + 2*x^2*w + 2*x^2*z
        + 3*x^2 + w^2 + 2*z*w + z^2 + 2*z + 2*w + 1 := by sos

-- FIXME sos.ml:1886 — 4-variable degree-4, with cross-terms
-- `2*x*y*z^2 + 2*x*y*w^2`. The 4-variable degree-2 multiplier basis
-- has 15 monomials; the SDP solves but rounding misses.
-- example (x y z w : ℝ) :
--     0 ≤ x^4 + 4*x^2*y^2 + 2*x*y*z^2 + 2*x*y*w^2 + y^4 + z^4 + w^4
--         + 2*z^2*w^2 + 2*x^2*w + 2*y^2*w + 2*x*y + 3*w^2 + 2*z^2 + 1 := by sos

-- FIXME sos.ml:1879 — Harrison's flagged hard Zeng case. He notes
-- "REAL_SOS does finally converge on the second run at level 12";
-- requires iterative deepening.
-- example (x y z : ℝ) :
--     0 ≤ x^4*y^4 - 2*x^5*y^3*z^2 + x^6*y^2*z^4
--         + 2*x^2*y^3*z - 4*x^3*y^2*z^3 + 2*x^4*y*z^5
--         + z^2*y^2 - 2*z^4*y*x + z^6*x^2 := by sos

/-! #### REAL_SOS with Putinar-style hypotheses -/

-- sos.ml:1718 — `0 ≤ x ∧ 0 ≤ y ⇒ x*y*(x+y)² ≤ (x²+y²)²`
example (x y : ℝ) (_hx : 0 ≤ x) (_hy : 0 ≤ y) :
    0 ≤ (x^2 + y^2)^2 - x*y*(x + y)^2 := by sos

-- FIXME sos.ml:1654 — `x ≥ 1 ∧ y ≥ 1 ⇒ x*y ≥ x + y - 1`. The
-- certificate `(x-1)(y-1)` requires σ₁ = (x-1) which is not SOS;
-- the next relaxation level (with degree-2 σᵢ) suffices but our
-- search has no iterative deepening.
-- example (x y : ℝ) (_hx : 0 ≤ x - 1) (_hy : 0 ≤ y - 1) :
--     0 ≤ x*y - (x + y - 1) := by sos

-- FIXME sos.ml:1657 — strict version of the above; same root cause.
-- example (x y : ℝ) (_hx : 0 < x - 1) (_hy : 0 < y - 1) :
--     0 < x*y - (x + y - 1) := by sos

-- FIXME sos.ml:1643 — `0 ≤ x,y,z ∧ x+y+z ≤ 3 ⇒ xy+xz+yz ≥ 3xyz`.
-- Putinar form needs degree-2 multipliers on the linear hypotheses.
-- example (x y z : ℝ) (_hx : 0 ≤ x) (_hy : 0 ≤ y) (_hz : 0 ≤ z)
--     (_hs : x + y + z - 3 ≤ 0) :
--     0 ≤ x*y + x*z + y*z - 3*x*y*z := by sos

-- FIXME sos.ml:1682 — interval `[2,4]³` Schur. Six interval
-- hypotheses blow up the SDP at the fixed relaxation level
-- (>60s timeout in isolation).
-- example (x y z : ℝ)
--     (_hx1 : 0 ≤ x - 2) (_hx2 : 0 ≤ 4 - x)
--     (_hy1 : 0 ≤ y - 2) (_hy2 : 0 ≤ 4 - y)
--     (_hz1 : 0 ≤ z - 2) (_hz2 : 0 ≤ 4 - z) :
--     0 ≤ 2*(x*z + x*y + y*z) - (x^2 + y^2 + z^2) := by sos

-- FIXME sos.ml:1672 — dodecahedral, intervals to `125841/50000`. Same
-- shape as 1682; same blow-up.
-- example (x y z : ℝ)
--     (_hx1 : 0 ≤ x - 2) (_hx2 : 0 ≤ 125841/50000 - x)
--     (_hy1 : 0 ≤ y - 2) (_hy2 : 0 ≤ 125841/50000 - y)
--     (_hz1 : 0 ≤ z - 2) (_hz2 : 0 ≤ 125841/50000 - z) :
--     0 ≤ 2*(x*z + x*y + y*z) - (x^2 + y^2 + z^2) := by sos

-- FIXME sos.ml:1690 — sharp `≥ 12` bound on the same interval.
-- Harrison reports needing depth 12; iterative deepening required.
-- example (x y z : ℝ)
--     (_hx1 : 0 ≤ x - 2) (_hx2 : 0 ≤ 4 - x)
--     (_hy1 : 0 ≤ y - 2) (_hy2 : 0 ≤ 4 - y)
--     (_hz1 : 0 ≤ z - 2) (_hz2 : 0 ≤ 4 - z) :
--     0 ≤ 2*(x*z + x*y + y*z) - (x^2 + y^2 + z^2) - 12 := by sos

/-! ### Pure invariant checks for search/round/reconstruct helpers

These exercise internal helpers (`monomialsUpTo`, `decodeSdpBlock`,
`LDL.reconstruct`) on degenerate inputs, so a refactor that
mis-handles the empty / null case is caught here rather than only by
the end-to-end `by sos` examples above. -/

#guard (SOS.Search.monomialsUpTo 2 2).size = 6
#guard
  match (SOS.Search.monomialsUpTo 2 2)[1]? with
  | some m =>
    let a := CMvMonomial.degreeOf m ⟨0, by decide⟩
    let b := CMvMonomial.degreeOf m ⟨1, by decide⟩
    a = 1 ∧ b = 0
  | none => False

#guard
  match SOS.Search.decodeSdpBlock (1 : ℚ) 2 FloatArray.empty with
  | none => true
  | some _ => false

#guard
  match SOS.LDL.reconstruct 2 (#[] : Array ℚ)
      (#[] : Array (CMvPolynomial 1 ℚ)) with
  | none => true
  | some _ => false
