/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

SDP encoding (CompPoly polynomials → an external solver), rational
rounding of the float Gram-matrix solution, and the top-level
`runSearch` driver.

**v0 status.** The lean-csdp FFI integration is not yet wired in (see
TODO in `lakefile.lean`). For now, this module:

* defines the monomial-basis enumerator (`monomialsUpTo`) and the
  rational-rounding denominator schedule (`niceDenominators`,
  `niceRound`);
* provides a stub `runSearch` that returns `none`, allowing the
  rest of the pipeline (verifier, tactic frontend) to compile and be
  exercised via `sos_witness` with literal certificates.

The full SDP encoding (constraint construction over the monomial
union, block-diagonal CSDP matrix layout) is documented in this
file's header but not yet implemented.

**Encoding (Putinar form).** For a closed-positivity goal `p ≥ 0` over
`{gᵢ ≥ 0}`:

* One SDP block per multiplier:
  - block 0  = σ₀ Gram matrix (size `|z₀|`, where `z₀` enumerates
    monomials of total degree ≤ ⌈deg(p)/2⌉).
  - block i+1 = σᵢ Gram matrix for `gᵢ` (size `|zᵢ|`, monomials of
    total degree ≤ ⌈(deg(p) − deg(gᵢ))/2⌉).
* Decision variables = upper-triangle entries of each Gram matrix.
* For each monomial `m` in the *union* of `support p ∪ support
  (zᵢ·zⱼ·gᵢ)`, one CSDP equality constraint:
    `coef_m(p) = Σ_{block b, j ≤ k} Q_b[j,k] · coef_m(z_b[j]·z_b[k]·g_b)`
  with `g_0 = 1`. CSDP's symmetric `tr(A·X) = b` form uses upper-
  triangle `A` with off-diagonal entries halved.
* Cost matrix `C = 0` (feasibility). Strict positivity adds a slack
  variable in an LP block.
* Float Gram matrices come back in `Solution.X`. We round each to
  rationals over a denominator schedule, then verify the resulting
  certificate exactly via `Certificate.checks`.
-/
import Sos.Certificate
import Sos.LDL
import LeanCsdp

namespace Sos.Search

open CPoly

variable {n : Nat}

/-! ### Monomial-basis enumeration -/

/-- All monomials in `n` variables of total degree ≤ `d`, in deterministic
order. Brute-force enumeration via a counter array. -/
def monomialsUpTo (n : Nat) (d : Nat) : Array (CMvMonomial n) :=
  Id.run do
    let mut acc : Array (CMvMonomial n) := #[]
    let total : Nat := d + 1
    let mut counters : Array Nat := Array.replicate n 0
    let mut done := false
    while not done do
      let sum := counters.foldl (· + ·) 0
      if sum ≤ d then
        if h : counters.size = n then
          acc := acc.push ⟨counters, h⟩
      let mut i : Nat := 0
      let mut carry := true
      while carry && i < n do
        let cur := counters[i]!
        if cur + 1 < total then
          counters := counters.set! i (cur + 1)
          carry := false
        else
          counters := counters.set! i 0
          i := i + 1
      if carry then done := true
    return acc

/-! ### Denominator schedule for rational rounding -/

/-- Schedule of denominators tried by the rational rounder, adapted from
`sos.ml`'s `find_rounding`. First small integers, then powers of two. -/
def niceDenominators : List ℚ :=
  let smalls : List ℚ := (List.range 31).map (fun i => (i + 1 : ℚ))
  let powTwo : List ℚ := (List.range 62).map (fun i => (2 ^ (i + 5) : ℚ))
  smalls ++ powTwo

/-- Round a single float to the nearest rational at denominator `d`. -/
def niceRound (d : ℚ) (x : Float) : ℚ :=
  let dFloat : Float := Float.ofInt d.num / Float.ofInt d.den
  let scaled := x * dFloat + 0.5
  let nUnsigned : Int := scaled.toUInt64.toNat
  let nSigned : Int :=
    if scaled < 0 then -((-scaled).toUInt64.toNat : Int) else nUnsigned
  (nSigned : ℚ) / d

/-! ### Search driver (stub)

Returns `none` until `lean-csdp` integration is wired in. The verifier
(`sos_sound`, `sos_strict_sound`, `sos_infeasible_sound`) and tactic
frontend (`sos_witness`) work with literal certificates without
needing the search.
-/

/-- v0 stub: produces no certificate. Replaced once the SDP-search backend
is wired in. -/
def runSearch (_goal : Goal n) (_gs : List (CMvPolynomial n ℚ)) :
    IO (Option (Certificate n)) := do
  return none

end Sos.Search
