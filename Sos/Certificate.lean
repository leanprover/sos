/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Sos.Raw
import CompPoly.Multivariate.CMvPolynomial
import CompPoly.Multivariate.Operations
import CompPoly.Multivariate.MvPolyEquiv.Instances
import Mathlib.Data.Rat.Cast.Defs

namespace Sos

open CPoly

/-- Convert the typed `Poly n` AST into a CompPoly polynomial with `ℚ`
coefficients. This is the bridge from our internal AST to the
computational substrate used by the verifier. -/
def Poly.toCMv {n : Nat} : Sos.Poly n → CMvPolynomial n ℚ
  | .const r   => CMvPolynomial.C r
  | .var i     => CMvPolynomial.X i
  | .neg p     => -p.toCMv
  | .add p q   => p.toCMv + q.toCMv
  | .sub p q   => p.toCMv - q.toCMv
  | .mul p q   => p.toCMv * q.toCMv
  | .pow p k   => p.toCMv ^ k

/-- A list of polynomials whose sum-of-squares is the witness polynomial. -/
structure SOSDecomp (n : Nat) where
  squares : List (CMvPolynomial n ℚ)
  deriving Inhabited

/-- The polynomial expansion of a sum-of-squares decomposition. -/
def SOSDecomp.toPoly {n : Nat} (sd : SOSDecomp n) : CMvPolynomial n ℚ :=
  sd.squares.foldr (fun q acc => acc + q * q) 0

/-- Goal shape with all data needed to reconstruct the soundness theorem
appropriately. -/
inductive Goal (n : Nat) where
  /-- `p ≥ 0` over the constraint set. -/
  | closed     (p : CMvPolynomial n ℚ)
  /-- `p > 0`, certified via `p − ε ≥ 0` with `ε > 0`. -/
  | strict     (p : CMvPolynomial n ℚ) (epsilon : ℚ) (hε : 0 < epsilon)
  /-- The constraint set is infeasible; certified via `−1 = σ₀ + Σ σᵢ gᵢ`. -/
  | infeasible

/-- The polynomial we certify against the constraint set. Closed: `p`.
Strict: `p − ε`. Infeasibility: `−1` (as the constant polynomial). -/
def Goal.target {n : Nat} : Goal n → CMvPolynomial n ℚ
  | .closed p     => p
  | .strict p ε _ => p - CMvPolynomial.C ε
  | .infeasible   => -1

/-- A Putinar-style Positivstellensatz certificate. The `sigmas` list pairs
each constraint polynomial `gᵢ` with its SOS multiplier `σᵢ`. -/
structure Certificate (n : Nat) where
  sigma0 : SOSDecomp n
  sigmas : List (SOSDecomp n × CMvPolynomial n ℚ)
  deriving Inhabited

/-- The full polynomial expansion `σ₀ + Σᵢ σᵢ · gᵢ` of a certificate. -/
def Certificate.toPoly {n : Nat} (c : Certificate n) : CMvPolynomial n ℚ :=
  c.sigma0.toPoly +
  c.sigmas.foldr (fun pair acc => acc + pair.fst.toPoly * pair.snd) 0

/-- Certificate validity check. We rely on CompPoly's `Lawful.instDecidableEq`
(automatic for `ℚ` coefficients) to make polynomial equality decidable
and `cbv_decide`-friendly. -/
def Certificate.checks {n : Nat} (c : Certificate n) (goal : Goal n)
    (gs : List (CMvPolynomial n ℚ)) : Bool :=
  -- The constraint list provided externally must match the certificate's σᵢ list.
  (c.sigmas.length == gs.length) &&
  (c.sigmas.zip gs).all (fun pair => pair.fst.snd == pair.snd) &&
  -- And the polynomial identity must hold exactly.
  decide (goal.target = c.toPoly)

/-- Bridge lemma: `checks goal gs = true` is equivalent to the polynomial
identity `goal.target = c.toPoly` together with the constraint-list match. -/
theorem Certificate.checks_iff {n : Nat} (c : Certificate n) (goal : Goal n)
    (gs : List (CMvPolynomial n ℚ)) :
    c.checks goal gs = true ↔
      c.sigmas.length = gs.length ∧
      (∀ pair ∈ c.sigmas.zip gs, pair.fst.snd = pair.snd) ∧
      goal.target = c.toPoly := by
  unfold Certificate.checks
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true]
  constructor
  · rintro ⟨⟨hlen, hpairs⟩, hid⟩
    refine ⟨hlen, ?_, hid⟩
    intro pair hpair
    have := hpairs pair hpair
    simpa using this
  · rintro ⟨hlen, hpairs, hid⟩
    refine ⟨⟨hlen, ?_⟩, hid⟩
    intro pair hpair
    simpa using hpairs pair hpair

end Sos
