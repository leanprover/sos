/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SOS.Raw
import CompPoly.Multivariate.CMvPolynomial
import CompPoly.Multivariate.Operations
import CompPoly.Multivariate.MvPolyEquiv.Instances
import Mathlib.Data.Rat.Cast.Defs

namespace SOS

open CPoly

/-- Convert the typed `Poly n` AST into a CompPoly polynomial with `ℚ`
coefficients. This is the bridge from our internal AST to the
computational substrate used by the verifier. -/
def Poly.toCMv {n : Nat} : SOS.Poly n → CMvPolynomial n ℚ
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

/-- A Putinar-style Positivstellensatz certificate. The list `sigmas`
provides one SOS multiplier per constraint, paired by position with
the externally-supplied constraint list `gs`. -/
structure Certificate (n : Nat) where
  sigma0 : SOSDecomp n
  sigmas : List (SOSDecomp n)
  deriving Inhabited

/-- Sum of `σᵢ.toPoly * gᵢ` over paired lists. -/
def Certificate.constraintSum {n : Nat}
    (sigmas : List (SOSDecomp n)) (gs : List (CMvPolynomial n ℚ)) :
    CMvPolynomial n ℚ :=
  (sigmas.zip gs).foldr (fun pair acc => acc + pair.fst.toPoly * pair.snd) 0

/-- The full polynomial expansion `σ₀ + Σᵢ σᵢ · gᵢ` of a certificate
evaluated against constraints `gs`. -/
def Certificate.toPoly {n : Nat} (c : Certificate n)
    (gs : List (CMvPolynomial n ℚ)) : CMvPolynomial n ℚ :=
  c.sigma0.toPoly + Certificate.constraintSum c.sigmas gs

/-- Certificate validity check. We rely on CompPoly's
`Lawful.instDecidableEq` (automatic for `ℚ` coefficients) to make
polynomial equality kernel-checkable via `decide +kernel`. -/
def Certificate.checks {n : Nat} (c : Certificate n) (goal : Goal n)
    (gs : List (CMvPolynomial n ℚ)) : Bool :=
  (c.sigmas.length == gs.length) &&
  decide (goal.target = c.toPoly gs)

/-- Bridge lemma: `checks goal gs = true` is equivalent to the polynomial
identity `goal.target = c.toPoly gs` together with the length match. -/
theorem Certificate.checks_iff {n : Nat} (c : Certificate n) (goal : Goal n)
    (gs : List (CMvPolynomial n ℚ)) :
    c.checks goal gs = true ↔
      c.sigmas.length = gs.length ∧
      goal.target = c.toPoly gs := by
  unfold Certificate.checks
  simp [decide_eq_true_eq]

/-! ### Building certificates from `SOS.Poly`-form data

The search produces `CMvPolynomial`-form squares; the elaborator
decompiles each square back into a `SOS.Poly n` AST so it can be
`ToExpr`-quoted into a Lean term. `Certificate.fromDecompiled` then
maps the AST squares back through `SOS.Poly.toCMv` to assemble a
`Certificate n`. -/

/-- Lift a `List (SOS.Poly n)` to a `SOSDecomp n` by mapping each
entry through `SOS.Poly.toCMv`. -/
def SOSDecomp.fromPolys {n : Nat} (squares : List (SOS.Poly n)) : SOSDecomp n :=
  { squares := squares.map SOS.Poly.toCMv }

/-- Build a `Certificate n` from `SOS.Poly`-keyed σ₀ / σᵢ data. -/
def Certificate.fromDecompiled {n : Nat}
    (sigma0Polys : List (SOS.Poly n))
    (sigmasPolys : List (List (SOS.Poly n))) : Certificate n :=
  { sigma0 := SOSDecomp.fromPolys sigma0Polys,
    sigmas := sigmasPolys.map SOSDecomp.fromPolys }

end SOS
