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
  /-- The constraint set is infeasible; certified via `−1 = σ₀ + …`. -/
  | infeasible

/-- The polynomial we certify against the constraint set. Closed: `p`.
Strict: `p − ε`. Infeasibility: `−1` (as the constant polynomial). -/
def Goal.target {n : Nat} : Goal n → CMvPolynomial n ℚ
  | .closed p     => p
  | .strict p ε _ => p - CMvPolynomial.C ε
  | .infeasible   => -1

/-- A full Positivstellensatz certificate. `sigmas` is a list of
subset-indexed SOS multipliers: each entry `(idxs, σ)` contributes
`σ.toPoly · ∏_{i ∈ idxs} gs[i]` to the certificate. The empty subset
`[]` recovers the original `σ₀` term; singletons `[i]` recover the
per-constraint `σᵢ` of a Putinar-style decomposition; higher cardinalities
give Schmüdgen-style preordering terms (products of constraints).

`eqCofs` provides one free polynomial cofactor `qⱼ` per equality
constraint `pⱼ`; the equality contribution is `qⱼ · pⱼ`. Cofactors are
unrestricted in sign (they are not required to be sums of squares).

Indices in each subset must be `< gs.length`; `Certificate.checks`
enforces this bound. -/
structure Certificate (n : Nat) where
  /-- Subset-indexed SOS multipliers. -/
  sigmas : List (List Nat × SOSDecomp n)
  /-- One free polynomial cofactor `qⱼ` per equality constraint `pⱼ`.
  Empty (default) when the goal has no equality hypotheses. -/
  eqCofs : List (CMvPolynomial n ℚ) := []
  deriving Inhabited

/-- Product of `gs[i]` for `i ∈ idxs`. Out-of-bounds indices default to
the constant `1`; the `Certificate.checks` bounds check ensures this
default never fires on a well-formed certificate. -/
def Certificate.constraintProduct {n : Nat}
    (gs : List (CMvPolynomial n ℚ)) (idxs : List Nat) :
    CMvPolynomial n ℚ :=
  idxs.foldr (fun i acc => acc * gs.getD i 1) 1

/-- Sum of `σ.toPoly · ∏_{i ∈ idxs} gs[i]` over the subset-indexed σ list. -/
def Certificate.monoidSum {n : Nat}
    (sigmas : List (List Nat × SOSDecomp n))
    (gs : List (CMvPolynomial n ℚ)) :
    CMvPolynomial n ℚ :=
  sigmas.foldr
    (fun pair acc => acc + pair.2.toPoly * Certificate.constraintProduct gs pair.1) 0

/-- Sum of `qⱼ * pⱼ` over paired lists of free cofactors and equality
polynomials. -/
def Certificate.equalitySum {n : Nat}
    (eqCofs : List (CMvPolynomial n ℚ)) (ps : List (CMvPolynomial n ℚ)) :
    CMvPolynomial n ℚ :=
  (eqCofs.zip ps).foldr (fun pair acc => acc + pair.fst * pair.snd) 0

/-- The full polynomial expansion
`Σ_S σ_S · ∏_{i ∈ S} gᵢ + Σⱼ qⱼ · pⱼ` of a certificate evaluated against
inequality constraints `gs` and equality constraints `ps`. -/
def Certificate.toPoly {n : Nat} (c : Certificate n)
    (gs : List (CMvPolynomial n ℚ)) (ps : List (CMvPolynomial n ℚ)) :
    CMvPolynomial n ℚ :=
  Certificate.monoidSum c.sigmas gs + Certificate.equalitySum c.eqCofs ps

/-- All indices in every subset are `< gs.length`. -/
def Certificate.indicesInBounds {n : Nat}
    (sigmas : List (List Nat × SOSDecomp n)) (gsLen : Nat) : Bool :=
  sigmas.all fun pair => pair.1.all (· < gsLen)

/-- Certificate validity check. Confirms every subset index is in
`[0, gs.length)`, that `eqCofs` and `ps` line up, then checks the
polynomial identity `goal.target = c.toPoly gs ps` via `decide +kernel`. -/
def Certificate.checks {n : Nat} (c : Certificate n) (goal : Goal n)
    (gs : List (CMvPolynomial n ℚ)) (ps : List (CMvPolynomial n ℚ)) : Bool :=
  Certificate.indicesInBounds c.sigmas gs.length &&
  (c.eqCofs.length == ps.length) &&
  decide (goal.target = c.toPoly gs ps)

/-- Bridge lemma: `checks goal gs ps = true` is equivalent to the
polynomial identity together with the bounds and length matches. -/
theorem Certificate.checks_iff {n : Nat} (c : Certificate n) (goal : Goal n)
    (gs : List (CMvPolynomial n ℚ)) (ps : List (CMvPolynomial n ℚ)) :
    c.checks goal gs ps = true ↔
      Certificate.indicesInBounds c.sigmas gs.length = true ∧
      c.eqCofs.length = ps.length ∧
      goal.target = c.toPoly gs ps := by
  unfold Certificate.checks
  simp [decide_eq_true_eq, and_assoc]

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

/-- Build a `Certificate n` from `SOS.Poly`-keyed subset-indexed σ data. -/
def Certificate.fromDecompiled {n : Nat}
    (sigmasPolys : List (List Nat × List (SOS.Poly n)))
    (eqCofPolys : List (SOS.Poly n) := []) : Certificate n :=
  { sigmas := sigmasPolys.map (fun pair => (pair.1, SOSDecomp.fromPolys pair.2)),
    eqCofs := eqCofPolys.map SOS.Poly.toCMv }

/-- Backward-compatible Putinar-shape builder: takes the original
`(σ₀, σᵢ list)` data and builds a subset-indexed certificate with the
empty subset for σ₀ and singletons `[i]` for each σᵢ. -/
def Certificate.fromPutinar {n : Nat}
    (sigma0 : SOSDecomp n) (sigmas : List (SOSDecomp n))
    (eqCofs : List (CMvPolynomial n ℚ) := []) : Certificate n :=
  let indexed : List (List Nat × SOSDecomp n) :=
    ([], sigma0) :: sigmas.zipIdx.map (fun pair => ([pair.2], pair.1))
  { sigmas := indexed, eqCofs }

end SOS
