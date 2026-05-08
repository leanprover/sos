/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Soundness theorems for SOS certificates.
-/
import Sos.Certificate
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Linarith

namespace Sos

open CPoly

variable {n : Nat}

/-! ### CompPoly aeval helpers

CompPoly ships `@[simp]` lemmas for `aeval_C`, `aeval_X`, `aeval_add`, and
`aeval_mul`, but not `aeval_zero`, `aeval_neg`, `aeval_sub`. We derive
these via the ring-hom structure of `eval₂Hom`.
-/

@[simp] lemma CMvPolynomial.aeval_zero {R σ : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R]
    [CommSemiring σ] [Algebra R σ]
    (f : Fin n → σ) :
    CMvPolynomial.aeval f (0 : CMvPolynomial n R) = 0 := by
  rw [CMvPolynomial.aeval_eq_eval₂]
  exact (CMvPolynomial.eval₂Hom (algebraMap R σ) f).map_zero

@[simp] lemma CMvPolynomial.aeval_one {R σ : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R]
    [CommSemiring σ] [Algebra R σ]
    (f : Fin n → σ) :
    CMvPolynomial.aeval f (1 : CMvPolynomial n R) = 1 := by
  rw [CMvPolynomial.aeval_eq_eval₂]
  exact (CMvPolynomial.eval₂Hom (algebraMap R σ) f).map_one

@[simp] lemma CMvPolynomial.aeval_neg {R σ : Type*}
    [CommRing R] [BEq R] [LawfulBEq R]
    [CommRing σ] [Algebra R σ]
    (f : Fin n → σ) (p : CMvPolynomial n R) :
    CMvPolynomial.aeval f (-p) = -(CMvPolynomial.aeval f p) := by
  rw [CMvPolynomial.aeval_eq_eval₂, CMvPolynomial.aeval_eq_eval₂]
  exact (CMvPolynomial.eval₂Hom (algebraMap R σ) f).map_neg p

@[simp] lemma CMvPolynomial.aeval_sub {R σ : Type*}
    [CommRing R] [BEq R] [LawfulBEq R]
    [CommRing σ] [Algebra R σ]
    (f : Fin n → σ) (p q : CMvPolynomial n R) :
    CMvPolynomial.aeval f (p - q)
      = CMvPolynomial.aeval f p - CMvPolynomial.aeval f q := by
  rw [CMvPolynomial.aeval_eq_eval₂, CMvPolynomial.aeval_eq_eval₂,
      CMvPolynomial.aeval_eq_eval₂]
  exact (CMvPolynomial.eval₂Hom (algebraMap R σ) f).map_sub p q

/-! ### Soundness theorems -/

/-- A square is non-negative under any algebra evaluation into a linearly
ordered ring. -/
private theorem aeval_sq_nonneg (φ : Fin n → ℝ) (q : CMvPolynomial n ℚ) :
    0 ≤ CMvPolynomial.aeval φ (q * q) := by
  rw [CMvPolynomial.aeval_mul]
  exact mul_self_nonneg _

/-- A sum of squares (built by `foldr (· + · * ·)` over a list of
polynomials) evaluates to a non-negative real. -/
theorem SOSDecomp.toPoly_aeval_nonneg (sd : SOSDecomp n) (φ : Fin n → ℝ) :
    0 ≤ CMvPolynomial.aeval φ sd.toPoly := by
  unfold SOSDecomp.toPoly
  induction sd.squares with
  | nil =>
    rw [List.foldr_nil, CMvPolynomial.aeval_zero]
  | cons q qs ih =>
    rw [List.foldr_cons, CMvPolynomial.aeval_add]
    exact add_nonneg ih (aeval_sq_nonneg φ q)

/-- The constraint sum `Σᵢ σᵢ.toPoly * gᵢ` evaluates non-negatively when
each `gᵢ` does. -/
theorem Certificate.constraintSum_aeval_nonneg
    (sigmas : List (SOSDecomp n)) (gs : List (CMvPolynomial n ℚ))
    (φ : Fin n → ℝ)
    (hgs : ∀ g ∈ gs, 0 ≤ CMvPolynomial.aeval φ g) :
    0 ≤ CMvPolynomial.aeval φ (Certificate.constraintSum sigmas gs) := by
  unfold Certificate.constraintSum
  induction sigmas generalizing gs with
  | nil =>
    rw [List.zip_nil_left, List.foldr_nil, CMvPolynomial.aeval_zero]
  | cons sd sds ih =>
    cases gs with
    | nil =>
      rw [List.zip_nil_right, List.foldr_nil, CMvPolynomial.aeval_zero]
    | cons g gs' =>
      rw [List.zip_cons_cons, List.foldr_cons, CMvPolynomial.aeval_add,
          CMvPolynomial.aeval_mul]
      refine add_nonneg ?tail ?head
      case tail =>
        apply ih
        intro g' hg'
        exact hgs g' (List.mem_cons_of_mem g hg')
      case head =>
        exact mul_nonneg
          (sd.toPoly_aeval_nonneg φ)
          (hgs g List.mem_cons_self)

/-- The certificate's full expansion evaluates non-negatively. -/
theorem Certificate.toPoly_aeval_nonneg
    (c : Certificate n) (gs : List (CMvPolynomial n ℚ)) (φ : Fin n → ℝ)
    (hgs : ∀ g ∈ gs, 0 ≤ CMvPolynomial.aeval φ g) :
    0 ≤ CMvPolynomial.aeval φ (c.toPoly gs) := by
  unfold Certificate.toPoly
  rw [CMvPolynomial.aeval_add]
  exact add_nonneg
    (c.sigma0.toPoly_aeval_nonneg φ)
    (Certificate.constraintSum_aeval_nonneg c.sigmas gs φ hgs)

/-- **Soundness, closed positivity.** -/
theorem sos_sound
    (p : CMvPolynomial n ℚ) (gs : List (CMvPolynomial n ℚ))
    (cert : Certificate n) (h : cert.checks (.closed p) gs = true) :
    ∀ φ : Fin n → ℝ,
      (∀ g ∈ gs, 0 ≤ CMvPolynomial.aeval φ g) →
      0 ≤ CMvPolynomial.aeval φ p := by
  intro φ hgs
  obtain ⟨_hlen, hid⟩ := (Certificate.checks_iff cert (.closed p) gs).mp h
  have htgt : (Goal.closed (n := n) p).target = p := rfl
  rw [htgt] at hid
  rw [hid]
  exact cert.toPoly_aeval_nonneg gs φ hgs

/-- **Soundness, strict positivity.** -/
theorem sos_strict_sound
    (p : CMvPolynomial n ℚ) (ε : ℚ) (hε : 0 < ε)
    (gs : List (CMvPolynomial n ℚ))
    (cert : Certificate n)
    (h : cert.checks (.strict p ε hε) gs = true) :
    ∀ φ : Fin n → ℝ,
      (∀ g ∈ gs, 0 ≤ CMvPolynomial.aeval φ g) →
      0 < CMvPolynomial.aeval φ p := by
  intro φ hgs
  obtain ⟨_hlen, hid⟩ := (Certificate.checks_iff cert (.strict p ε hε) gs).mp h
  have htgt : (Goal.strict (n := n) p ε hε).target = p - CMvPolynomial.C ε := rfl
  rw [htgt] at hid
  have h_diff : 0 ≤ CMvPolynomial.aeval φ (p - CMvPolynomial.C ε) := by
    rw [hid]; exact cert.toPoly_aeval_nonneg gs φ hgs
  rw [CMvPolynomial.aeval_sub, CMvPolynomial.aeval_C] at h_diff
  have hε_real : (0 : ℝ) < (algebraMap ℚ ℝ) ε := by
    rw [Algebra.algebraMap_eq_smul_one]; simpa using hε
  linarith

/-- **Soundness, infeasibility refutation.** -/
theorem sos_infeasible_sound
    (gs : List (CMvPolynomial n ℚ))
    (cert : Certificate n) (h : cert.checks .infeasible gs = true) :
    ∀ φ : Fin n → ℝ,
      ¬ ∀ g ∈ gs, 0 ≤ CMvPolynomial.aeval φ g := by
  intro φ hgs
  obtain ⟨_hlen, hid⟩ := (Certificate.checks_iff cert (.infeasible (n := n)) gs).mp h
  have htgt : (Goal.infeasible (n := n)).target = -1 := rfl
  rw [htgt] at hid
  have h_neg_one_nonneg : (0 : ℝ) ≤ CMvPolynomial.aeval φ (-1 : CMvPolynomial n ℚ) := by
    rw [hid]; exact cert.toPoly_aeval_nonneg gs φ hgs
  -- aeval φ (-1) = -1 in ℝ, by aeval_neg + aeval_one.
  rw [show ((-1 : CMvPolynomial n ℚ)) = -(1 : CMvPolynomial n ℚ) from rfl,
      CMvPolynomial.aeval_neg, CMvPolynomial.aeval_one] at h_neg_one_nonneg
  linarith

end Sos
