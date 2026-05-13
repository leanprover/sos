/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Soundness theorems for SOS certificates.
-/
import SOS.Certificate
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Linarith

namespace SOS

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

@[simp] lemma CMvPolynomial.aeval_pow {R σ : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R]
    [CommSemiring σ] [Algebra R σ]
    (f : Fin n → σ) (p : CMvPolynomial n R) (k : ℕ) :
    CMvPolynomial.aeval f (p ^ k) = (CMvPolynomial.aeval f p) ^ k := by
  rw [CMvPolynomial.aeval_eq_eval₂, CMvPolynomial.aeval_eq_eval₂]
  exact (CMvPolynomial.eval₂Hom (algebraMap R σ) f).map_pow p k

/-! ### Reflection: typed AST evaluation matches CMvPolynomial aeval -/

/-- The bridge between the typed AST `SOS.Poly n` and CompPoly's
`CMvPolynomial n ℚ`: evaluating the AST in `ℝ` agrees with evaluating
its `CMvPolynomial` image via `aeval`. Drives the `bridgeTo` /
`bridgeFrom` elaborator helpers. -/
theorem Poly.evalReal_eq_aeval (φ : Fin n → ℝ) (p : SOS.Poly n) :
    p.evalReal φ = CMvPolynomial.aeval φ p.toCMv := by
  induction p with
  | const r =>
    simp only [Poly.evalReal, Poly.toCMv, CMvPolynomial.aeval_C]
    rfl
  | var i =>
    simp only [Poly.evalReal, Poly.toCMv, CMvPolynomial.aeval_X]
  | neg p ih =>
    rw [Poly.evalReal, Poly.toCMv, CMvPolynomial.aeval_neg, ih]
  | add p q ihp ihq =>
    rw [Poly.evalReal, Poly.toCMv, CMvPolynomial.aeval_add, ihp, ihq]
  | sub p q ihp ihq =>
    rw [Poly.evalReal, Poly.toCMv, CMvPolynomial.aeval_sub, ihp, ihq]
  | mul p q ihp ihq =>
    rw [Poly.evalReal, Poly.toCMv, CMvPolynomial.aeval_mul, ihp, ihq]
  | pow p k ih =>
    rw [Poly.evalReal, Poly.toCMv, CMvPolynomial.aeval_pow, ih]

/-! ### Bridge lemmas for the elaborator

These two lemmas package the round-trip between user-side arithmetic
expressions and `aeval x p.toCMv`-form goals fed to `sos_sound`. -/

/-- Bring a hypothesis `0 ≤ origExpr` into `0 ≤ aeval x p.toCMv` form, given
a proof `evalReal x p = origExpr` (typically by `simp [evalReal]; ring`). -/
theorem aeval_nonneg_of_orig
    {x : Fin n → ℝ} {p : SOS.Poly n} {e : ℝ}
    (h_eq : SOS.Poly.evalReal x p = e) (h : 0 ≤ e) :
    0 ≤ CMvPolynomial.aeval x p.toCMv := by
  rw [← SOS.Poly.evalReal_eq_aeval, h_eq]; exact h

/-- Bring a hypothesis `0 < origExpr` into `0 < aeval x p.toCMv` form,
mirroring `aeval_nonneg_of_orig`. Used by the strict-product Positivstellensatz
path which needs *strict* positivity of each strict hypothesis. -/
theorem aeval_pos_of_orig
    {x : Fin n → ℝ} {p : SOS.Poly n} {e : ℝ}
    (h_eq : SOS.Poly.evalReal x p = e) (h : 0 < e) :
    0 < CMvPolynomial.aeval x p.toCMv := by
  rw [← SOS.Poly.evalReal_eq_aeval, h_eq]; exact h

/-- Bring a hypothesis `origExpr ≤ 0` into `0 ≤ aeval x p.toCMv` form, given
the bridge equality `evalReal x p = -origExpr`. The reifier emits
`p = -reify(origExpr)` for `≤ 0` constraints, so this matches. -/
theorem aeval_nonneg_of_orig_neg
    {x : Fin n → ℝ} {p : SOS.Poly n} {e : ℝ}
    (h_eq : SOS.Poly.evalReal x p = -e) (h : e ≤ 0) :
    0 ≤ CMvPolynomial.aeval x p.toCMv := by
  rw [← SOS.Poly.evalReal_eq_aeval, h_eq]
  exact neg_nonneg.mpr h

/-- Bring an equality hypothesis `origExpr = 0` into `aeval x p.toCMv = 0`
form, given a proof `evalReal x p = origExpr` (typically by
`simp [evalReal]; ring`). The reifier emits `p = reify(a − b)` for an
`a = b` constraint so the certified equality is again `aeval x p = 0`. -/
theorem aeval_eq_zero_of_orig
    {x : Fin n → ℝ} {p : SOS.Poly n} {e : ℝ}
    (h_eq : SOS.Poly.evalReal x p = e) (h : e = 0) :
    CMvPolynomial.aeval x p.toCMv = 0 := by
  rw [← SOS.Poly.evalReal_eq_aeval, h_eq]; exact h

/-- Take a `0 ≤ aeval x p.toCMv` proof back to the user goal `0 ≤ origExpr`,
given the same bridge equality. -/
theorem nonneg_orig_of_aeval
    {x : Fin n → ℝ} {p : SOS.Poly n} {e : ℝ}
    (h_eq : SOS.Poly.evalReal x p = e) (h : 0 ≤ CMvPolynomial.aeval x p.toCMv) :
    0 ≤ e := by
  rw [← h_eq, SOS.Poly.evalReal_eq_aeval]; exact h

/-- Strict version of `nonneg_orig_of_aeval`. -/
theorem pos_orig_of_aeval
    {x : Fin n → ℝ} {p : SOS.Poly n} {e : ℝ}
    (h_eq : SOS.Poly.evalReal x p = e) (h : 0 < CMvPolynomial.aeval x p.toCMv) :
    0 < e := by
  rw [← h_eq, SOS.Poly.evalReal_eq_aeval]; exact h

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

/-- The product `∏_{i ∈ idxs} gs[i]` (or `1` for out-of-bounds entries)
evaluates non-negatively when every `gᵢ` does. -/
theorem Certificate.constraintProduct_aeval_nonneg
    (gs : List (CMvPolynomial n ℚ)) (idxs : List Nat) (φ : Fin n → ℝ)
    (hgs : ∀ g ∈ gs, 0 ≤ CMvPolynomial.aeval φ g) :
    0 ≤ CMvPolynomial.aeval φ (Certificate.constraintProduct gs idxs) := by
  unfold Certificate.constraintProduct
  induction idxs with
  | nil =>
    rw [List.foldr_nil, CMvPolynomial.aeval_one]
    exact zero_le_one
  | cons i is ih =>
    rw [List.foldr_cons, CMvPolynomial.aeval_mul]
    refine mul_nonneg ih ?_
    -- `gs.getD i 1` is either some `g ∈ gs` (non-negative) or `1`.
    by_cases hi : i < gs.length
    · have hmem : gs.getD i 1 ∈ gs := by
        rw [List.getD_eq_getElem _ _ hi]
        exact List.getElem_mem hi
      exact hgs _ hmem
    · have : gs.getD i 1 = 1 := List.getD_eq_default _ _ (Nat.not_lt.mp hi)
      rw [this, CMvPolynomial.aeval_one]
      exact zero_le_one

/-- The monoid sum `Σ_S σ_S.toPoly · ∏_{i ∈ S} gs[i]` evaluates
non-negatively when every `gᵢ` does. -/
theorem Certificate.monoidSum_aeval_nonneg
    (sigmas : List (List Nat × SOSDecomp n))
    (gs : List (CMvPolynomial n ℚ)) (φ : Fin n → ℝ)
    (hgs : ∀ g ∈ gs, 0 ≤ CMvPolynomial.aeval φ g) :
    0 ≤ CMvPolynomial.aeval φ (Certificate.monoidSum sigmas gs) := by
  unfold Certificate.monoidSum
  induction sigmas with
  | nil =>
    rw [List.foldr_nil, CMvPolynomial.aeval_zero]
  | cons pair rest ih =>
    rw [List.foldr_cons, CMvPolynomial.aeval_add, CMvPolynomial.aeval_mul]
    refine add_nonneg ih ?_
    exact mul_nonneg
      (pair.2.toPoly_aeval_nonneg φ)
      (Certificate.constraintProduct_aeval_nonneg gs pair.1 φ hgs)

/-- The equality cofactor sum `Σⱼ qⱼ · pⱼ` evaluates to zero whenever
each `pⱼ` evaluates to zero. The cofactors `qⱼ` are unrestricted. -/
theorem Certificate.equalitySum_aeval_zero
    (eqCofs : List (CMvPolynomial n ℚ)) (ps : List (CMvPolynomial n ℚ))
    (φ : Fin n → ℝ)
    (hps : ∀ p ∈ ps, CMvPolynomial.aeval φ p = 0) :
    CMvPolynomial.aeval φ (Certificate.equalitySum eqCofs ps) = 0 := by
  unfold Certificate.equalitySum
  induction eqCofs generalizing ps with
  | nil =>
    rw [List.zip_nil_left, List.foldr_nil, CMvPolynomial.aeval_zero]
  | cons q qs ih =>
    cases ps with
    | nil =>
      rw [List.zip_nil_right, List.foldr_nil, CMvPolynomial.aeval_zero]
    | cons p ps' =>
      rw [List.zip_cons_cons, List.foldr_cons, CMvPolynomial.aeval_add,
          CMvPolynomial.aeval_mul]
      have h_p_zero : CMvPolynomial.aeval φ p = 0 :=
        hps p List.mem_cons_self
      have h_tail :
          CMvPolynomial.aeval φ
            (List.foldr (fun pair acc => acc + pair.fst * pair.snd) 0
              (qs.zip ps')) = 0 := by
        apply ih
        intro p' hp'
        exact hps p' (List.mem_cons_of_mem p hp')
      rw [h_p_zero, mul_zero, add_zero, h_tail]

/-- The certificate's full expansion
`Σ_S σ_S · ∏_{i ∈ S} gᵢ + Σⱼ qⱼ · pⱼ` evaluates non-negatively when
every `gᵢ` is non-negative and every `pⱼ` is zero. -/
theorem Certificate.toPoly_aeval_nonneg
    (c : Certificate n) (gs : List (CMvPolynomial n ℚ))
    (ps : List (CMvPolynomial n ℚ)) (φ : Fin n → ℝ)
    (hgs : ∀ g ∈ gs, 0 ≤ CMvPolynomial.aeval φ g)
    (hps : ∀ p ∈ ps, CMvPolynomial.aeval φ p = 0) :
    0 ≤ CMvPolynomial.aeval φ (c.toPoly gs ps) := by
  unfold Certificate.toPoly
  rw [CMvPolynomial.aeval_add,
      Certificate.equalitySum_aeval_zero c.eqCofs ps φ hps, add_zero]
  exact Certificate.monoidSum_aeval_nonneg c.sigmas gs φ hgs

/-- **Soundness, closed positivity, with equality hypotheses.** -/
theorem sos_sound
    (p : CMvPolynomial n ℚ) (gs : List (CMvPolynomial n ℚ))
    (ps : List (CMvPolynomial n ℚ))
    (cert : Certificate n) (h : cert.checks (.closed p) gs ps = true) :
    ∀ φ : Fin n → ℝ,
      (∀ g ∈ gs, 0 ≤ CMvPolynomial.aeval φ g) →
      (∀ q ∈ ps, CMvPolynomial.aeval φ q = 0) →
      0 ≤ CMvPolynomial.aeval φ p := by
  intro φ hgs hps
  obtain ⟨_hbounds, _hlenP, hid⟩ :=
    (Certificate.checks_iff cert (.closed p) gs ps).mp h
  have htgt : (Goal.closed (n := n) p).target = p := rfl
  rw [htgt] at hid
  rw [hid]
  exact cert.toPoly_aeval_nonneg gs ps φ hgs hps

/-- **Soundness, strict positivity, with equality hypotheses.** -/
theorem sos_strict_sound
    (p : CMvPolynomial n ℚ) (ε : ℚ) (hε : 0 < ε)
    (gs : List (CMvPolynomial n ℚ)) (ps : List (CMvPolynomial n ℚ))
    (cert : Certificate n)
    (h : cert.checks (.strict p ε hε) gs ps = true) :
    ∀ φ : Fin n → ℝ,
      (∀ g ∈ gs, 0 ≤ CMvPolynomial.aeval φ g) →
      (∀ q ∈ ps, CMvPolynomial.aeval φ q = 0) →
      0 < CMvPolynomial.aeval φ p := by
  intro φ hgs hps
  obtain ⟨_hbounds, _hlenP, hid⟩ :=
    (Certificate.checks_iff cert (.strict p ε hε) gs ps).mp h
  have htgt : (Goal.strict (n := n) p ε hε).target = p - CMvPolynomial.C ε := rfl
  rw [htgt] at hid
  have h_diff : 0 ≤ CMvPolynomial.aeval φ (p - CMvPolynomial.C ε) := by
    rw [hid]; exact cert.toPoly_aeval_nonneg gs ps φ hgs hps
  rw [CMvPolynomial.aeval_sub, CMvPolynomial.aeval_C] at h_diff
  have hε_real : (0 : ℝ) < (algebraMap ℚ ℝ) ε := by
    show (0 : ℝ) < (ε : ℝ); exact_mod_cast hε
  linarith

/-- The strict-product witness polynomial `∏ strictGs` evaluates
strictly positively when every `g ∈ strictGs` does. The base case
`strictGs = []` gives `aeval φ 1 = 1 > 0`; the inductive step combines
`mul_pos` with the head/tail of the product. -/
theorem strictProductPoly_aeval_pos
    (strictGs : List (CMvPolynomial n ℚ)) (φ : Fin n → ℝ)
    (h : ∀ g ∈ strictGs, 0 < CMvPolynomial.aeval φ g) :
    0 < CMvPolynomial.aeval φ (strictProductPoly strictGs) := by
  induction strictGs with
  | nil =>
    unfold strictProductPoly
    rw [CMvPolynomial.aeval_one]
    exact zero_lt_one
  | cons g rest ih =>
    unfold strictProductPoly
    rw [CMvPolynomial.aeval_mul]
    refine mul_pos (h g List.mem_cons_self) (ih ?_)
    intro g' hg'
    exact h g' (List.mem_cons_of_mem _ hg')

/-- **Soundness, strict positivity via strict-product Positivstellensatz.**

To prove `0 < p` against ≥-constraints `gs`, =-constraints `ps`, and
strict-positivity facts `0 < g` for each `g ∈ strictGs`, we ask for a
closed certificate of the polynomial `−(∏ strictGs)^i` against the
*augmented* inequality list `gs ++ [−p]`. Under the contrapositive
`p ≤ 0`, every entry of the augmented list is ≥ 0, so the cone term
`σ_cert ≥ 0` and the identity `−pol^i = σ_cert` force `pol^i ≤ 0` — but
`pol = ∏ strictGs > 0` from `strictProductPoly_aeval_pos`, giving
`pol^i > 0` and a contradiction. This unlocks boundary-tight strict
goals where no uniform `ε`-slack exists. -/
theorem sos_strict_product_sound
    (p : CMvPolynomial n ℚ) (strictGs : List (CMvPolynomial n ℚ))
    (exponent : Nat) (gs : List (CMvPolynomial n ℚ))
    (ps : List (CMvPolynomial n ℚ)) (cert : Certificate n)
    (h : cert.checks
            (.closed (-(strictProductPoly strictGs) ^ exponent))
            (gs ++ [-p]) ps = true) :
    ∀ φ : Fin n → ℝ,
      (∀ g ∈ gs, 0 ≤ CMvPolynomial.aeval φ g) →
      (∀ q ∈ ps, CMvPolynomial.aeval φ q = 0) →
      (∀ g ∈ strictGs, 0 < CMvPolynomial.aeval φ g) →
      0 < CMvPolynomial.aeval φ p := by
  intro φ hgs hps hstrict
  by_contra h_neg
  have h_neg : CMvPolynomial.aeval φ p ≤ 0 := not_lt.mp h_neg
  have h_negp_nonneg : 0 ≤ CMvPolynomial.aeval φ (-p) := by
    rw [CMvPolynomial.aeval_neg]; linarith
  have hgs_aug : ∀ g ∈ gs ++ [-p], 0 ≤ CMvPolynomial.aeval φ g := by
    intro g hg
    rcases List.mem_append.mp hg with hin | hin
    · exact hgs g hin
    · have : g = -p := List.mem_singleton.mp hin
      rw [this]; exact h_negp_nonneg
  have h_res :=
    sos_sound _ _ _ _ h φ hgs_aug hps
  rw [CMvPolynomial.aeval_neg, CMvPolynomial.aeval_pow] at h_res
  have h_pol_pos : 0 < CMvPolynomial.aeval φ (strictProductPoly strictGs) :=
    strictProductPoly_aeval_pos strictGs φ hstrict
  have h_pow_pos :
      0 < (CMvPolynomial.aeval φ (strictProductPoly strictGs)) ^ exponent :=
    pow_pos h_pol_pos exponent
  linarith

/-- **Soundness, infeasibility refutation, with equality hypotheses.** -/
theorem sos_infeasible_sound
    (gs : List (CMvPolynomial n ℚ)) (ps : List (CMvPolynomial n ℚ))
    (cert : Certificate n) (h : cert.checks .infeasible gs ps = true) :
    ∀ φ : Fin n → ℝ,
      (∀ g ∈ gs, 0 ≤ CMvPolynomial.aeval φ g) →
      (∀ q ∈ ps, CMvPolynomial.aeval φ q = 0) →
      False := by
  intro φ hgs hps
  obtain ⟨_hbounds, _hlenP, hid⟩ :=
    (Certificate.checks_iff cert (.infeasible (n := n)) gs ps).mp h
  have htgt : (Goal.infeasible (n := n)).target = -1 := rfl
  rw [htgt] at hid
  have h_neg_one_nonneg : (0 : ℝ) ≤ CMvPolynomial.aeval φ (-1 : CMvPolynomial n ℚ) := by
    rw [hid]; exact cert.toPoly_aeval_nonneg gs ps φ hgs hps
  rw [show ((-1 : CMvPolynomial n ℚ)) = -(1 : CMvPolynomial n ℚ) from rfl,
      CMvPolynomial.aeval_neg, CMvPolynomial.aeval_one] at h_neg_one_nonneg
  linarith

end SOS
