# Build `kim-em/sos`: Harrison's SOS tactic for Lean 4

## Context

Standalone Lake package implementing Harrison's sum-of-squares decision
procedure for nonlinear real arithmetic. Verifier-side reflective tactic
backed by external CSDP search; rational rounding + LDL-based
Gram→SOS reconstruction in Lean.

Stack:
- [`kim-em/lean-csdp`](https://github.com/kim-em/lean-csdp) (public
  Apache 2.0): FFI wrapper for CSDP 6.2.0; CI green Linux/macOS/
  Windows. Provides `LeanCsdp.solve : Problem → Solution`.
- [`Verified-zkEVM/CompPoly`](https://github.com/Verified-zkEVM/CompPoly)
  (Apache 2.0, sorry/axiom-free): `CMvPolynomial n R = Lawful n R` (a
  subtype of `Std.ExtTreeMap (CMvMonomial n) R compare` with no-zero
  invariant). Provides `aeval`, `eval₂_equiv`, `RingEquiv` to Mathlib
  `MvPolynomial`, `instDecidableEq` on `Lawful n R`.
- Mathlib: `IsSumSq.nonneg`, `ℝ`, `algebraMap ℚ ℝ`, atom infrastructure
  (`Mathlib.Util.AtomM`).

Codex review revealed five blocking issues in earlier plan iterations:
- SDP input encoding under-specified (CSDP wants block-diagonal sparse form).
- SDP output → SOS reconstruction missing (`Solution.X` is per-block
  Gram matrices, not a flat vector — need rational LDL + Lagrange
  4-square decomposition).
- `toSortedTerms` API doesn't exist in CompPoly; use `Lawful`'s
  `instDecidableEq` directly.
- `Mathlib.Tactic.Ring.parse` doesn't exist; `polyrith` is removed.
  Need bespoke reifier.
- Reification correctness theorems (relating syntax tree to Lean expr)
  were omitted entirely.

This plan addresses all five concretely.

## Verified upstream API surfaces

### lean-csdp

```lean
-- LeanCsdp/Basic.lean

structure Triple where           block : UInt32; row : UInt32; col : UInt32; value : Float
structure ConstraintTriple where constraint : UInt32; block : UInt32; row : UInt32; col : UInt32; value : Float

structure Problem where
  blockSizes     : Array Int32   -- positive = SDP block of order n; negative = LP block
  b              : Array Float   -- RHS vector, length = #constraints
  c              : Array Triple  -- cost matrix C entries (we use feasibility, so empty/zero)
  a              : Array ConstraintTriple  -- A_i entries; 1-indexed
  constantOffset : Float := 0.0

inductive Block
  | sdp  (n : Nat) (entries : FloatArray)   -- column-major n² entries
  | diag (n : Nat) (entries : FloatArray)   -- n diagonal entries

structure Solution where
  ret  : Nat              -- 0 = success
  pobj : Float
  dobj : Float
  X    : Array Block      -- primal: per-block matrices
  y    : FloatArray       -- dual: length = #constraints
  Z    : Array Block      -- dual slack

def solve (p : Problem) : Solution
```

CSDP solves: `maximise tr(C·X) s.t. tr(Aᵢ·X) = bᵢ ∧ X ⪰ 0`. For SOS we
use `c = 0` (feasibility) or add a slack-maximisation block for
strict positivity.

### CompPoly

```lean
-- CompPoly/Multivariate/CMvMonomial.lean
def CMvMonomial (n : ℕ) := Vector ℕ n        -- dense exponent vector
instance : Ord (CMvMonomial n) := …          -- lex on Vector
instance : Std.TransCmp (Ord.compare (α := CMvMonomial n))

-- CompPoly/Multivariate/Lawful.lean
def Lawful (n : ℕ) (R : Type*) [Zero R] : Type _ :=
  {p : Unlawful n R // p.isNoZeroCoef}        -- ExtTreeMap subtype

abbrev Lawful.monomials (p : Lawful n R) : List (CMvMonomial n)
instance instDecidableEq [DecidableEq R] : DecidableEq (Lawful n R)

-- CompPoly/Multivariate/CMvPolynomial.lean
abbrev CMvPolynomial (n : ℕ) (R : Type*) [Zero R] := Lawful n R
def C : R → CMvPolynomial n R                 -- constant
def X : Fin n → CMvPolynomial n R             -- variable
def coeff : CMvMonomial n → CMvPolynomial n R → R
def support : CMvPolynomial n R → Finset (Fin n →₀ ℕ)  -- via toFinsupp
def eval₂ : (R →+* S) → (Fin n → S) → CMvPolynomial n R → S
def eval  : (Fin n → R) → CMvPolynomial n R → R
@[ext, grind ext] theorem ext (h : ∀ m, coeff m p = coeff m q) : p = q

-- CompPoly/Multivariate/Operations.lean
def aeval [CommSemiring R] [CommSemiring σ] [Algebra R σ]
    (f : Fin n → σ) (p : CMvPolynomial n R) : σ := eval₂ (algebraMap R σ) f p

@[simp] lemma aeval_C   : aeval f (C c) = algebraMap R σ c
@[simp] lemma aeval_add : aeval f (p + q) = aeval f p + aeval f q
@[simp] lemma aeval_mul : aeval f (p * q) = aeval f p * aeval f q
-- aeval_X exists too; verify exact name when implementing

class MonomialOrder (n : ℕ) where compare : CMvMonomial n → CMvMonomial n → Ordering
-- (no laws — TODO upstream; we don't depend on it)

-- CompPoly/Multivariate/MvPolyEquiv/Eval.lean
lemma eval₂_equiv : p.eval₂ f vals = (fromCMvPolynomial p).eval₂ f vals
-- (fromCMvPolynomial : CMvPolynomial n R → MvPolynomial (Fin n) R is the Mathlib bridge)
```

Key consequence: **polynomial equality is `Decidable` on `CMvPolynomial n ℚ`** via `Lawful.instDecidableEq` (since `ℚ` has `DecidableEq`). No need for `toSortedTerms`. `cbv_decide` can compute it directly through the underlying `ExtTreeMap` operations.

`ExtTreeMap` is a quotient, but `Lawful` is a *subtype* — so structural equality on `Lawful` reduces to extensional `ExtTreeMap` equality (which is the quotient's `=`), which CompPoly proves decidable. We use that instance.

## Repository setup

`kim-em/sos`, public, Apache 2.0. Single Lake package.

```
sos/
├── PLAN.md                       ← this plan
├── README.md                     ← user-facing usage
├── LICENSE                       ← Apache 2.0
├── lakefile.lean                 ← deps: lean-csdp, CompPoly, Mathlib
├── lean-toolchain                ← matches CompPoly current (4.29.1)
├── lake-manifest.json
├── .gitignore
├── .github/workflows/ci.yml      ← Linux + macOS + Windows
├── Sos.lean                      ← root re-export
└── Sos/
    ├── Atoms.lean                ← atom valuation type, lookup theorems
    ├── Raw.lean                  ← Poly.Raw AST + denotation
    ├── Reify.lean                ← reify: Lean.Expr → Poly.Raw + valuation proof
    ├── Certificate.lean          ← Goal, SOSDecomp, Certificate, checks
    ├── Verifier.lean             ← sos_sound + variants (proof skeletons)
    ├── LDL.lean                  ← rational LDL decomposition + 4-square Lagrange
    ├── Search.lean               ← buildSdp (SDP encoding), runSearch
    ├── Tactic.lean               ← sos / sos_witness syntax + elaborators
    └── Examples.lean             ← worked examples + smoke test
```

## v1 scope (locked)

**In:** Goals over `∀ x : Fin n → ℝ`. Atoms: `x i` for the bound
variable plus rational literals. Hypotheses: `0 ≤ g x`, `g x ≤ 0`,
`g x = 0` (with `g` a polynomial in atoms). Three goal shapes:

```
∀ x : Fin n → ℝ, (g₁ x ≥ 0) → … → (gₘ x ≥ 0) → p x ≥ 0   -- closed
∀ x : Fin n → ℝ, (g₁ x ≥ 0) → … → (gₘ x ≥ 0) → p x > 0   -- strict
∀ x : Fin n → ℝ, (g₁ x ≥ 0) → … → (gₘ x ≥ 0) → False     -- infeasibility
```

**Out:** strict hypotheses (`g > 0`), non-`Fin n → ℝ` quantification,
non-rational atoms (`Real.sqrt`, etc), preprocessing (`field_simp`,
`1/x`-style goals), `Polynomial`-shaped goals via Mathlib
`Polynomial`. All fall through with a `trace[sos]` note. Documented
in README.

This matches Codex's "reduced v1 goal language" recommendation.

## Files in detail

### `Sos/Atoms.lean`

```lean
namespace Sos

/-- Atom valuation: a finite list of real-valued expressions. -/
structure AtomTable where
  atoms : Array Lean.Expr     -- atoms.size = number of atoms in scope

def AtomTable.size (t : AtomTable) : Nat := t.atoms.size

end Sos
```

Pure data; semantic content is owned by `Sos/Raw.lean`'s `eval`.

### `Sos/Raw.lean`

```lean
namespace Sos.Poly

inductive Raw where
  | const : ℚ → Raw
  | var   : ℕ → Raw                      -- atom index
  | neg   : Raw → Raw
  | add   : Raw → Raw → Raw
  | sub   : Raw → Raw → Raw
  | mul   : Raw → Raw → Raw
  | pow   : Raw → ℕ → Raw
  deriving Inhabited, Repr

/-- Maximum atom index referenced. -/
def Raw.maxAtom : Raw → ℕ
  | .const _   => 0
  | .var i     => i + 1
  | .neg p     => p.maxAtom
  | .add p q | .sub p q | .mul p q => max p.maxAtom q.maxAtom
  | .pow p _   => p.maxAtom

/-- Real-valued denotation under a valuation φ : ℕ → ℝ. -/
def Raw.eval (φ : ℕ → ℝ) : Raw → ℝ
  | .const r   => (r : ℝ)
  | .var i     => φ i
  | .neg p     => -p.eval φ
  | .add p q   => p.eval φ + q.eval φ
  | .sub p q   => p.eval φ - q.eval φ
  | .mul p q   => p.eval φ * q.eval φ
  | .pow p k   => p.eval φ ^ k

end Sos.Poly

/-- Indexed (n-variable) version of `Raw`. -/
inductive Sos.Poly (n : ℕ) where
  | const : ℚ → Poly n
  | var   : Fin n → Poly n
  | neg   : Poly n → Poly n
  | add sub mul : Poly n → Poly n → Poly n
  | pow   : Poly n → ℕ → Poly n

/-- Cast Raw into the typed Poly n once n is known to bound all atom indices. -/
def Sos.Poly.Raw.cast (n : ℕ) (r : Raw) (h : r.maxAtom ≤ n) : Sos.Poly n
  -- Fin.mk construction; structural recursion.

/-- Convert typed Poly to a CompPoly polynomial via C and X. -/
def Sos.Poly.toCMv {n : ℕ} : Sos.Poly n → CompPoly.CMvPolynomial n ℚ
  | .const r   => CompPoly.CMvPolynomial.C r
  | .var i     => CompPoly.CMvPolynomial.X i
  | .neg p     => -p.toCMv
  | .add p q   => p.toCMv + q.toCMv
  | .sub p q   => p.toCMv - q.toCMv
  | .mul p q   => p.toCMv * q.toCMv
  | .pow p k   => p.toCMv ^ k

/-- Real-valued denotation of typed Poly under a Fin n → ℝ valuation. -/
def Sos.Poly.evalReal {n : ℕ} (φ : Fin n → ℝ) : Sos.Poly n → ℝ
  | .const r   => (r : ℝ)
  | .var i     => φ i
  | .neg p     => -p.evalReal φ
  | .add p q   => p.evalReal φ + q.evalReal φ
  | .sub p q   => p.evalReal φ - q.evalReal φ
  | .mul p q   => p.evalReal φ * q.evalReal φ
  | .pow p k   => p.evalReal φ ^ k

/-- The crucial reflection theorem: typed-Poly evaluation matches
    aeval over the algebra map ℚ → ℝ. -/
theorem Sos.Poly.evalReal_eq_aeval {n : ℕ} (φ : Fin n → ℝ) (p : Sos.Poly n) :
    p.evalReal φ = (CompPoly.CMvPolynomial.aeval φ p.toCMv : ℝ) := by
  induction p with
  | const r   => simp [evalReal, toCMv, CompPoly.CMvPolynomial.aeval_C, algebraMap]
  | var i     => simp [evalReal, toCMv, /- aeval_X -/]
  | neg p ih  => simp [evalReal, toCMv, /- aeval_neg -/, ih]
  | add p q ihp ihq => simp [evalReal, toCMv, CompPoly.CMvPolynomial.aeval_add, ihp, ihq]
  | sub p q ihp ihq => simp [evalReal, toCMv, /- aeval_sub -/, ihp, ihq]
  | mul p q ihp ihq => simp [evalReal, toCMv, CompPoly.CMvPolynomial.aeval_mul, ihp, ihq]
  | pow p k ih      => simp [evalReal, toCMv, /- aeval_pow -/, ih]

/-- Raw evaluation under a Fin n-valuation lifted from φ : Fin n → ℝ
    matches typed evaluation. -/
theorem Sos.Poly.Raw.eval_cast {n : ℕ} (r : Raw) (h : r.maxAtom ≤ n) (φ : Fin n → ℝ) :
    r.eval (fun i => if h' : i < n then φ ⟨i, h'⟩ else 0)
      = (r.cast n h).evalReal φ := by
  induction r generalizing h <;> simp [Raw.eval, Raw.cast, evalReal] <;> grind
```

**Honest LOC budget**: ~150 lines. The two reflection theorems are
the load-bearing piece. Codex's blocker (5) addressed.

### `Sos/Reify.lean`

```lean
namespace Sos.Reify

open Lean Meta Elab Tactic

-- Atom is canonicalised by definitional equality up to `reducible`.
/-- Reify state: maps atom Lean.Expr to ℕ index. -/
structure ReifyState where
  atoms : Array Expr := #[]      -- ordered list; index = position

abbrev ReifyM := StateRefT ReifyState MetaM

/-- Look up or insert an atom; returns its index. -/
def addAtom (e : Expr) : ReifyM ℕ := do
  let st ← get
  -- Linear search up to definitional equality (small atom counts in practice).
  for i in [0:st.atoms.size] do
    if ← isDefEq st.atoms[i]! e then return i
  modify fun st => { st with atoms := st.atoms.push e }
  return st.atoms.size

/-- Walk a `Q(ℝ)` expression, building Poly.Raw and proving denotation
    along the way. Returns:
    (raw, pf) where pf : e = raw.eval ⟨atomTable lookup⟩. -/
partial def reifyExpr (e : Expr) : ReifyM (Poly.Raw × Expr) := do
  -- Match arithmetic constructors on ℝ:
  -- HAdd.hAdd, HSub.hSub, HMul.hMul, HPow.hPow (with Nat exponent),
  -- Neg.neg, OfNat.ofNat (for rational literals), HDiv.hDiv (rationals only),
  -- intCast / natCast / ratCast.
  match_expr e with
  | HAdd.hAdd α _ _ _ a b =>
    let (ra, pfa) ← reifyExpr a
    let (rb, pfb) ← reifyExpr b
    return (.add ra rb, /- combine pfa, pfb to produce e = (ra.add rb).eval φ -/)
  | HMul.hMul α _ _ _ a b => …
  | HSub.hSub α _ _ _ a b => …
  | HPow.hPow α _ _ _ a k =>
    -- only natural-number exponents
    let some kNat ← getNatLit? k | failOnNonPolynomial e
    let (ra, pfa) ← reifyExpr a
    return (.pow ra kNat, …)
  | Neg.neg α _ a => …
  | _ =>
    -- Rational literals: handle ratCast / intCast / natCast / OfNat patterns.
    if let some r ← getRatLit? e then
      return (.const r, /- reflexivity proof -/)
    -- Otherwise atomise.
    let i ← addAtom e
    return (.var i, /- atom valuation lookup -/)

/-- Helpers, not shown: getNatLit?, getRatLit?, failOnNonPolynomial. -/

/-- Top-level: reify a goal of shape `∀ x : Fin n → ℝ, (g₁ ≥ 0) → … → p ⊳ 0`.
    Returns the bound n, the reified `Poly n` polynomials, and a
    `Reflect` bundle carrying the proofs needed to close the goal. -/
def parseGoal (g : MVarId) :
    MetaM (Σ n, ParsedGoal n) := do
  let target ← g.getType >>= instantiateMVars
  -- 1. Strip the outer ∀-binder for `x : Fin n → ℝ` (we only support this exact shape).
  -- 2. Strip the chain of constraint hypotheses (g i ≥ 0) → ….
  -- 3. Extract conclusion (p ≥ 0 / p > 0 / False).
  -- 4. For each polynomial p / gᵢ: run reifyExpr under a fresh ReifyM state,
  --    keyed so atoms are exactly `x ⟨0, _⟩, x ⟨1, _⟩, …, x ⟨n-1, _⟩` and
  --    nothing else. Reject if any other atom appears.
  -- 5. Cast all Poly.Raw values to Poly n with bound n = #atoms.
  …

structure ParsedGoal (n : ℕ) where
  goal     : Sos.Goal n             -- Goal type from Certificate.lean
  gs       : List (Sos.Poly n)
  reifyPf  : Expr   -- proof: target = ∀ φ, (∀ i, gs[i].evalReal φ ≥ 0) → goal.targetProp φ

end Sos.Reify
```

**Atom restriction**: v1 only allows atoms that match `x ⟨i, _⟩` for
the bound variable `x`. Any other atom (including other free
variables, transcendental terms, etc.) causes `parseGoal` to fall
through with a `trace[sos]` note. This is Codex's recommended
"reduced v1 goal language."

**Honest LOC budget**: ~350 lines. Codex's blocker (4) addressed —
bespoke reifier, no `Mathlib.Tactic.Ring.parse` dependency. Uses
`StateRefT MetaM` directly (simpler than full `AtomM`).

### `Sos/Certificate.lean`

```lean
namespace Sos

open CompPoly

/-- A list of polynomials whose sum-of-squares we treat as a witness. -/
structure SOSDecomp (n : ℕ) where
  squares : List (CMvPolynomial n ℚ)
  deriving Repr

def SOSDecomp.toPoly {n} (sd : SOSDecomp n) : CMvPolynomial n ℚ :=
  sd.squares.foldr (fun q acc => acc + q * q) 0

/-- Goal shape, with all data needed to reconstruct the proof. -/
inductive Goal (n : ℕ) where
  /-- p ≥ 0 -/
  | closed     (p : CMvPolynomial n ℚ)
  /-- p > 0, certified via p − ε ≥ 0 with ε > 0. -/
  | strict     (p : CMvPolynomial n ℚ) (epsilon : ℚ) (hε : 0 < epsilon)
  /-- The constraint set is infeasible; certified via −1 = σ₀ + Σ σᵢ gᵢ. -/
  | infeasible

/-- The polynomial we certify against the constraint set. -/
def Goal.target {n} : Goal n → CMvPolynomial n ℚ
  | .closed p     => p
  | .strict p ε _ => p - CMvPolynomial.C ε
  | .infeasible   => -1

/-- Positivstellensatz certificate. -/
structure Certificate (n : ℕ) where
  sigma0 : SOSDecomp n
  -- One pair per constraint gᵢ; σᵢ.toPoly · gᵢ contributes to the sum.
  sigmas : List (SOSDecomp n × CMvPolynomial n ℚ)

/-- The polynomial expansion of the certificate. -/
def Certificate.toPoly {n} (c : Certificate n) : CMvPolynomial n ℚ :=
  c.sigma0.toPoly +
  (c.sigmas.foldr (fun ⟨sd, gᵢ⟩ acc => acc + sd.toPoly * gᵢ) 0)

/-- Certificate check: matches the goal's target polynomial against the
    expansion, and verifies the constraint list lines up with the
    certificate's σᵢ list. Uses Lawful's instDecidableEq via decide,
    which is computational on Lawful (subtype of ExtTreeMap). -/
def Certificate.checks {n} (c : Certificate n) (goal : Goal n)
    (gs : List (CMvPolynomial n ℚ)) : Bool :=
  -- gs and c.sigmas are paired by position.
  (c.sigmas.length == gs.length) &&
  (c.sigmas.zip gs |>.all (fun ⟨⟨_, cgᵢ⟩, gᵢ⟩ => cgᵢ == gᵢ)) &&
  (decide (goal.target = c.toPoly))

/-- The bridge lemma: checks = true iff the polynomial identity holds. -/
theorem Certificate.checks_iff_eq {n} (c : Certificate n) (goal : Goal n)
    (gs : List (CMvPolynomial n ℚ)) :
    c.checks goal gs = true ↔
      (c.sigmas.length = gs.length) ∧
      (∀ i (h : i < gs.length),
         c.sigmas[i]'(by omega) |>.snd = gs[i]) ∧
      goal.target = c.toPoly := by
  simp [checks, decide_eq_true_eq]

end Sos
```

**Honest LOC budget**: ~80 lines. No `toSortedTerms` — uses `Lawful`'s
direct `DecidableEq` via `decide`. Codex's blocker (3) addressed.

### `Sos/Verifier.lean`

```lean
namespace Sos

open CompPoly

/-- Sum of squares (under any commutative ring) is nonneg in any ordered
    field reached by an algebra map. -/
theorem SOSDecomp.toPoly_aeval_nonneg {n} (sd : SOSDecomp n) (φ : Fin n → ℝ) :
    0 ≤ CMvPolynomial.aeval φ sd.toPoly := by
  unfold SOSDecomp.toPoly
  induction sd.squares with
  | nil => simp [CMvPolynomial.aeval_zero]      -- aeval 0 = 0; 0 ≤ 0
  | cons q qs ih =>
    simp only [List.foldr_cons]
    rw [CMvPolynomial.aeval_add, CMvPolynomial.aeval_mul]
    exact add_nonneg (mul_self_nonneg _) ih

/-- Closed positivity. -/
theorem sos_sound {n}
    (p : CMvPolynomial n ℚ) (gs : List (CMvPolynomial n ℚ))
    (cert : Certificate n) (h : cert.checks (.closed p) gs = true) :
    ∀ φ : Fin n → ℝ,
      (∀ i (hi : i < gs.length),
        0 ≤ CMvPolynomial.aeval φ (gs[i]'hi)) →
      0 ≤ CMvPolynomial.aeval φ p := by
  intro φ hgs
  obtain ⟨hlen, hpair, hid⟩ := (Certificate.checks_iff_eq _ _ _).mp h
  -- After hid: p = sigma0.toPoly + Σᵢ σᵢ.toPoly * gᵢ
  -- Goal: 0 ≤ aeval φ p
  rw [show p = cert.toPoly from hid]            -- rewrite via the identity
  rw [Certificate.toPoly]
  rw [CMvPolynomial.aeval_add]
  refine add_nonneg ?_ ?_
  · exact cert.sigma0.toPoly_aeval_nonneg φ
  · -- Σ σᵢ * gᵢ part: each summand is nonneg.
    induction h_pairs : cert.sigmas.zip gs generalizing /- … -/ with
    | nil => simp
    | cons head tail ih =>
      rw [List.foldr_cons, CMvPolynomial.aeval_add, CMvPolynomial.aeval_mul]
      refine add_nonneg ?_ ?_
      · exact mul_nonneg (head.fst.toPoly_aeval_nonneg φ)
                          (hgs /- index of head -/ /- bound -/)
      · exact ih /- … -/

/-- Strict positivity: p > 0 via p − ε ≥ 0 with ε > 0. -/
theorem sos_strict_sound {n}
    (p : CMvPolynomial n ℚ) (ε : ℚ) (hε : 0 < ε)
    (gs : List (CMvPolynomial n ℚ))
    (cert : Certificate n) (h : cert.checks (.strict p ε hε) gs = true) :
    ∀ φ : Fin n → ℝ,
      (∀ i (hi : i < gs.length),
        0 ≤ CMvPolynomial.aeval φ (gs[i]'hi)) →
      0 < CMvPolynomial.aeval φ p := by
  intro φ hgs
  -- The certificate proves (p - C ε) ≥ 0 over the constraint set.
  -- Hence p ≥ C ε in ℝ. Combined with C ε > 0 (from algebraMap_pos hε),
  -- we get p > 0.
  have h_diff : 0 ≤ CMvPolynomial.aeval φ (p - CMvPolynomial.C ε) :=
    sos_sound (p - CMvPolynomial.C ε) gs cert h φ hgs
  rw [CMvPolynomial.aeval_sub, CMvPolynomial.aeval_C] at h_diff
  -- h_diff : 0 ≤ aeval φ p - (algebraMap ℚ ℝ ε)
  have hε_real : (0 : ℝ) < (algebraMap ℚ ℝ) ε := by
    simpa using (Rat.cast_pos.mpr hε)
  linarith

/-- Infeasibility: from a `−1 = σ₀ + Σ σᵢ gᵢ` certificate, derive False
    given any constraint-satisfying φ. -/
theorem sos_infeasible_sound {n}
    (gs : List (CMvPolynomial n ℚ))
    (cert : Certificate n) (h : cert.checks .infeasible gs = true) :
    ∀ φ : Fin n → ℝ,
      ¬ (∀ i (hi : i < gs.length),
          0 ≤ CMvPolynomial.aeval φ (gs[i]'hi)) := by
  intro φ hgs
  -- Apply sos_sound with goal = .closed (-1):
  -- but checks .infeasible hands us cert.toPoly = -1, so applying
  -- sos_sound shape directly gives 0 ≤ aeval φ (-1) = -1, contradiction.
  …

end Sos
```

**Honest LOC budget**: ~140 lines. Codex's blocker (5) and serious-9
addressed: no quotient detour, just direct `aeval` reasoning + the
`checks_iff_eq` bridge.

### `Sos/LDL.lean`

Rational LDLᵀ decomposition + Lagrange 4-square decomposition. **No
proofs needed — these are pure executable algorithms; their output is
checked by the verifier downstream.**

```lean
namespace Sos.LDL

/-- Rational LDLᵀ decomposition of a symmetric matrix. Input is the
    upper triangle as a flat array indexed (i, j) with i ≤ j by
    `(2*n - i - 1) * i / 2 + j`. Output is L (lower-unit-triangular,
    n×n) and D (n nonneg rationals). Returns `none` if the matrix
    is not PSD. -/
def decompose (n : ℕ) (upperTri : Array ℚ) : Option (Array (Array ℚ) × Array ℚ)
  -- Standard textbook LDL. ~50 lines.

/-- Lagrange 4-square decomposition for a positive rational.
    For r = p/q with p, q : ℕ, p > 0, q > 0:
    1. Compute pq.
    2. Find a, b, c, d : ℤ with a² + b² + c² + d² = pq.
       (Rabin-Shallit randomised, or exhaustive search for small inputs.)
    3. Return (a/q, b/q, c/q, d/q) so r = (a/q)² + … + (d/q)². -/
def fourSquares (r : ℚ) (hr : 0 ≤ r) : Array ℚ
  -- ~80 lines. For tests in v1 we accept slow algorithms; SDP problems
  -- typically yield diagonal entries with small denominators.

/-- Combined: given a PSD rational matrix Q (n×n) and a basis vector
    of monomials z (n entries), produce a list of polynomial squares
    whose sum equals zᵀ Q z. -/
def reconstruct {n_vars} (n : ℕ) (Q : Array ℚ)         -- upper triangle
    (basis : Array (CompPoly.CMvPolynomial n_vars ℚ))  -- z
    : Option (List (CompPoly.CMvPolynomial n_vars ℚ)) := do
  let (L, D) ← decompose n Q
  -- For each i: D[i] · ((Lᵀ z)[i])² = Σⱼ (cᵢⱼ · (Lᵀ z)[i])² where
  --   cᵢⱼ are the 4-square decomposition of D[i] over q-cleared form.
  -- Compute Lᵀ z as polynomials, then for each i, expand into 4 squares.
  let Ltz : Array (CompPoly.CMvPolynomial n_vars ℚ) := …  -- (Lᵀ · z)
  let mut squares := []
  for i in [0:n] do
    let coeffs := fourSquares D[i]! (by ⟨…⟩)
    for c in coeffs do
      squares := squares ++ [CompPoly.CMvPolynomial.C c * Ltz[i]!]
  return squares

end Sos.LDL
```

**Honest LOC budget**: ~250 lines. Codex's blocker (1) addressed.

### `Sos/Search.lean`

```lean
namespace Sos.Search

open LeanCsdp CompPoly

/-- Monomial basis used by σ₀: all monomials of total degree ≤ ⌈deg(p)/2⌉. -/
def Sos.Search.basis (n : ℕ) (deg : ℕ) : Array (CMvMonomial n) :=
  -- All vectors v : Fin n → ℕ with sum v ≤ deg/2.
  -- ~30 lines via stars-and-bars enumeration.
  …

/-- Encode the SDP for a Putinar Positivstellensatz problem.

    For closed positivity (p ≥ 0 over {gᵢ ≥ 0}):
    - One SDP block per multiplier:
      block 0 = σ₀ (size = |basis(deg(p))|),
      block i = σᵢ for gᵢ (size = |basis(deg(p) - deg(gᵢ))|).
    - Decision variables = upper-triangle entries of each Q block.
    - Each monomial m in the support of p contributes one equality
      constraint: coefficient of m in p must equal coefficient of m
      in σ₀.expand + Σ σᵢ.expand · gᵢ. We encode this as a row
      of the A matrix: which Q[i,j] entries (across all blocks)
      contribute to monomial m, with what factor.
    - b[m] = (coefficient of m in p) − (constant contribution from … if any).
    - Cost matrix C = 0 (feasibility). For strict positivity, add a
      slack variable λ ≥ 0 in an LP block, replace target with
      p − C λ on the equality side, set C = -e_λ (max λ = min -λ).

    Returns the Problem plus a "decoding map" specifying which
    block-and-(i,j) corresponds to which monomial pair, used by
    `decode`. -/
def buildSdp (goal : Goal n) (gs : List (CMvPolynomial n ℚ)) :
    Problem × DecodingMap := …

/-- Decode CSDP's `Solution.X` array into per-block rational Gram
    matrices, applying denominator-schedule rounding. -/
def roundGramMatrices (sol : Solution) (denom : ℚ) :
    Array (Array ℚ) := …
  -- For each Block in sol.X:
  --   if .sdp n entries: extract upper triangle as flat Array ℚ
  --                       via niceRound denom
  --   if .diag n entries: similar.

/-- Top-level search driver. -/
def runSearch (goal : Goal n) (gs : List (CMvPolynomial n ℚ)) :
    IO (Option (Certificate n)) := do
  let (prob, decMap) := buildSdp goal gs
  let sol := LeanCsdp.solve prob
  if sol.ret ≠ 0 then
    IO.println s!"sos: csdp failed (ret = {sol.ret})"
    return none
  -- For each denominator d in the schedule:
  for d in niceDenominators do
    let Qs := roundGramMatrices sol d
    -- For each Qᵢ: run LDL.reconstruct.
    let some sigma0Squares := LDL.reconstruct (basis 0).size Qs[0]! (basis 0) | continue
    let mut sigmas := []
    let mut ok := true
    for i in [1 : Qs.size] do
      match LDL.reconstruct …, gs[i-1]! with
      | some sqs, gᵢ => sigmas := sigmas ++ [(⟨sqs⟩, gᵢ)]
      | none, _ => ok := false; break
    unless ok do continue
    let cert : Certificate n := ⟨⟨sigma0Squares⟩, sigmas⟩
    if cert.checks goal gs then return some cert
  return none

def niceDenominators : List ℚ :=
  -- 1, 2, …, 31, 2^5, 2^6, …, 2^66
  …

end Sos.Search
```

**Honest LOC budget**: ~300 lines. Codex's blocker (2) addressed —
explicit block layout, explicit constraint encoding.

### `Sos/Tactic.lean`

```lean
namespace Sos

syntax (name := sosTactic)        "sos"          : tactic
syntax (name := sosWitnessTactic) "sos_witness " term : tactic

open Lean Elab Tactic Meta

elab_rules : tactic
  | `(tactic| sos) => do
    let g ← getMainGoal
    let some ⟨n, parsed⟩ ← (Sos.Reify.parseGoal g).run' { atoms := #[] } |
      throwError "sos: goal shape not recognised"
    let some cert ← (Sos.Search.runSearch parsed.goal parsed.gs).run | …
    -- Build the proof term:
    --   sos_sound parsed.goal.p parsed.gs cert (by decide) φ_proof gs_proofs
    -- where decide closes cert.checks goal gs = true.
    let proof ← buildProof parsed cert
    g.assign proof

elab_rules : tactic
  | `(tactic| sos_witness $cert:term) => do
    -- Same shape, but cert is supplied literally.
    …

end Sos
```

**Honest LOC budget**: ~120 lines.

### `Sos/Examples.lean`

```lean
namespace Sos.Examples

open CompPoly

-- Closed positivity:
example : ∀ x : Fin 2 → ℝ, 0 ≤ (x 0)^2 + 2*(x 0)*(x 1) + (x 1)^2 := by sos
example : ∀ x : Fin 1 → ℝ, 0 ≤ ((x 0) - 1)^2 := by sos

-- Strict positivity:
example : ∀ x : Fin 1 → ℝ, 0 < (x 0)^2 + 1 := by sos

-- Infeasibility:
example : ∀ x : Fin 1 → ℝ, ¬ ((x 0)^2 + 1 ≤ 0) := by sos

-- Constrained:
example : ∀ x : Fin 1 → ℝ, 0 ≤ x 0 → 0 ≤ (x 0)^2 - x 0 + 1/4 := by sos

-- Negative case (Motzkin): should fall through, not produce wrong proof.
example : ∀ x : Fin 2 → ℝ,
    0 ≤ (x 0)^4 * (x 1)^2 + (x 0)^2 * (x 1)^4 + 1 - 3*(x 0)^2*(x 1)^2 := by
  fail_if_success sos        -- documents fall-through; user proves manually

end Sos.Examples
```

## Implementation order

1. **Repo + scaffolding** (commit 1): `gh repo create kim-em/sos --public --license=Apache-2.0`. Initialise `lakefile.lean`, `lean-toolchain` matching CompPoly's, `lake-manifest.json`, `.gitignore`, `README.md` (skeleton), `LICENSE`. CI workflow mirroring lean-csdp's three-platform setup.

2. **`Sos/Atoms.lean` + `Sos/Raw.lean`** (commit 2): the AST and reflection theorems. ~150 lines. `lake build` passes.

3. **`Sos/Certificate.lean`** (commit 3): types + checks. ~80 lines. Builds.

4. **`Sos/Verifier.lean`** (commit 4): three soundness theorems. ~140 lines. Builds.

5. **`Sos/LDL.lean`** (commit 5): rational LDL + 4-square. ~250 lines. Unit-tested via `#eval` examples.

6. **`Sos/Search.lean`** (commit 6): SDP encoding + Gram-matrix decoding. ~300 lines. Smoke-tested with a simple problem (`x²+1>0`).

7. **`Sos/Reify.lean`** (commit 7): bespoke reifier with valuation theorems. ~350 lines. Tested with `parseGoal` on Examples-style goals.

8. **`Sos/Tactic.lean` + `Sos/Examples.lean`** (commit 8): tactic surface + worked examples. ~120 + ~50 lines. End-to-end test.

9. **CI green** (commit 9 if needed): platform fixes.

10. **Polish**: README with usage example. Tag `v0.1`.

## Verification

- `lake build` clean on Linux + macOS + Windows in CI.
- `Sos/Examples.lean` end-to-end via `lake env lean Sos/Examples.lean` (or as a `lean_exe` smoke test).
- Negative cases (Motzkin) provably fall through — `fail_if_success sos` succeeds.
- Final code is sorry-free and axiom-free (`grep -rn '\bsorry\b\|^\s*axiom' Sos/` empty).

## End state

Public Apache-2.0 repo `kim-em/sos`. Tactic available as
`by sos`. Total ~1500 Lean lines (up from earlier "1000-line" estimate;
the difference is explicit reflection theorems + the LDL/4-square
algorithm + concrete SDP encoding).

The key honesty correction from earlier iterations: this is **a few
days of focused work**, not "single-shot in one session" as the
previous plan implied. Each of LDL.lean, Search.lean, and Reify.lean
is a meaningful chunk with its own design choices and debug cycles.
But all three are now concretely scoped — none is "fill in the
blanks."
