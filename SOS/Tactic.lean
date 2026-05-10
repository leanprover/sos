/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

`sos` and `sos_witness` tactic surface.
-/
import SOS.Reify
import SOS.Search
import SOS.Verifier
import Lean.ToExpr
import Lean.Elab.Tactic
import Lean.Meta.Tactic.TryThis
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace SOS

open Lean Elab Tactic Meta

/-! ### `SOS.Poly n` → `Lean.Expr` -/

/-- Build a `Lean.Expr` denoting the given `SOS.Poly n` value. -/
partial def Poly.toExprImpl {n : Nat} (p : SOS.Poly n) : Lean.Expr :=
  let nE : Expr := Lean.mkNatLit n
  match p with
  | .const r => mkApp2 (.const ``SOS.Poly.const []) nE (Lean.toExpr r)
  | .var i   => mkApp2 (.const ``SOS.Poly.var []) nE (Lean.toExpr i)
  | .neg p'  => mkApp2 (.const ``SOS.Poly.neg []) nE p'.toExprImpl
  | .add p' q => mkApp3 (.const ``SOS.Poly.add []) nE p'.toExprImpl q.toExprImpl
  | .sub p' q => mkApp3 (.const ``SOS.Poly.sub []) nE p'.toExprImpl q.toExprImpl
  | .mul p' q => mkApp3 (.const ``SOS.Poly.mul []) nE p'.toExprImpl q.toExprImpl
  | .pow p' k => mkApp3 (.const ``SOS.Poly.pow []) nE p'.toExprImpl (Lean.mkNatLit k)

instance Poly.instToExpr (n : Nat) : Lean.ToExpr (SOS.Poly n) where
  toExpr := Poly.toExprImpl
  toTypeExpr := Lean.mkApp (.const ``SOS.Poly []) (Lean.mkNatLit n)

/-! ### Decompiling `CMvPolynomial n ℚ` to `SOS.Poly n` -/

/-- Build the AST for a single monomial `c · Πᵢ xᵢ^(eᵢ)`. -/
def Poly.ofMonomial {n : Nat} (c : Rat) (mono : CPoly.CMvMonomial n) : SOS.Poly n :=
  Fin.foldr n (init := SOS.Poly.const c) fun i acc =>
    let e := mono[i]
    if e = 0 then acc
    else SOS.Poly.mul acc (SOS.Poly.pow (SOS.Poly.var i) e)

/-- Decompile a `CMvPolynomial n ℚ` value into a `SOS.Poly n` AST. -/
def Poly.decompile {n : Nat} (p : CPoly.CMvPolynomial n ℚ) : SOS.Poly n :=
  p.1.toList.foldr
    (fun (term : CPoly.CMvMonomial n × ℚ) (acc : SOS.Poly n) =>
      SOS.Poly.add acc (Poly.ofMonomial term.2 term.1))
    (SOS.Poly.const 0)

/-! ### Bridge equality: `evalReal x p = origExpr` -/

/-- Run a Lean tactic on a fresh metavariable of the given type and
return the resulting proof, throwing if the tactic leaves open goals. -/
private def proveByTactic (type : Expr) (tac : Syntax) : TacticM Expr := do
  let mv ← mkFreshExprSyntheticOpaqueMVar type
  let goalsBefore ← Tactic.getGoals
  Tactic.setGoals [mv.mvarId!]
  try
    Tactic.evalTactic tac
    let remaining ← Tactic.getGoals
    unless remaining.isEmpty do
      throwError "SOS.proveByTactic: tactic left open goals"
  finally
    Tactic.setGoals goalsBefore
  instantiateMVars mv

/-- Build `SOS.Poly.evalReal x p` as an `Expr`. -/
private def evalRealExpr (n : Nat) (xE : Expr) (p : SOS.Poly n) : MetaM Expr := do
  let pE := Lean.toExpr p
  mkAppOptM ``SOS.Poly.evalReal #[some (Lean.mkNatLit n), some xE, some pE]

/-- Build `(p : SOS.Poly n).toCMv` as an `Expr`. -/
private def toCMvExpr (n : Nat) (p : SOS.Poly n) : MetaM Expr := do
  let pE := Lean.toExpr p
  mkAppOptM ``SOS.Poly.toCMv #[some (Lean.mkNatLit n), some pE]

/-- Build `CMvPolynomial.aeval x p.toCMv` as an `Expr`. -/
private def aevalExpr (n : Nat) (xE : Expr) (p : SOS.Poly n) : MetaM Expr := do
  let pCMv ← toCMvExpr n p
  mkAppOptM ``CPoly.CMvPolynomial.aeval #[some (Lean.mkNatLit n),
    some (Lean.mkConst ``Rat), some (Lean.mkConst ``Real),
    none, none, none, some xE, some pCMv]

/-! ### Atomic-bridge helpers

These build the `Fin n → ℝ` valuation expression `![atom₀, …,
atomₙ₋₁]` from an atom array, and prove the bridge equation
`pTyped.evalReal φ = origExpr` where `pTyped := raw.cast n h` and `φ
:= ![…]`. The bridge proof reduces `φ ⟨k, _⟩` to `atom_k` via
`Matrix.cons_val_*` simp lemmas. -/

/-- Build `Expr` of type `Fin n → ℝ`, where `n = atoms.size`,
defined by the vector literal `![atoms[0], …, atoms[n-1]]`
(right-associated `Matrix.vecCons` chain ending in
`Matrix.vecEmpty`). -/
private def buildFinValExpr (atoms : Array Expr) : MetaM Expr := do
  let realTy := Lean.mkConst ``Real
  let n := atoms.size
  -- Tail: `Matrix.vecEmpty : Fin 0 → ℝ`.
  let mut acc : Expr ←
    mkAppOptM ``Matrix.vecEmpty #[some realTy]
  -- Right-to-left: the leftmost atom is the outermost cons. After
  -- pushing `k` atoms, `acc : Fin k → ℝ`. The next push prepends
  -- `atoms[n-1-k]`.
  for k in [:n] do
    let i := n - 1 - k
    let m := Lean.mkNatLit k  -- current length of `acc`
    acc ← mkAppOptM ``Matrix.vecCons
      #[some realTy, some m, some atoms[i]!, some acc]
  return acc

/-- Meta-compute the typed `SOS.Poly n` from a `SOS.Poly.Raw` whose
`maxAtomBound ≤ n`. The boundedness is decided at meta-time. Returns
`none` if the bound check fails. -/
private def castRawToPoly (raw : SOS.Poly.Raw) (n : Nat) :
    Option (SOS.Poly n) :=
  if h : raw.maxAtomBound ≤ n then some (raw.cast n h) else none

/-- Prove `SOS.Poly.evalReal φ p = origExpr` where `φ` is the
`![atoms[0], …]` vector. The proof uses `SOS.Poly.evalReal` plus
`Matrix.cons_val_*` to reduce `φ ⟨k, _⟩` for each literal `k`. -/
private def buildAtomicBridgeEq (n : Nat) (φE : Expr) (p : SOS.Poly n)
    (origExpr : Expr) : TacticM Expr := do
  let lhs ← evalRealExpr n φE p
  let eqType ← mkEq lhs origExpr
  let tac ← `(tactic|
    (simp only [SOS.Poly.evalReal, Matrix.cons_val_zero,
       Matrix.cons_val_succ, Matrix.cons_val_zero',
       Matrix.cons_val_succ', Fin.isValue]
     all_goals (push_cast; ring)))
  proveByTactic eqType tac

/-! ### Closed-positivity proof builder -/

/-- Build the `List (CMvPolynomial n ℚ)` expression
`[g₁.toCMv, …, gₘ.toCMv]`. -/
private def gsCMvListExpr (n : Nat) (gs : List (SOS.Poly n)) : MetaM Expr := do
  let cmvTy ← Meta.mkAppOptM ``CPoly.CMvPolynomial
    #[some (Lean.mkNatLit n), some (Lean.mkConst ``Rat), none]
  let mut acc ← mkAppOptM ``List.nil #[some cmvTy]
  for g in gs.reverse do
    let gCMv ← toCMvExpr n g
    acc ← mkAppOptM ``List.cons #[some cmvTy, some gCMv, some acc]
  return acc

/-- Build a proof of `∀ g ∈ gsList, 0 ≤ CMvPolynomial.aeval x g`, given
per-hypothesis proofs `hAevalProofs i : 0 ≤ aeval x gs[i].toCMv`. -/
private def buildForallMemProof (n : Nat) (xE : Expr) (gs : List (SOS.Poly n))
    (hAevalProofs : List Expr) : MetaM Expr := do
  let cmvTy ← Meta.mkAppOptM ``CPoly.CMvPolynomial
    #[some (Lean.mkNatLit n), some (Lean.mkConst ``Rat), none]
  -- predicate: fun g => 0 ≤ aeval x g
  let predicate ← withLocalDeclD `g cmvTy fun gFV => do
    let body ← mkAppM ``LE.le
      #[(← mkAppOptM ``OfNat.ofNat #[some (Lean.mkConst ``Real),
          some (Lean.mkNatLit 0), none]),
        (← mkAppOptM ``CPoly.CMvPolynomial.aeval
          #[some (Lean.mkNatLit n), some (Lean.mkConst ``Rat),
            some (Lean.mkConst ``Real), none, none, none, some xE, some gFV])]
    mkLambdaFVars #[gFV] body
  let mut accList ← mkAppOptM ``List.nil #[some cmvTy]
  let mut accProof ← mkAppOptM ``List.forall_mem_nil #[some cmvTy, some predicate]
  for (g, hP) in (gs.zip hAevalProofs).reverse do
    let gCMv ← toCMvExpr n g
    let newList ← mkAppOptM ``List.cons #[some cmvTy, some gCMv, some accList]
    let pair ← mkAppM ``And.intro #[hP, accProof]
    let iff ← mkAppOptM ``List.forall_mem_cons
      #[some cmvTy, some predicate, some gCMv, some accList]
    accProof ← mkAppM ``Iff.mpr #[iff, pair]
    accList := newList
  return accProof

/-- Discharge the `cert.checks goal gs = true` side condition by
`with_unfolding_all decide`. The polynomial equality reduces only with
the `Lawful` substrate fully unfolded. -/
private def buildDecideTrue (type : Expr) : TacticM Expr := do
  let tac ← `(tactic| (with_unfolding_all decide))
  proveByTactic type tac

/-! ### Per-hypothesis bridged proofs

Builds `0 ≤ aeval φ g_i.toCMv` from the parser's hypothesis FVars,
dispatching on `ConstraintKind`. -/

/-- Build per-hypothesis bridged proofs `0 ≤ aeval φ g_i.toCMv` from
the ParsedGoal's hFVars, using `aeval_nonneg_of_orig` (or
`_neg` for `.nonpos`). -/
private def buildHypothesisAevalProofsA (n : Nat) (φE : Expr)
    (rawGs : List SOS.Poly.Raw) (origGs : List Lean.Expr)
    (gsKinds : List SOS.Reify.ConstraintKind) (hFVars : Array FVarId) :
    TacticM (List Expr × List (SOS.Poly n)) := do
  let nE := Lean.mkNatLit n
  let mut acc : List Expr := []
  let mut polys : List (SOS.Poly n) := []
  for i in [:rawGs.length] do
    let raw := rawGs[i]!
    let some gTree := castRawToPoly raw n |
      throwError "sos: constraint poly's maxAtomBound exceeds n = {n}"
    let origExpr := origGs[i]!
    let kind := gsKinds[i]!
    let hFVar := hFVars[i]!
    let hExpr := Lean.mkFVar hFVar
    let gE := Lean.toExpr gTree
    polys := polys ++ [gTree]
    match kind with
    | .nonneg =>
      let eqProof ← buildAtomicBridgeEq n φE gTree origExpr
      let aProof ← mkAppOptM ``SOS.aeval_nonneg_of_orig
        #[some nE, some φE, some gE, some origExpr,
          some eqProof, some hExpr]
      acc := acc ++ [aProof]
    | .nonpos =>
      -- gTree's evalReal yields `-origExpr` because the reifier
      -- already wrapped the orig poly in `Raw.neg`.
      let negOrig ← mkAppM ``Neg.neg #[origExpr]
      let eqProof ← buildAtomicBridgeEq n φE gTree negOrig
      let aProof ← mkAppOptM ``SOS.aeval_nonneg_of_orig_neg
        #[some nE, some φE, some gE, some origExpr,
          some eqProof, some hExpr]
      acc := acc ++ [aProof]
    | .pos =>
      -- Hypothesis is `0 < origExpr`; promote to `0 ≤ origExpr`.
      let hLeExpr ← mkAppM ``le_of_lt #[hExpr]
      let eqProof ← buildAtomicBridgeEq n φE gTree origExpr
      let aProof ← mkAppOptM ``SOS.aeval_nonneg_of_orig
        #[some nE, some φE, some gE, some origExpr,
          some eqProof, some hLeExpr]
      acc := acc ++ [aProof]
  return (acc, polys)

/-- Closed-positivity close. -/
def closeClosedSosA (parsed : SOS.Reify.ParsedGoal)
    (certE : Expr) : TacticM Unit := Tactic.withMainContext do
  let some rawConcl := parsed.rawConcl |
    throwError "sos (closed): missing rawConcl"
  let some origConcl := parsed.origConcl |
    throwError "sos (closed): missing origConcl"
  let n := parsed.atoms.size
  let some pTree := castRawToPoly rawConcl n |
    throwError "sos: conclusion poly's maxAtomBound exceeds n = {n}"
  let mv ← Tactic.getMainGoal
  let φE ← buildFinValExpr parsed.atoms
  let (hAevalProofs, gPolys) ← buildHypothesisAevalProofsA n φE
    parsed.rawGs parsed.origGs parsed.gsKinds parsed.hFVars
  let gsListE ← gsCMvListExpr n gPolys
  let hgsProof ← buildForallMemProof n φE gPolys hAevalProofs
  let pCMv ← toCMvExpr n pTree
  let goalE ← mkAppOptM ``SOS.Goal.closed
    #[some (Lean.mkNatLit n), some pCMv]
  let checksE ← mkAppM ``SOS.Certificate.checks #[certE, goalE, gsListE]
  let trueE ← mkAppOptM ``Bool.true #[]
  let decType ← mkEq checksE trueE
  let decProof ← buildDecideTrue decType
  let hTarget ← mkAppM ``SOS.sos_sound
    #[pCMv, gsListE, certE, decProof, φE, hgsProof]
  let eqProof_p ← buildAtomicBridgeEq n φE pTree origConcl
  let pE := Lean.toExpr pTree
  let final ← mkAppOptM ``SOS.nonneg_orig_of_aeval
    #[some (Lean.mkNatLit n), some φE, some pE, some origConcl,
      some eqProof_p, some hTarget]
  mv.assign final
  Tactic.replaceMainGoal []

/-- Strict-positivity close. -/
def closeStrictSosA (parsed : SOS.Reify.ParsedGoal)
    (certE : Expr) (εE : Expr) (hεE : Expr) : TacticM Unit :=
    Tactic.withMainContext do
  let some rawConcl := parsed.rawConcl |
    throwError "sos (strict): missing rawConcl"
  let some origConcl := parsed.origConcl |
    throwError "sos (strict): missing origConcl"
  let n := parsed.atoms.size
  let some pTree := castRawToPoly rawConcl n |
    throwError "sos: conclusion poly's maxAtomBound exceeds n = {n}"
  let mv ← Tactic.getMainGoal
  let φE ← buildFinValExpr parsed.atoms
  let (hAevalProofs, gPolys) ← buildHypothesisAevalProofsA n φE
    parsed.rawGs parsed.origGs parsed.gsKinds parsed.hFVars
  let gsListE ← gsCMvListExpr n gPolys
  let hgsProof ← buildForallMemProof n φE gPolys hAevalProofs
  let pCMv ← toCMvExpr n pTree
  let goalE ← mkAppOptM ``SOS.Goal.strict
    #[some (Lean.mkNatLit n), some pCMv, some εE, some hεE]
  let checksE ← mkAppM ``SOS.Certificate.checks #[certE, goalE, gsListE]
  let trueE ← mkAppOptM ``Bool.true #[]
  let decType ← mkEq checksE trueE
  let decProof ← buildDecideTrue decType
  let hTarget ← mkAppM ``SOS.sos_strict_sound
    #[pCMv, εE, hεE, gsListE, certE, decProof, φE, hgsProof]
  let eqProof_p ← buildAtomicBridgeEq n φE pTree origConcl
  let pE := Lean.toExpr pTree
  let final ← mkAppOptM ``SOS.pos_orig_of_aeval
    #[some (Lean.mkNatLit n), some φE, some pE, some origConcl,
      some eqProof_p, some hTarget]
  mv.assign final
  Tactic.replaceMainGoal []

/-- Infeasibility close. The conclusion is `False`; the goal becomes
`<gᵢ_constraints> → False` after intros. -/
def closeInfeasibleSosA (parsed : SOS.Reify.ParsedGoal)
    (certE : Expr) : TacticM Unit := Tactic.withMainContext do
  let n := parsed.atoms.size
  let mv ← Tactic.getMainGoal
  let φE ← buildFinValExpr parsed.atoms
  let (hAevalProofs, gPolys) ← buildHypothesisAevalProofsA n φE
    parsed.rawGs parsed.origGs parsed.gsKinds parsed.hFVars
  let gsListE ← gsCMvListExpr n gPolys
  let hgsProof ← buildForallMemProof n φE gPolys hAevalProofs
  let goalE ← mkAppOptM ``SOS.Goal.infeasible #[some (Lean.mkNatLit n)]
  let checksE ← mkAppM ``SOS.Certificate.checks #[certE, goalE, gsListE]
  let trueE ← mkAppOptM ``Bool.true #[]
  let decType ← mkEq checksE trueE
  let decProof ← buildDecideTrue decType
  let infeasibleProof ← mkAppM ``SOS.sos_infeasible_sound
    #[gsListE, certE, decProof, φE, hgsProof]
  mv.assign infeasibleProof
  Tactic.replaceMainGoal []

/-! ### Tactic surface -/

syntax (name := sosTactic) "sos" : tactic
syntax (name := sosWitnessTactic) "sos_witness " term : tactic

/-- Build a `SOS.Certificate n` Expr from a runtime `Certificate n`,
quoted via `SOS.Poly.decompile` so each square round-trips through
`ToExpr (SOS.Poly n)`. -/
private def certExprOfRuntime (n : Nat) (cert : SOS.Certificate n) : MetaM Expr := do
  let sigma0Decompiled : List (SOS.Poly n) :=
    cert.sigma0.squares.map SOS.Poly.decompile
  let sigmasDecompiled : List (List (SOS.Poly n)) :=
    cert.sigmas.map (·.squares.map SOS.Poly.decompile)
  let sigma0E := Lean.toExpr sigma0Decompiled
  let sigmasE := Lean.toExpr sigmasDecompiled
  mkAppOptM ``SOS.Certificate.fromDecompiled
    #[some (Lean.mkNatLit n), some sigma0E, some sigmasE]

/-- Helper: cast rawGs to typed Poly n. -/
private def castGs (rawGs : List SOS.Poly.Raw) (n : Nat) :
    TacticM (List (SOS.Poly n)) := do
  let mut acc : List (SOS.Poly n) := []
  for raw in rawGs do
    let some gT := castRawToPoly raw n |
      throwError "sos: constraint poly's maxAtomBound > n = {n}"
    acc := acc ++ [gT]
  return acc

elab_rules : tactic
  | `(tactic| sos) => do
    let some parsed ← SOS.Reify.parseGoalAtomic |
      throwError "sos: goal not in supported fragment"
    let n := parsed.atoms.size
    let gPolys ← castGs parsed.rawGs n
    let gsCMv := gPolys.map SOS.Poly.toCMv
    match parsed.shape with
    | .closed =>
      let some rawConcl := parsed.rawConcl |
        throwError "sos (closed): missing rawConcl"
      let some pTree := castRawToPoly rawConcl n |
        throwError "sos: conclusion's maxAtomBound > n = {n}"
      let goal : SOS.Goal n := .closed pTree.toCMv
      match (← (SOS.Search.runSearch goal gsCMv : IO _)) with
      | none => throwError "sos: search failed to find a certificate"
      | some cert =>
        let certE ← certExprOfRuntime n cert
        closeClosedSosA parsed certE
    | .infeasible =>
      let goal : SOS.Goal n := .infeasible
      match (← (SOS.Search.runSearch goal gsCMv : IO _)) with
      | none => throwError "sos: search failed to find an infeasibility certificate"
      | some cert =>
        let certE ← certExprOfRuntime n cert
        closeInfeasibleSosA parsed certE
    | .strict =>
      let some rawConcl := parsed.rawConcl |
        throwError "sos (strict): missing rawConcl"
      let some pTree := castRawToPoly rawConcl n |
        throwError "sos: conclusion's maxAtomBound > n = {n}"
      match (← (SOS.Search.runStrictSearch pTree.toCMv gsCMv : IO _)) with
      | none => throwError "sos: search failed to find a strict-positivity certificate"
      | some res =>
        let certE ← certExprOfRuntime n res.cert
        let εE := Lean.toExpr res.ε
        let hεType ← mkAppM ``LT.lt #[(← mkAppOptM ``OfNat.ofNat
          #[some (Lean.mkConst ``Rat), some (Lean.mkNatLit 0), none]), εE]
        let hεE ← buildDecideTrue (← mkEq
          (← mkAppOptM ``Decidable.decide #[some hεType, none])
          (Lean.mkConst ``Bool.true))
        let hεProof ← mkAppM ``of_decide_eq_true #[hεE]
        closeStrictSosA parsed certE εE hεProof

/-! ### `sos?` — Try-this suggestion for the inline witness form

Produces a "Try this: sos_witness <cert>" suggestion where `<cert>`
is a literal `SOS.Certificate` value matching what the search just
produced, decompiled to a clean `CMvPolynomial`-form. The user can
click the suggestion to replace `sos?` in their source. -/

/-- Render a single `SOS.Poly n` as a Lean source string using
`CMvPolynomial.X` / `CMvPolynomial.C` and the standard arithmetic
operators. Strips redundant `0 + …`, `1 * …`, and `…^1` that arise
from `SOS.Poly.decompile`'s normal form. -/
private partial def formatPoly {n : Nat} (p : SOS.Poly n)
    (parenIfComposite : Bool := false) : String :=
  -- Simplifications applied before formatting, preserving semantics:
  --   (const 0) + q        → q
  --   p + (const 0)        → p
  --   (const 1) * q        → q
  --   p * (const 1)        → p
  --   p ^ 1                → p
  match p with
  | .add (.const r) q =>
    if r = 0 then formatPoly q parenIfComposite
    else formatComposite parenIfComposite
      s!"CMvPolynomial.C {ratLit r} + {formatPoly q}"
  | .add p (.const r) =>
    if r = 0 then formatPoly p parenIfComposite
    else formatComposite parenIfComposite
      s!"{formatPoly p} + CMvPolynomial.C {ratLit r}"
  | .add p q =>
    formatComposite parenIfComposite s!"{formatPoly p} + {formatPoly q}"
  | .sub p q =>
    formatComposite parenIfComposite s!"{formatPoly p} - {formatPoly q true}"
  | .mul (.const r) q =>
    if r = 1 then formatPoly q parenIfComposite
    else formatComposite parenIfComposite
      s!"CMvPolynomial.C {ratLit r} * {formatPoly q true}"
  | .mul p (.const r) =>
    if r = 1 then formatPoly p parenIfComposite
    else formatComposite parenIfComposite
      s!"{formatPoly p true} * CMvPolynomial.C {ratLit r}"
  | .mul p q =>
    formatComposite parenIfComposite s!"{formatPoly p true} * {formatPoly q true}"
  | .neg p =>
    formatComposite parenIfComposite s!"-{formatPoly p true}"
  | .pow p 1 => formatPoly p parenIfComposite
  | .pow p k => formatComposite parenIfComposite s!"{formatPoly p true}^{k}"
  | .const r => s!"CMvPolynomial.C {ratLit r}"
  | .var i => s!"CMvPolynomial.X {i.val}"
where
  ratLit (r : Rat) : String :=
    if r.den = 1 then s!"({r.num} : ℚ)"
    else s!"(({r.num} : ℚ) / {r.den})"
  formatComposite (parens : Bool) (s : String) : String :=
    if parens then s!"({s})" else s

private def formatSquares {n : Nat} (sqs : List (SOS.Poly n)) : String :=
  "[" ++ ", ".intercalate (sqs.map (fun p => formatPoly p)) ++ "]"

private def formatSigmasList {n : Nat}
    (ds : List (List (SOS.Poly n))) : String :=
  let entries := ds.map fun sqs => s!"\{ squares := {formatSquares sqs} }"
  "[" ++ ", ".intercalate entries ++ "]"

/-- Render a runtime `SOS.Certificate n` as a Lean source literal
suitable as the argument to `sos_witness`. -/
private def formatCertificate {n : Nat} (cert : SOS.Certificate n) : String :=
  let σ₀_decomp : List (SOS.Poly n) :=
    cert.sigma0.squares.map SOS.Poly.decompile
  let σᵢ_decomp : List (List (SOS.Poly n)) :=
    cert.sigmas.map (fun sd => sd.squares.map SOS.Poly.decompile)
  s!"\{ sigma0 := \{ squares := {formatSquares σ₀_decomp} }, \
     sigmas := {formatSigmasList σᵢ_decomp} }"

syntax (name := sosTryTactic) "sos?" : tactic

/-- Emit the `Try this:` suggestion for a found certificate. -/
private def emitSosSuggestion (tk : Syntax) (certText : String) : TacticM Unit := do
  let suggestion : String := s!"sos_witness {certText}"
  match Lean.Parser.runParserCategory (← getEnv) `tactic suggestion with
  | .ok stx =>
    Lean.Meta.Tactic.TryThis.addSuggestion tk (⟨stx⟩ : TSyntax `tactic)
  | .error err =>
    throwError "sos?: failed to parse suggestion as tactic syntax: {err}"

elab_rules : tactic
  | `(tactic| sos?%$tk) => do
    let some parsed ← SOS.Reify.parseGoalAtomic |
      throwError "sos?: goal not in supported fragment"
    let n := parsed.atoms.size
    let gPolys ← castGs parsed.rawGs n
    let gsCMv := gPolys.map SOS.Poly.toCMv
    match parsed.shape with
    | .closed =>
      let some rawConcl := parsed.rawConcl |
        throwError "sos? (closed): missing rawConcl"
      let some pTree := castRawToPoly rawConcl n |
        throwError "sos?: conclusion's maxAtomBound > n = {n}"
      let goal : SOS.Goal n := .closed pTree.toCMv
      match (← (SOS.Search.runSearch goal gsCMv : IO _)) with
      | none => throwError "sos?: search failed to find a certificate"
      | some cert =>
        emitSosSuggestion tk (formatCertificate cert)
        let certE ← certExprOfRuntime n cert
        closeClosedSosA parsed certE
    | .infeasible =>
      let goal : SOS.Goal n := .infeasible
      match (← (SOS.Search.runSearch goal gsCMv : IO _)) with
      | none => throwError "sos?: search failed to find an infeasibility certificate"
      | some cert =>
        emitSosSuggestion tk (formatCertificate cert)
        let certE ← certExprOfRuntime n cert
        closeInfeasibleSosA parsed certE
    | .strict =>
      let some rawConcl := parsed.rawConcl |
        throwError "sos? (strict): missing rawConcl"
      let some pTree := castRawToPoly rawConcl n |
        throwError "sos?: conclusion's maxAtomBound > n = {n}"
      match (← (SOS.Search.runStrictSearch pTree.toCMv gsCMv : IO _)) with
      | none => throwError "sos?: search failed to find a strict-positivity certificate"
      | some res =>
        emitSosSuggestion tk (formatCertificate res.cert)
        let certE ← certExprOfRuntime n res.cert
        let εE := Lean.toExpr res.ε
        let hεType ← mkAppM ``LT.lt #[(← mkAppOptM ``OfNat.ofNat
          #[some (Lean.mkConst ``Rat), some (Lean.mkNatLit 0), none]), εE]
        let hεE ← buildDecideTrue (← mkEq
          (← mkAppOptM ``Decidable.decide #[some hεType, none])
          (Lean.mkConst ``Bool.true))
        let hεProof ← mkAppM ``of_decide_eq_true #[hεE]
        closeStrictSosA parsed certE εE hεProof

elab_rules : tactic
  | `(tactic| sos_witness $cert:term) => do
    let some parsed ← SOS.Reify.parseGoalAtomic |
      throwError "sos_witness: goal not in supported fragment"
    let n := parsed.atoms.size
    let certTy ← mkAppOptM ``SOS.Certificate #[some (Lean.mkNatLit n)]
    let certE ← Term.elabTermEnsuringType cert certTy
    Term.synthesizeSyntheticMVarsNoPostponing
    let certE ← instantiateMVars certE
    match parsed.shape with
    | .closed => closeClosedSosA parsed certE
    | .infeasible => closeInfeasibleSosA parsed certE
    | _ =>
      throwError "sos_witness: strict-positivity goals are not yet supported"

end SOS
