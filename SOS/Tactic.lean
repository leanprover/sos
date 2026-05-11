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

/-! ### Common Expr fragments -/

/-- `Lean.Expr` for `ℝ`, used throughout the elaborator. -/
private def realTy : Expr := Lean.mkConst ``Real

/-- `Lean.Expr` for `ℚ`, used throughout the elaborator. -/
private def ratTy : Expr := Lean.mkConst ``Rat

/-- `Lean.Expr` for `CMvPolynomial n ℚ`. -/
private def cmvType (n : Nat) : MetaM Expr :=
  Meta.mkAppOptM ``CPoly.CMvPolynomial
    #[some (Lean.mkNatLit n), some ratTy, none]

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
    some ratTy, some realTy, none, none, none, some xE, some pCMv]

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
  let cmvTy ← cmvType n
  let mut acc ← mkAppOptM ``List.nil #[some cmvTy]
  for g in gs.reverse do
    let gCMv ← toCMvExpr n g
    acc ← mkAppOptM ``List.cons #[some cmvTy, some gCMv, some acc]
  return acc

/-- Build a proof of `∀ g ∈ gsList, 0 ≤ CMvPolynomial.aeval x g`, given
per-hypothesis proofs `hAevalProofs i : 0 ≤ aeval x gs[i].toCMv`. -/
private def buildForallMemProof (n : Nat) (xE : Expr) (gs : List (SOS.Poly n))
    (hAevalProofs : List Expr) : MetaM Expr := do
  let cmvTy ← cmvType n
  -- predicate: fun g => 0 ≤ aeval x g
  let predicate ← withLocalDeclD `g cmvTy fun gFV => do
    let body ← mkAppM ``LE.le
      #[(← mkAppOptM ``OfNat.ofNat
          #[some realTy, some (Lean.mkNatLit 0), none]),
        (← mkAppOptM ``CPoly.CMvPolynomial.aeval
          #[some (Lean.mkNatLit n), some ratTy, some realTy,
            none, none, none, some xE, some gFV])]
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
`decide +kernel`. Kernel reduction handles `Std.ExtTreeMap` lookups
and rational arithmetic at the witness denominators the search
actually emits. -/
private def buildDecideTrue (type : Expr) : TacticM Expr := do
  let tac ← `(tactic| (decide +kernel))
  proveByTactic type tac

/-! ### Per-hypothesis bridged proofs

Builds `0 ≤ aeval φ g_i.toCMv` from the parser's hypothesis FVars,
dispatching on `ConstraintKind`. -/

/-- Build per-hypothesis bridged proofs `0 ≤ aeval φ g_i.toCMv` from
the ParsedGoal's constraints, using `aeval_nonneg_of_orig` (or
`_neg` for `.nonpos`, or `le_of_lt` lifting for `.pos`). -/
private def buildHypothesisAevalProofsA (n : Nat) (φE : Expr)
    (constraints : Array SOS.Reify.ConstraintInfo) :
    TacticM (List Expr × List (SOS.Poly n)) := do
  let nE := Lean.mkNatLit n
  let mut acc : Array Expr := Array.mkEmpty constraints.size
  let mut polys : Array (SOS.Poly n) := Array.mkEmpty constraints.size
  for c in constraints do
    let some gTree := castRawToPoly c.raw n |
      throwError "sos: constraint poly's maxAtomBound exceeds n = {n}"
    let hExpr := Lean.mkFVar c.fvar
    let gE := Lean.toExpr gTree
    polys := polys.push gTree
    match c.kind with
    | .nonneg =>
      let eqProof ← buildAtomicBridgeEq n φE gTree c.orig
      let aProof ← mkAppOptM ``SOS.aeval_nonneg_of_orig
        #[some nE, some φE, some gE, some c.orig,
          some eqProof, some hExpr]
      acc := acc.push aProof
    | .nonpos =>
      -- gTree's evalReal yields `-orig` because the reifier already
      -- wrapped the orig poly in `Raw.neg`.
      let negOrig ← mkAppM ``Neg.neg #[c.orig]
      let eqProof ← buildAtomicBridgeEq n φE gTree negOrig
      let aProof ← mkAppOptM ``SOS.aeval_nonneg_of_orig_neg
        #[some nE, some φE, some gE, some c.orig,
          some eqProof, some hExpr]
      acc := acc.push aProof
    | .pos =>
      -- Hypothesis is `0 < orig`; promote to `0 ≤ orig`.
      let hLeExpr ← mkAppM ``le_of_lt #[hExpr]
      let eqProof ← buildAtomicBridgeEq n φE gTree c.orig
      let aProof ← mkAppOptM ``SOS.aeval_nonneg_of_orig
        #[some nE, some φE, some gE, some c.orig,
          some eqProof, some hLeExpr]
      acc := acc.push aProof
  return (acc.toList, polys.toList)

/-- Closed and strict goals carry a conclusion polynomial plus the
original user expression it must bridge back to. -/
private structure ParsedConclusionData (n : Nat) where
  tree : SOS.Poly n
  cmv  : Expr
  orig : Expr

/-- Extract and cast the conclusion polynomial for closed/strict modes. -/
private def parsedConclusionData (tag : String)
    (parsed : SOS.Reify.ParsedGoal) (n : Nat) :
    TacticM (ParsedConclusionData n) := do
  let some concl := parsed.concl |
    throwError "{tag}: missing concl"
  let some pTree := castRawToPoly concl.raw n |
    throwError "{tag}: conclusion poly's maxAtomBound exceeds n = {n}"
  let pCMv ← toCMvExpr n pTree
  return { tree := pTree, cmv := pCMv, orig := concl.orig }

/-- The shape-specific data the unified close needs: which `Goal`
constructor to invoke, which soundness lemma, and (for closed/strict)
how to bridge the resulting `0 ≤ aeval …` / `0 < aeval …` proof back
to the user's original `0 ≤ origExpr` / `0 < origExpr` goal.
Infeasibility's conclusion is `False`, so it skips the bridge. -/
inductive CloseMode where
  | closed
  | strict (εE : Expr) (hεE : Expr)
  | infeasible

/-- Unified close: builds `decide`-checked soundness application for
the closed / strict / infeasible certificate and assigns the main goal.
Mode-specific differences are tabulated in `CloseMode`. -/
def closeSos (parsed : SOS.Reify.ParsedGoal) (certE : Expr)
    (mode : CloseMode) : TacticM Unit := Tactic.withMainContext do
  let n := parsed.atoms.size
  let nE := Lean.mkNatLit n
  let mv ← Tactic.getMainGoal
  let φE ← buildFinValExpr parsed.atoms
  let (hAevalProofs, gPolys) ←
    buildHypothesisAevalProofsA n φE parsed.constraints
  let gsListE ← gsCMvListExpr n gPolys
  let hgsProof ← buildForallMemProof n φE gPolys hAevalProofs
  -- Closed and strict need the conclusion polynomial; infeasible doesn't.
  let pData? : Option (ParsedConclusionData n) ← do
    match mode with
    | .infeasible => pure none
    | .closed | .strict .. =>
      pure (some (← parsedConclusionData "sos" parsed n))
  let goalE ← match mode, pData? with
    | .closed, some p =>
      mkAppOptM ``SOS.Goal.closed #[some nE, some p.cmv]
    | .strict εE hεE, some p =>
      mkAppOptM ``SOS.Goal.strict #[some nE, some p.cmv, some εE, some hεE]
    | .infeasible, _ =>
      mkAppOptM ``SOS.Goal.infeasible #[some nE]
    | _, _ => throwError "sos: internal: pData missing for non-infeasible mode"
  let checksE ← mkAppM ``SOS.Certificate.checks #[certE, goalE, gsListE]
  let trueE ← mkAppOptM ``Bool.true #[]
  let decProof ← buildDecideTrue (← mkEq checksE trueE)
  match mode, pData? with
  | .closed, some p =>
    let hTarget ← mkAppM ``SOS.sos_sound
      #[p.cmv, gsListE, certE, decProof, φE, hgsProof]
    let eqProof_p ← buildAtomicBridgeEq n φE p.tree p.orig
    let pE := Lean.toExpr p.tree
    let final ← mkAppOptM ``SOS.nonneg_orig_of_aeval
      #[some nE, some φE, some pE, some p.orig, some eqProof_p, some hTarget]
    mv.assign final
  | .strict εE hεE, some p =>
    let hTarget ← mkAppM ``SOS.sos_strict_sound
      #[p.cmv, εE, hεE, gsListE, certE, decProof, φE, hgsProof]
    let eqProof_p ← buildAtomicBridgeEq n φE p.tree p.orig
    let pE := Lean.toExpr p.tree
    let final ← mkAppOptM ``SOS.pos_orig_of_aeval
      #[some nE, some φE, some pE, some p.orig, some eqProof_p, some hTarget]
    mv.assign final
  | .infeasible, _ =>
    let infeasibleProof ← mkAppM ``SOS.sos_infeasible_sound
      #[gsListE, certE, decProof, φE, hgsProof]
    mv.assign infeasibleProof
  | _, _ => throwError "sos: internal: pData missing for non-infeasible mode"
  Tactic.replaceMainGoal []

/-! ### Tactic surface -/

syntax (name := sosTactic) "sos" : tactic
syntax (name := sosTryTactic) "sos?" : tactic
syntax (name := sosWitnessTactic)
  "sos_witness " term ("with" "ε" ":=" term)? : tactic

/-- Build a `SOS.Certificate n` Expr from a runtime `Certificate n`,
quoted via `SOS.Poly.decompile` so each square round-trips through
`ToExpr (SOS.Poly n)`. -/
private structure DecompiledCertificate (n : Nat) where
  sigma0 : List (SOS.Poly n)
  sigmas : List (List (SOS.Poly n))

private def decompileCertificate {n : Nat}
    (cert : SOS.Certificate n) : DecompiledCertificate n :=
  { sigma0 := cert.sigma0.squares.map SOS.Poly.decompile,
    sigmas := cert.sigmas.map (·.squares.map SOS.Poly.decompile) }

private def certExprOfDecompiled (n : Nat)
    (cert : DecompiledCertificate n) : MetaM Expr := do
  let sigma0E := Lean.toExpr cert.sigma0
  let sigmasE := Lean.toExpr cert.sigmas
  mkAppOptM ``SOS.Certificate.fromDecompiled
    #[some (Lean.mkNatLit n), some sigma0E, some sigmasE]

/-- Cast each constraint's `Raw` to the typed `Poly n`. -/
private def castConstraints (constraints : Array SOS.Reify.ConstraintInfo)
    (n : Nat) : TacticM (List (SOS.Poly n)) := do
  let mut acc : Array (SOS.Poly n) := Array.mkEmpty constraints.size
  for c in constraints do
    let some gT := castRawToPoly c.raw n |
      throwError "sos: constraint poly's maxAtomBound > n = {n}"
    acc := acc.push gT
  return acc.toList

/-- Build the `LT.lt 0 ε` proof needed by `closeSos (.strict εE hεE)`,
given the `ε` returned by the search. -/
private def buildStrictHεProof (εE : Expr) : TacticM Expr := do
  let hεType ← mkAppM ``LT.lt #[(← mkAppOptM ``OfNat.ofNat
    #[some ratTy, some (Lean.mkNatLit 0), none]), εE]
  let hεE ← buildDecideTrue (← mkEq
    (← mkAppOptM ``Decidable.decide #[some hεType, none])
    (Lean.mkConst ``Bool.true))
  mkAppM ``of_decide_eq_true #[hεE]

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
private def formatDecompiledCertificate {n : Nat}
    (cert : DecompiledCertificate n) : String :=
  s!"\{ sigma0 := \{ squares := {formatSquares cert.sigma0} }, \
     sigmas := {formatSigmasList cert.sigmas} }"

/-- Format an ε rational as a Lean source literal (`(num : ℚ)` or
`((num : ℚ) / den)`), suitable for the `with ε := …` clause. -/
private def formatRat (r : ℚ) : String :=
  if r.den = 1 then s!"({r.num} : ℚ)"
  else s!"(({r.num} : ℚ) / {r.den})"

/-- Emit the `Try this:` suggestion for a found certificate. When `ε?`
is `some r`, append `with ε := <r>` so the suggestion compiles for
strict-positivity goals.

We pass the suggestion as a raw `SuggestionText.string` rather than
roundtripping through `Parser.runParserCategory`; the latter re-pretty-
prints the parsed syntax tree and squashes whitespace around the
`with ε := …` clause. -/
private def emitSosSuggestion (tk : Syntax) (certText : String)
    (ε? : Option ℚ) : TacticM Unit := do
  let suffix := match ε? with
    | none => ""
    | some r => s!" with ε := {formatRat r}"
  let suggestion : String := s!"sos_witness {certText}{suffix}"
  let sugg : Lean.Meta.Tactic.TryThis.Suggestion :=
    { suggestion := .string suggestion }
  Lean.Meta.Tactic.TryThis.addSuggestion tk sugg

/-- The shared body of `sos` and `sos?`. Runs search for the parsed
goal, optionally emits a `Try this:` suggestion at `suggest?`, and
closes the goal with the resulting certificate. The error-message
prefix (`"sos"` vs `"sos?"`) is taken from `tag`. -/
private def runSosTactic (parsed : SOS.Reify.ParsedGoal)
    (suggest? : Option Syntax) (tag : String) : TacticM Unit := do
  let n := parsed.atoms.size
  let gPolys ← castConstraints parsed.constraints n
  let gsCMv := gPolys.map SOS.Poly.toCMv
  let withFoundCert (cert : SOS.Certificate n) (mode : CloseMode)
      (ε? : Option ℚ) : TacticM Unit := do
    let decompiled := decompileCertificate cert
    if let some tk := suggest? then
      emitSosSuggestion tk (formatDecompiledCertificate decompiled) ε?
    let certE ← certExprOfDecompiled n decompiled
    closeSos parsed certE mode
  match parsed.shape with
  | .closed =>
    let p ← parsedConclusionData s!"{tag} (closed)" parsed n
    let goal : SOS.Goal n := .closed p.tree.toCMv
    match (← (SOS.Search.runSearch goal gsCMv : IO _)) with
    | none => throwError "{tag}: search failed to find a certificate"
    | some cert => withFoundCert cert .closed none
  | .infeasible =>
    match (← (SOS.Search.runSearch .infeasible gsCMv : IO _)) with
    | none => throwError "{tag}: search failed to find an infeasibility certificate"
    | some cert => withFoundCert cert .infeasible none
  | .strict =>
    let p ← parsedConclusionData s!"{tag} (strict)" parsed n
    match (← (SOS.Search.runStrict p.tree.toCMv gsCMv : IO _)) with
    | none => throwError "{tag}: search failed to find a strict-positivity certificate"
    | some res =>
      let εE := Lean.toExpr res.ε
      let hεProof ← buildStrictHεProof εE
      withFoundCert res.cert (.strict εE hεProof) (some res.ε)

elab_rules : tactic
  | `(tactic| sos) => do
    let some parsed ← SOS.Reify.parseGoalAtomic |
      throwError "sos: goal not in supported fragment"
    runSosTactic parsed none "sos"

elab_rules : tactic
  | `(tactic| sos?%$tk) => do
    let some parsed ← SOS.Reify.parseGoalAtomic |
      throwError "sos?: goal not in supported fragment"
    runSosTactic parsed (some tk) "sos?"

/-- Shared body of `sos_witness` (with and without the `with ε := …`
suffix). Elaborates the certificate, dispatches on the parsed goal
shape, and routes through `closeSos`. -/
private def runSosWitness (cert : Term)
    (epsTerm? : Option Term) : TacticM Unit := do
  let some parsed ← SOS.Reify.parseGoalAtomic |
    throwError "sos_witness: goal not in supported fragment"
  let n := parsed.atoms.size
  let certTy ← mkAppOptM ``SOS.Certificate #[some (Lean.mkNatLit n)]
  let certE ← Term.elabTermEnsuringType cert certTy
  Term.synthesizeSyntheticMVarsNoPostponing
  let certE ← instantiateMVars certE
  match parsed.shape, epsTerm? with
  | .closed, none => closeSos parsed certE .closed
  | .infeasible, none => closeSos parsed certE .infeasible
  | .strict, some εT =>
    let εE ← Term.elabTermEnsuringType εT ratTy
    Term.synthesizeSyntheticMVarsNoPostponing
    let εE ← instantiateMVars εE
    let hεProof ← buildStrictHεProof εE
    closeSos parsed certE (.strict εE hεProof)
  | .strict, none =>
    throwError "sos_witness: strict-positivity goal requires `with ε := <rat>`"
  | _, some _ =>
    throwError "sos_witness: `with ε := …` is only valid on strict-positivity goals"

elab_rules : tactic
  | `(tactic| sos_witness $cert:term) => runSosWitness cert none
  | `(tactic| sos_witness $cert:term with ε := $eps:term) =>
      runSosWitness cert (some eps)

end SOS
