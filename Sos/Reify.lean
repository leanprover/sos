/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Goal reifier: walks a Lean `Expr` representing
`∀ x : Fin n → ℝ, (g₁ x ≥ 0) → … → (gₘ x ≥ 0) → p x ⊳ 0`
and extracts:

  * the variable count `n`,
  * the bound variable's `FVarId` for atom matching,
  * the polynomial `p : CMvPolynomial n ℚ` (the goal's RHS),
  * the constraint polynomials `gs : List (CMvPolynomial n ℚ)`,
  * the goal shape (`closed` / `strict` / `infeasible`).

**v0.1 scope.** The reifier handles a concrete subset of arithmetic
expressions over `ℝ`:

  * `HAdd.hAdd`, `HSub.hSub`, `HMul.hMul`, `HPow.hPow` (with `ℕ`
    literal exponent), `Neg.neg`.
  * Numeric literals (`OfNat.ofNat`, integer/rational casts).
  * Atom: an application `x ⟨i, _⟩` of the bound variable to a
    `Fin n` element with literal `i`. Anything else fails with an
    error and the tactic falls through.

The proof of the equality between the original Lean expression and
the reflected `aeval` form is left to the elaborator (Stage 5),
which discharges it via `simp` against CompPoly's `aeval_*` simp
lemmas. This pragmatically sidesteps the explicit-`reduceGoal`-`Expr`
construction the v0.1 plan documented; the cost is one extra `simp`
call per `sos` invocation.
-/
import Sos.Certificate
import Lean

namespace Sos.Reify

open Lean Meta Elab CPoly

/-- Result of parsing a goal. The polynomials and goal shape are
in CompPoly form, ready to be passed to `Sos.Search.runSearch`. -/
structure ParsedGoal where
  n            : Nat
  goal         : Goal n
  gs           : List (CMvPolynomial n ℚ)

/-- Extract a `Nat` literal from an `Expr`, peeking through `OfNat.ofNat`. -/
def natLit? (e : Expr) : MetaM (Option Nat) := do
  let e ← whnfR e
  if let some n := e.rawNatLit? then return some n
  -- `OfNat.ofNat n` where n is a Nat literal.
  match_expr e with
  | OfNat.ofNat _ n _ =>
    let n ← whnfR n
    return n.rawNatLit?
  | _ => return none

/-- Extract a rational from an `Expr`. Recognises:
  * Natural / integer literals (incl. via OfNat.ofNat).
  * `Neg.neg` of a literal.
  * Integer / rational casts to `ℝ`.
Returns `none` if the expression is not a rational literal. -/
partial def ratLit? (e : Expr) : MetaM (Option ℚ) := do
  let e ← whnfR e
  -- Try natural-number literal.
  if let some n ← natLit? e then return some (n : ℚ)
  match_expr e with
  | Neg.neg _ _ a =>
    let some r ← ratLit? a | return none
    return some (-r)
  | HDiv.hDiv _ _ _ _ a b =>
    let some ra ← ratLit? a | return none
    let some rb ← ratLit? b | return none
    if rb = 0 then return none
    return some (ra / rb)
  | IntCast.intCast _ _ a =>
    let some r ← ratLit? a | return none
    return some r
  | NatCast.natCast _ _ a =>
    let some r ← ratLit? a | return none
    return some r
  | Int.ofNat a =>
    let some n ← natLit? a | return none
    return some (n : ℚ)
  | Int.negSucc a =>
    let some n ← natLit? a | return none
    return some (-(n + 1) : ℚ)
  | _ => return none

/-- Match `e = x ⟨i, _⟩` where `x : Fin n → ℝ` is the bound variable
and `i` is a `Nat` literal. Returns `i` if matched. -/
def boundVarApp? (xFVar : FVarId) (e : Expr) : MetaM (Option Nat) := do
  let e ← whnfR e
  -- The expected shape is `xFVar (Fin.mk i h)` or `xFVar i_coerced`.
  let .app f arg := e | return none
  let .fvar id := f.consumeMData | return none
  if id != xFVar then return none
  -- arg is a `Fin n` value. It might be `⟨i, _⟩` or `(i : Fin n)`.
  let arg ← whnfR arg
  match_expr arg with
  | Fin.mk _ i _ =>
    natLit? i
  | _ =>
    -- Try to extract the underlying `Nat` via `Fin.val`.
    let argType ← inferType arg
    let argType ← whnfR argType
    -- Otherwise: try a literal `OfNat.ofNat n : Fin _`.
    natLit? arg

/-- Walk an `Expr` of type `ℝ`, building a `CMvPolynomial n ℚ`.
Atoms must match `xFVar ⟨i, _⟩` for `i < n`; anything else throws. -/
partial def reifyExpr (n : Nat) (xFVar : FVarId) (e : Expr) :
    MetaM (CMvPolynomial n ℚ) := do
  let e ← whnfR e
  -- First try: numeric literal.
  if let some r ← ratLit? e then
    return CMvPolynomial.C r
  -- Then: bound-variable atom.
  if let some i ← boundVarApp? xFVar e then
    if h : i < n then
      return CMvPolynomial.X ⟨i, h⟩
    else
      throwError "sos: variable index {i} out of range (n = {n})"
  -- Otherwise: arithmetic operator.
  match_expr e with
  | HAdd.hAdd _ _ _ _ a b =>
    return (← reifyExpr n xFVar a) + (← reifyExpr n xFVar b)
  | HSub.hSub _ _ _ _ a b =>
    return (← reifyExpr n xFVar a) - (← reifyExpr n xFVar b)
  | HMul.hMul _ _ _ _ a b =>
    return (← reifyExpr n xFVar a) * (← reifyExpr n xFVar b)
  | HPow.hPow _ _ _ _ a k =>
    let some kNat ← natLit? k |
      throwError "sos: non-literal exponent in {indentExpr e}"
    return (← reifyExpr n xFVar a) ^ kNat
  | Neg.neg _ _ a =>
    return -(← reifyExpr n xFVar a)
  | _ =>
    throwError "sos: unrecognised subexpression in goal: {indentExpr e}"

/-- Match a constraint hypothesis of the form `0 ≤ g x` or `g x ≥ 0`
(or the strict `<` variants). Returns the polynomial side. v0.1
treats both `≤` and `<` the same way (as nonneg constraints), which
is sound for proving nonnegativity (the resulting cert is valid for
the weaker form too). -/
def constraintExpr? (h : Expr) : MetaM (Option Expr) := do
  let h ← whnfR h
  match_expr h with
  | LE.le _ _ a b =>
    -- 0 ≤ b form (preferred).
    if let some r ← ratLit? a then
      if r = 0 then return some b
    -- a ≤ 0 form: g ≤ 0 is the constraint -g ≥ 0.
    if let some r ← ratLit? b then
      if r = 0 then return some (mkApp (mkApp (mkConst ``Neg.neg) (← inferType a)) a)
    return none
  | GE.ge _ _ a b =>
    if let some r ← ratLit? b then
      if r = 0 then return some a
    return none
  | LT.lt _ _ a b =>
    if let some r ← ratLit? a then
      if r = 0 then return some b
    return none
  | GT.gt _ _ a b =>
    if let some r ← ratLit? b then
      if r = 0 then return some a
    return none
  | _ => return none

/-- Match the goal's conclusion shape. Returns either `some (.closed,
p_expr)`, `some (.strict, p_expr, ε_expr_optional)`, or
`some (.infeasible, _)` and the conclusion's polynomial side. -/
inductive ConclusionShape where
  | closed     (pExpr : Expr)
  | strict     (pExpr : Expr)
  | infeasible

def conclusionShape? (e : Expr) : MetaM (Option ConclusionShape) := do
  let e ← whnfR e
  match_expr e with
  | LE.le _ _ a b =>
    if let some r ← ratLit? a then
      if r = 0 then return some (.closed b)
    return none
  | GE.ge _ _ a b =>
    if let some r ← ratLit? b then
      if r = 0 then return some (.closed a)
    return none
  | LT.lt _ _ a b =>
    if let some r ← ratLit? a then
      if r = 0 then return some (.strict b)
    return none
  | GT.gt _ _ a b =>
    if let some r ← ratLit? b then
      if r = 0 then return some (.strict a)
    return none
  | False => return some .infeasible
  | _ => return none

/-- Walk a chain of `→` (Pi without dependence) collecting hypotheses
plus the final conclusion. -/
partial def stripImplications (e : Expr) :
    Array Expr × Expr := Id.run do
  let mut hyps : Array Expr := #[]
  let mut e := e
  while true do
    match e with
    | .forallE _ ty body bi =>
      if !body.hasLooseBVars && bi.isExplicit then
        hyps := hyps.push ty
        e := body
      else
        break
    | _ => break
  return (hyps, e)

/-- Top-level goal parser. Matches `∀ x : Fin n → ℝ, hyps → conclusion`
and returns a `ParsedGoal`. Returns `none` if the shape doesn't match
the v0.1 fragment. -/
def parseGoal (goalType : Expr) : MetaM (Option ParsedGoal) := do
  let goalType ← whnfR goalType
  -- The leading binder must be `∀ x : Fin n → ℝ, …` for some Nat literal n.
  let .forallE _ binderType body _ := goalType | return none
  -- Parse binderType = Fin n → ℝ.
  let binderType ← whnfR binderType
  match_expr binderType with
  | _ => pure ()
  let .forallE _ finN realTy _ := binderType | return none
  -- realTy must be `ℝ`.
  unless ← Meta.isDefEq realTy (mkConst ``Real) do return none
  -- finN must be `Fin n`.
  let finN ← whnfR finN
  let .app finK n_expr := finN | return none
  unless finK.isConstOf ``Fin do return none
  let some n ← natLit? n_expr | return none
  -- Now bind a fresh fvar for x and walk the body.
  withLocalDecl `x .default binderType fun xFVar => do
    let body := body.instantiate1 xFVar
    let (hypsExprs, conclExpr) := stripImplications body
    -- Reify each hypothesis: must be 0 ≤ g x or g x ≥ 0 etc.
    let mut gs : List (CMvPolynomial n ℚ) := []
    for hExpr in hypsExprs do
      let some gExpr ← constraintExpr? hExpr |
        throwError "sos: hypothesis not in supported shape: {indentExpr hExpr}"
      let g ← reifyExpr n xFVar.fvarId! gExpr
      gs := gs ++ [g]
    -- Reify the conclusion.
    let some shape ← conclusionShape? conclExpr | return none
    match shape with
    | .closed pExpr =>
      let p ← reifyExpr n xFVar.fvarId! pExpr
      return some ⟨n, .closed p, gs⟩
    | .strict pExpr =>
      let p ← reifyExpr n xFVar.fvarId! pExpr
      -- ε is filled in later by the search (or, for v0.1, this falls through).
      return some ⟨n, .strict p 1 (by decide), gs⟩
    | .infeasible =>
      return some ⟨n, .infeasible, gs⟩

end Sos.Reify
