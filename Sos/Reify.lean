/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Goal reifier. Walks a Lean expression of shape

    ∀ x : Fin n → ℝ, (g₁ x ⊳ 0) → … → (gₘ x ⊳ 0) → conclusion

and returns a `ParsedGoal` containing both the typed-AST form
(`Sos.Poly n`) of every polynomial encountered and the original
`Lean.Expr` for each polynomial side. Both forms are needed by the
elaborator: the AST drives the search and the verifier; the
original Expr appears in the user-facing goal and must be matched
syntactically by the bridge.

v0.1 fragment: atoms must be applications of the bound variable
`x ⟨i, _⟩` for some `Nat`-literal `i < n`, plus rational literals
and the standard arithmetic constructors `HAdd`, `HSub`, `HMul`,
`HPow` (with `Nat`-literal exponent), `Neg`, and the rational casts
into ℝ. Anything else throws an error and the tactic falls through.
-/
import Sos.Raw
import Sos.Certificate
import Lean

namespace Sos.Reify

open Lean Meta Elab CPoly

/-! ### Goal classification -/

/-- The three goal shapes the reifier recognises. The conclusion's
polynomial side is held in the `ParsedGoal`'s `goal_pTree` /
`goal_orig_expr` fields (or absent for `.infeasible`). -/
inductive ShapeKind where
  | closed
  | strict
  | infeasible
  deriving Inhabited, Repr, DecidableEq

/-! ### Output of reification -/

/-- All data the elaborator needs from reification.

* `goal_pTree` is the conclusion polynomial as a typed AST. Absent
  (`none`) iff `shape = .infeasible`.
* `goal_orig_abs` / `gs_orig_abs` are the original arithmetic Lean
  expressions for the conclusion / constraints, abstracted over the
  bound variable: `bvar 0` represents `x : Fin n → ℝ`. Re-instantiate
  via `e.instantiate1 (mkFVar newX)` once the elaborator has
  introduced its own `x`.
* `gs_pTrees` / `gs_orig_abs` are paired by index.
-/
structure ParsedGoal where
  n              : Nat
  shape          : ShapeKind
  goal_pTree     : Option (Sos.Poly n)
  goal_orig_abs  : Option Lean.Expr
  gs_pTrees      : List (Sos.Poly n)
  gs_orig_abs    : List Lean.Expr

namespace ParsedGoal

/-- The constraint polynomials in `CMvPolynomial n ℚ` form, used by
the search engine. -/
def gs_cmv (parsed : ParsedGoal) : List (CMvPolynomial parsed.n ℚ) :=
  parsed.gs_pTrees.map Sos.Poly.toCMv

/-- The `Sos.Goal n` value the verifier consumes. Strict goals carry a
placeholder `ε := 1` here; the elaborator replaces it with the
search-found rational. -/
def goal (parsed : ParsedGoal) : Sos.Goal parsed.n :=
  match h : parsed.shape, parsed.goal_pTree with
  | .closed, some pTree   => .closed (Sos.Poly.toCMv pTree)
  | .strict, some pTree   => .strict (Sos.Poly.toCMv pTree) 1 (by decide)
  | .infeasible, _        => .infeasible
  | .closed, none         => .infeasible -- unreachable; satisfies the totality requirement
  | .strict, none         => .infeasible

end ParsedGoal

/-! ### Numeric-literal extraction -/

/-- Extract a `Nat` literal from an `Expr`, peeking through `OfNat.ofNat`. -/
def natLit? (e : Expr) : MetaM (Option Nat) := do
  let e ← whnfR e
  if let some n := e.rawNatLit? then return some n
  match_expr e with
  | OfNat.ofNat _ n _ =>
    let n ← whnfR n
    return n.rawNatLit?
  | _ => return none

/-- Extract a rational from an `Expr`. -/
partial def ratLit? (e : Expr) : MetaM (Option ℚ) := do
  let e ← whnfR e
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

/-! ### Atom recognition -/

/-- Match `e = xFVar i` where `i` is a `Fin n` value (literal or `Fin.mk`).
Returns `i`'s `Nat` value if matched. -/
def boundVarApp? (xFVar : FVarId) (e : Expr) : MetaM (Option Nat) := do
  let e ← whnfR e
  let .app f arg := e | return none
  let .fvar id := f.consumeMData | return none
  if id != xFVar then return none
  let arg ← whnfR arg
  match_expr arg with
  | Fin.mk _ i _ => natLit? i
  | _ => natLit? arg

/-! ### Expression-to-`Sos.Poly` reifier -/

/-- Walk an `Expr` of type `ℝ`, building a `Sos.Poly n`. -/
partial def reifyExpr (n : Nat) (xFVar : FVarId) (e : Expr) :
    MetaM (Sos.Poly n) := do
  let e ← whnfR e
  if let some r ← ratLit? e then
    return Sos.Poly.const r
  if let some i ← boundVarApp? xFVar e then
    if h : i < n then
      return Sos.Poly.var ⟨i, h⟩
    else
      throwError "sos: variable index {i} out of range (n = {n})"
  match_expr e with
  | HAdd.hAdd _ _ _ _ a b =>
    return Sos.Poly.add (← reifyExpr n xFVar a) (← reifyExpr n xFVar b)
  | HSub.hSub _ _ _ _ a b =>
    return Sos.Poly.sub (← reifyExpr n xFVar a) (← reifyExpr n xFVar b)
  | HMul.hMul _ _ _ _ a b =>
    return Sos.Poly.mul (← reifyExpr n xFVar a) (← reifyExpr n xFVar b)
  | HPow.hPow _ _ _ _ a k =>
    let some kNat ← natLit? k |
      throwError "sos: non-literal exponent in {indentExpr e}"
    return Sos.Poly.pow (← reifyExpr n xFVar a) kNat
  | Neg.neg _ _ a =>
    return Sos.Poly.neg (← reifyExpr n xFVar a)
  | _ =>
    throwError "sos: unrecognised subexpression in goal: {indentExpr e}"

/-! ### Hypothesis classification -/

/-- Recognise a constraint hypothesis. Returns `(origExpr, pTree)` where
`pTree` is the polynomial whose nonneg-witness the hypothesis provides,
and `origExpr` is the polynomial side of the original Lean expression.

Supported forms:
  * `0 ≤ origExpr` → returns `(origExpr, reify origExpr)`
  * `origExpr ≥ 0` → returns `(origExpr, reify origExpr)`
  * `0 < origExpr` → treated as `0 ≤ origExpr` (sound for nonnegativity proofs).
  * `origExpr > 0` → similarly.
  * `origExpr ≤ 0` → returns `(neg origExpr, neg origExpr-form)`.
  * `0 ≥ origExpr` → similarly.
-/
def constraintExpr? (n : Nat) (xFVar : FVarId) (h : Expr) :
    MetaM (Option (Expr × Sos.Poly n)) := do
  let h ← whnfR h
  match_expr h with
  | LE.le _ _ a b =>
    if let some r ← ratLit? a then
      if r = 0 then
        let pTree ← reifyExpr n xFVar b
        return some (b, pTree)
    if let some r ← ratLit? b then
      if r = 0 then
        -- a ≤ 0 ⟹ -a ≥ 0
        let aTree ← reifyExpr n xFVar a
        return some (a, Sos.Poly.neg aTree)
    return none
  | GE.ge _ _ a b =>
    if let some r ← ratLit? b then
      if r = 0 then
        let pTree ← reifyExpr n xFVar a
        return some (a, pTree)
    if let some r ← ratLit? a then
      if r = 0 then
        let bTree ← reifyExpr n xFVar b
        return some (b, Sos.Poly.neg bTree)
    return none
  | LT.lt _ _ a b =>
    if let some r ← ratLit? a then
      if r = 0 then
        let pTree ← reifyExpr n xFVar b
        return some (b, pTree)
    return none
  | GT.gt _ _ a b =>
    if let some r ← ratLit? b then
      if r = 0 then
        let pTree ← reifyExpr n xFVar a
        return some (a, pTree)
    return none
  | _ => return none

/-! ### Conclusion classification -/

inductive ConclusionShape (n : Nat) where
  | closed (origExpr : Expr) (pTree : Sos.Poly n)
  | strict (origExpr : Expr) (pTree : Sos.Poly n)
  | infeasible

def conclusionShape? (n : Nat) (xFVar : FVarId) (e : Expr) :
    MetaM (Option (ConclusionShape n)) := do
  let e ← whnfR e
  match_expr e with
  | LE.le _ _ a b =>
    if let some r ← ratLit? a then
      if r = 0 then
        let pTree ← reifyExpr n xFVar b
        return some (.closed b pTree)
    return none
  | GE.ge _ _ a b =>
    if let some r ← ratLit? b then
      if r = 0 then
        let pTree ← reifyExpr n xFVar a
        return some (.closed a pTree)
    return none
  | LT.lt _ _ a b =>
    if let some r ← ratLit? a then
      if r = 0 then
        let pTree ← reifyExpr n xFVar b
        return some (.strict b pTree)
    return none
  | GT.gt _ _ a b =>
    if let some r ← ratLit? b then
      if r = 0 then
        let pTree ← reifyExpr n xFVar a
        return some (.strict a pTree)
    return none
  | False => return some (.infeasible)
  | Not q =>
    -- ¬ Q where Q is constraint-shaped: treat as infeasibility with one
    -- extra constraint Q.
    -- For v0.1 we don't fold ¬ into infeasibility automatically; the user
    -- must write the goal in the explicit `→ False` form.
    let _ := q
    return none
  | _ => return none

/-! ### Top-level goal parser -/

/-- Walk a chain of `→` (Pi without dependence) collecting hypothesis
types and the final conclusion. Stops when the binder body refers to
the bound variable (so we don't recurse past the conclusion). -/
partial def stripImplications : Expr → Array Expr × Expr
  | e =>
    match e with
    | .forallE _ ty body bi =>
      if !body.hasLooseBVars && bi.isExplicit then
        let (rest, concl) := stripImplications body
        (#[ty] ++ rest, concl)
      else
        (#[], e)
    | _ => (#[], e)

/-- Parse the main goal of the given metavariable. Returns `none` if
the goal isn't in the v0.1 fragment.

The implementation introduces the bound variable as an FVar via
`withLocalDecl`, so every Expr returned in `ParsedGoal` references
this FVar, which the elaborator then replaces with the real
quantifier-bound variable. -/
def parseGoalFull (mvarId : MVarId) :
    MetaM (Option ParsedGoal) := do
  let goalType ← mvarId.getType >>= instantiateMVars
  let goalType ← whnfR goalType
  let .forallE _ binderType body _ := goalType | return none
  let binderType ← whnfR binderType
  let .forallE _ finN realTy _ := binderType | return none
  unless ← Meta.isDefEq realTy (mkConst ``Real) do return none
  let finN ← whnfR finN
  let .app finK n_expr := finN | return none
  unless finK.isConstOf ``Fin do return none
  let some n ← natLit? n_expr | return none
  withLocalDecl `x .default binderType fun xLocal => do
    let body := body.instantiate1 xLocal
    let xFVar := xLocal.fvarId!
    let (hypsExprs, conclExpr) := stripImplications body
    let mut gs_pTrees : List (Sos.Poly n) := []
    let mut gs_orig_abs : List Lean.Expr := []
    for hExpr in hypsExprs do
      let some (origExpr, pTree) ← constraintExpr? n xFVar hExpr |
        throwError "sos: hypothesis not in supported shape: {indentExpr hExpr}"
      gs_pTrees := gs_pTrees ++ [pTree]
      gs_orig_abs := gs_orig_abs ++ [origExpr.abstract #[xLocal]]
    let some shape ← conclusionShape? n xFVar conclExpr | return none
    match shape with
    | .closed origExpr pTree =>
      return some ⟨n, .closed, some pTree, some (origExpr.abstract #[xLocal]),
                   gs_pTrees, gs_orig_abs⟩
    | .strict origExpr pTree =>
      return some ⟨n, .strict, some pTree, some (origExpr.abstract #[xLocal]),
                   gs_pTrees, gs_orig_abs⟩
    | .infeasible =>
      return some ⟨n, .infeasible, none, none, gs_pTrees, gs_orig_abs⟩

/-- Backwards-compatible thin wrapper: returns the legacy `(n, goal, gs_cmv)` triple. -/
def parseGoal (mvarId : MVarId) :
    MetaM (Option (Σ n, Sos.Goal n × List (CMvPolynomial n ℚ))) := do
  let some parsed ← parseGoalFull mvarId | return none
  return some ⟨parsed.n, parsed.goal, parsed.gs_cmv⟩

end Sos.Reify
