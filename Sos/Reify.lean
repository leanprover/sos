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

/-- The three goal shapes the reifier recognises. -/
inductive ShapeKind where
  | closed
  | strict
  | infeasible
  deriving Inhabited, Repr, DecidableEq

/-- Shape of a constraint hypothesis as written by the user. -/
inductive ConstraintKind where
  /-- `h : 0 ≤ origExpr` (or `origExpr ≥ 0`, `0 < origExpr`, `origExpr > 0`). -/
  | nonneg
  /-- `h : origExpr ≤ 0` (or `0 ≥ origExpr`). The reifier negates the
  polynomial in `pTree` so the certified facet is again `0 ≤ pTree`. -/
  | nonpos
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
  gs_kinds       : List ConstraintKind

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

/-! ### Atom-collection monad

The new design treats the reifier as a `Nat → ℝ`-indexed walker that
accumulates atoms (arbitrary `ℝ`-typed subterms it doesn't recognise
as ring operators or rational literals) into a state array. The
output is a `Sos.Poly.Raw` whose `.var i` references atom `i` in the
final array.

Atom identity uses `withTransparency .reducible` plus pre-normalisation
(`whnfR` + zeta + beta) before the `isDefEq` check, so e.g. `(fun a =>
a) x` collapses with `x` but `f x` and `f y` (distinct FVars) do not. -/

/-- Reifier state: the running atom array. -/
structure ReifyState where
  atoms : Array Expr := #[]

/-- Reifier monad: state-tracking over `MetaM`. -/
abbrev ReifyM := StateRefT ReifyState MetaM

/-- Run a `ReifyM` action with an empty atom array. Returns the action's
result alongside the final atom array. -/
def ReifyM.go {α} (act : ReifyM α) : MetaM (α × Array Expr) := do
  let (a, st) ← StateRefT'.run act ({} : ReifyState)
  return (a, st.atoms)

/-- Run a `ReifyM` action against a pre-existing atom array (so atoms
across multiple reifies share indices). -/
def ReifyM.goWith {α} (atoms : Array Expr) (act : ReifyM α) :
    MetaM (α × Array Expr) := do
  let (a, st) ← StateRefT'.run act ({ atoms } : ReifyState)
  return (a, st.atoms)

/-- Look up `e` in the atom array, deduplicating by `isDefEq` at
`reducible` transparency. Returns the index. -/
def addAtom (e : Expr) : ReifyM Nat := do
  let st ← get
  -- Normalise the candidate atom for stable deduplication. `whnfR`
  -- handles `reducible` definitions, beta, and zeta-reduction of let
  -- bindings; this is what `ring`'s atom collector does.
  let eNorm ← liftM (m := MetaM) (whnfR e)
  for i in [:st.atoms.size] do
    let a := st.atoms[i]!
    let aNorm ← liftM (m := MetaM) (whnfR a)
    if ← liftM (m := MetaM) (Meta.withTransparency .reducible (Meta.isDefEq eNorm aNorm)) then
      return i
  let n := st.atoms.size
  set { st with atoms := st.atoms.push e }
  return n

/-! ### Raw-AST reifier -/

/-- Walk an `Expr` of type `ℝ`, accumulating atoms and producing an
untyped `Sos.Poly.Raw`. Recognises:

  * Rational literals via `ratLit?`.
  * `HAdd`, `HSub`, `HMul` over ℝ.
  * `HPow` with a `Nat`-literal exponent.
  * `Neg`.

Anything else becomes an atom via `addAtom`. -/
partial def reifyRaw (e : Expr) : ReifyM Sos.Poly.Raw := do
  let e ← liftM (m := MetaM) (whnfR e)
  if let some r ← liftM (m := MetaM) (ratLit? e) then
    return Sos.Poly.Raw.const r
  match_expr e with
  | HAdd.hAdd _ _ _ _ a b =>
    return Sos.Poly.Raw.add (← reifyRaw a) (← reifyRaw b)
  | HSub.hSub _ _ _ _ a b =>
    return Sos.Poly.Raw.sub (← reifyRaw a) (← reifyRaw b)
  | HMul.hMul _ _ _ _ a b =>
    return Sos.Poly.Raw.mul (← reifyRaw a) (← reifyRaw b)
  | HPow.hPow _ _ _ _ a k =>
    if let some kNat ← liftM (m := MetaM) (natLit? k) then
      return Sos.Poly.Raw.pow (← reifyRaw a) kNat
    -- Non-literal exponent: opacify the whole pow expression.
    return Sos.Poly.Raw.var (← addAtom e)
  | Neg.neg _ _ a =>
    return Sos.Poly.Raw.neg (← reifyRaw a)
  | _ =>
    return Sos.Poly.Raw.var (← addAtom e)

/-! ### Legacy atom recognition (`Fin n → ℝ` form) -/

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
    MetaM (Option (Expr × Sos.Poly n × ConstraintKind)) := do
  let h ← whnfR h
  match_expr h with
  | LE.le _ _ a b =>
    if let some r ← ratLit? a then
      if r = 0 then
        let pTree ← reifyExpr n xFVar b
        return some (b, pTree, .nonneg)
    if let some r ← ratLit? b then
      if r = 0 then
        let aTree ← reifyExpr n xFVar a
        return some (a, Sos.Poly.neg aTree, .nonpos)
    return none
  | GE.ge _ _ a b =>
    if let some r ← ratLit? b then
      if r = 0 then
        let pTree ← reifyExpr n xFVar a
        return some (a, pTree, .nonneg)
    if let some r ← ratLit? a then
      if r = 0 then
        let bTree ← reifyExpr n xFVar b
        return some (b, Sos.Poly.neg bTree, .nonpos)
    return none
  | LT.lt _ _ a b =>
    if let some r ← ratLit? a then
      if r = 0 then
        let pTree ← reifyExpr n xFVar b
        return some (b, pTree, .nonneg)
    return none
  | GT.gt _ _ a b =>
    if let some r ← ratLit? b then
      if r = 0 then
        let pTree ← reifyExpr n xFVar a
        return some (a, pTree, .nonneg)
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
types and the final conclusion. Recognises `Not Q` as `Q → False`. -/
partial def stripImplications : Expr → MetaM (Array Expr × Expr)
  | e => do
    let e ← whnfR e
    match e with
    | .forallE _ ty body bi =>
      if !body.hasLooseBVars && bi.isExplicit then
        let (rest, concl) ← stripImplications body
        return (#[ty] ++ rest, concl)
      else
        return (#[], e)
    | _ =>
      -- Handle `Not Q` explicitly: unfold to `Q → False` and recurse.
      match_expr e with
      | Not q =>
        let (rest, concl) ← stripImplications (Lean.mkConst ``False)
        return (#[q] ++ rest, concl)
      | _ => return (#[], e)

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
    let (hypsExprs, conclExpr) ← stripImplications body
    let mut gs_pTrees : List (Sos.Poly n) := []
    let mut gs_orig_abs : List Lean.Expr := []
    let mut gs_kinds : List ConstraintKind := []
    for hExpr in hypsExprs do
      let some (origExpr, pTree, kind) ← constraintExpr? n xFVar hExpr |
        throwError "sos: hypothesis not in supported shape: {indentExpr hExpr}"
      gs_pTrees := gs_pTrees ++ [pTree]
      gs_orig_abs := gs_orig_abs ++ [origExpr.abstract #[xLocal]]
      gs_kinds := gs_kinds ++ [kind]
    let some shape ← conclusionShape? n xFVar conclExpr | return none
    match shape with
    | .closed origExpr pTree =>
      return some ⟨n, .closed, some pTree, some (origExpr.abstract #[xLocal]),
                   gs_pTrees, gs_orig_abs, gs_kinds⟩
    | .strict origExpr pTree =>
      return some ⟨n, .strict, some pTree, some (origExpr.abstract #[xLocal]),
                   gs_pTrees, gs_orig_abs, gs_kinds⟩
    | .infeasible =>
      return some ⟨n, .infeasible, none, none, gs_pTrees, gs_orig_abs, gs_kinds⟩

/-- Backwards-compatible thin wrapper: returns the legacy `(n, goal, gs_cmv)` triple. -/
def parseGoal (mvarId : MVarId) :
    MetaM (Option (Σ n, Sos.Goal n × List (CMvPolynomial n ℚ))) := do
  let some parsed ← parseGoalFull mvarId | return none
  return some ⟨parsed.n, parsed.goal, parsed.gs_cmv⟩

/-! ### Atomic parser (Task 2 of the atom-bridge refactor)

The conservative parser operates directly on the main goal:
introducing ∀ binders (when the binder type is ℝ), introducing
constraint hypotheses (when their shape is recognised), and reifying
the conclusion / each constraint into `Sos.Poly.Raw` against a
shared atom array.

Each speculative intro is wrapped in `Tactic.saveState` /
`state.restore`, so a reify failure deeper in the parser doesn't
leave the local context polluted with introduced binders.
-/

/-- Output of `parseGoalAtomic`. The reified polynomials are kept as
untyped `Sos.Poly.Raw`; the elaborator casts them to `Sos.Poly n` at
`n = atoms.size` via `Raw.cast`. -/
structure AtomicParsedGoal where
  /-- Atom Exprs collected from the conclusion and constraints. -/
  atoms    : Array Expr
  /-- Coarse shape of the conclusion. -/
  shape    : ShapeKind
  /-- Reified conclusion. `none` iff `shape = .infeasible`. -/
  rawConcl : Option Sos.Poly.Raw
  /-- Reified constraint polynomials. Indices align with `gsKinds`
  and `hFVars`. -/
  rawGs    : List Sos.Poly.Raw
  /-- Constraint kinds (.nonneg or .nonpos). -/
  gsKinds  : List ConstraintKind
  /-- FVarIds of intro'd constraint hypotheses. The hypothesis at
  index `i` proves `0 ≤ origGᵢ` (or `origGᵢ ≤ 0` if `gsKinds[i] =
  .nonpos`), where `origGᵢ` is the original `ℝ` expression. -/
  hFVars   : Array FVarId

/-- Atomic parser entry. Steps through the main goal:

  1. If the conclusion matches a recognised shape (`0 ≤ p`, `0 < p`,
     `False`, `Not (q ≤ 0)`, `Not (q < 0)`), reify it via `reifyRaw`
     against the running atom array, package, return.
  2. Otherwise, if the conclusion is `∀ x : ℝ, body`, intro the
     binder and recurse.
  3. Otherwise, if the conclusion is `g → body` where `g` matches a
     recognised constraint shape that reifies cleanly, intro the
     hypothesis FVar, record `(hFVar, kind, rawG)`, recurse.
  4. Otherwise, restore the saved state and return `none`.

The first step is "atomic" in the SaveState sense: any partial
intros from steps 2/3 are rolled back if step 1 ultimately fails. -/
partial def parseGoalAtomicAux
    (atoms : Array Expr) (rawGs : List Sos.Poly.Raw)
    (gsKinds : List ConstraintKind) (hFVars : Array FVarId) :
    Tactic.TacticM (Option AtomicParsedGoal) := Tactic.withMainContext do
  let mv ← Tactic.getMainGoal
  let goalType ← mv.getType >>= instantiateMVars
  -- Step 1: try a recognised-conclusion match first.
  if let some out ←
      tryReifyConclusion goalType atoms rawGs gsKinds hFVars then
    return some out
  -- Step 2 / 3: descend into ∀ or →.
  let goalType' ← whnfR goalType
  if let .forallE _ binderType body _ := goalType' then
    if !body.hasLooseBVars then
      return ← tryConstraintIntro goalType' atoms rawGs gsKinds hFVars
    if (← Meta.isDefEq binderType (Lean.mkConst ``Real)) then
      let st ← Tactic.saveState
      let (_, mv') ← mv.intro1
      Tactic.replaceMainGoal [mv']
      match ← parseGoalAtomicAux atoms rawGs gsKinds hFVars with
      | some out => return some out
      | none => st.restore; return none
  return none
where
  /-- Try to match the goal against a recognised conclusion shape.
  Reifies via `reifyRaw` against the running `atoms`. -/
  tryReifyConclusion (goalType : Expr) (atoms : Array Expr)
      (rawGs : List Sos.Poly.Raw) (gsKinds : List ConstraintKind)
      (hFVars : Array FVarId) :
      Tactic.TacticM (Option AtomicParsedGoal) := do
    let goalType ← whnfR goalType
    match_expr goalType with
    | LE.le _ _ a b =>
      let some r ← ratLit? a | return none
      unless r = 0 do return none
      let some (raw, atoms') ← tryReify b atoms | return none
      return some
        { atoms := atoms', shape := .closed, rawConcl := some raw,
          rawGs, gsKinds, hFVars }
    | LT.lt _ _ a b =>
      let some r ← ratLit? a | return none
      unless r = 0 do return none
      let some (raw, atoms') ← tryReify b atoms | return none
      return some
        { atoms := atoms', shape := .strict, rawConcl := some raw,
          rawGs, gsKinds, hFVars }
    | False =>
      return some
        { atoms, shape := .infeasible, rawConcl := none,
          rawGs, gsKinds, hFVars }
    | _ => return none
  /-- Try to recognise `g → body` and recurse. The hypothesis must
  reify cleanly under the current atom set; otherwise we restore. -/
  tryConstraintIntro (goalType : Expr) (atoms : Array Expr)
      (rawGs : List Sos.Poly.Raw) (gsKinds : List ConstraintKind)
      (hFVars : Array FVarId) :
      Tactic.TacticM (Option AtomicParsedGoal) := do
    let .forallE _ hypType body _ := goalType | return none
    unless !body.hasLooseBVars do return none
    let some (kind, rawG, atoms') ← recogniseConstraint hypType atoms | return none
    let st ← Tactic.saveState
    let mv ← Tactic.getMainGoal
    let (hFV, mv') ← mv.intro `h
    Tactic.replaceMainGoal [mv']
    match ← parseGoalAtomicAux atoms' (rawGs ++ [rawG])
        (gsKinds ++ [kind]) (hFVars.push hFV) with
    | some out => return some out
    | none => st.restore; return none
  /-- Run `reifyRaw` against the current atom array, returning none
  if reify throws. -/
  tryReify (e : Expr) (atoms : Array Expr) :
      Tactic.TacticM (Option (Sos.Poly.Raw × Array Expr)) := do
    try
      let (raw, atoms') ← (reifyRaw e).goWith atoms
      return some (raw, atoms')
    catch _ =>
      return none
  /-- Recognise a constraint hypothesis and reify its polynomial side. -/
  recogniseConstraint (h : Expr) (atoms : Array Expr) :
      Tactic.TacticM (Option (ConstraintKind × Sos.Poly.Raw × Array Expr)) := do
    let h ← whnfR h
    match_expr h with
    | LE.le _ _ a b =>
      if let some r ← ratLit? a then
        if r = 0 then
          let some (raw, atoms') ← tryReify b atoms | return none
          return some (.nonneg, raw, atoms')
      if let some r ← ratLit? b then
        if r = 0 then
          let some (raw, atoms') ← tryReify a atoms | return none
          return some (.nonpos, .neg raw, atoms')
      return none
    | LT.lt _ _ a b =>
      let some r ← ratLit? a | return none
      unless r = 0 do return none
      let some (raw, atoms') ← tryReify b atoms | return none
      return some (.nonneg, raw, atoms')
    | _ => return none

/-- Scan the local context for hypothesis FVars matching a constraint
shape, and merge them into `pg`. Skips FVars already in `pg.hFVars`
(intro'd by the iterative parser) and FVars whose type isn't `Prop`. -/
def mergeLocalCtxConstraints (pg : AtomicParsedGoal) :
    Tactic.TacticM AtomicParsedGoal := Tactic.withMainContext do
  let mut atoms := pg.atoms
  let mut rawGs := pg.rawGs
  let mut gsKinds := pg.gsKinds
  let mut hFVars := pg.hFVars
  let lctx ← Lean.getLCtx
  for ldecl in lctx do
    if ldecl.isImplementationDetail then continue
    if hFVars.contains ldecl.fvarId then continue
    -- Only look at hypotheses of type Prop.
    let ty ← Lean.Meta.inferType ldecl.type
    unless ty.isProp do continue
    -- Try to recognise as a constraint.
    match_expr (← whnfR ldecl.type) with
    | LE.le _ _ a b =>
      if let some r ← ratLit? a then
        if r = 0 then
          try
            let (raw, atoms') ← (reifyRaw b).goWith atoms
            atoms := atoms'
            rawGs := rawGs ++ [raw]
            gsKinds := gsKinds ++ [.nonneg]
            hFVars := hFVars.push ldecl.fvarId
          catch _ => pure ()
      else if let some r ← ratLit? b then
        if r = 0 then
          try
            let (raw, atoms') ← (reifyRaw a).goWith atoms
            atoms := atoms'
            rawGs := rawGs ++ [Sos.Poly.Raw.neg raw]
            gsKinds := gsKinds ++ [.nonpos]
            hFVars := hFVars.push ldecl.fvarId
          catch _ => pure ()
    | LT.lt _ _ a b =>
      if let some r ← ratLit? a then
        if r = 0 then
          try
            let (raw, atoms') ← (reifyRaw b).goWith atoms
            atoms := atoms'
            rawGs := rawGs ++ [raw]
            gsKinds := gsKinds ++ [.nonneg]
            hFVars := hFVars.push ldecl.fvarId
          catch _ => pure ()
    | _ => pure ()
  return { pg with atoms, rawGs, gsKinds, hFVars }

/-- Top-level entry. Intros all parseable ∀-binders and constraint
hypotheses, scans the local context for additional constraint
hypotheses, then returns the parsed goal. Returns `none` if the
conclusion isn't in the supported fragment. -/
def parseGoalAtomic : Tactic.TacticM (Option AtomicParsedGoal) := do
  let st ← Tactic.saveState
  match ← parseGoalAtomicAux #[] [] [] #[] with
  | some out => return some (← mergeLocalCtxConstraints out)
  | none => st.restore; return none

end Sos.Reify
