/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Lift ℕ / ℤ / ℚ goals to ℝ before the rest of the `sos` pipeline.

Runs as a pre-pass before `parseGoalAtomic`: introduces all leading
universal binders whose type lies in `{ℕ, ℤ, ℚ, ℝ}`, splits equality
conclusions via `le_antisymm`, rewrites ℕ/ℤ strict inequalities via
`lt_iff_add_one_le`, applies the cast bridge (`Nat.cast_le.mp`, etc.)
on the conclusion, runs `rify at *` to normalise hypotheses and casts,
then adds a `0 ≤ (↑a : ℝ)` hypothesis for every ℕ-typed cast atom now
appearing in the goal.

The pre-pass is a no-op when the goal is already entirely over ℝ.
-/
import SOS.Reify
import Mathlib.Tactic.Rify
import Mathlib.Tactic.Linarith

namespace SOS.Lift

open Lean Elab Tactic Meta

initialize Lean.registerTraceClass `sos.lift

/-- The recognised source domains for the lift pre-pass. -/
inductive Domain where
  | nat | int | rat | real
  deriving Inhabited, Repr, DecidableEq

/-- Recognise one of ℕ, ℤ, ℚ, ℝ as a `Domain`. Returns `none` for
anything else (including dependent or function-type binders). -/
def domainOf? (α : Expr) : MetaM (Option Domain) := do
  let α ← whnfR α
  if α.isConstOf ``Nat then return some .nat
  if α.isConstOf ``Int then return some .int
  if α.isConstOf ``Rat then return some .rat
  if α.isConstOf ``Real then return some .real
  return none

/-! ### Out-of-scope operator detection

Walks the original (pre-lift) goal Expr looking for ℕ subtraction.
Elaborates as an overloaded `HSub` node; detection inspects the
type-class argument.

ℕ/ℤ DIV/MOD are no longer rejected here: they're enriched in-place
by `enrichDivMod` (see below), which introduces ℝ-typed witness
equalities and bounds for each `a / b` / `a % b` site. Sites whose
divisor positivity is decidable by `omega` (positive numeric literals
or non-literal divisors with `n ≠ 0` / `0 < n` / `m < n` in scope)
get the full witness suite; the strict-bound witness is silently
dropped for sites that don't, leaving an opaque atom for that site —
the reifier still picks up the unconditional witnesses but the
search may not certify. -/

private def realConst : Expr := Lean.mkConst ``Real

/-- Throw if the expression tree contains `Nat.sub` (`HSub` over ℕ).
Walks `e` recursively. -/
partial def checkUnsupportedOps (e : Expr) : MetaM Unit := do
  match_expr e with
  | HSub.hSub α _ _ _ a b =>
    let αn ← whnfR α
    if αn.isConstOf ``Nat then
      throwError "sos: `by sos` does not handle truncated ℕ subtraction \
        in goals; cast to `Int.sub`, or rewrite via `Nat.sub_eq` with \
        `m ≤ n` in context."
    checkUnsupportedOps a; checkUnsupportedOps b
  | _ =>
    match e with
    | .app f a => checkUnsupportedOps f; checkUnsupportedOps a
    | .lam _ _ b _ => checkUnsupportedOps b
    | .forallE _ t b _ => checkUnsupportedOps t; checkUnsupportedOps b
    | .mdata _ b => checkUnsupportedOps b
    | _ => pure ()

/-! ### ℕ/ℤ DIV/MOD enrichment (issue #24, #45)

Harrison's `SOS_RULE` battery includes goals like `n ≤ n*n + n / 2 +
n % 2` where the discrete-arithmetic operators `/` and `%` over
ℕ / ℤ are essential. The SOS reifier only speaks ℝ ring arithmetic;
treating `a / b` as an opaque atom loses the algebraic relationship
between divisor, quotient, and remainder.

The enrichment pre-pass walks the post-binder-intro goal, finds each
maximal `a / b` and `a % b` subterm (over ℕ or ℤ), and tries to
introduce ℝ-typed witness hypotheses

  * `hdm : (a : ℝ) = b * (a / b) + a % b`        — div/mod identity
  * `hnn : (0 : ℝ) ≤ a % b`                       — remainder ≥ 0
  * `hgap : (0 : ℝ) ≤ b - (a % b) - 1`            — remainder < b

These three encode the algebraic content of Euclidean division. The
SOS reifier then sees `↑(a/b)` and `↑(a%b)` as atoms tied together by
the witness constraints, which is enough for Putinar / Schmüdgen-style
certificates to use them.

Each `have` is wrapped in `try`, with the strict-bound witness routed
through an `omega` call on `0 < b`. This subsumes both the positive
literal divisor case (issue #24 — `omega` decides `0 < 7` trivially)
and the non-literal divisor case (issue #45 — `omega` derives `0 < n`
from any `n ≠ 0`, `0 < n`, `m < n`, etc. already in the local context).
Sites whose positivity can't be derived just lose the strict-bound
witness; the unconditional identity and remainder-nonneg facts are
still added. For ℕ, `Nat.div_add_mod` and `Nat.zero_le` hold without
preconditions; for ℤ, `Int.emod_nonneg` and `Int.emod_lt_of_pos` both
require an `omega`-derived bound on the divisor.

For ℤ we only handle `Int.ediv` / `Int.emod` (which is what
`(a : Int) / (b : Int)` elaborates to in Lean 4); T-division
`Int.div` would need different witness inequalities and is out of
scope. -/

/-- A DIV/MOD site to enrich: the source domain (ℕ or ℤ), the
dividend `a`, and the divisor expression `b`. The same `(domain, a,
b)` triple may be the dividend/divisor of both `a / b` and `a % b`;
we record one site for the pair. -/
private structure DivModSite where
  domain : Domain     -- `.nat` or `.int` only
  num    : Expr       -- the dividend `a`
  denExpr : Expr      -- the divisor expression `b`

/-- Local names used for the canonical quotient/remainder witnesses
introduced for a DIV/MOD site. -/
private structure DivModLocals where
  q : Expr
  r : Expr

/-- Look up an existing `DivModSite` matching `(domain, num, denExpr)`.
Compares both `num` and `denExpr` via `isDefEq` at reducible
transparency. -/
private def findSite (sites : Array DivModSite) (domain : Domain) (num denExpr : Expr) :
    MetaM (Option DivModSite) := do
  for s in sites do
    if s.domain = domain then
      if ← Meta.withTransparency .reducible (Meta.isDefEq s.num num) then
        if ← Meta.withTransparency .reducible (Meta.isDefEq s.denExpr denExpr) then
          return some s
  return none

/-- Walk `e` collecting DIV/MOD sites. `acc` is the running list of
unique sites, keyed by `(domain, num, denExpr)`.

Matches both the `HDiv.hDiv` / `HMod.hMod` user syntax form and the
raw `Nat.div`, `Nat.mod`, `Int.ediv`, `Int.emod` constants in case a
prior `simp` or unfold step has elaborated the heterogeneous instance
away. -/
partial def collectDivModSites (e : Expr) (acc : Array DivModSite := #[]) :
    MetaM (Array DivModSite) := do
  let record (domain : Domain) (a b : Expr) (acc : Array DivModSite) :
      MetaM (Array DivModSite) := do
    if (← findSite acc domain a b).isSome then return acc
    return acc.push { domain, num := a, denExpr := b }
  let recordHDivOrHMod (α a b : Expr) (acc : Array DivModSite) :
      MetaM (Array DivModSite) := do
    let acc ← collectDivModSites a acc
    let acc ← collectDivModSites b acc
    let αn ← whnfR α
    if αn.isConstOf ``Nat then record .nat a b acc
    else if αn.isConstOf ``Int then record .int a b acc
    else return acc
  match_expr e with
  | HDiv.hDiv α _ _ _ a b => recordHDivOrHMod α a b acc
  | HMod.hMod α _ _ _ a b => recordHDivOrHMod α a b acc
  | Nat.div a b =>
    let acc ← collectDivModSites a acc
    let acc ← collectDivModSites b acc
    record .nat a b acc
  | Nat.mod a b =>
    let acc ← collectDivModSites a acc
    let acc ← collectDivModSites b acc
    record .nat a b acc
  | Int.ediv a b =>
    let acc ← collectDivModSites a acc
    let acc ← collectDivModSites b acc
    record .int a b acc
  | Int.emod a b =>
    let acc ← collectDivModSites a acc
    let acc ← collectDivModSites b acc
    record .int a b acc
  | _ =>
    match e with
    | .app f a =>
      let acc ← collectDivModSites f acc
      collectDivModSites a acc
    | .lam _ t b _ =>
      let acc ← collectDivModSites t acc
      collectDivModSites b acc
    | .forallE _ t b _ =>
      let acc ← collectDivModSites t acc
      collectDivModSites b acc
    | .mdata _ b => collectDivModSites b acc
    | _ => return acc

/-- Introduce local quotient/remainder definitions for `site` and rewrite
all ordinary hypotheses and the goal through those locals.

This is the single source of truth for a DIV/MOD site during a lift/refute
pass: the generated witness hypotheses and the target/refute constraint both
mention the same locals, so the reifier cannot split `a / b` and `a % b`
occurrences into separate witness-side and goal-side atoms. -/
private def localizeSite (site : DivModSite) : TacticM DivModLocals := withMainContext do
  let aStx ← Elab.Term.exprToSyntax site.num
  let bStx ← Elab.Term.exprToSyntax site.denExpr
  let before := (← Lean.getLCtx).foldl (init := #[]) fun acc ldecl => acc.push ldecl.fvarId
  match site.domain with
  | .nat =>
    evalTactic <| ← `(tactic| set sos_q : ℕ := ($aStx : ℕ) / ($bStx : ℕ) with _sos_hq)
    evalTactic <| ← `(tactic| set sos_r : ℕ := ($aStx : ℕ) % ($bStx : ℕ) with _sos_hr)
    evalTactic <| ← `(tactic| rw [← _sos_hq, ← _sos_hr] at *)
    evalTactic <| ← `(tactic| clear _sos_hq _sos_hr)
  | .int =>
    evalTactic <| ← `(tactic| set sos_q : ℤ := ($aStx : ℤ) / ($bStx : ℤ) with _sos_hq)
    evalTactic <| ← `(tactic| set sos_r : ℤ := ($aStx : ℤ) % ($bStx : ℤ) with _sos_hr)
    evalTactic <| ← `(tactic| rw [← _sos_hq, ← _sos_hr] at *)
    evalTactic <| ← `(tactic| clear _sos_hq _sos_hr)
  | _ => throwError "localizeSite: unsupported DIV/MOD domain"
  let lctx ← withMainContext Lean.getLCtx
  let mut newDecls : Array LocalDecl := #[]
  for ldecl in lctx do
    if before.contains ldecl.fvarId then continue
    unless (← domainOf? ldecl.type) = some site.domain do continue
    newDecls := newDecls.push ldecl
  let some qDecl := newDecls[0]? |
    throwError "localizeSite: failed to introduce quotient local"
  let some rDecl := newDecls[1]? |
    throwError "localizeSite: failed to introduce remainder local"
  return { q := mkFVar qDecl.fvarId, r := mkFVar rDecl.fvarId }

/-- Introduce ℝ-typed witness hypotheses for one localized DIV/MOD site:

  * `hdm : (↑a : ℝ) = ↑b * ↑q + ↑r`
  * `hnn : (0 : ℝ) ≤ ↑r`
  * `hgap : (0 : ℝ) ≤ ↑b - ↑r - 1`

The local quotient/remainder are definitionally `a / b` and `a % b`,
but all visible constraints use the locals, matching the rewritten target. -/
def enrichLocalizedSite (site : DivModSite) (locals : DivModLocals) : TacticM Unit :=
    withMainContext do
  let a := site.num
  let b := site.denExpr
  let q := locals.q
  let r := locals.r
  let aStx ← Elab.Term.exprToSyntax a
  let bStx ← Elab.Term.exprToSyntax b
  let qStx ← Elab.Term.exprToSyntax q
  let rStx ← Elab.Term.exprToSyntax r
  -- The div/mod identity, remainder-nonneg, and remainder-bound lemmas
  -- differ between ℕ and ℤ. We synthesise the proof terms via `by`
  -- blocks rather than `mkAppM` so `push_cast` / `linarith` can do the
  -- arithmetic normalisation in one shot.
  match site.domain with
  | .nat =>
    -- `Nat.div_add_mod` and `Nat.zero_le` are unconditional; failures
    -- here are bugs, not optional features, so we do not soft-fail.
    evalTactic <| ← `(tactic|
      have _sos_hdm : (($aStx : ℕ) : ℝ) = (($bStx : ℕ) : ℝ) * (($qStx : ℕ) : ℝ)
          + (($rStx : ℕ) : ℝ) :=
        by exact_mod_cast (Nat.div_add_mod ($aStx : ℕ) $bStx).symm)
    evalTactic <| ← `(tactic|
      have _sos_hnn : (0 : ℝ) ≤ (($rStx : ℕ) : ℝ) :=
        by exact_mod_cast Nat.zero_le ($rStx : ℕ))
    -- `Nat.mod_lt` needs `0 < b`; route through `omega`, which decides
    -- positive literals trivially and pulls positivity from in-scope
    -- `b ≠ 0` / `0 < b` / `m < b` hypotheses for non-literal divisors.
    -- Soft-failed: a site without an in-scope positivity fact simply
    -- loses this witness.
    evalTactic <| ← `(tactic|
      first
        | have _sos_hgap : (0 : ℝ) ≤ (($bStx : ℕ) : ℝ) - (($rStx : ℕ) : ℝ) - 1 := by
            have hpos : (0 : ℕ) < ($bStx : ℕ) := by omega
            have h : ($aStx : ℕ) % $bStx + 1 ≤ $bStx := Nat.mod_lt ($aStx : ℕ) hpos
            have h' : ((($aStx : ℕ) % $bStx + 1 : ℕ) : ℝ) ≤ ((($bStx : ℕ) : ℝ)) :=
              by exact_mod_cast h
            push_cast at h' ⊢
            linarith
        | skip)
  | .int =>
    -- `Int.emod_add_ediv` (via `Int.mul_ediv_add_emod`) is unconditional;
    -- failures here are bugs.
    evalTactic <| ← `(tactic|
      have _sos_hdm : (($aStx : ℤ) : ℝ) = (($bStx : ℤ) : ℝ) * (($qStx : ℤ) : ℝ)
          + (($rStx : ℤ) : ℝ) :=
        by exact_mod_cast (Int.mul_ediv_add_emod ($aStx : ℤ) $bStx).symm)
    -- `Int.emod_nonneg` needs `b ≠ 0`; `Int.emod_lt_of_pos` needs
    -- `0 < b`. Both flow through `omega`; both soft-fail.
    evalTactic <| ← `(tactic|
      first
        | have _sos_hnn : (0 : ℝ) ≤ (($rStx : ℤ) : ℝ) := by
            have hne : ($bStx : ℤ) ≠ 0 := by omega
            have h : (0 : ℤ) ≤ ($aStx : ℤ) % $bStx := Int.emod_nonneg _ hne
            exact_mod_cast h
        | skip)
    evalTactic <| ← `(tactic|
      first
        | have _sos_hgap : (0 : ℝ) ≤ (($bStx : ℤ) : ℝ) - (($rStx : ℤ) : ℝ) - 1 := by
            have hpos : (0 : ℤ) < ($bStx : ℤ) := by omega
            have h : ($aStx : ℤ) % $bStx + 1 ≤ $bStx :=
              Int.add_one_le_iff.mpr (Int.emod_lt_of_pos _ hpos)
            have h' : ((($aStx : ℤ) % $bStx + 1 : ℤ) : ℝ) ≤ ((($bStx : ℤ) : ℝ)) :=
              by exact_mod_cast h
            push_cast at h' ⊢
            linarith
        | skip)
  | _ => pure ()

/-- The shared user-name prefix for hypotheses introduced by
`enrichLocalizedSite`. Hypotheses whose user name starts with this string are
skipped during the local-context scan in `enrichDivMod`, so a
recursive entry into `liftToReal` (e.g. after an `apply le_antisymm`
split on an equality conclusion) doesn't re-enrich the same site by
rediscovering its own witnesses. -/
private def witnessNamePrefix : String := "_sos_h"

/-- True if `name`'s user-facing string starts with `witnessNamePrefix`,
ignoring macro scopes that elaboration may have appended. -/
private def isWitnessHyp (name : Name) : Bool :=
  name.eraseMacroScopes.toString.startsWith witnessNamePrefix

/-- Walk the current goal and all local hypothesis types, collect
every DIV/MOD site over ℕ/ℤ, and introduce witness hypotheses for
each. The conditional witnesses (strict-bound, plus ℤ remainder-nonneg)
are routed through `omega` on the divisor positivity and silently
dropped when omega fails; see `enrichLocalizedSite`.

Skips hypotheses already produced by a prior `enrichLocalizedSite` (identified
by `witnessNamePrefix`-prefixed user names) so this is idempotent
under recursive calls. -/
def enrichDivMod : TacticM Unit := withMainContext do
  let mv ← getMainGoal
  let goal ← mv.getType >>= instantiateMVars
  let mut sites ← collectDivModSites goal
  -- Also scan hypothesis types — `introLeadingBindersAux` has already
  -- moved leading hypothesis binders into the local context, so any
  -- `a / b` / `a % b` over ℕ/ℤ inside them needs the same enrichment.
  let lctx ← Lean.getLCtx
  for ldecl in lctx do
    if ldecl.isImplementationDetail then continue
    -- Skip our own previously-introduced witness hypotheses; otherwise
    -- their RHS (which contains `↑(a / b)` and `↑(a % b)`) would
    -- re-trigger enrichment on the same site after every recursive
    -- entry into `liftToReal` / `refuteToReal`.
    if isWitnessHyp ldecl.userName then continue
    let ty ← instantiateMVars ldecl.type
    if (← Meta.inferType ty).isProp then
      sites ← collectDivModSites ty sites
  trace[sos.lift] "enrichDivMod: found {sites.size} DIV/MOD site(s)"
  for site in sites do
    let locals ← localizeSite site
    enrichLocalizedSite site locals

/-! ### Leading-binder intros

Intros all leading universal binders whose type is one of ℕ/ℤ/ℚ/ℝ,
and all non-dependent (hypothesis) binders whose type is a `Prop`.
Stops on anything else, so `parseGoalAtomic` still gets to attempt
its speculative constraint intros on the remaining goal if for some
reason we didn't intro a hypothesis.

We intro hypothesis binders here so that `rify at *` can lift their
types from ℕ/ℤ/ℚ to ℝ before the SOS reifier sees them; otherwise
hypotheses like `0 ≤ n` over ℕ would slip past the reifier (which
only recognises ℝ-typed constraints). -/

partial def introLeadingBindersAux : TacticM Unit := withMainContext do
  let mv ← getMainGoal
  let goal ← mv.getType >>= instantiateMVars
  let goal ← whnfR goal
  let .forallE _ ty body _ := goal | return
  if body.hasLooseBVars then
    -- Dependent forall: only intro if the binder type is numeric.
    let some _ ← domainOf? ty | return
    let (_, mv') ← mv.intro1
    replaceMainGoal [mv']
    introLeadingBindersAux
  else
    -- Non-dependent forall (hypothesis): intro iff it's a Prop, so
    -- that `rify at *` can lift it before the reifier runs.
    if (← Meta.inferType ty).isProp then
      let (_, mv') ← mv.intro1
      replaceMainGoal [mv']
      introLeadingBindersAux

/-! ### Conclusion-shape dispatch -/

/-- Coarse classification of the conclusion relation. -/
inductive ConclShape where
  | le (α : Expr)         -- `LE.le α _ _ _`
  | lt (α : Expr)         -- `LT.lt α _ _ _`
  | eq (α : Expr)         -- `Eq α _ _`
  | false_                -- `False`
  | other
  deriving Inhabited

/-- Classify the current goal type. -/
def classifyConcl (goal : Expr) : MetaM ConclShape := do
  let goal ← whnfR goal
  match_expr goal with
  | LE.le α _ _ _ => return .le α
  | LT.lt α _ _ _ => return .lt α
  | Eq α _ _ => return .eq α
  | False => return .false_
  | _ => return .other

/-! ### Cast-bridge application

`Nat.cast_le {α} [...] {m n : ℕ} : (↑m : α) ≤ ↑n ↔ m ≤ n`. To prove
the source-domain side from the ℝ side we use `.mp`. -/

private def castLeMpStx (d : Domain) : MetaM (TSyntax `tactic) := do
  match d with
  | .nat => `(tactic| refine (Nat.cast_le (α := ℝ)).mp ?_)
  | .int => `(tactic| refine (Int.cast_le (R := ℝ)).mp ?_)
  | .rat => `(tactic| refine (Rat.cast_le (K := ℝ)).mp ?_)
  | .real => throwError "castLeMpStx: domain already ℝ"

private def castLtMpStx (d : Domain) : MetaM (TSyntax `tactic) := do
  match d with
  | .nat => `(tactic| refine (Nat.cast_lt (α := ℝ)).mp ?_)
  | .int => `(tactic| refine (Int.cast_lt (R := ℝ)).mp ?_)
  | .rat => `(tactic| refine (Rat.cast_lt (K := ℝ)).mp ?_)
  | .real => throwError "castLtMpStx: domain already ℝ"

/-! ### ℕ-cast atom harvesting

After `rify`, the goal Expr may contain subterms `↑a : ℝ` where
`a : ℕ`. Each such atom is non-negative; adding `0 ≤ ↑a` as a local
hypothesis lets the SOS reifier treat `↑a` as a constrained atom. -/

/-- True if `e` is `@Nat.cast α _ a` or `@NatCast.natCast α _ a` with
codomain `α` reducing to ℝ. -/
private def isNatCastToReal (e : Expr) : MetaM Bool := do
  match_expr e with
  | Nat.cast α _ _ =>
    return (← whnfR α).isConstOf ``Real
  | NatCast.natCast α _ _ =>
    return (← whnfR α).isConstOf ``Real
  | _ => return false

/-- Walk `e`, collecting `Nat.cast _` applications whose codomain is
ℝ. Deduplicates by `isDefEq`. -/
partial def collectNatCastAtoms (e : Expr) (acc : Array Expr := #[]) :
    MetaM (Array Expr) := do
  if ← isNatCastToReal e then
    -- Descend into the cast's argument first (in case it itself
    -- contains further casts), then add this atom if it's not
    -- already there.
    let acc ← descend e acc
    if (← acc.anyM (fun e' => isDefEq e' e)) then
      return acc
    return acc.push e
  else
    descend e acc
where
  descend (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
    match e with
    | .app f a =>
      let acc ← collectNatCastAtoms f acc
      collectNatCastAtoms a acc
    | .lam _ t b _ =>
      let acc ← collectNatCastAtoms t acc
      collectNatCastAtoms b acc
    | .forallE _ t b _ =>
      let acc ← collectNatCastAtoms t acc
      collectNatCastAtoms b acc
    | .mdata _ b => collectNatCastAtoms b acc
    | _ => return acc

/-- Extract the ℕ-typed operand from a Nat.cast / NatCast.natCast Expr. -/
private def natCastArg? (e : Expr) : Option Expr :=
  match_expr e with
  | Nat.cast _ _ a => some a
  | NatCast.natCast _ _ a => some a
  | _ => none

/-- For each ℕ-cast atom in the current goal **or any local hypothesis**,
add a hypothesis `(0 : ℝ) ≤ ↑a := Nat.cast_nonneg _`.

Scanning hypotheses too matters when the ℕ-cast atom appears only in a
constraint (e.g. `h : (n : ℝ) = x` with `n : ℕ`): `parseGoalAtomic` will
later pick up the atom from the constraint, but without a `0 ≤ ↑n`
hypothesis the SOS reifier loses the nonneg fact, causing search to
fail on goals that are otherwise certifiable. -/
def assertNatCastNonneg : TacticM Unit := withMainContext do
  let goal ← (← getMainGoal).getType >>= instantiateMVars
  let mut atoms ← collectNatCastAtoms goal
  -- Also scan local-context hypothesis types so ℕ-casts that survive
  -- only in `h : (n : ℝ) = …` style hypotheses still get their nonneg
  -- fact.
  let lctx ← Lean.getLCtx
  for ldecl in lctx do
    if ldecl.isImplementationDetail then continue
    let ty ← instantiateMVars ldecl.type
    if (← Meta.inferType ty).isProp then
      atoms ← collectNatCastAtoms ty atoms
  trace[sos.lift] "assertNatCastNonneg: found {atoms.size} ℕ-cast atom(s)"
  for atom in atoms do
    let some natArg := natCastArg? atom | continue
    let proof? : Option Expr ← try
      -- `Nat.cast_nonneg (α := ℝ) natArg : 0 ≤ (↑natArg : ℝ)`.
      -- Signature: `{α} [Semiring α] [PartialOrder α] [IsOrderedRing α] (n : ℕ)`.
      let p ← mkAppOptM ``Nat.cast_nonneg
        #[some realConst, none, none, none, some natArg]
      pure (some p)
    catch _ => pure none
    let some proof := proof? | continue
    let typ ← Meta.inferType proof
    let newMV ← (← getMainGoal).assert `hnn typ proof
    let (_, newMV) ← newMV.intro1
    replaceMainGoal [newMV]

/-! ### `rify` invocation -/

/-- Run `try rify at *` to normalise casts in hypotheses and goal. -/
def runRifyOnAll : TacticM Unit := do
  evalTactic (← `(tactic| try rify at *))

/-! ### Main pre-pass

`liftToReal` is the entry the `sos` tactic calls before
`parseGoalAtomic`. It produces zero or more subgoals, each entirely
over ℝ and ready for the existing reifier.

The recursion handles the equality split: `le_antisymm` produces two
subgoals which both need the rest of the pipeline. -/

partial def liftToReal : TacticM Unit := withMainContext do
  trace[sos.lift] "liftToReal: starting on goal {← (← getMainGoal).getType >>= instantiateMVars}"
  -- Intro all leading numeric universal binders and hypothesis binders
  -- before checking unsupported operators. Checking pre-intro would
  -- reject theorems with `Nat.sub` etc. anywhere in the Π-type,
  -- including unused hypothesis positions; the post-intro conclusion
  -- is what the SOS reifier actually has to handle.
  introLeadingBindersAux
  -- DIV/MOD enrichment runs before `checkUnsupportedOps` so that
  -- ℕ/ℤ `a / b` / `a % b` subterms are supported (issues #24 and
  -- #45): we introduce witness equalities and bounds here, then the
  -- SOS reifier treats `↑(a / b)` and `↑(a % b)` as atoms tied
  -- together by those witnesses.
  enrichDivMod
  let mv ← getMainGoal
  let goal ← mv.getType >>= instantiateMVars
  -- Out-of-scope ops are checked on the conclusion *after* intros but
  -- *before* `rify`, since rify rewrites may obscure the source-domain
  -- operators we want to detect.
  checkUnsupportedOps goal
  let shape ← classifyConcl goal
  match shape with
  | .false_ | .other =>
    -- Nothing more to do here. `parseGoalAtomic` will handle (or
    -- reject) the goal.
    return
  | .eq α =>
    -- Equality conclusion. Determine domain; if non-ℝ, the split is
    -- still over the source domain.
    let some _d ← domainOf? α | return
    evalTactic (← `(tactic| apply le_antisymm))
    let goals ← getGoals
    let mut newGoals : List MVarId := []
    for g in goals do
      setGoals [g]
      liftToReal
      newGoals := newGoals ++ (← getGoals)
    setGoals newGoals
  | .le α =>
    let some d ← domainOf? α |
      -- Unknown source domain. Leave it to the caller; parseGoalAtomic
      -- will produce a sensible error.
      return
    match d with
    | .real =>
      runRifyOnAll
      if (← getGoals).isEmpty then return
      assertNatCastNonneg
    | _ =>
      evalTactic (← castLeMpStx d)
      runRifyOnAll
      if (← getGoals).isEmpty then return
      assertNatCastNonneg
  | .lt α =>
    let some d ← domainOf? α | return
    match d with
    | .real =>
      runRifyOnAll
      if (← getGoals).isEmpty then return
      assertNatCastNonneg
    | .nat =>
      -- Discrete-strict rewrite: `a < b ↔ a + 1 ≤ b`. Then cast bridge.
      evalTactic (← `(tactic| rw [Nat.lt_iff_add_one_le]))
      -- The rewrite may close the goal (e.g. `n < n+1` reduces to
      -- `n+1 ≤ n+1`, which `rw` closes via reflexivity).
      if (← getGoals).isEmpty then return
      evalTactic (← castLeMpStx .nat)
      runRifyOnAll
      if (← getGoals).isEmpty then return
      assertNatCastNonneg
    | .int =>
      evalTactic (← `(tactic| rw [Int.lt_iff_add_one_le]))
      if (← getGoals).isEmpty then return
      evalTactic (← castLeMpStx .int)
      runRifyOnAll
      if (← getGoals).isEmpty then return
      assertNatCastNonneg
    | .rat =>
      evalTactic (← castLtMpStx .rat)
      runRifyOnAll
      if (← getGoals).isEmpty then return
      assertNatCastNonneg

/-! ### Negate-and-refute path (Harrison's `INT_SOS` trick)

For ℕ/ℤ goals that are not in the quadratic module of their constraint
cone over ℝ — e.g. `∀ n : ℕ, n ≤ n*n`, which fails Putinar at the
admissible real point `n = 0.5` — Harrison's `INT_SOS` negates the
conclusion, applies the integer discreteness rewrite
`¬ (a ≤ b) ⟺ b + 1 ≤ a`, and feeds the resulting system of ℤ-side
≤-inequalities to a real infeasibility search. See
https://github.com/jrh13/hol-light/blob/master/Examples/sos.ml#L1336
for `INT_SOS`'s implementation.

We mirror that here:

  1. Intro leading numeric / hypothesis binders (same as `liftToReal`).
  2. `by_contra hneg`, producing `hneg : ¬ <orig_conclusion>` and goal
     `False`.
  3. Push the negation into NNF via `simp only [not_le, not_lt,
     Nat.lt_iff_add_one_le, Int.lt_iff_add_one_le] at hneg`. The result
     has shape `c ≤ d` over ℕ/ℤ (possibly with a `+1` from the
     discreteness rewrite).
  4. `rify at *` casts everything to ℝ, then `assertNatCastNonneg` adds
     `0 ≤ ↑a` for each ℕ-typed cast atom.
  5. `replace hneg := sub_nonneg.mpr hneg` puts the refute hypothesis
     into the `0 ≤ ↑d − ↑c` canonical form that `recogniseConstraint`
     picks up.
  6. The caller routes the `False` goal into the existing `.infeasible`
     SOS arm via `parseGoalAtomic`.

This branch is only attempted when the direct lift (which corresponds to
asking for a Putinar certificate of the original inequality) fails to
close the goal. We do not handle `=`-shape conclusions directly: those
are split by the direct path via `le_antisymm`, and each ≤-subgoal can
then take the refute branch on its own.

Note: `≠`-shape conclusions, which Harrison handles via the disjunction
`¬ (a = b) ⟺ a + 1 ≤ b ∨ b + 1 ≤ a`, are not supported here. The
disjunction would require a case split before search, and the only
canonical Harrison ℕ/ℤ test that exercises it (the `m * n ≠ 0` style)
admits a much shorter `omega`-based proof. -/

partial def refuteToReal : TacticM Unit := withMainContext do
  trace[sos.lift] "refuteToReal: starting on goal {← (← getMainGoal).getType >>= instantiateMVars}"
  introLeadingBindersAux
  enrichDivMod
  let mv ← getMainGoal
  let goal ← mv.getType >>= instantiateMVars
  checkUnsupportedOps goal
  let shape ← classifyConcl goal
  match shape with
  | .eq α =>
    -- Equality conclusion: split via `le_antisymm` and recurse on each
    -- ≤-subgoal. The direct path does the same; here we recurse with
    -- `refuteToReal` so that the refute branch covers both halves.
    let some _ ← domainOf? α | return
    evalTactic (← `(tactic| apply le_antisymm))
    let goals ← getGoals
    let mut newGoals : List MVarId := []
    for g in goals do
      setGoals [g]
      refuteToReal
      newGoals := newGoals ++ (← getGoals)
    setGoals newGoals
  | .le α | .lt α =>
    let some d ← domainOf? α |
      throwError "sos refute: unsupported conclusion domain"
    match d with
    | .nat =>
      evalTactic (← `(tactic| by_contra hneg))
      -- Apply the discreteness rewrite at `*` so that ℕ-typed `<`
      -- hypotheses introduced earlier (e.g. `h : m < n`) also become
      -- `m + 1 ≤ n` — otherwise rify turns them into ℝ-typed `<`
      -- constraints, which `recogniseConstraint` downgrades to nonneg
      -- (losing the strict integrality info) and breaks the search.
      evalTactic (← `(tactic|
        simp only [not_le, not_lt, Nat.lt_iff_add_one_le] at *))
      finishRefute
    | .int =>
      evalTactic (← `(tactic| by_contra hneg))
      evalTactic (← `(tactic|
        simp only [not_le, not_lt, Int.lt_iff_add_one_le] at *))
      finishRefute
    | .rat | .real =>
      -- Refute path adds nothing over the direct path for dense
      -- (ℚ / ℝ) domains: there's no discreteness rewrite.
      throwError "sos refute: not applicable to {repr d} conclusions"
  | .false_ | .other =>
    throwError "sos refute: unsupported conclusion shape"
where
  /-- Finish the refute branch: rify, add ℕ-nonneg hyps, and normalise
  the negated hypothesis to `0 ≤ …` form for the constraint reifier. -/
  finishRefute : TacticM Unit := do
    if (← getGoals).isEmpty then return
    runRifyOnAll
    if (← getGoals).isEmpty then return
    assertNatCastNonneg
    -- `hneg : c ≤ d` (over ℝ after rify) → `hneg : 0 ≤ d − c`. Wrapped
    -- in `try`: if the simp set above closed the hypothesis (e.g. by
    -- reducing the negation to `False`), there's nothing to replace.
    evalTactic (← `(tactic|
      first
        | (replace hneg := sub_nonneg.mpr hneg)
        | skip))
    -- `push_cast at *` normalises any lingering `Nat.cast` / `Int.cast`
    -- subterms to a single canonical instance synthesis. Without this,
    -- `↑n` produced by `rify` and `↑n` produced by `assertNatCastNonneg`
    -- (via `mkAppOptM ``Nat.cast_nonneg`) can land on distinct
    -- type-class instances (`Real.instNatCast` vs the one derived from
    -- `AddMonoidWithOne.toNatCast`); the reifier's atom dedup runs at
    -- `reducible` transparency and does not unify them, splitting `↑n`
    -- across two atoms and breaking the search.
    evalTactic (← `(tactic| try push_cast at *))

end SOS.Lift
