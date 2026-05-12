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

Walks the original (pre-lift) goal Expr looking for ℕ subtraction or
ℕ/ℤ division/modulo. These elaborate as overloaded `HSub` / `HDiv` /
`HMod` nodes; we detect by inspecting the type-class argument. Throws
a hint that points to #24 for DIV/MOD support. -/

private def realConst : Expr := Lean.mkConst ``Real

/-- Throw if the expression tree contains `Nat.sub` (`HSub` over ℕ)
or `HDiv` / `HMod` over ℕ or ℤ. Walks `e` recursively. -/
partial def checkUnsupportedOps (e : Expr) : MetaM Unit := do
  match_expr e with
  | HSub.hSub α _ _ _ a b =>
    let αn ← whnfR α
    if αn.isConstOf ``Nat then
      throwError "sos: `by sos` does not handle truncated ℕ subtraction \
        in goals; cast to `Int.sub`, or rewrite via `Nat.sub_eq` with \
        `m ≤ n` in context."
    checkUnsupportedOps a; checkUnsupportedOps b
  | HDiv.hDiv α _ _ _ a b =>
    let αn ← whnfR α
    if αn.isConstOf ``Nat || αn.isConstOf ``Int then
      throwError "sos: `by sos` does not handle `Nat.div` / `Int.div`; \
        DIV / MOD support is tracked in \
        https://github.com/kim-em/sos/issues/24."
    checkUnsupportedOps a; checkUnsupportedOps b
  | HMod.hMod α _ _ _ a b =>
    let αn ← whnfR α
    if αn.isConstOf ``Nat || αn.isConstOf ``Int then
      throwError "sos: `by sos` does not handle `Nat.mod` / `Int.mod`; \
        DIV / MOD support is tracked in \
        https://github.com/kim-em/sos/issues/24."
    checkUnsupportedOps a; checkUnsupportedOps b
  | _ =>
    match e with
    | .app f a => checkUnsupportedOps f; checkUnsupportedOps a
    | .lam _ _ b _ => checkUnsupportedOps b
    | .forallE _ t b _ => checkUnsupportedOps t; checkUnsupportedOps b
    | .mdata _ b => checkUnsupportedOps b
    | _ => pure ()

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

/-- For each ℕ-cast atom in the current goal, add a hypothesis
`(0 : ℝ) ≤ ↑a := Nat.cast_nonneg _`. -/
def assertNatCastNonneg : TacticM Unit := withMainContext do
  let goal ← (← getMainGoal).getType >>= instantiateMVars
  let atoms ← collectNatCastAtoms goal
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
  let mv ← getMainGoal
  let goalOriginal ← mv.getType >>= instantiateMVars
  trace[sos.lift] "liftToReal: starting on goal {goalOriginal}"
  -- Out-of-scope ops are checked on the *original* goal Expr (before
  -- any rify rewrites obscure the source-domain operators).
  checkUnsupportedOps goalOriginal
  -- Intro all leading numeric universal binders and hypothesis binders.
  introLeadingBindersAux
  -- Re-fetch the goal after the intros.
  let mv ← getMainGoal
  let goal ← mv.getType >>= instantiateMVars
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

end SOS.Lift
