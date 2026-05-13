/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

`sos` and `sos_witness` tactic surface.
-/
import SOS.Reify
import SOS.Search
import SOS.Verifier
import SOS.Lift
import Lean.ToExpr
import Lean.Elab.Tactic
import Lean.Elab.Tactic.Config
import Lean.Meta.Tactic.TryThis
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace SOS

open Lean Elab Tactic Meta

/-- Per-call configuration for the `sos` / `sos?` tactics. Pass as
`sos (config := { maxDepth := 3 })` or omit the clause to use defaults.

* `maxDepth` — iterative-deepening cap. At each `extraDeg ∈ [0..maxDepth]`
  the σ₀ and σᵢ bases grow by one monomial degree. Harrison's `REAL_SOS`
  reports needing depth up to 12; each level is a fresh CSDP solve and
  scales combinatorially with the basis. The default is chosen
  empirically against `SOSTest` — at the time of writing, `1` is the
  largest value with no measurable wall-clock cost over `0`, and the
  depth-1 retry unlocks the discriminant identity among others. Raise
  per-call for hard targets.
* `maxRoundingDenom` — upper cap on rounding-denominator candidates
  filtered against `SOS.Search.niceDenominators` (which itself tops out
  at `2^20`). Raise for targets whose `polyDenom` exceeds the cap;
  lower to fail faster on goals you know won't round cleanly.
* `basisStrategy` — σ₀ basis pruning. `.newton` (default) uses
  Reznick's half-Newton-polytope test via an exact-rational simplex;
  `.dense` disables pruning entirely. A `.dense` fallback runs at
  the same `extraDeg` if the pruned variant doesn't certify, so the
  choice is a speed/sparsity knob, not a completeness one. -/
structure Config where
  /-- Iterative-deepening cap (see field docs above). -/
  maxDepth : Nat := 1
  /-- Upper cap on rounding-denominator candidates. Raised to `2^24`
  to give the preordering encoding (issue #38) room when product blocks
  push the rounding pressure beyond `2^20`. -/
  maxRoundingDenom : Nat := 16777216
  /-- σ₀-basis pruning strategy. See field docs above. -/
  basisStrategy : SOS.Search.BasisStrategy := .newton
  /-- Internal performance knob for the constraint-product monoid (Schmüdgen
  preordering): caps the cardinality of subsets enumerated in the σ-block
  monoid. `1` is pure Putinar (one σᵢ per constraint, no products); higher
  values let the search use products of constraint polynomials. The search
  always tries Putinar (cardinality 1) first; if that fails it falls back
  to `maxSubsetCardinality`. The default cap is high enough to cover all
  Harrison preordering targets; lower it for batch/performance-critical
  pipelines where interval-Schur-style targets with many constraints can
  produce up to `2^k − 1` product blocks. -/
  maxSubsetCardinality : Nat := 6
  deriving Inhabited

/-- Elaborator for `(config := …)` clauses on `sos`/`sos?`. -/
declare_config_elab elabConfig Config

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

/-- Build a proof of `∀ g ∈ gsList, P g` from per-element proofs `hP i :
P gs[i].toCMv`, given the predicate `P` as a one-argument lambda. -/
private def buildForallMemProofGen (n : Nat) (gs : List (SOS.Poly n))
    (hAevalProofs : List Expr) (predicate : Expr) : MetaM Expr := do
  let cmvTy ← cmvType n
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

/-- Build a proof of `∀ g ∈ gsList, 0 ≤ CMvPolynomial.aeval x g`, given
per-hypothesis proofs `hAevalProofs i : 0 ≤ aeval x gs[i].toCMv`. -/
private def buildForallMemProof (n : Nat) (xE : Expr) (gs : List (SOS.Poly n))
    (hAevalProofs : List Expr) : MetaM Expr := do
  let cmvTy ← cmvType n
  let predicate ← withLocalDeclD `g cmvTy fun gFV => do
    let body ← mkAppM ``LE.le
      #[(← mkAppOptM ``OfNat.ofNat
          #[some realTy, some (Lean.mkNatLit 0), none]),
        (← mkAppOptM ``CPoly.CMvPolynomial.aeval
          #[some (Lean.mkNatLit n), some ratTy, some realTy,
            none, none, none, some xE, some gFV])]
    mkLambdaFVars #[gFV] body
  buildForallMemProofGen n gs hAevalProofs predicate

/-- Build a proof of `∀ p ∈ psList, CMvPolynomial.aeval x p = 0`, given
per-hypothesis proofs `hP i : aeval x ps[i].toCMv = 0`. -/
private def buildForallMemEqZeroProof (n : Nat) (xE : Expr)
    (ps : List (SOS.Poly n)) (hAevalProofs : List Expr) : MetaM Expr := do
  let cmvTy ← cmvType n
  let predicate ← withLocalDeclD `q cmvTy fun gFV => do
    let lhs ← mkAppOptM ``CPoly.CMvPolynomial.aeval
      #[some (Lean.mkNatLit n), some ratTy, some realTy,
        none, none, none, some xE, some gFV]
    let zero ← mkAppOptM ``OfNat.ofNat
      #[some realTy, some (Lean.mkNatLit 0), none]
    let body ← mkEq lhs zero
    mkLambdaFVars #[gFV] body
  buildForallMemProofGen n ps hAevalProofs predicate

/-- Discharge the `cert.checks goal gs = true` side condition by
`decide +kernel`. Kernel reduction handles `Std.ExtTreeMap` lookups
and rational arithmetic at the witness denominators the search
actually emits. -/
private def buildDecideTrue (type : Expr) : TacticM Expr := do
  let tac ← `(tactic| (decide +kernel))
  proveByTactic type tac

/-! ### Per-hypothesis bridged proofs

Builds `0 ≤ aeval φ g_i.toCMv` for inequality constraints and
`aeval φ p_j.toCMv = 0` for equality constraints, dispatching on
`ConstraintKind`. -/

/-- Bundle of bridged proofs partitioned by constraint kind. -/
private structure BridgedConstraints (n : Nat) where
  ineqProofs : List Expr
  ineqPolys  : List (SOS.Poly n)
  eqProofs   : List Expr
  eqPolys    : List (SOS.Poly n)

/-- Build per-hypothesis bridged proofs from the ParsedGoal's
constraints, partitioning into inequality and equality halves. -/
private def buildHypothesisAevalProofsA (n : Nat) (φE : Expr)
    (constraints : Array SOS.Reify.ConstraintInfo) :
    TacticM (BridgedConstraints n) := do
  let nE := Lean.mkNatLit n
  let mut accIneq : Array Expr := #[]
  let mut polysIneq : Array (SOS.Poly n) := #[]
  let mut accEq : Array Expr := #[]
  let mut polysEq : Array (SOS.Poly n) := #[]
  for c in constraints do
    let some gTree := castRawToPoly c.raw n |
      throwError "sos: constraint poly's maxAtomBound exceeds n = {n}"
    let hRaw := Lean.mkFVar c.fvar
    let gE := Lean.toExpr gTree
    match c.kind with
    | .nonneg =>
      -- For general `a ≤ b` hypotheses, `c.orig = b − a` and the raw
      -- FVar has type `a ≤ b`; `sub_nonneg_of_le` lifts it to the
      -- canonical `0 ≤ b − a` shape `aeval_nonneg_of_orig` expects.
      let hExpr ← if c.useSubBridge then mkAppM ``sub_nonneg_of_le #[hRaw]
                  else pure hRaw
      let eqProof ← buildAtomicBridgeEq n φE gTree c.orig
      let aProof ← mkAppOptM ``SOS.aeval_nonneg_of_orig
        #[some nE, some φE, some gE, some c.orig,
          some eqProof, some hExpr]
      accIneq := accIneq.push aProof
      polysIneq := polysIneq.push gTree
    | .nonpos =>
      let negOrig ← mkAppM ``Neg.neg #[c.orig]
      let eqProof ← buildAtomicBridgeEq n φE gTree negOrig
      let aProof ← mkAppOptM ``SOS.aeval_nonneg_of_orig_neg
        #[some nE, some φE, some gE, some c.orig,
          some eqProof, some hRaw]
      accIneq := accIneq.push aProof
      polysIneq := polysIneq.push gTree
    | .pos =>
      -- For general `a < b` hypotheses, `c.orig = b − a` and the raw
      -- FVar has type `a < b`; `sub_pos_of_lt` lifts it to `0 < b − a`
      -- before downgrading to `0 ≤ b − a` via `le_of_lt`.
      let hExpr ← if c.useSubBridge then mkAppM ``sub_pos_of_lt #[hRaw]
                  else pure hRaw
      let hLeExpr ← mkAppM ``le_of_lt #[hExpr]
      let eqProof ← buildAtomicBridgeEq n φE gTree c.orig
      let aProof ← mkAppOptM ``SOS.aeval_nonneg_of_orig
        #[some nE, some φE, some gE, some c.orig,
          some eqProof, some hLeExpr]
      accIneq := accIneq.push aProof
      polysIneq := polysIneq.push gTree
    | .eq =>
      -- `c.orig` is the difference `a − b`; `c.fvar : a = b`.
      -- Bridge: `evalReal x p = a − b`. Combined with
      -- `sub_eq_zero_of_eq h : a − b = 0` we get `aeval x p.toCMv = 0`
      -- via `aeval_eq_zero_of_orig`.
      let eqProof ← buildAtomicBridgeEq n φE gTree c.orig
      let hSubZero ← mkAppM ``sub_eq_zero_of_eq #[hRaw]
      let aProof ← mkAppOptM ``SOS.aeval_eq_zero_of_orig
        #[some nE, some φE, some gE, some c.orig,
          some eqProof, some hSubZero]
      accEq := accEq.push aProof
      polysEq := polysEq.push gTree
  return { ineqProofs := accIneq.toList, ineqPolys := polysIneq.toList,
           eqProofs := accEq.toList, eqPolys := polysEq.toList }

/-- Closed and strict goals carry a conclusion polynomial plus the
original user expression it must bridge back to. -/
private structure ParsedConclusionData (n : Nat) where
  tree : SOS.Poly n
  cmv  : Expr
  orig : Expr
  /-- See `SOS.Reify.ParsedConcl.useSubBridge`. -/
  useSubBridge : Bool

/-- Extract and cast the conclusion polynomial for closed/strict modes. -/
private def parsedConclusionData (tag : String)
    (parsed : SOS.Reify.ParsedGoal) (n : Nat) :
    TacticM (ParsedConclusionData n) := do
  let some concl := parsed.concl |
    throwError "{tag}: missing concl"
  let some pTree := castRawToPoly concl.raw n |
    throwError "{tag}: conclusion poly's maxAtomBound exceeds n = {n}"
  let pCMv ← toCMvExpr n pTree
  return { tree := pTree, cmv := pCMv, orig := concl.orig,
           useSubBridge := concl.useSubBridge }

/-- The shape-specific data the unified close needs: which `Goal`
constructor to invoke, which soundness lemma, and (for closed/strict)
how to bridge the resulting `0 ≤ aeval …` / `0 < aeval …` proof back
to the user's original `0 ≤ origExpr` / `0 < origExpr` goal.
Infeasibility's conclusion is `False`, so it skips the bridge. -/
inductive CloseMode where
  | closed
  | strict (εE : Expr) (hεE : Expr)
  | infeasible

/-- Build a `decide +kernel`-checked proof of
`cert.checks goal gs ps = true`. -/
private def buildCheckProof (certE goalE gsListE psListE : Expr) :
    TacticM Expr := do
  let checksE ← mkAppM ``SOS.Certificate.checks
    #[certE, goalE, gsListE, psListE]
  let trueE ← mkAppOptM ``Bool.true #[]
  buildDecideTrue (← mkEq checksE trueE)

/-- Unified close: builds `decide +kernel`-checked soundness application
for the closed / strict / infeasible certificate and assigns the main
goal. Mode-specific differences are tabulated in `CloseMode`. -/
def closeSos (parsed : SOS.Reify.ParsedGoal) (certE : Expr)
    (mode : CloseMode) : TacticM Unit := Tactic.withMainContext do
  let n := parsed.atoms.size
  let nE := Lean.mkNatLit n
  let mv ← Tactic.getMainGoal
  let φE ← buildFinValExpr parsed.atoms
  let bridged ← buildHypothesisAevalProofsA n φE parsed.constraints
  let gsListE ← gsCMvListExpr n bridged.ineqPolys
  let psListE ← gsCMvListExpr n bridged.eqPolys
  let hgsProof ← buildForallMemProof n φE bridged.ineqPolys bridged.ineqProofs
  let hpsProof ← buildForallMemEqZeroProof n φE bridged.eqPolys bridged.eqProofs
  let final ← match mode with
    | .closed =>
      let p ← parsedConclusionData "sos" parsed n
      let goalE ← mkAppOptM ``SOS.Goal.closed #[some nE, some p.cmv]
      let decProof ← buildCheckProof certE goalE gsListE psListE
      let hTarget ← mkAppM ``SOS.sos_sound
        #[p.cmv, gsListE, psListE, certE, decProof, φE, hgsProof, hpsProof]
      let eqProof_p ← buildAtomicBridgeEq n φE p.tree p.orig
      let pE := Lean.toExpr p.tree
      let hNonneg ← mkAppOptM ``SOS.nonneg_orig_of_aeval
        #[some nE, some φE, some pE, some p.orig, some eqProof_p, some hTarget]
      -- For `a ≤ b` (sub-bridge) goals, `p.orig = b − a`, so the
      -- recovered fact is `0 ≤ b − a`; wrap with `le_of_sub_nonneg`
      -- to get the user-form `a ≤ b`.
      if p.useSubBridge then
        mkAppM ``le_of_sub_nonneg #[hNonneg]
      else
        pure hNonneg
    | .strict εE hεE =>
      let p ← parsedConclusionData "sos" parsed n
      let goalE ← mkAppOptM ``SOS.Goal.strict
        #[some nE, some p.cmv, some εE, some hεE]
      let decProof ← buildCheckProof certE goalE gsListE psListE
      let hTarget ← mkAppM ``SOS.sos_strict_sound
        #[p.cmv, εE, hεE, gsListE, psListE, certE, decProof, φE,
          hgsProof, hpsProof]
      let eqProof_p ← buildAtomicBridgeEq n φE p.tree p.orig
      let pE := Lean.toExpr p.tree
      let hPos ← mkAppOptM ``SOS.pos_orig_of_aeval
        #[some nE, some φE, some pE, some p.orig, some eqProof_p, some hTarget]
      if p.useSubBridge then
        mkAppM ``lt_of_sub_pos #[hPos]
      else
        pure hPos
    | .infeasible =>
      let goalE ← mkAppOptM ``SOS.Goal.infeasible #[some nE]
      let decProof ← buildCheckProof certE goalE gsListE psListE
      mkAppM ``SOS.sos_infeasible_sound
        #[gsListE, psListE, certE, decProof, φE, hgsProof, hpsProof]
  mv.assign final
  Tactic.replaceMainGoal []

/-! ### Tactic surface -/

syntax (name := sosTactic) "sos" Lean.Parser.Tactic.optConfig : tactic
syntax (name := sosTryTactic) "sos?" Lean.Parser.Tactic.optConfig : tactic
syntax (name := sosWitnessTactic)
  "sos_witness " term ("with" "ε" ":=" term)? : tactic

/-- Build a `SOS.Certificate n` Expr from a runtime `Certificate n`,
quoted via `SOS.Poly.decompile` so each square round-trips through
`ToExpr (SOS.Poly n)`. -/
private structure DecompiledCertificate (n : Nat) where
  /-- Subset-indexed σ blocks: each entry pairs the constraint-index
  subset with the SOS decomposition's squares. The empty subset is σ₀;
  singletons are Putinar σᵢ; higher cardinalities are Schmüdgen products. -/
  sigmas : List (List Nat × List (SOS.Poly n))
  eqCofs : List (SOS.Poly n) := []

private def decompileCertificate {n : Nat}
    (cert : SOS.Certificate n) : DecompiledCertificate n :=
  { sigmas := cert.sigmas.map (fun pair => (pair.1, pair.2.squares.map SOS.Poly.decompile)),
    eqCofs := cert.eqCofs.map SOS.Poly.decompile }

private def certExprOfDecompiled (n : Nat)
    (cert : DecompiledCertificate n) : MetaM Expr := do
  let sigmasE := Lean.toExpr cert.sigmas
  let eqCofsE := Lean.toExpr cert.eqCofs
  mkAppOptM ``SOS.Certificate.fromDecompiled
    #[some (Lean.mkNatLit n), some sigmasE, some eqCofsE]

/-- Cast each constraint's `Raw` to the typed `Poly n`. Returns
`(inequality polys, equality polys)`, partitioned by `ConstraintKind`. -/
private def castConstraints (constraints : Array SOS.Reify.ConstraintInfo)
    (n : Nat) : TacticM (List (SOS.Poly n) × List (SOS.Poly n)) := do
  let mut accIneq : Array (SOS.Poly n) := #[]
  let mut accEq : Array (SOS.Poly n) := #[]
  for c in constraints do
    let some gT := castRawToPoly c.raw n |
      throwError "sos: constraint poly's maxAtomBound > n = {n}"
    match c.kind with
    | .nonneg | .nonpos | .pos => accIneq := accIneq.push gT
    | .eq => accEq := accEq.push gT
  return (accIneq.toList, accEq.toList)

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
  -- These arise from `SOS.Poly.decompile`'s fold-from-zero normal form.
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

/-- Render a subset of constraint indices as a Lean source literal
`[i₀, i₁, …]`. -/
private def formatIdxs (idxs : List Nat) : String :=
  "[" ++ ", ".intercalate (idxs.map toString) ++ "]"

/-- Render the subset-indexed σ list as a Lean source literal
`[(idxs₀, { squares := … }), …]`. -/
private def formatSigmasList {n : Nat}
    (ds : List (List Nat × List (SOS.Poly n))) : String :=
  let entries := ds.map fun pair =>
    s!"({formatIdxs pair.1}, \{ squares := {formatSquares pair.2} })"
  "[" ++ ", ".intercalate entries ++ "]"

/-- Render a list of polynomial cofactors as a Lean source literal
`[q₀, q₁, …]` for the `eqCofs` field. -/
private def formatEqCofsList {n : Nat} (qs : List (SOS.Poly n)) : String :=
  "[" ++ ", ".intercalate (qs.map (fun p => formatPoly p)) ++ "]"

/-- Render a runtime `SOS.Certificate n` as a Lean source literal
suitable as the argument to `sos_witness`. Includes `eqCofs := …` when
the certificate carries equality cofactors. -/
private def formatDecompiledCertificate {n : Nat}
    (cert : DecompiledCertificate n) : String :=
  let eqSuffix :=
    if cert.eqCofs.isEmpty then ""
    else s!", eqCofs := {formatEqCofsList cert.eqCofs}"
  s!"\{ sigmas := {formatSigmasList cert.sigmas}{eqSuffix} }"

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
private def runSosTactic (parsed : SOS.Reify.ParsedGoal) (cfg : Config)
    (suggest? : Option Syntax) (tag : String) : TacticM Unit := do
  let n := parsed.atoms.size
  let (gPolys, pPolys) ← castConstraints parsed.constraints n
  let gsCMv := gPolys.map SOS.Poly.toCMv
  let psCMv := pPolys.map SOS.Poly.toCMv
  let withFoundCert (cert : SOS.Certificate n) (mode : CloseMode)
      (ε? : Option ℚ) : TacticM Unit := do
    let decompiled := decompileCertificate cert
    if let some tk := suggest? then
      emitSosSuggestion tk (formatDecompiledCertificate decompiled) ε?
    let certE ← certExprOfDecompiled n decompiled
    closeSos parsed certE mode
  let maxDenom := cfg.maxRoundingDenom
  let maxDepth := cfg.maxDepth
  let strategy := cfg.basisStrategy
  let maxCard := cfg.maxSubsetCardinality
  match parsed.shape with
  | .closed =>
    let p ← parsedConclusionData s!"{tag} (closed)" parsed n
    let goal : SOS.Goal n := .closed p.tree.toCMv
    match (← (SOS.Search.runSearch goal gsCMv psCMv
        (maxRoundingDenom := maxDenom) (maxDepth := maxDepth)
        (basisStrategy := strategy)
        (maxSubsetCardinality := maxCard) : IO _)) with
    | none => throwError "{tag}: search failed to find a certificate"
    | some cert => withFoundCert cert .closed none
  | .infeasible =>
    match (← (SOS.Search.runSearch .infeasible gsCMv psCMv
        (maxRoundingDenom := maxDenom) (maxDepth := maxDepth)
        (basisStrategy := strategy)
        (maxSubsetCardinality := maxCard) : IO _)) with
    | none => throwError "{tag}: search failed to find an infeasibility certificate"
    | some cert => withFoundCert cert .infeasible none
  | .strict =>
    let p ← parsedConclusionData s!"{tag} (strict)" parsed n
    match (← (SOS.Search.runStrict p.tree.toCMv gsCMv psCMv
        (maxRoundingDenom := maxDenom) (maxDepth := maxDepth)
        (basisStrategy := strategy)
        (maxSubsetCardinality := maxCard) : IO _)) with
    | none => throwError "{tag}: search failed to find a strict-positivity certificate"
    | some res =>
      let εE := Lean.toExpr res.ε
      let hεProof ← buildStrictHεProof εE
      withFoundCert res.cert (.strict εE hεProof) (some res.ε)

/-- Detect whether the *original* goal (before any lift / refute step)
has a ℕ/ℤ ≤/</= conclusion at its head after stripping leading binders.
This is the syntactic precondition for the negate-and-refute fallback. -/
private partial def isDiscreteIneqGoal : TacticM Bool := withMainContext do
  let mv ← getMainGoal
  let rec go (e : Expr) : MetaM Bool := do
    let e ← whnfR e
    match e with
    | .forallE _ _ body _ => go body
    | _ =>
      match_expr e with
      | LE.le α _ _ _ =>
        match ← SOS.Lift.domainOf? α with
        | some .nat | some .int => return true
        | _ => return false
      | LT.lt α _ _ _ =>
        match ← SOS.Lift.domainOf? α with
        | some .nat | some .int => return true
        | _ => return false
      | Eq α _ _ =>
        match ← SOS.Lift.domainOf? α with
        | some .nat | some .int => return true
        | _ => return false
      | _ => return false
  go (← mv.getType >>= instantiateMVars)

/-- Drive parse + search on every open goal. Used by both the direct
and refute arms of `runSosWithLift`. -/
private def parseAndSearchAll (cfg : Config) (suggest? : Option Syntax)
    (tag : String) : TacticM Unit := do
  let goals ← getGoals
  for g in goals do
    if ← g.isAssigned then continue
    setGoals [g]
    let some parsed ← SOS.Reify.parseGoalAtomic |
      throwError "{tag}: goal not in supported fragment"
    runSosTactic parsed cfg suggest? tag
  setGoals []

/-- Run the lift pre-pass, then the SOS pipeline. The pre-pass may
produce multiple subgoals (e.g. from an `Eq` conclusion split via
`le_antisymm`), or close some subgoals outright (e.g. `n < n+1` over
ℕ becomes `n+1 ≤ n+1` and the rewrite step closes it reflexively).
Each surviving subgoal is parsed and closed independently.

For ℕ/ℤ ≤/</= goals where the direct path fails (no Putinar certificate
over ℝ — e.g. `n ≤ n*n`, which is false at `n = 0.5`), we restore the
pre-lift state and retry on the negate-and-refute branch (Harrison's
`INT_SOS` trick), which routes through the existing `.infeasible` SOS
arm. See `SOS.Lift.refuteToReal`. -/
private def runSosWithLift (cfg : Config) (suggest? : Option Syntax)
    (tag : String) : TacticM Unit := do
  let canRefute ← isDiscreteIneqGoal
  if canRefute then
    -- Try the direct path first; on any failure, restore and retry on
    -- the refute branch. This mirrors the dense-fallback pattern in
    -- `runSearch`: the direct path is cheaper for goals that *are*
    -- Putinar-certifiable; the refute branch only earns its keep on
    -- discreteness-dependent goals.
    let st ← saveState
    try
      SOS.Lift.liftToReal
      parseAndSearchAll cfg suggest? tag
    catch direct =>
      -- Trace the direct-path failure under `sos.lift` for debuggability:
      -- the catch is intentionally broad (any failure shape — search
      -- miss, reify rejection, lift error — falls through to refute), so
      -- a stray bug in the direct arm would otherwise be hidden by a
      -- successful refute. If refute also fails, its exception
      -- propagates and the user sees the second-stage error.
      trace[sos.lift] "direct path failed; trying refute: {direct.toMessageData}"
      st.restore
      SOS.Lift.refuteToReal
      parseAndSearchAll cfg suggest? tag
  else
    SOS.Lift.liftToReal
    parseAndSearchAll cfg suggest? tag

/-! ### Boolean-combination splitter

Harrison's frontend reduces a conclusion of the form `p ∧ q` or
`p ∨ q` (possibly nested) to a finite set of refutation subproblems
before handing each off to the SOS pipeline. We do the same:

* `p ∧ q` — split via `And.intro` and recurse on both subgoals.
* `p ∨ q` — try the left disjunct (via `Or.inl`) and recurse on the
  resulting subgoal; on any failure, restore the pre-split state and
  try the right disjunct.

Leading universal / hypothesis binders are introduced before the
match so e.g. `∀ x : ℝ, 0 ≤ x^2 ∧ 0 ≤ x^4` is recognised. Nesting is
capped at 3 levels — search cost grows multiplicatively in the
conjunctive case and as a try/restore tree in the disjunctive case,
so the cap protects users from runaway elaboration. The cap is
enforced by a single preflight scan of the conclusion's Boolean tree,
so it is a global property of the goal rather than a per-path bound
(a `(too-deep) ∨ easy` goal is rejected even though the easy disjunct
would otherwise succeed). Flatten the goal manually if you really
need more depth.

Disjunctive *hypotheses* are out of scope. -/

/-- Maximum nested-Boolean depth handled by the splitter. -/
private def maxBoolDepth : Nat := 3

/-- Count the maximum nesting depth of `And` / `Or` in `e`, descending
under `whnfR`. Leaves (anything that isn't an `And`/`Or` after
reduction) contribute depth `0`; each `And`/`Or` node adds `1`. -/
private partial def boolDepthOf (e : Expr) : MetaM Nat := do
  let e ← whnfR e
  match_expr e with
  | And p q => return 1 + max (← boolDepthOf p) (← boolDepthOf q)
  | Or  p q => return 1 + max (← boolDepthOf p) (← boolDepthOf q)
  | _ => return 0

/-- Split an `And p q` goal into its two children via the meta API,
avoiding any tail-goal contamination that a generic `apply` /
`refine` would expose to `getGoals`. -/
private def splitAndGoal (mv : MVarId) : MetaM (MVarId × MVarId) := mv.withContext do
  let goal ← mv.getType >>= instantiateMVars
  match_expr (← whnfR goal) with
  | And p q =>
    let pMV ← mkFreshExprSyntheticOpaqueMVar p
    let qMV ← mkFreshExprSyntheticOpaqueMVar q
    mv.assign (← mkAppM ``And.intro #[pMV, qMV])
    return (pMV.mvarId!, qMV.mvarId!)
  | _ => throwError "splitAndGoal: goal is not an `And`"

/-- Apply `Or.inl` (`side = false`) or `Or.inr` (`side = true`) to an
`Or p q` goal, returning the single resulting subgoal. -/
private def splitOrGoal (mv : MVarId) (side : Bool) : MetaM MVarId := mv.withContext do
  let goal ← mv.getType >>= instantiateMVars
  match_expr (← whnfR goal) with
  | Or p q =>
    if side then
      let qMV ← mkFreshExprSyntheticOpaqueMVar q
      mv.assign (← mkAppOptM ``Or.inr #[some p, some q, some qMV])
      return qMV.mvarId!
    else
      let pMV ← mkFreshExprSyntheticOpaqueMVar p
      mv.assign (← mkAppOptM ``Or.inl #[some p, some q, some pMV])
      return pMV.mvarId!
  | _ => throwError "splitOrGoal: goal is not an `Or`"

/-- Splitter for Boolean combinations in the conclusion. Intros leading
universal / hypothesis binders, then dispatches on `And` / `Or` /
anything-else. Falls through to `runSosWithLift` at the leaves. The
depth cap is enforced upstream by `runSosBool`. -/
private partial def runSosBoolAux (cfg : Config) (suggest? : Option Syntax)
    (tag : String) : TacticM Unit := withMainContext do
  SOS.Lift.introLeadingBindersAux
  let mv ← getMainGoal
  let goal ← mv.getType >>= instantiateMVars
  match_expr (← whnfR goal) with
  | And _ _ =>
    let (lMV, rMV) ← splitAndGoal mv
    setGoals [lMV]
    runSosBoolAux cfg suggest? tag
    let lLeftovers ← getGoals
    setGoals [rMV]
    runSosBoolAux cfg suggest? tag
    let rLeftovers ← getGoals
    setGoals (lLeftovers ++ rLeftovers)
  | Or _ _ =>
    let st ← saveState
    try
      let lMV ← splitOrGoal mv (side := false)
      setGoals [lMV]
      runSosBoolAux cfg suggest? tag
    catch leftEx =>
      trace[sos.lift] "Or.inl failed; trying Or.inr: {leftEx.toMessageData}"
      st.restore
      let mv ← getMainGoal
      let rMV ← splitOrGoal mv (side := true)
      setGoals [rMV]
      runSosBoolAux cfg suggest? tag
  | _ =>
    runSosWithLift cfg suggest? tag

/-- Entry point. Intros leading binders so the depth scan sees the
conclusion under any `∀`, checks the Boolean-nesting cap once
globally, and then dispatches via `runSosBoolAux`. -/
private def runSosBool (cfg : Config) (suggest? : Option Syntax)
    (tag : String) : TacticM Unit := withMainContext do
  SOS.Lift.introLeadingBindersAux
  let mv ← getMainGoal
  let goal ← mv.getType >>= instantiateMVars
  let d ← boolDepthOf goal
  if d > maxBoolDepth then
    throwError "{tag}: boolean nesting in conclusion exceeds depth \
      {maxBoolDepth} (found {d}); flatten the goal or split manually"
  runSosBoolAux cfg suggest? tag

elab_rules : tactic
  | `(tactic| sos $cfg:optConfig) => do
    let cfg ← elabConfig cfg
    runSosBool cfg none "sos"

elab_rules : tactic
  | `(tactic| sos?%$tk $cfg:optConfig) => do
    let cfg ← elabConfig cfg
    runSosBool cfg (some tk) "sos?"

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
