/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

`sos` and `sos_witness` tactic surface.
-/
import Sos.Reify
import Sos.Search
import Sos.Verifier
import Lean.ToExpr
import Lean.Elab.Tactic
import Lean.Meta.Tactic.TryThis
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace Sos

open Lean Elab Tactic Meta

/-! ### `Sos.Poly n` → `Lean.Expr` -/

/-- Build a `Lean.Expr` denoting the given `Sos.Poly n` value. -/
partial def Poly.toExprImpl {n : Nat} (p : Sos.Poly n) : Lean.Expr :=
  let nE : Expr := Lean.mkNatLit n
  match p with
  | .const r => mkApp2 (.const ``Sos.Poly.const []) nE (Lean.toExpr r)
  | .var i   => mkApp2 (.const ``Sos.Poly.var []) nE (Lean.toExpr i)
  | .neg p'  => mkApp2 (.const ``Sos.Poly.neg []) nE p'.toExprImpl
  | .add p' q => mkApp3 (.const ``Sos.Poly.add []) nE p'.toExprImpl q.toExprImpl
  | .sub p' q => mkApp3 (.const ``Sos.Poly.sub []) nE p'.toExprImpl q.toExprImpl
  | .mul p' q => mkApp3 (.const ``Sos.Poly.mul []) nE p'.toExprImpl q.toExprImpl
  | .pow p' k => mkApp3 (.const ``Sos.Poly.pow []) nE p'.toExprImpl (Lean.mkNatLit k)

instance Poly.instToExpr (n : Nat) : Lean.ToExpr (Sos.Poly n) where
  toExpr := Poly.toExprImpl
  toTypeExpr := Lean.mkApp (.const ``Sos.Poly []) (Lean.mkNatLit n)

/-! ### Decompiling `CMvPolynomial n ℚ` to `Sos.Poly n` -/

/-- Build the AST for a single monomial `c · Πᵢ xᵢ^(eᵢ)`. -/
def Poly.ofMonomial {n : Nat} (c : Rat) (mono : CPoly.CMvMonomial n) : Sos.Poly n :=
  Fin.foldr n (init := Sos.Poly.const c) fun i acc =>
    let e := mono[i]
    if e = 0 then acc
    else Sos.Poly.mul acc (Sos.Poly.pow (Sos.Poly.var i) e)

/-- Decompile a `CMvPolynomial n ℚ` value into a `Sos.Poly n` AST. -/
def Poly.decompile {n : Nat} (p : CPoly.CMvPolynomial n ℚ) : Sos.Poly n :=
  p.1.toList.foldr
    (fun (term : CPoly.CMvMonomial n × ℚ) (acc : Sos.Poly n) =>
      Sos.Poly.add acc (Poly.ofMonomial term.2 term.1))
    (Sos.Poly.const 0)

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
      throwError "Sos.proveByTactic: tactic left open goals"
  finally
    Tactic.setGoals goalsBefore
  instantiateMVars mv

/-- Build `Sos.Poly.evalReal x p` as an `Expr`. -/
private def evalRealExpr (n : Nat) (xE : Expr) (p : Sos.Poly n) : MetaM Expr := do
  let pE := Lean.toExpr p
  mkAppOptM ``Sos.Poly.evalReal #[some (Lean.mkNatLit n), some xE, some pE]

/-- Build `(p : Sos.Poly n).toCMv` as an `Expr`. -/
private def toCMvExpr (n : Nat) (p : Sos.Poly n) : MetaM Expr := do
  let pE := Lean.toExpr p
  mkAppOptM ``Sos.Poly.toCMv #[some (Lean.mkNatLit n), some pE]

/-- Build `CMvPolynomial.aeval x p.toCMv` as an `Expr`. -/
private def aevalExpr (n : Nat) (xE : Expr) (p : Sos.Poly n) : MetaM Expr := do
  let pCMv ← toCMvExpr n p
  mkAppOptM ``CPoly.CMvPolynomial.aeval #[some (Lean.mkNatLit n),
    some (Lean.mkConst ``Rat), some (Lean.mkConst ``Real),
    none, none, none, some xE, some pCMv]

/-- Prove `Sos.Poly.evalReal x p = origExpr` via
`simp only [Sos.Poly.evalReal]; push_cast; ring`. -/
private def buildBridgeEq (n : Nat) (xE : Expr) (p : Sos.Poly n)
    (origExpr : Expr) : TacticM Expr := do
  let lhs ← evalRealExpr n xE p
  let eqType ← mkEq lhs origExpr
  -- `simp only [evalReal]` may close the goal by `rfl` for very simple
  -- polynomials (e.g. a single variable). Wrap the cast/ring step in
  -- `all_goals` so it's a no-op when the goal is already done.
  let tac ← `(tactic|
    (simp only [Sos.Poly.evalReal, Fin.isValue]
     all_goals (push_cast; ring)))
  proveByTactic eqType tac

/-! ### Atomic-bridge helpers (new front-end)

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

/-- Meta-compute the typed `Sos.Poly n` from a `Sos.Poly.Raw` whose
`maxAtomBound ≤ n`. The boundedness is decided at meta-time. Returns
`none` if the bound check fails. -/
private def castRawToPoly (raw : Sos.Poly.Raw) (n : Nat) :
    Option (Sos.Poly n) :=
  if h : raw.maxAtomBound ≤ n then some (raw.cast n h) else none

/-- Prove `Sos.Poly.evalReal φ p = origExpr` where `φ` is the
`![atoms[0], …]` vector. The proof uses `Sos.Poly.evalReal` plus
`Matrix.cons_val_*` to reduce `φ ⟨k, _⟩` for each literal `k`. -/
private def buildAtomicBridgeEq (n : Nat) (φE : Expr) (p : Sos.Poly n)
    (origExpr : Expr) : TacticM Expr := do
  let lhs ← evalRealExpr n φE p
  let eqType ← mkEq lhs origExpr
  let tac ← `(tactic|
    (simp only [Sos.Poly.evalReal, Matrix.cons_val_zero,
       Matrix.cons_val_succ, Matrix.cons_val_zero',
       Matrix.cons_val_succ', Fin.isValue]
     all_goals (push_cast; ring)))
  proveByTactic eqType tac

/-! ### Closed-positivity proof builder -/

/-- Build the `List (CMvPolynomial n ℚ)` expression
`[g₁.toCMv, …, gₘ.toCMv]`. -/
private def gsCMvListExpr (n : Nat) (gs : List (Sos.Poly n)) : MetaM Expr := do
  let cmvTy ← Meta.mkAppOptM ``CPoly.CMvPolynomial
    #[some (Lean.mkNatLit n), some (Lean.mkConst ``Rat), none]
  let mut acc ← mkAppOptM ``List.nil #[some cmvTy]
  for g in gs.reverse do
    let gCMv ← toCMvExpr n g
    acc ← mkAppOptM ``List.cons #[some cmvTy, some gCMv, some acc]
  return acc

/-- Build a proof of `∀ g ∈ gsList, 0 ≤ CMvPolynomial.aeval x g`, given
per-hypothesis proofs `hAevalProofs i : 0 ≤ aeval x gs[i].toCMv`. -/
private def buildForallMemProof (n : Nat) (xE : Expr) (gs : List (Sos.Poly n))
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

/-- Helper: intro a fresh hypothesis on the main goal, returning its
`FVarId` and updating the tactic frame. -/
private def introMain (name : Name) : TacticM FVarId := do
  let mv ← Tactic.getMainGoal
  let (fv, mv') ← mv.intro name
  Tactic.replaceMainGoal [mv']
  return fv

/-- Build the per-hypothesis bridged proofs `0 ≤ aeval x g_i.toCMv` from
the user's introduced hypothesis FVars. Dispatches on the constraint
kind: `nonneg` uses `aeval_nonneg_of_orig`; `nonpos` uses
`aeval_nonneg_of_orig_neg`, with the bridge equality
`evalReal x g_i = -origExpr_i`. -/
private def buildHypothesisAevalProofs (parsed : Sos.Reify.ParsedGoal)
    (xE : Expr) (hFVars : Array FVarId) : TacticM (List Expr) := do
  let nE := Lean.mkNatLit parsed.n
  let mut acc : List Expr := []
  for i in [:parsed.gs_pTrees.length] do
    let gTree := parsed.gs_pTrees[i]!
    let gAbs := parsed.gs_orig_abs[i]!
    let kind := parsed.gs_kinds[i]!
    let hFVar := hFVars[i]!
    let origExpr := gAbs.instantiate1 xE
    let hExpr := Lean.mkFVar hFVar
    let gE := Lean.toExpr gTree
    match kind with
    | .nonneg =>
      -- evalReal x g = origExpr
      let eqProof ← buildBridgeEq parsed.n xE gTree origExpr
      let aProof ← mkAppOptM ``Sos.aeval_nonneg_of_orig
        #[some nE, some xE, some gE, some origExpr,
          some eqProof, some hExpr]
      acc := acc ++ [aProof]
    | .nonpos =>
      -- evalReal x g = -origExpr  (because gTree = -reify(origExpr))
      let negOrig ← mkAppM ``Neg.neg #[origExpr]
      let eqProof ← buildBridgeEq parsed.n xE gTree negOrig
      let aProof ← mkAppOptM ``Sos.aeval_nonneg_of_orig_neg
        #[some nE, some xE, some gE, some origExpr,
          some eqProof, some hExpr]
      acc := acc ++ [aProof]
  return acc

/-- Close the main goal of a closed-positivity SOS witness application. -/
def closeClosedSos (parsed : Sos.Reify.ParsedGoal)
    (certE : Expr) : TacticM Unit := do
  let some pTree := parsed.goal_pTree |
    throwError "sos_witness (closed): missing goal_pTree"
  let some goalAbs := parsed.goal_orig_abs |
    throwError "sos_witness (closed): missing goal_orig_abs"
  let xFVar ← introMain `x
  let mut hFVars : Array FVarId := #[]
  for _ in parsed.gs_pTrees do
    hFVars := hFVars.push (← introMain `h)
  Tactic.withMainContext do
    let mv ← Tactic.getMainGoal
    let xE := Lean.mkFVar xFVar
    let hAevalProofs ← buildHypothesisAevalProofs parsed xE hFVars
    let gsListE ← gsCMvListExpr parsed.n parsed.gs_pTrees
    let hgsProof ← buildForallMemProof parsed.n xE parsed.gs_pTrees hAevalProofs
    let pCMv ← toCMvExpr parsed.n pTree
    let goalE ← mkAppOptM ``Sos.Goal.closed #[some (Lean.mkNatLit parsed.n), some pCMv]
    let checksE ← mkAppM ``Sos.Certificate.checks #[certE, goalE, gsListE]
    let trueE ← mkAppOptM ``Bool.true #[]
    let decType ← mkEq checksE trueE
    let decProof ← buildDecideTrue decType
    let hTarget ← mkAppM ``Sos.sos_sound
      #[pCMv, gsListE, certE, decProof, xE, hgsProof]
    let origGoal := goalAbs.instantiate1 xE
    let eqProof_p ← buildBridgeEq parsed.n xE pTree origGoal
    let pE := Lean.toExpr pTree
    let final ← mkAppOptM ``Sos.nonneg_orig_of_aeval
      #[some (Lean.mkNatLit parsed.n), some xE, some pE, some origGoal,
        some eqProof_p, some hTarget]
    mv.assign final
    Tactic.replaceMainGoal []

/-- Close the main goal of a strict-positivity SOS witness application,
given the certificate, the slack `ε`, and a proof `0 < ε`. -/
def closeStrictSos (parsed : Sos.Reify.ParsedGoal)
    (certE : Expr) (εE : Expr) (hεE : Expr) : TacticM Unit := do
  let some pTree := parsed.goal_pTree |
    throwError "sos (strict): missing goal_pTree"
  let some goalAbs := parsed.goal_orig_abs |
    throwError "sos (strict): missing goal_orig_abs"
  let xFVar ← introMain `x
  let mut hFVars : Array FVarId := #[]
  for _ in parsed.gs_pTrees do
    hFVars := hFVars.push (← introMain `h)
  Tactic.withMainContext do
    let mv ← Tactic.getMainGoal
    let xE := Lean.mkFVar xFVar
    let hAevalProofs ← buildHypothesisAevalProofs parsed xE hFVars
    let gsListE ← gsCMvListExpr parsed.n parsed.gs_pTrees
    let hgsProof ← buildForallMemProof parsed.n xE parsed.gs_pTrees hAevalProofs
    let pCMv ← toCMvExpr parsed.n pTree
    let goalE ← mkAppOptM ``Sos.Goal.strict
      #[some (Lean.mkNatLit parsed.n), some pCMv, some εE, some hεE]
    let checksE ← mkAppM ``Sos.Certificate.checks #[certE, goalE, gsListE]
    let trueE ← mkAppOptM ``Bool.true #[]
    let decType ← mkEq checksE trueE
    let decProof ← buildDecideTrue decType
    -- sos_strict_sound : (p) (ε) (hε) (gs) (cert) (h_check) (φ) (h_gs) → 0 < aeval φ p
    let hTarget ← mkAppM ``Sos.sos_strict_sound
      #[pCMv, εE, hεE, gsListE, certE, decProof, xE, hgsProof]
    let origGoal := goalAbs.instantiate1 xE
    let eqProof_p ← buildBridgeEq parsed.n xE pTree origGoal
    let pE := Lean.toExpr pTree
    let final ← mkAppOptM ``Sos.pos_orig_of_aeval
      #[some (Lean.mkNatLit parsed.n), some xE, some pE, some origGoal,
        some eqProof_p, some hTarget]
    mv.assign final
    Tactic.replaceMainGoal []

/-- Close the main goal of an infeasibility SOS witness application. The
goal must reduce after `intro x` to `<gᵢ_constraints> → False`. -/
def closeInfeasibleSos (parsed : Sos.Reify.ParsedGoal)
    (certE : Expr) : TacticM Unit := do
  let xFVar ← introMain `x
  let mut hFVars : Array FVarId := #[]
  for _ in parsed.gs_pTrees do
    hFVars := hFVars.push (← introMain `h)
  Tactic.withMainContext do
    let mv ← Tactic.getMainGoal
    let xE := Lean.mkFVar xFVar
    let hAevalProofs ← buildHypothesisAevalProofs parsed xE hFVars
    let gsListE ← gsCMvListExpr parsed.n parsed.gs_pTrees
    let hgsProof ← buildForallMemProof parsed.n xE parsed.gs_pTrees hAevalProofs
    let goalE ← mkAppOptM ``Sos.Goal.infeasible #[some (Lean.mkNatLit parsed.n)]
    let checksE ← mkAppM ``Sos.Certificate.checks #[certE, goalE, gsListE]
    let trueE ← mkAppOptM ``Bool.true #[]
    let decType ← mkEq checksE trueE
    let decProof ← buildDecideTrue decType
    -- sos_infeasible_sound : (gs : List ...) → (cert : Certificate n) → cert.checks .infeasible gs = true →
    --                        ∀ x, ¬ ∀ g ∈ gs, 0 ≤ aeval x g
    let infeasibleProof ← mkAppM ``Sos.sos_infeasible_sound
      #[gsListE, certE, decProof, xE, hgsProof]
    -- infeasibleProof : False
    mv.assign infeasibleProof
    Tactic.replaceMainGoal []

/-! ### Atomic close*Sos (new front-end)

Versions of `close{Closed,Strict,Infeasible}Sos` that consume an
`AtomicParsedGoal`. The parser has already done all intros; these
helpers read the atom Exprs, meta-cast `rawConcl`/`rawGs` into
`Sos.Poly atoms.size`, build the vector valuation, and apply the
soundness lemma. -/

/-- Build per-hypothesis bridged proofs `0 ≤ aeval φ g_i.toCMv` from
the AtomicParsedGoal's hFVars, using `aeval_nonneg_of_orig` (or
`_neg` for `.nonpos`). -/
private def buildHypothesisAevalProofsA (n : Nat) (φE : Expr)
    (rawGs : List Sos.Poly.Raw) (origGs : List Lean.Expr)
    (gsKinds : List Sos.Reify.ConstraintKind) (hFVars : Array FVarId) :
    TacticM (List Expr × List (Sos.Poly n)) := do
  let nE := Lean.mkNatLit n
  let mut acc : List Expr := []
  let mut polys : List (Sos.Poly n) := []
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
      let aProof ← mkAppOptM ``Sos.aeval_nonneg_of_orig
        #[some nE, some φE, some gE, some origExpr,
          some eqProof, some hExpr]
      acc := acc ++ [aProof]
    | .nonpos =>
      -- gTree's evalReal yields `-origExpr` because the reifier
      -- already wrapped the orig poly in `Raw.neg`.
      let negOrig ← mkAppM ``Neg.neg #[origExpr]
      let eqProof ← buildAtomicBridgeEq n φE gTree negOrig
      let aProof ← mkAppOptM ``Sos.aeval_nonneg_of_orig_neg
        #[some nE, some φE, some gE, some origExpr,
          some eqProof, some hExpr]
      acc := acc ++ [aProof]
  return (acc, polys)

/-- Closed-positivity close. -/
def closeClosedSosA (parsed : Sos.Reify.AtomicParsedGoal)
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
  let goalE ← mkAppOptM ``Sos.Goal.closed
    #[some (Lean.mkNatLit n), some pCMv]
  let checksE ← mkAppM ``Sos.Certificate.checks #[certE, goalE, gsListE]
  let trueE ← mkAppOptM ``Bool.true #[]
  let decType ← mkEq checksE trueE
  let decProof ← buildDecideTrue decType
  let hTarget ← mkAppM ``Sos.sos_sound
    #[pCMv, gsListE, certE, decProof, φE, hgsProof]
  let eqProof_p ← buildAtomicBridgeEq n φE pTree origConcl
  let pE := Lean.toExpr pTree
  let final ← mkAppOptM ``Sos.nonneg_orig_of_aeval
    #[some (Lean.mkNatLit n), some φE, some pE, some origConcl,
      some eqProof_p, some hTarget]
  mv.assign final
  Tactic.replaceMainGoal []

/-- Strict-positivity close. -/
def closeStrictSosA (parsed : Sos.Reify.AtomicParsedGoal)
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
  let goalE ← mkAppOptM ``Sos.Goal.strict
    #[some (Lean.mkNatLit n), some pCMv, some εE, some hεE]
  let checksE ← mkAppM ``Sos.Certificate.checks #[certE, goalE, gsListE]
  let trueE ← mkAppOptM ``Bool.true #[]
  let decType ← mkEq checksE trueE
  let decProof ← buildDecideTrue decType
  let hTarget ← mkAppM ``Sos.sos_strict_sound
    #[pCMv, εE, hεE, gsListE, certE, decProof, φE, hgsProof]
  let eqProof_p ← buildAtomicBridgeEq n φE pTree origConcl
  let pE := Lean.toExpr pTree
  let final ← mkAppOptM ``Sos.pos_orig_of_aeval
    #[some (Lean.mkNatLit n), some φE, some pE, some origConcl,
      some eqProof_p, some hTarget]
  mv.assign final
  Tactic.replaceMainGoal []

/-- Infeasibility close. The conclusion is `False`; the goal becomes
`<gᵢ_constraints> → False` after intros. -/
def closeInfeasibleSosA (parsed : Sos.Reify.AtomicParsedGoal)
    (certE : Expr) : TacticM Unit := Tactic.withMainContext do
  let n := parsed.atoms.size
  let mv ← Tactic.getMainGoal
  let φE ← buildFinValExpr parsed.atoms
  let (hAevalProofs, gPolys) ← buildHypothesisAevalProofsA n φE
    parsed.rawGs parsed.origGs parsed.gsKinds parsed.hFVars
  let gsListE ← gsCMvListExpr n gPolys
  let hgsProof ← buildForallMemProof n φE gPolys hAevalProofs
  let goalE ← mkAppOptM ``Sos.Goal.infeasible #[some (Lean.mkNatLit n)]
  let checksE ← mkAppM ``Sos.Certificate.checks #[certE, goalE, gsListE]
  let trueE ← mkAppOptM ``Bool.true #[]
  let decType ← mkEq checksE trueE
  let decProof ← buildDecideTrue decType
  let infeasibleProof ← mkAppM ``Sos.sos_infeasible_sound
    #[gsListE, certE, decProof, φE, hgsProof]
  mv.assign infeasibleProof
  Tactic.replaceMainGoal []

/-! ### Tactic surface -/

syntax (name := sosTactic) "sos" : tactic
syntax (name := sosWitnessTactic) "sos_witness " term : tactic

/-- Build a `Sos.Certificate n` Expr from a runtime `Certificate n`,
quoted via `Sos.Poly.decompile` so each square round-trips through
`ToExpr (Sos.Poly n)`. -/
private def certExprOfRuntime (n : Nat) (cert : Sos.Certificate n) : MetaM Expr := do
  let sigma0Decompiled : List (Sos.Poly n) :=
    cert.sigma0.squares.map Sos.Poly.decompile
  let sigmasDecompiled : List (List (Sos.Poly n)) :=
    cert.sigmas.map (·.squares.map Sos.Poly.decompile)
  let sigma0E := Lean.toExpr sigma0Decompiled
  let sigmasE := Lean.toExpr sigmasDecompiled
  mkAppOptM ``Sos.Certificate.fromDecompiled
    #[some (Lean.mkNatLit n), some sigma0E, some sigmasE]

/-- Helper: cast rawGs to typed Poly n. -/
private def castGs (rawGs : List Sos.Poly.Raw) (n : Nat) :
    TacticM (List (Sos.Poly n)) := do
  let mut acc : List (Sos.Poly n) := []
  for raw in rawGs do
    let some gT := castRawToPoly raw n |
      throwError "sos: constraint poly's maxAtomBound > n = {n}"
    acc := acc ++ [gT]
  return acc

elab_rules : tactic
  | `(tactic| sos) => do
    let some parsed ← Sos.Reify.parseGoalAtomic |
      throwError "sos: goal not in supported fragment"
    let n := parsed.atoms.size
    let gPolys ← castGs parsed.rawGs n
    let gsCMv := gPolys.map Sos.Poly.toCMv
    match parsed.shape with
    | .closed =>
      let some rawConcl := parsed.rawConcl |
        throwError "sos (closed): missing rawConcl"
      let some pTree := castRawToPoly rawConcl n |
        throwError "sos: conclusion's maxAtomBound > n = {n}"
      let goal : Sos.Goal n := .closed pTree.toCMv
      match (← (Sos.Search.runSearch goal gsCMv : IO _)) with
      | none => throwError "sos: search failed to find a certificate"
      | some cert =>
        let certE ← certExprOfRuntime n cert
        closeClosedSosA parsed certE
    | .infeasible =>
      let goal : Sos.Goal n := .infeasible
      match (← (Sos.Search.runSearch goal gsCMv : IO _)) with
      | none => throwError "sos: search failed to find an infeasibility certificate"
      | some cert =>
        let certE ← certExprOfRuntime n cert
        closeInfeasibleSosA parsed certE
    | .strict =>
      let some rawConcl := parsed.rawConcl |
        throwError "sos (strict): missing rawConcl"
      let some pTree := castRawToPoly rawConcl n |
        throwError "sos: conclusion's maxAtomBound > n = {n}"
      match (← (Sos.Search.runStrictSearch pTree.toCMv gsCMv : IO _)) with
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
is a literal `Sos.Certificate` value matching what the search just
produced, decompiled to a clean `CMvPolynomial`-form. The user can
click the suggestion to replace `sos?` in their source. -/

/-- Render a single `Sos.Poly n` as a Lean source string using
`CMvPolynomial.X` / `CMvPolynomial.C` and the standard arithmetic
operators. Strips redundant `0 + …`, `1 * …`, and `…^1` that arise
from `Sos.Poly.decompile`'s normal form. -/
private partial def formatPoly {n : Nat} (p : Sos.Poly n)
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

private def formatSquares {n : Nat} (sqs : List (Sos.Poly n)) : String :=
  "[" ++ ", ".intercalate (sqs.map (fun p => formatPoly p)) ++ "]"

private def formatSigmasList {n : Nat}
    (ds : List (List (Sos.Poly n))) : String :=
  let entries := ds.map fun sqs => s!"\{ squares := {formatSquares sqs} }"
  "[" ++ ", ".intercalate entries ++ "]"

/-- Render a runtime `Sos.Certificate n` as a Lean source literal
suitable as the argument to `sos_witness`. -/
private def formatCertificate {n : Nat} (cert : Sos.Certificate n) : String :=
  let σ₀_decomp : List (Sos.Poly n) :=
    cert.sigma0.squares.map Sos.Poly.decompile
  let σᵢ_decomp : List (List (Sos.Poly n)) :=
    cert.sigmas.map (fun sd => sd.squares.map Sos.Poly.decompile)
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
    let mvarId ← Tactic.getMainGoal
    let some parsed ← Sos.Reify.parseGoalFull mvarId |
      throwError "sos?: goal not in supported fragment"
    -- Run the same search the `sos` tactic uses, then both close the
    -- goal AND emit a `Try this:` suggestion of `sos_witness <inline
    -- cert>`. The build is silent on success — projects that demand
    -- no warnings see no warnings; the suggestion is delivered as an
    -- info message and as a clickable widget in the IDE.
    match parsed.shape with
    | .closed =>
      let some pTree := parsed.goal_pTree |
        throwError "sos? (closed): missing goal_pTree"
      let pCMv := Sos.Poly.toCMv pTree
      let gsCMv := parsed.gs_pTrees.map Sos.Poly.toCMv
      let goal : Sos.Goal parsed.n := .closed pCMv
      match (← (Sos.Search.runSearch goal gsCMv : IO _)) with
      | none => throwError "sos?: search failed to find a certificate"
      | some cert =>
        emitSosSuggestion tk (formatCertificate cert)
        let certE ← certExprOfRuntime parsed.n cert
        closeClosedSos parsed certE
    | .infeasible =>
      let gsCMv := parsed.gs_pTrees.map Sos.Poly.toCMv
      let goal : Sos.Goal parsed.n := .infeasible
      match (← (Sos.Search.runSearch goal gsCMv : IO _)) with
      | none => throwError "sos?: search failed to find an infeasibility certificate"
      | some cert =>
        emitSosSuggestion tk (formatCertificate cert)
        let certE ← certExprOfRuntime parsed.n cert
        closeInfeasibleSos parsed certE
    | .strict =>
      let some pTree := parsed.goal_pTree |
        throwError "sos? (strict): missing goal_pTree"
      let pCMv := Sos.Poly.toCMv pTree
      let gsCMv := parsed.gs_pTrees.map Sos.Poly.toCMv
      match (← (Sos.Search.runStrictSearch pCMv gsCMv : IO _)) with
      | none => throwError "sos?: search failed to find a strict-positivity certificate"
      | some res =>
        emitSosSuggestion tk (formatCertificate res.cert)
        let certE ← certExprOfRuntime parsed.n res.cert
        let εE := Lean.toExpr res.ε
        let hεType ← mkAppM ``LT.lt #[(← mkAppOptM ``OfNat.ofNat
          #[some (Lean.mkConst ``Rat), some (Lean.mkNatLit 0), none]), εE]
        let hεE ← buildDecideTrue (← mkEq
          (← mkAppOptM ``Decidable.decide #[some hεType, none])
          (Lean.mkConst ``Bool.true))
        let hεProof ← mkAppM ``of_decide_eq_true #[hεE]
        closeStrictSos parsed certE εE hεProof

elab_rules : tactic
  | `(tactic| sos_witness $cert:term) => do
    let mvarId ← Tactic.getMainGoal
    let some parsed ← Sos.Reify.parseGoalFull mvarId |
      throwError "sos_witness: goal not in supported fragment"
    let certTy ← mkAppOptM ``Sos.Certificate #[some (Lean.mkNatLit parsed.n)]
    let certE ← Term.elabTermEnsuringType cert certTy
    Term.synthesizeSyntheticMVarsNoPostponing
    let certE ← instantiateMVars certE
    match parsed.shape with
    | .closed => closeClosedSos parsed certE
    | .infeasible => closeInfeasibleSos parsed certE
    | _ =>
      throwError "sos_witness: strict-positivity goals are not yet supported"

end Sos
