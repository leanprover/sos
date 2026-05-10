/-
Task 0 prototype for the atom-bridge refactor. Verifies that the
chain `Raw.eval atomVal raw = origExpr` → `(raw.cast n h).evalReal
finVal = origExpr` → `sos_sound` closes a closed-positivity goal,
on three toy cases.

Hand-written to validate the proof tactics before automating in
`Sos/Tactic.lean`.
-/
import Sos
import Mathlib.Tactic.Ring

namespace Sos.AtomBridgeProto

open Sos Sos.Poly

/-! ### Case 1: one atom, `(x : ℝ) ⊢ 0 ≤ x² + 1` -/

section Case1

variable (x : ℝ)

/-- The atom valuation as an `if`-chain. -/
def atomVal1 : Nat → ℝ := fun i => if i = 0 then x else 0

/-- The reified raw polynomial `(var 0)^2 + const 1`. -/
def raw1 : Sos.Poly.Raw := .add (.pow (.var 0) 2) (.const 1)

example : (raw1).eval (atomVal1 x) = x^2 + 1 := by
  simp only [raw1, atomVal1, Sos.Poly.Raw.eval]
  -- After eval-unfolding: (if 0 = 0 then x else 0)^2 + ((1 : ℚ) : ℝ) = x^2 + 1
  all_goals (push_cast; ring)

end Case1

/-! ### Case 2: two atoms, `(x y : ℝ) ⊢ 0 ≤ (x + y)²` -/

section Case2

variable (x y : ℝ)

def atomVal2 : Nat → ℝ := fun i => if i = 0 then x else if i = 1 then y else 0

/-- `(var 0 + var 1)^2 = (var 0)² + 2·var 0·var 1 + (var 1)²`. -/
def raw2 : Sos.Poly.Raw :=
  .add (.add (.pow (.var 0) 2)
             (.mul (.mul (.const 2) (.var 0)) (.var 1)))
       (.pow (.var 1) 2)

example : (raw2).eval (atomVal2 x y) = x^2 + 2*x*y + y^2 := by
  simp only [raw2, atomVal2, Sos.Poly.Raw.eval]
  all_goals (push_cast; ring)

end Case2

/-! ### Case 3: hypothesis FVar, `(x : ℝ) (h : 0 ≤ x) ⊢ 0 ≤ x³ + x` -/

section Case3

variable (x : ℝ)

/-- Same atomVal as Case 1, since only `x` is involved. -/
def atomVal3 : Nat → ℝ := fun i => if i = 0 then x else 0

/-- The constraint `g = var 0` (representing `0 ≤ x`). -/
def gRaw3 : Sos.Poly.Raw := .var 0

/-- The conclusion `(var 0)^3 + var 0`. -/
def pRaw3 : Sos.Poly.Raw := .add (.pow (.var 0) 3) (.var 0)

example : (gRaw3).eval (atomVal3 x) = x := by
  simp only [gRaw3, atomVal3, Sos.Poly.Raw.eval]
  simp

example : (pRaw3).eval (atomVal3 x) = x^3 + x := by
  simp only [pRaw3, atomVal3, Sos.Poly.Raw.eval]
  all_goals (push_cast; ring)

end Case3

/-! ### Bridge to `Poly.evalReal` via `Raw.eval_cast`

For Case 1: we have `n = 1`, and need to show
`(raw1.cast 1 h).evalReal (fun ⟨i,_⟩ => atomVal1 x i) = x^2 + 1`. -/

section BridgeCase1

variable (x : ℝ)

example :
    let raw : Sos.Poly.Raw := raw1
    let h : raw.maxAtomBound ≤ 1 := by decide
    let finVal : Fin 1 → ℝ := fun ⟨i, _⟩ => atomVal1 x i
    (raw.cast 1 h).evalReal finVal = x^2 + 1 := by
  -- `Raw.eval_cast` says: raw.eval (naturalValuation finVal) = (raw.cast n h).evalReal finVal
  -- We pick atomVal so that `naturalValuation finVal = atomVal` definitionally
  -- (well, propositionally) when finVal is built from atomVal. Then we use the
  -- Case 1 lemma.
  -- Actually let's just compute directly:
  show (raw1.cast 1 _).evalReal _ = _
  -- Use Raw.eval_cast in reverse:
  rw [← Sos.Poly.Raw.eval_cast]
  -- Now goal: raw1.eval (naturalValuation (fun ⟨i,_⟩ => atomVal1 x i)) = x^2 + 1
  -- naturalValuation extends with 0 outside [0, n). For raw1 we only access index 0,
  -- which is < 1, so naturalValuation finVal 0 = finVal ⟨0, _⟩ = atomVal1 x 0 = x.
  simp only [raw1, Sos.Poly.Raw.eval, Sos.Poly.naturalValuation, atomVal1]
  all_goals (push_cast; ring)

end BridgeCase1

/-! ### End-to-end via `sos_sound`

Closes `(x : ℝ) ⊢ 0 ≤ x² + 1` by:
  1. Building the Putinar certificate `σ₀ = 1² + x²` (no constraints).
  2. Bridging `evalReal finVal pTyped = x² + 1`.
  3. Applying `sos_sound` and `nonneg_orig_of_aeval`. -/

section EndToEndCase1

variable (x : ℝ)

/-- The typed polynomial precomputed at definition site, to mirror the
production design where the Raw → Poly n cast happens at meta-time. -/
def pTyped1 : Sos.Poly 1 := raw1.cast 1 (by decide)

/-- Certificate: `σ₀.squares = [C 1, X 0]`, `σᵢ = []`. -/
def cert1 : Sos.Certificate 1 :=
  { sigma0 := { squares := [CPoly.CMvPolynomial.C (1 : ℚ), CPoly.CMvPolynomial.X 0] }
    sigmas := [] }

example : 0 ≤ x^2 + 1 := by
  -- Bridge equality: evalReal finVal pTyped1 = x^2 + 1
  have h_bridge :
      pTyped1.evalReal (fun ⟨i, _⟩ => atomVal1 x i) = x^2 + 1 := by
    show (raw1.cast 1 _).evalReal _ = _
    rw [← Sos.Poly.Raw.eval_cast]
    simp only [raw1, Sos.Poly.Raw.eval, Sos.Poly.naturalValuation, atomVal1]
    all_goals (push_cast; ring)
  -- Cert validity.
  have h_check : cert1.checks (.closed pTyped1.toCMv) [] = true := by
    with_unfolding_all decide
  -- Empty constraints satisfied trivially.
  have h_gs : ∀ g ∈ ([] : List (CPoly.CMvPolynomial 1 ℚ)),
      0 ≤ CPoly.CMvPolynomial.aeval (fun ⟨i, _⟩ => atomVal1 x i) g := by
    intro g hg; cases hg
  -- Apply sos_sound and bridge back.
  exact Sos.nonneg_orig_of_aeval h_bridge
    (Sos.sos_sound pTyped1.toCMv [] cert1 h_check _ h_gs)

end EndToEndCase1

/-! ### Inline-Raw bridge

Mirrors what the elaborator will do: feed `simp` the *literal* Raw
constructor expression, not a named `def`. Validates that
`Sos.Poly.Raw.eval` simp-rewriting reduces the inline form. -/

section InlineRaw

variable (x : ℝ)

example :
    (Sos.Poly.Raw.add (.pow (.var 0) 2) (.const 1)).eval
        (fun i => if i = 0 then x else 0) = x^2 + 1 := by
  simp only [Sos.Poly.Raw.eval]
  all_goals (push_cast; ring)

example :
    ((Sos.Poly.Raw.add (.pow (.var 0) 2) (.const 1)).cast 1
        (by decide)).evalReal
      (fun ⟨i, _⟩ => if i = 0 then x else 0) = x^2 + 1 := by
  rw [← Sos.Poly.Raw.eval_cast]
  simp only [Sos.Poly.Raw.eval, Sos.Poly.naturalValuation]
  all_goals (push_cast; ring)

end InlineRaw

/-! ### Case 3 end-to-end: Putinar with constraint -/

section EndToEndCase3

variable (x : ℝ)

/-- pTyped3 = x³ + x. -/
def pTyped3 : Sos.Poly 1 := pRaw3.cast 1 (by decide)

/-- gTyped3 = x (constraint). -/
def gTyped3 : Sos.Poly 1 := gRaw3.cast 1 (by decide)

/-- Cert: σ₀ = 0 (empty squares), σ₁ = X² + 1² (so σ₁·g = (x²+1)·x = x³+x). -/
def cert3 : Sos.Certificate 1 :=
  { sigma0 := { squares := [] }
    sigmas := [{ squares := [CPoly.CMvPolynomial.X 0, CPoly.CMvPolynomial.C (1 : ℚ)] }] }

example (h : 0 ≤ x) : 0 ≤ x^3 + x := by
  -- Bridge for conclusion.
  have h_bridge_p : pTyped3.evalReal (fun ⟨i, _⟩ => atomVal3 x i) = x^3 + x := by
    show (pRaw3.cast 1 _).evalReal _ = _
    rw [← Sos.Poly.Raw.eval_cast]
    simp only [pRaw3, Sos.Poly.Raw.eval, Sos.Poly.naturalValuation, atomVal3]
    all_goals (push_cast; ring)
  -- Bridge for constraint.
  have h_bridge_g : gTyped3.evalReal (fun ⟨i, _⟩ => atomVal3 x i) = x := by
    show (gRaw3.cast 1 _).evalReal _ = _
    rw [← Sos.Poly.Raw.eval_cast]
    simp only [gRaw3, Sos.Poly.Raw.eval, Sos.Poly.naturalValuation, atomVal3]
    all_goals simp
  -- Cert validity.
  have h_check :
      cert3.checks (.closed pTyped3.toCMv) [gTyped3.toCMv] = true := by
    with_unfolding_all decide
  -- gs hypothesis: 0 ≤ aeval finVal gTyped3.toCMv (from h : 0 ≤ x via bridge).
  have h_g0 : 0 ≤ CPoly.CMvPolynomial.aeval (fun ⟨i, _⟩ => atomVal3 x i)
                gTyped3.toCMv :=
    Sos.aeval_nonneg_of_orig h_bridge_g h
  have h_gs : ∀ g ∈ ([gTyped3.toCMv] : List (CPoly.CMvPolynomial 1 ℚ)),
      0 ≤ CPoly.CMvPolynomial.aeval (fun ⟨i, _⟩ => atomVal3 x i) g := by
    intro g hg
    simp at hg
    rw [hg]
    exact h_g0
  exact Sos.nonneg_orig_of_aeval h_bridge_p
    (Sos.sos_sound pTyped3.toCMv [gTyped3.toCMv] cert3 h_check _ h_gs)

end EndToEndCase3

/-! ### Case 4: old-form `∀ x : Fin 1 → ℝ, 0 ≤ (x 0)² + 1`

Validates that `x 0` (a function application of an arbitrary FVar)
is treatable as one opaque atom. The atomVal returns `x 0` for index
0. Same machinery as Case 1, just a different concrete atom Expr. -/

section Case4

variable (x : Fin 1 → ℝ)

/-- atomVal returns the function-application `x 0`. -/
def atomVal4 : Nat → ℝ := fun i => if i = 0 then x 0 else 0

example : 0 ≤ (x 0)^2 + 1 := by
  have h_bridge :
      pTyped1.evalReal (fun ⟨i, _⟩ => atomVal4 x i) = (x 0)^2 + 1 := by
    show (raw1.cast 1 _).evalReal _ = _
    rw [← Sos.Poly.Raw.eval_cast]
    simp only [raw1, Sos.Poly.Raw.eval, Sos.Poly.naturalValuation, atomVal4]
    all_goals (push_cast; ring)
  have h_check : cert1.checks (.closed pTyped1.toCMv) [] = true := by
    with_unfolding_all decide
  have h_gs : ∀ g ∈ ([] : List (CPoly.CMvPolynomial 1 ℚ)),
      0 ≤ CPoly.CMvPolynomial.aeval (fun ⟨i, _⟩ => atomVal4 x i) g := by
    intro g hg; cases hg
  exact Sos.nonneg_orig_of_aeval h_bridge
    (Sos.sos_sound pTyped1.toCMv [] cert1 h_check _ h_gs)

end Case4

/-! ### `reifyRaw` smoke checks (Task 1) -/

section ReifySmoke

open Lean Meta Elab Term Sos.Reify

/-- Round-trip: reify `x^2 + 2*x*y + y^2` (elaborated from Lean
syntax so the `2` is canonical) and check we get `maxAtomBound = 2`
and atom array is `[x, y]`. -/
elab "#sos_reify_smoke" : command => do
  Lean.Elab.Command.runTermElabM fun _ => do
    withLocalDeclD `x (Lean.mkConst ``Real) fun xE => do
      withLocalDeclD `y (Lean.mkConst ``Real) fun yE => do
        let stx ← `(($(← xE.toSyntax))^2 + 2 * $(← xE.toSyntax) * $(← yE.toSyntax)
          + ($(← yE.toSyntax))^2)
        let e ← Term.elabTermAndSynthesize stx (some (Lean.mkConst ``Real))
        let (raw, atoms) ← (reifyRaw e).go
        IO.println s!"reify maxAtomBound = {raw.maxAtomBound}, n_atoms = {atoms.size}"
        for i in [:atoms.size] do
          IO.println s!"  atom[{i}] = {← Meta.ppExpr atoms[i]!}"
        IO.println s!"raw repr: {repr raw}"
        unless raw.maxAtomBound = 2 do
          throwError "expected maxAtomBound = 2, got {raw.maxAtomBound}"
        unless atoms.size = 2 do
          throwError "expected n_atoms = 2, got {atoms.size}"

#sos_reify_smoke

end ReifySmoke

/-! ### `parseGoalAtomic` smoke checks (Task 2) -/

section ParserSmoke

open Lean Elab Tactic Sos.Reify

/-- A throwaway tactic that runs `parseGoalAtomic`, prints the
result, and then aborts (so the goal isn't consumed). -/
elab "sos_parse_dump" : tactic => do
  match ← parseGoalAtomic with
  | none => Lean.logInfo "parseGoalAtomic: none"
  | some pg =>
    Lean.logInfo m!"parseGoalAtomic OK: \
      n_atoms={pg.atoms.size}, shape={repr pg.shape}, \
      n_gs={pg.rawGs.length}, n_hFVars={pg.hFVars.size}\n\
      atoms: {pg.atoms}\n\
      rawConcl: {repr pg.rawConcl}\n\
      rawGs: {repr pg.rawGs}"
  -- Avoid "unused tactic" — leave the goal as-is.
  -- The caller dispatches the real proof.

example (x : ℝ) : 0 ≤ x^2 + 1 := by
  sos_parse_dump
  sorry

example (x y : ℝ) : 0 ≤ x^2 + 2*x*y + y^2 := by
  sos_parse_dump
  sorry

example (x : ℝ) (h : 0 ≤ x) : 0 ≤ x^3 + x := by
  sos_parse_dump
  sorry

example : ∀ x : Fin 1 → ℝ, 0 ≤ (x 0)^2 + 1 := by
  sos_parse_dump
  sorry

example : ∀ x : ℝ, 0 ≤ x^2 + 1 := by
  sos_parse_dump
  sorry

example : ∀ x : ℝ, 0 ≤ x → 0 ≤ x^3 + x := by
  sos_parse_dump
  sorry

end ParserSmoke

/-! ### End-to-end via the production `sos` tactic on natural form -/

section ProductionEndToEnd

example (x : ℝ) : 0 ≤ x^2 + 1 := by sos
example (x y : ℝ) : 0 ≤ x^2 + 2*x*y + y^2 := by sos
example (x : ℝ) : 0 < x^2 + 1 := by sos
example (x : ℝ) (h : 0 ≤ x) : 0 ≤ x^3 + x := by sos
example : ∀ x : ℝ, 0 ≤ x^2 + 1 := by sos

end ProductionEndToEnd

/-! ### Inline atomVal: validates the production-shape bridge

The production elaborator builds `atomVal` programmatically as a
`fun i => if i = 0 then atomE₀ else if i = 1 then atomE₁ else 0`
Expr (no named `def`). Verifies that `simp only [naturalValuation,
Sos.Poly.Raw.eval]` plus `push_cast; ring` closes the bridge without
needing a name to unfold. -/

section InlineAtomVal

variable (x y : ℝ)

example : 0 ≤ (x + y)^2 := by
  -- pTyped : Poly 2 = (X 0 + X 1)²-expansion, hand-built for the prototype.
  let pT : Sos.Poly 2 :=
    .add (.add (.pow (.var 0) 2)
               (.mul (.mul (.const 2) (.var 0)) (.var 1)))
         (.pow (.var 1) 2)
  let cert : Sos.Certificate 2 :=
    { sigma0 := { squares := [CPoly.CMvPolynomial.X 0 + CPoly.CMvPolynomial.X 1] }
      sigmas := [] }
  have h_bridge :
      pT.evalReal
        (fun ⟨i, _⟩ => (fun (j : Nat) => if j = 0 then x else if j = 1 then y else 0) i)
        = (x + y)^2 := by
    simp only [pT, Sos.Poly.evalReal, Sos.Poly.naturalValuation, Fin.isValue]
    all_goals (push_cast; ring)
  have h_check : cert.checks (.closed pT.toCMv) [] = true := by
    with_unfolding_all decide
  have h_gs : ∀ g ∈ ([] : List (CPoly.CMvPolynomial 2 ℚ)),
      0 ≤ CPoly.CMvPolynomial.aeval
            (fun ⟨i, _⟩ => (fun (j : Nat) => if j = 0 then x else if j = 1 then y else 0) i) g := by
    intro g hg; cases hg
  exact Sos.nonneg_orig_of_aeval h_bridge
    (Sos.sos_sound pT.toCMv [] cert h_check _ h_gs)

end InlineAtomVal

end Sos.AtomBridgeProto
