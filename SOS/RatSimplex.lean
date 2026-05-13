/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Rat.Defs

/-!
# Exact-rational Phase-1 simplex for LP feasibility over `ℚ`

The half-Newton-polytope test for SOS basis selection (#23) reduces
to: given a `target` polynomial with support exponents
`m₁, …, mₖ ∈ ℕⁿ` and a candidate exponent `2·exp(m) ∈ ℕⁿ`, does there
exist `λ ∈ ℚᵏ` with `λ ≥ 0`, `Σ λᵢ = 1`, `Σ λᵢ · mᵢ = 2·exp(m)`?

That's a small equality LP. We solve feasibility exactly over `ℚ` via
a hand-rolled Phase-1 simplex with Bland's rule (smallest-index
entering and leaving variable, anti-cycling). No FFI, no floats —
soundness requires the answer to be exact, and the LPs are small
enough that microseconds per call in pure Lean is fine.

## Tableau layout

For `m × n` system `Ax = b` with `b ≥ 0`, we introduce `m`
artificial variables `aⱼ ≥ 0` and form `Ax + Ia = b`. The Phase-1
objective is `min Σ aⱼ`. The combined tableau has

* `(rows + 1)` rows: cost row at index `0`, then constraint rows;
* `(nVars + rows + 1)` columns: `nVars` original, `rows` artificial,
  one RHS column.

`tableau[0][nCols-1]` holds `-z`, where `z = Σ aⱼ` is the current
objective. Feasible iff Phase-1 terminates at `z = 0`.
-/

namespace SOS.RatSimplex

/-- Result of one Bland's pivot step. -/
private inductive StepResult where
  /-- Made progress; tableau and basis updated. -/
  | progress (tab : Array (Array ℚ)) (basis : Array Nat)
  /-- All reduced costs ≥ 0: optimum of the relaxation reached. -/
  | optimal
  /-- Entering column has no positive pivot entry: the LP is
  unbounded along this direction. For a well-formed Phase-1 dictionary
  this is impossible (objective `Σ aⱼ ≥ 0`); we still distinguish it
  from `.optimal` so a malformed input can't be silently mistaken for
  feasibility. -/
  | unbounded

/-- One Bland's-rule pivot. Smallest-index entering and leaving
variable (tie-break by smallest basis index) for anti-cycling. -/
private def step (tab : Array (Array ℚ)) (basis : Array Nat)
    (rows nVars : Nat) : StepResult := Id.run do
  let nCols := nVars + rows + 1
  let cost := tab[0]!
  -- Bland: smallest index with negative reduced cost.
  let mut pCol? : Option Nat := none
  for j in [0:nVars + rows] do
    if cost[j]! < 0 then
      pCol? := some j
      break
  let some pCol := pCol? | return .optimal
  -- Leaving variable: min positive ratio `b_i / a_{i, pCol}`; ties
  -- broken by smallest basis index (Bland's anti-cycling rule).
  let mut pRow? : Option Nat := none
  let mut bestRatio : ℚ := 0
  for i in [0:rows] do
    let aij := tab[i+1]![pCol]!
    if aij > 0 then
      let bi := tab[i+1]![nCols - 1]!
      let ratio := bi / aij
      match pRow? with
      | none =>
        pRow? := some i
        bestRatio := ratio
      | some prev =>
        if ratio < bestRatio then
          pRow? := some i
          bestRatio := ratio
        else if ratio == bestRatio && basis[i]! < basis[prev]! then
          pRow? := some i
  let some pRow := pRow? | return .unbounded
  let pivVal := tab[pRow + 1]![pCol]!
  let mut normRow := tab[pRow + 1]!
  for j in [0:nCols] do
    normRow := normRow.set! j (normRow[j]! / pivVal)
  let mut newTab := tab.set! (pRow + 1) normRow
  for i in [0:rows + 1] do
    if i ≠ pRow + 1 then
      let coeff := newTab[i]![pCol]!
      if coeff ≠ 0 then
        let mut row := newTab[i]!
        for j in [0:nCols] do
          row := row.set! j (row[j]! - coeff * normRow[j]!)
        newTab := newTab.set! i row
  return .progress newTab (basis.set! pRow pCol)

/-- Outcome of Phase-1 simplex. Tableau is returned only on `.optimal`
so the caller can read the objective from `tab[0][nCols-1]`. -/
private inductive Phase1Outcome where
  | optimal (tab : Array (Array ℚ)) (basis : Array Nat)
  | unbounded
  /-- Pivot budget exhausted. Bland's rule terminates in at most
  `C(nVars + rows, rows)` iterations, so this only fires on
  pathological / malformed inputs. -/
  | exhausted

/-- Drive Bland's-rule pivots until optimum, unboundedness, or fuel
exhaustion. -/
private def runPhase1 : Nat → Array (Array ℚ) → Array Nat → Nat → Nat →
    Phase1Outcome
  | 0, _, _, _, _ => .exhausted
  | fuel + 1, tab, basis, rows, nVars =>
    match step tab basis rows nVars with
    | .optimal => .optimal tab basis
    | .unbounded => .unbounded
    | .progress tab' basis' => runPhase1 fuel tab' basis' rows nVars

/-- Return one feasible solution of the equality LP `A x = b, x ≥ 0`,
exactly over `ℚ`, if one is found. `A` has `b.size` rows; rows of `A`
whose length differs from the common column count return `none`. -/
def findFeasibleEqLP? (A : Array (Array ℚ)) (b : Array ℚ) :
    Option (Array ℚ) := Id.run do
  let rows := b.size
  if rows = 0 then
    if A.size = 0 then return some #[]
    else return none
  if A.size ≠ rows then return none
  let nVars := A[0]!.size
  -- Build the constraint rows with `b ≥ 0` normalisation in one pass.
  let mut Ab : Array (Array ℚ) := Array.mkEmpty rows
  let mut bs : Array ℚ := Array.mkEmpty rows
  for i in [0:rows] do
    let row₀ := A[i]!
    if row₀.size ≠ nVars then return none
    if b[i]! < 0 then
      let mut neg : Array ℚ := Array.mkEmpty nVars
      for j in [0:nVars] do neg := neg.push (-(row₀[j]!))
      Ab := Ab.push neg
      bs := bs.push (-(b[i]!))
    else
      Ab := Ab.push row₀
      bs := bs.push b[i]!
  let nCols := nVars + rows + 1
  -- Cost row. Reduced cost on column `j < nVars` is `-Σ_i A_{i,j}`
  -- after zeroing the basis (initial basis = artificials, all with
  -- cost `1`). Reduced cost on artificials is `0`. RHS column stores
  -- `-z` where `z = Σ b_i`.
  let mut cost : Array ℚ := Array.replicate nCols 0
  for j in [0:nVars] do
    let mut s : ℚ := 0
    for i in [0:rows] do
      s := s + Ab[i]![j]!
    cost := cost.set! j (-s)
  let mut z₀ : ℚ := 0
  for i in [0:rows] do
    z₀ := z₀ + bs[i]!
  cost := cost.set! (nCols - 1) (-z₀)
  let mut tab : Array (Array ℚ) := Array.mkEmpty (rows + 1)
  tab := tab.push cost
  for i in [0:rows] do
    let mut row : Array ℚ := Array.replicate nCols 0
    for j in [0:nVars] do
      row := row.set! j (Ab[i]![j]!)
    row := row.set! (nVars + i) 1
    row := row.set! (nCols - 1) (bs[i]!)
    tab := tab.push row
  let basis : Array Nat := (Array.range rows).map (· + nVars)
  -- Fuel: Bland's rule terminates in at most `C(nVars + rows, rows)`
  -- iterations (number of distinct bases). For our LPs `nVars ≤ ~50`
  -- and `rows ≤ ~6` the bound is small, but to be safe against
  -- adversarial inputs and unforeseen degeneracies, we use a cubic
  -- cap that exceeds the binomial up to `~rows ≤ 8`. Exhaustion
  -- falls through to `false` — sound for `isInHalfNewton` (a false
  -- negative just makes the Newton heuristic more conservative; the
  -- `.dense` fallback still recovers).
  let fuel := (nVars + rows + 1) ^ 3 * 4 + 4096
  match runPhase1 fuel tab basis rows nVars with
  | .optimal final finalBasis =>
    if final[0]![nCols - 1]! != 0 then return none
    let mut sol : Array ℚ := Array.replicate nVars 0
    for i in [0:rows] do
      let v := finalBasis[i]!
      if v < nVars then
        sol := sol.set! v final[i+1]![nCols - 1]!
    return some sol
  | .unbounded => none
  | .exhausted => none

/-- Test feasibility of the equality LP `A x = b, x ≥ 0` exactly over
`ℚ`. `A` has `b.size` rows; rows of `A` whose length differs from the
common column count return `false`. -/
def isFeasibleEqLP (A : Array (Array ℚ)) (b : Array ℚ) : Bool :=
  (findFeasibleEqLP? A b).isSome

end SOS.RatSimplex
