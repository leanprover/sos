/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

SDP encoding (CompPoly polynomials → `LeanCsdp.Problem`), rational
rounding of the float Gram-matrix solution, and the top-level
`runSearch` driver.

**v0.1 scope.** Closed positivity (`Goal.closed p`) and infeasibility
(`Goal.infeasible`) are implemented end-to-end. Strict positivity
(`Goal.strict p ε hε`) is deferred — the LP-slack-maximisation
encoding adds a separate code path that's not needed for v0.1's
example set.

**Encoding (Putinar form).** For a target polynomial `t` (= `p` for
closed, `-1` for infeasibility) over constraints `{gᵢ ≥ 0}` (with
`g₀ = 1`):

* One SDP block per multiplier:
  - block 0  = σ₀ Gram matrix (size `|z₀|`, where `z₀` enumerates
    monomials of total degree ≤ ⌈deg(t)/2⌉).
  - block i+1 = σᵢ Gram matrix for `gᵢ` (size `|zᵢ|`, monomials of
    total degree ≤ ⌈max(0, deg(t) − deg(gᵢ))/2⌉; minimum 1 to
    always include the constant monomial).
* Decision variables = upper-triangle entries of each Gram matrix.
* For each monomial `m` in the *union* of `support t ∪ support
  (z_b[j]·z_b[k]·g_b)`, one CSDP equality constraint:
    `coef_m(t) = Σ_b Σ_{j ≤ k} Q_b[j,k] · coef_m(z_b[j]·z_b[k]·g_b)`
  with `g_0 = 1`. CSDP's symmetric `tr(A·X) = b` form uses upper-
  triangle `A` with off-diagonal entries halved.
* Cost matrix `C = 0` (feasibility).
* Float Gram matrices come back in `Solution.X`. We round each to
  rationals over a denominator schedule, then verify the resulting
  certificate exactly via `Certificate.checks`.
-/
import SOS.Certificate
import SOS.LDL
import LeanCsdp

namespace SOS.Search

open CPoly

variable {n : Nat}

/-! ### Monomial-basis enumeration -/

/-- All monomials in `n` variables of total degree ≤ `d`, in deterministic
order. Brute-force enumeration via a counter array. -/
def monomialsUpTo (n : Nat) (d : Nat) : Array (CMvMonomial n) :=
  Id.run do
    let mut acc : Array (CMvMonomial n) := #[]
    let total : Nat := d + 1
    let mut counters : Array Nat := Array.replicate n 0
    let mut done := false
    while not done do
      let sum := counters.foldl (· + ·) 0
      if sum ≤ d then
        if h : counters.size = n then
          acc := acc.push ⟨counters, h⟩
      let mut i : Nat := 0
      let mut carry := true
      while carry && i < n do
        let cur := counters[i]!
        if cur + 1 < total then
          counters := counters.set! i (cur + 1)
          carry := false
        else
          counters := counters.set! i 0
          i := i + 1
      if carry then done := true
    return acc

/-! ### Multiplier basis sizing -/

/-- Half-ceiling: `⌈d/2⌉`. -/
@[inline] def halfCeil (d : Nat) : Nat := (d + 1) / 2

/-- Default monomial: `Vector ℕ n` of all zeros. -/
@[inline] def zeroMono (n : Nat) : CMvMonomial n :=
  ⟨Array.replicate n 0, by simp⟩

/-- The basis-degree bound for σᵢ given target degree and gᵢ degree. -/
@[inline] def multiplierBasisDeg (targetDeg : Nat) (gDeg : Nat) : Nat :=
  if targetDeg < gDeg then 0 else halfCeil (targetDeg - gDeg)

/-! ### Building per-block bases -/

/-- Per-block data: the basis (monomials), the multiplier polynomial
(`g_b`, with `g_0 = 1`), and the block size. Block 0 is the σ₀ block. -/
structure BlockSpec (n : Nat) where
  basis : Array (CMvMonomial n)
  multiplier : CMvPolynomial n ℚ

instance : Inhabited (BlockSpec n) where
  default := { basis := #[], multiplier := CMvPolynomial.C 0 }

namespace BlockSpec
def size (b : BlockSpec n) : Nat := b.basis.size
end BlockSpec

/-- Build the per-block specs from the target polynomial and constraint
list. Block 0 is σ₀ (multiplier = 1); block i+1 is σᵢ (multiplier = gᵢ). -/
def buildBlocks (target : CMvPolynomial n ℚ)
    (gs : List (CMvPolynomial n ℚ)) : Array (BlockSpec n) := Id.run do
  let targetDeg := target.totalDegree
  -- The Putinar identity `target = σ₀ + Σᵢ σᵢ·gᵢ` allows `deg(σ₀)` to
  -- reach `max(deg(target), max_i deg(σᵢ·gᵢ)) ≤ max(deg(target), max_i
  -- deg(gᵢ) + deg(σᵢ))`. For infeasibility (`target = -1`) the σ₀
  -- terms must cancel against constraint products, so we size the
  -- basis using the maximum constraint degree as well.
  let maxGDeg := gs.foldl (fun acc g => Nat.max acc g.totalDegree) 0
  let σ₀Deg := Nat.max targetDeg maxGDeg
  let mut blocks : Array (BlockSpec n) := #[]
  -- Block 0: σ₀.
  -- Heuristic: drop the constant monomial from the σ₀ basis when the
  -- target has no constant term. The corresponding `M[0][0]` would be
  -- forced to zero, leaving CSDP's interior-point step on the boundary
  -- of PSD and stalling its line search.
  let σ₀Basis := monomialsUpTo n (halfCeil σ₀Deg)
  let σ₀Basis :=
    if target.coeff (zeroMono n) = 0 then
      σ₀Basis.filter (fun m => m ≠ zeroMono n)
    else σ₀Basis
  blocks := blocks.push { basis := σ₀Basis, multiplier := CMvPolynomial.C 1 }
  -- Blocks 1..m: σᵢ for each gᵢ.
  for g in gs do
    let gDeg := g.totalDegree
    let basisDeg := multiplierBasisDeg σ₀Deg gDeg
    let basis := monomialsUpTo n basisDeg
    -- Always include at least the constant monomial.
    let basis := if basis.size == 0 then monomialsUpTo n 0 else basis
    blocks := blocks.push { basis := basis, multiplier := g }
  return blocks

/-! ### Rational ↔ Float -/

@[inline] def ratToFloat (q : ℚ) : Float :=
  Float.ofInt q.num / Float.ofInt q.den

/-! ### Polynomial product accessors -/

instance : Inhabited (CMvMonomial n) := ⟨zeroMono n⟩

/-- For block `b`, compute the polynomial `z_b[j] · z_b[k] · g_b`. -/
def blockProduct (block : BlockSpec n) (j k : Nat) : CMvPolynomial n ℚ :=
  let mj : CMvPolynomial n ℚ :=
    CMvPolynomial.monomial (block.basis.getD j (zeroMono n)) (1 : ℚ)
  let mk : CMvPolynomial n ℚ :=
    CMvPolynomial.monomial (block.basis.getD k (zeroMono n)) (1 : ℚ)
  mj * mk * block.multiplier

/-! ### Constraint monomial set

Collect all monomials appearing in `target` plus all monomials
appearing in any `block.multiplier · z_b[j] · z_b[k]` polynomial.
Each such monomial corresponds to one CSDP equality constraint.
-/

private def monoBeq (a b : CMvMonomial n) : Bool := a == b

/-- Return the union of supports as a deduplicated list. -/
def constraintMonomials (target : CMvPolynomial n ℚ)
    (blocks : Array (BlockSpec n)) : Array (CMvMonomial n) := Id.run do
  let mut acc : Array (CMvMonomial n) := target.monomials.toArray
  for block in blocks do
    let bsize := block.size
    for j in [0:bsize] do
      for k in [j:bsize] do
        let prod := blockProduct block j k
        for m in prod.monomials do
          if not (acc.contains m) then
            acc := acc.push m
  return acc

/-! ### CSDP problem construction -/

/-- Build the SDP feasibility problem for `target ≥ 0` over `gs`.

`useTraceCost = true` populates the cost matrix `C` with the
identity on every block (CSDP minimises `tr(X)`). This is Harrison's
HOL Light convention and is required to make CSDP converge on
near-rank-deficient SDPs (closed positivity / strict positivity).
For infeasibility certificates the trace objective interacts badly
with CSDP's homogeneous self-dual embedding (CSDP declares "dual
infeasible" on what is otherwise a feasible problem); pass
`useTraceCost = false` for that case to keep `C = 0` (pure
feasibility). -/
def buildSdp (target : CMvPolynomial n ℚ) (gs : List (CMvPolynomial n ℚ))
    (useTraceCost : Bool := true) :
    LeanCsdp.Problem × Array (BlockSpec n) × Array (CMvMonomial n) :=
  let blocks := buildBlocks target gs
  let monos := constraintMonomials target blocks
  let blockSizes : Array Int32 := blocks.map fun b => Int32.ofNat b.size
  let b : Array Float := monos.map fun m => ratToFloat (target.coeff m)
  -- For each (constraint = monoIdx, block = blockIdx, j, k), append a
  -- ConstraintTriple if z_b[j]·z_b[k]·g_b has nonzero coef of monos[monoIdx].
  let aTriples : Array LeanCsdp.ConstraintTriple := Id.run do
    let mut acc : Array LeanCsdp.ConstraintTriple := #[]
    for blockIdx in [0:blocks.size] do
      let block := blocks[blockIdx]!
      let bsize := block.size
      for j in [0:bsize] do
        for k in [j:bsize] do
          let prod := blockProduct block j k
          for monoIdx in [0:monos.size] do
            let m := monos[monoIdx]!
            let c := prod.coeff m
            if c ≠ 0 then
              -- CSDP mirrors the upper-triangle of each `A_i` to the
              -- lower triangle and computes `tr(A_i · X) = Σⱼₖ Aⱼₖ Xⱼₖ`
              -- on the resulting symmetric matrix. For a symmetric `X`
              -- this expands to `Σⱼ Aⱼⱼ Xⱼⱼ + 2 Σⱼ<k Aⱼₖ Xⱼₖ`. We want
              -- `target.coef(m) = Σⱼ cⱼⱼ Mⱼⱼ + 2 Σⱼ<k cⱼₖ Mⱼₖ` where
              -- `cⱼₖ = coef(m in zⱼ·zₖ)`, so `Aⱼⱼ = cⱼⱼ`, `Aⱼₖ = cⱼₖ`.
              let val : ℚ := c
              acc := acc.push
                { constraint := UInt32.ofNat (monoIdx + 1)
                  block := UInt32.ofNat (blockIdx + 1)
                  row := UInt32.ofNat (j + 1)
                  col := UInt32.ofNat (k + 1)
                  value := ratToFloat val }
    return acc
  -- Cost matrix: minimise `tr(X) = Σ_b Σ_j M_b[j,j]`. CSDP minimises
  -- `tr(C·X)`, so populating `c` with `(b, j, j, 1.0)` for every block
  -- diagonal position expresses `min tr(X)`. Pure feasibility (`c = []`)
  -- leaves CSDP's primal objective at 0 and gives no preferred direction
  -- when the feasible set is a single boundary point; Harrison's HOL
  -- Light SOS reports that an arbitrary objective improves rounding
  -- behaviour and may change CSDP's stopping criterion. This is an
  -- empirical knob, not a principled cure for boundary feasibility.
  let cTriples : Array LeanCsdp.Triple :=
    if useTraceCost then Id.run do
      let mut acc : Array LeanCsdp.Triple := #[]
      for blockIdx in [0:blocks.size] do
        let block := blocks[blockIdx]!
        for j in [0:block.size] do
          acc := acc.push
            { block := UInt32.ofNat (blockIdx + 1)
              row   := UInt32.ofNat (j + 1)
              col   := UInt32.ofNat (j + 1)
              value := 1.0 }
      return acc
    else #[]
  let problem : LeanCsdp.Problem :=
    { blockSizes := blockSizes
      b := b
      c := cTriples
      a := aTriples
      constantOffset := 0.0 }
  (problem, blocks, monos)

/-! ### Denominator schedule for rational rounding -/

/-- Schedule of denominators tried by the rational rounder, adapted from
`sos.ml`'s `find_rounding`. First small integers, then powers of two.

Harrison's HOL Light caps at `2^66`; we cap at `2^20`. Beyond that
range, CSDP rounding noise produces tiny positive `LDL` pivots whose
`fourSquaresRat` decomposition is `O(√num · denom)` and exceeds
practical wall time. If a target genuinely needs a denom ≥ 2^20 to
round cleanly, we treat the search as a fall-through and rely on
`sos_witness <hand-cert>` (matching Harrison's documented rounding
caveat). -/
def niceDenominators : List ℚ :=
  let smalls : List ℚ := (List.range 31).map (fun i => (i + 1 : ℚ))
  let powTwo : List ℚ := (List.range 16).map (fun i => (2 ^ (i + 5) : ℚ))
  smalls ++ powTwo

/-- Round a single float to the nearest rational at denominator `d`,
using round-half-away-from-zero on the numerator. -/
def niceRound (d : ℚ) (x : Float) : ℚ :=
  let dFloat : Float := ratToFloat d
  let nSigned : Int :=
    if x < 0 then -(((-x) * dFloat + 0.5).toUInt64.toNat : Int)
    else (x * dFloat + 0.5).toUInt64.toNat
  (nSigned : ℚ) / d

/-! ### Decoding `Solution.X` -/

/-- Extract the upper-triangle of a column-major n×n SDP block as a flat
`Array ℚ` after rational rounding. The CSDP `.sdp` block stores
column-major, so element `(row, col)` is at index `col * n + row`. -/
def decodeSdpBlock (denom : ℚ) (n : Nat) (entries : FloatArray) :
    Array ℚ := Id.run do
  let mut acc : Array ℚ := #[]
  for i in [0:n] do
    for j in [i:n] do
      let v := entries.get! (j * n + i)
      acc := acc.push (niceRound denom v)
  return acc

/-- Decode the full primal solution into per-block rational Gram matrices. -/
def decodeSolution (sol : LeanCsdp.Solution) (denom : ℚ) :
    Array (Array ℚ) := Id.run do
  let mut acc : Array (Array ℚ) := #[]
  for b in sol.X do
    match b with
    | .sdp n entries => acc := acc.push (decodeSdpBlock denom n entries)
    | .diag n entries =>
      -- Diagonal block: extract just the n diagonal entries (each in its
      -- own 1×1 sub-Gram in the upper-triangle convention).
      let mut diag : Array ℚ := #[]
      for i in [0:n] do
        diag := diag.push (niceRound denom (entries.get! i))
      acc := acc.push diag
  return acc

/-! ### Top-level search driver -/

/-- Convert a basis of monomials into the `Array (CMvPolynomial n ℚ)`
that `LDL.reconstruct` expects. -/
def basisAsPolys (basis : Array (CMvMonomial n)) :
    Array (CMvPolynomial n ℚ) :=
  basis.map (fun m => CMvPolynomial.monomial m (1 : ℚ))

/-- Try one denominator: round Gram matrices, reconstruct via LDL,
build a Certificate, check it. Returns `none` if any step fails. -/
def tryDenominator (target : CMvPolynomial n ℚ) (gs : List (CMvPolynomial n ℚ))
    (blocks : Array (BlockSpec n)) (sol : LeanCsdp.Solution) (denom : ℚ)
    (goal : Goal n) : Option (Certificate n) := Id.run do
  let _ := target  -- silence unused (used implicitly via goal/gs in checks)
  let Qs := decodeSolution sol denom
  if Qs.size ≠ blocks.size then return none
  -- Reconstruct σ₀ from block 0.
  let block0 := blocks.getD 0 default
  let some sigma0Squares :=
    LDL.reconstruct block0.size (Qs.getD 0 #[]) (basisAsPolys block0.basis)
    | return none
  -- Reconstruct each σᵢ from block i+1.
  let mut sigmas : List (SOSDecomp n) := []
  for blockIdx in [1:blocks.size] do
    let block := blocks.getD blockIdx default
    let Q := Qs.getD blockIdx #[]
    let some sigmaSquares :=
      LDL.reconstruct block.size Q (basisAsPolys block.basis)
      | return none
    sigmas := sigmas ++ [{ squares := sigmaSquares }]
  let cert : Certificate n :=
    { sigma0 := { squares := sigma0Squares }, sigmas := sigmas }
  if cert.checks goal gs then return some cert
  return none

/-- Try a single SDP encoding (one choice of `useTraceCost`) and the
denominator schedule. Returns `none` if CSDP fails or no rounding
validates. -/
private def tryOneSdp (target : CMvPolynomial n ℚ)
    (gs : List (CMvPolynomial n ℚ)) (goal : Goal n)
    (useTraceCost : Bool) : IO (Option (Certificate n)) := do
  let (problem, blocks, _monos) := buildSdp target gs useTraceCost
  if problem.b.size = 0 then
    if target = 0 then
      return some { sigma0 := { squares := [] },
                    sigmas := gs.map fun _ => { squares := [] } }
    else
      return none
  let sol := LeanCsdp.solve problem
  if sol.ret ∉ [0, 3] then
    return none
  for d in niceDenominators do
    if let some cert := tryDenominator target gs blocks sol d goal then
      return some cert
  return none

/-- Closed-positivity / infeasibility search: produce a Certificate
proving `target = σ₀ + Σᵢ σᵢ · gᵢ` for the chosen `target`. -/
def runFeasibilitySearch (target : CMvPolynomial n ℚ)
    (gs : List (CMvPolynomial n ℚ)) (goal : Goal n) :
    IO (Option (Certificate n)) := do
  -- Cost-matrix strategies, in order. Trace minimisation gives CSDP
  -- a well-defined central path on rank-deficient SDPs (Harrison's
  -- HOL Light convention) but interacts badly with infeasibility
  -- certificates and with some basis choices that include the
  -- constant monomial. Pure feasibility (`c = []`) is CSDP's
  -- standard mode and works on most non-boundary problems plus
  -- infeasibility. Try whichever is more likely to succeed first
  -- and fall back.
  let strategies : List Bool := match goal with
    | .infeasible => [false]
    | _           => [true, false]
  for useTraceCost in strategies do
    if let some cert ← tryOneSdp target gs goal useTraceCost then
      return some cert
  return none

/-! ### Strict positivity via ε-schedule

The proper LP-slack-maximisation encoding (one extra LP block with a
slack variable λ, optimising `-λ`) lives in the original Harrison
plan. The schedule below exchanges optimality for simplicity: we try
a list of progressively smaller positive rationals `ε`, calling
`runFeasibilitySearch` on `p - ε` for each, and stop at the first ε
that yields a valid certificate. -/

/-- Rationals tried in order when searching for a strict-positivity
witness. -/
def strictEpsSchedule : List ℚ :=
  [1, 1/2, 1/4, 1/8, 1/16, 1/32, 1/64, 1/128, 1/256, 1/512]

/-- Strict-positivity certificate output bundle. -/
structure StrictResult (n : Nat) where
  cert : Certificate n
  ε    : ℚ
  hε   : 0 < ε

/-- Search for a strict-positivity certificate by trying each ε in
`strictEpsSchedule`. -/
def runStrictSearch (p : CMvPolynomial n ℚ)
    (gs : List (CMvPolynomial n ℚ)) :
    IO (Option (StrictResult n)) := do
  for ε in strictEpsSchedule do
    if hε : 0 < ε then
      let goal : Goal n := .strict p ε hε
      let target := p - CMvPolynomial.C ε
      match (← runFeasibilitySearch target gs goal) with
      | some cert => return some { cert, ε, hε }
      | none => pure ()
  return none

/-- Top-level search driver. Dispatches on the goal shape. -/
def runSearch (goal : Goal n) (gs : List (CMvPolynomial n ℚ)) :
    IO (Option (Certificate n)) := do
  match goal with
  | .closed p     => runFeasibilitySearch p gs goal
  | .infeasible   => runFeasibilitySearch (-1) gs goal
  | .strict _ _ _ =>
    -- The strict case yields both a certificate and an ε. Callers that
    -- only want the certificate (e.g. to exercise the verifier) should
    -- use `runStrictSearch`. Here we drop the ε.
    return none

end SOS.Search
