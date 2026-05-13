/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

SDP encoding (CompPoly polynomials → `LeanCsdp.Problem`), rational
rounding of the float Gram-matrix solution, and the top-level
`runSearch` driver.

Closed positivity and infeasibility go through the feasibility SDP
(`runFeasibilitySearch`); strict positivity goes through `runStrict`,
which adds a slack variable to the SDP via the `.lpSlack` mode of
`buildSdp`, reads back `λ*` from CSDP, and re-solves `p − ε ≥ 0` for
`ε = 2^-k` near `λ*`.

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
  with `g_0 = 1`. We emit upper-triangle `A` entries `Aⱼₖ = coef_m(zⱼ·zₖ·g_b)`
  directly (no halving): CSDP's `op_a` doubles off-diagonal sparse
  entries against symmetric `X`, so `tr(A·X)` expands to
  `Σⱼ Aⱼⱼ Xⱼⱼ + 2 Σⱼ<k Aⱼₖ Xⱼₖ` which matches the constraint above.
* Cost matrix `C = 0` (feasibility).
* Float Gram matrices come back in `Solution.X`. We round each to
  rationals over a denominator schedule, then verify the resulting
  certificate exactly via `Certificate.checks`.
-/
import SOS.Certificate
import SOS.LDL
import SOS.RatLinAlg
import SOS.RatSimplex
import SOS.Symmetry
import LeanCsdp

namespace SOS.Search

open CPoly

variable {n : Nat}

/-! ### Polynomial denominator -/

/-- The least common multiple of the denominators of all (non-zero)
coefficients of `p`. The true Gram matrix realising `σ = zᵀ Q z = p`
has rational entries whose denominators divide this; using it as a
rounding grid lets the rounder land on the exact rational matrix
when CSDP returns a near-true float solution. -/
def polyDenom {n : Nat} (p : CMvPolynomial n ℚ) : Nat :=
  p.monomials.foldl (fun acc m => Nat.lcm acc (p.coeff m).den) 1

/-! ### Monomial-basis enumeration -/

/-- Default monomial: `Vector ℕ n` of all zeros. -/
@[inline] def zeroMono (n : Nat) : CMvMonomial n :=
  ⟨Array.replicate n 0, by simp⟩

instance : Inhabited (CMvMonomial n) := ⟨zeroMono n⟩

/-- Auxiliary: enumerate length-`k` weak compositions (entries ≥ 0,
sum ≤ `budget`) appended to `acc.reverse`, pushed into `results`.

Iterates the *current* dimension as the outermost loop, which means
the position pushed earliest into `acc` becomes the outermost (slowest-
varying) coordinate after the final reverse — i.e. the result list is
ordered with the first coordinate varying fastest, matching the
deterministic order callers depended on. -/
private partial def monomialsUpToAux (n : Nat) :
    (k : Nat) → Nat → (acc : Array Nat) → acc.size + k = n →
      Array (CMvMonomial n) → Array (CMvMonomial n)
  | 0, _, acc, h, results =>
    results.push ⟨acc.reverse, by
      simp at h ⊢
      omega⟩
  | k+1, budget, acc, h, results => Id.run do
    let mut results := results
    for e in [0:budget+1] do
      results := monomialsUpToAux n k (budget - e) (acc.push e) (by
        simp at h ⊢
        omega) results
    return results

/-- All monomials in `n` variables of total degree ≤ `d`, in
deterministic order (lex with first coordinate varying fastest).
For example, `monomialsUpTo 2 2` produces
`#[(0,0), (1,0), (2,0), (0,1), (1,1), (0,2)]`.

Cardinality is `C(n+d, d)` — recursion enumerates only valid
compositions, avoiding the `(d+1)^n` blow-up of generate-then-filter
at moderate variable counts. -/
def monomialsUpTo (n d : Nat) : Array (CMvMonomial n) :=
  monomialsUpToAux n n d #[] (by simp) #[]

/-! ### Half-Newton-polytope membership

Reznick's theorem: if `target = Σⱼ qⱼ²`, every monomial appearing in
any `qⱼ` has exponent `α` with `2·α ∈ Newton(target)`. So the
`σ₀` basis is contained in `{m : 2·exp(m) ∈ Newton(target)}`. The
membership test is an LP:

  `∃ λ ≥ 0 : Σᵢ λᵢ = 1, Σᵢ λᵢ · exp(mᵢ) = 2·exp(m)`

where `m₁, …, mₖ` are the support exponents of `target`. We solve
this exactly in `ℚ` via `RatSimplex` — float-based solvers cannot
soundly decide `λᵢ ≥ 0`. -/

/-- Per-coordinate max exponent across the support. Any point in
`Newton(target)` is componentwise `≤` this vector, so `2·exp(m)`
exceeding it in any coordinate is a sound cheap rejection. -/
private def coordwiseMaxSupportExp (n : Nat)
    (targetMonos : Array (CMvMonomial n)) : Array Nat := Id.run do
  let mut maxExp : Array Nat := Array.replicate n 0
  for m in targetMonos do
    for i in [0:n] do
      if m[i]! > maxExp[i]! then maxExp := maxExp.set! i m[i]!
  return maxExp

/-- Half-Newton-polytope membership: does `2·exp(m)` lie in the
convex hull of `{exp(m') : m' ∈ support(target)}`?

Two layers, cheapest first:
1. **Coordwise max rejection.** If `2·m[i]` exceeds the per-coordinate
   max support exponent for any `i`, reject. Sound for any point in
   the convex hull.
2. **Exact LP feasibility.** Otherwise, solve the membership LP via
   Phase-1 simplex over `ℚ`.

Empty support means `target = 0`; we conservatively return `false`
(no σ₀ basis monomial admissible). -/
def isInHalfNewton (target : CMvPolynomial n ℚ) (m : CMvMonomial n) :
    Bool := Id.run do
  let targetMonos : Array (CMvMonomial n) := target.monomials.toArray
  if targetMonos.isEmpty then return false
  let maxExp := coordwiseMaxSupportExp n targetMonos
  for i in [0:n] do
    if 2 * m[i]! > maxExp[i]! then return false
  -- Build the equality LP `A λ = b`, λ ≥ 0:
  --   row 0 (normalisation):  Σ λᵢ = 1
  --   row j+1 (var j):         Σ λᵢ · mᵢ[j] = 2·m[j]
  let k := targetMonos.size
  let mut A : Array (Array ℚ) := Array.mkEmpty (n + 1)
  let mut b : Array ℚ := Array.mkEmpty (n + 1)
  let mut normRow : Array ℚ := Array.mkEmpty k
  for _ in [0:k] do normRow := normRow.push 1
  A := A.push normRow
  b := b.push 1
  for j in [0:n] do
    let mut row : Array ℚ := Array.mkEmpty k
    for i in [0:k] do
      let e : Nat := (targetMonos[i]!)[j]!
      row := row.push (e : ℚ)
    A := A.push row
    let bj : Nat := 2 * m[j]!
    b := b.push (bj : ℚ)
  return RatSimplex.isFeasibleEqLP A b

/-- Half-Newton-polytope basis for σ₀: those monomials `m` with
`totalDegree m ≤ deg` such that `2·exp(m) ∈ Newton(target)`.

This is Reznick's tightest necessary condition for unconstrained σ₀:
any monomial that can appear in any `qⱼ` of `target = Σⱼ qⱼ²` lies in
this set. -/
def newtonBasis (target : CMvPolynomial n ℚ) (deg : Nat) :
    Array (CMvMonomial n) :=
  if target.monomials.isEmpty then #[]
  else (monomialsUpTo n deg).filter (fun m => isInHalfNewton target m)

/-- Harrison's `newton_polytope` basis order for pure SOS search. It
enumerates the rectangular per-variable half-degree box, filters by
half-Newton membership, and reverses the result so high-degree terms
come first and the constant monomial is last. The order matters for the
Harrison-style sparse eliminator used by the symmetry-reduced path. -/
private def harrisonNewtonBasis (target : CMvPolynomial n ℚ) :
    Array (CMvMonomial n) := Id.run do
  if target.monomials.isEmpty then return #[]
  let mut bounds : Array Nat := Array.replicate n 0
  for m in target.monomials do
    for i in [0:n] do
      let b := ((m[i]! + 1) / 2)
      if bounds[i]! < b then
        bounds := bounds.set! i b
  let rec go (fuel i : Nat) (acc : Array Nat) :
      Array (CMvMonomial n) :=
    if fuel = 0 then
      #[Vector.ofFn fun (j : Fin n) => acc[j.val]?.getD 0]
    else if i = n then
      #[Vector.ofFn fun (j : Fin n) => acc[j.val]?.getD 0]
    else Id.run do
      let mut out : Array (CMvMonomial n) := #[]
      for e in [0:(bounds[i]?.getD 0) + 1] do
        out := out ++ go (fuel - 1) (i + 1) (acc.push e)
      return out
  (go (n + 1) 0 #[]).filter (fun m => isInHalfNewton target m) |>.reverse

/-- Basis-selection strategy for the σ₀ block.

* `.dense` — `monomialsUpTo n σ₀BasisDeg`. Complete; the safety net.
* `.newton` — `newtonBasis`. Reznick's half-Newton-polytope. Sound
  pruning for unconstrained σ₀; in the Putinar setting it can
  over-prune (σ₀ may need to absorb cancellations against `σᵢ·gᵢ`
  whose Newton extends past `½·Newton(target)`), which the `.dense`
  fallback covers. -/
inductive BasisStrategy where
  | dense
  | newton
  deriving Inhabited, DecidableEq, Repr

namespace BasisStrategy

/-- Compute the σ₀ basis at the given degree under this strategy. -/
def basisAt (s : BasisStrategy) (target : CMvPolynomial n ℚ)
    (deg : Nat) : Array (CMvMonomial n) :=
  match s with
  | .dense => monomialsUpTo n deg
  | .newton => newtonBasis target deg

end BasisStrategy

/-! ### Multiplier basis sizing -/

/-- Half-ceiling: `⌈d/2⌉`. -/
@[inline] def halfCeil (d : Nat) : Nat := (d + 1) / 2

/-- The basis-degree bound for σᵢ given target degree and gᵢ degree. -/
@[inline] def multiplierBasisDeg (targetDeg : Nat) (gDeg : Nat) : Nat :=
  if targetDeg < gDeg then 0 else halfCeil (targetDeg - gDeg)

/-- The cofactor basis-degree bound for an equality polynomial `pⱼ`.
The cofactor `qⱼ` needs degree headroom up to `σ₀Deg − pⱼ.totalDegree`. -/
@[inline] def cofactorBasisDeg (targetDeg : Nat) (pDeg : Nat) : Nat :=
  if targetDeg < pDeg then 0 else targetDeg - pDeg

/-! ### Building per-block bases -/

/-- Per-block data: the subset of constraint indices `idxs ⊆ [0, |gs|)`
this block represents, the monomial basis, and the multiplier polynomial
`∏_{i ∈ idxs} gs[i]`. The empty subset corresponds to the σ₀ block with
multiplier `1`; singletons `[i]` correspond to the Putinar σᵢ blocks;
higher cardinalities are Schmüdgen-style preordering blocks. -/
structure BlockSpec (n : Nat) where
  idxs : List Nat := []
  basis : Array (CMvMonomial n)
  multiplier : CMvPolynomial n ℚ

instance : Inhabited (BlockSpec n) where
  default := { idxs := [], basis := #[], multiplier := CMvPolynomial.C 0 }

namespace BlockSpec
@[inline] def size (b : BlockSpec n) : Nat := b.basis.size
end BlockSpec

/-- Per-equality cofactor data: basis of monomials and the equality
polynomial `pⱼ`. The cofactor coefficients are unrestricted in sign
and encoded via two LP diagonal blocks (`x⁺`, `x⁻`) downstream. -/
structure EqCofactorSpec (n : Nat) where
  basis  : Array (CMvMonomial n)
  eqPoly : CMvPolynomial n ℚ

instance : Inhabited (EqCofactorSpec n) where
  default := { basis := #[], eqPoly := CMvPolynomial.C 0 }

namespace EqCofactorSpec
@[inline] def size (e : EqCofactorSpec n) : Nat := e.basis.size
end EqCofactorSpec

/-- Enumerate non-empty subsets of `[0, gs.length)` whose product has
total degree `≤ maxDeg` and cardinality `≤ maxCard`. Each entry pairs
the subset of indices (sorted ascending) with the product polynomial.
Mirrors Harrison's `enumerate_products` (sos.ml:889) modulo the trivial
empty subset (which the caller injects as the σ₀ block). Indices are
generated in lex order, products are accumulated incrementally to avoid
recomputation. Constant-polynomial constraints are filtered (their
inclusion in a product is redundant). -/
def enumerateConstraintProducts (maxDeg maxCard : Nat)
    (gs : Array (CMvPolynomial n ℚ)) :
    Array (List Nat × CMvPolynomial n ℚ) := Id.run do
  let mut results : Array (List Nat × CMvPolynomial n ℚ) := #[]
  if maxCard = 0 then return results
  let count := gs.size
  -- Level 1: singletons (filter constants and degree-overflow).
  let mut prev : Array (List Nat × CMvPolynomial n ℚ) := #[]
  for i in [0:count] do
    let g := gs.getD i 0
    if g.totalDegree = 0 then continue
    if g.totalDegree > maxDeg then continue
    prev := prev.push ([i], g)
  results := results ++ prev
  -- Level k+1: extend each (idxs, prod) by an index strictly larger than
  -- the maximum index already in `idxs` (kept sorted ascending; the last
  -- element is the maximum).
  for _ in [1:maxCard] do
    if prev.isEmpty then break
    let mut next : Array (List Nat × CMvPolynomial n ℚ) := #[]
    for (idxs, prod) in prev do
      let startIdx := match idxs.getLast? with
        | some k => k + 1
        | none   => 0
      for j in [startIdx:count] do
        let g := gs.getD j 0
        if g.totalDegree = 0 then continue
        let prod' := prod * g
        if prod'.totalDegree > maxDeg then continue
        next := next.push (idxs ++ [j], prod')
    results := results ++ next
    prev := next
  return results

/-- Build the per-block specs from the target polynomial and constraint
list. Block 0 is σ₀ (idxs = `[]`, multiplier = 1); subsequent blocks are
indexed by subsets `S ⊆ [0, gs.length)` with `|S| ≥ 1` enumerated by
`enumerateConstraintProducts`. `maxSubsetCardinality = 1` recovers
the Putinar quadratic-module encoding (one σᵢ per constraint); higher
values enumerate Schmüdgen-style preordering products (e.g. `g₁·g₂`).

The `ps` argument provides equality polynomials whose total degree
participates in σ₀ sizing — `target = Σ_S σ_S·∏_{i ∈ S} gᵢ + Σⱼ qⱼ·pⱼ`
may need σ₀ to absorb cancellations against `qⱼ·pⱼ` of degree close to
`σ₀Deg`.

`extraDeg` raises the relaxation level: it is added to both the σ₀
basis degree and to every σ_S multiplier basis degree, growing each
Gram matrix accordingly. `extraDeg = 0` is the original fixed-level
encoding; iterative-deepening drivers loop `extraDeg = 0, 1, …`.

`strategy` selects the σ₀ basis: `.dense` (complete, default) or
`.newton` (half-Newton-polytope from Reznick — sound pruning via
exact-rational LP). The pruning is only applied to σ₀ — product
multipliers σ_S have no analogous heuristic. The deepening driver is
responsible for falling back to `.dense` if a pruned attempt fails. -/
def buildBlocks (target : CMvPolynomial n ℚ)
    (gs : List (CMvPolynomial n ℚ))
    (ps : List (CMvPolynomial n ℚ) := []) (extraDeg : Nat := 0)
    (strategy : BasisStrategy := .dense)
    (maxSubsetCardinality : Nat := 1) :
    Array (BlockSpec n) := Id.run do
  let targetDeg := target.totalDegree
  let maxGDeg := gs.foldl (fun acc g => Nat.max acc g.totalDegree) 0
  let maxPDeg := ps.foldl (fun acc p => Nat.max acc p.totalDegree) 0
  let σ₀Deg := Nat.max (Nat.max targetDeg maxGDeg) maxPDeg
  let mut blocks : Array (BlockSpec n) := #[]
  let σ₀BasisDeg := halfCeil σ₀Deg + extraDeg
  let σ₀Basis := strategy.basisAt target σ₀BasisDeg
  let σ₀Basis :=
    if target.coeff (zeroMono n) = 0 then
      σ₀Basis.filter (fun m => m ≠ zeroMono n)
    else σ₀Basis
  blocks := blocks.push
    { idxs := [], basis := σ₀Basis, multiplier := CMvPolynomial.C 1 }
  -- Product degree cap grows with `extraDeg`: a relaxation that adds
  -- `extraDeg` to every σ-block basis-degree gives `2 * extraDeg` extra
  -- room on the polynomial degree, so products with degree up to
  -- `σ₀Deg + 2 * extraDeg` can still combine with a non-trivial σ_S
  -- multiplier (basis degree ≥ 0). Without this, deeper relaxations
  -- never admit higher-degree product subsets.
  let products := enumerateConstraintProducts (σ₀Deg + 2 * extraDeg)
                    maxSubsetCardinality gs.toArray
  for (idxs, prod) in products do
    let basisDeg := multiplierBasisDeg σ₀Deg prod.totalDegree + extraDeg
    let basis := monomialsUpTo n basisDeg
    let basis := if basis.size == 0 then monomialsUpTo n 0 else basis
    blocks := blocks.push { idxs, basis, multiplier := prod }
  return blocks

/-- Build per-equality cofactor specs. The cofactor basis for `pⱼ` has
degree `cofactorBasisDeg σ₀Deg deg(pⱼ)`, computed against the same
`σ₀Deg` that drives `buildBlocks`. `extraDeg` mirrors `buildBlocks`'
iterative-deepening parameter: a relaxation that grows σ₀ by `extraDeg`
in basis (i.e. by `2 * extraDeg` in polynomial degree) needs the
matching headroom on each cofactor `qⱼ`. -/
def buildEqCofactorSpecs (target : CMvPolynomial n ℚ)
    (gs : List (CMvPolynomial n ℚ)) (ps : List (CMvPolynomial n ℚ))
    (extraDeg : Nat := 0) : Array (EqCofactorSpec n) := Id.run do
  let targetDeg := target.totalDegree
  let maxGDeg := gs.foldl (fun acc g => Nat.max acc g.totalDegree) 0
  let maxPDeg := ps.foldl (fun acc p => Nat.max acc p.totalDegree) 0
  let σ₀Deg := Nat.max (Nat.max targetDeg maxGDeg) maxPDeg
  let mut specs : Array (EqCofactorSpec n) := #[]
  for p in ps do
    let pDeg := p.totalDegree
    let cofDeg := cofactorBasisDeg σ₀Deg pDeg + 2 * extraDeg
    let basis := monomialsUpTo n cofDeg
    let basis := if basis.size == 0 then monomialsUpTo n 0 else basis
    specs := specs.push { basis, eqPoly := p }
  return specs

/-! ### Rational ↔ Float -/

@[inline] def ratToFloat (q : ℚ) : Float :=
  Float.ofInt q.num / Float.ofInt q.den

/-! ### Polynomial product accessors -/

/-- For block `b`, compute the polynomial `z_b[j] · z_b[k] · g_b`. -/
private def blockProduct (block : BlockSpec n) (j k : Nat) : CMvPolynomial n ℚ :=
  let mj : CMvPolynomial n ℚ :=
    CMvPolynomial.monomial block.basis[j]! (1 : ℚ)
  let mk : CMvPolynomial n ℚ :=
    CMvPolynomial.monomial block.basis[k]! (1 : ℚ)
  mj * mk * block.multiplier

/-! ### Cached block products

Each `(block, j, k)` triple's `blockProduct` is consumed twice during
SDP construction: once to collect the union of monomials, and once to
emit the CSDP `A`-matrix triples. Computing the products and walking
their supports once is cheaper, especially as block sizes grow. -/

/-- One cached `(block, j, k)` product as its sparse support.
`support` lists the (monomial, coefficient) pairs with non-zero
coefficient. -/
structure CachedProduct (n : Nat) where
  blockIdx : Nat
  j        : Nat
  k        : Nat
  support  : Array (CMvMonomial n × ℚ)

/-- One cached `(equality j, basis index b)` product `monomial_b · pⱼ`
as its sparse support. -/
structure CachedEqProduct (n : Nat) where
  eqIdx    : Nat
  basisIdx : Nat
  support  : Array (CMvMonomial n × ℚ)

/-- Compute `monomial_b · pⱼ` as a polynomial. -/
private def eqProduct (spec : EqCofactorSpec n) (b : Nat) :
    CMvPolynomial n ℚ :=
  let mb : CMvPolynomial n ℚ := CMvPolynomial.monomial spec.basis[b]! (1 : ℚ)
  mb * spec.eqPoly

/-! ### CSDP problem construction -/

/-- Which SDP we're building.

* `.feasibility (useTraceCost := true)` (default for closed positivity):
  cost matrix `C` is the identity on every σ-block, so CSDP maximises
  `tr(X)`. Harrison's HOL Light convention; required to make CSDP
  converge on near-rank-deficient SDPs.
* `.feasibility (useTraceCost := false)` (infeasibility certificates):
  `C = 0`. The trace objective interacts badly with CSDP's homogeneous
  self-dual embedding on infeasibility (CSDP declares "dual infeasible"
  on what is otherwise a feasible problem).
* `.lpSlack` (strict positivity): adds a `1×1` PSD λ-block (so `λ ≥ 0`),
  attaches `+1·λ` to the constant-monomial equality, and asks CSDP to
  maximise λ via cost `+1` on the λ-block diagonal. The direction is
  empirically irrelevant for the trace regularisation in `.feasibility`,
  but the LP-slack direction must be `max` so `runStrict` can read back
  `λ*` as the largest admissible slack. -/
inductive SdpMode where
  /-- Feasibility encoding `target = σ₀ + Σᵢ σᵢ · gᵢ`. -/
  | feasibility (useTraceCost : Bool := true)
  /-- LP-slack encoding for strict positivity: certifies `target − λ ≥ 0`
  with `λ ≥ 0` as a decision variable and asks CSDP to maximise `λ`. -/
  | lpSlack
  deriving Inhabited

/-- Build the SDP encoding `target = σ₀ + Σᵢ σᵢ · gᵢ + Σⱼ qⱼ · pⱼ`
for the chosen `mode`. The equality list `ps` may be empty (the
ordinary Putinar case). Returns the CSDP problem, the σ-block specs,
the equality cofactor specs (empty when `ps = []`), the monomial
array, and (for `.lpSlack`) the 0-based index of the λ block in
`Solution.X`.

Equality cofactors. Each `qⱼ` is `Σ_b cⱼ_b · monomial_b` with `cⱼ_b`
free in sign. Encode `cⱼ_b = x⁺ᵢ − x⁻ᵢ` and require `x⁺ ≥ 0`, `x⁻ ≥ 0`:
two diagonal LP blocks of width `Σⱼ |basisⱼ|`. Trace cost gives these
blocks zero weight — otherwise the objective drives `x⁺` and `x⁻` to
infinity together. -/
def buildSdp (target : CMvPolynomial n ℚ) (gs : List (CMvPolynomial n ℚ))
    (mode : SdpMode := .feasibility) (ps : List (CMvPolynomial n ℚ) := [])
    (extraDeg : Nat := 0) (strategy : BasisStrategy := .dense)
    (maxSubsetCardinality : Nat := 1) :
    LeanCsdp.Problem × Array (BlockSpec n) × Array (EqCofactorSpec n) ×
      Array (CMvMonomial n) × Option Nat :=
  let σBlocks := buildBlocks target gs ps extraDeg strategy maxSubsetCardinality
  let eqSpecs := buildEqCofactorSpecs target gs ps extraDeg
  let hasEqs := !ps.isEmpty
  let cumOffsets : Array Nat := Id.run do
    let mut offsets : Array Nat := #[]
    let mut acc : Nat := 0
    for spec in eqSpecs do
      offsets := offsets.push acc
      acc := acc + spec.size
    return offsets
  let totalCofactorWidth : Nat :=
    eqSpecs.foldl (fun acc s => acc + s.size) 0
  -- Block layout: [σ-blocks…, (x⁺, x⁻ if eqs), (λ if .lpSlack)].
  let xPosBlockIdx : Nat := σBlocks.size
  let xNegBlockIdx : Nat := σBlocks.size + 1
  let lambdaBlockIdx? : Option Nat :=
    match mode with
    | .lpSlack => some (σBlocks.size + (if hasEqs then 2 else 0))
    | _        => none
  let σBlockSizes := σBlocks.map fun b => Int32.ofNat b.size
  let withEqsSizes : Array Int32 :=
    if hasEqs then
      σBlockSizes
        |>.push (-(Int32.ofNat totalCofactorWidth))
        |>.push (-(Int32.ofNat totalCofactorWidth))
    else σBlockSizes
  let blockSizes : Array Int32 :=
    match mode with
    | .lpSlack => withEqsSizes.push 1
    | _        => withEqsSizes
  let constMono := zeroMono n
  -- One pass: cache σ-block and eq-cofactor products, accumulate the
  -- monomial union, build a (monomial → index) lookup.
  let (cached, cachedEq, monos, monoIndex) :
      Array (CachedProduct n) × Array (CachedEqProduct n) ×
        Array (CMvMonomial n) ×
        Std.TreeMap (CMvMonomial n) Nat compare :=
    Id.run do
      let mut monos : Array (CMvMonomial n) := #[]
      let mut monoIndex : Std.TreeMap (CMvMonomial n) Nat compare := {}
      match mode with
      | .lpSlack =>
        monoIndex := monoIndex.insert constMono 0
        monos := monos.push constMono
      | _ => pure ()
      for m in target.monomials do
        if !monoIndex.contains m then
          monoIndex := monoIndex.insert m monos.size
          monos := monos.push m
      let mut cached : Array (CachedProduct n) := #[]
      for blockIdx in [0:σBlocks.size] do
        let block := σBlocks[blockIdx]!
        let bsize := block.size
        for j in [0:bsize] do
          for k in [j:bsize] do
            let prod := blockProduct block j k
            let mut support : Array (CMvMonomial n × ℚ) := #[]
            for m in prod.monomials do
              let c := prod.coeff m
              if c ≠ 0 then
                support := support.push (m, c)
                if !monoIndex.contains m then
                  monoIndex := monoIndex.insert m monos.size
                  monos := monos.push m
            cached := cached.push { blockIdx, j, k, support }
      let mut cachedEq : Array (CachedEqProduct n) := #[]
      for eqIdx in [0:eqSpecs.size] do
        let spec := eqSpecs[eqIdx]!
        for b in [0:spec.size] do
          let prod := eqProduct spec b
          let mut support : Array (CMvMonomial n × ℚ) := #[]
          for m in prod.monomials do
            let c := prod.coeff m
            if c ≠ 0 then
              support := support.push (m, c)
              if !monoIndex.contains m then
                monoIndex := monoIndex.insert m monos.size
                monos := monos.push m
          cachedEq := cachedEq.push { eqIdx, basisIdx := b, support }
      return (cached, cachedEq, monos, monoIndex)
  let b : Array Float := monos.map fun m => ratToFloat (target.coeff m)
  let aTriples : Array LeanCsdp.ConstraintTriple := Id.run do
    let mut acc : Array LeanCsdp.ConstraintTriple := #[]
    for cp in cached do
      for (m, c) in cp.support do
        let monoIdx := monoIndex[m]!
        acc := acc.push
          { constraint := UInt32.ofNat (monoIdx + 1)
            block := UInt32.ofNat (cp.blockIdx + 1)
            row := UInt32.ofNat (cp.j + 1)
            col := UInt32.ofNat (cp.k + 1)
            value := ratToFloat c }
    -- Cofactor LP: contribution `cⱼ_b · coef_m(monomial_b · pⱼ)` with
    -- `cⱼ_b = x⁺[idx] − x⁻[idx]`, so emit two diagonal entries per
    -- monomial: `+coef` on the x⁺ block, `−coef` on the x⁻ block.
    for cp in cachedEq do
      let idx : Nat := cumOffsets[cp.eqIdx]! + cp.basisIdx
      for (m, c) in cp.support do
        let monoIdx := monoIndex[m]!
        let cFloat := ratToFloat c
        acc := acc.push
          { constraint := UInt32.ofNat (monoIdx + 1)
            block := UInt32.ofNat (xPosBlockIdx + 1)
            row := UInt32.ofNat (idx + 1)
            col := UInt32.ofNat (idx + 1)
            value := cFloat }
        acc := acc.push
          { constraint := UInt32.ofNat (monoIdx + 1)
            block := UInt32.ofNat (xNegBlockIdx + 1)
            row := UInt32.ofNat (idx + 1)
            col := UInt32.ofNat (idx + 1)
            value := -cFloat }
    -- LP-slack: append `+1·λ` on the constant-monomial equality.
    if let some lambdaBlockIdx := lambdaBlockIdx? then
      let constMonoIdx := monoIndex[constMono]!
      acc := acc.push
        { constraint := UInt32.ofNat (constMonoIdx + 1)
          block := UInt32.ofNat (lambdaBlockIdx + 1)
          row := 1, col := 1, value := 1.0 }
    return acc
  -- Cost matrix: trace cost on σ-blocks only. The cofactor LP blocks
  -- must have zero cost — `tr` would drive `x⁺` and `x⁻` to infinity
  -- together. CSDP maximises `tr(C·X)`. See `SdpMode`.
  let cTriples : Array LeanCsdp.Triple :=
    match mode, lambdaBlockIdx? with
    | .feasibility true, _ => Id.run do
      let mut acc : Array LeanCsdp.Triple := #[]
      for blockIdx in [0:σBlocks.size] do
        let block := σBlocks[blockIdx]!
        for j in [0:block.size] do
          acc := acc.push
            { block := UInt32.ofNat (blockIdx + 1)
              row   := UInt32.ofNat (j + 1)
              col   := UInt32.ofNat (j + 1)
              value := 1.0 }
      return acc
    | .feasibility false, _ => #[]
    | .lpSlack, some lambdaBlockIdx => #[
      { block := UInt32.ofNat (lambdaBlockIdx + 1), row := 1, col := 1,
        value := 1.0 }]
    | .lpSlack, none => #[]  -- unreachable; lambdaBlockIdx? is `some` in .lpSlack
  let problem : LeanCsdp.Problem :=
    { blockSizes := blockSizes
      b := b
      c := cTriples
      a := aTriples
      constantOffset := 0.0 }
  (problem, σBlocks, eqSpecs, monos, lambdaBlockIdx?)

/-! ### Denominator schedule for rational rounding -/

/-- Schedule of denominators tried by the rational rounder, adapted from
`sos.ml`'s `find_rounding`. First a dense small-integer region
(`[1..63]`), then powers of two interleaved with their 1.5× scalings
(`64, 96, 128, 192, 256, 384, …, 2^20`).

Harrison reports that "small ints first, then doubling" works
empirically better than a strict doubling schedule — the densified
small region and 1.5× interleaves catch Gram denominators that the
old `[1..31] ++ [2^5..2^20]` schedule missed.

Harrison's HOL Light caps at `2^66`; we cap at `2^24`. Beyond that
range, CSDP rounding noise produces tiny positive `LDL` pivots whose
`fourSquaresRat` decomposition is `O(√num · denom)` and exceeds
practical wall time. The `maxRoundingDenom` field of `SOS.Config` (see
`SOS/Tactic.lean`) filters the *full* candidate list — schedule entries,
`polyDenom target`, constraint denoms, and cross denoms — against the
cap. Targets needing a strictly larger denom fall through to
`sos_witness <hand-cert>`. -/
def niceDenominators : List ℚ :=
  let smalls : List ℚ := (List.range 63).map (fun i => (i + 1 : ℚ))
  -- For k = 6..23, alternate `2^k` and `3·2^(k-1) = 1.5·2^k`; then `2^24`.
  -- The extended range (past `2^20`) gives the Schmüdgen preordering
  -- room for product-block Grams whose denominator grows with subset
  -- cardinality (issue #38).
  let bigs : List ℚ :=
    (List.range 18).flatMap
        (fun i => [(2 ^ (i + 6) : ℚ), ((3 : ℚ) * 2 ^ (i + 5))])
      ++ [(2 ^ 24 : ℚ)]
  smalls ++ bigs

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
    Option (Array ℚ) := Id.run do
  if entries.size ≠ n * n then return none
  let mut acc : Array ℚ := #[]
  for i in [0:n] do
    for j in [i:n] do
      let v := entries.get! (j * n + i)
      acc := acc.push (niceRound denom v)
  return some acc

/-- Decode the full primal solution into per-block rational Gram matrices. -/
def decodeSolution (sol : LeanCsdp.Solution) (denom : ℚ) :
    Option (Array (Array ℚ)) := Id.run do
  let mut acc : Array (Array ℚ) := #[]
  for b in sol.X do
    match b with
    | .sdp n entries =>
      let some block := decodeSdpBlock denom n entries | return none
      acc := acc.push block
    | .diag n entries =>
      -- Defensive: the SDP builders use non-negative block sizes, so CSDP
      -- never returns `.diag` blocks for this encoding. Handle them as
      -- 1×1 sub-Grams in case the encoding changes.
      if entries.size ≠ n then return none
      let mut diag : Array ℚ := #[]
      for i in [0:n] do
        diag := diag.push (niceRound denom (entries.get! i))
      acc := acc.push diag
  return some acc

/-! ### Pre-CSDP matrix conditioning

Harrison's `scale_then` (`sos.ml:634`) preconditions the SDP before CSDP
by scaling the constraint matrices and the LP cost vector by *independent*
powers of two so each lands near `2^20`. We mirror this in our primal
encoding by choosing two shifts: `shiftAC` for the constraint matrices
`Aᵢ` (and the cost matrix `C`), and `shiftB` for the RHS `b`. Both are
computed so the corresponding entries land near `2^20` after scaling.

Under `Aᵢ → 2^shiftAC · Aᵢ`, `b → 2^shiftB · b` (`C → 2^shiftAC · C`),
the new constraint reads
  `tr(2^shiftAC · Aᵢ · X') = 2^shiftB · bᵢ`
i.e. `tr(Aᵢ · X') = 2^(shiftB − shiftAC) · bᵢ`. By linearity in `b`,
the scaled optimum is `X' = 2^(shiftB − shiftAC) · X*`, so we recover
`X* = 2^(shiftAC − shiftB) · X'` before the rational rounder runs.

When `shiftAC = shiftB` the scaling is uniform (an SDP equivalence,
`X*` preserved theoretically) and the post-multiply is a no-op. This
is the common case — typical targets have `Aᵢ` entries `0`/`1` and `b`
entries `O(1)`, both shifted to `2^20`. Targets like `sos.ml:1829`
with target coefficients spanning `100..6800` get `shiftAC = 20` but
`shiftB = 7`, so CSDP sees a problem where the scaled optimum sits in
a moderate magnitude band — better-conditioned but not, on its own,
sufficient to close every `PURE_SOS` rounding miss. Treat this as
groundwork rather than a complete fix for the conditioning-flagged
FIXMEs (see issue #36's "Why this also matters" note). -/

/-- Largest absolute value over a single component of the SDP data. -/
private def maxA (problem : LeanCsdp.Problem) : Float := Id.run do
  let mut m : Float := 0.0
  for t in problem.a do
    let v := t.value.abs
    if v > m then m := v
  return m

private def maxB (problem : LeanCsdp.Problem) : Float := Id.run do
  let mut m : Float := 0.0
  for x in problem.b do
    let v := x.abs
    if v > m then m := v
  return m

private def maxC (problem : LeanCsdp.Problem) : Float := Id.run do
  let mut m : Float := 0.0
  for t in problem.c do
    let v := t.value.abs
    if v > m then m := v
  return m

/-- Power-of-two shift bringing `entry` near `2^20`, clamped to
`[-30, +30]` so a wild value (zero, inf, NaN) can't blow the exponent.
Returns `0` (no-op) when `entry` is non-positive or non-finite. -/
private def chooseShift (entry : Float) : Int :=
  if entry ≤ 0.0 then 0
  else if entry.isNaN || entry.isInf then 0
  else
    let logRatio : Float := Float.log entry / Float.log 2.0
    -- `⌈x⌉` via `−⌊−x⌋`; convert through Int64.
    let ceilLog : Int := (-((-logRatio).floor.toInt64.toInt))
    let s : Int := 20 - ceilLog
    if s < -30 then -30 else if s > 30 then 30 else s

/-- `2^shift` as a `Float`. Implemented via `Float.pow` with the
exponent cast through `Float.ofInt`, which is exact for the clamped
range `[-30, 30]`. -/
private def pow2Float (shift : Int) : Float :=
  Float.pow 2.0 (Float.ofInt shift)

/-- Apply `(shiftAC, shiftB)` to a CSDP problem: `Aᵢ` and `C` are
multiplied by `2^shiftAC`, `b` by `2^shiftB`. Returns the scaled
problem and the resulting "X back-shift" — the exponent to multiply
CSDP's returned `X` by to recover `X*` (see the module note above).
Both shifts `0` ⇒ identity. -/
private def conditionProblem (problem : LeanCsdp.Problem) :
    LeanCsdp.Problem × Int :=
  let mA := maxA problem
  let mC := maxC problem
  let shiftAC := chooseShift (if mA > mC then mA else mC)
  let shiftB  := chooseShift (maxB problem)
  if shiftAC = 0 ∧ shiftB = 0 then (problem, 0)
  else
    let sAC := pow2Float shiftAC
    let sB  := pow2Float shiftB
    let problem' : LeanCsdp.Problem := { problem with
        a := problem.a.map fun t => { t with value := t.value * sAC }
        b := problem.b.map (· * sB)
        c := problem.c.map fun t => { t with value := t.value * sAC } }
    (problem', shiftAC - shiftB)

/-- Multiply every Gram entry of `sol.X` by `2^xShift` to reverse the
back-shift accumulated by `conditionProblem`. `xShift = 0` is a no-op. -/
private def unscaleSolution (sol : LeanCsdp.Solution) (xShift : Int) :
    LeanCsdp.Solution :=
  if xShift = 0 then sol
  else
    let s := pow2Float xShift
    let scaleArr (a : FloatArray) : FloatArray := Id.run do
      let mut out : FloatArray := FloatArray.empty
      for i in [0:a.size] do out := out.push (a.get! i * s)
      return out
    let scaleBlock : LeanCsdp.Block → LeanCsdp.Block
      | .sdp n e  => .sdp n (scaleArr e)
      | .diag n e => .diag n (scaleArr e)
    { sol with X := sol.X.map scaleBlock }

/-! ### Top-level search driver -/

/-- Convert a basis of monomials into the `Array (CMvPolynomial n ℚ)`
that `LDL.reconstruct` expects. -/
def basisAsPolys (basis : Array (CMvMonomial n)) :
    Array (CMvPolynomial n ℚ) :=
  basis.map (fun m => CMvPolynomial.monomial m (1 : ℚ))

/-- Decode an equality cofactor from the diagonal LP blocks: for each
basis monomial `m_b` of cofactor `j`, the coefficient is
`x⁺[idx] − x⁻[idx]` where `idx = cumOffset[j] + b`. Returns the
polynomial `qⱼ = Σ_b coef_b · m_b`. -/
def decodeCofactorBlock (eqSpec : EqCofactorSpec n)
    (xPosDiag : Array ℚ) (xNegDiag : Array ℚ) (offset : Nat) :
    Option (CMvPolynomial n ℚ) := Id.run do
  let mut q : CMvPolynomial n ℚ := CMvPolynomial.C 0
  for b in [0:eqSpec.size] do
    let some xp := xPosDiag[offset + b]? | return none
    let some xn := xNegDiag[offset + b]? | return none
    let coef := xp - xn
    if coef ≠ 0 then
      q := q + CMvPolynomial.monomial eqSpec.basis[b]! coef
  return some q

/-- Try one denominator: round Gram matrices, reconstruct via LDL,
decode cofactors, build a Certificate, check it. Returns `none` if any
step fails. -/
def tryDenominator (gs : List (CMvPolynomial n ℚ))
    (ps : List (CMvPolynomial n ℚ))
    (blocks : Array (BlockSpec n)) (eqSpecs : Array (EqCofactorSpec n))
    (sol : LeanCsdp.Solution) (denom : ℚ)
    (goal : Goal n) : Option (Certificate n) := Id.run do
  let some Qs := decodeSolution sol denom | return none
  let hasEqs := !ps.isEmpty
  let expectedSize := blocks.size + (if hasEqs then 2 else 0)
  if Qs.size ≠ expectedSize then return none
  let mut sigmas : Array (List Nat × SOSDecomp n) := Array.mkEmpty blocks.size
  for blockIdx in [0:blocks.size] do
    let some block := blocks[blockIdx]? | return none
    let some Q := Qs[blockIdx]? | return none
    let some sigmaSquares :=
      LDL.reconstruct block.size Q (basisAsPolys block.basis)
      | return none
    sigmas := sigmas.push (block.idxs, { squares := sigmaSquares })
  let mut eqCofs : List (CMvPolynomial n ℚ) := []
  if hasEqs then
    let some xPosDiag := Qs[blocks.size]? | return none
    let some xNegDiag := Qs[blocks.size + 1]? | return none
    let mut offset : Nat := 0
    let mut acc : Array (CMvPolynomial n ℚ) := #[]
    for spec in eqSpecs do
      let some q := decodeCofactorBlock spec xPosDiag xNegDiag offset
        | return none
      acc := acc.push q
      offset := offset + spec.size
    eqCofs := acc.toList
  let cert : Certificate n :=
    { sigmas := sigmas.toList, eqCofs := eqCofs }
  if cert.checks goal gs ps then return some cert
  return none

/-! ### Symmetry-reduced pure SOS path -/

/-- Number of upper-triangle variables in an `N × N` symmetric matrix. -/
@[inline] private def upperTriCount (N : Nat) : Nat := N * (N + 1) / 2

/-- Dense index for an upper-triangle pair `(i,j)`, normalising the pair
first. The order is row-major over `i ≤ j`: `(0,0),(0,1),...,(1,1),...`. -/
private def upperTriIndex (N i j : Nat) : Nat :=
  let a := if i ≤ j then i else j
  let b := if i ≤ j then j else i
  a * N - (a * (a - 1)) / 2 + (b - a)

/-- Inverse of `upperTriIndex`, by bounded search. The matrices involved
in SOS search are small enough that this is cheaper than maintaining a
second encoding throughout the exact elimination code. -/
private def upperTriPair (N idx : Nat) : Nat × Nat := Id.run do
  let mut k := 0
  for i in [0:N] do
    for j in [i:N] do
      if k = idx then return (i, j)
      k := k + 1
  return (0, 0)

/-- Add `delta` to an augmented dense row at variable column `idx`. -/
private def addVarCoeff (row : Array ℚ) (idx : Nat) (delta : ℚ) :
    Array ℚ :=
  row.set! idx (row[idx]! + delta)

/-- Build the exact equality system for a pure SOS Gram matrix:
coefficient-matching equations plus σ₀ Gram symmetry equations. -/
private def symmetricPureEquations (target : CMvPolynomial n ℚ)
    (block : BlockSpec n) (symmetries : Array (Array Nat)) :
    Option (Array (Array ℚ) × Array (CMvMonomial n)) := Id.run do
  let N := block.size
  let numVars := upperTriCount N
  let mut monos : Array (CMvMonomial n) := #[]
  let mut monoIndex : Std.TreeMap (CMvMonomial n) Nat compare := {}
  for m in target.monomials do
    if !monoIndex.contains m then
      monoIndex := monoIndex.insert m monos.size
      monos := monos.push m
  let mut cached : Array (Nat × Nat × Array (CMvMonomial n × ℚ)) := #[]
  for i in [0:N] do
    for j in [i:N] do
      let prod := blockProduct block i j
      let mut support : Array (CMvMonomial n × ℚ) := #[]
      for m in prod.monomials do
        let c := prod.coeff m
        if c ≠ 0 then
          support := support.push (m, c)
          if !monoIndex.contains m then
            monoIndex := monoIndex.insert m monos.size
            monos := monos.push m
      cached := cached.push (i, j, support)
  let mut rows : Array (Array ℚ) := #[]
  for m in monos do
    let mut row : Array ℚ := Array.replicate (numVars + 1) 0
    for (i, j, support) in cached do
      for (m', c) in support do
        if m' = m then
          let factor : ℚ := if i = j then 1 else 2
          let idx := upperTriIndex N i j
          row := addVarCoeff row idx (factor * c)
    row := row.set! numVars (target.coeff m)
    rows := rows.push row
  let mut basisIndex : Std.TreeMap (CMvMonomial n) Nat compare := {}
  for i in [0:N] do
    basisIndex := basisIndex.insert block.basis[i]! i
  let mut basisPerms : Array (Array Nat) := #[]
  for π in symmetries do
    let some p := SOS.Symmetry.basisPermutation π block.basis basisIndex
      | return none
    basisPerms := basisPerms.push p
  for ((i, j), (ri, rj)) in SOS.Symmetry.gramSymmetryConstraints N basisPerms do
    let mut row : Array ℚ := Array.replicate (numVars + 1) 0
    row := addVarCoeff row (upperTriIndex N i j) 1
    row := addVarCoeff row (upperTriIndex N ri rj) (-1)
    rows := rows.push row
  return some (rows, monos)

/-- Expressions for all Gram entries after exact elimination.
`constant[v]` and `coeffs[v][k]` describe upper-triangle variable `v` as
`constant[v] + Σ_k coeffs[v][k] * q_k`, where `q_k` ranges over the
free columns. -/
private structure GramParam where
  freeCols : Array Nat
  constant : Array ℚ
  coeffs   : Array (Array ℚ)

/-- Solve the equality system over `ℚ` and express every Gram entry in
terms of the remaining free orbit parameters. -/
private def gramParam (numVars : Nat) (rows : Array (Array ℚ)) :
    Option GramParam := Id.run do
  let rows := rows.map fun row => row.set! numVars (-(row[numVars]!))
  let some E := SOS.RatLinAlg.eliminateAll numVars rows | return none
  let freeCols := E.freeCols
  let mut freeIndex : Std.TreeMap Nat Nat compare := {}
  for k in [0:freeCols.size] do
    freeIndex := freeIndex.insert freeCols[k]! k
  let mut constants : Array ℚ := Array.replicate numVars 0
  let mut coeffs : Array (Array ℚ) :=
    Array.replicate numVars (Array.replicate freeCols.size 0)
  for k in [0:freeCols.size] do
    let v := freeCols[k]!
    let row := (coeffs[v]!).set! k 1
    coeffs := coeffs.set! v row
  for (pivot, row) in E.assignments do
    constants := constants.set! pivot row[numVars]!
    let mut cs : Array ℚ := Array.replicate freeCols.size 0
    for f in freeCols do
      if let some k := freeIndex[f]? then
        cs := cs.set! k row[f]!
    coeffs := coeffs.set! pivot cs
  return some { freeCols, constant := constants, coeffs }

/-- Build the constant Gram matrix and one coefficient matrix per free
parameter. Matrices are stored in upper-triangle flat order. -/
private def gramMats (N : Nat) (param : GramParam) :
    Array (Array ℚ) := Id.run do
  let numVars := upperTriCount N
  let mut mats : Array (Array ℚ) :=
    Array.replicate (param.freeCols.size + 1) (Array.replicate numVars 0)
  for v in [0:numVars] do
    let c := param.constant[v]!
    if c ≠ 0 then
      mats := mats.set! 0 ((mats[0]!).set! v c)
    let cs := param.coeffs[v]!
    for k in [0:param.freeCols.size] do
      let a := cs[k]!
      if a ≠ 0 then
        mats := mats.set! (k + 1) ((mats[k + 1]!).set! v a)
  return mats

private def upperTriTrace (N : Nat) (M : Array ℚ) : ℚ := Id.run do
  let mut t : ℚ := 0
  for i in [0:N] do
    t := t + M[upperTriIndex N i i]!
  return t

/-- CSDP encoding of the reduced dual:
`mats[0] + Σ qᵢ mats[i+1] ⪰ 0`. CSDP returns the reduced vector as the
dual variable `y`. The objective is a trace extremum in reduced
coordinates; currently this uses CSDP's dual minimisation direction,
which is enough to expose rational boundary points in the covered
`Z₂×Z₂` case. -/
private def buildReducedProblem (N : Nat) (mats : Array (Array ℚ)) :
    LeanCsdp.Problem :=
  let freeCount := mats.size - 1
  let aTriples : Array LeanCsdp.ConstraintTriple := Id.run do
    let mut acc : Array LeanCsdp.ConstraintTriple := #[]
    for k in [0:freeCount] do
      let M := mats[k + 1]!
      for v in [0:M.size] do
        let c := M[v]!
        if c ≠ 0 then
          let (i, j) := upperTriPair N v
          acc := acc.push
            { constraint := UInt32.ofNat (k + 1)
              block := 1
              row := UInt32.ofNat (i + 1)
              col := UInt32.ofNat (j + 1)
              value := ratToFloat c }
    return acc
  let cTriples : Array LeanCsdp.Triple := Id.run do
    let mut acc : Array LeanCsdp.Triple := #[]
    let M0 := mats[0]!
    for v in [0:M0.size] do
      let c := M0[v]!
      if c ≠ 0 then
        let (i, j) := upperTriPair N v
        acc := acc.push
          { block := 1
            row := UInt32.ofNat (i + 1)
            col := UInt32.ofNat (j + 1)
            value := ratToFloat (-c) }
    return acc
  let b : Array Float := Id.run do
    let mut out : Array Float := #[]
    for k in [0:freeCount] do
      out := out.push (ratToFloat (upperTriTrace N (mats[k + 1]!)))
    return out
  { blockSizes := #[Int32.ofNat N], b, c := cTriples, a := aTriples,
    constantOffset := 0.0 }

/-- Reconstruct a rational Gram matrix from a rounded reduced vector. -/
private def reconstructReducedGram (N : Nat) (mats : Array (Array ℚ))
    (vec : Array ℚ) : Option (Array ℚ) := Id.run do
  if mats.isEmpty ∨ vec.size + 1 ≠ mats.size then return none
  let numVars := upperTriCount N
  let mut Q := mats[0]!
  if Q.size ≠ numVars then return none
  for k in [0:vec.size] do
    let M := mats[k + 1]!
    if M.size ≠ numVars then return none
    for v in [0:numVars] do
      Q := Q.set! v (Q[v]! + vec[k]! * M[v]!)
  return some Q

/-- Try one denominator in the reduced free-parameter space. -/
private def tryReducedDenominator (block : BlockSpec n) (mats : Array (Array ℚ))
    (raw : FloatArray) (denom : ℚ) (goal : Goal n) :
    Option (Certificate n) := Id.run do
  let mut vec : Array ℚ := #[]
  for i in [0:raw.size] do
    vec := vec.push (niceRound denom (raw.get! i))
  let some Q := reconstructReducedGram block.size mats vec | return none
  let some sigma0Squares :=
    LDL.reconstruct block.size Q (basisAsPolys block.basis)
    | return none
  let cert : Certificate n :=
    { sigmas := [([], { squares := sigma0Squares })], eqCofs := [] }
  if cert.checks goal [] [] then return some cert
  return none

/-- Pure SOS search through the Harrison-style symmetry reduction:
eliminate coefficient and Gram-symmetry equalities over `ℚ`, solve CSDP
in the free orbit parameters, and round that small vector. -/
private def tryReducedPureSdp (target : CMvPolynomial n ℚ) (goal : Goal n)
    (useTraceCost : Bool) (extraDeg : Nat) (_strategy : BasisStrategy)
    (maxRoundingDenom : Nat) (symmetries : Array (Array Nat)) :
    IO (Option (Certificate n)) := do
  if !useTraceCost then
    return none
  if extraDeg ≠ 0 then
    return none
  let block : BlockSpec n :=
    { idxs := [],
      basis := harrisonNewtonBasis target, multiplier := CMvPolynomial.C 1 }
  if block.size = 0 then
    if target = 0 then
      return some { sigmas := [([], { squares := [] })], eqCofs := [] }
    else
      return none
  let some (eqs, _monos) := symmetricPureEquations target block symmetries
    | return none
  let numVars := upperTriCount block.size
  let some param := gramParam numVars eqs | return none
  if param.freeCols.isEmpty then
    let mats := gramMats block.size param
    let some Q := reconstructReducedGram block.size mats #[] | return none
    let some sigma0Squares :=
      LDL.reconstruct block.size Q (basisAsPolys block.basis)
      | return none
    let cert : Certificate n :=
      { sigmas := [([], { squares := sigma0Squares })], eqCofs := [] }
    if cert.checks goal [] [] then return some cert else return none
  let mats := gramMats block.size param
  let problem := buildReducedProblem block.size mats
  let sol := LeanCsdp.solve problem
  if sol.ret ∉ [0, 3] then
    return none
  let targetDenom : ℚ := (polyDenom target : ℚ)
  let denomCandidates : List ℚ := targetDenom :: niceDenominators
  let maxDenomQ : ℚ := (maxRoundingDenom : ℚ)
  for d in denomCandidates do
    if d ≤ maxDenomQ then
      if let some cert := tryReducedDenominator block mats sol.y d goal then
        return some cert
  return none

/-- Try a single SDP encoding (one choice of `useTraceCost` and one
`extraDeg` relaxation level) and the denominator schedule. Candidates
are filtered against `maxRoundingDenom` (default `2^20`); raise it via
the tactic-surface `Config.maxRoundingDenom` field for targets whose
Gram needs a larger denom. Returns `none` if CSDP fails or no rounding
validates. -/
private def tryOneSdp (target : CMvPolynomial n ℚ)
    (gs : List (CMvPolynomial n ℚ)) (ps : List (CMvPolynomial n ℚ))
    (goal : Goal n) (useTraceCost : Bool) (extraDeg : Nat)
    (strategy : BasisStrategy := .dense)
    (maxRoundingDenom : Nat := 1048576)
    (maxSubsetCardinality : Nat := 1) : IO (Option (Certificate n)) := do
  let (problem, blocks, eqSpecs, _monos, _) :=
    buildSdp target gs (.feasibility useTraceCost) ps extraDeg strategy
      maxSubsetCardinality
  if problem.b.size = 0 then
    if target = 0 then
      return some { sigmas := [([], { squares := [] })],
                    eqCofs := ps.map fun _ => CMvPolynomial.C 0 }
    else
      return none
  -- Precondition the SDP: scale `Aᵢ`/`C` and `b` by independent powers
  -- of two so each lands near `2^20`. When the chosen shifts differ
  -- (e.g. `sos.ml:1829` where target coefficients span `100..6800`),
  -- CSDP's returned `X' = 2^(shiftB − shiftAC) · X*` is moderate-magnitude
  -- and rounds cleanly; we recover `X*` by `unscaleSolution`. See the
  -- "Pre-CSDP matrix conditioning" section above.
  let (problem, xShift) := conditionProblem problem
  let sol := LeanCsdp.solve problem
  if sol.ret ∉ [0, 3] then
    return none
  let sol := unscaleSolution sol xShift
  let targetDenom : ℚ := (polyDenom target : ℚ)
  let constraintDenoms : List ℚ := gs.map fun g => (polyDenom g : ℚ)
  let equalityDenoms : List ℚ := ps.map fun p => (polyDenom p : ℚ)
  -- Heuristic extra candidates: the σᵢ-block Gram for constraint `gᵢ`
  -- often needs a denominator divisible by factors from both `target`
  -- and `gᵢ`. `polyDenom (target * gᵢ)` is a cheap shot at that grid
  -- (not a guaranteed superset of the true Gram denom — but often
  -- closer than either input alone).
  let crossDenoms : List ℚ := gs.map fun g => (polyDenom (target * g) : ℚ)
  let denomCandidates : List ℚ :=
    targetDenom :: constraintDenoms ++ crossDenoms ++ equalityDenoms
      ++ niceDenominators
  let maxDenomQ : ℚ := (maxRoundingDenom : ℚ)
  for d in denomCandidates do
    if d ≤ maxDenomQ then
      if let some cert := tryDenominator gs ps blocks eqSpecs sol d goal then
        return some cert
  return none

/-- Closed-positivity / infeasibility search: produce a Certificate
proving `target = σ₀ + Σᵢ σᵢ · gᵢ + Σⱼ qⱼ · pⱼ` for the chosen `target`.
The equality list `ps` may be empty.

Iteratively deepens the relaxation level: starts at `extraDeg = 0`
(the original fixed encoding) and grows σ₀ and each σᵢ basis by 1
monomial-degree per retry, up to `maxDepth` (default 0 — no
deepening). Harrison's `REAL_SOS` reports needing depth as high as
12; each level is a full fresh CSDP solve (CSDP has no warm starts)
and the SDP grows combinatorially with the basis, so the failure path
is `(maxDepth+1) × strategies` CSDP solves. Opt in per call via
`sos (config := { maxDepth := k })`.

`maxRoundingDenom` caps the denominator schedule (default `2^20`).
Same config struct on the tactic side. -/
def runFeasibilitySearch (target : CMvPolynomial n ℚ)
    (gs : List (CMvPolynomial n ℚ)) (ps : List (CMvPolynomial n ℚ))
    (goal : Goal n) (maxRoundingDenom : Nat := 1048576)
    (maxDepth : Nat := 0) (basisStrategy : BasisStrategy := .newton)
    (maxSubsetCardinality : Nat := 1) :
    IO (Option (Certificate n)) := do
  -- Cost-matrix strategies, in order. Trace maximisation gives CSDP
  -- a well-defined central path on rank-deficient SDPs (Harrison's
  -- HOL Light convention) but interacts badly with infeasibility
  -- certificates and with some basis choices that include the
  -- constant monomial. Pure feasibility (`c = []`) is CSDP's
  -- standard mode and works on most non-boundary problems plus
  -- infeasibility. Try whichever is more likely to succeed first
  -- and fall back.
  let costStrategies : List Bool := match goal with
    | .infeasible => [false]
    | _           => [true, false]
  -- Basis-pruning is disabled for infeasibility goals, where
  -- `target = -1` and the support of `target` carries no information
  -- about which σ₀ basis monomials can appear. The fallback to
  -- `.dense` before bumping `extraDeg` is mandatory for completeness
  -- — Reznick's half-Newton condition is only necessary for
  -- *unconstrained* σ₀; in the Putinar setting `target = σ₀ + Σ
  -- σᵢ·gᵢ`, σ₀ can absorb cancellations against terms whose Newton
  -- polytope extends past `½·Newton(target)`, so `.dense` is the
  -- safety net.
  let targetDeg := target.totalDegree
  let maxGDeg := gs.foldl (fun acc g => Nat.max acc g.totalDegree) 0
  let maxPDeg := ps.foldl (fun acc p => Nat.max acc p.totalDegree) 0
  let σ₀Deg := Nat.max (Nat.max targetDeg maxGDeg) maxPDeg
  let supportSize := target.monomials.length
  let dropConstant := target.coeff (zeroMono n) = 0
  let symmetries := SOS.Symmetry.detectSymmetries target gs ps
  let useReducedPure := gs.isEmpty ∧ ps.isEmpty ∧ symmetries.size > 1
  let pruneAllowed : Bool := match goal with
    | .infeasible => false
    | _           => basisStrategy ≠ .dense
  -- Cardinality schedule: at each relaxation depth, first try Putinar
  -- (max-cardinality 1, no product blocks — cheap when it works); if that
  -- fails fall back to Schmüdgen-style enumeration up to the caller's
  -- cap. Depth-outer keeps the easy Putinar cases fast while still
  -- letting Schmüdgen close interval-Schur-style targets at the same
  -- depth before the search bumps to the next, more expensive depth.
  let putinarCap : Nat := 1
  let fullCap : Nat := min maxSubsetCardinality gs.length
  let cardinalitySchedule : List Nat :=
    if fullCap ≤ putinarCap then [putinarCap]
    else [putinarCap, fullCap]
  for extraDeg in [0:maxDepth + 1] do
    for maxCard in cardinalitySchedule do
      let basisDeg := halfCeil σ₀Deg + extraDeg
      let fullBasisSize := (monomialsUpTo n basisDeg).size
      -- Sparsity gate (`4·|support| < C(n+D, D)`): for visibly dense
      -- targets the pruning is unlikely to shrink the basis enough to
      -- matter — and small σ₀ blocks (single-monomial bases on a
      -- target with multiple-monomial supports) can drive CSDP into a
      -- degenerate SDP that segfaults the FFI. We compute the pruned
      -- basis only when the gate clears, and additionally require the
      -- post-dropConstant size to be ≥ 2 and strictly less than dense.
      -- The `≥ 2` floor is a defence against the CSDP crash on
      -- pathologically small σ₀ blocks.
      let basisStrategies : List BasisStrategy :=
        if !pruneAllowed then [.dense]
        else if 4 * supportSize ≥ fullBasisSize then [.dense]
        else
          let pruned := basisStrategy.basisAt target basisDeg
          let post := if dropConstant then pruned.filter (· ≠ zeroMono n) else pruned
          if 2 ≤ post.size ∧ post.size < fullBasisSize
            then [basisStrategy, .dense] else [.dense]
      for strat in basisStrategies do
        for useTraceCost in costStrategies do
          if useReducedPure then
            if let some cert ← tryReducedPureSdp target goal useTraceCost extraDeg
                strat maxRoundingDenom symmetries then
              return some cert
          else
            if let some cert ← tryOneSdp target gs ps goal useTraceCost extraDeg
                strat maxRoundingDenom maxCard then
              return some cert
  return none

/-! ### Strict positivity via LP-slack maximisation

For `0 < p` over constraints `gᵢ ≥ 0`, encode `λ` as a decision
variable via `buildSdp _ _ .lpSlack` and let CSDP discover the largest
`λ*` for which `p − λ` admits a Putinar certificate at the chosen
relaxation level. Then re-solve `p − ε ≥ 0` with a rational
`ε ∈ (0, λ*)` to obtain a verifiable certificate. The two-stage
design avoids trying to round the σ-block Gram matrices from the LP
solve directly: the witnesses for `p − λ*` won't generally round to
witnesses for `p − ε`, so a clean re-solve is more robust. -/

/-- Strict-positivity certificate output bundle. -/
structure StrictResult (n : Nat) where
  cert : Certificate n
  ε    : ℚ
  hε   : 0 < ε

/-- Read `λ*` from the LP-slack solve. The λ block is a 1×1 PSD block,
so its sole entry is the value we want. The `.diag` arm is defensive
— the LP-slack builder uses a positive `1×1` block size, so CSDP
returns `.sdp` here. -/
private def readLambda (sol : LeanCsdp.Solution) (lambdaBlockIdx : Nat) :
    Float :=
  match sol.X[lambdaBlockIdx]? with
  | some (.sdp _ entries) => if entries.size > 0 then entries.get! 0 else 0.0
  | some (.diag _ entries) => if entries.size > 0 then entries.get! 0 else 0.0
  | none => 0.0

/-- Strict-positivity search via LP-slack maximisation. CSDP discovers
`λ*`, the largest slack admissible at this relaxation level. We then
try `ε = 2^-k` for `k` chosen so that `2^-k ≲ λ*`, descending until a
candidate certifies. Powers-of-two denominators keep the residual
`p − ε` clean for the LDL + four-squares pipeline. The factor-2 slack
on `λ*` accounts for CSDP imprecision — when `λ*` is reported just
below a clean power of two, we still try the natural largest `ε`.
Returns `none` if CSDP fails, `λ* ≤ 1e-9`, or no candidate ε in the
window admits a verifiable certificate. -/
def runStrict (p : CMvPolynomial n ℚ)
    (gs : List (CMvPolynomial n ℚ)) (ps : List (CMvPolynomial n ℚ) := [])
    (maxRoundingDenom : Nat := 1048576) (maxDepth : Nat := 0)
    (basisStrategy : BasisStrategy := .newton)
    (maxSubsetCardinality : Nat := 1) :
    IO (Option (StrictResult n)) := do
  -- Iteratively deepen alongside `runFeasibilitySearch`: each outer
  -- pass re-runs the LP-slack solve at the higher relaxation. Each
  -- LP-slack solve generally returns a different `λ*` (and thus a
  -- different sweep of ε candidates), so the work isn't redundant
  -- with earlier outer iterations. The inner feasibility call passes
  -- `(maxDepth := extraDeg)`, which is one strictly larger than
  -- necessary — it re-tries depths `0..extraDeg-1` on each `(ε,
  -- extraDeg)` pair. Bounded redundancy; acceptable for the simpler
  -- driver structure.
  for extraDeg in [0:maxDepth + 1] do
    -- The LP-slack pass uses the `.dense` σ₀ basis. The slack solve
    -- estimates `λ*`; dense is more robust against degeneracy and
    -- the gain from pruning here is small compared to the inner
    -- feasibility loops, which do honour `basisStrategy`.
    let (problem, _σBlocks, _eqSpecs, _monos, lambdaBlockIdx?) :=
      buildSdp p gs .lpSlack ps extraDeg .dense maxSubsetCardinality
    let some lambdaBlockIdx := lambdaBlockIdx? | return none
    -- Same pre-CSDP conditioning as `tryOneSdp`. `λ` lives in a primal
    -- block of `sol.X`, so it scales with `X*` and `unscaleSolution`
    -- recovers it in the polynomial scale used to pick rational `ε`.
    let (problem, xShift) := conditionProblem problem
    let sol := LeanCsdp.solve problem
    if sol.ret ∉ [0, 3] then continue
    let sol := unscaleSolution sol xShift
    let lambdaStar := readLambda sol lambdaBlockIdx
    if lambdaStar ≤ 0.000000001 then continue
    -- Find the smallest k such that 2^-k ≤ 2·λ*. The factor-2 slack
    -- means CSDP returning `λ* = 0.999...` for a true optimum of 1
    -- still starts at k = 0 (ε = 1).
    let mut bound : Float := 1.0
    let mut k : Nat := 0
    let mut bail := false
    while bound > 2.0 * lambdaStar do
      bound := bound * 0.5
      k := k + 1
      if k > 25 then
        bail := true
        break
    if bail then continue
    -- Try ε = 2^-k, 2^-(k+1), ..., 2^-(k+7). Each is a power-of-two
    -- denominator; the first that closes wins. Pass `extraDeg` as the
    -- inner `maxDepth` cap so the inner search tries up to the same
    -- relaxation as the LP-slack solve that produced `λ*`.
    for j in [0:8] do
      let denom : Nat := 2 ^ (k + j)
      let ε : ℚ := 1 / (denom : ℚ)
      if hε : 0 < ε then
        let goal : Goal n := .strict p ε hε
        let targetPoly := p - CMvPolynomial.C ε
        match (← runFeasibilitySearch targetPoly gs ps goal maxRoundingDenom
            (maxDepth := extraDeg) (basisStrategy := basisStrategy)
            (maxSubsetCardinality := maxSubsetCardinality)) with
        | some cert => return some { cert, ε, hε }
        | none => pure ()
  return none

/-- Closed/infeasibility search dispatcher. Owns the `Goal → target`
translation (`p` for `.closed`, `-1` for `.infeasible`). Strict
positivity has its own entry point: `runStrict`; the `.strict` arm
here is a defensive `none` for direct callers (the tactic surface
routes `.strict` goals straight to `runStrict`). -/
def runSearch (goal : Goal n) (gs : List (CMvPolynomial n ℚ))
    (ps : List (CMvPolynomial n ℚ) := [])
    (maxRoundingDenom : Nat := 1048576) (maxDepth : Nat := 0)
    (basisStrategy : BasisStrategy := .newton)
    (maxSubsetCardinality : Nat := 1) :
    IO (Option (Certificate n)) := do
  match goal with
  | .closed p   =>
    runFeasibilitySearch p gs ps goal maxRoundingDenom maxDepth basisStrategy
      maxSubsetCardinality
  | .infeasible =>
    runFeasibilitySearch (-1) gs ps goal maxRoundingDenom maxDepth basisStrategy
      maxSubsetCardinality
  | .strict ..  => return none

end SOS.Search
