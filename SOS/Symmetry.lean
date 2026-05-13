/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Variable-permutation symmetry detection for the σ₀ Gram block. A
permutation `π : Fin n → Fin n` is a *symmetry of the problem*
`target = σ₀ + Σ σᵢ·gᵢ + Σ qⱼ·pⱼ` iff it fixes every input
polynomial (`target`, every `gᵢ`, every `pⱼ`). For such π, the σ₀
Gram matrix `Q` admits the symmetry `Q[π̂(i), π̂(j)] = Q[i, j]` where
`π̂` is the lift of π to the σ₀ basis monomials. This file builds the
permutation group of the problem and the resulting equality
constraints on `Q` for CSDP to enforce, following Harrison's
`sumofsquares_general_symmetry` (`sos.ml:1487`).
-/
import CompPoly.Multivariate.CMvPolynomial
import CompPoly.Multivariate.Operations
import Std.Data.TreeMap

namespace SOS.Symmetry

open CPoly

/-- Maximum `n` for which we enumerate the full symmetric group `S_n`.
`5! = 120`; beyond this the cost of generate-then-filter outweighs the
gain. Targets with `n > 5` get the trivial (identity-only) symmetry
group, which makes the symmetry pipeline a no-op. -/
def maxSymmetryArity : Nat := 5

/-- All permutations of `[0, n)` as length-`n` arrays, in lex order
over the prefix. For `n > maxSymmetryArity` returns just the
identity. -/
partial def allPermutations (n : Nat) : Array (Array Nat) :=
  if n > maxSymmetryArity then
    #[Array.range n]
  else
    let rec go (rem : List Nat) (acc : Array Nat) : Array (Array Nat) :=
      match rem with
      | [] => #[acc]
      | _  => Id.run do
        let mut out : Array (Array Nat) := #[]
        for x in rem do
          out := out ++ go (rem.filter (· ≠ x)) (acc.push x)
        return out
    go (List.range n) #[]

variable {n : Nat}

/-- Local default: the all-zero monomial. Required for `Array.get!` /
`basis[i]!` lookups in this module — `Search.lean` provides the same
instance, but we declare it here too so `SOS.Symmetry` builds standalone. -/
private def zeroMono (n : Nat) : CMvMonomial n :=
  ⟨Array.replicate n 0, by simp⟩

instance : Inhabited (CMvMonomial n) := ⟨zeroMono n⟩

/-- Permute the exponent vector of a monomial under `π : Fin n → Fin n`
(encoded as `perm[i] = π i`): the new monomial `m'` satisfies
`m'[π i] = m[i]`, i.e., variable `Xᵢ` is renamed to `X_{π i}`. -/
def permuteMono (perm : Array Nat) (m : CMvMonomial n) : CMvMonomial n :=
  let invArr : Array Nat := Id.run do
    let mut inv : Array Nat := Array.replicate n 0
    for i in [0:n] do
      let pi := perm[i]?.getD i
      if pi < n then inv := inv.set! pi i
    return inv
  Vector.ofFn fun (j : Fin n) =>
    let k := invArr[j.val]?.getD j.val
    m[k]?.getD 0

/-- Apply a variable permutation to a polynomial: `(π · p)(X) = p(X_π)`.
The new polynomial has, for each support monomial `m` of `p`, the
coefficient of `m` moved onto `permuteMono perm m`. -/
def applyVarPerm (perm : Array Nat) (p : CMvPolynomial n ℚ) :
    CMvPolynomial n ℚ := Id.run do
  let mut acc : CMvPolynomial n ℚ := 0
  for m in p.monomials do
    let c := p.coeff m
    if c ≠ 0 then
      acc := acc + CMvPolynomial.monomial (permuteMono perm m) c
  return acc

/-- The variable-permutation symmetry group of the problem
`target = σ₀ + Σ σᵢ·gᵢ + Σ qⱼ·pⱼ`: permutations of `Fin n` that fix
`target`, every `gᵢ`, and every `pⱼ` simultaneously. Identity is
always included. -/
def detectSymmetries (target : CMvPolynomial n ℚ)
    (gs : List (CMvPolynomial n ℚ)) (ps : List (CMvPolynomial n ℚ)) :
    Array (Array Nat) := Id.run do
  let mut out : Array (Array Nat) := #[]
  for π in allPermutations n do
    if applyVarPerm π target = target ∧
        gs.all (fun g => applyVarPerm π g = g) ∧
        ps.all (fun p => applyVarPerm π p = p) then
      out := out.push π
  return out

/-! ### Lifting a variable permutation to the σ₀ basis -/

/-- Lift a variable permutation `π` to a permutation `π̂` on the σ₀
basis indices: `π̂(i)` is the index of `permuteMono π basis[i]` in
`basis`. Returns `none` if some permuted basis monomial falls outside
the basis (shouldn't happen for a symmetry of `target` on the
half-Newton-polytope basis — Newton(π·t) = π·Newton(t), so the
half-Newton basis is closed under π; for the dense `monomialsUpTo n d`
basis closure is automatic since `π` preserves total degree). -/
def basisPermutation (perm : Array Nat) (basis : Array (CMvMonomial n))
    (basisIndex : Std.TreeMap (CMvMonomial n) Nat compare) :
    Option (Array Nat) := Id.run do
  let mut out : Array Nat := Array.mkEmpty basis.size
  for i in [0:basis.size] do
    let m := basis[i]!
    let permM := permuteMono perm m
    match basisIndex[permM]? with
    | some j => out := out.push j
    | none   => return none
  return some out

/-! ### Gram-symmetry constraint generation -/

/-- Encode an unordered pair `(i, j)` with `i, j < N` as a single
`Nat` in `[0, N²)`. The pair is first normalised so `i ≤ j`. -/
@[inline] private def pairIdx (N i j : Nat) : Nat :=
  if i ≤ j then i * N + j else j * N + i

/-- Walk parent pointers to the root. No path compression — chains
stay short because we union by linking the smaller-index root onto
the larger-index root, and orbits over `N ≤ ~30` basis entries are
small. -/
private partial def ufFind (parent : Array Nat) (i : Nat) : Nat :=
  let p := parent[i]?.getD i
  if p = i then i else ufFind parent p

/-- For each non-trivial orbit on the unordered pairs `{(i, j) : i ≤ j < N}`
under the action of `basisPerms` (each π acts by `(i, j) ↦ (π i, π j)`),
return one `(pair, root)` entry for every pair that is *not* its orbit
representative. The root of each orbit is the lex-smallest pair
(normalised so the first coordinate ≤ the second). The caller emits
one `Q[pair] − Q[root] = 0` constraint per entry. -/
def gramSymmetryConstraints (N : Nat) (basisPerms : Array (Array Nat)) :
    Array ((Nat × Nat) × (Nat × Nat)) := Id.run do
  let total := N * N
  let mut parent : Array Nat := Array.range total
  for π in basisPerms do
    for i in [0:N] do
      for j in [i:N] do
        let pi := π[i]?.getD i
        let pj := π[j]?.getD j
        let a := pairIdx N i j
        let b := pairIdx N pi pj
        if a ≠ b then
          let ra := ufFind parent a
          let rb := ufFind parent b
          if ra ≠ rb then
            -- Link the larger-rooted index onto the smaller, so roots
            -- end up at the lex-smallest pair (small `i*N+j` ⇔ small
            -- `(i, j)` lex).
            if ra < rb then parent := parent.set! rb ra
            else parent := parent.set! ra rb
  let mut out : Array ((Nat × Nat) × (Nat × Nat)) := #[]
  for i in [0:N] do
    for j in [i:N] do
      let p := pairIdx N i j
      let r := ufFind parent p
      if r ≠ p then
        let ri := r / N
        let rj := r % N
        out := out.push ((i, j), (ri, rj))
  return out

end SOS.Symmetry
