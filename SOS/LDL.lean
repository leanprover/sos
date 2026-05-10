/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Rational LDLᵀ decomposition and Lagrange four-square decomposition.

These are pure executable algorithms. Their *output* is verified
downstream (the certificate's polynomial identity is checked by
`cbv_decide` against `Certificate.checks`); no Lean-side correctness
proofs are needed at this layer. If LDL fails (matrix is not strictly
PSD on its diagonal pivots) or the four-square search fails, we
return `none` and the search loop tries the next denominator.
-/
import SOS.Certificate

namespace SOS.LDL

open CPoly

/-! ### Rational LDLᵀ decomposition -/

/-- Index into the upper-triangle row-major flat array for an n×n matrix.
We store entries `Q[i,j]` for `0 ≤ i ≤ j < n` at position
`i*n - i*(i+1)/2 + j`. -/
@[inline] def upperIdx (n : Nat) (i j : Nat) : Nat :=
  i * n - i * (i + 1) / 2 + j

/-- Number of entries in the upper-triangle storage for an `n × n`
symmetric matrix. -/
@[inline] def upperSize (n : Nat) : Nat :=
  n * (n + 1) / 2

/-- Read entry `(i, j)` from a symmetric matrix stored as upper-triangle.
The caller may pass `i > j`; we transpose. -/
@[inline] def readSym (n : Nat) (Q : Array ℚ) (i j : Nat) : ℚ :=
  if i ≤ j then Q[upperIdx n i j]! else Q[upperIdx n j i]!

/-- Result of LDLᵀ: `L` (n×n lower-unit-triangular, row-major dense) and
`D` (length-n diagonal). -/
structure LDLT where
  n : Nat
  L : Array ℚ
  D : Array ℚ
  deriving Inhabited, Repr

namespace LDLT

@[inline] def get (ldl : LDLT) (i j : Nat) : ℚ := ldl.L[i * ldl.n + j]!

end LDLT

/-- Compute the rational LDLᵀ decomposition of a symmetric matrix `Q`
(upper-triangle flat form). Returns `none` if any pivot is strictly
negative or if the matrix is not PSD. Zero pivots are accepted when
the corresponding residual column is also zero — this is the
"completing the square" convention from Harrison's HOL Light
`Examples/sos.ml`, and lets us decompose rank-deficient PSD matrices
whose Gram lies on the boundary of the PSD cone (e.g. the unique SOS
Gram of `(x + y)²`). When `D[j] = 0` we set `L[i, j] := 0` for
`i > j`; `LDL.reconstruct` and `transposeMulBasis` already drop
zero-`D` and zero-`L` contributions. -/
def decompose (n : Nat) (Q : Array ℚ) : Option LDLT := Id.run do
  if Q.size ≠ upperSize n then return none
  let mut L : Array ℚ := Array.replicate (n * n) 0
  let mut D : Array ℚ := Array.replicate n 0
  for j in [0:n] do
    let mut djAcc : ℚ := readSym n Q j j
    for k in [0:j] do
      let ljk := L[j * n + k]!
      djAcc := djAcc - D[k]! * ljk * ljk
    if djAcc < 0 then return none
    D := D.set! j djAcc
    L := L.set! (j * n + j) 1
    if djAcc = 0 then
      -- Rank deficient at this pivot. The matrix is PSD iff the
      -- residual column for this `j` is also zero. Check; reject if
      -- any residual is non-zero, otherwise leave `L[i, j] = 0`.
      for i in [j+1:n] do
        let mut numer : ℚ := readSym n Q i j
        for k in [0:j] do
          numer := numer - D[k]! * L[i * n + k]! * L[j * n + k]!
        if numer ≠ 0 then return none
    else
      for i in [j+1:n] do
        let mut numer : ℚ := readSym n Q i j
        for k in [0:j] do
          numer := numer - D[k]! * L[i * n + k]! * L[j * n + k]!
        L := L.set! (i * n + j) (numer / djAcc)
  return some { n := n, L := L, D := D }

/-! ### Lagrange four-square decomposition -/

/-- Integer square root, lower-bound. -/
def isqrt (n : Nat) : Nat := Id.run do
  let mut k : Nat := 0
  let mut bound : Nat := n
  -- We're looking for the largest k with k² ≤ n. Try increasing.
  while (k + 1) * (k + 1) ≤ bound do
    k := k + 1
  return k

/-- Find naturals `a, b, c, d` with `a² + b² + c² + d² = n`. By Lagrange's
four-square theorem this exists for every `n : ℕ`; we brute-force search.

We cap `n` at `1 <<< 20` to bound the worst-case `O(n^(3/2))` inner-loop
work to a few seconds. The rounding loop in `runFeasibilitySearch`
calls this on `target_pivot.num · target_pivot.den` per LDL diagonal;
huge `num · den` happens when CSDP rounding noise produces tiny
pivots at large schedule denominators (the rounded value is "real
noise rounded to a fine grid", not a genuine SOS coefficient). Giving
up on those rounding attempts is the right semantics — the next
denominator in the schedule is what we want to try. -/
def fourSquaresNat (n : Nat) : Option (Nat × Nat × Nat × Nat) := Id.run do
  if n > 1 <<< 20 then return none
  let m := isqrt n
  for d in [0:m+1] do
    if d * d > n then break
    for c in [0:d+1] do
      if d * d + c * c > n then break
      for b in [0:c+1] do
        if d * d + c * c + b * b > n then break
        let rem := n - d * d - c * c - b * b
        let a := isqrt rem
        if a * a == rem then
          return some (a, b, c, d)
  return none

/-- Decompose a non-negative rational `r` as a sum of (at most four)
rational squares. Returns the list of square roots. -/
def fourSquaresRat (r : ℚ) : Option (List ℚ) := Id.run do
  if r == 0 then return some []
  if r < 0 then return none
  let p := r.num
  let q := (r.den : Int)
  let pq := p * q
  if pq < 0 then return none
  match fourSquaresNat pq.toNat with
  | none => return none
  | some (a, b, c, d) =>
    let qq : ℚ := (q : ℚ)
    return some [
      (a : ℚ) / qq,
      (b : ℚ) / qq,
      (c : ℚ) / qq,
      (d : ℚ) / qq
    ]

/-! ### Reconstruction: Gram matrix → list of polynomial squares -/

/-- Compute `Lᵀ · z`. The result has length `ldl.n`; element `i` is
`Σ_k L[k,i] · z[k]`. -/
def transposeMulBasis {nVar : Nat} (ldl : LDLT)
    (basis : Array (CMvPolynomial nVar ℚ)) :
    Option (Array (CMvPolynomial nVar ℚ)) := Id.run do
  let n := ldl.n
  if basis.size ≠ n then return none
  let mut w : Array (CMvPolynomial nVar ℚ) := Array.mkEmpty n
  for i in [0:n] do
    let mut acc : CMvPolynomial nVar ℚ := CMvPolynomial.C 0
    for k in [0:n] do
      let lki := ldl.get k i
      if lki ≠ 0 then
        let some bk := basis[k]? | return none
        acc := acc + CMvPolynomial.C lki * bk
    w := w.push acc
  return some w

/-- Given a PSD rational matrix `Q` and a basis polynomial vector `z`,
produce a list of polynomial squares whose sum equals `zᵀ Q z`. -/
def reconstruct {nVar : Nat} (n : Nat) (Q : Array ℚ)
    (basis : Array (CMvPolynomial nVar ℚ)) :
    Option (List (CMvPolynomial nVar ℚ)) := Id.run do
  if Q.size ≠ upperSize n then return none
  if basis.size ≠ n then return none
  match decompose n Q with
  | none => return none
  | some ldl =>
    let some w := transposeMulBasis ldl basis | return none
    let mut squares : Array (CMvPolynomial nVar ℚ) := #[]
    for i in [0:n] do
      let Di := ldl.D[i]!
      let some wi := w[i]? | return none
      match fourSquaresRat Di with
      | none => return none
      | some coeffs =>
        for c in coeffs do
          if c ≠ 0 then
            squares := squares.push (CMvPolynomial.C c * wi)
    return some squares.toList

end SOS.LDL
