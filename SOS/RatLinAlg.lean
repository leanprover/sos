/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Rat.Defs

namespace SOS.RatLinAlg

/-!
# Small exact-rational linear algebra

Dense Gauss-Jordan elimination over `ℚ`, used by the symmetric SOS
path to eliminate polynomial-coefficient and Gram-symmetry equalities
before calling CSDP.
-/

/-- RREF output for a system `A x = b`. Each row in `rows` has
`numVars + 1` entries, with the final entry the RHS. `pivots[i]` is the
pivot column for `rows[i]`. -/
structure Rref where
  rows    : Array (Array ℚ)
  pivots  : Array Nat
  numVars : Nat

/-- Output of Harrison-style equation elimination. `assignments` stores
one `(pivot, expr)` per eliminated variable; `expr` is an augmented row
with zero pivot coefficient and means `pivot = expr`. -/
structure Elim where
  assignments : Array (Nat × Array ℚ)
  freeCols    : Array Nat
  numVars     : Nat

/-- Remove all-zero rows from a row-echelon form. -/
private def nonzeroRows (numVars : Nat) (rows : Array (Array ℚ)) :
    Array (Array ℚ) × Array Nat := Id.run do
  let mut out : Array (Array ℚ) := #[]
  let mut pivots : Array Nat := #[]
  for row in rows do
    let mut pivot? : Option Nat := none
    for j in [0:numVars] do
      if row[j]?.getD 0 ≠ 0 then
        pivot? := some j
        break
    if let some j := pivot? then
      out := out.push row
      pivots := pivots.push j
    else if row[numVars]?.getD 0 ≠ 0 then
      out := out.push row
  return (out, pivots)

/-- Reduced row-echelon form of a dense augmented matrix over `ℚ`.
Malformed rows are padded/truncated defensively via `getD 0`; callers in
this repository always pass rows of length `numVars + 1`. -/
def rref (numVars : Nat) (inputRows : Array (Array ℚ)) : Rref := Id.run do
  let width := numVars + 1
  let mut rows : Array (Array ℚ) := #[]
  for row in inputRows do
    let mut r : Array ℚ := Array.mkEmpty width
    for j in [0:width] do
      r := r.push (row[j]?.getD 0)
    rows := rows.push r
  let mut lead : Nat := 0
  let mut r : Nat := 0
  while r < rows.size ∧ lead < numVars do
    let mut i := r
    while i < rows.size ∧ rows[i]![lead]! = 0 do
      i := i + 1
    if i = rows.size then
      lead := lead + 1
    else
      let tmp := rows[r]!
      rows := rows.set! r rows[i]!
      rows := rows.set! i tmp
      let pivot := rows[r]![lead]!
      let mut prow := rows[r]!
      for j in [0:width] do
        prow := prow.set! j (prow[j]! / pivot)
      rows := rows.set! r prow
      for i2 in [0:rows.size] do
        if i2 ≠ r then
          let factor := rows[i2]![lead]!
          if factor ≠ 0 then
            let mut row := rows[i2]!
            for j in [0:width] do
              row := row.set! j (row[j]! - factor * prow[j]!)
            rows := rows.set! i2 row
      r := r + 1
      lead := lead + 1
  let (finalRows, pivots) := nonzeroRows numVars rows
  { rows := finalRows, pivots, numVars }

/-- Free columns of an RREF result. -/
def Rref.freeCols (R : Rref) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  for j in [0:R.numVars] do
    if !(R.pivots.contains j) then
      out := out.push j
  return out

/-- Does a reduced system contain a contradictory row `0 = c`, `c ≠ 0`? -/
def Rref.inconsistent (R : Rref) : Bool := Id.run do
  for row in R.rows do
    let mut lhsZero := true
    for j in [0:R.numVars] do
      if row[j]?.getD 0 ≠ 0 then
        lhsZero := false
    if lhsZero ∧ row[R.numVars]?.getD 0 ≠ 0 then
      return true
  return false

private def addRows (r s : Array ℚ) : Array ℚ := Id.run do
  let width := Nat.max r.size s.size
  let mut out : Array ℚ := Array.mkEmpty width
  for j in [0:width] do
    out := out.push (r[j]?.getD 0 + s[j]?.getD 0)
  return out

private def scaleRow (a : ℚ) (r : Array ℚ) : Array ℚ :=
  r.map (fun x => a * x)

/-- Choose the first non-zero variable coefficient in a dense augmented
row. The RHS column is deliberately ignored. -/
private def firstVar? (numVars : Nat) (row : Array ℚ) : Option Nat := Id.run do
  for j in [0:numVars] do
    if row[j]?.getD 0 ≠ 0 then
      return some j
  return none

/-- Eliminate one variable from `row` using the original equation `eq`,
whose pivot variable is `v` with coefficient `a`. -/
private def eliminateFromRow (v : Nat) (a : ℚ) (eq row : Array ℚ) : Array ℚ :=
  let b := row[v]?.getD 0
  if b = 0 then row
  else
    let out := addRows row (scaleRow (-(b / a)) eq)
    out.set! v 0

/-- Harrison-style one-pass exact elimination.

Unlike RREF, this does not canonicalise the row space. It walks equations
in order, chooses a pivot from the current equation, substitutes that
pivot out of prior assignments and later equations, and finally reports
the variables that remain in assignment right-hand sides as free
parameters. This non-canonical coordinate chart is intentionally useful
for SOS rounding: it matches Harrison's reduced SDP much more closely
than lexicographic RREF coordinates. -/
def eliminateAll (numVars : Nat) (inputRows : Array (Array ℚ)) :
    Option Elim := Id.run do
  let width := numVars + 1
  let mut future : Array (Array ℚ) := #[]
  for row in inputRows do
    let mut r : Array ℚ := Array.mkEmpty width
    for j in [0:width] do
      r := r.push (row[j]?.getD 0)
    future := future.push r
  let mut assignments : Array (Nat × Array ℚ) := #[]
  while !future.isEmpty do
    let eq := future[0]!
    future := future.extract 1 future.size
    match firstVar? numVars eq with
    | none =>
      if eq[numVars]?.getD 0 ≠ 0 then
        return none
    | some v =>
      let a := eq[v]!
      let mut expr := scaleRow (-(1 / a)) eq
      expr := expr.set! v 0
      let mut assignments' : Array (Nat × Array ℚ) := #[]
      for (w, row) in assignments do
        assignments' :=
          assignments'.push (w, eliminateFromRow v a eq row)
      assignments := assignments'.push (v, expr)
      let mut future' : Array (Array ℚ) := #[]
      for row in future do
        let row' := eliminateFromRow v a eq row
        future' := future'.push row'
      future := future'
  let mut freeCols : Array Nat := #[]
  for (_, row) in assignments do
    for j in [0:numVars] do
      if row[j]?.getD 0 ≠ 0 ∧ !(freeCols.contains j) then
        freeCols := freeCols.push j
  return some { assignments, freeCols, numVars }

end SOS.RatLinAlg
