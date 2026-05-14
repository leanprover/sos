/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Pure invariant checks for search / round / reconstruct helpers. These
exercise internal helpers (`monomialsUpTo`, `decodeSdpBlock`,
`LDL.reconstruct`, the rounding-denominator schedule) on degenerate
or boundary inputs, so a refactor that mis-handles the empty / null
case is caught here rather than only by the end-to-end `by sos`
examples in `SOSTest.Examples`.
-/
import SOS

open SOS CPoly

/-! ### Rounding-denominator schedule

The schedule is `[1..31]` followed by `2^k` for `k = 5..66`, matching
`sos.ml`'s `find_rounding`. -/

#guard SOS.Search.niceDenominators.length = 31 + 62
#guard (SOS.Search.niceDenominators.take 31) =
    ((List.range 31).map (fun i => (i + 1 : ℚ)))
#guard (SOS.Search.niceDenominators.drop 31).take 4 =
    [(32 : ℚ), 64, 128, 256]
#guard SOS.Search.niceDenominators.getLast? = some ((2 ^ 66 : Nat) : ℚ)

/-! ### Exact rational row reduction -/

#guard
  let R := SOS.RatLinAlg.rref 2
    #[#[(1 : ℚ), 1, 3],
      #[(2 : ℚ), -1, 0]]
  R.pivots = #[0, 1] ∧ R.freeCols = #[] ∧
    R.rows = #[#[(1 : ℚ), 0, 1], #[(0 : ℚ), 1, 2]]

#guard
  let R := SOS.RatLinAlg.rref 3
    #[#[(1 : ℚ), 1, 0, 0]]
  R.pivots = #[0] ∧ R.freeCols = #[1, 2]

#guard
  match SOS.RatLinAlg.eliminateAll 2
      #[#[(1 : ℚ), 1, -3],
        #[(2 : ℚ), -1, 0]] with
  | some E =>
      E.freeCols = #[] ∧
        E.assignments.map (fun (v, row) => (v, row)) =
          #[(0, #[(0 : ℚ), 0, 1]), (1, #[(0 : ℚ), 0, 2])]
  | none => false

/-! ### `monomialsUpTo` -/

#guard (SOS.Search.monomialsUpTo 2 2).size = 6

#guard
  match (SOS.Search.monomialsUpTo 2 2)[1]? with
  | some m =>
    let a := CMvMonomial.degreeOf m ⟨0, by decide⟩
    let b := CMvMonomial.degreeOf m ⟨1, by decide⟩
    a = 1 ∧ b = 0
  | none => False

/-! ### Degenerate `decodeSdpBlock` / `LDL.reconstruct` -/

#guard
  match SOS.Search.decodeSdpBlock (1 : ℚ) 2 FloatArray.empty with
  | none => true
  | some _ => false

#guard
  match SOS.LDL.reconstruct 2 (#[] : Array ℚ)
      (#[] : Array (CMvPolynomial 1 ℚ)) with
  | none => true
  | some _ => false
