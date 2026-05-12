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

/-! ### Rounding-denominator schedule (#15)

The denser schedule is `[1..63]` followed by alternating `2^k`,
`3·2^(k-1)` for `k = 6..19`, then `2^20`. -/

#guard SOS.Search.niceDenominators.length = 63 + 14 * 2 + 1
#guard (SOS.Search.niceDenominators.take 63) =
    ((List.range 63).map (fun i => (i + 1 : ℚ)))
#guard (SOS.Search.niceDenominators.drop 63).take 6 =
    [(64 : ℚ), 96, 128, 192, 256, 384]
#guard SOS.Search.niceDenominators.getLast? = some (1048576 : ℚ)

-- Densified region was absent from the old `[1..31] ++ [2^5..2^20]`.
#guard SOS.Search.niceDenominators.contains (45 : ℚ)
#guard SOS.Search.niceDenominators.contains (96 : ℚ)

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
