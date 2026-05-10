/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SOS.Atoms
import Mathlib.Data.Real.Basic

namespace SOS.Poly

/-- Untyped polynomial AST with `ℕ`-valued atom indices. Built up during
reification before the total atom count is known. -/
inductive Raw where
  | const : Rat → Raw
  | var   : Nat → Raw          -- atom index
  | neg   : Raw → Raw
  | add   : Raw → Raw → Raw
  | sub   : Raw → Raw → Raw
  | mul   : Raw → Raw → Raw
  | pow   : Raw → Nat → Raw
  deriving Inhabited, Repr

/-- One past the largest atom index referenced in `r`. Used as the lower
bound on `n` when casting to the typed form `Poly n`. -/
def Raw.maxAtomBound : Raw → Nat
  | .const _   => 0
  | .var i     => i + 1
  | .neg p     => p.maxAtomBound
  | .add p q   => max p.maxAtomBound q.maxAtomBound
  | .sub p q   => max p.maxAtomBound q.maxAtomBound
  | .mul p q   => max p.maxAtomBound q.maxAtomBound
  | .pow p _   => p.maxAtomBound

/-- Real-valued denotation under an unbounded valuation. -/
def Raw.eval (φ : Nat → ℝ) : Raw → ℝ
  | .const r   => (r : ℝ)
  | .var i     => φ i
  | .neg p     => -p.eval φ
  | .add p q   => p.eval φ + q.eval φ
  | .sub p q   => p.eval φ - q.eval φ
  | .mul p q   => p.eval φ * q.eval φ
  | .pow p k   => p.eval φ ^ k

end SOS.Poly

namespace SOS

/-- Typed polynomial AST in `n` variables. Obtained from `Poly.Raw` once the
total atom count is known. -/
inductive Poly (n : Nat) where
  | const : Rat → Poly n
  | var   : Fin n → Poly n
  | neg   : Poly n → Poly n
  | add   : Poly n → Poly n → Poly n
  | sub   : Poly n → Poly n → Poly n
  | mul   : Poly n → Poly n → Poly n
  | pow   : Poly n → Nat → Poly n
  deriving Inhabited, Repr, DecidableEq

end SOS

namespace SOS.Poly

/-- Cast `Raw` into the typed `Poly n` once `n ≥ r.maxAtomBound`. -/
def Raw.cast : (n : Nat) → (r : Raw) → r.maxAtomBound ≤ n → SOS.Poly n
  | _, .const r,   _ => .const r
  | _, .var i,     h => .var ⟨i, by simp [maxAtomBound] at h; omega⟩
  | n, .neg p,     h => .neg (cast n p h)
  | n, .add p q, h =>
    .add (cast n p (le_trans (Nat.le_max_left _ _) h))
         (cast n q (le_trans (Nat.le_max_right _ _) h))
  | n, .sub p q, h =>
    .sub (cast n p (le_trans (Nat.le_max_left _ _) h))
         (cast n q (le_trans (Nat.le_max_right _ _) h))
  | n, .mul p q, h =>
    .mul (cast n p (le_trans (Nat.le_max_left _ _) h))
         (cast n q (le_trans (Nat.le_max_right _ _) h))
  | n, .pow p k, h => .pow (cast n p h) k

end SOS.Poly

namespace SOS.Poly

/-- Real-valued denotation of the typed AST under a `Fin n → ℝ` valuation. -/
def evalReal {n : Nat} (φ : Fin n → ℝ) : SOS.Poly n → ℝ
  | .const r   => (r : ℝ)
  | .var i     => φ i
  | .neg p     => -evalReal φ p
  | .add p q   => evalReal φ p + evalReal φ q
  | .sub p q   => evalReal φ p - evalReal φ q
  | .mul p q   => evalReal φ p * evalReal φ q
  | .pow p k   => evalReal φ p ^ k

/-- Lift a `Fin n → ℝ` valuation to a `Nat → ℝ` valuation by extending
with zero on out-of-bound indices. The reifier produces proofs against
`Raw.eval` with a `Nat`-indexed valuation; this is the canonical
extension that lines up with `Poly.evalReal` after casting. -/
def naturalValuation {n : Nat} (φ : Fin n → ℝ) (i : Nat) : ℝ :=
  if h : i < n then φ ⟨i, h⟩ else 0

/-- The crucial reflection theorem: `Raw.eval` under the natural
valuation matches `Poly.evalReal` after casting to the typed form.
Proof is structural induction on `r`; both sides reduce in lockstep. -/
theorem Raw.eval_cast {n : Nat} (r : Raw) (h : r.maxAtomBound ≤ n) (φ : Fin n → ℝ) :
    r.eval (naturalValuation φ) = (r.cast n h).evalReal φ := by
  induction r with
  | const r => rfl
  | var i =>
    simp only [Raw.eval, Raw.cast, evalReal, naturalValuation]
    have hi : i < n := by simp [maxAtomBound] at h; omega
    simp [hi]
  | neg p ih =>
    simp only [Raw.eval, Raw.cast, evalReal]
    rw [ih]
  | add p q ihp ihq =>
    simp only [Raw.eval, Raw.cast, evalReal]
    rw [ihp, ihq]
  | sub p q ihp ihq =>
    simp only [Raw.eval, Raw.cast, evalReal]
    rw [ihp, ihq]
  | mul p q ihp ihq =>
    simp only [Raw.eval, Raw.cast, evalReal]
    rw [ihp, ihq]
  | pow p k ih =>
    simp only [Raw.eval, Raw.cast, evalReal]
    rw [ih]

end SOS.Poly
