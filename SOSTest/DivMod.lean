/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Test cases for the ℕ/ℤ DIV/MOD enrichment of the integer frontend
(issue #24). Each goal contains `a / b` or `a % b` over ℕ or ℤ with
positive literal divisor; the lift pre-pass introduces witness
equalities and bounds before the SOS reifier runs.
-/
import SOS

-- Trivial ℕ div lower bound: `n / 2 + n / 2 ≤ n` follows from
-- `n = 2 * (n / 2) + n % 2` and `0 ≤ n % 2`.
example : ∀ n : ℕ, n / 2 + n / 2 ≤ n := by sos

-- Trivial ℕ mod upper bound: `n % 3 ≤ 2` follows from `n % 3 + 1 ≤ 3`.
example : ∀ n : ℕ, n % 3 ≤ 2 := by sos

-- ℕ div+mod identity: `2 * (n / 2) + n % 2 = n` is the witness itself.
example : ∀ n : ℕ, 2 * (n / 2) + n % 2 = n := by sos

-- ℤ remainder nonneg under ediv (the default `/` on ℤ).
example : ∀ n : ℤ, 0 ≤ n % 3 := by sos

-- ℤ remainder bound: `n % 5 ≤ 4`.
example : ∀ n : ℤ, n % 5 ≤ 4 := by sos

-- ℤ div+mod identity with sign-invariant statement.
example : ∀ n : ℤ, 2 * (n / 2) + n % 2 = n := by sos

-- `n / 2 ≤ n` over ℕ (the witness `n = 2*(n/2) + n%2` and `0 ≤ n%2`
-- give `n/2 ≤ n/2 + (n/2 + n%2) = n`).
example : ∀ n : ℕ, n / 2 ≤ n := by sos

-- Tight: `3 * (n / 3) ≤ n`.
example : ∀ n : ℕ, 3 * (n / 3) ≤ n := by sos

-- ℤ goal with a non-negativity precondition.
example : ∀ n : ℤ, 0 ≤ n → 2 * (n / 2) ≤ n := by sos

-- Larger divisor literal: `n / 7 + n / 7 ≤ n` (the search treats
-- `n/7` as an atom `q`; from `n = 7q + r` and `0 ≤ r` it gets
-- `2q ≤ 2q + 5q + r = n` requiring `5q ≥ 0`, which follows from
-- `0 ≤ q` introduced by `assertNatCastNonneg`).
example : ∀ n : ℕ, n / 7 + n / 7 ≤ n := by sos

-- Two distinct sites (different divisor literals) on the same `n`:
-- both `n / 2` and `n / 3` need witnesses, with non-shadowing names.
example : ∀ n : ℕ, 2 * (n / 2) ≤ n ∧ 3 * (n / 3) ≤ n → True := by
  intro _ _; trivial

-- Both divisor literals as distinct atoms in the conclusion.
example : ∀ n : ℕ, n / 2 + n / 3 ≤ n + n := by sos

-- DIV/MOD in a `0 ≤ …`-shape hypothesis is enriched too (the lift
-- scans hypothesis types in addition to the conclusion). Trivial
-- consequence of `0 ≤ n / 2` plus the witness `n = 2 * (n/2) + n%2`.
example : ∀ n : ℕ, 0 ≤ n / 2 → 0 ≤ n / 2 + n / 2 + n / 2 := by sos

-- Equality conclusion `liftToReal` splits via `le_antisymm` and
-- recurses on each ≤-subgoal; the second entry into `enrichDivMod`
-- must NOT re-enrich the same site by rediscovering its own
-- previously-introduced witness hypotheses.
example : ∀ n : ℕ, n % 2 + 2 * (n / 2) = n := by sos

-- Non-literal divisor remains an opaque atom — the witness equality
-- isn't introduced because the divisor isn't a positive literal, so
-- the search has nothing to certify against and the tactic fails.
-- The error path is intentionally a search failure, not a hard
-- precondition rejection, so the user can still write the dividend
-- as a literal expression at the call site if needed.
example : True := by
  fail_if_success
    (have : ∀ m n : ℕ, m / n ≤ m := by sos)
  trivial

