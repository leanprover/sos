/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Test cases for the ℕ/ℤ DIV/MOD enrichment of the integer frontend
(issues #24 and #45). Each goal contains `a / b` or `a % b` over ℕ
or ℤ; the lift pre-pass introduces witness equalities and bounds
before the SOS reifier runs. The leading block covers positive
literal divisors (issue #24); the trailing block (after the
non-literal-divisor section header) covers divisors whose positivity
is derived from in-scope hypotheses via `omega` (issue #45).
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

-- Non-literal divisor with no positivity hypothesis in scope: the
-- unconditional witnesses (`n · (m/n) + m%n = m` and `m%n ≥ 0`) are
-- still introduced, but the strict bound `m%n < n` is skipped because
-- `omega` can't prove `0 < n`. The goal `m / n ≤ m` is false at the
-- real point `n := 0, m := 0, m/n := 1, m%n := 0` (consistent with
-- the unconditional witnesses), so the search correctly fails.
example : True := by
  fail_if_success
    (have : ∀ m n : ℕ, m / n ≤ m := by sos)
  trivial

/-! ### Non-literal divisor enrichment (issue #45)

When the divisor is not a positive literal, `enrichDivMod` introduces
the unconditional div/mod identity and remainder ≥ 0 witnesses, and
routes the strict bound `r < n` through `omega` on the divisor
positivity (over the source domain). Sites whose positivity is
derivable from the local context — a `n ≠ 0` / `0 < n` / `m < n`
hypothesis — get the full witness suite; sites whose positivity isn't
provable get only the unconditional facts. The omega-derived `0 < n`
is local to the `by` block: it's used to discharge `Nat.mod_lt` /
`Int.emod_lt_of_pos`, not added as a separate ℝ-cast hypothesis.

Harrison's `sos.ml:1729` lands directly on the unconditional ℕ path
(no positivity hypothesis needed). The remaining `:1726`, `:1727`,
`:1730`, `:1731` examples enrich correctly but their natural
certificates require products of inequality constraints (e.g.
`n · (m/n) ≥ 0` derived from `n ≥ 0 ∧ m/n ≥ 0`), which is a
Schmüdgen-preordering certificate rather than a Putinar one — out of
scope until #38 lands. See the FIXME blocks below for the per-case
diagnoses. -/

-- sos.ml:1729 — `n · (m / n) ≤ m`. Holds unconditionally over ℕ:
-- `n · (m/n) = m - m%n ≤ m`. The unconditional witnesses (div/mod
-- identity and `0 ≤ m%n`) give a direct Putinar cert.
example : ∀ m n : ℕ, n * (m / n) ≤ m := by sos

-- ℤ companion: with `0 < n` in scope, `omega` discharges the
-- divisor-positivity sides of `Int.emod_nonneg` / `Int.emod_lt_of_pos`
-- and the same cert closes the goal.
example : ∀ m n : ℤ, 0 < n → n * (m / n) ≤ m := by sos

-- Focused tests for the optional positivity-guarded witnesses.
-- Each one directly exercises the `omega`-derived bound that
-- `enrichSite` adds for non-literal divisors and would silently
-- regress if the soft-failed witness intros stopped firing.

-- ℕ strict bound from `n ≠ 0`: the witness `0 ≤ n - (m%n) - 1` is
-- precisely what's needed (the rest is `Nat.cast_lt` on the
-- conclusion).
example : ∀ m n : ℕ, n ≠ 0 → m % n < n := by sos

-- ℤ remainder ≥ 0 from `n ≠ 0`: directly the `hnn` witness.
example : ∀ m n : ℤ, n ≠ 0 → 0 ≤ m % n := by sos

-- ℤ strict bound from `0 < n`: directly the `hgap` witness.
example : ∀ m n : ℤ, 0 < n → m % n < n := by sos

-- FIXME sos.ml:1726 — `n ≠ 0 ⇒ 0 % n = 0`. With the strict bound
-- `n - (0%n) - 1 ≥ 0` in scope the cert needs `n · (0/n) ≥ 0`, a
-- product of two non-negative atoms, which Putinar can't form
-- without Schmüdgen preordering (#38).
-- example : ∀ n : ℕ, n ≠ 0 → 0 % n = 0 := by sos

-- FIXME sos.ml:1730 — `n ≠ 0 ⇒ 0 / n = 0`. Same preordering
-- obstruction as 1726.
-- example : ∀ n : ℕ, n ≠ 0 → 0 / n = 0 := by sos

-- FIXME sos.ml:1727 — `m < n ⇒ m / n = 0`. Refute path turns it
-- into `m/n ≥ 1 ∧ m + 1 ≤ n ⇒ False`, which needs the multiplicative
-- step `n · (m/n) ≥ n` (i.e. constraint product `n · (m/n - 1) ≥ 0`).
-- example : ∀ m n : ℕ, m < n → m / n = 0 := by sos

-- FIXME sos.ml:1731 — `p ≠ 0 ∧ m ≤ n ⇒ m / p ≤ n / p`. Two DIV
-- sites with the same non-literal divisor `p`; both get the full
-- witness suite from `omega`. The natural refutation chains
-- `p · (m/p - n/p - 1) ≥ p` against `m - n ≤ 0`, again a Schmüdgen
-- product.
-- example : ∀ m n p : ℕ, p ≠ 0 → m ≤ n → m / p ≤ n / p := by sos

