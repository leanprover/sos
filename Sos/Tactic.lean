/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Tactic surface: `sos` (search-driven) and `sos_witness` (literal-cert).

**v0.1 status.** The verifier core (`Sos.Verifier`) is complete with
no holes. The search engine (`Sos.Search.runSearch`) is end-to-end
operational — `sos-example` calls CSDP and produces a verified
`Certificate` for `(x 0)² + 1 ≥ 0`.

The tactic-surface elaborators wrapping these into `by sos` / `by
sos_witness <cert>` need a non-trivial bridge that v0.1 does not
provide:

- **For `sos_witness <cert>`**: the user supplies a literal
  `Certificate n` term. The elaborator must reify the goal,
  `elabTerm` the cert against `Certificate n`, then refine via
  `sos_sound` with `cert.checks goal gs = true` discharged by
  `cbv_decide`. The remaining gap is a `simp`-driven rewrite from
  the user's original `0 ≤ <expr>` goal to `0 ≤ aeval x p` where
  `p` is the reified polynomial. CompPoly's `@[simp] aeval_C / X /
  add / mul` lemmas make this discharge tractable but the proof
  construction needs careful threading.

- **For `sos`**: same path, plus a `Lean.ToExpr` instance for
  `Certificate n` so the search-produced certificate can be
  embedded in the proof term. CompPoly's `CMvPolynomial n ℚ` is a
  `Lawful` subtype of an `ExtTreeMap` quotient; building a `ToExpr`
  instance requires walking the polynomial via `monomials` and
  emitting a normalised constructor expression. ~100-150 lines.

Both are deferred to v0.2. Until then, users can:
1. Apply `Sos.sos_sound` (or its strict / infeasibility variants)
   directly with a hand-constructed `Certificate`.
2. Use `Sos.Search.runSearch` programmatically (`#eval` / `IO`) to
   discover certificates for goals.

See `Sos/Examples.lean` for a worked end-to-end demonstration.
-/
import Sos.Reify
import Sos.Search
import Lean.Elab.Tactic

namespace Sos

open Lean Elab Tactic Meta

syntax (name := sosTactic) "sos" : tactic
syntax (name := sosWitnessTactic) "sos_witness " term : tactic

elab_rules : tactic
  | `(tactic| sos) => do
    throwError "sos: tactic surface is v0.2 work (see Sos/Tactic.lean header). \
                Use `Sos.Search.runSearch` programmatically + apply `Sos.sos_sound` \
                with the resulting certificate; see `Sos/Examples.lean`."

elab_rules : tactic
  | `(tactic| sos_witness $_cert:term) => do
    throwError "sos_witness: tactic surface is v0.2 work (see Sos/Tactic.lean header). \
                Apply `Sos.sos_sound` (or sos_strict_sound / sos_infeasible_sound) \
                directly with your literal certificate."

end Sos
