/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Tactic surface: `sos` (search-driven) and `sos_witness` (literal-cert).

**v0 status.** The `sos` tactic and the `sos_witness` term-syntax tactic
are declared at the syntax level only. The elaborators are TODO; until
`Sos/Reify.lean` provides `parseGoal` (Lean.Expr → typed `Poly n` AST
with valuation theorems) the tactics fall through to `throwError`.

The verifier core (`Sos/Verifier.lean`) is independently usable: a user
can construct a `Sos.Certificate n` value by hand and invoke
`Sos.sos_sound` / `Sos.sos_strict_sound` / `Sos.sos_infeasible_sound`
directly to close goals. Once the elaborators are written, those
soundness theorems become the engine `sos_witness` calls into.
-/
import Sos.Reify
import Sos.Search
import Lean.Elab.Tactic

namespace Sos

open Lean Elab Tactic Meta

/-- The search-driven tactic. -/
syntax (name := sosTactic) "sos" : tactic

/-- The literal-certificate tactic. The argument is a `Sos.Certificate n`
expression; the tactic refines via the appropriate `sos_*_sound`
lemma and discharges `Certificate.checks goal gs = true` with
`cbv_decide`. -/
syntax (name := sosWitnessTactic) "sos_witness " term : tactic

/-! ### v0 elaborator stubs -/

elab_rules : tactic
  | `(tactic| sos) => do
    throwError "sos: tactic surface not yet implemented (search backend stubbed; \
                see PLAN.md for roadmap). Use `sos_witness <cert>` to validate \
                a literal certificate via the verifier core."

elab_rules : tactic
  | `(tactic| sos_witness $_cert:term) => do
    throwError "sos_witness: tactic surface not yet implemented. \
                Apply Sos.sos_sound (or sos_strict_sound / sos_infeasible_sound) \
                directly until reification lands."

end Sos
