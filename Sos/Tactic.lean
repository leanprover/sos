/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

`sos` and `sos_witness` tactic surface.
-/
import Sos.Reify
import Sos.Search
import Sos.Verifier
import Lean.ToExpr
import Lean.Elab.Tactic

namespace Sos

open Lean Elab Tactic Meta

syntax (name := sosTactic) "sos" : tactic
syntax (name := sosWitnessTactic) "sos_witness " term : tactic

elab_rules : tactic
  | `(tactic| sos) => throwError "sos: not yet implemented"

elab_rules : tactic
  | `(tactic| sos_witness $_cert:term) => throwError "sos_witness: not yet implemented"

end Sos
