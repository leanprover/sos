/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.Expr

namespace SOS

/-- Atom valuation table: a finite ordered list of `Lean.Expr`s that appear
in a reified goal, indexed by ℕ. The interpretation is supplied externally
(see `SOS.Reify` for the build-up and `SOS.Raw` for evaluation). -/
structure AtomTable where
  atoms : Array Lean.Expr := #[]
  deriving Inhabited

namespace AtomTable

def size (t : AtomTable) : Nat := t.atoms.size

def push (t : AtomTable) (e : Lean.Expr) : AtomTable := { t with atoms := t.atoms.push e }

def get? (t : AtomTable) (i : Nat) : Option Lean.Expr := t.atoms[i]?

end AtomTable

end SOS
