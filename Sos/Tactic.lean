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
import Mathlib.Tactic.Ring

namespace Sos

open Lean Elab Tactic Meta

/-! ### `Sos.Poly n` → `Lean.Expr` -/

/-- Build a `Lean.Expr` denoting the given `Sos.Poly n` value. The
output is a tree of `Sos.Poly.{const,var,neg,add,sub,mul,pow}`
applications with `n` left as a `Nat` literal at every position. The
outermost `n` argument therefore matches the polynomial's static type
`Sos.Poly n`. -/
partial def Poly.toExprImpl {n : Nat} (p : Sos.Poly n) : Lean.Expr :=
  let nE : Expr := Lean.mkNatLit n
  match p with
  | .const r => mkApp2 (.const ``Sos.Poly.const []) nE (Lean.toExpr r)
  | .var i   => mkApp2 (.const ``Sos.Poly.var []) nE (Lean.toExpr i)
  | .neg p'  => mkApp2 (.const ``Sos.Poly.neg []) nE p'.toExprImpl
  | .add p' q => mkApp3 (.const ``Sos.Poly.add []) nE p'.toExprImpl q.toExprImpl
  | .sub p' q => mkApp3 (.const ``Sos.Poly.sub []) nE p'.toExprImpl q.toExprImpl
  | .mul p' q => mkApp3 (.const ``Sos.Poly.mul []) nE p'.toExprImpl q.toExprImpl
  | .pow p' k => mkApp3 (.const ``Sos.Poly.pow []) nE p'.toExprImpl (Lean.mkNatLit k)

instance Poly.instToExpr (n : Nat) : Lean.ToExpr (Sos.Poly n) where
  toExpr := Poly.toExprImpl
  toTypeExpr := Lean.mkApp (.const ``Sos.Poly []) (Lean.mkNatLit n)

/-! ### Decompiling `CMvPolynomial n ℚ` to `Sos.Poly n` -/

/-- Build the AST for a single monomial `c · Πᵢ xᵢ^(eᵢ)` from a coefficient
`c : ℚ` and exponent vector `mono : CMvMonomial n` (= `Vector ℕ n`). -/
def Poly.ofMonomial {n : Nat} (c : Rat) (mono : CPoly.CMvMonomial n) : Sos.Poly n :=
  Fin.foldr n (init := Sos.Poly.const c) fun i acc =>
    let e := mono[i]
    if e = 0 then acc
    else Sos.Poly.mul acc (Sos.Poly.pow (Sos.Poly.var i) e)

/-- Decompile a `CMvPolynomial n ℚ` value into a `Sos.Poly n` AST,
walking the monomial map and emitting `c · Πᵢ xᵢ^eᵢ` for each nonzero
term. The resulting AST has `toCMv = id` modulo polynomial equality;
Lawful normalisation guarantees the round-trip on the
search-produced squares we care about. -/
def Poly.decompile {n : Nat} (p : CPoly.CMvPolynomial n ℚ) : Sos.Poly n :=
  p.1.toList.foldr
    (fun (term : CPoly.CMvMonomial n × ℚ) (acc : Sos.Poly n) =>
      Sos.Poly.add acc (Poly.ofMonomial term.2 term.1))
    (Sos.Poly.const 0)

/-! ### Tactic stubs (filled in by later tasks) -/

syntax (name := sosTactic) "sos" : tactic
syntax (name := sosWitnessTactic) "sos_witness " term : tactic

elab_rules : tactic
  | `(tactic| sos) => throwError "sos: not yet implemented"

elab_rules : tactic
  | `(tactic| sos_witness $_cert:term) => throwError "sos_witness: not yet implemented"

end Sos
