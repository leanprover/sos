/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SOS.Certificate
import CompPoly.Multivariate.Operations

namespace SOS.EqElim

open CPoly

variable {n : Nat}

/-- One equality-elimination step, recorded with the system state before
the substitution so certificates can be lifted back exactly. -/
structure ElimStep (n : Nat) where
  targetBefore : CMvPolynomial n ℚ
  gsBefore     : List (CMvPolynomial n ℚ)
  psBefore     : List (CMvPolynomial n ℚ)
  dropIdx      : Nat
  var          : Fin n
  coeff        : ℚ
  rhs          : CMvPolynomial n ℚ

/-- One reconstruction step: either a real substitution, or dropping a
constant-zero equality that arose after earlier substitutions. -/
inductive ReconstructStep (n : Nat) where
  | subst (step : ElimStep n)
  | dropZero (dropIdx : Nat)

/-- Data needed to reconstruct a certificate for the original equality list. -/
abbrev ReconstructMap (n : Nat) := List (ReconstructStep n)

@[inline] private def zeroMono (n : Nat) : CMvMonomial n :=
  ⟨Array.replicate n 0, by simp⟩

private instance : Inhabited (CMvMonomial n) := ⟨zeroMono n⟩

private def unitMono (i : Fin n) : CMvMonomial n :=
  Vector.ofFn (fun j => if j = i then 1 else 0)

private def eraseVarMono (i : Fin n) (m : CMvMonomial n) : CMvMonomial n :=
  Vector.ofFn (fun j => if j = i then 0 else m.get j)

private def powPoly (p : CMvPolynomial n ℚ) : Nat → CMvPolynomial n ℚ
  | 0 => 1
  | k + 1 => p * powPoly p k

private def substMap (i : Fin n) (expr : CMvPolynomial n ℚ) :
    Fin n → CMvPolynomial n ℚ :=
  fun j => if j = i then expr else CMvPolynomial.X j

def substVar (i : Fin n) (expr : CMvPolynomial n ℚ)
    (p : CMvPolynomial n ℚ) : CMvPolynomial n ℚ :=
  CMvPolynomial.bind₁ (substMap i expr) p

/-- Substitute `var := expr` in `p`, also returning the cofactor `q` such
that `p = substVar var expr p + q * (coeff * (X var - expr))`. -/
def substVarWithCof (var : Fin n) (expr : CMvPolynomial n ℚ) (coeff : ℚ)
    (p : CMvPolynomial n ℚ) : CMvPolynomial n ℚ × CMvPolynomial n ℚ := Id.run do
  let subst := substVar var expr p
  let mut cof : CMvPolynomial n ℚ := 0
  for m in p.monomials do
    let k := m.get var
    if k = 0 then
      continue
    let c := p.coeff m
    let base : CMvPolynomial n ℚ := CMvPolynomial.monomial (eraseVarMono var m) (c / coeff)
    let x := CMvPolynomial.X var
    let mut sum : CMvPolynomial n ℚ := 0
    for t in [0:k] do
      sum := sum + powPoly x (k - 1 - t) * powPoly expr t
    cof := cof + base * sum
  return (subst, cof)

private structure Candidate (n : Nat) where
  idx   : Nat
  var   : Fin n
  coeff : ℚ
  rhs   : CMvPolynomial n ℚ
  score : Nat

private def varOccurrenceScore (var : Fin n) (target : CMvPolynomial n ℚ)
    (gs ps : List (CMvPolynomial n ℚ)) : Nat :=
  let targetScore := if 0 < target.degreeOf var then 1 else 0
  let gsScore := gs.foldl (fun acc g => if 0 < g.degreeOf var then acc + 1 else acc) 0
  let psScore := ps.foldl (fun acc p => if 0 < p.degreeOf var then acc + 1 else acc) 0
  targetScore + gsScore + psScore

private def candidatesFor (target : CMvPolynomial n ℚ)
    (gs ps : List (CMvPolynomial n ℚ)) : List (Candidate n) := Id.run do
  let mut out : List (Candidate n) := []
  for idx in [0:ps.length] do
    let p := ps.getD idx 0
    for var in Fin.foldr n (fun i acc => i :: acc) [] do
      if p.degreeOf var = 1 then
        let coeff := p.coeff (unitMono var)
        if coeff != 0 then
          let rest := p - (CMvPolynomial.C coeff) * CMvPolynomial.X var
          if rest.degreeOf var = 0 then
            let rhs := -(CMvPolynomial.C (1 / coeff)) * rest
            let score := varOccurrenceScore var target gs ps
            out := { idx := idx, var := var, coeff := coeff, rhs := rhs, score := score } :: out
  return out.reverse

private def betterCandidate (a b : Candidate n) : Candidate n :=
  if a.score < b.score then a
  else if a.score > b.score then b
  else if a.idx ≤ b.idx then a
  else b

private def chooseCandidate (target : CMvPolynomial n ℚ)
    (gs ps : List (CMvPolynomial n ℚ)) : Option (Candidate n) :=
  match candidatesFor target gs ps with
  | [] => none
  | c :: cs => some (cs.foldl betterCandidate c)

private def findZeroIdx (ps : List (CMvPolynomial n ℚ)) : Option Nat := Id.run do
  for idx in [0:ps.length] do
    if ps.getD idx 1 = 0 then
      return some idx
  return none

private def removeIdx {α : Type*} (xs : List α) (idx : Nat) : List α :=
  (xs.zipIdx.filter (fun pair => pair.2 != idx)).map (fun pair => pair.1)

private def insertIdx {α : Type*} (xs : List α) (idx : Nat) (x : α) : List α :=
  let rec go : Nat → List α → List α
    | _, [] => [x]
    | 0, ys => x :: ys
    | k + 1, y :: ys => y :: go k ys
  go idx xs

private def goalOfTarget (target : CMvPolynomial n ℚ) : Goal n :=
  .closed target

/-- Iteratively eliminate equalities that are linear in a single variable
whose remaining terms do not mention that variable. Returns `none` when no
equality was eliminated. -/
def eliminateEqualities (goal : Goal n)
    (gs : List (CMvPolynomial n ℚ)) (ps : List (CMvPolynomial n ℚ)) :
    Option (Goal n × List (CMvPolynomial n ℚ) × List (CMvPolynomial n ℚ) ×
      ReconstructMap n) := Id.run do
  if ps.isEmpty then return none
  let mut target := goal.target
  let mut gs := gs
  let mut ps := ps
  let mut steps : ReconstructMap n := []
  let mut changed := false
  while true do
    if let some idx := findZeroIdx ps then
      ps := removeIdx ps idx
      steps := ReconstructStep.dropZero idx :: steps
      changed := true
    else
      let some cand := chooseCandidate target gs ps | break
      let step : ElimStep n :=
        { targetBefore := target, gsBefore := gs, psBefore := ps,
          dropIdx := cand.idx, var := cand.var, coeff := cand.coeff, rhs := cand.rhs }
      target := substVar cand.var cand.rhs target
      gs := gs.map (substVar cand.var cand.rhs)
      ps := (removeIdx ps cand.idx).map (substVar cand.var cand.rhs)
      steps := ReconstructStep.subst step :: steps
      changed := true
  if changed then
    return some (goalOfTarget target, gs, ps, steps.reverse)
  return none

private def liftStep (step : ElimStep n) (cert : Certificate n) : Certificate n :=
  let (_, targetCof) := substVarWithCof step.var step.rhs step.coeff step.targetBefore
  let monoidCof :=
    cert.sigmas.foldl
      (fun acc pair =>
        let term := pair.2.toPoly * Certificate.constraintProduct step.gsBefore pair.1
        let (_, cof) := substVarWithCof step.var step.rhs step.coeff term
        acc + cof)
      0
  let remainingPs := removeIdx step.psBefore step.dropIdx
  let eqCof :=
    (cert.eqCofs.zip remainingPs).foldl
      (fun acc pair =>
        let term := pair.1 * pair.2
        let (_, cof) := substVarWithCof step.var step.rhs step.coeff term
        acc + cof)
      0
  let eliminated := targetCof - monoidCof - eqCof
  { cert with eqCofs := insertIdx cert.eqCofs step.dropIdx eliminated }

/-- Lift a certificate produced after equality elimination back over the
original variables and equality list. -/
def reconstructCertificate (map : ReconstructMap n) (cert : Certificate n) :
    Certificate n :=
  map.reverse.foldl
    (fun c step =>
      match step with
      | .subst step => liftStep step c
      | .dropZero idx => { c with eqCofs := insertIdx c.eqCofs idx 0 })
    cert

end SOS.EqElim
