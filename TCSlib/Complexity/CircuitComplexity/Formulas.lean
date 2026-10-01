/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Data.Nat.Notation

/-!
# Literals, Terms, and DNF/CNF Formulas

`Literal` / `Term` / `DNF` / `CNF`: the flat formula representations used by the
switching lemma, with their `eval` and `width` measures.  `width` is the
bottom-layer fan-in that the switching lemma is parameterized by.

These are independent of `TCSlib.Complexity.CircuitComplexity.Basic`; the bridge
between the two lives in `TCSlib.BooleanAnalysis.LMN.NormalFormConversion`.

## Main definitions

* `Literal`, `Term`, `DNF`, `CNF` — the formula types, with `Term.width`,
  `DNF.width`, `CNF.width` and the `eval` semantics of each.

## Main results

None; this file is definitions only.

## Divergences from [OD14, §4.1]

A `Term` is a plain list, so it may hold both a variable and its negation, which
[OD14, Def 4.1] forbids; the development imposes `Nodup` only where it needs it,
at the base clauses of `Basic.lean`'s normal-form circuits.  [OD14, Def 4.3] also
gives a formula a *size*, its number of terms; no size measure is defined here.
Split out of `TCSlib/BooleanAnalysis/Switching/Circuit.lean` (commit 94fd7c6),
which carried no copyright header; `Authors` above is that file's git author.

## References

* [OD14] R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University
  Press, 2014.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-! ## Literals, Terms, and DNF/CNF formulas -/

/-- A literal: variable `var : Fin n` with polarity `neg` (true = negated literal).
[OD14, Def 4.1] -/
structure Literal (n : ℕ) where
  var : Fin n
  neg : Bool
  deriving DecidableEq

/-- Evaluate literal `l` on input `x`: positive literal returns `x i`, negated returns `¬(x i)`. -/
def Literal.eval {n : ℕ} (l : Literal n) (x : Fin n → Bool) : Bool :=
  if l.neg then !x l.var else x l.var

/-- A term is a conjunction of literals.  [OD14, Def 4.1] -/
abbrev Term (n : ℕ) := List (Literal n)

/-- Width of a term (number of literals).  [OD14, Def 4.1] -/
def Term.width {n : ℕ} (t : Term n) : ℕ := t.length

/-- Evaluate term `t` as a conjunction: all literals must hold. -/
def Term.eval {n : ℕ} (t : Term n) (x : Fin n → Bool) : Bool :=
  t.all (fun l => l.eval x)

/-- A DNF formula is a disjunction of terms.  [OD14, Def 4.1] -/
abbrev DNF (n : ℕ) := List (Term n)

/-- Width of a DNF formula (maximum term width; 0 for empty).  [OD14, Def 4.3] -/
def DNF.width {n : ℕ} (d : DNF n) : ℕ := (d.map Term.width).foldr max 0

/-- Evaluate DNF `d`: at least one term must hold. -/
def DNF.eval {n : ℕ} (d : DNF n) (x : Fin n → Bool) : Bool :=
  d.any (fun t => t.eval x)

/-- A CNF formula is a conjunction of clauses, each a disjunction of literals.
[OD14, Def 4.4] -/
abbrev CNF (n : ℕ) := List (Term n)

/-- Width of a CNF formula (maximum clause width).  [OD14, Def 4.4] -/
def CNF.width {n : ℕ} (c : CNF n) : ℕ := (c.map Term.width).foldr max 0

/-- Evaluate a single clause as a disjunction: some literal must hold. -/
def CNF.evalClause {n : ℕ} (t : Term n) (x : Fin n → Bool) : Bool :=
  t.any (fun l => l.eval x)

/-- Evaluate CNF `c`: all clauses must hold. -/
def CNF.eval {n : ℕ} (c : CNF n) (x : Fin n → Bool) : Bool :=
  c.all (fun t => CNF.evalClause t x)
