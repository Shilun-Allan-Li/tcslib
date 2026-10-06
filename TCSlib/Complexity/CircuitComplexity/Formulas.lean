/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Data.Nat.Notation

/-!
# Literals, Literal Lists, and DNF/CNF Formulas

`Literal` / `LitList` / `Depth2`: the flat formula syntax used by the switching
lemma, and `DNF` / `CNF`: its two readings.  A `LitList` is read as a `Term`
(conjunction) or a `Clause` (disjunction); a `Depth2` shape is wrapped as a
`DNF` (OR of terms) or a `CNF` (AND of clauses).  The wrappers are distinct
structures, so a CNF cannot be passed where a DNF is expected without an
explicit conversion (`CNF.dual`, `DNF.dual`).  `width` is reading-independent
and is the bottom-layer fan-in that the switching lemma is parameterized by.

These are independent of `TCSlib.Complexity.CircuitComplexity.Basic`; the bridge
between the two lives in `TCSlib.BooleanAnalysis.LMN.NormalFormConversion`.

## Main definitions

* `Literal`, `LitList`, `Depth2` — reading-neutral syntax, with
  `LitList.width` and `Depth2.width`.
* `Term`, `Clause` — a `LitList` read as AND / OR, with `Term.eval`,
  `Clause.eval`.
* `DNF`, `CNF` — structures wrapping the term / clause list, with `width` and
  `eval`.

## Main results

None; this file is definitions only.

## Divergences from [OD14, §4.1]

A `LitList` is a plain list, so it may hold both a variable and its negation, which
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

/-! ## Literals, literal lists, and DNF/CNF formulas -/

/-- A literal: variable `var : Fin n` with polarity `neg` (true = negated literal).
[OD14, Def 4.1] -/
structure Literal (n : ℕ) where
  var : Fin n
  neg : Bool
  deriving DecidableEq

/-- Evaluate literal `l` on input `x`: positive literal returns `x i`, negated returns `¬(x i)`. -/
def Literal.eval {n : ℕ} (l : Literal n) (x : Fin n → Bool) : Bool :=
  if l.neg then !x l.var else x l.var

/-- A finite list of literals, with no AND/OR reading attached: the common
syntax of a term (read as a conjunction) and a clause (read as a disjunction). -/
abbrev LitList (n : ℕ) := List (Literal n)

/-- Width of a literal list (number of literals); reading-independent.
[OD14, Def 4.1] -/
def LitList.width {n : ℕ} (t : LitList n) : ℕ := t.length

/-- A term: a literal list read as a conjunction.  [OD14, Def 4.1] -/
abbrev Term (n : ℕ) := LitList n

/-- A clause: a literal list read as a disjunction.  [OD14, Def 4.4] -/
abbrev Clause (n : ℕ) := LitList n

/-- Evaluate term `t` as a conjunction: all literals must hold. -/
def Term.eval {n : ℕ} (t : Term n) (x : Fin n → Bool) : Bool :=
  t.all (fun l => l.eval x)

/-- Evaluate clause `c` as a disjunction: some literal must hold. -/
def Clause.eval {n : ℕ} (c : Clause n) (x : Fin n → Bool) : Bool :=
  c.any (fun l => l.eval x)

/-- A depth-2 formula shape: a list of literal lists, with no reading fixed.
`DNF` and `CNF` wrap it with their two readings; `width` does not depend on the
reading. -/
abbrev Depth2 (n : ℕ) := List (LitList n)

/-- Width of a depth-2 shape (maximum inner width; 0 for empty).  [OD14, Def 4.3] -/
def Depth2.width {n : ℕ} (F : Depth2 n) : ℕ := (F.map LitList.width).foldr max 0

/-- A DNF formula: a depth-2 shape read as a disjunction of terms.
[OD14, Def 4.1] -/
structure DNF (n : ℕ) where
  /-- The terms of the DNF, read as conjunctions. -/
  terms : List (Term n)
  deriving Inhabited

/-- A CNF formula: a depth-2 shape read as a conjunction of clauses.
[OD14, Def 4.4] -/
structure CNF (n : ℕ) where
  /-- The clauses of the CNF, read as disjunctions. -/
  clauses : List (Clause n)
  deriving Inhabited

/-- Width of a DNF formula (maximum term width; 0 for empty).  [OD14, Def 4.3] -/
def DNF.width {n : ℕ} (d : DNF n) : ℕ := Depth2.width d.terms

/-- Evaluate DNF `d`: at least one term must hold. -/
def DNF.eval {n : ℕ} (d : DNF n) (x : Fin n → Bool) : Bool :=
  d.terms.any (fun t => Term.eval t x)

/-- Width of a CNF formula (maximum clause width).  [OD14, Def 4.4] -/
def CNF.width {n : ℕ} (c : CNF n) : ℕ := Depth2.width c.clauses

/-- Evaluate CNF `c`: all clauses must hold. -/
def CNF.eval {n : ℕ} (c : CNF n) (x : Fin n → Bool) : Bool :=
  c.clauses.all (fun c => Clause.eval c x)

/-! ### Evaluation simp lemmas -/

/-- The empty term (empty conjunction) evaluates to `true` on every input. -/
@[simp] theorem Term.eval_nil {n : ℕ} (x : Fin n → Bool) : Term.eval [] x = true := rfl

/-- A term `l :: t` holds exactly when the literal `l` holds and the rest `t` holds. -/
@[simp] theorem Term.eval_cons {n : ℕ} (l : Literal n) (t : Term n) (x : Fin n → Bool) :
    Term.eval (l :: t) x = (l.eval x && Term.eval t x) := rfl

/-- The empty clause (empty disjunction) evaluates to `false` on every input. -/
@[simp] theorem Clause.eval_nil {n : ℕ} (x : Fin n → Bool) : Clause.eval [] x = false := rfl

/-- A clause `l :: c` holds exactly when the literal `l` holds or the rest `c` holds. -/
@[simp] theorem Clause.eval_cons {n : ℕ} (l : Literal n) (c : Clause n) (x : Fin n → Bool) :
    Clause.eval (l :: c) x = (l.eval x || Clause.eval c x) := rfl

/-- The DNF with term list `ts` evaluates to `true` iff some term of `ts` holds. -/
@[simp] theorem DNF.eval_mk {n : ℕ} (ts : List (Term n)) (x : Fin n → Bool) :
    (DNF.mk ts).eval x = ts.any (fun t => Term.eval t x) := rfl

/-- The CNF with clause list `cs` evaluates to `true` iff every clause of `cs` holds. -/
@[simp] theorem CNF.eval_mk {n : ℕ} (cs : List (Clause n)) (x : Fin n → Bool) :
    (CNF.mk cs).eval x = cs.all (fun c => Clause.eval c x) := rfl

/-- The width of the DNF with term list `ts` is the depth-2 width of `ts` (its maximum term
width). -/
@[simp] theorem DNF.width_mk {n : ℕ} (ts : List (Term n)) :
    (DNF.mk ts).width = Depth2.width ts := rfl

/-- The width of the CNF with clause list `cs` is the depth-2 width of `cs` (its maximum
clause width). -/
@[simp] theorem CNF.width_mk {n : ℕ} (cs : List (Clause n)) :
    (CNF.mk cs).width = Depth2.width cs := rfl
