/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Logic.Function.Basic
import TCSlib.Complexity.Formulas.CNF

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Quantified Boolean formulas (prenex, CNF matrix)

[AB09, §4.2, Definition 4.10]: a quantified Boolean formula is
`Q₁x₁ Q₂x₂ … Qₙxₙ φ(x₁, …, xₙ)` with each `Qᵢ` one of `∀`/`∃`, the variables
ranging over `{0, 1}`, and `φ` a plain Boolean formula. Phase P4.3 of
`AroraBarakChapters3-4Plan.md`; the campaign carrier per decision CH34-Q5:
**prenex form with a CNF matrix**, reusing the chapter-2 carrier
(`Std.Sat.CNF ℕ`, `TCSlib.Complexity.Formulas.CNF`).

## Divergences from [AB09] (each deliberate, recorded for the audit)

* **CNF matrix.** Definition 4.10 allows an arbitrary unquantified matrix and
  notes (p. 83) that restricting to 3CNF is harmless via auxiliary variables.
  The campaign takes the CNF restriction *as the carrier* (decision CH34-Q5):
  `TQBF`'s hardness pays the Tseitin step inside its reduction, and a
  general-formula carrier remains future work (`backlog.md`, general Boolean
  formulas).
* **Prenex by construction**: the quantifier prefix is a `List`, the matrix
  follows; non-prenex formulas are out of scope (the book converts to prenex
  in polynomial time, p. 83 — not formalized here).
* **Free variables read `false`.** Quantifier `i` binds variable `i` (the
  prefix binds an initial segment of `ℕ`); matrix variables at or beyond the
  prefix length are unbound and evaluate at the all-`false` base assignment.
  [AB09] considers only closed formulas; this totalization (in the spirit of
  the chapter-2 `codeFallback` conventions) makes `QBF.truth` total without a
  well-formedness side condition, and well-formed consumers never rely on it.

## Main definitions

* `Complexity.QBF.Quant`, `Complexity.QBF` — the prefix alphabet and the
  formula. [AB09, Definition 4.10]
* `Complexity.QBF.truth` — the truth value, by recursion on the prefix.
  [AB09, Definition 4.10 and Example 4.11]

## Main results (sorried; phase-P4.3 statement)

* `Complexity.QBF.truth_exPrefix_iff_satisfiable` — an all-`∃` prefix covering
  the matrix's variables renders exactly satisfiability: the `SAT` embedding
  of [AB09, Example 4.12].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.2, Definitions 4.9-4.10, Examples
  4.11-4.12.)
-/

namespace Complexity

open Std.Sat (CNF)

namespace QBF

/-- A quantifier of the prenex prefix. [AB09, Definition 4.10] -/
inductive Quant where
  /-- the existential quantifier `∃` -/
  | ex
  /-- the universal quantifier `∀` -/
  | all
deriving DecidableEq

end QBF

/-- A prenex quantified Boolean formula with CNF matrix: the quantifier
prefix (quantifier `i` binds variable `i`) and the matrix. Matrix variables
beyond the prefix length are free and read `false` under `QBF.truth` (see the
divergences list). [AB09, Definition 4.10, with decision CH34-Q5's CNF
restriction] -/
structure QBF where
  /-- the prenex quantifier prefix; entry `i` binds variable `i` -/
  quants : List QBF.Quant
  /-- the CNF matrix over the chapter-2 carrier -/
  matrix : CNF ℕ

namespace QBF

/-- Truth of the matrix `m` under the remaining prefix, the partial
assignment built so far, and the next variable index: the recursion of
[AB09, Definition 4.10]'s semantics ("∀ and ∃ have their standard meaning"),
peeling one quantifier per step. -/
def truthAux (m : CNF ℕ) : List Quant → (ℕ → Bool) → ℕ → Prop
  | [], σ, _ => m.eval σ = true
  | .ex :: qs, σ, i => ∃ b : Bool, truthAux m qs (Function.update σ i b) (i + 1)
  | .all :: qs, σ, i => ∀ b : Bool, truthAux m qs (Function.update σ i b) (i + 1)

/-- **The truth value of a QBF** [AB09, Definition 4.10]: peel the prefix
from variable `0`, starting at the all-`false` base assignment (free
variables read `false`; see the divergences list). Since every prefix
variable is bound, a closed formula's truth is assignment-independent. -/
def truth (Q : QBF) : Prop :=
  truthAux Q.matrix Q.quants (fun _ => false) 0

/-- **The `SAT` embedding** ([AB09, Example 4.12]; spec, fill pending —
phase P4.3): under an all-`∃` prefix covering every matrix variable, truth
is exactly satisfiability of the matrix.

**Proof sketch.** Forward: the recursion's witnesses assemble an assignment
on `[0, n)` under which the matrix evaluates `true`; variables `≥ n` carry
the base `false`, and `Std.Sat.CNF.eval_congr_of_lt_numVars` (chapter 2)
transports evaluation to the assembled assignment. Backward: given a
satisfying `σ`, choose the witness `σ i` at step `i`; after `n` updates the
built assignment agrees with `σ` below `numVars m ≤ n`, and
`eval_congr_of_lt_numVars` closes. Fill obligations: the update-prefix
agreement lemma (`Function.update` accumulation agrees with `σ` on the
consumed segment) and the two inductions. -/
theorem truth_exPrefix_iff_satisfiable (m : CNF ℕ) (n : ℕ) (hn : m.numVars ≤ n) :
    QBF.truth ⟨List.replicate n .ex, m⟩ ↔ m.Satisfiable := by
  sorry

end QBF

end Complexity
