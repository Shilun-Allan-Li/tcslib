/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.Formulas.CNF

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The DNF reading and the De Morgan dual

[AB09, §2.6.1, Example 2.21] negates the Cook-Levin CNF formula `φ_x` and asks
whether `¬φ_x` is a tautology; the negation of a CNF is a **DNF** — an OR of
ANDs of literals. This module supplies the minimal dual layer that renders
that argument: a DNF *evaluation* of the existing carrier, the literal-negating
dual map, and the De Morgan bridge between satisfiability and dual tautology.

## Design and deviations from [AB09]

* **A DNF is the same syntax read dually, not a new type**: a list of lists of
  literals evaluated as an OR of ANDs (`Std.Sat.CNF.evalDNF`), on the same
  carrier `Std.Sat.CNF ℕ` and therefore with the same audited serialization
  (`Std.Sat.CNF.serialize`/`decode`). This is deliberate and documented — the
  phase-3 round-1 audit's guidance (finding 7): the DNF rendering is presented
  **as a fragment**, never silently identified with [AB09]'s general Boolean
  formulas; the fragment is exactly what Example 2.21's reduction produces,
  and `TAUTOLOGY` over it carries the example's full mathematical content
  (`TCSlib.Complexity.ClassNP.Tautology`).
* **The dual map negates every literal in place**:
  `¬(⋀_i ⋁_j v_ij) = ⋁_i ⋀_j ¬v_ij` — same list shape, each polarity bit
  flipped. No distributive expansion occurs anywhere (which would be
  exponential); the dual is size-preserving.
* Under the DNF reading the conventions dualize: the empty formula evaluates
  `false` (empty OR) and an empty clause evaluates `true` (empty AND) — the
  exact mirror of the CNF conventions.

## Main definitions

* `Std.Sat.CNF.evalDNF` — the OR-of-ANDs evaluation of the carrier.
  [AB09, §2.6.1]
* `Std.Sat.CNF.dual` — the literal-negating De Morgan dual.
* `Std.Sat.CNF.DNFTautology` — every assignment satisfies the DNF reading.
  [AB09, §2.6.1]

## Main results

* `Std.Sat.CNF.evalDNF_dual` — the pointwise De Morgan law:
  the dual's DNF value is the negation of the CNF value.
* `Std.Sat.CNF.dnfTautology_dual_iff` — the dual is a DNF tautology iff the
  CNF is unsatisfiable; Example 2.21's pivot. [AB09, §2.6.1]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.6.1, Example 2.21, pp. 55-56.)
-/

namespace Std.Sat.CNF

/-- The **DNF reading** of the carrier: an OR of ANDs — the formula holds when
some clause has all its literals satisfied (`(v, b)` satisfied iff the
assignment gives `v` the value `b`, as in the CNF reading). Empty formula:
`false`; empty clause: `true` — the duals of the CNF conventions. -/
def evalDNF (a : ℕ → Bool) (φ : CNF ℕ) : Bool :=
  φ.any fun C => C.all fun ℓ => a ℓ.1 == ℓ.2

/-- The **De Morgan dual**: negate every literal in place, keeping the list
shape — `¬(⋀_i ⋁_j v_ij) = ⋁_i ⋀_j ¬v_ij` read dually. Size-preserving; no
distributive expansion. -/
def dual (φ : CNF ℕ) : CNF ℕ :=
  φ.map (List.map fun ℓ => (ℓ.1, !ℓ.2))

/-- The formula is a *tautology under the DNF reading*: every assignment makes
`evalDNF` true. [AB09, §2.6.1]'s tautology notion, on the DNF fragment. -/
def DNFTautology (φ : CNF ℕ) : Prop :=
  ∀ a : ℕ → Bool, φ.evalDNF a = true

/-- **The pointwise De Morgan law**: the dual's DNF value is the negation of
the CNF value, at every assignment.

**Proof sketch.** Induction on the clause list with `Bool.not_and`/`Bool.not_or`
pushed through `List.any`/`List.all` (`List.any_map`, `List.all_map`,
`Bool.not_all` in its Mathlib spelling): at the literal level,
`a v == !b = !(a v == b)` by cases on the two booleans; at the clause level the
negated OR of literals is the AND of negated literals; at the formula level
the negated AND of clauses is the OR of negated clauses. -/
theorem evalDNF_dual (φ : CNF ℕ) (a : ℕ → Bool) :
    (dual φ).evalDNF a = !(φ.eval a) := by
  sorry

/-- **The De Morgan pivot of Example 2.21**: the dual is a DNF tautology iff
the original CNF is unsatisfiable.

**Proof sketch.** Unfold both sides through `Std.Sat.CNF.evalDNF_dual`:
`(dual φ).evalDNF a = true ↔ φ.eval a = false` pointwise, so "every `a`
satisfies the dual" is "no `a` satisfies `φ`", which is the negation of
`Std.Sat.CNF.Satisfiable`. -/
theorem dnfTautology_dual_iff (φ : CNF ℕ) :
    (dual φ).DNFTautology ↔ ¬φ.Satisfiable := by
  sorry

end Std.Sat.CNF
