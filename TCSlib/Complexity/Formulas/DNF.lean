/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.Formulas.CNFEncoding

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

* **A DNF is the same syntax read dually, in its own type**: `Std.Sat.DNF`
  wraps a list of literal lists — exactly the shape of `Std.Sat.CNF ℕ` — and
  evaluates it as an OR of ANDs (`Std.Sat.DNF.eval`). Keeping the shape lets it
  reuse the audited serialization (`Std.Sat.DNF.decode`/`serialize` delegate to
  `Std.Sat.CNF.decode`/`serialize`); wrapping it means a DNF cannot be passed
  where a CNF is expected, or vice versa, without an explicit conversion. Per
  the phase-3 round-1 audit's guidance (finding 7), the DNF rendering is
  presented **as a fragment**, never silently identified with [AB09]'s general
  Boolean formulas; the fragment is exactly what Example 2.21's reduction
  produces, and `TAUTOLOGY` over it carries the example's full mathematical
  content (`TCSlib.Complexity.ClassNP.Tautology`).
* **The dual map negates every literal in place**:
  `¬(⋀_i ⋁_j v_ij) = ⋁_i ⋀_j ¬v_ij` — same list shape, each polarity bit
  flipped, read the other way (`Std.Sat.CNF.dual : CNF ℕ → DNF`). No
  distributive expansion occurs anywhere (which would be exponential); the
  dual is size-preserving.
* Under the DNF reading the conventions dualize: the empty formula evaluates
  `false` (empty OR) and an empty term evaluates `true` (empty AND) — the
  exact mirror of the CNF conventions.

## Main definitions

* `Std.Sat.DNF` — a DNF over `ℕ`: a list of terms read as an OR of ANDs.
* `Std.Sat.DNF.eval` — the OR-of-ANDs evaluation. [AB09, §2.6.1]
* `Std.Sat.DNF.Tautology` — every assignment satisfies the DNF.
  [AB09, §2.6.1]
* `Std.Sat.DNF.decode`, `Std.Sat.DNF.serialize` — the shared serialization.
* `Std.Sat.CNF.dual`, `Std.Sat.DNF.dual` — the literal-negating De Morgan duals, a CNF to a
  DNF and back (`Std.Sat.CNF.dual_dual`, `Std.Sat.DNF.dual_dual`).

## Main results

* `Std.Sat.CNF.eval_dual` — the pointwise De Morgan law:
  the dual's value is the negation of the CNF value.
* `Std.Sat.CNF.tautology_dual_iff` — the dual is a tautology iff the
  CNF is unsatisfiable; Example 2.21's pivot. [AB09, §2.6.1]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.6.1, Example 2.21, pp. 55-56.)
-/

namespace Std.Sat

/-- A **DNF formula** over variables `ℕ`: a list of terms, each a list of
literals read as a conjunction, the whole read as a disjunction. The same
list-of-literal-lists shape as `Std.Sat.CNF ℕ`, in a distinct type so the two
readings cannot be confused. -/
structure DNF where
  /-- The terms of the DNF, each read as a conjunction of literals. -/
  terms : List (List (Literal ℕ))

namespace DNF

/-- **Evaluation** of a DNF: some term has all its literals satisfied
(`(v, b)` satisfied iff the assignment gives `v` the value `b`, as in the CNF
reading). Empty formula: `false`; empty term: `true` — the duals of the CNF
conventions. [AB09, §2.6.1] -/
def eval (a : ℕ → Bool) (φ : DNF) : Bool :=
  φ.terms.any fun t => t.all fun ℓ => a ℓ.1 == ℓ.2

/-- The DNF is a *tautology*: every assignment makes `eval` true. [AB09,
§2.6.1]'s tautology notion, on the DNF fragment. -/
def Tautology (φ : DNF) : Prop :=
  ∀ a : ℕ → Bool, φ.eval a = true

/-- Decode a string as a DNF through the shared audited serialization
`Std.Sat.CNF.decode` (total: malformed strings give the empty formula). -/
def decode (x : List Bool) : DNF :=
  ⟨CNF.decode x⟩

/-- Serialize a DNF through the shared audited serialization
`Std.Sat.CNF.serialize`. -/
def serialize (φ : DNF) : List Bool :=
  CNF.serialize φ.terms

/-- Decoding inverts serialization for DNFs: through the shared clause-list
serialization, a serialized DNF decodes to itself (the DNF face of
`Std.Sat.CNF.decode_serialize`). -/
theorem decode_serialize (φ : DNF) : decode (serialize φ) = φ := by
  simp [decode, serialize, CNF.decode_serialize]

/-- Decoding a serialized CNF as a DNF reads the same clause list as terms. -/
theorem decode_cnf_serialize (φ : CNF ℕ) : decode (CNF.serialize φ) = ⟨φ⟩ := by
  simp [decode, CNF.decode_serialize]

/-- The **De Morgan dual** of a DNF: negate every literal in place and read the result
as a CNF, the inverse of `Std.Sat.CNF.dual`. -/
def dual (ψ : DNF) : CNF ℕ :=
  ψ.terms.map (List.map fun ℓ => (ℓ.1, !ℓ.2))

end DNF

namespace CNF

/-- The **De Morgan dual**: negate every literal in place, keeping the list
shape, and read the result as a DNF — `¬(⋀_i ⋁_j v_ij) = ⋁_i ⋀_j ¬v_ij`.
Size-preserving; no distributive expansion. -/
def dual (φ : CNF ℕ) : DNF :=
  ⟨φ.map (List.map fun ℓ => (ℓ.1, !ℓ.2))⟩

/-- **The pointwise De Morgan law**: the dual's value is the negation of
the CNF value, at every assignment.

**Proof sketch.** Induction on the clause list with `Bool.not_and`/`Bool.not_or`
pushed through `List.any`/`List.all`: at the literal level,
`a v == !b = !(a v == b)` by cases on the two booleans; at the clause level the
negated OR of literals is the AND of negated literals; at the formula level
the negated AND of clauses is the OR of negated clauses. -/
theorem eval_dual (φ : CNF ℕ) (a : ℕ → Bool) :
    (dual φ).eval a = !(φ.eval a) := by
  have hclause (C : Clause ℕ) :
      (C.map fun ℓ => (ℓ.1, !ℓ.2)).all (fun ℓ => a ℓ.1 == ℓ.2) = !(C.eval a) := by
    induction C with
    | nil => rfl
    | cons ℓ C ih =>
        simp only [List.map_cons, List.all_cons, Clause.eval_cons, ih, Bool.not_or]
        cases a ℓ.1 <;> cases ℓ.2 <;> rfl
  induction φ with
  | nil => rfl
  | cons C φ ih =>
      change ((C.map fun ℓ => (ℓ.1, !ℓ.2)).all (fun ℓ => a ℓ.1 == ℓ.2) ||
        (dual φ).eval a) = !(C.eval a && eval a φ)
      rw [hclause, ih, Bool.not_and]

/-- Dualizing twice restores a CNF. -/
@[simp] theorem dual_dual (φ : CNF ℕ) : (dual φ).dual = φ := by
  simp [dual, DNF.dual, List.map_map, Function.comp_def]

/-- Dualizing twice restores a DNF. -/
@[simp] theorem _root_.Std.Sat.DNF.dual_dual (ψ : DNF) : dual ψ.dual = ψ := by
  rcases ψ with ⟨ts⟩
  simp [dual, DNF.dual, List.map_map, Function.comp_def]

/-- **The De Morgan pivot of Example 2.21**: the dual is a tautology iff
the original CNF is unsatisfiable.

**Proof sketch.** Unfold both sides through `Std.Sat.CNF.eval_dual`:
`(dual φ).eval a = true ↔ φ.eval a = false` pointwise, so "every `a`
satisfies the dual" is "no `a` satisfies `φ`", which is the negation of
`Std.Sat.CNF.Satisfiable`. -/
theorem tautology_dual_iff (φ : CNF ℕ) :
    (dual φ).Tautology ↔ ¬φ.Satisfiable := by
  simp only [DNF.Tautology, eval_dual, Satisfiable, not_exists,
    Bool.not_eq_true', Bool.eq_false_iff]

end CNF

end Std.Sat
