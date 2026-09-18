/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Std.Sat.CNF
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Fintype.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# CNF formulas for the complexity development

[AB09, §2.3.1]: a CNF formula is an AND of ORs of literals (variables or their
negations); a `k`CNF is a CNF in which every clause has **at most** `k` literals.
This module supplies the formula layer that `SAT`, `3SAT`, and the Cook-Levin
development consume: the carrier type, satisfiability, the variable-count measure
used by certificate-length formulas, clause-width bounds, and the statement of
[AB09, Claim 2.13] (CNF universality).

## Design and deviations from [AB09]

* **The carrier is `Std.Sat.CNF ℕ`** — the Lean-core SAT type: a formula is a
  `List` of clauses, a clause a `List` of literals, a literal a pair
  `(v, b) : ℕ × Bool` satisfied by an assignment `a` exactly when `a v = b` (so
  `b = true` is the positive literal `u_v` and `b = false` its negation). This is
  the **provisional resolution of the phase-3 seeded design question** (in-house
  type vs. `Std.Sat.CNF`; see the plan's decision log): the in-house candidate
  would have been byte-for-byte this shape, core supplies the evaluation
  (`Std.Sat.CNF.eval`, an all/any nest exactly matching [AB09]'s ⋀⋁), the
  mentioned-variable machinery (`Std.Sat.CNF.Mem`, `Std.Sat.CNF.eval_congr`),
  and relabeling with `Std.Sat.CNF.eval_relabel` (the fresh-variable tool of the
  clause-splitting and tableau constructions), and the repository policy is to
  use an existing mechanism rather than invent a parallel one. The type is pinned
  by `lean-toolchain`; the risk of upstream namespace drift is accepted and
  recorded. Campaign-side additions live in the `Std.Sat.CNF` namespace when they
  are formula-level (this file and the serialization layer) and in `Complexity`
  when they are complexity-level.
* **Conventions inherited from the carrier**: the empty formula evaluates `true`
  (`Std.Sat.CNF.eval_nil`) and an empty clause evaluates `false` — [AB09]'s
  standard reading of empty conjunctions/disjunctions.
* **Assignments are total functions `ℕ → Bool`.** [AB09] assigns to the `n`
  variables of the formula; a total assignment restricted to the mentioned
  variables carries the same information, and `Complexity.eval_congr_of_lt_numVars`
  (below) is the bridge that lets a finite certificate of `numVars φ` bits
  determine the value.
* **`kCNF` is "at most `k` literals per clause"** ([AB09, §2.3.1] verbatim);
  `Std.Sat.CNF.WidthAtMost` renders it.
* **Claim 2.13's size measure**: [AB09] counts `∧`/`∨` symbols (size `ℓ·2^ℓ`).
  Our statement bounds the clause count by `2^ℓ` and every clause's width by `ℓ`,
  from which [AB09]'s connective count follows by the trivial accounting
  (`#∧ = clauses − 1`, `#∨ = Σ (width − 1)` on nonempty data); the two
  renderings carry the same content and ours is the form the consumers use.

## Main definitions

* `Std.Sat.CNF.Satisfiable` — some assignment evaluates to `true`.
  [AB09, §2.3.1]
* `Std.Sat.CNF.numVars` — one plus the largest mentioned variable index (`0` for
  formulas mentioning nothing); the measure certificate-length formulas use.
* `Std.Sat.CNF.WidthAtMost` — every clause has at most `k` literals ([AB09]'s
  `k`CNF, §2.3.1).

## Main results

* `Complexity.eval_congr_of_lt_numVars` — evaluation depends only on the first
  `numVars` assignment bits.
* `Complexity.exists_cnf_boolFun` — CNF universality. [AB09, Claim 2.13]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.3.1, pp. 44-45; Claim 2.13, p. 46.)
-/

namespace Std.Sat.CNF

/-- The formula `φ` is *satisfiable*: some assignment makes it evaluate `true`
[AB09, §2.3.1]. (Core's `Std.Sat.CNF.Sat` fixes the assignment and
`Std.Sat.CNF.Unsat` is the universal negative; this is the existential the
language `SAT` quantifies.) -/
def Satisfiable {α : Type} (φ : CNF α) : Prop :=
  ∃ a : α → Bool, φ.eval a = true

/-- One plus the largest variable index mentioned in `φ`, and `0` when `φ`
mentions no variable (in particular on the empty formula and on empty clauses).
Every mentioned variable of `φ` is `< φ.numVars`, so an assignment certificate
of `numVars` bits determines the evaluation
(`Complexity.eval_congr_of_lt_numVars`); this is the measure the explicit
certificate-length formulas of `SAT ∈ NP` are budgeted against. -/
def numVars (φ : CNF ℕ) : ℕ :=
  (φ.flatMap fun C => C.map fun ℓ => ℓ.1 + 1).foldr max 0

/-- Every clause of `φ` has at most `k` literals — [AB09, §2.3.1]'s `k`CNF
("a CNF formula in which all clauses contain at most `k` literals"). The empty
formula qualifies vacuously for every `k`. -/
def WidthAtMost {α : Type} (φ : CNF α) (k : ℕ) : Prop :=
  ∀ C ∈ φ, C.length ≤ k

end Std.Sat.CNF

namespace Complexity

open Std.Sat (CNF)

/-- Evaluation reads only the first `numVars` assignment values: assignments that
agree below `φ.numVars` evaluate `φ` identically. This is the bridge from finite
assignment certificates to total assignments.

**Proof sketch.** Every variable `v` mentioned in `φ` (`Std.Sat.CNF.Mem v φ`)
contributes `v + 1` to the `foldr max` defining `Std.Sat.CNF.numVars`, so
`v < φ.numVars` (a list-membership-to-fold bound, by induction on the flattened
list); then `Std.Sat.CNF.eval_congr` applies, its agreement hypothesis
discharged by the assumed agreement below `numVars`. -/
theorem eval_congr_of_lt_numVars {φ : CNF ℕ} {a b : ℕ → Bool}
    (h : ∀ v < φ.numVars, a v = b v) : φ.eval a = φ.eval b := by
  sorry

/-- **CNF universality** [AB09, Claim 2.13]: every Boolean function
`f : {0,1}^ℓ → {0,1}` is computed by an `ℓ`-variable CNF formula with at most
`2^ℓ` clauses of width at most `ℓ` ([AB09]'s size measure `ℓ·2^ℓ` follows by
counting connectives — see the deviations list). The formula mentions only
variables `< ℓ`, so its evaluation at a total assignment is `f` of the
assignment's restriction.

**Proof sketch.** [AB09]'s construction. For each `v : Fin ℓ → Bool` with
`f v = false`, the clause `C_v = [(i, !(v i)) : i < ℓ]` evaluates to `false`
exactly at the assignments restricting to `v` (a literal `(i, !(v i))` is
satisfied iff `a i ≠ v i`, so `C_v.eval a = false` iff `a` agrees with `v` below
`ℓ`). Take `φ` to be the list of `C_v` over the (finitely many, at most `2^ℓ`)
falsifying `v`, e.g. via `Finset.univ.filter (fun v => f v = false)` on the
`Fintype` of `Fin ℓ → Bool`. Then `φ.eval a = false` iff some `C_v` fails at `a`
iff `f` of `a`'s restriction is `false`. Bounds: clause count at most
`2^ℓ = Fintype.card (Fin ℓ → Bool)`, width exactly `ℓ`, mentioned variables
`< ℓ` so `numVars ≤ ℓ`. Edge cases: at `ℓ = 0` the function is a constant on
the empty vector — `φ = []` (evaluating `true`) or `φ = [[]]` (one empty
clause, evaluating `false`, width `0 ≤ ℓ`), both within the `2^0 = 1` clause
bound. -/
theorem exists_cnf_boolFun (ℓ : ℕ) (f : (Fin ℓ → Bool) → Bool) :
    ∃ φ : CNF ℕ, φ.numVars ≤ ℓ ∧ φ.length ≤ 2 ^ ℓ ∧ φ.WidthAtMost ℓ ∧
      ∀ a : ℕ → Bool, φ.eval a = f fun i => a i.val := by
  sorry

end Complexity
