/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.Formulas.CNFEncoding
import TCSlib.Complexity.ClassNP.NP
import TCSlib.Complexity.ClassNP.Reductions

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# SAT and 3SAT

[AB09, §2.3.1]: `SAT` is the language of (strings representing) satisfiable CNF
formulas, `3SAT` its restriction to 3CNF formulas (at most three literals per
clause). This module defines both over the audited serialization layer, states
their membership in `NP`, and states [AB09, Lemma 2.14] (`SAT ≤ₚ 3SAT`) — the
(b) half of the Cook-Levin proof plan, whose (a) half (Lemma 2.11, `SAT` is
`NP`-hard) is phase-4 material.

## Design and deviations from [AB09]

* **Strings, not formulas, are the language elements**: membership goes through
  the total `Std.Sat.CNF.decode` ([AB09, footnote 3]). With the fallback being
  the empty formula — satisfiable, and vacuously 3CNF — **every non-well-formed
  string lies in `SAT` and in `3SAT`**. [AB09] declares the fallback choice
  immaterial, and every stated result survives any fixed fallback — but not
  "uniformly": each language's malformed-input branch follows **its own
  predicate** on the fallback (a satisfiable fallback of width four would put
  the non-well-formed strings in `SAT` and out of `3SAT` — round-1 audit,
  finding 5), and the Lemma-2.14 reduction maps a non-well-formed input to the
  serialization of the **transformed** fallback, which keeps the reduction
  equivalence whatever the fixed choice.
* **`TAUTOLOGY` and [AB09, Example 2.21] are deferred to phase 4** (plan
  decision log): [AB09]'s `TAUTOLOGY` ranges over general Boolean formulas, and
  its coNP-hardness reduction negates the Cook-Levin CNF into a **DNF** — while
  the CNF-restricted tautology language is polynomial-time decidable (a CNF is
  a tautology iff every clause contains a complementary literal pair), i.e. it
  is **not** [AB09]'s language. The faithful carrier (the DNF dual layer) and
  the hardness half's prerequisite (Lemma 2.11) both belong to phase 4, so the
  whole package moves there rather than stating a wrong-language definition
  here.

## Main definitions

* `Complexity.SAT` — satisfiable CNF strings. [AB09, §2.3.1]
* `Complexity.SAT3` — satisfiable 3CNF strings. [AB09, §2.3.1]

## Main results

* `Complexity.SAT_mem_NP`, `Complexity.SAT3_mem_NP` — the assignment is the
  certificate. [AB09, Theorem 2.10, membership part]
* `Complexity.SAT_reducible_SAT3` — clause splitting with fresh variables.
  [AB09, Lemma 2.14]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.3.1, pp. 44-45; Theorem 2.10, p. 45;
  Lemma 2.14, p. 48 with §2.3.5, pp. 50-51.)
-/

namespace Complexity

open Std.Sat (CNF)
open Turing

/-- **The language `SAT`** [AB09, §2.3.1]: binary strings whose decoded CNF
formula is satisfiable. Decoding is total ([AB09, footnote 3]), with the empty —
satisfiable — formula as fallback, so every non-well-formed string is in `SAT`
(see the deviations list). -/
def SAT : Language Bool :=
  {x | (CNF.decode x).Satisfiable}

/-- **The language `3SAT`** [AB09, §2.3.1]: binary strings whose decoded formula
is a satisfiable 3CNF — every clause with at most three literals. The fallback
formula has no clauses, so non-well-formed strings are in `3SAT` as well. -/
def SAT3 : Language Bool :=
  {x | (CNF.decode x).WidthAtMost 3 ∧ (CNF.decode x).Satisfiable}

/-- **`SAT ∈ NP`** [AB09, Theorem 2.10, membership]: the satisfying assignment
is the certificate.

**Proof sketch.** Certificate parameters `(C, c) = (1, 1)`: length exactly
`(n + 1)` bits. A certificate `u` encodes the assignment `a_u = fun v => u.getD v
false`; by `Std.Sat.CNF.numVars_decode_le` the decoded formula mentions only
variables `< n`, and `Complexity.eval_congr_of_lt_numVars` makes the first
`numVars` bits decisive — so `x` is satisfiable iff some length-`(n+1)`
certificate `u` makes `(CNF.decode x).eval a_u = true` (forward: truncate a
satisfying assignment to `n + 1` bits; backward: `a_u` itself). The verifier
language is `V = {x ++ u : |u| = |x| + 1 ∧ (CNF.decode x).eval a_u = true}`;
`V ∈ P` by a machine with the named fill obligations: (i) unique-split recovery
— on input `y` of length `m`, the split `n + (n + 1) = m` forces `m` odd and
`n = (m - 1) / 2`, **rejecting explicitly on even `m`** (the round-3 pattern of
`Complexity.mem_NP_iff_exists_length_le`); (ii) the **parsing machine** for the
LL(1) grammar of `Std.Sat.CNF.parse` (run-length counting over unary indices;
on parse failure continue with the fallback, i.e. accept — the empty formula
evaluates `true`); (iii) the **evaluation machine**: stream the clauses; for a
literal `(v, b)`, walk to position `v` of the certificate region (the unary
index makes the walk linear) and compare with `b`; a clause with no satisfied
literal rejects the formula, exhausting all clauses accepts; (iv) the verdict
`[true]`/`[false]` with buffered output (the standing isolation obligation).
Budget: polynomial in `m`; conclude with `Complexity.mem_P_of_dtime_le`, and
`SAT ∈ NP` with `(1, 1, V)`. -/
theorem SAT_mem_NP : SAT ∈ NP := by
  sorry

/-- **`3SAT ∈ NP`** [AB09, Theorem 2.10, membership].

**Proof sketch.** The `Complexity.SAT_mem_NP` verifier with one more pass:
after parsing, additionally scan each clause counting literals to at most
three, rejecting a wider clause (so the verifier decides membership of the
decoded formula in the 3CNF fragment before evaluating). The fallback formula
has no clauses and passes the width check, keeping non-well-formed strings on
the member side, as `Complexity.SAT3` requires. Same parameters `(1, 1)`, same
budget shape. -/
theorem SAT3_mem_NP : SAT3 ∈ NP := by
  sorry

/-- **`SAT ≤ₚ 3SAT`** [AB09, Lemma 2.14]: clause splitting with fresh
variables.

**Proof sketch.** The formula-level transform `t : CNF ℕ → CNF ℕ` maps each
clause of width `> 3` to a chain: `C = ℓ₁ ∨ ℓ₂ ∨ rest` becomes
`(ℓ₁ ∨ ℓ₂ ∨ z) ∧ t(¬z ∨ rest)` with `z` a fresh variable, recursively until
width `≤ 3` ([AB09, §2.3.5]); clauses of width `≤ 3` pass through. Fresh
variables are allocated from `φ.numVars` upward by a running counter, so
freshness is by construction (indices `≥ numVars` are unmentioned —
`Complexity.eval_congr_of_lt_numVars`'s bound). **Equisatisfiability**, the
mathematical content, by induction on the splitting: forward, a satisfying
assignment extends to the fresh variables by giving each `z` the value "the
tail `rest` is satisfied" (if `ℓ₁ ∨ ℓ₂` already holds, `z := false` keeps the
second clause on its `¬z` disjunct — [AB09]'s case analysis); backward, a
satisfying assignment of the image restricted to the original variables
satisfies `C`, since from `(ℓ₁ ∨ ℓ₂ ∨ z)` and inductively `¬z ∨ rest` either
some original literal holds or the chain walks to one. Width and size: every
output clause has width `≤ 3`, and the output has at most `|C| - 2` chain
links per clause — total size linear in the input size, fresh indices at most
`numVars + Σ widths`. **The string-level reduction** is
`f = Std.Sat.CNF.serialize ∘ t ∘ Std.Sat.CNF.decode`, with
`Complexity.PolyTimeComputable f` by the named machine obligations: the parsing
machine (shared with `Complexity.SAT_mem_NP`), the streaming transform (a
clause buffer, a width counter, and the fresh-variable counter whose unary
serialization stays linear in the output position), and the serializer;
output length polynomial in `|x|`. **Correctness for every string**:
well-formed `x` by `Std.Sat.CNF.decode_serialize` and equisatisfiability
(width of `t φ` is `≤ 3` by construction); non-well-formed `x` decodes to the
fallback `[]`, which `t` fixes, so `f x = Std.Sat.CNF.serialize []` — and both
sides of `x ∈ SAT ↔ f x ∈ SAT3` are true (the fallback and the empty formula
are satisfiable and 3CNF). Conclude with the definition
`Complexity.PolyTimeReducible`. -/
theorem SAT_reducible_SAT3 : SAT ≤ₚ SAT3 := by
  sorry

end Complexity
