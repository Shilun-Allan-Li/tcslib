/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.Logspace.Path
import TCSlib.Complexity.SpaceComplexity.Constructible

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Immerman-Szelepcsényi theorem

[AB09, §4.3.2, Theorem 4.20 and Corollary 4.21]: nondeterministic space is
closed under complement — `PATH-complement ∈ NL`, hence `NL = coNL`, and for
space-constructible `S` the same inductive counting gives
`NSPACE(S) = coNSPACE(S)`. Phase P4.4 of `AroraBarakChapters3-4Plan.md`.

## Design

* **No read-once certificate model is introduced.** [AB09] proves Theorem
  4.20 in the certificate view of `NL` (its §4.3.1, Definition 4.19 — a
  read-once certificate tape), which the plan defers. The campaign's
  binary-choice NDTM makes that view *native*: a choice word is consumed one
  bit per step and can never be re-read, so the book's certificates are
  exactly choice words and the inductive-counting verifier runs directly on
  `Turing.FinNDTM` — the deviation is a simplification, recorded here for
  the audit.
* The counting runs over the configuration-graph layer of phase P4.2
  (`Turing.NDTM.coreSum`, `Turing.FinNDTM.configBound`) for Corollary 4.21,
  and over the decoded adjacency relation for the `PATH` form.

## Main results (all sorried; phase-P4.4 statements)

* `Complexity.compl_PATH_mem_NL` — [AB09, Theorem 4.20] as stated there.
* `Complexity.NL_eq_coNL` — the headline equality. [AB09, §4.3.2]
* `Complexity.NSPACE_compl_eq` — [AB09, Corollary 4.21].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3.1-§4.3.2, Theorem 4.20,
  Corollary 4.21.)
* [Imm88] N. Immerman, *Nondeterministic space is closed under
  complementation*, SIAM J. Comput. 17(5), 1988; [Sze87] R. Szelepcsényi,
  *The method of forcing for nondeterministic automata*, Acta Informatica
  26, 1988. (Cited through [AB09]; no external text required.)
-/

namespace Complexity

open Turing

/-- **`PATH`-complement is in `NL`** ([AB09, Theorem 4.20]; spec, fill
pending — phase P4.4): nonreachability has nondeterministically verifiable
certificates, by inductive counting.

**Proof sketch.** The verifier of [AB09]'s proof, with choice words as the
certificates (native read-once — see the module docstring). For the decoded
instance `⟨G, s, t⟩` with `n` vertices, guess and check, for
`i = 0, …, n`, the sizes `cᵢ = |Cᵢ|` of the balls `Cᵢ` (vertices reachable
from `s` within `i` steps): membership certificates are guessed paths
(replayable within `O(logSpace n)` registers, as in
`Complexity.PATH_mem_NL`'s walk); non-membership of `v` in `Cᵢ` is certified
by enumerating, in **ascending vertex order**, `cᵢ₋₁` members of `Cᵢ₋₁` with
their paths and checking none equals or neighbors `v` (the ascending-order
discipline and the exact count `cᵢ₋₁` are what make cheating impossible);
`c₀ = 1`, and the final stage certifies `t ∉ Cₙ`. Registers: the stage, two
counters, the current and enumerated vertices, a path cursor — all
`O(logSpace n)` cells; all-branch halting at a uniform polynomial budget.
Membership of non-encodings: strings outside the instance format are in
`PATHᶜ` by definition, so the verifier accepts exactly the malformed shapes
too (the shape validator of `Complexity.PATH_mem_NL`, answer flipped).
Fill obligations, named: the counting verifier's register machine (the
nondeterministic ARM extension's second named customer, after the `PATH`
walk), the ascending-order and exact-count checks, the two-level certificate
layout along one choice word, and the `DecidesInSpace` packaging. -/
theorem compl_PATH_mem_NL : (PATHᶜ : Language Bool) ∈ NL := by
  sorry

/-- **`NL = coNL`** ([AB09, §4.3.2]; spec, fill pending).

**Proof sketch.** `⊆`: for `B ∈ NL`, `B ≤ₗ PATH`
(`Complexity.PATH_NLComplete`); the same reduction also reduces `Bᶜ` to
`PATHᶜ` (complement both sides of the equivalence), and `NL` is closed
downward under `≤ₗ` (a named fill obligation — the logspace analogue of
`Complexity.mem_LOGSPACE_of_logspaceReducible`, proved by the same
virtual-input composition against the `NL` verifier, so `Bᶜ ∈ NL` by
`Complexity.compl_PATH_mem_NL`), i.e. `B ∈ coNL`. `⊇` is the same argument
read backwards (complements are involutive). -/
theorem NL_eq_coNL : NL = coNL := by
  sorry

/-- **Nondeterministic space is closed under complement**
([AB09, Corollary 4.21]; spec, fill pending): for space-constructible `S`,
the complements of `NSPACE S` languages are exactly `NSPACE S`.

**Proof sketch.** [AB09, Exercise 4.11]'s route: run the inductive counting
of `Complexity.compl_PATH_mem_NL` on the **configuration graph** instead of
a decoded instance — balls of the start vertex among the
`Turing.FinNDTM.configBound`-many coded vertices (phase P4.2's layer),
membership certificates being guessed choice-word paths replayed through
the step relation, with the window radius computed from the
constructibility witness. Space: the counters and vertex registers are
`O(S n)` bits, within `NSPACE S`'s constant absorption; the `logSpace`
floor bundled in `Complexity.SpaceConstructible` powers the index
arithmetic. Fill obligations, named: the vertex-coded counting verifier
(the graph-level twin of the `PATH` one), the accepting normalization
reuse, and the two-sided packaging `{L | Lᶜ ∈ NSPACE S} = NSPACE S`. -/
theorem NSPACE_compl_eq (S : ℕ → ℕ) (hS : SpaceConstructible S) :
    {L : Language Bool | Lᶜ ∈ NSPACE S} = NSPACE S := by
  sorry

end Complexity
