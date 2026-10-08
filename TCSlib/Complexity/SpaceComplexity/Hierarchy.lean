/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.ConfigGraph
import TCSlib.Complexity.SpaceComplexity.Constructible
import TCSlib.Complexity.TimeHierarchy.CodePrefix
import TCSlib.Complexity.TimeHierarchy.Diagonal
import TCSlib.Complexity.ClassNP.NP

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The space hierarchy theorem

[AB09, §4.1.3, Theorem 4.8] with its tool, the space-bounded universal
machine ([AB09, Exercise 4.1]), the strictness corollary `L ⊊ PSPACE` on the
p. 92 chain, and `SPACE(n+1) ≠ NP` ([AB09, Exercise 3.2], restated with the
positive normalization per the P0 convention —
`AroraBarakChapters3-4Plan.md` §2.4). Phase P4.3.

## Design

* **Constant-factor overhead is the point** ([AB09]: "one can have a
  universal TM using only a constant factor of space overhead, and hence we
  don't need the logarithmic term of Theorem 3.1"): the hierarchy hypothesis
  below is eventual domination of every constant multiple — no square, no
  log — in contrast to the received `f²` time hierarchy.
* **The space-universal machine** reuses the fixed code scheme
  `Complexity.TimeHierarchy.code` (one-work-tape binary codes) and mirrors
  the two-clause shape of `Turing.timed_universal`, with the budget a
  **space** bound: simulate within constant-factor space, and detect
  non-halting-within-space by the configuration-count clock
  (`Turing.MultiTapeTM.ConfigCount`). Its space bound carries a
  `+ logSpace n` addend for the clock — a declared deviation from
  Exercise 4.1's literal `C_α · t`, which presumes the standing
  `S(n) > log n` convention.
* **Both bounds space-constructible**, as in the book; constructibility of
  `g` drives the budget computation and the clock, constructibility of `f`
  is carried for fidelity (the proof uses only `g`'s — recorded in the
  sketch, seeded to the audit).
* The facade is frozen under the live P4.1 gate: wired through the root
  import only.

## Main results (all sorried; phase-P4.3 statements)

* `Complexity.space_universal` — [AB09, Exercise 4.1].
* `Complexity.space_hierarchy` — [AB09, Theorem 4.8].
* `Complexity.LOGSPACE_ssubset_PSPACE` — `L ⊊ PSPACE` on the p. 92 chain.
* `Complexity.SPACE_linear_ne_NP` — [AB09, Exercise 3.2], normalized.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.3, Theorem 4.8, Exercise 4.1;
  Exercise 3.2; [SHL65] through [AB09].)
-/

namespace Complexity

open Turing

/-- **The space-bounded universal machine** ([AB09, Exercise 4.1]; spec,
fill pending — phase P4.3): for the fixed scheme there is a machine `SU`
such that for every code `α` there is a constant `C` with, on input
`⟨bits s, ⟨α, x⟩⟩`: if the coded machine computes some output on `x` within
`s` visited work cells, `SU` outputs `true :: output` ; otherwise `SU`
outputs `[false]` — in both cases within `C · (s + logSpace |x| + 1)`
visited work cells (constant-factor space overhead plus the clock's
logarithmic addend; the time is existential, as
`Turing.FinTM.ComputesInTime`'s halting demands, with no stated bound).

**Proof sketch.** The interpreter of the chapter-1 `universal` machine
(table capture, virtual input, one simulated work tape held on one real
tape) is already constant-factor in *space*: the simulated tape occupies
one bank of at most `s` cells plus markers, the captured table and state
word are `O(|α|) ≤ C` cells, and the virtual-input discipline reads `x`
from the real input tape without copying. Non-halting-within-space is
detected by the configuration-count clock: a binary step counter of
`log₂ (configBound) = O(s + logSpace n)` bits (the
`Turing.MultiTapeTM.ConfigCount` arithmetic as in
`ComputesInTime.of_spaceUsed_le`), decremented per simulated step; window
overflow (the simulated head leaving `[-s, s]`) and counter exhaustion both
produce the `[false]` clause. Fill obligations, named: the space ledger of
the interpreter's banks (a §12 R1/R3 consumer — bank embedding and the
catalog space rows); the clock machine (`incrementTM` discipline at width
`O(s + logSpace n)`); the overflow detector; the two-clause assembly
mirroring `Turing.timed_universal`'s packaging. -/
theorem space_universal :
    ∃ SU : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, 0 < C ∧
      ∀ (s : ℕ) (x : List Bool),
        ((∃ (output : List Bool) (t : ℕ),
            ((TimeHierarchy.code).decode α).toFinTM.ComputesInTime x output t ∧
            ((TimeHierarchy.code).decode α).toFinTM.tm.spaceUsed
              (((TimeHierarchy.code).decode α).toFinTM.tm.initCfg x) t ≤ s) →
          ∀ (output : List Bool) (t : ℕ),
            ((TimeHierarchy.code).decode α).toFinTM.ComputesInTime x output t →
            ((TimeHierarchy.code).decode α).toFinTM.tm.spaceUsed
              (((TimeHierarchy.code).decode α).toFinTM.tm.initCfg x) t ≤ s →
            ∃ t' : ℕ,
              SU.ComputesInTime (pairEncode (Nat.bits s) (pairEncode α x))
                (true :: output) t' ∧
              SU.tm.spaceUsed
                  (SU.tm.initCfg (pairEncode (Nat.bits s) (pairEncode α x))) t'
                ≤ C * (s + logSpace x.length + 1)) ∧
        ((¬ ∃ (output : List Bool) (t : ℕ),
            ((TimeHierarchy.code).decode α).toFinTM.ComputesInTime x output t ∧
            ((TimeHierarchy.code).decode α).toFinTM.tm.spaceUsed
              (((TimeHierarchy.code).decode α).toFinTM.tm.initCfg x) t ≤ s) →
          ∃ t' : ℕ,
            SU.ComputesInTime (pairEncode (Nat.bits s) (pairEncode α x))
              [false] t' ∧
            SU.tm.spaceUsed
                (SU.tm.initCfg (pairEncode (Nat.bits s) (pairEncode α x))) t'
              ≤ C * (s + logSpace x.length + 1)) := by
  sorry

/-- **The space hierarchy theorem** ([AB09, Theorem 4.8]; [SHL65] through
[AB09]; spec, fill pending — phase P4.3): for space-constructible `f` and
`g`, if every constant multiple of `f` is eventually below `g`, then
`SPACE f ⊊ SPACE g`. Constant-factor hypothesis — no square and no
logarithmic term, by the constant-overhead universal simulation
(`Complexity.space_universal`); both constructibility hypotheses are the
book's, and the proof consumes only `g`'s (recorded here, seeded to the
audit). Positivity of both bounds is automatic from the bundled `logSpace`
floor, so the P0 zero-bound convention needs no side condition.

**Proof sketch.** The diagonal language of the padded-code discipline
(`TCSlib.Complexity.TimeHierarchy.CodePrefix`'s `preTM`/`scanPre`
self-application, exactly as the received time hierarchy): on input
`pairEncode α w`, compute the budget `g(n)` bits by `g`'s constructibility
witness (space `O(g n)`), run `Complexity.space_universal`'s interpreter on
the self-applied input at window budget proportional to `g n`, and flip the
answer; the flip is total because the universal's second clause answers
`[false]` on window or clock overflow. `D ∈ SPACE g` by the universal's
`C · (g n + logSpace n + 1)` bound and the floor `logSpace ≤ g`. If
`D ∈ SPACE f` via machine `M` with constant `c₀`, normal-form and code `M`
(the scheme's canonization), pad to a code string `α_M` long enough that
`C_M · (c₀ · f n + logSpace n + 1) ≤ g n` at the diagonal length — the
eventual-domination hypothesis instantiated at the constant assembled from
`C_M`, `c₀`, and the floor — and the flipped verdict contradicts `M`'s on
that input, both runs fitting inside the simulated window. Fill
obligations, named: the budget computation and window wiring; the
self-application assembly (`scanPre_pairEncode_append` precedent); the
contradiction arithmetic; `D`'s `DecidesInSpace` packaging. -/
theorem space_hierarchy (f g : ℕ → ℕ) (hf : SpaceConstructible f)
    (hg : SpaceConstructible g)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * f n ≤ g n) :
    SPACE f ⊂ SPACE g := by
  sorry

/-- **`L ⊊ PSPACE`** — the strict step of the p. 92 chain ([AB09, §4.3.2,
"the hierarchy theorems imply `L ⊊ PSPACE`"]; spec, fill pending).

**Proof sketch.** `Complexity.space_hierarchy` at `f := logSpace`,
`g := fun n => n + 1` (both constructible — the received
`Complexity.spaceConstructible_logSpace` and
`Complexity.spaceConstructible_linear` of phase P4.1; domination:
`A · logSpace n ≤ n + 1` eventually, a logarithm-versus-identity
inequality), then `SPACE (n + 1) ⊆ PSPACE`
(`Complexity.space_poly_subset_PSPACE` at degree one) and strictness
transports along the inclusion. -/
theorem LOGSPACE_ssubset_PSPACE : LOGSPACE ⊂ PSPACE := by
  sorry

/-- **`SPACE(n + 1) ≠ NP`** ([AB09, Exercise 3.2], stated at the positive
normalization `n + 1` per the P0 convention — the literal `SPACE(n)` is the
zero-work-tape class; spec, fill pending). Neither inclusion between the
two classes is claimed, matching the book's remark.

**Proof sketch.** Suppose `SPACE (n + 1) = NP`. `NP` is closed downward
under `≤ₚ` (the chapter-2 bounded-certificate transport — a derived
obligation from `Complexity.mem_NP_iff_exists_length_le`, Exercise 2.1's
bounded form, named for the brief). Padding transfers space bounds down:
for `L ∈ SPACE (n² + 1)`, the padded language
`L' := {x ++ 1^(|x|²) markers}` lies in `SPACE (m + 1)` in the padded
length `m` (run the `L`-decider on the unpadded prefix; the pad supplies
the room — the chapter-2 padding-cluster discipline, `EXP_subset_NEXP`'s
precedent), so `L' ∈ NP` by the assumption, and `L ≤ₚ L'` by the padding
reduction (a `polyUnary` emitter), so `L ∈ NP = SPACE (n + 1)`. Hence
`SPACE (n² + 1) ⊆ SPACE (n + 1)`, contradicting
`Complexity.space_hierarchy` at the constructible pair
(`Complexity.spaceConstructible_linear`,
`Complexity.spaceConstructible_poly` at degree two; domination
`A · (n + 1) ≤ n² + 1` eventually). Fill obligations, named: the `NP`
`≤ₚ`-closure lemma; the padded-language space decider; the padding
reduction machine; the strictness extraction. -/
theorem SPACE_linear_ne_NP : SPACE (fun n => n + 1) ≠ NP := by
  sorry

end Complexity
