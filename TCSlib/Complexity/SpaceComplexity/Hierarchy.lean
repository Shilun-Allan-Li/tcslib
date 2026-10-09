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
  is carried for fidelity (the proof uses only `g`'s witness and `f`'s
  bundled `logSpace` floor — round-1 confirmed, recorded in the sketch).
* Facade wiring: root-wired while the P4.1 gate was live; the
  `SpaceComplexity.lean` facade has carried this module since that gate
  closed.

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
(table capture, virtual input, the simulated work tape held on one real
bank) is constant-factor in *space*; the budget test and the output contract
need care (round-1 finding 4). (i) **Space is tested as visited-interval
cardinality, not window membership**: maintain the simulated head's minimum
and maximum positions — both start at `0`, so one cell is visited
immediately, and at `s = 0` the failure clause fires on every input; unit
moves make `max − min + 1` exactly the visited count, checked **including
the final configuration**, with `max − min + 1 > s` rejecting (head
membership in `[-s, s]` does not count cells: visiting `0` then `1` uses two
cells inside `[-1, 1]`). (ii) **Non-halting-within-space is detected by the
core-count clock**: a binary counter of `O_α(s + logSpace n)` bits bounding
`(|Q|+1)·(n+2)·3^{2s+1}·(2s+1)` — a deterministic run repeating a live core
inside the window is periodic forever, so no first halt occurs after an
undetected repeat; outputs never enter the argument, cores excluding the
output tape (the `Turing.MultiTapeTM.ConfigCount` arithmetic as in
`ComputesInTime.of_spaceUsed_le`). (iii) **Probe silently, then replay**:
streamed output cannot be retracted when a later overflow or clock
exhaustion must yield exactly `[false]`, so the first pass runs with output
captured (W1); on success the machine resets the simulated banks, emits
`true`, and replays the run forwarding output — fixed banks reused between
the passes. (iv) The canonizer cost is a **finite code-dependent constant**
absorbed into `C` (the effective scheme supplies no bound linear in the code
length, and none is claimed). The `+ logSpace n` addend pays for the clock's
input-position factor under this construction — no lower-bound claim against
other universal simulations — and is absorbed under the standing
`s ≥ logSpace n` convention (`s + logSpace n + 1 ≤ 3s`). Fill obligations,
named: the interval counters with the final-configuration check; the
core-count clock at the stated width; the probe/replay two-pass assembly
over fixed banks (a §12 R1/R3 consumer); the per-code constant ledger. -/
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
self-application), with a **capped increasing-budget loop** that removes the
per-code constant from the space ledger (round-1 finding 5: `∀ α, ∃ Cα`
gives no uniform `O(g)` bound when the code is read off the input, and
padding a code can change its constant): on input `pairEncode α w`, `D`
(i) computes `g n` by `g`'s constructibility witness (space `O(g n)`);
(ii) tries budgets `s = 0, 1, …, g n`, reusing fixed banks, running
`Complexity.space_universal`'s machine on the self-applied virtual input at
budget `s` while **hard-capping the fixed universal's own work heads**
inside `[-g n, g n]` — a cap depending only on that machine's fixed tape
count, hence uniform in `α`; capped or failed attempts advance the budget;
(iii) answers the **opposite** of the first successful attempt's verdict,
retaining only a three-valued attempt summary (failure, success with
`[true]`, success otherwise; output suppressed, W1), and a fixed answer if
every attempt caps out. `D ∈ SPACE g`: the universal's fixed tapes confined
to the cap, the budget and address counters, and the bank resets are
`O(g n)` cells, uniformly in the input's code part. If `D ∈ SPACE f` via
machine `M` with constant `c₀`: put `M` into a **space-preserving
one-work-tape coded normal form** — a named fill obligation; the chapter-1
time-only normal form is not a space ledger — with fixed code `α_M`, and pad
the **payload**, never the code (the `CodePrefix` discipline keeps one code
fixed so a single constant `C_{α_M}` applies). By the eventual-domination
hypothesis at the assembled constant `A := C_{α_M} · (c₀ + 2)`, using the
bundled floors `logSpace n ≤ f n` and `1 ≤ f n`,
`C_{α_M}·(c₀·f n + logSpace n + 1) ≤ C_{α_M}·(c₀ + 2)·f n ≤ g n` eventually,
so some attempt at budget at most `c₀ · f n` succeeds within every cap, and
every successful attempt reports `M`'s deterministic verdict on the
self-applied input — which `D` flips: contradiction. Constructibility of `f`
contributes only its bundled floor. Fill obligations, named: the budget loop
with fixed-bank resets and the uniform cap; the attempt-summary discipline;
the space-preserving normal form; the self-application assembly
(`scanPre_pairEncode_append` precedent); the contradiction arithmetic;
`D`'s `DecidesInSpace` packaging. -/
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
`L' := {pairEncode x (List.replicate (|x|²) true)}` — padded length exactly
`m = n² + 2n + 2`, syntax validated — lies in `SPACE (m + 1)` in the padded
length (validate, then run the `L`-decider on the first component; the pad
supplies the room — the chapter-2 padding-cluster discipline,
`EXP_subset_NEXP`'s precedent), so `L' ∈ NP` by the assumption, and
`L ≤ₚ L'` by the padding reduction (a `polyUnary` emitter; the **unpadded**
language reduces to the **padded** one), so `L ∈ NP = SPACE (n + 1)` — the
`NP` pullback composing the reduction with the bounded-certificate verifier
at the reduction's polynomial output length. Hence
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
