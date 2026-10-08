/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.Examples

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The zero-space collapse and positive normalization

The sanity layer for the P0 reception audit's finding 1 (round 1, sanity targets
S1-S6): because every work tape's visited set contains its origin, `SPACE s`
collapses to the zero-work-tape class as soon as `s` has a **single** zero — in
particular the literal `SPACE (fun n => n)` is not linear space — while additive
normalization by `+ 1` is harmless for everywhere-positive bounds. These
statements pin the campaign convention (every asymptotic chapter bound is
everywhere positive) to elaborated sanity statements — their proofs are fill
obligations; the round-2 audit certified each statement true as stated — so
the convention cannot be overlooked. The
zero-space class is nevertheless not trivial: constant languages and the parity
language have zero-work-tape deciders (input is read in finite control).

## Main results (sorried; P0 round-1 sanity statements)

* `Turing.FinTM.k_le_spaceUsed` — S1: the tape count lower-bounds the space, at
  every input and time.
* `Turing.FinTM.ComputesInSpace.k_eq_zero_of_exists_zero` — S2: one zero of the
  bound forces zero work tapes.
* `Complexity.SPACE_eq_zero_of_exists_zero`, `Complexity.SPACE_id_eq_SPACE_zero`
  — S3: the collapse, and its instantiation at the identity bound.
* `Complexity.SPACE_succ_of_pos`, `Complexity.SPACE_succ_eq_max_one` — S4: when
  the `+ 1` normalization is invisible.
* `Turing.pairEncode_bits_inj` — S5: the `Complexity.indexLang` encoding is
  injective, index `0` included.
* `Complexity.trueLang_mem_SPACE_zero`, `Complexity.evenLang_mem_SPACE_zero` —
  S6: the zero-space class contains constants and parity (so it is not empty,
  and not only constants).
* `Complexity.exists_zeroTape_const_oneStep`,
  `Complexity.exists_zeroTape_parity_decider` — S6 with the explicit time
  contracts (P0 round 2, finding 12): the one-step constant machine and the
  `n + 1`-step parity decider, both with zero work tapes.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1, Definition 4.1 — the received
  `SPACE`; the collapse itself has no book counterpart, being an artifact of
  unnormalized bounds that the book's `S(n) > log n` convention rules out.)
-/

namespace Turing.FinTM

/-- **S1 — the tape count lower-bounds the space**: every work tape's visited set
contains the position of its head at time `0`, so `spaceUsed` is at least the
number of work tapes, on every input at every time.

**Proof sketch.** `Turing.MultiTapeTM.spaceUsedByTape` is the cardinality of
`Turing.MultiTapeTM.visitedByTapeHead`, an image of the nonempty
`Finset.range (t + 1)`; a nonempty image has positive cardinality
(`Finset.Nonempty.image`, `Finset.card_pos`). Sum `1 ≤ card` over the `k` tapes
(`Finset.card_le_card_of_injOn` is not needed — `Finset.sum_le_sum` on the
constant-one function). -/
theorem k_le_spaceUsed (M : FinTM Bool) (x : List Bool) (t : ℕ) :
    M.k ≤ M.tm.spaceUsed (M.tm.initCfg x) t := by
  sorry

/-- **S2 — one zero of the bound forces zero work tapes**: a machine computing
within space `s` where `s n₀ = 0` for even a single length `n₀` has no work
tapes at all (and hence zero space on **every** input).

**Proof sketch.** Instantiate the contract at the input
`List.replicate n₀ false`: it supplies a halting time `t` with
`spaceUsed ≤ s n₀ = 0`; `Turing.FinTM.k_le_spaceUsed` gives `M.k ≤ 0`
(`Nat.le_zero`). -/
theorem ComputesInSpace.k_eq_zero_of_exists_zero {M : FinTM Bool}
    {f : List Bool → List Bool} {s : ℕ → ℕ} (h : M.ComputesInSpace f s)
    (hz : ∃ n, s n = 0) : M.k = 0 := by
  sorry

end Turing.FinTM

namespace Complexity

open Turing

/-- **S3 — the collapse**: as soon as the bound has a single zero, `SPACE s` is
the zero-work-tape class `SPACE (fun _ => 0)`. Multiplicative absorption cannot
repair this: `c * 0 = 0` for every `c`.

**Proof sketch.** `⊆`: a witness machine has `M.k = 0` by
`Turing.FinTM.ComputesInSpace.k_eq_zero_of_exists_zero` (at the bound
`fun n => c * s n`, whose zero is inherited from `s`'s); a zero-tape machine has
`spaceUsed = 0` (`Finset.sum_empty` over `Fin 0`) on every input, so the same
machine and times witness `DecidesInSpace L (fun _ => 0)`. `⊇`: `0 ≤ c * s n`
pointwise, so the zero-space contract weakens to any bound
(`Turing.FinTM.ComputesInSpace.mono`). -/
theorem SPACE_eq_zero_of_exists_zero {s : ℕ → ℕ} (hz : ∃ n, s n = 0) :
    SPACE s = SPACE (fun _ => 0) := by
  sorry

/-- **S3, instantiated — literal `SPACE (fun n => n)` is the zero-work-tape
class**, because of the zero at the empty input. This is the statement that
makes the positive-normalization convention impossible to overlook: the
chapter-3/4 campaign states Exercise 3.2 and every other asymptotic space bound
with everywhere-positive functions (`fun n => n + 1`, `fun n => n ^ c + 1`,
`Complexity.logSpace`).

**Proof sketch.** `Complexity.SPACE_eq_zero_of_exists_zero` at `⟨0, rfl⟩`. -/
theorem SPACE_id_eq_SPACE_zero : SPACE (fun n => n) = SPACE (fun _ => 0) := by
  sorry

/-- **S4, first half — `+ 1` is invisible on everywhere-positive bounds**:
`SPACE s = SPACE (fun n => s n + 1)` when `0 < s n` for all `n`.

**Proof sketch.** `⊆`: `s n ≤ s n + 1`, `Complexity.SPACE.mono`. `⊇`: from
positivity `s n + 1 ≤ 2 * s n`, so a `c · (s n + 1)` contract is a
`(2c) · s n` contract — constant absorption inside the class's existential. -/
theorem SPACE_succ_of_pos {s : ℕ → ℕ} (hpos : ∀ n, 0 < s n) :
    SPACE s = SPACE (fun n => s n + 1) := by
  sorry

/-- **S4, second half — for arbitrary bounds, `+ 1` is the `max 1`
normalization**: `SPACE (fun n => s n + 1) = SPACE (fun n => max 1 (s n))`.

**Proof sketch.** Pointwise `max 1 (s n) ≤ s n + 1 ≤ 2 * max 1 (s n)` (case on
`s n = 0`); both directions are `Complexity.SPACE.mono` plus constant
absorption, as in `Complexity.SPACE_succ_of_pos`. -/
theorem SPACE_succ_eq_max_one (s : ℕ → ℕ) :
    SPACE (fun n => s n + 1) = SPACE (fun n => max 1 (s n)) := by
  sorry

end Complexity

namespace Turing

/-- **S5 — the index-pair encoding is injective, index `0` included**:
`pairEncode x (Nat.bits i)` determines both the string and the index. At
`i = 0` the payload is empty but the separator remains (`pairEncode [] [] =
[false, true] ≠ []`), so no collision with malformed words arises — the
boundary behavior behind `Complexity.indexLang`.

**Proof sketch.** Forward: `Turing.pairDecode_pairEncode` recovers both
components, and `Nat.bits` is injective (its value inverse — the
`Complexity.LogProg.bitsVal`/`bits_injective` layer of
`TCSlib.Complexity.SpaceComplexity.Machines.Bin`, or `Nat.bits` induction).
Backward: congruence. -/
theorem pairEncode_bits_inj (x y : List Bool) (i j : ℕ) :
    pairEncode x (Nat.bits i) = pairEncode y (Nat.bits j) ↔ x = y ∧ i = j := by
  sorry

end Turing

namespace Complexity

open Turing

/-- **S6a — the zero-space class contains the constant languages**: the full
language is decided by a zero-work-tape machine (emit `[true]`, halt), with
space `0` and even constant `c = 0` in the class existential.

**Proof sketch.** A one-live-state machine with `k = 0` whose single transition
emits `true` and halts; `spaceUsed` is the empty sum. Halting time `1` feeds
`Turing.FinTM.ComputesInSpace`'s existential. -/
theorem trueLang_mem_SPACE_zero : ({x | True} : Language Bool) ∈ SPACE fun _ => 0 := by
  sorry

/-- **S6b — the zero-space class is not only constants**: parity
(`Complexity.evenLang`) has a zero-work-tape decider — the input is read
two-way-read-only and the running parity lives in finite control. (With
`Complexity.SPACE.mono` this also strengthens
`Complexity.evenLang_mem_LOGSPACE`.) A zero-tape machine still takes `n + 1`
steps here, which is why no `2^{O(s)}` time bound without the input factor can
hold below logarithmic space — the received `configBound` correctly keeps its
`n + 2` factor.

**Proof sketch.** A two-state (`parity bit in control`) zero-tape machine scans
the input left to right (`n + 1` steps), then emits the indicator of even
parity and halts; the scan invariant is the parity of the consumed prefix, as
in the direct machine of `Complexity.evenLang_mem_LOGSPACE`'s sketch, minus the
work tape. -/
theorem evenLang_mem_SPACE_zero : evenLang ∈ SPACE fun _ => 0 := by
  sorry

/-- **S6a with the time contract** (P0 round 2, finding 12): a zero-work-tape
machine computes `[true]` within **one step** on every input — the explicit
witness behind `Complexity.trueLang_mem_SPACE_zero`, whose membership statement
alone leaves the halting time an unspecified existential.

**Proof sketch.** One live state, `k = 0`; the single transition emits `true`
and halts (`state := none`); `Turing.FinTM.ComputesInTime x [true] 1` holds on
every input, and the space is the empty sum. -/
theorem exists_zeroTape_const_oneStep :
    ∃ M : Turing.FinTM Bool, M.k = 0 ∧
      ∀ x : List Bool, M.ComputesInTime x [true] 1 := by
  sorry

/-- **S6b with the time contract** (P0 round 2, finding 12): a zero-work-tape
machine decides the parity language within `n + 1` steps — the explicit
witness behind `Complexity.evenLang_mem_SPACE_zero`. The construction is the
round-2 report's: two live control states carrying the parity of the consumed
prefix (toggle on `true`, keep on `false`), `x.length` symbol steps and one
final emit-and-halt step at the right blank.

**Proof sketch.** The scan invariant "control state = parity of
`(x.take j).count true`" by induction on the consumed prefix; at the boundary
emit `[Turing.MultiTapeTM.indicator evenLang x]` and halt, within
`x.length + 1` steps; `k = 0` makes the space the empty sum. -/
theorem exists_zeroTape_parity_decider :
    ∃ M : Turing.FinTM Bool, M.k = 0 ∧
      M.DecidesInTime evenLang fun n => n + 1 := by
  sorry

end Complexity
