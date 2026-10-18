/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.NDCodes
import TCSlib.Complexity.ClassNP.NTIME
import TCSlib.Complexity.ClassP.TimeConstructible
import TCSlib.Complexity.ClassNP.NDNormalForm
import TCSlib.Complexity.TuringMachine.Build.NDHost
import TCSlib.Complexity.TuringMachine.NDCodeSimulator
import TCSlib.Complexity.TuringMachine.UniversalStartup
import TCSlib.Complexity.ClassNP.ExhaustiveReplay
import TCSlib.Complexity.ClassNP.TMSAT

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The nondeterministic time hierarchy theorem

[AB09, §3.2, Theorem 3.2] ([Coo72]): for time-constructible `f` and `g` with
`f(n+1) = o(g(n))`, `NTIME(f) ⊊ NTIME(g)` — by **lazy diagonalization**, since
a nondeterministic machine cannot flip its own answer directly. The tools are
the clocked universal NDTM of [AB09, Exercise 2.6] at **linear overhead**
(decision CH34-Q8: the strongest form possible, and exactly what puts the
theorem at book strength), the trivial exponential-time deterministic
evaluation of nondeterministic acceptance (the flip at each stage top), and
the linear-overhead coded normal form ([BGW70]-style guess-then-verify).
Phase P3.3 of `AroraBarakChapters3-4Plan.md`, over the code layer of
`TCSlib.Complexity.TuringMachine.NDCodes`.

**Status.** The universal NDTM `Turing.exists_timed_universal_NDTM` and the hierarchy
`Complexity.ntime_hierarchy` are sorried; the exponential decider and the two corollaries are
proved from them.

## Design (declared deviations, each for the audit)

* **The universal is iff-packaged with an unconditional clock.** [AB09]'s
  step 1 says "if `M_i` has not halted in this time, then halt and accept";
  the campaign's universal instead delivers, on every budget-shaped input,
  all-branch halting within `C·(t+1)` **and** acceptance iff the coded
  machine accepts within `t` — so a branch cut by the clock rejects. The
  honest reason this is sound (round-1 finding 7 — it is **not** that every
  coded branch finishes: the normal form guarantees no all-branch halting,
  and its guess phase has infinite non-accepting branches even for total
  deciders): accepting witnesses finish within the forward transfer bound,
  every completed accepting display is sound, and the backward direction
  uses the *original* decider's all-branch halting for truncation. Cut
  branches reject, which can never create a false positive.
* **Linear overhead `C·(t+1)` with `C` per code** (decision CH34-Q8): the
  clock is fused into the interpreter loop — one countdown tick per
  simulated step, with **amortized** linear total cost (a single decrement
  can borrow across the whole counter width; the borrows sum to
  `Σⱼ ν₂(j) ≤ t`, round-1 finding 5) — not a countdown that re-scans the
  counter word at every tick: that is where the received
  `Turing.timed_universal` pays its `C·(t+1)²` (each simulated step costs a
  further `O(|bits t| + 1)`), and the quadratic would surrender the
  book-strength hierarchy. (The received `Complexity.TimeHierarchy.clockTM`
  is a *linear* fused runner, `Complexity.TimeHierarchy.clockTM_spec`; it
  runs its body only from the body's initial configuration and emits a
  negated `[true]`-test, so it is not reused here.)
* **The domination hypothesis carries an extra `f n` addend**:
  `∀ A, A·(f(n+1) + f n + n + 1) ≤ g n` eventually. The `f(n+1)` term is the
  book's `f(n+1) = o(g(n))`; the `f n` term covers the inclusion half
  `NTIME f ⊆ NTIME (g+1)` without assuming `f` monotone (the book reads it
  off `f(n+1) = o(g)` implicitly); the `n + 1` term covers linear
  startup/virtual-input costs. For monotone `f` the extra addend is absorbed,
  so no strength is lost against [AB09].
* **The larger class is `NTIME (g + 1)`**, as in the received deterministic
  `Complexity.time_hierarchy`; the positive-bound form recovers `NTIME g`.
* **Guess first, then interpret (sketch routes; user decisions of
  2026-10-13).** No statement changes. The universal NDTM and the
  diagonalizer guess their whole choice word up front with the bounded
  choice writer and then run deterministically, so no nondeterministic
  counter loop is built (statement note SC-3 is closed by this route); the
  exponential decider is `E(UN)`, the exhaustive replay of the universal;
  nondeterministic codes are interpreted through their replay machine, with
  the deterministic step block unchanged; the universal reads its input
  through a bounded window copy. The host contracts live in
  `TCSlib.Complexity.TuringMachine.ChoiceReplay`,
  `TCSlib.Complexity.TuringMachine.Build.NDHost`,
  `TCSlib.Complexity.TuringMachine.Build.InputWindow`,
  `TCSlib.Complexity.TuringMachine.NDCodeSimulator` and
  `TCSlib.Complexity.ClassNP.ExhaustiveReplay`; the normal form is in
  `TCSlib.Complexity.ClassNP.NDNormalForm`.

## Main results

* `Turing.exists_timed_universal_NDTM` — [AB09, Exercise 2.6] at linear
  overhead (CH34-Q8).
* `Turing.exists_ndAcceptsWithin_decider` — the exponential deterministic
  evaluation ("this trivial exponential simulation … does suffice").
* `Turing.FinNDTM.exists_codeNDTM_accepts_linear` — the linear-overhead coded
  normal form ([BGW70]-style), stated in
  `TCSlib.Complexity.ClassNP.NDNormalForm` (moved there, user 2026-10-17).
* `Complexity.ntime_hierarchy`, `Complexity.ntime_hierarchy_of_pos` —
  [AB09, Theorem 3.2].
* `Complexity.NTIME_linear_ssubset_square` — the ℕ-rendered showcase
  instance (the book displays `NTIME(n) ⊊ NTIME(n^{1.5})`).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.2, Theorem 3.2, Figure 3.1,
  Exercise 2.6.)
* [Coo72] S. Cook, *A hierarchy for nondeterministic time complexity*,
  STOC 1972. (Cited through [AB09]; no external text is required.)
* [BGW70] R. Book, S. Greibach, B. Wegbreit, *Time- and tape-bounded Turing
  acceptors and AFLs*, JCSS 4(6), 1970. (Cited through [AB09]; likewise.)
-/

namespace Turing

/-- **The clocked universal NDTM at linear overhead** ([AB09, Exercise 2.6];
decision CH34-Q8; spec, fill pending — phase P3.3): for every effective
nondeterministic scheme there is a universal NDTM `UN` such that for every
code `α` there is a constant `C` with, on input `⟨⟨bits t, α⟩, x⟩`: every
branch of `UN` halts within `C·(t+1)` steps, and `UN` accepts within
`C·(t+1)` iff the coded machine accepts `x` within `t`.

**Proof sketch.** Guess first, then interpret deterministically (user
decision 1 of 2026-10-13; a declared sketch deviation from the P3.3 route,
which passed choice bits through one per simulated step). `UN` parses the
header and expands `t` into a unary block on a stream tape
(`Turing.expandTM`). It then **guesses its whole choice word up front**: the
bounded choice writer (`Turing.ndWriterTM_run_block`) overwrites the block
with `t` choice bits in `t + 1` steps, the same time on every branch, and
the stream head is rewound (`Turing.skipBackTM`). Everything after the guess
is deterministic: the interpreter core `Turing.exists_ndInterpreterCore`,
run on the guessed stream `s`. Per code, the core installs the serialization
of the decoded machine's **replay machine** (`Turing.NDTM.replayTM`, the
coded NDTM as a deterministic three-work-tape machine that reads its choices
from the last tape; `Turing.exists_replayCanonizer`; user decision 3). It
copies the input window `x.take t` (`Turing.exists_inputWindowCopyTM`; the
whole `x` is never copied, so the budget need not dominate `|x|`, and input
locality, `Turing.NDTM.runWith_initCfg_take`, makes the window enough; user
decision 5). It then runs the deterministic clocked interpreter loop: one
round of the step block H2, at three work tapes, per simulated step, hosted
by Z1 on the window, with the countdown of the budget word `bits t`
**fused into the loop** and **amortized**, not pointwise (round-1 finding
5): a decrement from `j` borrows across `ν₂(j)` trailing zeros, unbounded
for a single tick, but the borrows of `t` ticks sum to at most `t`
(`Turing.counterOverhead_le_of_le`). It is not a countdown that re-scans
the counter word at every tick, which is where the received
`Turing.timed_universal` pays its `C·(t+1)²`, exactly what decision CH34-Q8
forbids. Per simulated step the remaining cost is one table round,
`O(|table|)`, a constant for fixed `α`, absorbed into `C`. The core accepts
iff the coded machine's branch along `s.take t` halts with output `[true]`.
The assembly is the nondeterministic phase host `Turing.NDTM.phaseHostND`
over a deterministic prefix, the writer and the deterministic core: the
transfer `Turing.NDTM.runWith_mapState_of_agreeOn_det` carries each
deterministic contract to every branch, and the replay lemma
`Turing.NDTM.replayTM_runFrom` identifies the core's simulated run with the
coded branch. So every branch of `UN` halts within `C·(t+1)`, and `UN`
accepts iff some guessed `s` is an accepting branch of length `t`
(`Turing.FinNDTM.AcceptsWithin.mono` absorbs the timing slack). No
nondeterministic counter loop is needed (statement note SC-3 dissolves): no
choice occurs inside a multi-step round. Linear overhead (CH34-Q8) is kept:
the expansion, the guess, the rewind and the window copy each cost
`O(t + 1)`. Fill obligations, named: the startup and per-code installation;
the choice writer's bounded contract; the window copy; the interpreter core
(H1's hosted clock over the step block at three work tapes, harvested with
H2's promotion); the guess-then-run assembly; the `C`-ledger per code. -/
theorem exists_timed_universal_NDTM (c : EffectiveNDMachineCode) :
    ∃ UN : FinNDTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ (x : List Bool) (t : ℕ),
      UN.tm.HaltsWithin (pairEncode (pairEncode (Nat.bits t) α) x) (C * (t + 1)) ∧
      (UN.AcceptsWithin (pairEncode (pairEncode (Nat.bits t) α) x) (C * (t + 1)) ↔
        (c.decode α).toFinNDTM.AcceptsWithin x t) := by
  sorry

/-- **Nondeterministic acceptance evaluates deterministically in exponential
time** ([AB09, §3.2: "this trivial exponential simulation … does suffice to
establish a hierarchy theorem"]): a
deterministic machine decides, on input `⟨⟨bits t, α⟩, x⟩`, whether the coded
machine accepts `x` within `t`, in time `C · 2^{C·(t+1)}`. This is the flip
at each stage top of the lazy diagonalization — the only place the answer is
ever negated.

**Proof sketch.** `BF := E(UN)` (user decision 2 of 2026-10-13; a declared
sketch deviation from the P3.3 route, which replayed every choice word
through the universal's deterministic core with an inter-replay cleanup):
the exhaustive replay `Turing.FinNDTM.exists_exhaustiveDecider` of the fixed
universal NDTM `UN` of `Turing.exists_timed_universal_NDTM`. On
`⟨⟨bits t, α⟩, x⟩` every branch of `UN` halts within `C_α·(t+1)`, so `E`
decides `UN`'s acceptance within that bound, which is the coded machine's
acceptance within `t`, in time `C_E·2^{C_E·(C_α·(t+1)+1)} ≤ C·2^{C·(t+1)}`
with `C := C_E·(C_α+1)`. This derivation is proved, as
`Turing.ndAcceptsWithin_decider_of_universal`. `E` itself is
`Turing.FinNDTM.exists_exhaustiveDecider`, proved (iterative deepening over the
choice words of the fixed `UN`, each replayed by its replay machine under the
step-clocked runner, with a window clear between replays; no `|x|` term), so the
decider's only open dependency is the universal NDTM. The proof applies
`Turing.ndAcceptsWithin_decider_of_universal` to `Turing.exists_timed_universal_NDTM`. -/
theorem exists_ndAcceptsWithin_decider (c : EffectiveNDMachineCode) :
    ∃ BF : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ (x : List Bool) (t : ℕ),
      ((c.decode α).toFinNDTM.AcceptsWithin x t →
        BF.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [true]
          (C * 2 ^ (C * (t + 1)))) ∧
      (¬(c.decode α).toFinNDTM.AcceptsWithin x t →
        BF.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [false]
          (C * 2 ^ (C * (t + 1)))) := by
  exact ndAcceptsWithin_decider_of_universal c (exists_timed_universal_NDTM c)

end Turing

namespace Complexity

open Turing

/-- **The nondeterministic time hierarchy theorem** ([AB09, Theorem 3.2];
[Coo72]; spec, fill pending — phase P3.3, **the phase summit**): for
time-constructible `f` and `g`, if every constant multiple of
`f(n+1) + f(n) + n + 1` is eventually below `g(n)` — the book's
`f(n+1) = o(g(n))` with the two declared addends (module docstring) — then
`NTIME f ⊊ NTIME (g + 1)`. Book strength: the overhead on `f` is **linear**
(decision CH34-Q8), in contrast to the received deterministic hierarchy's
square.

**Proof sketch.** *Inclusion:* the hypothesis at `A = 1` gives
`f n ≤ g n` eventually (the `f n` addend); finitely many lengths absorb into
the constant (the received `Complexity.time_hierarchy` `F`-sum idiom; no
monotonicity needed). *Strictness* is lazy diagonalization [AB09, proof of
Theorem 3.2 and Figure 3.1], over a scheme fixed by
`Turing.exists_effectiveNDMachineCode`, rebuilt per the round-1 audit (its
two majors: a per-code universal constant cannot be absorbed by choosing a
padded large index — padding preserves `decode`, no law preserves cost —
and the stage locator must be computable within the allowance). The
repaired construction: **(i) the fixed-code stage schedule**: stage
`i = pair(j, r)` runs the `j`-th binary string `α_j` (unranking), so every
code recurs at infinitely many stages — no padded-index selection, and the
alleged decider's constants stay fixed along its own stage subsequence (the
same discipline as the P3.2 enumeration's repetition coordinate).
**(ii) the `f`-adaptive ladder with capped comparisons**: with
`a := ℓ_i + 1` the stage bottom, `T*_i := (f a + a + 1)²` and
`ℓ_{i+1} := 2^{(T*_i)²}`, seeded at `ℓ₀ := 2` with the finitely many
lengths at or below the seed rejected (round-2 finding 1 fixed the seed
and this formula as *the* sequence — the round-2 pack's paraphrase
differed by an offset, a pack erratum acknowledged in the resolutions) —
an explicit recurrence over `f`'s constructibility witness; the locator
compares `n` against `ℓ_{i+1}` by **bit-length arithmetic with capped
witness runs** (the ladder value is
never materialized in unary, and a capped run that fails to finish itself
decides the comparison: an unfinished `f`-witness already certifies
`ℓ_{i+1} > n`), with the completed stages' costs summing geometrically and
the one incomplete evaluation capped — total `O(g n + 1)` after computing
`g n` once by `g`'s witness. **(iii) the self-clocked mid-rung, guess first** (user decision 1 of
2026-10-13; a declared sketch deviation from passing choice bits through):
right after computing `g n`, `D` **guesses a stream of `g n` choice bits**
with the bounded choice writer (`Turing.ndWriterTM_run_block`), its only
nondeterministic phase; every later phase is deterministic. For
`ℓ_i < n < ℓ_{i+1}`, `D` materializes `⟨⟨bits (g n), α_j⟩, 1^{n+1}⟩` and
runs the deterministic interpreter core `Turing.exists_ndInterpreterCore`
on it, hosted by Z1, with the guessed stream, at nominal simulated budget
`g n`, under `D`'s **own step-clocked countdown of `K·(g n + 1)` steps**
(the step clock `Turing.exists_stepClockTMVia`, shared with the B6 hosts)
— `K` fixed by `D`'s architecture, independent of the code, **with the
allowance split stated** (round-2 finding 2): a fixed share is reserved
ahead of simulation for the one `g`-witness run (bounded by its own
`c_g·(g n + 1)` clause — it runs *before* the countdown exists and is not
cut by it), for the guess, for budget and countdown preparation, and for
the worst single binary borrow; the **prefix-bound obligation is a clause
of the core's contract**: when the simulated branch halts at `t' ≤ g n`,
the core stops within `C_α·(t' + |x| + |bits (g n)| + 1)` (here
`|x| = n + 1`, the bounded window copy of user decision 5), so the
remaining share covers the relevant branches; `D` accepts iff the core
accepts within the countdown, and branches cut by the countdown **reject**
(sound: a cut branch is non-accepting, and completed accepting simulations
are sound).
**(iv) the top rung**: at `n = ℓ_{i+1}`, `D` runs `BF` on
`⟨bits T*_i, α_j, 1^{a}⟩` under the same self-cap and **flips** a completed
verdict (default answer if the cap trips); non-unary inputs reject.
`D ∈ NTIME (g + 1)` **by construction**: every phase is either bounded
within its reserved share of the `K·(g n + 1)` allowance or run under the
step-clock cap, uniformly in the code. *The chain, for the alleged
decider:* given `N` deciding `L(D)` within `c₀ · f`, take `M'` and `C₁`
from `Turing.FinNDTM.exists_codeNDTM_accepts_linear N` and let `α` be
`M'`'s code with its **fixed** interpreter constant `C_α`. Mid-rung, at the
late stages of `α`'s subsequence: by the core's prefix clause the genuine
simulation of an accepting `N`-branch costs at most
`C_α·(C₁·(c₀·f(n+1) + 1) + (n + 1) + |bits (g n)| + 1)`, which is at most
`A*·(f(n+1) + n + 1) + C_α·|bits (g n)|` host steps with
`A* := C_α·(C₁·c₀ + C₁ + 2) + 1` **fixed**, and the domination hypothesis
(its `f(n+1)` and `n + 1` addends; the logarithmic term is `o(g n)`) puts
that below `K·(g n + 1)` eventually — so the countdown never cuts the
relevant branches, and
`D(1^n) = [M'` accepts `1^{n+1}` within the window`] = [1^{n+1} ∈ L(D)]`
(forward by the linear transfer and `AcceptsWithin.mono`; backward by the
unbounded transfer plus truncation at `N`'s own all-branch budget,
`Turing.NDTM.runWith_of_halt`) — the chain (3.3). Top rung: the flip needs
the transfer at the **bottom** length `a`:
`T*_i = (f a + a + 1)² ≥ C₁·(c₀·f a + 1)` eventually — the square against
fixed constants, no `g a` comparison needed; the hypothesis's `f n` addend
serves the inclusion half (round-2 note 3) — and `BF`'s cost
`C_BF·2^{C_BF·(T*_i + 1)} ≤ K·(g n + 1)` eventually along the subsequence
since `g n ≥ n = 2^{(T*_i)²}` — the ladder's square in the exponent
outruns any fixed linear exponent — which is the chain's (3.4); `N`
agreeing with `D` on the whole stage collapses (3.3) into (3.4)'s flip,
the contradiction of [AB09, Figure 3.1]. Fill obligations, named: the
schedule and unranking; the ladder recurrence and the capped-comparison
locator with its amortized ledger; the guess and the step-clocked
interpreter core at fixed `K`; the two transfer instantiations (at `f(n+1)` mid-rung, at `f a`
bottom); the chain induction. -/
theorem ntime_hierarchy {f g : ℕ → ℕ} (hf : TimeConstructible f)
    (hg : TimeConstructible g)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f (n + 1) + f n + n + 1) ≤ g n) :
    NTIME f ⊂ NTIME (fun n => g n + 1) := by
  sorry

/-- **The nondeterministic time hierarchy for a positive bound**
([AB09, Theorem 3.2]; spec, fill pending): as `Complexity.ntime_hierarchy`,
with the larger class exactly `NTIME g` when `g` never vanishes — mirroring
`Complexity.time_hierarchy_of_pos`.

**Proof sketch.** `c·(g n + 1) ≤ 2c · g n` when `g n ≥ 1`, so
`NTIME (g + 1) ⊆ NTIME g`; the reverse is `Complexity.NTIME.mono`; conclude
from `Complexity.ntime_hierarchy`.

Formally, the factor `2` is absorbed into the membership witness's constant
(`Complexity.mem_NTIME_iff`, `Turing.FinNDTM.decidesInTime_iff`). -/
theorem ntime_hierarchy_of_pos {f g : ℕ → ℕ} (hf : TimeConstructible f)
    (hg : TimeConstructible g) (hpos : ∀ n, 0 < g n)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f (n + 1) + f n + n + 1) ≤ g n) :
    NTIME f ⊂ NTIME g := by
  have hback : NTIME (fun n => g n + 1) ⊆ NTIME g := by
    intro L hL
    have hscale : L ∈ NTIME (fun n => 2 * g n) :=
      NTIME.mono (fun n => by have := hpos n; omega) hL
    obtain ⟨a, N, hN⟩ := mem_NTIME_iff.mp hscale
    apply mem_NTIME_iff.mpr
    refine ⟨a * 2, N, FinNDTM.decidesInTime_iff.mpr ?_⟩
    intro x
    simpa only [Nat.mul_assoc] using (FinNDTM.decidesInTime_iff.mp hN x)
  have heq : NTIME (fun n => g n + 1) = NTIME g :=
    Set.Subset.antisymm hback (NTIME.mono (fun n => Nat.le_succ (g n)))
  simpa only [heq] using ntime_hierarchy hf hg hfg

/-- **The showcase separation** (spec, fill pending — phase P3.3):
`NTIME(n + 1) ⊊ NTIME((n + 1)²)`, the ℕ-rendering of the book's displayed
instance `NTIME(n) ⊊ NTIME(n^{1.5})` (fractional exponents have no ℕ-valued
normal form in the campaign; the square is the nearest constructible bound).
This is exactly what decision CH34-Q8 buys: under the received
**deterministic** hierarchy's quadratic overhead, `A·(2n + 2)² ≤ (n + 1)²`
fails for every **positive** `A` (round-1 finding 9; `A = 0` holds
vacuously), so no square-overhead route separates these two classes
— the linear-overhead universal is load-bearing.

**Proof sketch.** `Complexity.ntime_hierarchy_of_pos` at `f := n + 1`,
`g := (n + 1)²`: positivity is immediate; domination is
`A·((n + 2) + (n + 1) + n + 1) = A·(3n + 4) ≤ (n + 1)²` for `n ≥ 3A + 4`.
The two constructibility witnesses are `Complexity.timeConstructible_poly` at
`(C, c) = (1, 0)` and `(1, 1)`; domination takes `N = 3A + 4` and multiplies `N ≤ n` by `n`. -/
theorem NTIME_linear_ssubset_square :
    NTIME (fun n => n + 1) ⊂ NTIME (fun n => (n + 1) ^ 2) := by
  have hf : TimeConstructible (fun n => n + 1) := by
    have h : (fun n : ℕ => 1 * (n + 1) ^ (0 + 1)) = (fun n => n + 1) := by
      funext n
      simp only [Nat.zero_add, pow_one, one_mul]
    rw [← h]
    exact timeConstructible_poly 1 0 (by decide)
  have hg : TimeConstructible (fun n => (n + 1) ^ 2) := by
    have h : (fun n : ℕ => 1 * (n + 1) ^ (1 + 1)) = (fun n => (n + 1) ^ 2) := by
      funext n
      simp only [one_mul]
    rw [← h]
    exact timeConstructible_poly 1 1 (by decide)
  apply ntime_hierarchy_of_pos hf hg
  · intro n
    exact pow_pos (Nat.succ_pos n) _
  · intro A
    refine ⟨3 * A + 4, fun n hn => ?_⟩
    nlinarith [Nat.mul_le_mul_right n hn]

end Complexity
