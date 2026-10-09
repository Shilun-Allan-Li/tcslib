/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.NDCodes
import TCSlib.Complexity.ClassNP.NTIME
import TCSlib.Complexity.ClassP.TimeConstructible

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

**Status: statement skeleton (phase P3.3).** Every contract is sorried with a
sketch naming its fill obligations. The `Diagonalization.lean` facade is
frozen under the live P3.2 gate; this module is wired through the root import
only, with facade wiring at that gate's close (the P4.2 precedent).

## Design (declared deviations, each for the audit)

* **The universal is iff-packaged with an unconditional clock.** [AB09]'s
  step 1 says "if `M_i` has not halted in this time, then halt and accept";
  the campaign's universal instead delivers, on every budget-shaped input,
  all-branch halting within `C·(t+1)` **and** acceptance iff the coded
  machine accepts within `t`. Under the contradiction's assumption the coded
  machine beats the budget, so the timeout polarity never bites — the
  packaging is a simplification, not a strengthening.
* **Linear overhead `C·(t+1)` with `C` per code** (decision CH34-Q8): the
  clock is fused into the interpreter loop (a countdown tick per simulated
  step), not the deterministic `clockTM`'s re-scan — the received
  `Turing.timed_universal` pays `C·(t+1)²` exactly there, and the quadratic
  would surrender the book-strength hierarchy.
* **The domination hypothesis carries an extra `f n` addend**:
  `∀ A, A·(f(n+1) + f n + n + 1) ≤ g n` eventually. The `f(n+1)` term is the
  book's `f(n+1) = o(g(n))`; the `f n` term covers the inclusion half
  `NTIME f ⊆ NTIME (g+1)` without assuming `f` monotone (the book reads it
  off `f(n+1) = o(g)` implicitly); the `n + 1` term covers linear
  startup/virtual-input costs. For monotone `f` the extra addend is absorbed,
  so no strength is lost against [AB09].
* **The larger class is `NTIME (g + 1)`**, as in the received deterministic
  `Complexity.time_hierarchy`; the positive-bound form recovers `NTIME g`.

## Main results (all sorried; phase-P3.3 statements)

* `Turing.exists_timed_universal_NDTM` — [AB09, Exercise 2.6] at linear
  overhead (CH34-Q8).
* `Turing.exists_ndAcceptsWithin_decider` — the exponential deterministic
  evaluation ("this trivial exponential simulation … does suffice").
* `Turing.FinNDTM.exists_codeNDTM_accepts_linear` — the linear-overhead coded
  normal form ([BGW70]-style).
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

**Proof sketch.** Direct interpretation, not guess-then-verify: the coded
normal form has two work tapes (`Turing.CodeNDTM`), so `UN` maintains both
simulated tapes on two dedicated real tapes, holds the canonized table
(`Turing.EffectiveNDMachineCode.canonizer`) on a third, reads `x` in place by
the received virtual-input startup discipline
(`TCSlib.Complexity.TuringMachine.UniversalStartup` — no copying, so the
budget need not dominate `|x|`), and **passes its own choice bits through**:
at each simulated step boundary `UN` consumes one choice bit and applies the
corresponding table row, so `UN`'s branches at length `C·(t+1)` project onto
the coded machine's branches at length `t` (the alignment lemma, both
directions of the iff; deterministic bookkeeping steps ignore their bits, the
binary-choice semantics' absorption). The clock is the budget word `bits t`
counted **down one tick per simulated step, fused into the interpreter loop**
— not the deterministic `clockTM` re-scan, whose `C·(t+1)²` is exactly what
decision CH34-Q8 forbids — and every branch halts when the counter dies or
the simulated machine halts, whichever is first. Per simulated step the cost
is one table scan plus the tick, `O(|table|)` — a constant for fixed `α`,
absorbed into `C`. Fill obligations, named: the startup reuse at the
ND record format; the fused countdown; the two alignment directions; the
halting absorption on exhausted budgets; the `C`-ledger per code. -/
theorem exists_timed_universal_NDTM (c : EffectiveNDMachineCode) :
    ∃ UN : FinNDTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ (x : List Bool) (t : ℕ),
      UN.tm.HaltsWithin (pairEncode (pairEncode (Nat.bits t) α) x) (C * (t + 1)) ∧
      (UN.AcceptsWithin (pairEncode (pairEncode (Nat.bits t) α) x) (C * (t + 1)) ↔
        (c.decode α).toFinNDTM.AcceptsWithin x t) := by
  sorry

/-- **Nondeterministic acceptance evaluates deterministically in exponential
time** ([AB09, §3.2: "this trivial exponential simulation … does suffice to
establish a hierarchy theorem"]; spec, fill pending — phase P3.3): a
deterministic machine decides, on input `⟨⟨bits t, α⟩, x⟩`, whether the coded
machine accepts `x` within `t`, in time `C · 2^{C·(t+1)}`. This is the flip
at each stage top of the lazy diagonalization — the only place the answer is
ever negated.

**Proof sketch.** Enumerate the `2^t` choice words on a binary counter tape
in lexicographic order (`incrementTM` discipline); replay each word through
the deterministic core of `Turing.exists_timed_universal_NDTM`'s interpreter
— choices read from the counter instead of guessed — at cost `C_α·(t+1)` per
replay (virtual input, no copying), clearing the two simulated tapes between
replays (`O(t)` each); emit `[true]` on the first accepting replay, `[false]`
after the last. Ledger: `2^t · O_α(t+1) + 2^t` increments `≤ C·2^{C·(t+1)}`.
Fill obligations, named: the counter-driven replay loop (a §12 loop/catalog
consumer); the inter-replay cleanup; the first-accept/last-reject control;
the exponent arithmetic. -/
theorem exists_ndAcceptsWithin_decider (c : EffectiveNDMachineCode) :
    ∃ BF : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ (x : List Bool) (t : ℕ),
      ((c.decode α).toFinNDTM.AcceptsWithin x t →
        BF.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [true]
          (C * 2 ^ (C * (t + 1)))) ∧
      (¬(c.decode α).toFinNDTM.AcceptsWithin x t →
        BF.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [false]
          (C * 2 ^ (C * (t + 1)))) := by
  sorry

namespace FinNDTM

/-- **The linear-overhead coded normal form** ([BGW70]-style guess-then-verify,
cited through [AB09, §3.2]; spec, fill pending — phase P3.3): every
nondeterministic machine has a coded (two-work-tape) equivalent whose
acceptance tracks the original's at linear time overhead — forward with the
explicit constant, backward in unbounded form (the consumer recovers the
budgeted form from the original's all-branch halting by the truncation
argument, `Turing.NDTM.runWith_of_halt`).

**Proof sketch.** Guess-then-verify, the reason codes carry **two** work
tapes: on tape A the simulator guesses, left to right and one choice bit per
guessed bit, the full display sequence of a `k`-tape run of `N` — per step
the choice bit, the state, the `k + 1` scanned symbols, and the action record
(`O_N(1)` cells per step) — checking the **control-local** part on the fly
(each record must follow from its predecessor by `N`'s table, hardwired in
the simulator's finite control). Then the non-local reads are verified in
`k + 1` sweeps: the input claims by replaying the claimed input-head moves
against the real input tape, and each work tape `j` by replaying tape `j` on
tape B — B's head tracks tape `j`'s claimed head, so each step checks the
claimed read against B's cell and applies the claimed write at unit cost —
rewinding A and clearing B between sweeps. Total `O_N(k · t) = C·(t+1)`.
Forward transfer: a genuine accepting run of length `t` yields the accepting
display, guessed and verified within `C·(t+1)`. Backward: a verified display
**is** a genuine run (the sweeps force consistency), so an accepting branch
of the simulator exhibits an accepting branch of `N` at some length —
unbounded on purpose: runaway guessing branches never accept, and no
all-branch-halting claim is made for the simulator. State-space finiteness
packages as `Fin` by the received relabeling
(`Turing.MultiTapeTM.relabelState`, the `exists_codeTM` precedent). Fill
obligations, named: the display format and its on-the-fly control check; the
`k + 1` verification sweeps; the two transfer directions; the relabeling
packaging. -/
theorem exists_codeNDTM_accepts_linear (N : FinNDTM Bool) :
    ∃ (M : CodeNDTM) (C : ℕ),
      (∀ (x : List Bool) (t : ℕ),
        N.AcceptsWithin x t → M.toFinNDTM.AcceptsWithin x (C * (t + 1))) ∧
      (∀ (x : List Bool) (t : ℕ),
        M.toFinNDTM.AcceptsWithin x t → ∃ t', N.AcceptsWithin x t') := by
  sorry

end FinNDTM

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
the constant (the received `Complexity.time_hierarchy` `F`-sum idiom).
*Strictness* is lazy diagonalization [AB09, proof of Theorem 3.2 and
Figure 3.1], over a scheme fixed by `Turing.exists_effectiveNDMachineCode`
(the fill introduces the global scheme constant, mirroring
`Complexity.TimeHierarchy.code`), with `UN` and `BF` its universal and
evaluator. Fill obligations, named: **(i) the stage ladder**
`ℓ₁ := 2`, `ℓ_{i+1} := (BF's bound at budget(ℓ_i + 1)) + ℓ_i + 1`, and its
locator machine finding the sandwich `ℓ_i < n ≤ ℓ_{i+1}` within `O(g n)`
(iterated `f`-witness runs and doubling counters — the book's `O(n^{1.5})`
locating step); **(ii) the diagonal NDTM `D`**: on `1^n` with
`ℓ_i < n < ℓ_{i+1}`, run `UN` on the virtual input
`⟨bits (budget n), α_i, 1^{n+1}⟩` — `α_i` the `i`-th binary string
(unranking), `budget` computed from `g`'s constructibility witness — and
answer `UN`'s verdict; on `1^{ℓ_{i+1}}`, run `BF` at the stage bottom
`⟨bits (budget (ℓ_i + 1)), α_i, 1^{ℓ_i + 1}⟩` and **flip**; reject non-unary
inputs; **(iii) `D ∈ NTIME (g + 1)`**: `UN`'s unconditional all-branch clock,
`BF`'s determinism with its bound at most `ℓ_{i+1} ≤ n ≤ g n` by the ladder's
very definition and constructibility's floor `n ≤ g n`, and the locator
ledger; **(iv) `L(D) ∉ NTIME f`**: given `N` deciding `L(D)` within
`c₀ · f`, take `M'` and `C₁` from
`Turing.FinNDTM.exists_codeNDTM_accepts_linear N`, and by true-padding
(`Turing.NDMachineCode.decode_encode_pad`) pick `i` arbitrarily large with
`decode α_i = M'` and `C₁·(c₀·f(n+1) + 1) ≤ budget n` on the whole stage
(the domination hypothesis at the assembled constant — the `f(n+1)` and
`n + 1` addends); then mid-rung `D(1^n) = [M' accepts 1^{n+1} within budget]`
equals `[1^{n+1} ∈ L(D)]` — forward by the linear transfer and
`Turing.FinNDTM.AcceptsWithin.mono`, backward by the unbounded transfer plus
the truncation of `N`'s accepting word at `N`'s own all-branch budget
(`Turing.NDTM.runWith_of_halt`) — which is the chain (3.3), while the top
rung flips the stage bottom, (3.4); `N` agreeing with `D` on the whole stage
collapses the chain into the contradiction of [AB09, Figure 3.1]. -/
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
from `Complexity.ntime_hierarchy`. -/
theorem ntime_hierarchy_of_pos {f g : ℕ → ℕ} (hf : TimeConstructible f)
    (hg : TimeConstructible g) (hpos : ∀ n, 0 < g n)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f (n + 1) + f n + n + 1) ≤ g n) :
    NTIME f ⊂ NTIME g := by
  sorry

/-- **The showcase separation** (spec, fill pending — phase P3.3):
`NTIME(n + 1) ⊊ NTIME((n + 1)²)`, the ℕ-rendering of the book's displayed
instance `NTIME(n) ⊊ NTIME(n^{1.5})` (fractional exponents have no ℕ-valued
normal form in the campaign; the square is the nearest constructible bound).
This is exactly what decision CH34-Q8 buys: under the received
**deterministic** hierarchy's quadratic overhead, `A·(2n + 2)² ≤ (n + 1)²`
fails for every `A`, so no square-overhead route separates these two classes
— the linear-overhead universal is load-bearing.

**Proof sketch.** `Complexity.ntime_hierarchy_of_pos` at `f := n + 1`,
`g := (n + 1)²`: positivity is immediate; domination is
`A·((n + 2) + (n + 1) + n + 1) = A·(3n + 4) ≤ (n + 1)²` for `n ≥ 3A + 4`.
Fill obligations, named: the two constructibility witnesses —
`TimeConstructible (n + 1)` (dominance `n ≤ n + 1`; an input-scan counter
emitting `bits (n + 1)`, the `Complexity.timeConstructible_id` idiom) and
`TimeConstructible ((n + 1)²)` (dominance `n ≤ (n + 1)²`; the grade-school
square of the scanned length within `O((n + 1)²)` steps — a §12
catalog/counter consumer). -/
theorem NTIME_linear_ssubset_square :
    NTIME (fun n => n + 1) ⊂ NTIME (fun n => (n + 1) ^ 2) := by
  sorry

end Complexity
