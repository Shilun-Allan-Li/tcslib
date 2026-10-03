/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Nat.Bits
import TCSlib.Complexity.TuringMachine.Build.Convention
import TCSlib.Complexity.TuringMachine.Composition

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: the bounded loop

The control centerpiece of the machine-construction library
(`machine-library-design.md` §5, L): a bounded loop with tape-resident
round state, specified at two granularities.

* `Turing.loop_run` is the **summation lemma**: given a family of round
  configurations with an accept-or-advance contract, the run from round 0
  halts within the summed budget with the loop's single verdict bit. It is
  the generic form of the Chapter-2 enumerator's proved private
  `enumLoop_run`, whose proof is the harvest template.
* `Turing.FinTM.exists_loopTM` is the **constructive combinator**: from a
  body machine whose startup and rounds are `Turing.Cfg.ofWords` seam
  contracts, there is one finite machine iterating the body under a fuel
  bound, with the exhaustion rejection and the total polynomial budget
  owned by the combinator. It is the generic form of the enumerator batch's
  admitted `enumMachine_contracts` — the statement that every fill batch
  died re-deriving concretely — turned into a once-and-for-all interface.

**Status: spec phase.** Both theorems and the seam helper are stated; the
proofs are the library fill's risk concentration (continuation budget
anticipated, frozen design §10). New Chapter-1 surface, flagged for the
shared infrastructure audit round.

## The round discipline

Round state is one word on the body's tape 0; every other body tape is
scratch, blank at both seam ends of a round (body-restores-scratch, frozen
design decision 9.2 — a body proves its own restore from its own invariant;
the generic clearing fallback via the visited-region bound of
`TCSlib.Complexity.TuringMachine.Sweep` is recorded in the design document).
A round either **accepts** — halts with the single verdict `[true]`,
nothing else ever emitted — or **advances** to the seam carrying the
stepped state word. The combinator caps the rounds at a fuel bound
computed from the input length only, rejecting with `[false]` on
exhaustion; acceptance within fuel is therefore the Boolean
`(List.range (R n + 1)).any …` of the abstract orbit, which is the shape
the Chapter-2 enumerator consumes.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2; the clocked-loop discipline is
  the folklore engine of the enumeration and diagonalization arguments,
  §2.1 / §3.1–3.2.)
-/

namespace Turing

/-- Round state on tape 0, scratch blank: the standard word assignment for
a loop body's seam configurations. -/
def stateWord (k : ℕ) (s : List Bool) : Fin k → List Bool :=
  fun i => if (i : ℕ) = 0 then s else []

/-- **The loop summation lemma** (spec, fill pending — the generic form of
the enumerator's proved `enumLoop_run`, which is the harvest template).
Given round configurations `cfg 0, …, cfg N` of one machine with empty
outputs, such that each round `j < N` within budget `B` either halts with
the verdict `[true]` (when `accept j`) or reaches `cfg (j+1)`, and the
exhaustion round `cfg N` halts with `[false]` within `B`: the run from
`cfg 0` halts within `(N + 1) · B` steps with the single verdict bit
`(List.range N).any accept`.

**Proof sketch.** Induction on the first accepting round (or `N` when none
accepts), composing the advance segments with
`Turing.MultiTapeTM.runFrom_add` and absorbing halted tails with
`Turing.MultiTapeTM.runFrom_of_halt`; empty round outputs make the final
output exactly the one emitted verdict. -/
theorem loop_run {k : ℕ} {S : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (cfg : ℕ → Cfg k Bool S x)
    (accept : ℕ → Bool) (B N : ℕ)
    (hout : ∀ j ≤ N, (cfg j).output = [])
    (hend : ∃ t ≤ B, (tm.runFrom (cfg N) t).state = none ∧
      (tm.runFrom (cfg N) t).output = [false])
    (hround : ∀ j < N, ∃ t ≤ B,
      if accept j then
        (tm.runFrom (cfg j) t).state = none ∧
          (tm.runFrom (cfg j) t).output = [true]
      else tm.runFrom (cfg j) t = cfg (j + 1)) :
    ∃ t ≤ (N + 1) * B, (tm.runFrom (cfg 0) t).state = none ∧
      (tm.runFrom (cfg 0) t).output = [(List.range N).any accept] := by
  sorry

end Turing

namespace Turing.FinTM

/-- **The loop combinator** (spec, fill pending — the generic form of the
enumerator batch's admitted `enumMachine_contracts`; the construction is
the library fill's risk concentration). Given a fuel machine and a body
machine with

* a **fuel** contract: `F` writes the round bound `R |x|` in binary within
  `T |x|` (an arbitrary `R : ℕ → ℕ` is not machine-evaluable, so the
  combinator must be handed its fuel; the enumerator's `2^w` and the
  split search's `n + 1` both have immediately writable bit patterns),
* a **startup** contract: from its genuine initial configuration on `x`
  the body reaches, within `T |x|`, the seam `Turing.Cfg.ofWords` carrying
  the initial state word `s0 x` on tape 0 (scratch blank), **without
  visiting the anchor state earlier**, and
* a **round** contract: from the seam carrying any state word `s` it
  either halts with the verdict `[true]` within `T |x|` (when `acceptF s`)
  or reaches the seam carrying `stepF s` within `T |x|` — in both cases
  **without re-entering the anchor state strictly between the seam and
  that endpoint**,

there is one finite machine that, on every input `x`, emits the single
verdict bit of the first `R |x| + 1` orbit points
`s0 x, stepF (s0 x), …, stepF^[R |x|] (s0 x)` — `[false]` when none
accepts (fuel exhaustion) — within a constant multiple of
`(T |x| + 1) · (R |x| + 2)`.

The two discipline clauses are load-bearing (maintainer pre-audit
adversarial pass, recorded for the shared infrastructure round): the
combinator's host detects round boundaries **as entries into the embedded
anchor state**, so a mid-round anchor visit would decrement the fuel
early and change the computed function; and without the fuel machine the
statement would assert a finite machine materializing an arbitrary
natural-number function of the input length.

**Proof sketch.** The combinator machine runs `F` relocated-and-captured
to lay the fuel word on a counter tape, rewinds, and embeds the body via
the W1 capture discipline of
`TCSlib.Complexity.TuringMachine.Build.Wrappers` (the body's verdict is
captured, never physically emitted until the end). On each entry into the
embedded anchor it decrements the binary counter in place; the borrow
discipline is amortized — total countdown cost over all rounds is linear
in `R |x|` plus the counter width, and exhaustion is detected exactly
when a borrow runs off the counter's end, which is what keeps the stated
budget at `(T + 1) · (R + 2)` rather than acquiring a logarithmic factor.
`Turing.loop_run` sums the seam family; acceptance surfaces as the
captured halt (`[true]`), and borrow-overflow emits the exhaustion
rejection (`[false]`). Phase overheads are absorbed into `c`. -/
theorem exists_loopTM (body F : FinTM Bool) (anchor : body.State)
    (stepF : List Bool → List Bool) (acceptF : List Bool → Bool)
    (s0 : List Bool → List Bool) (R T : ℕ → ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T)
    (hstart : ∀ x : List Bool, ∃ t ≤ T x.length,
      (∀ t' < t,
        (body.tm.runFrom (body.tm.initCfg x) t').state ≠ some anchor) ∧
      body.tm.runFrom (body.tm.initCfg x) t =
        Cfg.ofWords anchor (stateWord body.k (s0 x)))
    (hround : ∀ (x : List Bool) (s : List Bool),
      ∃ t ≤ T x.length,
        (∀ t', 0 < t' → t' < t →
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t').state
              ≠ some anchor) ∧
        if acceptF s then
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).state
              = none ∧
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).output
              = [true]
        else
          body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t =
              Cfg.ofWords anchor (stateWord body.k (stepF s))) :
    ∃ (E : FinTM Bool) (c : ℕ),
      E.ComputesFunInTime
        (fun x => [(List.range (R x.length + 1)).any
          fun i => acceptF (stepF^[i] (s0 x))])
        (fun n => c * (T n + 1) * (R n + 2)) := by
  sorry

end Turing.FinTM
