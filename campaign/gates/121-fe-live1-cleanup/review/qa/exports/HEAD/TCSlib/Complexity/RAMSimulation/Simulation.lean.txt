/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Programs.WordRAM.Extended
import TCSlib.Complexity.RAMSimulation.WordSize
import TCSlib.Complexity.ClassNP.NTIME
import TCSlib.Complexity.TuringMachine.NondeterministicSpace

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Stage 2: the word RAM on Turing machines

A program `P` of the extended word RAM (`WordRAM.XProgram`: the nine vendored instructions and
`rdIn`, `emit`, `coin`, `half`) is run on an input `x`, a coin stream `ρ` and a word size
`W = W (|x|)`. Stage 2 (backlog PROG-4; design §15a, §15d, §16b) says that one `FinTM Bool`
simulates it, instruction by instruction, with a polynomial time overhead and a space bound
linear in the number of cells touched times the word size: with `n = |x|`,

* time `TW n + A·(t + 1)·(f·(W + 1) + W² + n + 1)`;
* space `SW n + A·(f·(W + 1) + W + logSpace n + 1)`;

where `t` bounds the RAM's steps, `f` the number of cells it touches, `W` is computed within
time `TW` and space `SW` (`WordRAM.WordSizeComputable`), and `A` depends on `P` only. The
nondeterministic form is the same with one `FinNDTM` choice step per `coin`, under bounds that
are uniform over all coin streams.

**Deviations from the shape drafted in design §15a**, each read off the code (design §15d):

* *No separate address width.* Addresses are words: `load` reads `m (m j).toInt` and `store`
  writes at `(m i).toInt` (`TCSlib/Programs/WordRAM/Basic.lean:62-63`), and the immediate
  addresses are constants of `P`. So a table entry has `W + O_P(1)` bits, and `f·(W + a)`
  becomes `f·(W + 1)`, the constant going into `A`.
* *The input seek is linear.* R8.5b (`Turing.exists_inputSeekTM`, `Build/InputCall.lean:294`)
  seeks position `p` within `C·(|w| + pos + p + 1)` steps for a position word `w`, with work
  envelope `C·(|w| + 1)`; here `|w| ≤ W` and `pos, p ≤ n + 1`. So the per-step seek term is `n`,
  not `n·log n`.
* *The word size's own cost* is added once, as `TW n` and `SW n`.

## Main definitions

* `WordRAM.simTime`, `WordRAM.simSpace`: the two bounds.
* `WordRAM.outputOf`: what the machine leaves on its output tape, in verdict or function mode.

## Main results (statements gated 2026-10-14, `audits/stage2-statements-findings.md`; proofs pending)

* `WordRAM.exists_simulation`: stage 2, deterministic form.
* `WordRAM.exists_ndSimulation`: stage 2, nondeterministic form.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9, p. 35: a RAM Turing machine is simulated with
  polynomial overhead; §2.1.2: NDTMs; Definition 4.1; §4.3.1: read-once certificates.)
* [AFM26] Anthropic, PBC, `anthropics/formal-math`, project `3sum-apsp`, commit
  `e1a4e6508154ea59f030480661590a9fe3018011` (2026-10-05), Apache-2.0: the word RAM of
  `EndStatement.lean` (vendored as `TCSlib/Programs/WordRAM/Basic.lean`), extended in
  `TCSlib/Programs/WordRAM/Extended.lean`, is the simulated model.
-/

namespace WordRAM

/-- **The time bound of stage 2**: computing the word size, then `t + 1` simulated steps, each at
most one scan of a table of `f` entries of `W + O(1)` bits, one shift-and-add multiplication of
`W`-bit words, and one input seek. -/
def simTime (A : ℕ) (TW : ℕ → ℕ) (n W t f : ℕ) : ℕ :=
  TW n + A * (t + 1) * (f * (W + 1) + W ^ 2 + n + 1)

/-- **The space bound of stage 2**: computing the word size, then the memory table (`f` entries
of `W + O(1)` bits), `O(1)` words of scratch, and the input length in binary. -/
def simSpace (A : ℕ) (SW : ℕ → ℕ) (n W f : ℕ) : ℕ :=
  SW n + A * (f * (W + 1) + W + Complexity.logSpace n + 1)

/-- What the stage-2 machine leaves on its output tape: in verdict mode (`fn = false`) the
one-bit verdict, as `Turing.FinTM.DecidesInTime` and `Turing.FinTM.DecidesInSpace` read it; in
function mode (`fn = true`) the emitted word, as `Turing.FinTM.ComputesInSpace` reads it. -/
def outputOf (fn v : Bool) (o : List Bool) : List Bool := if fn then o else [v]

/-- **Stage 2, deterministic form** (design §15a, §16b; backlog PROG-4). For every program `P` of
the extended word RAM, every output mode `fn` and every word size `W` computable within `TW` and
`SW`, there are a finite binary machine `M` and a constant `A` such that: whenever `P`, run on
`x` with word size `W (|x|)` and the empty coin stream (coins read `0`), gives the verdict `v`
within `t` steps, having emitted `o` and touched at most `f` cells, then `M` halts on `x` within
`TW n + A·(t + 1)·(f·(W + 1) + W² + n + 1)` steps with `outputOf fn v o` on its output tape,
having visited at most `SW n + A·(f·(W + 1) + W + logSpace n + 1)` work cells (`n = |x|`).
[AB09, Exercise 1.9]

Deviations: [AB09] has a RAM Turing machine with a symbol array and the bound `T(n)²`; this is
[AFM26]'s word RAM with input, output and coins, and the bound is explicit in steps, cells and
word size. From design §15a's draft shape: no separate address width, a seek term `n` rather than
`n·log n`, and the word size's own cost added (module docstring).

**Proof sketch.** The machine is a phase host (`Turing.phaseHostTM`, `Build/Seam.lean:813`) over
the finitely many positions of `P`, after a start-up. It works over `Bool` with fields of fixed
width `W + O_P(1)` measured against the ruler below; a richer alphabet would need a per-input
alphabet reduction, which is not public today (`Turing.FinTM.alphabet_reduction` has
length-indexed bounds; its per-input core `arTM_computes`, `Robustness/AlphabetReduction.lean:546`,
is private; there is no nondeterministic variant).
1. *Start-up.* Run the word-size witness with its output captured on a work tape (the R1 silent
   embedding `Turing.embedSilentTM`, `Build/Embed.lean:241`), turn `Nat.bits W` into a unary
   ruler of `W` cells, count `|x|` into a private binary copy (R8.5c,
   `Turing.exists_inputLengthTM`), and install the table entry `-1 ↦ |x| mod 2^W`
   (`WordRAM.initMem`). Cost `TW n + O(n + W²)`, space `SW n + O(W + logSpace n)`.
2. *One phase per position.* Each instruction kind is a framed contract (`Turing.Contract`,
   MIG-0a, landing first) whose precondition says that the tapes encode a RAM configuration (a
   memory table of (address, word) pairs, the position as the phase, the ruler, the length copy)
   and whose endpoint encodes its `xstep`. The new rows (design §15a) are find-by-key in the
   table with the key on another tape; two-tape addition and subtraction modulo `2^W`;
   shift-and-add multiplication; the sign test (`bltz`); the arithmetic shift (`half`); in-place
   overwrite or append of a table entry; the input seek R8.5b (`rdIn`, after a range test of the
   position against `|x|`, `O(W + logSpace n)`); and an output append (`emit`, in function mode
   only). `coin` writes `0`. Each costs at most `A·(f·(W + 1) + W² + n + 1)` steps on a table of
   at most `f + 1` entries.
3. *Simulation.* Induction on the `XStepsIn` run: the encoding invariant holds after every
   step, and the table holds only cells of the footprint `K` and `-1`, so at most
   `|K| + 1 ≤ f + 1` entries of `W + O_P(1)` bits.
4. *Verdict.* At `accept` or `reject`, write `[v]` in verdict mode, and halt. -/
theorem exists_simulation (P : XProgram) (fn : Bool) {W TW SW : ℕ → ℕ}
    (hW : WordSizeComputable W TW SW) :
    ∃ (M : Turing.FinTM Bool) (A : ℕ), ∀ (x : List Bool) (t f : ℕ) (v : Bool) (o : List Bool),
      HaltsWithin P x [] (W x.length) t v o f →
        M.ComputesInTime x (outputOf fn v o) (simTime A TW x.length (W x.length) t f) ∧
        M.tm.spaceUsed (M.tm.initCfg x) (simTime A TW x.length (W x.length) t f) ≤
          simSpace A SW x.length (W x.length) f := by
  sorry

/-- **Stage 2, nondeterministic form** (design §15c, §16b item 4; backlog PROG-4). For every
program `P` of the extended word RAM and every word size `W` computable within `TW` and `SW`,
there are a finite binary nondeterministic machine `N` and a constant `A` such that: if, on the
input `x`, **every** coin stream lets `P` give a verdict within `t` steps touching at most `f`
cells (bounds uniform over the streams, as `NTIME` and `NSPACE` require), then every branch of
`N` of length `T = simTime …` has halted, every such branch has visited at most `simSpace …` work
cells, and `N` accepts `x` within `T` exactly when some coin stream makes `P` accept.
[AB09, Exercise 1.9 with §2.1.2 and Definition 4.1; the coins are read once, as the certificate
of §4.3.1]

**Proof sketch.** As `exists_simulation`, in verdict mode, with one change: the phase for
`coin i` is a single choice step whose two transitions write `0` or `1` into the table entry of
`i`, and every other state has two equal transitions. A branch, a choice word `w` of length `T`,
then simulates the RAM run whose coin stream is the subsequence of `w` at the coin steps;
conversely every coin stream is realized by a branch that places its bits there, padded to length
`T`. Every branch is a run of `P` on some stream, so the uniform bounds bound every branch. On
the stretches between coin steps the branch is the deterministic run of the slice
`N.tm.fixChoice false` (`Turing.NDTM.runWith_eq_fixChoice_runFrom`, in `TuringMachine/Nondeterministic.lean`),
whose phases are those of `exists_simulation`. -/
theorem exists_ndSimulation (P : XProgram) {W TW SW : ℕ → ℕ} (hW : WordSizeComputable W TW SW) :
    ∃ (N : Turing.FinNDTM Bool) (A : ℕ), ∀ (x : List Bool) (t f : ℕ),
      (∀ ρ : List Bool, ∃ (v : Bool) (o : List Bool), HaltsWithin P x ρ (W x.length) t v o f) →
        N.tm.HaltsWithin x (simTime A TW x.length (W x.length) t f) ∧
        (∀ w : List Bool, w.length = simTime A TW x.length (W x.length) t f →
          N.tm.spaceUsedWith w (N.tm.initCfg x) ≤ simSpace A SW x.length (W x.length) f) ∧
        (N.AcceptsWithin x (simTime A TW x.length (W x.length) t f) ↔
          ∃ (ρ o : List Bool), HaltsWithin P x ρ (W x.length) t true o f) := by
  sorry

end WordRAM
