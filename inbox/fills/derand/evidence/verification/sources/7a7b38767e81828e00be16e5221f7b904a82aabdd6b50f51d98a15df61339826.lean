/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.ClassP.P
import TCSlib.Complexity.ClassNP.PolyTime
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Complexity.Randomized.Classes
import TCSlib.Complexity.Randomized.SeedMajority.Words
import TCSlib.Complexity.Randomized.SeedMajority.State
import TCSlib.Complexity.Randomized.SeedMajority.Enumeration
import TCSlib.Complexity.Randomized.SeedMajority.Envelope

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Deterministic majority over all seeds

The counting enumeration host: a deterministic machine that, on input `x`, runs a
polynomial-time test on `⟨x, u⟩` for **every** seed `u ∈ {0,1}^{w(|x|)}`, counts the accepting
seeds, and accepts iff more than half of them accept, in time `2^{w(n)} · poly(n)`. It is the
enumeration behind `BPP ⊆ EXP` [AB09, §7.1, p. 126] (run the machine on every random string
and count the accepting ones) and step 4 of the proof of [PS10, §8.2, Theorem 180.1] (run the
derandomized verifier on every seed of the generator and take the majority). It is a *host* in
the sense of `policy.md` §1 (*Hosts come first*): an odometer over all seeds, generic in the
leaf test `V` and in the width `w`. Its contract is stated here, ahead of its consumers, by
Seyoon's rulings of 2026-11-14 (the host) and 2026-11-15 (the machine-level contract with a
head envelope, Gate 28, G28-02). **Proof owner:** the `derand` fill proves the host contract
`Complexity.exists_seedMajorityTM`, its corollary `Complexity.seedMajority_mem_DTIME`, and
Theorem 180.1 (`TCSlib.Cryptography.Randomness.bpp_subset_dtime_subexp`).

**The formal reading.**
- **The test** is a language `V ∈ P` read on `Turing.pairEncode x u`, the library's two-argument
  convention (`Randomized.polyTimeModel`'s verifiers are read the same way), so that the test may
  depend on the input `x` as well as on the seed `u`.
- **The width** `w : ℕ → ℕ` depends on the input length only, and its unary word
  `x ↦ 1^{w(|x|)}` is polynomial-time computable. This makes `w` computable by the machine and
  bounds it polynomially (`Complexity.PolyTimeComputable.output_length_le`); it is otherwise
  arbitrary, so a consumer may use a non-polynomial schedule such as an integer root, or a
  piecewise one.
- **The count** is `#{u : Fin (w |x|) → Bool | ⟨x, u⟩ ∈ V}`, the numerator of
  `Randomized.randProb` (`Randomized.half_lt_randProb_iff` converts), and **majority** is the
  strict `2^{w(|x|)} < 2 · count`, so ties reject.
- **The machine contract** (`Complexity.exists_seedMajorityTM`) ties correctness, time and a
  head envelope to the **same machine**: some finite machine `M` and constants `c, e`, with the
  budget `B(n) = c · (2^{w(n)} · (n+1)^e)`, satisfy
  - *correctness and time:* `M` decides the majority language within `B`
    (`Turing.FinTM.DecidesInTime`, the library's machine-level decision contract);
  - *head envelope:* at every time `v` of the run of `M` from its initial configuration on `x`,
    every work head is within `B |x|` cells of the origin. This is the coarse envelope derived
    from the time bound, in the form of the clean-module host's `Turing.ModuleHost.Clean.envelope`
    (`machine-library-design.md` §14, rows H14 and H16).
- **The class** `DTIME (n ↦ 2^{w(n)} · (n+1)^e)` is a corollary (`seedMajority_mem_DTIME`),
  which follows from the contract through the reader `Complexity.mem_DTIME_iff`. The `derand`
  fill adds that reader beside `DTIME` (`ClassP/DTIME.lean`) under its pre-approval (Seyoon,
  2026-11-15). Until then the corollary is admitted: without the reader its proof would read
  `Turing.FinTM.DecidesInTime`, `Turing.FinTM.DecidesInTimeVia` and `DTIME` by their
  definitions (Rule 10).

## Contents

* `Complexity.Randomized.SeedMajority.Words`: binary seed words and prefix counts.
* `Complexity.Randomized.SeedMajority.State`: the FP counting round and terminal tests.
* `Complexity.Randomized.SeedMajority.Enumeration`: the finite binary-fuel machine.
* `Complexity.Randomized.SeedMajority.Envelope`: the all-times work-head bound.

## Main results

* `Complexity.exists_seedMajorityTM` — the host's machine-level contract: correctness, time and
  head envelope of one machine, proved through the generic binary-fuel harvest.
  [AB09, §7.1, p. 126]; [PS10, Theorem 180.1, step 4 of the proof]
* `Complexity.seedMajority_mem_DTIME` — the decision-class corollary
  `∃ e, {x | 2^{w(|x|)} < 2 · count} ∈ DTIME (n ↦ 2^{w(n)} · (n+1)^e)`, proved from
  the host contract through `mem_DTIME_iff`.
* `Randomized.half_lt_randProb_iff` — majority as a probability:
  `1/2 < randProb m A ↔ 2^m < 2 · #{r | A r}` (proved).

## Consumers

* `TCSlib.Cryptography.Randomness.bpp_subset_dtime_subexp` ([PS10, Theorem 180.1]), through
  `seedMajority_mem_DTIME`, with the test **and** the width of the paper proof, both piecewise in
  a threshold length `n₀`. Let `V₁` be the accepting paired language of the `BPP` verifier `M`,
  `m(n)` its coin width, `F'` the evaluator of the expanded generator, and `ℓ(n)` the least `t`
  with `n ≤ t^d`. Below `n₀`, the test is `V₁` itself on the true coins,
  `⟨x, u⟩ ↦ M(x; u)`, with the width `w(n) = m(n)`. From `n₀` on, the test is
  `⟨x, u⟩ ↦ M(x; F'(u)↾m(|x|))` with the width `w(n) = ℓ(n)`. Changing the width alone would not
  remove the generator: `PRG` security says nothing about finitely many seed lengths, so the test
  changes with it.
* Prospectively, `BPP ⊆ EXP` by coin enumeration [AB09, p. 126] (`w = polyLen a k`), which
  `Randomized.mem_EXP_of_inBPP_polyTimeModel` currently obtains through Sipser–Gács.

## Design

* The nearest relative is the existential projection decider `Complexity.exists_proj_decider`
  (`ClassNP/EXP.lean`): the same odometer with an *any* verdict, a fixed width `C(n+1)^c` and
  the test on `x ++ u`. Its engine `enumMachine_contracts` and the `enumCont_*` body are
  private, it does not count, and its width is not a parameter, so it is not reused.
* The polynomial block-majority tests (`Complexity.polyTimeComputable_blockMajorityTest`) count
  over polynomially many blocks; this host counts over exponentially many seeds.
* The test is polynomial-time (`V ∈ P`), not a decider of arbitrary time `Tv` as in
  `exists_proj_decider`: both consumers have polynomial tests, and the clean-module host below
  installs polynomial-time word functions only (`Turing.ModuleHost.clean_install`).
* **Head envelope** (`policy.md` §1, *Hosts come first*; Seyoon's ruling of 2026-11-15, Gate 28,
  G28-02). The contract is machine-level, and its envelope is the coarse one from its own time
  bound `B`, on the same machine, as H14 states `Clean.envelope` and H16 composes with it. A
  sharper envelope does hold (every state word has length `O(n + w(n))`), but no consumer needs
  it and it is not stated. The admitted `loopHostTM_*` and `timedCondTM_*` space specifications
  are not used for it.

## Route for the proof (the `derand` fill)

1. *State loop.* The state word is `⟨x, ⟨i, a⟩⟩`: the binary rank `i` of the current seed and
   the binary acceptance count `a`, from `⟨x, ⟨0, 0⟩⟩`. A step tests `⟨x, word_w(i)⟩ ∈ V`,
   where `word_w(i)` is the width-`w(|x|)` binary word of `i`, adds the verdict to `a` and
   increments `i`. The loop stops when `i = 2^{w(|x|)}` and outputs `[decide (2^w < 2a)]`.
   Every piece is a polynomial-time word function of the state (`Complexity.BinArith`'s
   `add`, `lt` and `beq`, zero padding, the unary width, and `V`'s decider through
   `Complexity.mem_P_iff_polyTimeComputable`).
2. *Machine.* The result-bearing loop combinator `Turing.FinTM.exists_loopFindTM` over the
   clean-module host (`Turing.ModuleHost`, with `Complexity.IterateFind.hostTM`, `hostCtrl`,
   `hostRet`, `copyTM` and their run lemmas), exactly as in
   `Complexity.IterateFind.polyTimeComputable_find`, but with the exponential fuel
   `R(n) = 2^{w(n)}`, written as `Nat.bits (2^{w(|x|)})`
   (`w(|x|)` zeros, then a one) from the unary width. The combinator's bound is
   `c (T(n) + 1)(R(n) + 2)`, with `T` polynomial because every state word has length
   `O(n + w(n))` and `w(n) ≤ C(n+1)^c`. The admitted `loopHostTM_*` and `timedCondTM_*` specs
   are not used: `exists_loopFindTM` is proved from the private `loopHost_contracts`.
3. *Count.* The first stopping round is `2^{w(|x|)}`; there `a` counts the ranks `i < 2^w`
   whose word is accepted, which is the `Finset` count above through the bijection
   `i ↦ word_w(i)` between `[0, 2^w)` and `{0,1}^w`.
4. *Normal form.* `c (T(n) + 1)(2^{w(n)} + 2) ≤ b · (2^{w(n)} · (n+1)^e)`: the budget `B`.
5. *Envelope.* Every work head starts at the origin (`Turing.Cfg.init_workTapePos`) and moves by
   at most one cell per step (`Turing.MultiTapeTM.workTapePos_runFrom_mem_Icc`); the run halts
   by time `B |x|` and is constant afterwards (`Turing.MultiTapeTM.runFrom_of_halt`). This is the
   argument of `Turing.ModuleHost.Clean.envelope`, applied to the machine of steps 2–4.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge University
  Press, 2009, §7.1, p. 126 (`BPP ⊆ EXP` by enumerating the random strings) and Claim 2.4 (the
  enumeration argument of `NP ⊆ EXP`).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §8.2, Theorem 180.1 (book p. 180).
-/

namespace Randomized

open Finset

/-- **Majority as a probability.** For an event `A` on `m`-bit strings, the uniform probability
of `A` exceeds `1/2` exactly when more than half of the `2^m` strings satisfy it:
`1/2 < randProb m A ↔ 2^m < 2 · #{r : Fin m → Bool | A (List.ofFn r)}`. This converts the
counting form of `Complexity.seedMajority_mem_DTIME` into the probabilistic form of
[AB09, Def 7.3] and [PS10, Theorem 180.1]. -/
theorem half_lt_randProb_iff (m : ℕ) (A : List Bool → Prop) [DecidablePred A] :
    1 / 2 < randProb m A ↔
      2 ^ m < 2 * (univ.filter fun r : Fin m → Bool => A (List.ofFn r)).card := by
  rw [randProb_eq, lt_div_iff₀ (by positivity), ← Nat.cast_lt (α := ℚ)]
  push_cast
  constructor <;> intro h <;> linarith

end Randomized

namespace Complexity

open Turing

open Classical in
/-- **Deterministic majority over all seeds: the machine contract** [AB09, §7.1, p. 126];
[PS10, §8.2, Theorem 180.1, step 4 of the proof]. For a test `V ∈ P` on paired words and a width
`w : ℕ → ℕ` whose unary word `x ↦ 1^{w(|x|)}` is polynomial-time computable, one finite machine
`M`, with constants `c, e` and the budget `B(n) = c · (2^{w(n)} · (n+1)^e)`,
- decides the strict-majority language
  `S = {x | 2^{w(|x|)} < 2 · #{u : Fin (w |x|) → Bool | pairEncode x (List.ofFn u) ∈ V}}`
  within `B` (`M.DecidesInTime S B`): on every input `x` it halts within `B |x|` steps with
  output `[true]` if `x ∈ S` and `[false]` otherwise; ties (`2 · count = 2^w`) reject; and
- keeps every work head within `B |x|` cells of the origin at every time `v` of its run on `x`:
  `|(M.tm.runFrom (M.tm.initCfg x) v).workTapePos j| ≤ B |x|` (the head envelope, the coarse one
  from the time bound, as `Turing.ModuleHost.Clean.envelope`).

**Deviation.** The source's machine runs the test on every seed and counts; here the test is a
`P`-language on `Turing.pairEncode x u` and the count is a `Finset` count over
`Fin (w |x|) → Bool`, the numerator of `Randomized.randProb` (`Randomized.half_lt_randProb_iff`).
The head envelope is not in the source; it is the host clause of `policy.md` §1.

**Status.** Proved through `SeedMajority.exists_countingTM` and
`SeedMajority.envelope_of_computesInTime`, using only the published decision and
computation readers.

**Proof sketch** (the route of the module docstring; implemented in the helpers).
1. Run the state loop `⟨x, ⟨i, a⟩⟩ ↦ ⟨x, ⟨i + 1, a + [⟨x, word_w(i)⟩ ∈ V]⟩⟩` from
   `⟨x, ⟨0, 0⟩⟩`, stopping at `i = 2^{w(|x|)}` with the payload `[2^w < 2a]`; each piece is a
   polynomial-time word function of the state.
2. Build the machine with the loop combinator `Turing.FinTM.exists_loopFindTM` over the
   clean-module host, as in `Complexity.IterateFind.polyTimeComputable_find`, with the fuel
   `Nat.bits (2^{w(|x|)})`; it halts within `c₀ (T(n) + 1)(2^{w(n)} + 2)` with `T` polynomial,
   since `w(n) ≤ C (n+1)^c` (`PolyTimeComputable.output_length_le`).
3. At the stopping round, `a` is the number of accepted ranks `i < 2^w`, which equals the
   `Finset` count through the bijection `i ↦ word_w(i)` onto `{0,1}^w`.
4. Bound `c₀ (T(n) + 1)(2^{w(n)} + 2)` by `c · (2^{w(n)} · (n+1)^e)`.
5. The envelope: the heads start at the origin (`Cfg.init_workTapePos`), move by at most one
   cell per step (`MultiTapeTM.workTapePos_runFrom_mem_Icc`), and the run is constant after its
   halt at a time `≤ B |x|` (`MultiTapeTM.runFrom_of_halt`). -/
theorem exists_seedMajorityTM {V : Language Bool} (hV : V ∈ P) (w : ℕ → ℕ)
    (hw : PolyTimeComputable fun x => List.replicate (w x.length) true) :
    ∃ (M : FinTM Bool) (c e : ℕ),
      M.DecidesInTime
          {x : List Bool | 2 ^ w x.length <
            2 * (Finset.univ.filter fun u : Fin (w x.length) → Bool =>
              pairEncode x (List.ofFn u) ∈ V).card}
          (fun n => c * (2 ^ w n * (n + 1) ^ e)) ∧
        ∀ (x : List Bool) (v : ℕ) (j : Fin M.k),
          |(M.tm.runFrom (M.tm.initCfg x) v).workTapePos j| ≤
            ((c * (2 ^ w x.length * (x.length + 1) ^ e) : ℕ) : ℤ) := by
  obtain ⟨M, c, e, hM⟩ := SeedMajority.exists_countingTM hV w hw
  refine ⟨M, c, e, ?_, ?_⟩
  · apply (FinTM.decidesInTime_iff _ _ _).mpr
    intro x
    have hx := (FinTM.computesFunInTime_iff _ _ _).mp hM x
    rw [MultiTapeTM.indicator_def]
    by_cases h : 2 ^ w x.length <
        2 * (Finset.univ.filter fun u : Fin (w x.length) → Bool =>
          pairEncode x (List.ofFn u) ∈ V).card
    · simpa only [Set.mem_setOf_eq, if_pos h, decide_eq_true h] using hx
    · simpa only [Set.mem_setOf_eq, if_neg h, decide_eq_false h] using hx
  · intro x v j
    exact SeedMajority.envelope_of_computesInTime
      ((FinTM.computesFunInTime_iff _ _ _).mp hM x) v j

open Classical in
/-- **Deterministic majority over all seeds: the decision class** [AB09, §7.1, p. 126];
[PS10, §8.2, Theorem 180.1, step 4 of the proof]: for a test `V ∈ P` on paired words and a width
`w : ℕ → ℕ` whose unary word `x ↦ 1^{w(|x|)}` is polynomial-time computable, some degree `e`
puts the strict-majority language in `DTIME (n ↦ 2^{w(n)} · (n+1)^e)`:
`∃ e, {x | 2^{w(|x|)} < 2 · #{u : Fin (w |x|) → Bool | pairEncode x (List.ofFn u) ∈ V}}
∈ DTIME (fun n => 2^{w(n)} · (n+1)^e)`. Ties (`2 · count = 2^w`) reject. It is the corollary
of the machine contract `exists_seedMajorityTM` that the consumers of the class read.

**Status.** Proved from `exists_seedMajorityTM`. The proof reads the machine contract
through `Complexity.mem_DTIME_iff`, added beside `DTIME` under the pre-approval of
2026-11-15. It uses no definitional reading of either `DTIME` or `DecidesInTime`.

**Proof sketch.** Take the machine `M` and constants `c, e` of `exists_seedMajorityTM` (the
envelope is not needed here). `M` decides the language within
`n ↦ c · (2^{w(n)} · (n+1)^e)`, which is `c · T n` for `T n = 2^{w(n)} · (n+1)^e`. By
`mem_DTIME_iff` (membership in `DTIME T` is a constant `c` together with a machine deciding
within `c · T`), the language is in `DTIME T`, with the witness `e`. -/
theorem seedMajority_mem_DTIME {V : Language Bool} (hV : V ∈ P) (w : ℕ → ℕ)
    (hw : PolyTimeComputable fun x => List.replicate (w x.length) true) :
    ∃ e : ℕ,
      {x : List Bool | 2 ^ w x.length <
          2 * (Finset.univ.filter fun u : Fin (w x.length) → Bool =>
            pairEncode x (List.ofFn u) ∈ V).card} ∈
        DTIME fun n => 2 ^ w n * (n + 1) ^ e := by
  obtain ⟨M, c, e, hM, _⟩ := exists_seedMajorityTM hV w hw
  exact ⟨e, mem_DTIME_iff.mpr ⟨c, M, hM⟩⟩

end Complexity
