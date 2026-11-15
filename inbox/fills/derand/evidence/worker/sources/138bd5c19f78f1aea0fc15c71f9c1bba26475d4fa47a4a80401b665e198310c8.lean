/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Randomness.BPPBridge
import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.Defs
import TCSlib.Complexity.ClassP.DTIME
import TCSlib.Cryptography.Randomness.Derandomization.RootSchedule
import TCSlib.Cryptography.Randomness.Derandomization.AdviceGap
import TCSlib.Cryptography.Randomness.Derandomization.Expanded
import TCSlib.Cryptography.Randomness.Derandomization.CoinGap
import TCSlib.Cryptography.Randomness.Derandomization.Majority
import TCSlib.Cryptography.Randomness.Derandomization.TimeBound
import TCSlib.Complexity.Randomized.QuasiPolyHierarchy

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Derandomization from pseudorandom generators

[PS10, Theorem 180.1]: if pseudorandom generators exist, then `BPP ⊆ DTIME(2^{n^ε})` for every
constant `ε > 0`.

**The formal reading.**
- **`BPP`** is `main`'s `Randomized.InBPP Randomized.polyTimeModel` ([AB09, Def 7.3]): an
  efficient verifier with randomness `polyLen a k |x|` and two-sided error `1/3` (decision D-6).
  It is inhabited: `P ⊆ BPP` is `Randomized.inBPP_polyTimeModel_of_mem_P`.
- **`DTIME(t)`** is `main`'s `Complexity.DTIME`, deterministic multi-tape time `O(t(n))`, the
  source's reading ("bounded by `O(t(n))`").
- **The bound** `2^{n^ε}` is taken with a real exponent and rounded up (`subexpBound`), so that
  every real `ε > 0` is covered, as in the source. It is at least `1` at every length
  (`subexpBound_pos`), so `DTIME (subexpBound ε)` is not empty for a trivial reason (`DTIME` of a
  bound that vanishes somewhere is).
- **"PRGs exist"** is `∃ G : PRG, G.Secure`, the ch. 2–4 layer's [PS10, Definition 77.1], secure
  against non-uniform distinguishers. A PRG of any stretch `ℓ(n) > n` gives one with any polynomial
  stretch by the ch. 2–4 expansion theorems (`PRG.Secure.truncate`, `prg_expand`), which the proof
  needs with a computable integer-root seed schedule and a syntactic polynomial output
  envelope, as specified in the proof sketch below.

## Main definitions

* `Randomness.subexpBound`: `n ↦ ⌈2^{n^ε}⌉`.

## Contents

* `Randomness.Derandomization.RootSchedule`: the integer-root seed schedule.
* `Randomness.Derandomization.AdviceGap`: the non-uniform advice gap bound.
* `Randomness.Derandomization.Expanded`: the secure polynomial output envelope.
* `Randomness.Derandomization.CoinGap`: the uniform prefix probability identification.
* `Randomness.Derandomization.Majority`: the piecewise verifier and strict majority.
* `Randomness.Derandomization.TimeBound`: the asymptotic estimate and finite exceptions.

## Main results

* `Randomness.subexpBound_pos`: the bound is positive.
* `Randomness.bpp_subset_dtime_subexp` (Thm 180.1), proved through the shared
  seed-majority machine contract and its DTIME corollary.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §8.2, Theorem 180.1 (book p. 180).
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge University
  Press, 2009, Definitions 1.12 and 7.3 (`main`'s `DTIME` and `BPP`).
-/

namespace TCSlib.Cryptography.Randomness

open Complexity TCSlib.Cryptography

/-- The subexponential time bound `n ↦ ⌈2^{n^ε}⌉` (real exponent, rounded up). -/
noncomputable def subexpBound (ε : ℝ) (n : ℕ) : ℕ := ⌈(2 : ℝ) ^ ((n : ℝ) ^ ε)⌉₊

/-- The subexponential bound is the natural ceiling of `2^{n^ε}` with real exponents:
`subexpBound ε n = ⌈2^{n^ε}⌉₊`. -/
theorem subexpBound_eq (ε : ℝ) (n : ℕ) :
    subexpBound ε n = ⌈(2 : ℝ) ^ ((n : ℝ) ^ ε)⌉₊ := rfl

/-- The subexponential bound is positive at every length. -/
theorem subexpBound_pos (ε : ℝ) (n : ℕ) : 0 < subexpBound ε n :=
  Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)

/-- **Theorem 180.1: pseudorandom generators derandomize `BPP` in subexponential time**
[PS10, Theorem 180.1]: if a secure PRG exists, then every language of `main`'s `BPP` is in
`DTIME(2^{n^ε})` for every `ε > 0`.

**Status.** Proved through `Complexity.exists_seedMajorityTM` and
`Complexity.seedMajority_mem_DTIME`; the helpers introduce no admissions.

**Proof sketch** ([PS10, Theorem 180.1], with an explicit piecewise test).
1. Choose an integer `d ≥ 2` with `1/d < min(ε,1)`. The least natural root
   `ℓ(n) = min{t | n ≤ t^d}` has an FP unary word and satisfies
   `n ≤ ℓ(n)^d` and `ℓ(n) ≤ n^(1/d)+1`, including at zero.
2. Expand a secure generator to `a(s^d+1)^k+s+1` and extract its FP evaluator.
   Apply the verifier bridge to one bad input at each bad seed length, with
   advice bound `s^d`. The published probability bridge and prefix projection
   identify its PRG advantage with the verifier gap. Negligibility's inverse-linear
   bound rules out every gap above `1/12` beyond a seed threshold, hence beyond
   some input threshold `n₀`.
3. Below `n₀`, use the original verifier with its true polynomial coin width;
   from `n₀` on, use the generated prefix and width `ℓ(n)`. Both this paired
   test and its unary width are polynomial-time. Acceptance is above `1/2`
   exactly on members, with margins at least `7/12` and at most `5/12` in the
   generated case. `half_lt_randProb_iff` identifies `L` with the strict seed
   majority, including ties and zero widths. No exceptional-input table is used.
4. Apply `seedMajority_mem_DTIME`. The logarithm of `2^w(n)(n+1)^e`, divided
   by `n^ε`, tends to zero because `1/d < ε`; thus the time is eventually at
   most `2^(n^ε)`. A natural constant absorbs all earlier lengths, since the
   rounded bound is positive. Finish through `DTIME.mono` and
   `Randomized.DTIME_const_mul_subset`. -/
theorem bpp_subset_dtime_subexp (hPRG : ∃ G : PRG, G.Secure) (ε : ℝ) (hε : 0 < ε) :
    {L | Randomized.InBPP Randomized.polyTimeModel L} ⊆ DTIME (subexpBound ε) := by
  intro L hL
  obtain ⟨d, hd, hdε, _⟩ := Derand.exists_root_degree hε
  have hdpos : 0 < d := by omega
  obtain ⟨V, w, n₀, hV, hw, hevent, hmajority⟩ :=
    Derand.exists_seed_majority hPRG hL d hdpos
  obtain ⟨e, htime⟩ := seedMajority_mem_DTIME hV w hw
  rw [← hmajority] at htime
  obtain ⟨C, hbound⟩ := Derand.seed_time_le_subexp hdpos hε hdε w n₀ hevent e
  apply Randomized.DTIME_const_mul_subset C (subexpBound ε)
  apply DTIME.mono (fun n => ?_) htime
  simpa only [subexpBound_eq] using hbound n

end TCSlib.Cryptography.Randomness
