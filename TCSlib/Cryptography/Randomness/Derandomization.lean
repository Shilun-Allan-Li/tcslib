/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Randomness.BPPBridge
import TCSlib.Cryptography.Asymptotic.Pseudorandom
import TCSlib.Complexity.ClassP.DTIME

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Derandomization from pseudorandom generators (statement phase)

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
  needs (seed length `n^{ε/2}`, output length `polyLen a k n`).

## Main definitions

* `Randomness.subexpBound`: `n ↦ ⌈2^{n^ε}⌉`.

## Main results

* `Randomness.subexpBound_pos`: the bound is positive.
* `Randomness.bpp_subset_dtime_subexp` (Thm 180.1, stated; a `sorry` under the source's sketch).

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

/-- The subexponential bound is positive at every length. -/
theorem subexpBound_pos (ε : ℝ) (n : ℕ) : 0 < subexpBound ε n :=
  Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)

/-- **Theorem 180.1: pseudorandom generators derandomize `BPP` in subexponential time**
[PS10, Theorem 180.1]: if a secure PRG exists, then every language of `main`'s `BPP` is in
`DTIME(2^{n^ε})` for every `ε > 0`.

**Proof sketch** (the source's, with the steps it leaves implicit; route note S3c).
1. Let `L ∈ BPP` with verifier `M` and randomness `m(n) = polyLen a k n`. Fix `ε' = ε/2`. By the
   expansion theorems, there is a secure PRG `G` with seed length `s` and output length at least
   `a (s^{1/ε'} + 1)^k` (a polynomial in `s`, `ε` being fixed). Let `ℓ(n) = ⌈n^{ε'}⌉`.
2. Let `M'(x; s) = M(x; G(s)↾m(|x|))` use `ℓ(|x|)` random bits. Suppose that for infinitely many
   `n` some input `x` of length `n` has `|Pr_r[M(x; r) = 1] − Pr_s[M'(x; s) = 1]| > 1/6`. With `x`
   hard-wired as advice at seed length `ℓ(n)`, the machine of `verifier_toNUPPT` (composed with
   the truncation of `G`'s output) distinguishes `G` with advantage `> 1/6` at infinitely many seed
   lengths. The two probabilities are compared through `randProb_eq_uprob`. It runs in time
   polynomial in `n`, which is polynomial in `ℓ(n)`. That contradicts the security of `G`.
3. So for all `n ≥ n₀`, `M'` decides `L` with error `< 1/2` on every input of length `n`, and the
   majority over all `2^{ℓ(n)}` seeds is correct. The finitely many inputs of length `< n₀` are
   decided by a finite table.
4. The machine-level obligation: a deterministic multi-tape machine that enumerates the seeds,
   runs `G` and `M`, and counts, in time `2^{ℓ(n)} · poly(n) ≤ c · 2^{n^ε}` for a constant `c`, on
   `main`'s TM library (`DTIME`). It is the largest single construction of prong D. -/
theorem bpp_subset_dtime_subexp (hPRG : ∃ G : PRG, G.Secure) (ε : ℝ) (hε : 0 < ε) :
    {L | Randomized.InBPP Randomized.polyTimeModel L} ⊆ DTIME (subexpBound ε) := by
  sorry

end TCSlib.Cryptography.Randomness
