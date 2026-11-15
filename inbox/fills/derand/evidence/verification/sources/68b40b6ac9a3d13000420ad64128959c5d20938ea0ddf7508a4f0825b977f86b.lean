/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Randomness.BPPBridge
import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.Defs
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
  needs with a computable integer-root seed schedule and a syntactic polynomial output
  envelope, as specified in the proof sketch below.

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

**Proof sketch** (the source's, with the steps it leaves implicit; route note S3c).
1. Let `L ∈ BPP` have verifier `M` and randomness `m(n) = a(n+1)^k`. Fix an integer `d ≥ 2`
   with `1/d < min(ε,1)`. Compute `ℓ(n)` as the least natural `t` with `n ≤ t^d`, using integer
   comparisons and powers. Then `n ≤ ℓ(n)^d` and `ℓ(n) ≤ n^{1/d}+1`. No computation of an
   arbitrary real exponent is required. Expand the PRG to the syntactic polynomial envelope
   `P(s) = a(s^d+1)^k+s+1`, which exceeds `s` and covers `m(n)` whenever `s = ℓ(n)`.
2. Let `M'(x; u) = M(x; G(u)↾m(|x|))`, with seed length `ℓ(|x|)`. If infinitely many lengths
   have an input with acceptance-probability gap `> 1/12`, choose one corresponding bad input
   at each bad seed length. Its advice length is at most `s^d`. The verifier bridge, composed
   with prefix truncation, is therefore a distinguisher polynomial in `s`; the probabilities
   agree through `randProb_eq_uprob`. Each seed length has only finitely many corresponding
   input lengths, so infinitely many bad input lengths give infinitely many bad seed lengths,
   contradicting PRG security. The fixed `1/12` threshold leaves an explicit majority margin.
3. Eventually every input has probability gap at most `1/12`. Since `M` is correct with
   probability at least `2/3`, `M'` is correct with probability at least `7/12 > 1/2`.
   The majority over all seeds is correct. A finite table handles the remaining input lengths.
4. Construct a deterministic multi-tape machine enumerating the seeds, running `G` and `M`,
   and counting, using the shared TM construction layer. For some constants `C,C'`, its time
   is at most `2^{ℓ(n)} · poly(n) ≤ 2^{n^{1/d}+1+C log₂(n+1)+C'}`. Since `1/d < ε`, this is
   eventually at most `2^{n^ε}`; a constant factor absorbs the finite exceptions. This machine
   construction is the substantive remaining fill obligation, not supplied by the sketch. -/
theorem bpp_subset_dtime_subexp (hPRG : ∃ G : PRG, G.Secure) (ε : ℝ) (hε : 0 < ε) :
    {L | Randomized.InBPP Randomized.polyTimeModel L} ⊆ DTIME (subexpBound ε) := by
  sorry

end TCSlib.Cryptography.Randomness
