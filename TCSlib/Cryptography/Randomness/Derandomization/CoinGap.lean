/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Randomness.Derandomization.AdviceGap
import TCSlib.Cryptography.Randomness.Derandomization.Expanded

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Replacing a verifier's coins by generated bits

The expanded generator and the non-uniform advice bound give a single FP
evaluator whose acceptance gap is at most `1/12` on every sufficiently long
input. The probability identification reuses the published counting bridge
and uniform prefix projection, including zero coin lengths.

## Main results

* `TCSlib.Cryptography.Randomness.Derand.exists_coin_gap_threshold`: the
  input-length threshold needed by the piecewise verifier.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
  3rd ed., January 2010, §8.2, Theorem 180.1.
-/

namespace TCSlib.Cryptography.Randomness.Derand

open Complexity Turing

/-- There are an FP generator evaluator `F` and a threshold `n₀` such that,
for every `|x| ≥ n₀`,
`|randProb (ceilRoot d |x|) (M x (F(u)↾m)) - randProb m (M x)| ≤ 1/12`,
where the rational probabilities are cast to `ℝ` and `m = polyLen a k |x|`.
[PS10, §8.2, Theorem 180.1]

**Proof sketch.** Expand a secure generator to cover the verifier's entire
coin width. Apply the advice-gap theorem to the prefix-truncated verifier,
which stays efficient by `eff_mapCoins` and `polyTimeComputable_pairTakePoly`.
Advice has bound `s^d` because `|x| ≤ (ceilRoot d |x|)^d`. If the seed threshold
is `S`, input lengths from `S^d+1` on have root greater than `S`. Identify the
generated probability with the first advantage term using the evaluator's
typed contract and `randProb_eq_uprob`; identify the uniform term using
`randProb_take`. No new expectation or probability-reindexing identity is used. -/
theorem exists_coin_gap_threshold (hPRG : ∃ G : PRG, G.Secure)
    {M : List Bool → List Bool → Bool}
    (hM : Randomized.polyTimeModel.Eff (Randomized.boolVerifier M))
    (a k d : ℕ) (hd : 0 < d) :
    ∃ (F : List Bool → List Bool) (n₀ : ℕ), PolyTimeComputable F ∧
      ∀ x : List Bool, n₀ ≤ x.length →
        |(Randomized.randProb (ceilRoot d x.length)
            (fun u => M x ((F u).take (Randomized.polyLen a k x.length)) = true) : ℝ) -
          (Randomized.randProb (Randomized.polyLen a k x.length)
            (fun r => M x r = true) : ℝ)| ≤ (1 : ℝ) / 12 := by
  classical
  obtain ⟨G, F, hG, hF, hFs, hcover⟩ := exists_secure_cover hPRG a k d hd
  let M' : List Bool → List Bool → Bool :=
    fun x r => M x (r.take (Randomized.polyLen a k x.length))
  have hM' : Randomized.polyTimeModel.Eff (Randomized.boolVerifier M') := by
    simpa only [pairFstD_pairEncode, pairSndD_pairEncode, eval_polyLenExpr, M'] using
      eff_mapCoins hM (polyTimeComputable_pairTakePoly (polyLenExpr a k))
  have hsize (n : ℕ) : n ≤ (PolyExpr.pow .var d).eval (ceilRoot d n) := by
    simpa only [PolyExpr.eval_pow, PolyExpr.eval_var] using le_ceilRoot_pow hd n
  obtain ⟨S, hS⟩ := exists_verifier_gap_bound hM' (ceilRoot d) (.pow .var d) hsize G hG
  refine ⟨F, S ^ d + 1, hF, fun x hx => ?_⟩
  have hs : S ≤ ceilRoot d x.length :=
    ((lt_ceilRoot_iff hd x.length S).mpr (by omega)).le
  have h := hS x hs
  have hgen :
      (Randomized.randProb (ceilRoot d x.length)
        (fun u => M x ((F u).take (Randomized.polyLen a k x.length)) = true) : ℝ) =
        uprob (fun r : Fin (ceilRoot d x.length) → Bool =>
          M' x (List.ofFn (G.G (ceilRoot d x.length) r)) = true) := by
    rw [randProb_eq_uprob]
    congr 1
    funext r
    rw [hFs]
  have huniform :
      uprob (fun r : Fin (G.stretch.eval (ceilRoot d x.length)) → Bool =>
        M' x (List.ofFn r) = true) =
        (Randomized.randProb (Randomized.polyLen a k x.length)
          (fun r => M x r = true) : ℝ) := by
    rw [← randProb_eq_uprob (G.stretch.eval (ceilRoot d x.length))
      (fun r => M' x r = true)]
    exact congrArg (fun q : ℚ => (q : ℝ))
      (Randomized.randProb_take (hcover x.length) (fun r => M x r = true))
  rw [hgen, ← huniform]
  exact h

end TCSlib.Cryptography.Randomness.Derand
