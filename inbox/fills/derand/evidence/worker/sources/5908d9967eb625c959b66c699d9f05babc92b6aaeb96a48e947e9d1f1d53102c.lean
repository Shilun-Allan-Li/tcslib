/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Data.Rat.Cast.Order
import TCSlib.Cryptography.Randomness.Derandomization.CoinGap
import TCSlib.Complexity.Randomized.SeedMajority

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The piecewise verifier and its seed majority

Below the security threshold, both the verifier and its width use the true
random coins. At and above the threshold, they use the expanded generator
and the ceiling-root seed length. The `1/12` gap gives a strict majority in
both cases, so no finite table of exceptional input words is needed.

## Main results

* `TCSlib.Cryptography.Randomness.Derand.exists_seed_majority`: a `P` test
  and an FP unary width whose strict seed majority equals the BPP language.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
  3rd ed., January 2010, §8.2, Theorem 180.1.
-/

namespace TCSlib.Cryptography.Randomness.Derand

open Complexity Turing

/-- A fixed upper threshold on the length of an FP word is an FP test.
The existing length comparison tests `|f z| + 1 ≤ N`. -/
private theorem short_poly {f : List Bool → List Bool} (hf : PolyTimeComputable f) (N : ℕ) :
    PolyTimeComputable fun z => [decide ((f z).length < N)] := by
  convert StateLoop.lenLe_comp (polyTimeComputable_const (List.replicate N true))
    (hf.append (polyTimeComputable_const [true])) using 1
  funext z
  simp only [List.length_append, List.length_singleton, List.length_replicate,
    Nat.add_one_le_iff]

open Classical in
/-- A BPP language is the strict seed-majority language of a `P` test with an
FP unary width `w`, where `w n = ceilRoot d n` beyond some threshold:
`L = {x | 2^(w |x|) < 2 * #{u | ⟨x,ofFn u⟩ ∈ V}}`.
[PS10, §8.2, Theorem 180.1]

**Proof sketch.** Extract the efficient Boolean verifier and polynomial coin
schedule through `inBPP_iff`. Use the coin-gap threshold and hard-code it
in a polynomial-time branch. Below it, the test uses the original coins and
the width is the original polynomial schedule. Above it, the test uses the
generated prefix and the width is the ceiling root. The test stays efficient
by `eff_mapCoins`; its accepting language is therefore in `P`. The unary
width is FP by the same fixed length branch. The true-coin acceptance bound
`2/3` and the gap bound give acceptance above `1/2` on members and below
`1/2` on nonmembers. Finally `half_lt_randProb_iff` identifies exactly the
strict seed count, with ties rejected and zero widths included. -/
theorem exists_seed_majority (hPRG : ∃ G : PRG, G.Secure)
    {L : Language Bool} (hL : Randomized.InBPP Randomized.polyTimeModel L)
    (d : ℕ) (hd : 0 < d) :
    ∃ (V : Language Bool) (w : ℕ → ℕ) (n₀ : ℕ), V ∈ P ∧
      PolyTimeComputable (fun x => List.replicate (w x.length) true) ∧
      (∀ n, n₀ ≤ n → w n = ceilRoot d n) ∧
      L = {x : List Bool | 2 ^ w x.length <
        2 * (Finset.univ.filter fun u : Fin (w x.length) → Bool =>
          pairEncode x (List.ofFn u) ∈ V).card} := by
  classical
  obtain ⟨M, a, k, hM, hcorrect⟩ :=
    (Randomized.inBPP_iff Randomized.polyTimeModel L).mp hL
  obtain ⟨F, n₀, hF, hgap⟩ := exists_coin_gap_threshold hPRG hM a k d hd
  let w (n : ℕ) := if n < n₀ then Randomized.polyLen a k n else ceilRoot d n
  let C (z : List Bool) := if (pairFstD z).length < n₀ then pairSndD z
    else (F (pairSndD z)).take (Randomized.polyLen a k (pairFstD z).length)
  let M' (x u : List Bool) := M x (C (pairEncode x u))
  have hprefix : PolyTimeComputable fun z =>
      (F (pairSndD z)).take (Randomized.polyLen a k (pairFstD z).length) := by
    convert (polyTimeComputable_pairTakePoly (polyLenExpr a k)).comp
      (polyTimeComputable_pairFstD.pairEncode (hF.comp polyTimeComputable_pairSndD)) using 1
    funext z
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
      eval_polyLenExpr]
  have hC : PolyTimeComputable C := by
    simpa only [C, decide_eq_true_eq] using
      polyTimeComputable_ite (short_poly polyTimeComputable_pairFstD n₀)
        polyTimeComputable_pairSndD hprefix
  have hM' : Randomized.polyTimeModel.Eff (Randomized.boolVerifier M') := eff_mapCoins hM hC
  obtain ⟨V, _, hV, _, hMV⟩ :=
    (Randomized.polyTimeModel_eff_iff (Randomized.boolVerifier M')).mp hM'
  have hVeq (x u : List Bool) : M' x u = true ↔ pairEncode x u ∈ V := by
    simpa only [Randomized.boolVerifier_apply, Option.some.injEq] using (hMV x u).1
  have hw : PolyTimeComputable fun x => List.replicate (w x.length) true := by
    have h := polyTimeComputable_ite (short_poly polyTimeComputable_id n₀)
      (polyTimeComputable_unaryPoly (polyLenExpr a k)) (polyTimeComputable_ceilRoot hd)
    convert h using 1
    funext x
    simp only [id_eq, decide_eq_true_eq, eval_polyLenExpr, w]
    split_ifs <;> rfl
  have hclose (x : List Bool) :
      |(Randomized.randProb (w x.length) (fun u => M' x u = true) : ℝ) -
        (Randomized.randProb (Randomized.polyLen a k x.length)
          (fun r => M x r = true) : ℝ)| ≤ (1 : ℝ) / 12 := by
    by_cases hx : x.length < n₀
    · have heq : Randomized.randProb (w x.length) (fun u => M' x u = true) =
          Randomized.randProb (Randomized.polyLen a k x.length) (fun r => M x r = true) := by
        simp only [w, if_pos hx]
        apply Randomized.randProb_congr
        intro u
        simp only [M', C, pairFstD_pairEncode, pairSndD_pairEncode, if_pos hx]
      rw [heq, sub_self, abs_zero]
      norm_num
    · simpa only [w, if_neg hx, M', C, pairFstD_pairEncode, pairSndD_pairEncode]
        using hgap x (by omega)
  have hmajority (x : List Bool) : x ∈ L ↔
      (1 / 2 : ℚ) < Randomized.randProb (w x.length) (fun u => M' x u = true) := by
    have hb := abs_le.mp (hclose x)
    constructor
    · intro hx
      have htrue : (2 : ℝ) / 3 ≤
          (Randomized.randProb (Randomized.polyLen a k x.length)
            (fun r => M x r = true) : ℝ) := by
        rw [show (2 : ℝ) / 3 = ((2 / 3 : ℚ) : ℝ) by norm_num, Rat.cast_le]
        exact (hcorrect x).1 hx
      have hhalf : (1 : ℝ) / 2 <
          (Randomized.randProb (w x.length) (fun u => M' x u = true) : ℝ) := by
        linarith
      apply (Rat.cast_lt (K := ℝ)).mp
      simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hhalf
    · intro hx
      by_contra hnot
      have hfalse := (hcorrect x).2 hnot
      rw [Randomized.randProb_bool_false] at hfalse
      have htrue :
          (Randomized.randProb (Randomized.polyLen a k x.length)
            (fun r => M x r = true) : ℝ) ≤ (1 : ℝ) / 3 := by
        rw [show (1 : ℝ) / 3 = ((1 / 3 : ℚ) : ℝ) by norm_num, Rat.cast_le]
        linarith
      have hhalf : (1 : ℝ) / 2 <
          (Randomized.randProb (w x.length) (fun u => M' x u = true) : ℝ) := by
        simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
          (Rat.cast_lt (K := ℝ)).mpr hx
      linarith
  refine ⟨V, w, n₀, hV, hw, fun n hn => if_neg (Nat.not_lt_of_ge hn), ?_⟩
  ext x
  change x ∈ L ↔ 2 ^ w x.length <
    2 * (Finset.univ.filter fun u : Fin (w x.length) → Bool =>
      pairEncode x (List.ofFn u) ∈ V).card
  rw [← Randomized.half_lt_randProb_iff (w x.length) (fun u => pairEncode x u ∈ V)]
  have hp := Randomized.randProb_congr (m := w x.length)
    (A := fun u => M' x u = true) (B := fun u => pairEncode x u ∈ V)
    (fun u => hVeq x (List.ofFn u))
  rw [← hp]
  exact hmajority x

end TCSlib.Cryptography.Randomness.Derand
