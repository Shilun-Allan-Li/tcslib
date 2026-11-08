/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Composability.SequentialZK
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Simulator

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Negligible soundness error for sequential 3-colouring

The quadratic repetition estimate for the sequential 3-colouring construction of
[PS10, Proposition 127.6 and Theorem 175.1].

## Contents

* The eventual dyadic bound for the repeated soundness error.

## Main definitions

The repetition count is `PolyExpr.normal 2 2`, which evaluates to `2 * (N + 1)^2`.

## Main results

* `Composability.negligible_colSeqSound`: raising `1 - 1/N + 2^{-N}` to this repetition
  count gives a negligible function of `N`.
* `Composability.colSeq_efficientProverProof_zk`: the resulting efficient-prover proof and
  computational zero-knowledge corollary.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Proposition 127.6 and Theorem 175.1.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §1.2 (negligible functions).
-/

namespace TCSlib.Cryptography.Composability

open Complexity

/-- The function `(1 - 1/N + (1/2)^N)^{2(N+1)^2}` is negligible: the quantitative estimate
for sequential repetition of the formal 3-colouring soundness bound
[PS10, Proposition 127.6 and Theorem 175.1], with the repetition count fixed explicitly.

**Proof sketch.** The dyadic function is negligible, so twice it is eventually smaller than
`1/N`. Beyond that threshold and `N = 0`, the one-run bound is nonnegative and at most
`1 - 1/(2N)`. This latter base lies in `[0, 1]`, and `2(N+1)^2 ≥ N(2N)`, so the repeated
bound is at most `(1 - 1/(2N))^{N(2N)} ≤ exp(-N) ≤ 2^{-N}`. Eventual domination by the
dyadic negligible function proves the claim; no estimate at `N = 0` is needed. -/
theorem negligible_colSeqSound :
    Negligible (fun N => (1 - 1 / (N : ℝ) + (1 / 2 : ℝ) ^ N) ^
      ((PolyExpr.normal 2 2).eval N)) := by
  have hdyad : Negligible (fun N : ℕ => (1 / 2 : ℝ) ^ N) := by
    simpa only [one_div] using negligible_two_pow_neg
  obtain ⟨N₀, htail⟩ := ((negligible_iff _).mp (hdyad.const_mul 2)) 1
  refine hdyad.mono ⟨max N₀ 1, ?_⟩
  intro N hN
  have hN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN₁ : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hN₁R : (1 : ℝ) ≤ N := by exact_mod_cast hN₁
  have hd : 0 ≤ (1 / 2 : ℝ) ^ N := by positivity
  -- The degree-one tail of twice the dyadic error absorbs half the inverse gap.
  have hscaled : 2 * (1 / 2 : ℝ) ^ N < 1 / (N : ℝ) := by
    have hmul : (0 : ℝ) ≤ 2 * (1 / 2 : ℝ) ^ N := by positivity
    simpa only [pow_one, abs_of_nonneg hmul] using htail N hN₀
  have hrec : 1 / ((2 * N : ℕ) : ℝ) = (1 / 2 : ℝ) * (1 / (N : ℝ)) := by
    rw [Nat.cast_mul, ← one_div_mul_one_div]
    norm_num
  have hsmall : (1 / 2 : ℝ) ^ N ≤ 1 / ((2 * N : ℕ) : ℝ) := by
    rw [hrec]
    linarith only [hscaled]
  have hinv : 1 / (N : ℝ) ≤ 1 := by
    simpa only [div_one] using one_div_le_one_div_of_le zero_lt_one hN₁R
  have ha : 0 ≤ 1 - 1 / (N : ℝ) + (1 / 2 : ℝ) ^ N := by
    linarith only [hinv, hd]
  have hab : 1 - 1 / (N : ℝ) + (1 / 2 : ℝ) ^ N ≤
      1 - 1 / ((2 * N : ℕ) : ℝ) := by
    rw [hrec] at hsmall ⊢
    linarith only [hsmall]
  have hb₀ : 0 ≤ 1 - 1 / ((2 * N : ℕ) : ℝ) := ha.trans hab
  have hb₁ : 1 - 1 / ((2 * N : ℕ) : ℝ) ≤ 1 :=
    sub_le_self _ (by positivity)
  -- A larger exponent decreases a power whose base lies in the unit interval.
  have hexponent : N * (2 * N) ≤ (PolyExpr.normal 2 2).eval N := by
    rw [PolyExpr.eval_normal]
    nlinarith
  calc
    |(1 - 1 / (N : ℝ) + (1 / 2 : ℝ) ^ N) ^ ((PolyExpr.normal 2 2).eval N)| =
        (1 - 1 / (N : ℝ) + (1 / 2 : ℝ) ^ N) ^ ((PolyExpr.normal 2 2).eval N) :=
      abs_of_nonneg (pow_nonneg ha _)
    _ ≤ (1 - 1 / ((2 * N : ℕ) : ℝ)) ^ ((PolyExpr.normal 2 2).eval N) :=
      pow_le_pow_left₀ ha hab _
    _ ≤ (1 - 1 / ((2 * N : ℕ) : ℝ)) ^ (N * (2 * N)) :=
      pow_le_pow_of_le_one hb₀ hb₁ hexponent
    _ ≤ Real.exp (-(N : ℝ)) :=
      one_sub_inv_pow_mul_le_exp (2 * N) N (by omega)
    _ ≤ (2 : ℝ)⁻¹ ^ N := exp_neg_le_inv_two_pow N
    _ = |(1 / 2 : ℝ) ^ N| := by
      rw [abs_of_nonneg hd, one_div]

/-- Quadratic sequential repetition of the commitment-based 3-colouring protocol is an
interactive proof with an efficient prover and is computational zero-knowledge
[PS10, Theorem 124.1, Propositions 127.6 and 128.8, Theorem 175.1].

**Deviation.** The phase count is the explicit polynomial `2(N+1)^2` in the encoded input
length, rather than the graph-dependent `n|E|` of the source. This is a larger sufficient
repetition count for the formal one-run bound `1 - 1/N + 2^{-N}`. The sequential protocol
uses the filler scheduling of `Protocol.seqRep`, not `colProtocolRep`.

**Proof sketch.** Apply sequential repetition to the efficient-prover proof with its
explicit one-run soundness error. The preceding estimate makes the repeated error negligible,
so the error-parametric proof gives an interactive proof. The original proof's bounded honest
prover messages supply the hypothesis of zero-knowledge composition, which applies to
`col_zk`. Here the prover-first base protocol has three moves: each padded six-move phase
contributes two real prover messages and one empty prover filler to the verifier's view.
The composition sketch normalizes simulated phases to that prescribed shape and message
bound, with a canonical fallback for malformed phase views; it assumes no new simulator
output guarantee. The generic repetition statements remain the campaign's admitted fill
targets. -/
theorem colSeq_efficientProverProof_zk {Com : List Bool → List Bool} {ℓ : PolyExpr}
    (hC : Commitment Com ℓ) :
    EfficientProverProof ((colProtocol Com ℓ).seqRep (.normal 2 2)) L3COL R3COL ∧
      ZK ((colProtocol Com ℓ).seqRep (.normal 2 2)) R3COL := by
  have hQ : ∀ n, 1 ≤ (PolyExpr.normal 2 2).eval n := by
    intro n
    rw [PolyExpr.eval_normal]
    exact Nat.succ_le_of_lt (by positivity)
  have hbase := col_efficientProverProofErr hC
  have hrep := EfficientProverProofErr.seqRep hbase (.normal 2 2) hQ
  obtain ⟨B, hB⟩ := hbase.boundedP
  exact ⟨EfficientProverProofErr.efficientProverProof negligible_colSeqSound hrep,
    ZK.seqRep (col_zk hC) hB (.normal 2 2)⟩

end TCSlib.Cryptography.Composability
