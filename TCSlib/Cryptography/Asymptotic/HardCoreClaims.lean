/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.HardCore

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The concrete claims of the proof of the Goldreich–Levin theorem

The concrete claims of the proof of [PS10, Theorem 87.3] (§3.4.3): the oversimplified case,
the `3/4 + ε` case, the good set, Fact 88.4, the pairwise-independence and union-bound
claims about Algorithm 89.6, and the final bound — each the family-level instance
(`FunFamily.glPad`, `FunFamily.glBit`, `FunFamily.glInverter` of
`TCSlib.Cryptography.Asymptotic.HardCore`) of the corresponding concrete lemma of the Garg
layer (`TCSlib/Cryptography/HardcoreBit/*`), through the bridges `FunFamily.predProb_glPad`
and `FunFamily.invProb_glInverter`. (Moved out of `Asymptotic/HardCore.lean` for size; the
statements are those of the audited statement phase.)

## Main definitions

None.

## Main results

* `TCSlib.Cryptography.fact_88_4` — `⟨a, b ⊕ c⟩ = ⟨a, b⟩ ⊕ ⟨a, c⟩` [PS10, Fact 88.4].
* `TCSlib.Cryptography.thm_87_3_1`, `thm_87_3_2`, `thm_87_3_3` — the oversimplified case, the
  `3/4 + ε` case (Algorithm 88.5) and the good set [PS10, §3.4.3].
* `TCSlib.Cryptography.thm_87_3_6`, `thm_87_3_7`, `thm_87_3_8`, `thm_87_3_9` — pairwise
  independent samples, subset sums, the guessing step and the final bound of
  Algorithm 89.6 [PS10, §3.4.3].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.4.2–3.4.3: Theorem 87.3, Fact 88.4, Algorithms 88.5, 89.6.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.5 (Theorem 2.3, Figures 2.3–2.5).
* [GL89] O. Goldreich, L. Levin, *A hard-core predicate for all one-way functions*, STOC 1989.
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ### The concrete claims of the proof of Theorem 87.3 [PS10, §3.4.3]

The setting (inventory Thm-87.3.c) is `FunFamily.glPad`, `FunFamily.glBit`,
`FunFamily.glInverter` over the concrete `HardcoreBit.ip`, `glPad`, `glBit`, `glInverter`,
`secProb` (`Pr_r[A(f(x), r) = ⟨x, r⟩]` for a fixed `x`). Algorithm 88.5 is
`HardcoreBit.majorityInverter` (`majorityRecover`, `trialBit`); Algorithm 89.6 is
`HardcoreBit.guessInverter` (`guessRecover`, the subroutine `C` realised by guessing the
`k = log m` bits `b'_j` and forming subset sums). Each claim below is the family-level
instance of the corresponding concrete lemma. -/

/-- **Fact 88.4** [PS10]: `⟨a, b ⊕ c⟩ = ⟨a, b⟩ ⊕ ⟨a, c⟩` (bit strings as a Boolean ring, `+` is
XOR); the concrete `HardcoreBit.ip_add`. -/
theorem fact_88_4 {n : ℕ} (a b c : Fin n → Bool) :
    HardcoreBit.ip a (b + c) = HardcoreBit.ip a b + HardcoreBit.ip a c :=
  HardcoreBit.ip_add a b c

/-- **The oversimplified case** [PS10, §3.4.3; inventory Thm-87.3.1]: if `A` predicts `⟨x, r⟩`
from `g(x, r)` with probability one, the inverter querying `e_1, …, e_n` (the concrete
`perfectRecover`, `⟨x, e_i⟩ = x_i`) inverts `g` with probability one. -/
theorem thm_87_3_1 (𝓕 : FunFamily) {ρ : Type*} [Fintype ρ] (n : ℕ)
    (A : (Fin (𝓕.glPad.outLen.eval n) → Bool) → ρ → Bool)
    (h : predProb (𝓕.glPad.f n) (𝓕.glBit n) A = 1) :
    invProb (𝓕.glPad.f n) (𝓕.glInverter n (HardcoreBit.perfectRecover
      fun y r => A (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y) r)) = 1 := by
  rw [FunFamily.predProb_glPad] at h
  rw [FunFamily.invProb_glInverter]
  exact HardcoreBit.invProb_perfectInverter _ _ h

/-- **The less simplified case** [PS10, §3.4.3, Algorithm 88.5; inventory Thm-87.3.2]: if `A`
predicts `⟨x, r⟩` with probability `3/4 + ε` and `n ≤ 2ε²T`, the inverter taking the majority
of `T` guesses `A(y, r) ⊕ A(y, r ⊕ e_i)` per bit inverts `g` with probability at least `ε/4`
(the text's Chernoff bound is Chebyshev with pairwise independence). -/
theorem thm_87_3_2 (𝓕 : FunFamily) {ρ : Type*} [Fintype ρ] [Nonempty ρ] (n : ℕ)
    (A : (Fin (𝓕.glPad.outLen.eval n) → Bool) → ρ → Bool) {T : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hT : (𝓕.inLen.eval n : ℝ) ≤ 2 * ε ^ 2 * T)
    (h : 3 / 4 + ε ≤ predProb (𝓕.glPad.f n) (𝓕.glBit n) A) :
    ε / 4 ≤ invProb (𝓕.glPad.f n) (𝓕.glInverter n (HardcoreBit.majorityRecover
      (fun y r => A (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y) r) T)) := by
  rw [FunFamily.predProb_glPad] at h
  rw [FunFamily.invProb_glInverter]
  exact HardcoreBit.invProb_majorityInverter _ _ hε hT h

/-- **The good set is large** [PS10, §3.4.3; inventory Thm-87.3.3]: if `A` predicts `⟨x, r⟩`
with probability `c + ε` (`c = 3/4` or `1/2`), then `Pr_x[Pr_r[A(f(x), r) = ⟨x, r⟩] ≥ c + ε/2] ≥ ε/2`
(the text's displayed chain `< ε/2 + (1 − ε/2)(c + ε/2) < c + ε`). -/
theorem thm_87_3_3 (𝓕 : FunFamily) {ρ : Type*} [Fintype ρ] (n : ℕ)
    (A : (Fin (𝓕.glPad.outLen.eval n) → Bool) → ρ → Bool) {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (h : c + ε ≤ predProb (𝓕.glPad.f n) (𝓕.glBit n) A) :
    ε / 2 ≤ uprob fun x => c + ε / 2 ≤ HardcoreBit.secProb (𝓕.f n)
      (fun y r => A (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y) r) x := by
  rw [FunFamily.predProb_glPad] at h
  exact HardcoreBit.half_le_uprob_good _ _ hc hε h

/-- **Pairwise-independent samples suffice** [PS10, §3.4.3; inventory Thm-87.3.6]: for a good
`x` (`secProb ≥ 1/2 + ε/2`) and `k ≥ 1`, each bit of the ideal recovery procedure (correct
guesses `b_L = ⟨x, S_L⟩`) is wrong with probability at most `1/(ε²(2^k − 1))` — the text's
`1/(mε'²)` with `m = 2^k − 1` nonempty subsets and `ε' = ε/2`, by the pairwise-independent
sampling inequality (`chebyshev_pairwise`); the concrete `uprob_idealRecover_ne_le`. -/
theorem thm_87_3_6 {n : ℕ} {β ρ : Type*} [Fintype ρ] [Nonempty ρ] (f : (Fin n → Bool) → β)
    (A : β × (Fin n → Bool) → ρ → Bool) {k : ℕ} (hk : 0 < k) (x : Fin n → Bool) (i : Fin n)
    {ε : ℝ} (hε : 0 < ε) (hx : 1 / 2 + ε / 2 ≤ HardcoreBit.secProb f A x) :
    uprob (fun ω : (Fin k → Fin n → Bool) × (Fin n → HardcoreBit.NESubset k → ρ) =>
      HardcoreBit.idealRecover f A x ω.1 ω.2 i ≠ x i) ≤ 1 / (ε ^ 2 * ((2 : ℝ) ^ k - 1)) :=
  HardcoreBit.uprob_idealRecover_ne_le f A hk x i hε hx

/-- **Subset sums are pairwise independent and uniform** [PS10, §3.4.3, "show this!";
inventory Thm-87.3.7]: for uniform `s_1, …, s_k ∈ {0,1}^n`, the `2^k − 1` strings
`r_L = ⊕_{j ∈ L} s_j` over nonempty `L ⊆ [k]` are each uniform and pairwise independent
(the concrete `pairwiseUniform_subsetSum`; `card_nonempty_finset` counts them). -/
theorem thm_87_3_7 {n k : ℕ} :
    HardcoreBit.PairwiseUniform fun (L : HardcoreBit.NESubset k) (s : Fin k → Fin n → Bool) =>
      HardcoreBit.subsetSum L.1 s :=
  HardcoreBit.pairwiseUniform_subsetSum

/-- **All guesses are right with probability `1/m = 2^{−k}`, and then every `b_L` is right**
[PS10, §3.4.3; inventory Thm-87.3.8]: the guessed bits `b'_1 ⋯ b'_k` equal `⟨x, s_1⟩ ⋯ ⟨x, s_k⟩`
with probability `1/2^k` (`uprob_guess_eq`), and under that event the recovery procedure
computes `b_L = ⟨x, S_L⟩` for every `L`, i.e. it is the ideal procedure
(`guessRecover_correct_guess`). -/
theorem thm_87_3_8 {n : ℕ} {β ρ : Type*} [Fintype ρ] (f : (Fin n → Bool) → β)
    (A : β × (Fin n → Bool) → ρ → Bool) {k : ℕ} (x : Fin n → Bool) (s : Fin k → Fin n → Bool)
    (cs : Fin n → HardcoreBit.NESubset k → ρ) :
    uprob (fun b : Fin k → Bool => b = fun j => HardcoreBit.ip x (s j)) = 1 / 2 ^ k ∧
      HardcoreBit.guessRecover A k (f x) (s, fun j => HardcoreBit.ip x (s j), cs) =
        HardcoreBit.idealRecover f A x s cs :=
  ⟨HardcoreBit.uprob_guess_eq _, HardcoreBit.guessRecover_correct_guess f A x s cs⟩

/-- **The final bound of the general case** [PS10, §3.4.3, Algorithm 89.6; inventory
Thm-87.3.9]: if `A` predicts `⟨x, r⟩` from `g(x, r)` with probability `1/2 + ε` and
`2n ≤ ε²(2^k − 1)`, the inverter of Algorithm 89.6 with `k` guessed bits inverts `g` with
probability at least `ε/(4·2^k)`; with `ε² 2^k ≤ 4n` this is at least `ε³/(16n)`.

**Deviation:** the text's constant is `ε'/(2m) = ε³/(32n)` with `ε' = ε/2`, `m = 2n/ε'²`
(source error 37); the concrete bound is stronger. -/
theorem thm_87_3_9 (𝓕 : FunFamily) {ρ : Type*} [Fintype ρ] [Nonempty ρ] (n : ℕ)
    (A : (Fin (𝓕.glPad.outLen.eval n) → Bool) → ρ → Bool) {k : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hk : 2 * (𝓕.inLen.eval n : ℝ) ≤ ε ^ 2 * ((2 : ℝ) ^ k - 1))
    (h : 1 / 2 + ε ≤ predProb (𝓕.glPad.f n) (𝓕.glBit n) A) :
    ε / (4 * 2 ^ k) ≤ invProb (𝓕.glPad.f n) (𝓕.glInverter n (HardcoreBit.guessRecover
      (fun y r => A (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y) r) k)) ∧
    (ε ^ 2 * (2 : ℝ) ^ k ≤ 4 * 𝓕.inLen.eval n →
      ε ^ 3 / (16 * 𝓕.inLen.eval n) ≤ invProb (𝓕.glPad.f n) (𝓕.glInverter n
        (HardcoreBit.guessRecover
          (fun y r => A (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y) r) k))) := by
  rw [FunFamily.predProb_glPad] at h
  rw [FunFamily.invProb_glInverter]
  exact ⟨HardcoreBit.invProb_guessInverter _ _ hε hk h,
    fun hk' => HardcoreBit.invProb_guessInverter_cubic _ _ hε hk hk' h⟩

end TCSlib.Cryptography
