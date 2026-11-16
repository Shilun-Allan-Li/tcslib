/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.SpecialEncryptionMulti
import TCSlib.Complexity.Randomized.Closure
import TCSlib.Cryptography.Asymptotic.Sampling

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Advice and averaging for a slice-encryption reduction

A polynomial-time reconstruction can use polynomial-length advice without depending
on the challenge key or nonces. The machine below keeps the original distinguisher's
random tape and runs it at the same security parameter.

## Main definitions

There are no new definitions.

## Main results

* `exists_adviceReduction`: a reconstruction with fixed advice is a non-uniform PPT test.
* `reconstruction_negligible`: one negligible bound covers all bounded advice choices.
* `distAdv_fibers_le`: a uniform bound survives averaging over auxiliary randomness.
* `distAdv_chain_le`: a chain of `t` bounded steps has advantage at most `t ε`.
* `chain_negligible`: a polynomially bounded chain preserves a uniform negligible bound.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Theorem 163.7 and the hybrid argument in §6.2.3.
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, UC Berkeley lecture notes,
  draft of 22 January 2026, Lemma 3.3 (the hybrid argument).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReduction

open Complexity Turing TCSlib.Cryptography

/-- For a polynomial-time `rebuild` and advice `β n` of polynomially bounded length,
there is one non-uniform PPT test that runs `D` on
`rebuild ⟨1^n, ⟨challenge, β n⟩⟩`, at parameter `n`, with the same random bits.
[PS10, Theorem 163.7, non-uniform reduction]
`∃ R : NUPPT, ∃ hcoins : R.coins = D.coins, ∀ n challenge (r : D.Coins n), R.distinguisherL n
challenge (NUPPT.coinsCongr hcoins.symm n r) = D.distinguisherL n (rebuild (pairEncode
(List.replicate n true) (pairEncode challenge (β n)))) r`.

**Proof sketch.** Use the existing parameter-aware composition constructor to run the
reconstruction before `D`, then the advice constructor to fix `β`. The published coin
congruence preserves the entire tape, so the resulting tests agree pointwise. -/
theorem exists_adviceReduction (D : NUPPT) {rebuild : List Bool → List Bool}
    (hRebuild : PolyTimeComputable rebuild) (β : ℕ → List Bool) (b : PolyExpr)
    (hβ : ∀ n, (β n).length ≤ b.eval n) :
    ∃ R : NUPPT, ∃ hcoins : R.coins = D.coins,
      ∀ n challenge (r : D.Coins n),
        R.distinguisherL n challenge (NUPPT.coinsCongr hcoins.symm n r) =
          D.distinguisherL n
            (rebuild (pairEncode (List.replicate n true) (pairEncode challenge (β n)))) r := by
  obtain ⟨C, hCc, _, _, hC⟩ :=
    D.exists_compParam hRebuild polyTimeComputable_pairSndD
  obtain ⟨R, hRc, hR⟩ := C.exists_withAdvice β b hβ
  refine ⟨R, hRc.trans hCc, ?_⟩
  intro n challenge r
  rw [NUPPT.distinguisherL_eq, NUPPT.distinguisherL_eq, NUPPT.runAt_eq,
    NUPPT.runAt_eq, NUPPT.coinsCongr_ofFn, hR, hC, pairSndD_pairEncode,
    NUPPT.advInput_eq]

/-- A polynomial-time reconstruction of two slice-encryption experiments has a negligible
distinguishing advantage uniformly over a finite family of polynomial-length advice choices.
Slices and deterministic messages may depend on the choice; the reconstruction is fixed.
[PS10, Theorem 163.7, fixing worst inputs, hybrid index and auxiliary randomness]
`∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n a, distAdv (fun t => rebuild (pairEncode (List.replicate n true)
(pairEncode (sliceMultiEncDist G n (q.eval n) (offset n a) (len n a) (m₀ n a) t) (advice n a))))
(fun t => rebuild (pairEncode (List.replicate n true) (pairEncode (sliceMultiEncDist G n (q.eval n)
(offset n a) (len n a) (m₁ n a) t) (advice n a)))) (D.distinguisherL n) ≤ ε n`.

**Proof sketch.** At each parameter choose the advice option maximizing the reconstructed
advantage. Hard-wire this polynomial-length option into one reduction, independent of the
challenge key and nonces. The reduction's pointwise contract and coin equivalence identify
its two acceptance probabilities with the reconstructed experiments. Slice multi-message
security gives one negligible bound for this reduction, and maximality extends it to every
option. This does not assert that a reconstruction or a sampler identity exists. -/
theorem reconstruction_negligible {L : PolyExpr}
    {G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L.eval n) → Bool)}
    (hSecure : SliceMultiMessageSecure G) (D : NUPPT) (q b : PolyExpr)
    {A : ℕ → Type*} [∀ n, Fintype (A n)] [∀ n, Nonempty (A n)]
    (advice : ∀ n, A n → List Bool) (hAdvice : ∀ n a, (advice n a).length ≤ b.eval n)
    {rebuild : List Bool → List Bool} (hRebuild : PolyTimeComputable rebuild)
    (offset len : ∀ n, A n → Fin (q.eval n + 1) → ℕ)
    (hFit : ∀ n a i, offset n a i + n + len n a i ≤ L.eval n)
    (m₀ m₁ : ∀ n a i, Fin (len n a i) → Bool) :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n a,
      distAdv
        (fun t => rebuild (pairEncode (List.replicate n true)
          (pairEncode (sliceMultiEncDist G n (q.eval n) (offset n a) (len n a) (m₀ n a) t)
            (advice n a))))
        (fun t => rebuild (pairEncode (List.replicate n true)
          (pairEncode (sliceMultiEncDist G n (q.eval n) (offset n a) (len n a) (m₁ n a) t)
            (advice n a)))) (D.distinguisherL n) ≤ ε n := by
  classical
  let gap := fun n (a : A n) => distAdv
    (fun t => rebuild (pairEncode (List.replicate n true)
      (pairEncode (sliceMultiEncDist G n (q.eval n) (offset n a) (len n a) (m₀ n a) t)
        (advice n a))))
    (fun t => rebuild (pairEncode (List.replicate n true)
      (pairEncode (sliceMultiEncDist G n (q.eval n) (offset n a) (len n a) (m₁ n a) t)
        (advice n a)))) (D.distinguisherL n)
  have hMax : ∀ n, ∃ a : A n, ∀ a', gap n a' ≤ gap n a := by
    intro n
    obtain ⟨a, _, ha⟩ := Finset.exists_max_image Finset.univ (gap n) Finset.univ_nonempty
    exact ⟨a, fun a' => ha a' (Finset.mem_univ a')⟩
  choose μ hμ using hMax
  obtain ⟨R, hcoins, hRun⟩ := exists_adviceReduction D hRebuild
    (fun n => advice n (μ n)) b (fun n => hAdvice n (μ n))
  obtain ⟨ε, hε, hBound⟩ := (sliceMultiMessageSecure_iff G).mp hSecure R q
  refine ⟨ε, hε, fun n a => (hμ n a).trans ?_⟩
  have hAccept {σ : Type} [Fintype σ] (X : σ → List Bool) :
      acceptProb (fun t => rebuild (pairEncode (List.replicate n true)
        (pairEncode (X t) (advice n (μ n))))) (D.distinguisherL n) =
          acceptProb X (R.distinguisherL n) := by
    rw [← EnsembleLemmas.acceptProb_coins_equiv (NUPPT.coinsCongr hcoins.symm n)
      X (R.distinguisherL n), acceptProb_def, acceptProb_def]
    congr 1
    funext t
    rw [hRun]
  change distAdv _ _ _ ≤ ε n
  rw [distAdv_def,
    hAccept (sliceMultiEncDist G n (q.eval n) (offset n (μ n)) (len n (μ n)) (m₀ n (μ n))),
    hAccept (sliceMultiEncDist G n (q.eval n) (offset n (μ n)) (len n (μ n)) (m₁ n (μ n)))]
  simpa only [distAdv_def] using
    hBound n (offset n (μ n)) (len n (μ n)) (hFit n (μ n)) (m₀ n (μ n)) (m₁ n (μ n))

/-- If every fixed auxiliary seed gives advantage at most nonnegative `ε`, then averaging
that seed independently of the challenge and distinguisher coins also gives advantage at
most `ε`. This permits the auxiliary keys, nonces and shifts to be fixed in the reduction.
[PS10, Theorem 163.7, averaging the remaining randomness]
`distAdv (fun r : α × β => X r.1 r.2) (fun r : α × β => Y r.1 r.2) D ≤ ε`.

**Proof sketch.** Reassociate the joint sample and test coins, then apply the existing
product-probability equation. Each acceptance probability becomes the average of its
fixed-seed probabilities. The public bound for averages of pointwise close functions
gives the claim. -/
theorem distAdv_fibers_le {α β γ ρ : Type*} [Fintype α] [Fintype β] [Fintype ρ]
    (X Y : α → β → γ) (D : γ → ρ → Bool) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ a, distAdv (X a) (Y a) D ≤ ε) :
    distAdv (fun r : α × β => X r.1 r.2) (fun r : α × β => Y r.1 r.2) D ≤ ε := by
  have hAccept (Z : α → β → γ) :
      acceptProb (fun r : α × β => Z r.1 r.2) D =
        uexp (fun a => acceptProb (Z a) D) := by
    simp only [acceptProb_def]
    rw [← uprob_comp_equiv (Equiv.prodAssoc α β ρ).symm, uprob_prod]
    rfl
  rw [distAdv_def, hAccept X, hAccept Y]
  apply abs_uexp_sub_le hε
  intro a
  simpa only [distAdv_def] using h a

/-- If each of `t` consecutive hybrids has distinguishing advantage at most `ε`, then
the endpoints have advantage at most `t ε`. The assertion includes an empty chain.
[PS10, Theorem 163.7, the gate hybrid; Gar26, Lemma 3.3]
`distAdv (H 0) (H t) D ≤ (t : ℝ) * ε`. -/
theorem distAdv_chain_le {σ γ ρ : Type*} [Fintype σ] [Fintype ρ]
    (H : ℕ → σ → γ) (D : γ → ρ → Bool) (t : ℕ) (ε : ℝ)
    (h : ∀ i < t, distAdv (H i) (H (i + 1)) D ≤ ε) :
    distAdv (H 0) (H t) D ≤ (t : ℝ) * ε := by
  rw [distAdv_def]
  refine (abs_sub_le_sum_hybrids (fun i => acceptProb (H i) D) t).trans ?_
  calc
    _ ≤ ∑ i ∈ Finset.range t, ε := Finset.sum_le_sum fun i hi => by
      simpa only [distAdv_def] using h i (Finset.mem_range.mp hi)
    _ = (t : ℝ) * ε := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- A polynomially bounded chain with a negligible bound on every neighboring advantage
has a negligible endpoint advantage, uniformly over the same input family. Zero steps and
signed negligible bounds are included. [PS10, Theorem 163.7, summing the gate hybrids]
`∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n a, distAdv (H n a 0) (H n a (steps n)) (D.distinguisherL n) ≤ ε n`.

**Proof sketch.** Replace the neighboring bound by its absolute value, which is still
negligible by the existing domination rule. Apply the finite-chain bound and enlarge the
number of steps to its polynomial envelope. The public polynomial-times-negligible theorem
then gives one bound valid for every input. -/
theorem chain_negligible {I σ : ℕ → Type*} [∀ n, Fintype (σ n)]
    (H : ∀ n, I n → ℕ → σ n → List Bool) (D : NUPPT) (steps : ℕ → ℕ) (p : PolyExpr)
    (hSteps : ∀ n, steps n ≤ p.eval n) {μ : ℕ → ℝ} (hμ : Negligible μ)
    (h : ∀ n a i, i < steps n → distAdv (H n a i) (H n a (i + 1))
      (D.distinguisherL n) ≤ μ n) :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n a,
      distAdv (H n a 0) (H n a (steps n)) (D.distinguisherL n) ≤ ε n := by
  have hAbs : Negligible (fun n => |μ n|) :=
    hμ.mono ⟨0, fun _ _ => by rw [abs_abs]⟩
  refine ⟨fun n => (p.eval n : ℝ) * |μ n|,
    EnsembleLemmas.negligible_polyExpr_mul p hAbs, ?_⟩
  intro n a
  refine (distAdv_chain_le (H n a) (D.distinguisherL n) (steps n) |μ n|
    (fun i hi => (h n a i hi).trans (le_abs_self _))).trans ?_
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hSteps n) (abs_nonneg _)

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReduction
