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

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Theorem 163.7 and the hybrid argument in §6.2.3.
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReduction

open Complexity Turing TCSlib.Cryptography

/-- For a polynomial-time `rebuild` and advice `β n` of polynomially bounded length,
there is one non-uniform PPT test that runs `D` on
`rebuild ⟨1^n, ⟨challenge, β n⟩⟩`, at parameter `n`, with the same random bits.
[PS10, Theorem 163.7, non-uniform reduction]

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
  have hAccept {σ : Type*} [Fintype σ] (X : σ → List Bool) :
      acceptProb (fun t => rebuild (pairEncode (List.replicate n true)
        (pairEncode (X t) (advice n (μ n))))) (D.distinguisherL n) =
          acceptProb X (R.distinguisherL n) := by
    rw [← EnsembleLemmas.acceptProb_coins_equiv (NUPPT.coinsCongr hcoins.symm n)
      X (R.distinguisherL n), acceptProb_def, acceptProb_def]
    congr 1
    funext t
    rw [hRun]
  change distAdv _ _ _ ≤ ε n
  rw [distAdv_def, hAccept, hAccept]
  exact hBound n (offset n (μ n)) (len n (μ n)) (hFit n (μ n)) (m₀ n (μ n)) (m₁ n (μ n))

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReduction
