/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Scheme
import TCSlib.Cryptography.LWE.Experiments

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Secret-key GSW: batched encryption under one secret, and its DLWE security

## Main definitions

* `rowEquiv`: split `m = k·N` LWE rows into `k` blocks of `N`.
* `symEncrypt`: `k` ciphertexts `Cᵢ = Āᵢ + μᵢ G` from one LWE challenge, block `i` of the
  augmented sample matrix supplying `Āᵢ`; one common secret for all of them.

## Main results

* `encrypts_symEncrypt`: every secret-key ciphertext has noise at most `B` (not `m·B`).
* `distAdv_symEncrypt_le`: two message vectors' batches differ by at most two DLWE
  advantages with `k·N` rows; no leftover hashing.

## References

* [AP14] J. Alperin-Sheriff, C. Peikert, ePrint 2014/094 version dated 13 June 2014,
  Section 3.2 (`GSW.Enc`: "a fresh ciphertext is just `μG` plus a matrix of `nℓ` independent
  LWE samples").
* [BV14] Z. Brakerski, V. Vaikuntanathan, ePrint 2013/541, Section 3.1 (`NCCrypt.SecEnc`:
  "a secret-key encryption of `μ` is somewhat less noisy than a public-key encryption").
* [Wu24] D. Wu, CS395T lecture notes, Spring 2024, Definition 20.5 (the batched direct
  pattern of the existing symmetric Regev scheme).

**Deviations.** The secret is uniform ([AP14] draws it from the error law, which needs a
separate normal-form assumption excluded by plan decision D1). The batch of `k` ciphertexts
uses one DLWE instance with exactly `k·N` rows, so multi-message security is part of the
statement rather than a further hybrid. Row reindexing goes through the published equivalence
`rowEquiv`, the domain-equivalence pattern used elsewhere for type-valued parameters.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

open Encryption.PublicKey

/-- Split `m = k·N` LWE rows into `k` blocks of `N` consecutive rows. Technical glue. -/
def rowEquiv (P : Parameters) {k : ℕ} (hN : P.lwe.samples = k * P.columns) :
    Fin k × Fin P.columns ≃ Fin P.lwe.samples :=
  finProdFinEquiv.trans (finCongr hN.symm)

/-- `rowEquiv P hN` is `finProdFinEquiv` followed by the cast along `hN`. -/
theorem rowEquiv_eq (P : Parameters) {k : ℕ} (hN : P.lwe.samples = k * P.columns) :
    rowEquiv P hN = finProdFinEquiv.trans (finCongr hN.symm) := rfl

/-- Batched secret-key GSW encryption [AP14, Section 3.2, `GSW.Enc`; BV14, Section 3.1,
`NCCrypt.SecEnc`, gadget form]: from an LWE challenge `(A, b)` with `k·N` rows, ciphertext `i`
is the block-`i` columns of the augmented matrix plus `μᵢ G`. -/
def symEncrypt (P : Parameters) {k : ℕ} (hN : P.lwe.samples = k * P.columns)
    (c : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus))
    (μ : Fin k → Bool) : Fin k → Ciphertext P :=
  fun i => (Regev.augmented P.lwe c).submatrix id (fun j => rowEquiv P hN (i, j)) +
    ((μ i).toNat : ZMod P.lwe.modulus) • gadget P

/-- Ciphertext `i` is the reindexed block of the augmented challenge plus `μᵢ G`. -/
theorem symEncrypt_apply (P : Parameters) {k : ℕ} (hN : P.lwe.samples = k * P.columns)
    (c : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus))
    (μ : Fin k → Bool) (i : Fin k) :
    symEncrypt P hN c μ i = (Regev.augmented P.lwe c).submatrix id (fun j => rowEquiv P hN (i, j)) +
      ((μ i).toNat : ZMod P.lwe.modulus) • gadget P := rfl

/-- **Secret-key noise.** On a real LWE challenge with row errors bounded by `B`, every
secret-key ciphertext encrypts its bit under `t = (−s,1)` with noise at most `B` [AP14,
Section 3.2, "Notice that `sᵗC = eᵗ + μ·sᵗG`"; BV14, Section 3.1].

**Proof sketch.** The witness is `j ↦ e (rowEquiv (i, j))`, bounded by `B`.
`Matrix.vecMul_add`, `Matrix.vecMul_smul` split `tᵗ Cᵢ`; the block of `tᵗ Ā` is `tᵗ Ā` read at
the reindexed columns (`Matrix.submatrix_apply`), equal to `e ∘ rowEquiv` by
`vecMul_secretVector_augmented`. -/
theorem encrypts_symEncrypt (P : Parameters) {k : ℕ} (hN : P.lwe.samples = k * P.columns)
    (A : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus))
    (s : Fin P.lwe.dimension → ZMod P.lwe.modulus) (e : Fin P.lwe.samples → ℤ) (B : ℕ)
    (he : ∀ i, (e i).natAbs ≤ B) (μ : Fin k → Bool) (i : Fin k) :
    Encrypts P (secretVector P s) ((μ i).toNat : ℤ) B
      (symEncrypt P hN (A, LWE.noisyValues P.lwe A s e) μ i) := by
  rw [encrypts_iff]
  refine ⟨fun j => e (rowEquiv P hN (i, j)), fun j => he _, ?_⟩
  -- Step 1: `tᵗ Cᵢ = (tᵗ Ā) ∘ rowEquiv(i, ·) + μᵢ tᵗ G`.
  rw [symEncrypt_apply, Matrix.vecMul_add, Matrix.vecMul_smul, Int.cast_natCast, add_comm]
  congr 1
  funext j
  -- Step 2: column `j` of the block is column `rowEquiv (i, j)` of `Ā`, read by
  -- `vecMul_secretVector_augmented`.
  change ∑ a, secretVector P s a *
    (Regev.augmented P.lwe (A, LWE.noisyValues P.lwe A s e)).submatrix
      id (fun j => rowEquiv P hN (i, j)) a j = _
  simp only [Matrix.submatrix_apply, id_eq]
  exact congrFun (vecMul_secretVector_augmented P A s e) (rowEquiv P hN (i, j))

/-- For every message vector `μ`, the batch map `c ↦ symEncrypt P hN c μ` on challenges is a
bijection onto `Fin k → Ciphertext P`, given as an equivalence. Technical glue.

**Proof sketch.** Compose the augmentation bijection (`Regev.augmented_bijective`), the
column reindexing `M ↦ (i ↦ M · rowEquiv(i, ·))` (inverse: read column `c` of block
`rowEquiv⁻¹ c`), and the translation by `i ↦ μᵢ G`. -/
private theorem exists_equiv_symEncrypt (P : Parameters) {k : ℕ}
    (hN : P.lwe.samples = k * P.columns) (μ : Fin k → Bool) :
    ∃ E : (Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
        (Fin P.lwe.samples → ZMod P.lwe.modulus)) ≃ (Fin k → Ciphertext P),
      ∀ c, E c = symEncrypt P hN c μ := by
  -- Step 1: augmentation.
  let E₁ := Equiv.ofBijective _ (Regev.augmented_bijective P.lwe)
  -- Step 2: column reindexing through `rowEquiv`.
  let E₂ : Matrix (Fin (P.lwe.dimension + 1)) (Fin P.lwe.samples) (ZMod P.lwe.modulus) ≃
      (Fin k → Ciphertext P) :=
    { toFun := fun M i => M.submatrix id (fun j => rowEquiv P hN (i, j))
      invFun := fun F a c => F ((rowEquiv P hN).symm c).1 a ((rowEquiv P hN).symm c).2
      left_inv := by
        intro M
        funext a c
        change M a (rowEquiv P hN (((rowEquiv P hN).symm c).1, ((rowEquiv P hN).symm c).2)) =
          M a c
        rw [Prod.mk.eta, Equiv.apply_symm_apply]
      right_inv := by
        intro F
        funext i a j
        change F ((rowEquiv P hN).symm (rowEquiv P hN (i, j))).1 a
          ((rowEquiv P hN).symm (rowEquiv P hN (i, j))).2 = F i a j
        rw [Equiv.symm_apply_apply] }
  -- Step 3: translation by the message gadgets.
  refine ⟨E₁.trans (E₂.trans
    (Equiv.addRight fun i => ((μ i).toNat : ZMod P.lwe.modulus) • gadget P)), fun c => ?_⟩
  funext i
  rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.coe_addRight, Equiv.ofBijective_apply,
    symEncrypt_apply]
  rfl

/-- **Concrete IND-CPA bound for batched secret-key GSW** [AP14, Section 3.2, "The IND-CPA
security of the scheme follows immediately from the assumed hardness of LWE"; Wu24,
Lecture 21, the two-hybrid pattern]. For two message vectors, the distributions of the `k`
ciphertexts under one uniform secret differ by at most two DLWE advantages with `k·N` rows.

**Proof sketch.** As `Encryption.Symmetric.Regev.distAdv_encrypt_le`: each real batch is
`symEncrypt` of the actual LWE sample (`acceptProb_def`); on the uniform side,
`(A,b) ↦ symEncrypt P hN (A,b) μ` is an equivalence onto `Fin k → Ciphertext P` (the private
glue `exists_equiv_symEncrypt`: `Regev.augmented_bijective`, the column reindexing by
`rowEquiv`, and translation by `μG`), so by `acceptProb_comp_equiv` both ideal acceptance
probabilities equal that of a uniform batch. Insert it between the two real experiments
(`LWE.decisionAdvantage_eq`, `distAdv_def`) and use the triangle inequality. -/
theorem distAdv_symEncrypt_le {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters) {k : ℕ} (hN : P.lwe.samples = k * P.columns) (χ : LWE.Noise)
    (μ₀ μ₁ : Fin k → Bool) (D : (Fin k → Ciphertext P) → ρ → Bool) :
    distAdv (fun r => symEncrypt P hN (LWE.sample P.lwe χ r) μ₀)
        (fun r => symEncrypt P hN (LWE.sample P.lwe χ r) μ₁) D ≤
      LWE.decisionAdvantage P.lwe χ (fun c r => D (symEncrypt P hN c μ₀) r) +
      LWE.decisionAdvantage P.lwe χ (fun c r => D (symEncrypt P hN c μ₁) r) := by
  -- Step 1: each real batch is `symEncrypt` of the actual LWE sample.
  have hreal (μ : Fin k → Bool) :
      acceptProb (fun r => symEncrypt P hN (LWE.sample P.lwe χ r) μ) D =
        acceptProb (LWE.sample P.lwe χ) (fun c r => D (symEncrypt P hN c μ) r) := by
    rw [acceptProb_def, acceptProb_def]
  -- Step 2: on a uniform challenge, every batch is a uniform batch of ciphertexts.
  have hideal (μ : Fin k → Bool) :
      acceptProb (id : (Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
        (Fin P.lwe.samples → ZMod P.lwe.modulus)) → _) (fun c r => D (symEncrypt P hN c μ) r) =
        acceptProb (id : (Fin k → Ciphertext P) → _) D := by
    obtain ⟨E, hE⟩ := exists_equiv_symEncrypt P hN μ
    rw [← acceptProb_comp_equiv E id D, acceptProb_def, acceptProb_def]
    simp only [id_eq, hE]
  -- Step 3: insert the uniform batch and use the triangle inequality.
  rw [LWE.decisionAdvantage_eq, LWE.decisionAdvantage_eq, distAdv_def, distAdv_def,
    distAdv_def, hideal μ₀, hideal μ₁, ← hreal μ₀, ← hreal μ₁]
  calc
    _ ≤ |acceptProb (fun r => symEncrypt P hN (LWE.sample P.lwe χ r) μ₀) D -
          acceptProb (id : (Fin k → Ciphertext P) → _) D| +
        |acceptProb (id : (Fin k → Ciphertext P) → _) D -
          acceptProb (fun r => symEncrypt P hN (LWE.sample P.lwe χ r) μ₁) D| :=
      abs_sub_le _ _ _
    _ = _ := by rw [abs_sub_comm (acceptProb (id : (Fin k → Ciphertext P) → _) D)]

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
