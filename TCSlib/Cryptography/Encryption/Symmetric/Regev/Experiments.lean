/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.Symmetric.Regev.Basic
import TCSlib.Cryptography.LWE.Experiments

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Concrete security bound for direct Regev symmetric encryption

## Main definitions

* `encryptDist`: sample a uniform matrix, one uniform secret and independent noise seeds.

## Main results

`acceptProb_uniform_shift` proves that codepoint translation hides a fixed plaintext
in the ideal uniform experiment. `distAdv_encrypt_le` proves the two-reduction bound.
Both results are at fixed parameters and make no running-time claims.

## References

* [Wu24] D. Wu, CS395T *Topics in Cryptography*, Spring 2024 lecture notes,
  compilation last updated 30 April 2024, Definition 20.5 and Lecture 21.
* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Definition 4.2.3.

No asymptotic assumption is strengthened here. In particular, an efficient
multi-message bridge requires the sample schedule `κ * (Q(κ) + 1)`, implemented
preprocessing and polynomial-length advice for the worst message pair. Adaptive CPA
and the existing machine-valued `PrivateKeyScheme` bridge are later owner-coordinated work.
-/

namespace TCSlib.Cryptography.Encryption.Symmetric.Regev

open LWE (Parameters Noise)

variable {ρ : Type*} [Fintype ρ] [Nonempty ρ]

/-- The encryption sampler uses a uniform matrix, one common uniform secret, and
independent scalar-noise seeds for all message bits [Wu24, Definition 20.5;
Pei16, Definition 4.2.3, finite-seed specialization]. -/
def encryptDist (P : Parameters) (χ : Noise) (μ : Fin P.samples → Bool)
    (r : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      ((Fin P.dimension → ZMod P.modulus) × (Fin P.samples → χ.Coins))) :
    Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus) :=
  encrypt P r.2.1 r.1 (fun i => χ.sample (r.2.2 i)) μ

attribute [simps (config := { isSimp := false }) fst snd] encryptDist

/-- The encryption sampler is exactly codepoint translation of the existing LWE
sample map [Wu24, Definition 20.5; Pei16, Definition 4.2.3].

**Proof sketch.** Read the encryption and shift projections and `LWE.sample_fst`,
`LWE.sample_snd`; both components agree on the same matrix, secret and row seeds. -/
theorem encryptDist_eq_shift_sample (P : Parameters) (χ : Noise)
    (μ : Fin P.samples → Bool)
    (r : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      ((Fin P.dimension → ZMod P.modulus) × (Fin P.samples → χ.Coins))) :
    encryptDist P χ μ r = shift P μ (LWE.sample P χ r) := by
  apply Prod.ext
  · rw [encryptDist_fst, shift_fst, LWE.sample_fst]
  · funext i
    rw [encryptDist_snd, shift_snd, LWE.sample_snd, Pi.add_apply]

/-- Translating a uniform value vector by a fixed message's codepoints preserves
every distinguisher's acceptance probability [Wu24, Lecture 21, ideal hybrid].

**Proof sketch.** Translation is a bijection on the value-vector additive group and
leaves the independent matrix unchanged. Reuse the public uniform-translation and
coin-equivalence lemmas; no distributional property of the actual errors is needed. -/
theorem acceptProb_uniform_shift (P : Parameters) (μ : Fin P.samples → Bool)
    (D : (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) → ρ → Bool) :
    acceptProb (shift P μ) D =
      acceptProb (id : (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
        (Fin P.samples → ZMod P.modulus)) → _) D := by
  let e : (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) ≃
      (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) :=
    { toFun := shift P μ
      invFun := fun c => (c.1, c.2 - fun i => LWE.BitEncoding.codepoint P (μ i))
      left_inv := by
        intro c
        apply Prod.ext
        · exact shift_fst P μ c
        · change (shift P μ c).2 - (fun i => LWE.BitEncoding.codepoint P (μ i)) = c.2
          funext i
          rw [Pi.sub_apply, shift_snd, Pi.add_apply, add_sub_cancel_right]
      right_inv := by
        intro c
        apply Prod.ext
        · exact shift_fst P μ _
        · funext i
          rw [shift_snd, Pi.add_apply]
          change (c.2 i - LWE.BitEncoding.codepoint P (μ i)) +
            LWE.BitEncoding.codepoint P (μ i) = c.2 i
          exact sub_add_cancel _ _ }
  exact acceptProb_comp_equiv e id D

/-- Distinguishing two fixed plaintexts' encryptions is bounded by the sum of two
DLWE distinguishing advantages with those plaintext translations
[Wu24, Definition 20.5 and Lecture 21, explicit two-hybrid bound].

**Proof sketch.** Insert the independent uniform matrix/value experiment. Rewrite each
real encryption distribution through `encryptDist_eq_shift_sample`, and use uniform
translation to identify both ideal acceptance probabilities. The real absolute-value
triangle inequality gives the sum. Both reductions use the same fixed sample count;
efficiency and all-polynomial sample quantification remain separate obligations. -/
theorem distAdv_encrypt_le (P : Parameters) (χ : Noise)
    (μ₀ μ₁ : Fin P.samples → Bool)
    (D : (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) → ρ → Bool) :
    distAdv (encryptDist P χ μ₀) (encryptDist P χ μ₁) D ≤
      LWE.decisionAdvantage P χ (fun c r => D (shift P μ₀ c) r) +
      LWE.decisionAdvantage P χ (fun c r => D (shift P μ₁ c) r) := by
  have hreal (μ : Fin P.samples → Bool) :
      acceptProb (encryptDist P χ μ) D =
        acceptProb (LWE.sample P χ) (fun c r => D (shift P μ c) r) := by
    simp only [acceptProb_def, encryptDist_eq_shift_sample]
  have hideal (μ : Fin P.samples → Bool) :
      acceptProb id (fun c r => D (shift P μ c) r) = acceptProb id D := by
    simpa only [acceptProb_def, id_eq] using acceptProb_uniform_shift P μ D
  simp only [LWE.decisionAdvantage_eq, distAdv_def]
  rw [hideal μ₀, hideal μ₁, ← hreal μ₀, ← hreal μ₁]
  calc
    _ ≤ |acceptProb (encryptDist P χ μ₀) D - acceptProb id D| +
        |acceptProb id D - acceptProb (encryptDist P χ μ₁) D| := abs_sub_le _ _ _
    _ = _ := by rw [abs_sub_comm (acceptProb id D)]

end TCSlib.Cryptography.Encryption.Symmetric.Regev
