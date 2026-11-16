/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Scheme
import TCSlib.Cryptography.Hashing.SIS.Columns
import TCSlib.Cryptography.LWE.Experiments
import Mathlib.Tactic.Simps.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Public-key GSW: IND-CPA security from decisional LWE (concrete hybrids)

## Main definitions

* `view`, `realView`, `uniformKeyView`: publish the key and one GSW encryption of a fixed bit.
* `reduction`: the DLWE test that encrypts under its challenge key with its own coins.
* `columnHashParameters`: the SIS-hash shape `(n+1) × m` of the augmented public key.

## Main results

* `real_uniformKey_advantage`: real-to-uniform-key advantage equals one DLWE advantage.
* `uniformKey_uniform_advantage_le`: under a uniform key the view is within
  `N · ε_LHL` of uniform, with `ε_LHL = Regev.extractionError`.
* `distAdv_encrypt_le`: two fixed bits' views differ by at most two DLWE advantages plus
  `2·N·ε_LHL` [GSW13, Section 3.2].
* `distAdv_encrypt_le_of_width`: with `(n+1)·w + 2κ ≤ m` the statistical term is at most
  `N · 2^{−κ}`.

## References

* [GSW13] C. Gentry, A. Sahai, B. Waters, CRYPTO 2013; author version dated 8 June 2013,
  Section 3.2 and Lemma 1 ("the joint distribution `(A, R·A)` is computationally
  indistinguishable from uniform"; "it suffices to take `m > 2n log q`").
* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Section 6.1.3 ("semantic security follows by a lossiness argument") and
  Section 5.2.1 (Regev's hybrids).
* [BV14] Z. Brakerski, V. Vaikuntanathan, ePrint 2013/541, Section 3.1, "Security".

**Scope.** Concrete, fixed-bit, single-ciphertext statements with function-level
distinguishers, exactly as the audited Regev PKE hybrids. The LWE instance has the GSW
key's `m` rows and one common uniform secret. The asymptotic primitive bridge (`NUPPT`
reductions, `BitPublicKeyScheme.SingleBitSecure`) is a separate unit after the Regev PKE
bridge; multi-ciphertext security then follows from the existing shared-key hybrid
`distAdv_multi_le_sum` (Encryption/PublicKey/EnsembleSecurity.lean:134).
-/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

open Encryption.PublicKey

/-- The view `(pk, Enc_pk(μ; R))` [GSW13, Section 3.2, passive-view formulation]. -/
@[simps! (config := { isSimp := false }) fst snd]
def view (P : Parameters) (μ : Bool)
    (pk : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus))
    (R : Matrix (Fin P.lwe.samples) (Fin P.columns) Bool) :
    (Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus)) × Ciphertext P :=
  (pk, encrypt P pk μ R)

/-- The view is the key paired with its GSW encryption. -/
theorem view_eq (P : Parameters) (μ : Bool)
    (pk : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus))
    (R : Matrix (Fin P.lwe.samples) (Fin P.columns) Bool) :
    view P μ pk R = (pk, encrypt P pk μ R) := rfl

/-- The real view: an actual LWE public key and independent uniform binary `R` [GSW13,
Section 3.1]. -/
@[simps! (config := { isSimp := false }) fst snd]
def realView (P : Parameters) (χ : LWE.Noise) (μ : Bool)
    (r : (Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      ((Fin P.lwe.dimension → ZMod P.lwe.modulus) × (Fin P.lwe.samples → χ.Coins))) ×
        Matrix (Fin P.lwe.samples) (Fin P.columns) Bool) :
    (Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus)) × Ciphertext P :=
  view P μ (LWE.sample P.lwe χ r.1) r.2

/-- The real sampler applies `view` to the existing common-secret LWE sample. -/
theorem realView_eq (P : Parameters) (χ : LWE.Noise) (μ : Bool)
    (r : (Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      ((Fin P.lwe.dimension → ZMod P.lwe.modulus) × (Fin P.lwe.samples → χ.Coins))) ×
        Matrix (Fin P.lwe.samples) (Fin P.columns) Bool) :
    realView P χ μ r = view P μ (LWE.sample P.lwe χ r.1) r.2 := rfl

/-- The first hybrid encrypts under an independent uniform key [GSW13, Section 3.2;
Pei16, Section 6.1.3, "a uniformly random (malformed) public key"]. -/
@[simps! (config := { isSimp := false }) fst snd]
def uniformKeyView (P : Parameters) (μ : Bool)
    (r : (Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus)) ×
        Matrix (Fin P.lwe.samples) (Fin P.columns) Bool) :
    (Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus)) × Ciphertext P :=
  view P μ r.1 r.2

/-- The uniform-key hybrid applies `view` to its uniform key seed. -/
theorem uniformKeyView_eq (P : Parameters) (μ : Bool)
    (r : (Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus)) ×
        Matrix (Fin P.lwe.samples) (Fin P.columns) Bool) :
    uniformKeyView P μ r = view P μ r.1 r.2 := rfl

/-- The DLWE reduction: encrypt the fixed bit under the challenge key with independent
binary coins, then run the view distinguisher with its own coins [GSW13, Section 3.2,
Lemma 1, computational half]. -/
def reduction {ρ : Type*} (P : Parameters) (μ : Bool)
    (D : ((Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus)) × Ciphertext P) → ρ → Bool)
    (pk : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus))
    (r : Matrix (Fin P.lwe.samples) (Fin P.columns) Bool × ρ) : Bool :=
  D (view P μ pk r.1) r.2

/-- The reduction calls the distinguisher on exactly one simulated view. -/
theorem reduction_eq {ρ : Type*} (P : Parameters) (μ : Bool)
    (D : ((Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus)) × Ciphertext P) → ρ → Bool)
    (pk : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus))
    (r : Matrix (Fin P.lwe.samples) (Fin P.columns) Bool × ρ) :
    reduction P μ D pk r = D (view P μ pk r.1) r.2 := rfl

/-- The SIS-hash shape of the augmented public key: `n+1` rows, `m` binary columns, modulus
`q`. The norm budget is unused by the unconditional extraction argument. Technical glue.

**Disclosure.** Field-for-field equal to `Regev.hashParameters`; a GSW-local copy because
GSW's types index matrices by `Fin (n+1)`, and reading `Regev.hashParameters` at the type level
would unfold another file's definition (Rule 10). Alternative: Regev publishes a domain
equivalence. Either needs a maintainer decision. -/
def columnHashParameters (P : Parameters) : TCSlib.Cryptography.SIS.Parameters where
  dimension := P.lwe.dimension + 1
  columns := P.lwe.samples
  modulus := P.lwe.modulus
  sqNormBound := P.lwe.samples
  modulus_ge_two := P.lwe.modulus_ge_two

attribute [simps (config := { isSimp := false }) dimension columns modulus sqNormBound]
  columnHashParameters

/-- **Computational hybrid.** The real view and the uniform-key view are distinguished with
exactly the DLWE advantage of the encryption reduction [GSW13, Section 3.2, Lemma 1; Pei16,
Section 6.1.3].

**Proof sketch.** As `Regev.real_uniformKey_advantage`: reassociate the independent key,
coin-matrix and distinguisher seeds (`uprob_comp_equiv` with `Equiv.prodAssoc`) on both
sides, then read `LWE.decisionAdvantage_eq` and `distAdv_def`. -/
theorem real_uniformKey_advantage {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters) (χ : LWE.Noise) (μ : Bool)
    (D : ((Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus)) × Ciphertext P) → ρ → Bool) :
    distAdv (realView P χ μ) (uniformKeyView P μ) D =
      LWE.decisionAdvantage P.lwe χ (reduction P μ D) := by
  sorry

/-- **Statistical hybrid.** Under a uniform key the view is within `N · ε_LHL` of a fully
uniform key-and-ciphertext pair, where `ε_LHL = ½·√(q^{n+1}/2^m)` is the existing
`Regev.extractionError` [GSW13, Section 3.2, "`R · A` is statistically uniform by the
leftover hash lemma"; Pei16, Section 6.1.3].

**Proof sketch.** Relabel the key by the bijection `Regev.augmented_bijective`. The ciphertext
is `hashColumns (columnHashParameters P) N Ā R + μG` (`encrypt_eq`, `hashColumns_eq_mul`);
translation by `μG` is a bijection of the ciphertext space, so after relabelling both samplers
(`acceptProb_comp_equiv`) the gap is that of `(Ā, ĀR)` versus `(Ā, U)`. Apply
`distAdv_hashColumns_uniform_le` and rewrite its bound with the `columnHashParameters` readers
and `Regev.extractionError_eq`. -/
theorem uniformKey_uniform_advantage_le {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters) (μ : Bool)
    (D : ((Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus)) × Ciphertext P) → ρ → Bool) :
    distAdv (uniformKeyView P μ)
      (id : ((Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
        (Fin P.lwe.samples → ZMod P.lwe.modulus)) × Ciphertext P) → _) D ≤
      P.columns * Regev.extractionError P.lwe := by
  sorry

/-- **Concrete IND-CPA bound for public-key GSW** [GSW13, Section 3.2 and Lemma 1; Pei16,
Section 6.1.3]. The views of two fixed bits differ by at most two DLWE advantages plus
`2·N·ε_LHL`.

**Proof sketch.** Insert both uniform-key views and the common uniform view; the triangle
inequality gives the two exact DLWE terms (`real_uniformKey_advantage`) and two statistical
terms (`uniformKey_uniform_advantage_le`), as in `Regev.distAdv_encrypt_le`. -/
theorem distAdv_encrypt_le {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters) (χ : LWE.Noise) (μ₀ μ₁ : Bool)
    (D : ((Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus)) × Ciphertext P) → ρ → Bool) :
    distAdv (realView P χ μ₀) (realView P χ μ₁) D ≤
      LWE.decisionAdvantage P.lwe χ (reduction P μ₀ D) +
      LWE.decisionAdvantage P.lwe χ (reduction P μ₁ D) +
      2 * (P.columns * Regev.extractionError P.lwe) := by
  sorry

/-- With residue width `w` (`q ≤ 2^w`) and `m ≥ (n+1)·w + 2κ` rows, the statistical term is at
most `N · 2^{−κ}` [GSW13, Section 3.2, "it suffices to take `m > 2n log q`", explicit
repository budget].

**Proof sketch.** `distAdv_encrypt_le` and `Regev.two_extractionError_le`, multiplying the
latter by `N ≥ 0`. -/
theorem distAdv_encrypt_le_of_width {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters) (χ : LWE.Noise) (μ₀ μ₁ : Bool) (w κ : ℕ)
    (hq : P.lwe.modulus ≤ 2 ^ w)
    (hm : (P.lwe.dimension + 1) * w + 2 * κ ≤ P.lwe.samples)
    (D : ((Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus)) × Ciphertext P) → ρ → Bool) :
    distAdv (realView P χ μ₀) (realView P χ μ₁) D ≤
      LWE.decisionAdvantage P.lwe χ (reduction P μ₀ D) +
      LWE.decisionAdvantage P.lwe χ (reduction P μ₁ D) +
      P.columns * ((2 : ℝ)⁻¹) ^ κ := by
  sorry

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
