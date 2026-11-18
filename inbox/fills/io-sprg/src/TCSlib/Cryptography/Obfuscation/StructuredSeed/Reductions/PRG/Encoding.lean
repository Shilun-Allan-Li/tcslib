/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Reductions.PRG.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Injective and bounded Boolean PRG reduction encodings

## Main definitions

None; this module proves properties of the imported reduction interface.

## Main results

The three original canonical/advice injectivity and advice-length theorems.

## References

* [JLS26] A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Well-Founded Assumptions*, J. ACM 73(1), Article 1, February 2026,
  Lemma 4.2, p. 19; Definition 3.4, p. 11.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
  3rd ed., January 2010, Definition 26.8.

**Deviations.** Dv9, Dv12 and Dv15 count the unchanged prime-first advice layout and
all explicit hardwired fields, with no new encoder or sampler.
-/

namespace TCSlib.Cryptography.Obfuscation.StructuredSeed

open Complexity Turing Games

namespace Params

/-- The canonical Boolean challenge encoding is injective.
[JLS26, Definition 3.4, p. 11; Lemma 4.2, p. 19]. Dv15 retains the complete typed challenge.

**Proof sketch.** Read the canonical challenge pair through prgEnc_eq and challengeStr_eq,
then apply the primitive's index-code injectivity and List.ofFn injectivity. -/
theorem prgEnc_injective (P : Params) (N : ℕ) : Function.Injective (P.prgEnc N) := by
  intro x y h
  simp only [P.prgEnc_eq, P.G.challengeStr_eq] at h
  have hp := pairEncode_injective (a₁ := (_, _)) (a₂ := (_, _)) h
  exact Prod.ext (P.G.encIdx_injective N (congrArg Prod.fst hp))
    (List.ofFn_injective (congrArg Prod.snd hp))

/-- The explicit PRG-hop advice code retains every fixed bucket, matrix and public vector.
[JLS26, Lemma 4.2, p. 19]. Dv9, Dv12 and Dv15 retain the prime prefix and all hardwired data.

**Proof sketch.** Split the nested pairs, apply the bucket-code and canonical matrix-code
injectivity readers at the public prime's residue width, then use record extensionality. -/
theorem encPRGAdvice_injective (P : Params) (π : PrimeSchedule) (N : ℕ) :
    Function.Injective (P.encPRGAdvice π N) := by
  intro a b h
  rw [P.encPRGAdvice_eq, P.encPRGAdvice_eq] at h
  have h0 := congrArg Prod.snd
    (pairEncode_injective (a₁ := (_, _)) (a₂ := (_, _)) h)
  have h1 := congrArg Prod.snd
    (pairEncode_injective (a₁ := (_, _)) (a₂ := (_, _)) h0)
  have h2 := pairEncode_injective (a₁ := (_, _)) (a₂ := (_, _)) h1
  have h3 := pairEncode_injective (a₁ := (_, _)) (a₂ := (_, _))
    (congrArg Prod.snd h2)
  have hb : a.buckets = b.buckets :=
    P.encBuckets_injective (P.kappaOfN N) (congrArg Prod.fst h2)
  have hM : a.matrix = b.matrix :=
    Encoding.Modular.encodeMatrix_injective (P.kappaOfN N + 1)
      (π (P.kappaOfN N)).le_two_pow (congrArg Prod.fst h3)
  have hu : a.uniform = b.uniform :=
    Encoding.Modular.encodeMatrix_injective (P.kappaOfN N + 1)
      (π (P.kappaOfN N)).le_two_pow (congrArg Prod.snd h3)
  apply (PRGAdvice.prodEquiv P π N).injective
  simp only [PRGAdvice.prodEquiv_eq]
  exact Prod.ext hb (Prod.ext hM hu)

/-- Every advice encoding fits the explicit syntactic polynomial at N.
[JLS26, Lemma 4.2, p. 19]. Dv12 bounds the full hardwired data instead of using fresh
sampling; Dv15 accounts for its concrete finite-coordinate string.

**Proof sketch.** Read the nested pair lengths and canonical matrix lengths. Bound buckets
and the LPN matrix by idxBound, and the repeated uniform vectors by the public seed bound
with residue width kappa+1. Apply kappaOfN_le and polynomial evaluation monotonicity, then
absorb all constant and linear factors into the stated cubic majorant. -/
theorem encPRGAdvice_length_le (P : Params) (π : PrimeSchedule) (N : ℕ)
    (ω : P.PRGAdvice π N) :
    (P.encPRGAdvice π N ω).length ≤ P.prgAdviceBound.eval N := by
  classical
  let κ := P.kappaOfN N
  let pp := π κ
  let S := P.idxBound.eval N + (P.seedBound.eval N +
    (P.mBound.eval N + (P.nBound.eval N + (P.ellBound.eval N + (N + 1)))))
  have hκ : κ ≤ N := P.kappaOfN_le N
  have hN1 : N + 1 ≤ S := ?_
  swap
  · dsimp only [S]
    omega
  have hκ1 : κ + 1 ≤ S := (Nat.succ_le_succ hκ).trans hN1
  have hS1 : 1 ≤ S := (Nat.succ_le_succ (Nat.zero_le N)).trans hN1
  have hidx : P.idxBound.eval κ ≤ S := ?_
  swap
  · have h := PolyExpr.eval_mono P.idxBound hκ
    dsimp only [S]
    omega
  have hseed : P.seedBound.eval κ ≤ S := ?_
  swap
  · have h := PolyExpr.eval_mono P.seedBound hκ
    dsimp only [S]
    omega
  obtain ⟨I⟩ := P.G.idxNonempty (P.n κ)
  have hindex := P.encIdx'_length_le κ pp (I, ω.buckets, ω.matrix)
  rw [P.encIdx'_eq, length_pairEncode, length_pairEncode] at hindex
  dsimp only at hindex
  have hb : (P.encBuckets κ ω.buckets).length ≤ S := ?_
  swap
  · omega
  have hM : (Encoding.Modular.encodeMatrix (κ + 1) ω.matrix).length ≤ S := ?_
  swap
  · omega
  have hpub := P.pubLen_le_seedBound κ
  rw [P.pubLen_eq] at hpub
  have hbase : κ * P.n κ ≤ P.seedBound.eval κ :=
    (Nat.le_add_right _ 1).trans hpub
  have hu : (Encoding.Modular.encodeMatrix (κ + 1) ω.uniform).length ≤ S ^ 2 := ?_
  swap
  · rw [Encoding.Modular.encodeMatrix_length]
    calc
      κ * P.n κ * (κ + 1) ≤ P.seedBound.eval κ * (κ + 1) :=
        Nat.mul_le_mul_right (κ + 1) hbase
      _ ≤ S * S := Nat.mul_le_mul hseed hκ1
      _ = S ^ 2 := (pow_two S).symm
  have hS2 : S ≤ S ^ 2 := ?_
  swap
  · simpa only [pow_two, Nat.mul_one] using Nat.mul_le_mul_left S hS1
  have hS23 : S ^ 2 ≤ S ^ 3 :=
    calc
      S ^ 2 = S ^ 2 * 1 := (Nat.mul_one _).symm
      _ ≤ S ^ 2 * S := Nat.mul_le_mul_left (S ^ 2) hS1
      _ = S ^ 3 := (pow_succ S 2).symm
  have hS3 : S ≤ S ^ 3 := hS2.trans hS23
  have hone : 1 ≤ S ^ 3 := hS1.trans hS3
  have hcoarse : (P.encPRGAdvice π N ω).length ≤ 100 * S ^ 3 := ?_
  swap
  · rw [P.encPRGAdvice_eq]
    simp only [length_pairEncode, PrimeParam.enc_eq, Candidates.length_natToList,
      List.length_replicate]
    change 2 * (κ + 2) + 2 + (2 * N + 2 +
      (2 * (P.encBuckets κ ω.buckets).length + 2 +
        (2 * (Encoding.Modular.encodeMatrix (κ + 1) ω.matrix).length + 2 +
          (Encoding.Modular.encodeMatrix (κ + 1) ω.uniform).length))) ≤ 100 * S ^ 3
    omega
  apply hcoarse.trans
  rw [P.prgAdviceBound_eq, P.prgAdviceDataBound_eq]
  simp only [PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_add,
    PolyExpr.eval_var, PolyExpr.eval_pow]
  change 100 * S ^ 3 ≤ 100 * ((N + 1) * S ^ 3)
  apply Nat.mul_le_mul_left
  simpa only [Nat.one_mul] using
    Nat.mul_le_mul_right (S ^ 3) (Nat.succ_le_succ (Nat.zero_le N))

end Params

end TCSlib.Cryptography.Obfuscation.StructuredSeed
