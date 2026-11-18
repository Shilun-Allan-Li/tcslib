/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Reductions.LPN.Defs
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Injective and polynomially bounded LPN reduction encodings

## Main definitions

None; this module proves properties of the imported reduction interface.

## Main results

* Canonical challenge-code injectivity.
* Advice-code injectivity and its explicit polynomial bound.

## References

* [JLS26] A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from Well-Founded
  Assumptions*, J. ACM 73(1), Article 1, February 2026, Lemma 4.2, p. 19.
* [PS10] R. Pass, A. Shelat, *A Course in Cryptography*, 2010, Definition 26.8.

**Deviations.** Dv9, Dv12 and Dv15 retain the prime-first fixed-layout advice code;
no encoder, algorithm, sampler or polynomial-bound definition changes.
-/

namespace TCSlib.Cryptography.Obfuscation.StructuredSeed

open Complexity Turing
open scoped BigOperators

namespace Params

/-- Canonical LPN challenge encoding is injective [JLS26, Lemma 4.2, p. 19].
Dv3 reuses the assumption's width and canonical encoder unchanged.

**Proof sketch.** Apply the existing `LWE.encodeChallenge_injective` with the LWE
family's public modulus-width field. -/
theorem lpnEnc_injective (P : Params) (π : PrimeSchedule) (L : ℕ) :
    Function.Injective (P.lpnEnc π L) := by
  intro x y h
  apply LWE.encodeChallenge_injective
    ((P.lpnFamily_raw π).toLWE.parameters L)
    ((P.lpnFamily_raw π).toLWE.residueBits.eval L)
    ((P.lpnFamily_raw π).toLWE.modulus_le_pow L)
  simpa only [P.lpnEnc_eq] using h

/-- All six hardwired advice fields are retained by the explicit code
[JLS26, Lemma 4.2, p. 19]. Dv9 and Dv15 place the prime first and use fixed coordinate codes.

**Proof sketch.** Split the nested pairs, recover hop/index/bucket/draw/tail coordinates,
and use modular vector injectivity on each uniform-vector list entry. -/
theorem encLPNAdvice_injective (P : Params) (π : PrimeSchedule) (L : ℕ) :
    Function.Injective (P.encLPNAdvice π L) := by
  intro a b h
  rw [P.encLPNAdvice_eq, P.encLPNAdvice_eq] at h
  have h0 := congrArg Prod.snd
    (pairEncode_injective (a₁ := (_, _)) (a₂ := (_, _)) h)
  have h1 := congrArg Prod.snd
    (pairEncode_injective (a₁ := (_, _)) (a₂ := (_, _)) h0)
  have h2 := pairEncode_injective (a₁ := (_, _)) (a₂ := (_, _)) h1
  have h3 := pairEncode_injective (a₁ := (_, _)) (a₂ := (_, _))
    (congrArg Prod.snd h2)
  have h4 := pairEncode_injective (a₁ := (_, _)) (a₂ := (_, _))
    (congrArg Prod.snd h3)
  have h5 := pairEncode_injective (a₁ := (_, _)) (a₂ := (_, _))
    (congrArg Prod.snd h4)
  have h6 := pairEncode_injective (a₁ := (_, _)) (a₂ := (_, _))
    (congrArg Prod.snd h5)
  have hh : a.hop = b.hop := Fin.ext
    (Candidates.natToList_injOn
      (a.hop.isLt.trans Nat.lt_two_pow_self)
      (b.hop.isLt.trans Nat.lt_two_pow_self) (congrArg Prod.fst h2))
  have hI : a.I = b.I := P.G.encIdx_injective (P.n (P.kappaOf L))
    (congrArg Prod.fst h3)
  have hb : a.buckets = b.buckets := P.encBuckets_injective (P.kappaOf L)
    (congrArg Prod.fst h4)
  have hd : a.draw = b.draw := P.encDraw_injective (P.kappaOf L)
    (π (P.kappaOf L)) (congrArg Prod.fst h5)
  have ht : a.tail = b.tail := List.ofFn_injective (congrArg Prod.fst h6)
  have hu : a.uniform = b.uniform := List.ofFn_injective
    (Internal.encodeList_injective_of_fixedWidth
      (Encoding.Modular.encodeVector_injective
        (q := (π (P.kappaOf L)).p) (length := P.n (P.kappaOf L))
        (P.kappaOf L + 1) (π (P.kappaOf L)).le_two_pow)
      (P.n (P.kappaOf L) * (P.kappaOf L + 1))
      (fun row : Fin (P.n (P.kappaOf L)) → ZMod (π (P.kappaOf L)).p =>
        Encoding.Modular.encodeVector_length (P.kappaOf L + 1) row)
      (congrArg Prod.snd h6))
  apply (P.lpnAdviceProductEquiv π L).injective
  simp only [P.lpnAdviceProductEquiv_apply]
  exact Prod.ext hh (Prod.ext hI (Prod.ext hb (Prod.ext hd (Prod.ext ht hu))))

/-- Every advice word has length at most the explicit polynomial at its independent dimension
[JLS26, Lemma 4.2, p. 19]. Dv12 and Dv15 count hardwired data rather than sampler coins.

**Proof sketch.** Use the existing pair/list/vector length equations, the exact draw
layout, the published numeric bounds, κOf(L)≤L and PolyExpr.eval_mono; the factor4096
covers all separators in the deliberately generous cubic majorant. -/
theorem encLPNAdvice_length_le (P : Params) (π : PrimeSchedule) (L : ℕ)
    (w : P.LPNAdvice π L) : (P.encLPNAdvice π L w).length ≤ P.lpnAdviceBound.eval L := by
  classical
  let κ := P.kappaOf L
  let pp := π κ
  let S := P.idxBound.eval L + (P.seedBound.eval L +
    (P.mBound.eval L + (P.nBound.eval L + (P.ellBound.eval L + (L + 1)))))
  have hκ : κ ≤ L := P.kappaOf_le L
  have hL1 : L + 1 ≤ S := ?_
  swap
  · dsimp only [S]
    omega
  have hκ1 : κ + 1 ≤ S := (Nat.succ_le_succ hκ).trans hL1
  have hκS : κ ≤ S := (Nat.le_succ κ).trans hκ1
  have hS1 : 1 ≤ S := (Nat.succ_le_succ (Nat.zero_le L)).trans hL1
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
  have hn : P.n κ ≤ S := ?_
  swap
  · have h := (P.n_le_nBound κ).trans (PolyExpr.eval_mono P.nBound hκ)
    dsimp only [S]
    omega
  have hEll : P.ℓ κ ≤ S := ?_
  swap
  · have h := (P.ell_le_ellBound κ).trans (PolyExpr.eval_mono P.ellBound hκ)
    dsimp only [S]
    omega
  have hm : P.m κ ≤ S := ?_
  swap
  · have h := (P.m_le_mBound κ).trans (PolyExpr.eval_mono P.mBound hκ)
    dsimp only [S]
    omega
  have hindex := P.encIdx'_length_le κ pp (w.I, w.buckets, fun _ _ => 0)
  rw [P.encIdx'_eq, length_pairEncode, length_pairEncode] at hindex
  dsimp only at hindex
  have hG : (P.G.encIdx (P.n κ) w.I).length ≤ S := ?_
  swap
  · omega
  have hb : (P.encBuckets κ w.buckets).length ≤ S := ?_
  swap
  · omega
  have hS2 : S ≤ S ^ 2 := ?_
  swap
  · simpa only [pow_two, Nat.mul_one] using Nat.mul_le_mul_left S hS1
  have hone2 : 1 ≤ S ^ 2 := hS1.trans hS2
  have hS23 : S ^ 2 ≤ S ^ 3 :=
    calc
      S ^ 2 = S ^ 2 * 1 := (Nat.mul_one _).symm
      _ ≤ S ^ 2 * S := Nat.mul_le_mul_left (S ^ 2) hS1
      _ = S ^ 3 := (pow_succ S 2).symm
  have hS3 : S ≤ S ^ 3 := hS2.trans hS23
  have hone3 : 1 ≤ S ^ 3 := hS1.trans hS3
  let noiseCode : Fin (P.W κ) × ZMod pp.p → List Bool := fun c =>
    pairEncode (Candidates.natToList (P.ℓ κ + 1) c.1.val)
      (Candidates.natToList (κ + 1) c.2.val)
  let payload := 2 * (P.ℓ κ + 1) + 2 + (κ + 1)
  let oneWidth := 2 * (P.ℓ κ * (κ + 1)) + 2 + (P.n κ * (payload + 1) + 1)
  have hnoise : ∀ c, (noiseCode c).length = payload := ?_
  swap
  · intro c
    change (pairEncode _ _).length = payload
    rw [length_pairEncode, Candidates.length_natToList, Candidates.length_natToList]
  have hone : ∀ r, (P.encOneDraw κ pp r).length = oneWidth := ?_
  swap
  · intro r
    rw [P.encOneDraw_eq, length_pairEncode, Encoding.Modular.encodeVector_length]
    rw [Internal.encodeList_length_of_fixedWidth noiseCode payload hnoise,
      List.length_ofFn]
  have hdraw : (P.encDraw κ pp w.draw).length =
      2 * P.n κ + 2 + (κ * (oneWidth + 1) + 1) := ?_
  swap
  · rw [P.encDraw_eq, length_pairEncode, List.length_ofFn,
      Internal.encodeList_length_of_fixedWidth (P.encOneDraw κ pp) oneWidth hone,
      List.length_ofFn]
  have hsecret : P.ℓ κ * (κ + 1) ≤ S ^ 2 :=
    (Nat.mul_le_mul hEll hκ1).trans_eq (pow_two S).symm
  have hpayload : payload + 1 ≤ 9 * S := ?_
  swap
  · dsimp only [payload]
    omega
  have hnoisePart : P.n κ * (payload + 1) ≤ 9 * S ^ 2 := ?_
  swap
  · calc
      P.n κ * (payload + 1) ≤ S * (9 * S) := Nat.mul_le_mul hn hpayload
      _ = 9 * S ^ 2 := ?_
    ring
  have honeBound : oneWidth + 1 ≤ 15 * S ^ 2 := ?_
  swap
  · dsimp only [oneWidth]
    omega
  have htable : κ * (oneWidth + 1) ≤ 15 * S ^ 3 := ?_
  swap
  · calc
      κ * (oneWidth + 1) ≤ S * (15 * S ^ 2) := Nat.mul_le_mul hκS honeBound
      _ = 15 * S ^ 3 := ?_
    ring
  have hdrawBound : (P.encDraw κ pp w.draw).length ≤ 32 * S ^ 3 := ?_
  swap
  · rw [hdraw]
    omega
  have hpub := P.pubLen_le_seedBound κ
  rw [P.pubLen_eq] at hpub
  have hbase : κ * P.n κ ≤ P.seedBound.eval κ :=
    (Nat.le_add_right _ 1).trans hpub
  have huPayload : κ * P.n κ * (κ + 1) ≤ S ^ 2 :=
    ((Nat.mul_le_mul_right (κ + 1) hbase).trans
      (Nat.mul_le_mul hseed hκ1)).trans_eq (pow_two S).symm
  let rows := BoolCircuit.encodeList
    (Encoding.Modular.encodeVector (κ + 1)) (List.ofFn w.uniform)
  have hrows : rows.length ≤ S ^ 2 + S := ?_
  swap
  · dsimp only [rows]
    rw [Internal.encodeList_length_of_fixedWidth
      (Encoding.Modular.encodeVector (q := pp.p) (length := P.n κ) (κ + 1))
      (P.n κ * (κ + 1))
      (fun row => Encoding.Modular.encodeVector_length (κ + 1) row), List.length_ofFn]
    calc
      κ * (P.n κ * (κ + 1) + 1) + 1 =
        κ * P.n κ * (κ + 1) + (κ + 1) := ?_
      _ ≤ S ^ 2 + S := Nat.add_le_add huPayload hκ1
    ring
  have hcoarse : (P.encLPNAdvice π L w).length ≤ 128 * S ^ 3 := ?_
  swap
  · rw [P.encLPNAdvice_eq]
    simp only [length_pairEncode, PrimeParam.enc_eq, Candidates.length_natToList,
      List.length_replicate, List.length_ofFn]
    change 2 * (κ + 2) + 2 + (2 * L + 2 + (2 * (κ + 1) + 2 +
      (2 * (P.G.encIdx (P.n κ) w.I).length + 2 +
        (2 * (P.encBuckets κ w.buckets).length + 2 +
          (2 * (P.encDraw κ pp w.draw).length + 2 +
            (2 * P.m κ + 2 + rows.length)))))) ≤ 128 * S ^ 3
    omega
  apply hcoarse.trans
  rw [P.lpnAdviceBound_eq]
  simp only [PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_add,
    PolyExpr.eval_var, PolyExpr.eval_pow]
  change 128 * S ^ 3 ≤ 4096 * ((L + 1) * S ^ 3)
  have hscale : S ^ 3 ≤ (L + 1) * S ^ 3 := ?_
  swap
  · simpa only [Nat.one_mul] using
      Nat.mul_le_mul_right (S ^ 3) (Nat.succ_le_succ (Nat.zero_le L))
  omega

end Params

end TCSlib.Cryptography.Obfuscation.StructuredSeed
