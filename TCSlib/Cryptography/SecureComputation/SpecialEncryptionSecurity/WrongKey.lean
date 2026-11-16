/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.SpecialEncryptionSecurity.Pad
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.HybridLemmas

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The one-query test for a wrong encryption key

## Main definitions

* `SecureComputation.SpecialWrongKey.prefixTest`: compare an oracle answer's prefix with
  the evaluator's prefix under an independent key.

## Main results

* `SecureComputation.SpecialWrongKey.polyTimeComputable_prefixTest`: efficiency of the test.
* `SecureComputation.SpecialWrongKey.exists_negligible_prefix_collision`: two independent keys
  give equal `n`-bit pad prefixes on a common nonce with negligible probability.
* `SecureComputation.SpecialWrongKey.spDecStr_none_iff_prefix_ne`: an honest ciphertext
  decrypts to `⊥` under a second key exactly when the two pad prefixes differ.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.2, Claim 157.a (ii).
-/

namespace TCSlib.Cryptography.SecureComputation.SpecialWrongKey

open Complexity Turing TCSlib.Cryptography

/-- On layout `⟨⟨⟨1^n,⟨r,u⟩⟩,α⟩,k'⟩`, return
`[decide (u.take n = (E ⟨k',r⟩).take n)]`. [PS10, §6.2.2, Claim 157.a (ii)] -/
def prefixTest (E : List Bool → List Bool) (z : List Bool) : List Bool :=
  [decide ((pairSndD (NUPPT.inArg z)).take (NUPPT.inParam z).length =
    (E (pairEncode (NUPPT.inCoins z) (pairFstD (NUPPT.inArg z)))).take
      (NUPPT.inParam z).length)]

/-- The test is the singleton comparison word:
`prefixTest E z = [decide ((snd (inArg z)).take |inParam z| =
  (E ⟨inCoins z,fst (inArg z)⟩).take |inParam z|)]`. -/
theorem prefixTest_eq (E : List Bool → List Bool) (z : List Bool) :
    prefixTest E z =
      [decide ((pairSndD (NUPPT.inArg z)).take (NUPPT.inParam z).length =
        (E (pairEncode (NUPPT.inCoins z) (pairFstD (NUPPT.inArg z)))).take
          (NUPPT.inParam z).length)] := rfl

/-- A polynomial-time evaluator gives a polynomial-time prefix test:
`PolyTimeComputable E → PolyTimeComputable (prefixTest E)`.

**Proof sketch.** Read the unary parameter, argument components, and independent key.
Evaluate the family, take both prefixes, and compare them with the polynomial-time
string equality test. All operations are compositions of published polynomial-time maps. -/
theorem polyTimeComputable_prefixTest {E : List Bool → List Bool}
    (hE : PolyTimeComputable E) : PolyTimeComputable (prefixTest E) := by
  have hp := NUPPT.polyTimeComputable_inParam
  have hr := polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg
  have hu := polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg
  have hv := hE.comp (NUPPT.polyTimeComputable_inCoins.pairEncode hr)
  have hleft := (polyTimeComputable_pairTakePoly .var).comp (hp.pairEncode hu)
  have hright := (polyTimeComputable_pairTakePoly .var).comp (hp.pairEncode hv)
  have h := polyTimeComputable_pairEq.comp (hleft.pairEncode hright)
  refine (congrArg PolyTimeComputable (?_ : prefixTest E = _)).mpr h
  funext z
  simp only [prefixTest_eq, Function.comp_apply, pairFstD_pairEncode,
    pairSndD_pairEncode, PolyExpr.eval_var]

/-- Reading `n` fixed coordinates of one random-function answer hits any fixed `n`-bit
word with probability `2^{-n}`:
`Pr_R[(⟦R r⟧).take n = ⟦v⟧] = (2⁻¹)^n`, for `n ≤ L`. -/
theorem uprob_random_prefix {n L : ℕ} (h : n ≤ L) (r v : Fin n → Bool) :
    uprob (fun R : (Fin n → Bool) → (Fin L → Bool) =>
      (List.ofFn (R r)).take n = List.ofFn v) = (2 : ℝ)⁻¹ ^ n := by
  rw [(HardcoreBit.pushesUniform_eval r).uprob_eq
    (fun u : Fin L → Bool => (List.ofFn u).take n = List.ofFn v)]
  have hcast := Fin.castLE_injective h
  have hprob := (HardcoreBit.pushesUniform_restrict (O := Bool) hcast).uprob_eq
    (fun u : Fin n → Bool => u = v)
  rw [OneWay.uprob_congr (fun u => by rw [take_ofFn_castLE h, List.ofFn_inj])]
  rw [hprob, OneWay.uprob_eq_one_div_card]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat, one_div, inv_pow]

/-- For a pseudorandom family with `n + ℓ(n)` output bits and a polynomial-time evaluator,
independent keys have equal `n`-bit output prefixes at one uniform point with negligible
probability: `∃ ε, Negligible ε ∧ ∀ n, Pr_{k,k',r}[F_k(r)_{<n} = F_{k'}(r)_{<n}] ≤ ε(n)`.
[PS10, §6.2.2, Claim 157.a (ii)]

**Proof sketch.** Use the published one-query machine with the efficient prefix test and
one query. Relabel its coins as the query point and an independent key. Its real acceptance
probability is the prefix collision probability; its random acceptance probability is
`2^{-n}` by uniform evaluation, restriction, and point probability. The difference is at
most its PRF advantage. The budget-one advantage and `2^{-n}` are negligible. -/
theorem exists_negligible_prefix_collision (ℓ : PolyExpr)
    (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) →
      (Fin ((PolyExpr.add .var ℓ).eval n) → Bool))
    (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (k r : Fin n → Bool), E (pairEncode (List.ofFn k) (List.ofFn r)) =
      List.ofFn (F n k r))
    (hF : (OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := .add .var ℓ) F).Indist
      (OracleEnsemble.random .var (.add .var ℓ))) :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n,
      uprob (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
        (List.ofFn (F n t.1 t.2.2)).take n =
          (List.ofFn (F n t.2.1 t.2.2)).take n) ≤ ε n := by
  let htest := polyTimeComputable_prefixTest hE
  let D := NUPPT.ofPolyTimeUniform htest .var
  obtain ⟨B, hB⟩ := MultiMsg.exists_oneQuery_nuppt D (.add .var ℓ)
  refine ⟨fun n => prfAdv (F n) (B.toOracleAdversary n n ((PolyExpr.add .var ℓ).eval n) 1) +
      (2 : ℝ)⁻¹ ^ n, ?_, fun n => ?_⟩
  · simpa only [PolyExpr.eval_const] using
      (hF.negligible_prfAdv B (.const 1)).add negligible_two_pow_neg
  · obtain ⟨φ, hφ⟩ := hB n
    let eD := NUPPT.coinsEquiv_ofPolyTimeUniform htest .var n
    let χ : ((Fin n → Bool) × (Fin n → Bool)) ≃ B.Coins n :=
      ((Equiv.refl (Fin n → Bool)).prodCongr eD.symm).trans φ
    have hχ : ∀ (g : (Fin n → Bool) →
        (Fin ((PolyExpr.add .var ℓ).eval n) → Bool)) (r k : Fin n → Bool),
        (B.toOracleAdversary n n ((PolyExpr.add .var ℓ).eval n) 1 (χ (r, k))).eval g =
          decide ((List.ofFn (g r)).take n = (List.ofFn (F n k r)).take n) := by
      intro g r k
      have hcoins : List.ofFn (eD.symm k) = List.ofFn k := by
        simpa only [eD, Equiv.apply_symm_apply] using
          (NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn htest .var n (eD.symm k)).symm
      rw [show χ (r, k) = φ (r, eD.symm k) from rfl, hφ]
      have hrun : D.runAt n (pairEncode (List.ofFn r) (List.ofFn (g r))) (eD.symm k) =
          [decide ((List.ofFn (g r)).take n = (List.ofFn (F n k r)).take n)] := by
        rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
        simp only [prefixTest_eq, NUPPT.inParam_eq, NUPPT.inArg_eq, NUPPT.inCoins_eq,
          NUPPT.advInput_eq, pairFstD_pairEncode, pairSndD_pairEncode,
          List.length_replicate, hcoins, hFE]
      rw [hrun]
      simp only [List.cons.injEq, and_true, decide_eq_true_eq]
    have hreal :
        uprob (fun z : (Fin n → Bool) × B.Coins n =>
          (B.toOracleAdversary n n ((PolyExpr.add .var ℓ).eval n) 1 z.2).eval (F n z.1) = true) =
        uprob (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
          (List.ofFn (F n t.1 t.2.2)).take n =
            (List.ofFn (F n t.2.1 t.2.2)).take n) := by
      let e : ((Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool)) ≃
          ((Fin n → Bool) × B.Coins n) :=
        (Equiv.refl (Fin n → Bool)).prodCongr
          ((Equiv.prodComm (Fin n → Bool) (Fin n → Bool)).trans χ)
      rw [← uprob_comp_equiv e]
      apply OneWay.uprob_congr
      intro t
      change (B.toOracleAdversary n n ((PolyExpr.add .var ℓ).eval n) 1
        (χ (t.2.2, t.2.1))).eval (F n t.1) = true ↔ _
      rw [hχ, decide_eq_true_eq]
    have hrandom :
        uprob (fun z : ((Fin n → Bool) →
            (Fin ((PolyExpr.add .var ℓ).eval n) → Bool)) × B.Coins n =>
          (B.toOracleAdversary n n ((PolyExpr.add .var ℓ).eval n) 1 z.2).eval z.1 = true) =
            (2 : ℝ)⁻¹ ^ n := by
      let e := (Equiv.refl ((Fin n → Bool) →
        (Fin ((PolyExpr.add .var ℓ).eval n) → Bool))).prodCongr χ
      rw [← uprob_comp_equiv e]
      have he : ∀ z : ((Fin n → Bool) →
          (Fin ((PolyExpr.add .var ℓ).eval n) → Bool)) ×
            ((Fin n → Bool) × (Fin n → Bool)),
          (B.toOracleAdversary n n ((PolyExpr.add .var ℓ).eval n) 1 (e z).2).eval (e z).1 = true ↔
            (List.ofFn (z.1 z.2.1)).take n =
              (List.ofFn (F n z.2.2 z.2.1)).take n := by
        intro z
        change (B.toOracleAdversary n n ((PolyExpr.add .var ℓ).eval n) 1
          (χ (z.2.1, z.2.2))).eval z.1 = true ↔ _
        rw [hχ, decide_eq_true_eq]
      rw [OneWay.uprob_congr he,
        ← uprob_comp_equiv (Equiv.prodComm
          ((Fin n → Bool) × (Fin n → Bool))
          ((Fin n → Bool) → (Fin ((PolyExpr.add .var ℓ).eval n) → Bool))), uprob_prod]
      have hn : n ≤ (PolyExpr.add .var ℓ).eval n := by
        simp only [PolyExpr.eval_add, PolyExpr.eval_var]
        omega
      have hp : ∀ t : (Fin n → Bool) × (Fin n → Bool),
          uprob (fun R : (Fin n → Bool) →
              (Fin ((PolyExpr.add .var ℓ).eval n) → Bool) =>
            (List.ofFn (R t.1)).take n =
              (List.ofFn (F n t.2 t.1)).take n) = (2 : ℝ)⁻¹ ^ n := by
        intro t
        rw [take_ofFn_castLE hn]
        exact uprob_random_prefix hn t.1 _
      exact (congrArg uexp (funext hp)).trans (OneWay.uexp_const _)
    have ha := le_abs_self
      (uprob (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
        (List.ofFn (F n t.1 t.2.2)).take n =
          (List.ofFn (F n t.2.1 t.2.2)).take n) - (2 : ℝ)⁻¹ ^ n)
    dsimp only
    rw [prfAdv_eq, hreal, hrandom]
    linarith

/-- Honest string ciphertexts fail under a second key exactly when the pad prefixes
differ:
`spDecStr E n l ⟦k'⟧ (spEncStr E ⟦k⟧ ⟦m⟧ ⟦r⟧) = none ↔
  (⟦F k r⟧).take n ≠ (⟦F k' r⟧).take n`, when `E` evaluates `F` with `n+l` output bits.
[PS10, §6.2.2, Claim 157.a (ii)]

**Proof sketch.** The honest nonce and key lengths pass the length guard. The pad prefix
has `n` bits and the masked suffix has `l` bits, so the ciphertext length also passes.
Its first `n` bits are the first pad's prefix; decryption tests exactly its equality
with the second pad's prefix. -/
theorem spDecStr_none_iff_prefix_ne {n l : ℕ}
    (F : (Fin n → Bool) → (Fin n → Bool) → (Fin (n + l) → Bool))
    (E : List Bool → List Bool)
    (hFE : ∀ k r, E (pairEncode (List.ofFn k) (List.ofFn r)) = List.ofFn (F k r))
    (k k' r : Fin n → Bool) (m : Fin l → Bool) :
    spDecStr E n l (List.ofFn k')
      (spEncStr E (List.ofFn k) (List.ofFn m) (List.ofFn r)) = none ↔
        (List.ofFn (F k r)).take n ≠ (List.ofFn (F k' r)).take n := by
  have ht : ((List.ofFn (F k r)).take n).length = n := by
    rw [List.length_take, List.length_ofFn, Nat.min_eq_left (by omega)]
  have hz : (List.zipWith xor (List.ofFn m) ((List.ofFn (F k r)).drop n)).length = l := by
    rw [List.length_zipWith, List.length_ofFn, List.length_drop, List.length_ofFn]
    omega
  simp only [spDecStr_eq, spEncStr_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_ofFn, hFE]
  rw [if_pos ⟨trivial, trivial, by rw [List.length_append, ht, hz]⟩, List.take_left' ht]
  by_cases h : (List.ofFn (F k r)).take n = (List.ofFn (F k' r)).take n <;> simp [h]

end TCSlib.Cryptography.SecureComputation.SpecialWrongKey
