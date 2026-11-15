/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.GarblingSpecial
import TCSlib.Cryptography.SecureComputation.SpecialEncryptionSecurity
import TCSlib.Cryptography.SecureComputation.GarblingSecurity.CoinMarginals

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Concrete wrong-key bounds for nested special encryption

## Main definitions

This module adds no definitions.

## Main results

* `SecureComputation.GarblingCoins.length_nestedInner`: the inner ciphertext has `4n+2` bits.
* `SecureComputation.GarblingCoins.nestedSpecial_wrongKeyBot_of_string_bounds`: inner and outer
  string success bounds `ε₁, ε₂` give `(nestedSpecial E₁ E₂ n).WrongKeyBot (ε₁ + ε₂)`.
* `SecureComputation.uprob_not_good_distinct_le_of_uniform_data`: with uniform keys and row
  coins, goodness with distinct output keys fails with probability at most
  `12 · |gates| · δ + m / |K|`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.2, Claim 157.a (ii).
-/

namespace TCSlib.Cryptography.SecureComputation.GarblingCoins

open Complexity Turing TCSlib.Cryptography

/-- A special ciphertext with an `n`-bit nonce, an `n`-bit message, and a `2n`-bit pad has
`innerLen(n) = 4n+2` bits:
`|spEncStr E ⟦k⟧ ⟦m⟧ ⟦r⟧| = innerLen.eval n`. -/
theorem length_nestedInner
    {G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool)}
    {E : List Bool → List Bool}
    (hGE : ∀ n (k r : Fin n → Bool), E (pairEncode (List.ofFn k) (List.ofFn r)) =
      List.ofFn (G n k r)) (n : ℕ) (k m r : Fin n → Bool) :
    (spEncStr E (List.ofFn k) (List.ofFn m) (List.ofFn r)).length = innerLen.eval n := by
  rw [length_spEncStr E (by rw [hGE]; simp), List.length_ofFn, List.length_ofFn,
    innerLen_eq, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const,
    PolyExpr.eval_var, PolyExpr.eval_const]
  omega

/-- Inner and outer string success bounds `ε₁, ε₂` give
`(nestedSpecial E₁ E₂ n).WrongKeyBot (ε₁+ε₂)`, provided both errors are nonnegative and
the evaluators have the specified `2n` and `n+innerLen(n)` output lengths.
[PS10, §6.2.2, Claim 157.a (ii)]

**Proof sketch.** There are at most two key positions. With one position use the inner
string bound and its uniform key/nonce marginal. With two positions, if the first key
differs, condition on the second position's keys and inner nonce, and apply the outer
bound to the resulting fixed inner ciphertext. If the first key agrees, correctness
opens the outer layer and the inner key/nonce marginal gives the inner bound. Add the
nonnegative unused error in each case. The zero-position case has no distinct choices. -/
theorem nestedSpecial_wrongKeyBot_of_string_bounds
    (G₁ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool))
    (G₂ : ∀ n, (Fin n → Bool) → (Fin n → Bool) →
      (Fin ((PolyExpr.add .var innerLen).eval n) → Bool))
    (E₁ E₂ : List Bool → List Bool)
    (hGE₁ : ∀ n (k r : Fin n → Bool), E₁ (pairEncode (List.ofFn k) (List.ofFn r)) =
      List.ofFn (G₁ n k r))
    (hGE₂ : ∀ n (k r : Fin n → Bool), E₂ (pairEncode (List.ofFn k) (List.ofFn r)) =
      List.ofFn (G₂ n k r)) (n : ℕ) {ε₁ ε₂ : ℝ} (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂)
    (h₁ : ∀ m : Fin n → Bool,
      uprob (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
        (spDecStr E₁ n n (List.ofFn t.2.1)
          (spEncStr E₁ (List.ofFn t.1) (List.ofFn m) (List.ofFn t.2.2))).isSome = true) ≤ ε₁)
    (h₂ : ∀ m : Fin (innerLen.eval n) → Bool,
      uprob (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
        (spDecStr E₂ n (innerLen.eval n) (List.ofFn t.2.1)
          (spEncStr E₂ (List.ofFn t.1) (List.ofFn m) (List.ofFn t.2.2))).isSome = true) ≤ ε₂) :
    (nestedSpecial E₁ E₂ n).WrongKeyBot (ε₁ + ε₂) := by
  rw [MultiEnc.wrongKeyBot_iff]
  intro len hlen a a' hne o
  have hcases : len = 0 ∨ len = 1 ∨ len = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  · exact (hne (Subsingleton.elim a a')).elim
  · have hab : a 0 ≠ a' 0 := fun h => hne (funext (Fin.forall_fin_one.mpr h))
    have hu := (pushesUniform_position_keys_coin (K := Fin n → Bool) (0 : Fin 1)
      hab false).uprob_eq (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
        (spDecStr E₁ n n (List.ofFn t.2.1)
          (spEncStr E₁ (List.ofFn t.1) (List.ofFn o) (List.ofFn t.2.2))).isSome = true)
    refine (uprob_mono (fun t ht => ?_)).trans
      ((hu.trans_le (h₁ o)).trans (le_add_of_nonneg_right hε₂))
    simp only [List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one,
      nestedSpecial_enc, nestedSpecial_dec] at ht
    exact Option.isSome_of_isSome_bind ht
  · by_cases hfirst : a 0 = a' 0
    · have hsecond : a 1 ≠ a' 1 := fun h =>
        hne (funext (Fin.forall_fin_two.mpr ⟨hfirst, h⟩))
      have hu := (pushesUniform_position_keys_coin (K := Fin n → Bool) (1 : Fin 2)
        hsecond true).uprob_eq (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
          (spDecStr E₁ n n (List.ofFn t.2.1)
            (spEncStr E₁ (List.ofFn t.1) (List.ofFn o) (List.ofFn t.2.2))).isSome = true)
      refine (uprob_mono (fun t ht => ?_)).trans
        ((hu.trans_le (h₁ o)).trans (le_add_of_nonneg_right hε₂))
      simp only [List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one,
      nestedSpecial_enc, nestedSpecial_dec] at ht
      have hc := length_nestedInner hGE₁ n (t.1 1 (a 1)) o t.2.2
      have hp : (E₂ (pairEncode (List.ofFn (t.1 0 (a 0))) (List.ofFn t.2.1))).length =
          n + innerLen.eval n := by
        rw [hGE₂, List.length_ofFn]
        rfl
      rw [← hfirst, spDecStr_spEncStr E₂ List.length_ofFn hc List.length_ofFn hp,
        Option.bind_some] at ht
      exact Option.isSome_of_isSome_bind ht
    · let K := Fin n → Bool
      let e : ((Fin 2 → Bool → K) × (K × K)) ≃
          ((Bool → K) × K) × ((Bool → K) × K) :=
        ((piFinTwoEquiv fun _ : Fin 2 => Bool → K).prodCongr (Equiv.refl (K × K))).trans
          ((Equiv.prodProdProdComm (Bool → K) (Bool → K) K K).trans
            (Equiv.prodComm ((Bool → K) × K) ((Bool → K) × K)))
      rw [← uprob_comp_equiv e.symm, uprob_prod]
      refine (OneWay.uexp_mono (g := fun _ => ε₂) (fun s => ?_)).trans ?_
      · let c := spEncStr E₁ (List.ofFn (s.1 (a 1))) (List.ofFn o) (List.ofFn s.2)
        have hc : c.length = innerLen.eval n := length_nestedInner hGE₁ n _ o _
        let m := padFin (innerLen.eval n) c
        have hm : List.ofFn m = c := ofFn_padFin_of_length hc
        have hlaw : HardcoreBit.PushesUniform
            (fun t : (Bool → K) × K => (t.1 (a 0), t.1 (a' 0), t.2)) :=
          ((HardcoreBit.pushesUniform_eval_pair (γ := K) hfirst).prodMap
            HardcoreBit.pushesUniform_id).comp
              (HardcoreBit.pushesUniform_equiv (Equiv.prodAssoc K K K))
        have hu := hlaw.uprob_eq (fun t : K × K × K =>
          (spDecStr E₂ n (innerLen.eval n) (List.ofFn t.2.1)
            (spEncStr E₂ (List.ofFn t.1) (List.ofFn m) (List.ofFn t.2.2))).isSome = true)
        have hb := hu.trans_le (h₂ m)
        rw [hm] at hb
        refine (uprob_mono (fun t ht => ?_)).trans hb
        simp only [List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one,
      nestedSpecial_enc, nestedSpecial_dec] at ht
        exact Option.isSome_of_isSome_bind ht
      · simpa only [OneWay.uexp_const] using
          (le_add_of_nonneg_left hε₁ : ε₂ ≤ ε₁ + ε₂)

end TCSlib.Cryptography.SecureComputation.GarblingCoins

namespace TCSlib.Cryptography.SecureComputation

open BoolCircuit

variable {K C ρ : Type} [Inhabited K] {n : ℕ} (M : MultiEnc K C ρ) (Cc : DAGCircuit n)

/-- Uniform independent keys and row coins give goodness and distinct output keys:
`Pr_w[¬ (Good M Cc (s w) ∧ ∀ j, keyAt Cc (s w) (out j) false ≠
  keyAt Cc (s w) (out j) true)] ≤ 12*|Cc.gates|*δ + m/|K|`, if `out j < Cc.size`
and `w ↦ ((s w).1,(s w).2.1)` pushes uniform to uniform.
Outputs may coincide. [PS10, §6.2.3, Claim 159.a and Protocol 162.6]

**Proof sketch.** Use the B2 uniform-data bound for goodness. At each output, the two
keys are independent uniform elements of `K`, so their collision probability is `1/|K|`.
The finite union bound over output positions does not require distinct output vertices.
Add this collision bound to the goodness failure bound. -/
theorem uprob_not_good_distinct_le_of_uniform_data [Fintype K] [Fintype ρ] [Nonempty ρ]
    (hdec : M.DecCorrect) {δ : ℝ} (hδ : M.WrongKeyBot δ) (hC : Cc.IsFaninTwo)
    {Ω : Type} [Fintype Ω] (s : Ω → GarbleSeed Cc K ρ)
    (hs : HardcoreBit.PushesUniform (fun w => ((s w).1, (s w).2.1)))
    {m : ℕ} (out : Fin m → ℕ) (hout : ∀ j, out j < Cc.size) :
    uprob (fun w => ¬ (Good M Cc (s w) ∧ ∀ j,
      keyAt Cc (s w) (out j) false ≠ keyAt Cc (s w) (out j) true)) ≤
      12 * Cc.gates.length * δ + m * (1 / Fintype.card K) := by
  classical
  let collision : Fin m → Ω → Prop := fun j w =>
    keyAt Cc (s w) (out j) false = keyAt Cc (s w) (out j) true
  have hpoint (j : Fin m) : uprob (collision j) = 1 / Fintype.card K := by
    let v : Fin Cc.size := ⟨out j, hout j⟩
    have hkeys : HardcoreBit.PushesUniform (fun w => (s w).1) :=
      hs.comp HardcoreBit.pushesUniform_fst
    have hpair : HardcoreBit.PushesUniform (fun w => ((s w).1 v false, (s w).1 v true)) :=
      (hkeys.comp (HardcoreBit.pushesUniform_eval (γ := Bool → K) v)).comp
        (HardcoreBit.pushesUniform_eval_pair (γ := K) Bool.false_ne_true)
    have hu := hpair.uprob_eq (fun z : K × K => z.1 = z.2)
    calc
      _ = uprob (fun w => (s w).1 v false = (s w).1 v true) := by
        apply OneWay.uprob_congr
        intro w
        simp only [collision, keyAt_eq, dif_pos (hout j)]
        rfl
      _ = uprob (fun z : K × K => z.1 = z.2) := hu
      _ = 1 / Fintype.card K := MultiMsg.uprob_eq_pair
  have hcoll : uprob (fun w => ∃ j ∈ Finset.univ, collision j w) ≤
      m * (1 / Fintype.card K) := by
    refine (uprob_exists_le Finset.univ collision).trans ?_
    simp only [hpoint, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact le_rfl
  have hbad : ∀ w, ¬ (Good M Cc (s w) ∧ ∀ j,
      keyAt Cc (s w) (out j) false ≠ keyAt Cc (s w) (out j) true) →
        ¬ Good M Cc (s w) ∨ ∃ j ∈ Finset.univ, collision j w := by
    intro w hw
    by_cases hg : Good M Cc (s w)
    · right
      have hj : ∃ j, collision j w := by simpa only [not_and, hg, true_implies,
        not_forall, not_not, collision] using hw
      obtain ⟨j, hj⟩ := hj
      exact ⟨j, Finset.mem_univ _, hj⟩
    · exact Or.inl hg
  calc
    _ ≤ uprob (fun w => ¬ Good M Cc (s w) ∨ ∃ j ∈ Finset.univ, collision j w) :=
      uprob_mono hbad
    _ ≤ uprob (fun w => ¬ Good M Cc (s w)) +
        uprob (fun w => ∃ j ∈ Finset.univ, collision j w) := uprob_or_le _ _
    _ ≤ 12 * Cc.gates.length * δ + m * (1 / Fintype.card K) :=
      add_le_add (uprob_not_good_le_of_uniform_data M Cc hdec hδ hC
        (fun w => ((s w).1, (s w).2.1)) hs (fun w => (s w).2.2)) hcoll

end TCSlib.Cryptography.SecureComputation
