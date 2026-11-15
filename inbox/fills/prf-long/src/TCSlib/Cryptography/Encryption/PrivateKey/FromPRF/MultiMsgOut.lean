/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.Hybrid
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.HybridLemmas
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.ReductionMachine
import TCSlib.Cryptography.Encryption.PrivateKey.EnsembleSecurity
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.Defs
import TCSlib.Cryptography.Pseudorandom.Indistinguishability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The multi-message bound at `ℓ(n)`-bit outputs

The total of [PS10, Theorem 99.2] for a keyed family with `ℓ(n)`-bit outputs (ruling B3), without
the scheme: for a family `F` whose keyed ensemble is oracle-indistinguishable from the random
functions with `ℓ(n)`-bit outputs, every non-uniform PPT `D` distinguishes the encoded real
hybrids of any two mask vectors with negligible advantage, uniformly in the masks
(`MultiMsg.exists_negligible_distAdv_prfEncRealOut`). The `n`-bit scheme's
`prfScheme_multiMessageSecure` is its case `ℓ = var`.

## Main definitions

* `encodeTupleOut`: the encoded tuple of ciphertext pairs with `n`-bit points and `l`-bit pads.

## Main results

* `MultiMsg.encodeList_eq_flatMap`: `encodeList` as a concatenation of chunks (the general form of
  a private lemma of `FromPRF.lean`).
* `encodeTupleOut_eq_flatten`: the encoded tuple as the machine produces it.
* `MultiMsg.exists_negligible_distAdv_prfEncRealOut`: the total.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.8, Definition 96.2, and §3.9, Theorem 99.2, with `ℓ`-bit outputs.)
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-- **The encoded ciphertext tuple at output width `l`**: `encodeList` of the pairs
`⟨r_j, c_j⟩` of an `n`-bit point and an `l`-bit string,
`encodeTupleOut v = encodeList (List.ofFn fun j => ⟨⟦(v j).1⟧, ⟦(v j).2⟧⟩)`. -/
def encodeTupleOut {n l q : ℕ} (v : Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) :
    List Bool :=
  PrivateKeyScheme.encodeList
    (List.ofFn fun j => pairEncode (List.ofFn (v j).1) (List.ofFn (v j).2))

/-- The defining equation:
`encodeTupleOut v = encodeList (List.ofFn fun j => ⟨⟦(v j).1⟧, ⟦(v j).2⟧⟩)`. -/
theorem encodeTupleOut_eq {n l q : ℕ} (v : Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) :
    encodeTupleOut v = PrivateKeyScheme.encodeList
      (List.ofFn fun j => pairEncode (List.ofFn (v j).1) (List.ofFn (v j).2)) :=
  rfl

/-- **`encodeList` is a concatenation of chunks**: `encodeList l` is the concatenation of the
self-delimited chunks `⟨c, []⟩`, `encodeList l = l.flatMap fun c => ⟨c, []⟩`. -/
theorem MultiMsg.encodeList_eq_flatMap : ∀ l : List (List Bool),
    PrivateKeyScheme.encodeList l = l.flatMap fun c => pairEncode c []
  | [] => by rw [PrivateKeyScheme.encodeList_nil, List.flatMap_nil]
  | c :: l => by
    rw [PrivateKeyScheme.encodeList_cons, List.flatMap_cons, MultiMsg.encodeList_eq_flatMap l]
    simp [pairEncode_eq]

/-- The encoded tuple at width `l` is the concatenation of the chunks `⟨⟨r_j, c_j⟩, []⟩` (the
form in which `MultiMsg.exists_queryChainOut_nuppt` produces it):
`encodeTupleOut v = (List.ofFn fun j => ⟨⟨⟦(v j).1⟧, ⟦(v j).2⟧⟩, []⟩).flatten`. -/
theorem encodeTupleOut_eq_flatten {n l q : ℕ}
    (v : Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) :
    encodeTupleOut v =
      (List.ofFn fun j =>
        pairEncode (pairEncode (List.ofFn (v j).1) (List.ofFn (v j).2)) []).flatten := by
  rw [encodeTupleOut_eq, MultiMsg.encodeList_eq_flatMap, MultiMsg.flatMap_ofFn]

/-- **[PS10, Theorem 99.2] at `ℓ(n)`-bit outputs, the total** (with `ℓ`-bit outputs; ruling B3):
if the keyed ensemble of `F n : {0,1}^n → {0,1}^n → {0,1}^{ℓ(n)}` is oracle-indistinguishable
from the random functions with `ℓ(n)`-bit outputs, then for every non-uniform PPT `D` and
polynomial `q` there is a negligible `ε` with, for every `n` and all masks
`w, w' ∈ ({0,1}^{ℓ(n)})^{q(n)+1}`,
`distAdv (encodeTupleOut ∘ prfEncRealOut (F n) w) (encodeTupleOut ∘ prfEncRealOut (F n) w')
(D.distinguisherL n) ≤ ε n`, the seeds being a uniform key and `q(n) + 1` uniform points.

**Deviation:** the collision bound is `C(q(n)+1, 2) · 2^{−n}` for the `q(n) + 1` values
`r₀, …, r_{q(n)}` (the text writes `C(q(n), 2) · 2^{−n}`; source error 35 of the plan).

**Proof sketch.** As `prfScheme_multiMessageSecure`, without the scheme.
1. At each `n` choose the pair of masks maximizing the advantage (`Finset.exists_max_image`).
2. For the two maximizing mask vectors, build the next-query machines `B₀`, `B₁`
   (`MultiMsg.exists_queryChainOut_nuppt`, budget `q + 1`); with `MultiMsg.prfAdv_congr_equiv`,
   `eval_multiMsgAdvOut` and `encodeTupleOut_eq_flatten` their PRF advantages are those of
   `multiMsgAdvOut w (D ∘ encodeTupleOut)`.
3. `distAdv_comp` and `distAdv_prfEncRealOut_le` bound the advantage by
   `prfAdv (F n) B₀ + prfAdv (F n) B₁ + 2 · C(q(n)+1, 2) / 2^n`.
4. This is negligible: `OracleEnsemble.Indist.negligible_prfAdv` at the budget `q + 1` and
   `MultiMsg.negligible_choose_div_two_pow`, with `Negligible.add` and `Negligible.const_mul`. -/
theorem MultiMsg.exists_negligible_distAdv_prfEncRealOut {ℓ : PolyExpr}
    {F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (ℓ.eval n) → Bool)}
    (hF : (OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := ℓ) F).Indist (OracleEnsemble.random .var ℓ))
    (D : NUPPT) (q : PolyExpr) :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (w w' : Fin (q.eval n + 1) → Fin (ℓ.eval n) → Bool),
      distAdv (fun z => encodeTupleOut (prfEncRealOut (F n) w z))
        (fun z => encodeTupleOut (prfEncRealOut (F n) w' z)) (D.distinguisherL n) ≤ ε n := by
  -- the worst mask pair at each parameter (hard-wired into the reductions)
  have hmax : ∀ n, ∃ p : (Fin (q.eval n + 1) → Fin (ℓ.eval n) → Bool) ×
      (Fin (q.eval n + 1) → Fin (ℓ.eval n) → Bool),
      ∀ w : (Fin (q.eval n + 1) → Fin (ℓ.eval n) → Bool) ×
          (Fin (q.eval n + 1) → Fin (ℓ.eval n) → Bool),
        distAdv (fun z => encodeTupleOut (prfEncRealOut (F n) w.1 z))
            (fun z => encodeTupleOut (prfEncRealOut (F n) w.2 z)) (D.distinguisherL n) ≤
          distAdv (fun z => encodeTupleOut (prfEncRealOut (F n) p.1 z))
            (fun z => encodeTupleOut (prfEncRealOut (F n) p.2 z)) (D.distinguisherL n) := by
    intro n
    obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ
      (fun w : (Fin (q.eval n + 1) → Fin (ℓ.eval n) → Bool) ×
          (Fin (q.eval n + 1) → Fin (ℓ.eval n) → Bool) =>
        distAdv (fun z => encodeTupleOut (prfEncRealOut (F n) w.1 z))
          (fun z => encodeTupleOut (prfEncRealOut (F n) w.2 z)) (D.distinguisherL n))
      Finset.univ_nonempty
    exact ⟨p, fun w => hp w (Finset.mem_univ w)⟩
  choose μ hμ using hmax
  -- the next-query machines for the two hard-wired mask vectors
  obtain ⟨B₀, hB₀⟩ := MultiMsg.exists_queryChainOut_nuppt D q ℓ fun n => (μ n).1
  obtain ⟨B₁, hB₁⟩ := MultiMsg.exists_queryChainOut_nuppt D q ℓ fun n => (μ n).2
  refine ⟨fun n => prfAdv (F n) (B₀.toOracleAdversary n n (ℓ.eval n) (q.eval n + 1)) +
      prfAdv (F n) (B₁.toOracleAdversary n n (ℓ.eval n) (q.eval n + 1)) +
      2 * ((Nat.choose (q.eval n + 1) 2 : ℝ) / 2 ^ n), ?_, fun n w w' => ?_⟩
  · -- the asymptotic step: two PRF advantages and the collision term
    simpa only [PolyExpr.eval_add, PolyExpr.eval_const] using
      ((hF.negligible_prfAdv B₀ (.add q (.const 1))).add
        (hF.negligible_prfAdv B₁ (.add q (.const 1)))).add
        ((MultiMsg.negligible_choose_div_two_pow q).const_mul 2)
  · refine (hμ n (w, w')).trans ?_
    -- the machine step: the oracle adversaries of `B₀`, `B₁` are the `multiMsgAdvOut`
    have hadv : ∀ (B : NUPPT) (v : Fin (q.eval n + 1) → Fin (ℓ.eval n) → Bool)
        (φ : (Fin (q.eval n + 1) → Fin n → Bool) × D.Coins n ≃ B.Coins n),
        (∀ (g : (Fin n → Bool) → (Fin (ℓ.eval n) → Bool)) ρ c,
          (B.toOracleAdversary n n (ℓ.eval n) (q.eval n + 1) (φ (ρ, c))).eval g =
            decide (D.runAt n (List.ofFn fun j =>
              pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v j + g (ρ j)))) []).flatten c =
                [true])) →
        prfAdv (F n) (B.toOracleAdversary n n (ℓ.eval n) (q.eval n + 1)) =
          prfAdv (F n) (multiMsgAdvOut v fun x c => D.distinguisherL n (encodeTupleOut x) c) := by
      intro B v φ hφ
      refine MultiMsg.prfAdv_congr_equiv (F n) _ _ φ fun g x => ?_
      rw [hφ g x.1 x.2, eval_multiMsgAdvOut, NUPPT.distinguisherL_eq, encodeTupleOut_eq_flatten]
    obtain ⟨φ₀, hφ₀⟩ := hB₀ n
    obtain ⟨φ₁, hφ₁⟩ := hB₁ n
    dsimp only
    rw [hadv B₀ (μ n).1 φ₀ hφ₀, hadv B₁ (μ n).2 φ₁ hφ₁]
    -- the concrete step: the six hybrids at width `ℓ(n)`
    exact (distAdv_comp encodeTupleOut (prfEncRealOut (F n) (μ n).1)
      (prfEncRealOut (F n) (μ n).2) (D.distinguisherL n)).symm.trans_le
        (distAdv_prfEncRealOut_le (F n) (μ n).1 (μ n).2
          (fun x c => D.distinguisherL n (encodeTupleOut x) c))

end TCSlib.Cryptography
