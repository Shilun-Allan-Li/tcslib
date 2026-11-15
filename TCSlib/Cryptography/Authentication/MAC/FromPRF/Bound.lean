/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.MAC.FromPRF.Game
import TCSlib.Cryptography.Authentication.MAC.FromPRF.Random
import TCSlib.Cryptography.Games.Bridges.Experiments

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The bound of the PRF-MAC reduction

Step 5 of the proof of [PS10, Theorem 135.4], for any MAC whose tag is a keyed function family
`F` (`n`-bit messages and tags, the key read off the generator's coins, a deterministic tag
`F_k(m)` and verification `F_k(m) = σ`): for every forger `A` and budget `q` there is a
distinguisher `D` with, at every `n`,
`Pr[forgeGame A q(n) n] ≤ prfAdv (F n) (D^{q(n) · 1 + 1}) + 2^{-n}` (`exists_forgeGame_le`).

The forgery probability is the acceptance probability of `D` against `F_k` (`accept_forgeGame_eq`,
`exists_macReduction`), and its acceptance probability against a uniform random function is at
most `2^{-n}` (`exists_macReduction`, `expect_fnForge_random_le`). The functions of the scheme's
widths are those of `n` bits read through `padFin` (`eval_toOracleAdversary_width₂`).

## Main results

* `PRFMAC.eval_toOracleAdversary_width₂`: an oracle adversary read at equal widths.
* `PRFMAC.exists_forgeGame_le`: the bound.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 135.4 (book p. 135).
-/

namespace TCSlib.Cryptography.Authentication.PRFMAC

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp

/-- **An oracle adversary read at equal widths:** for `m₁ = n` and `m₂ = n`, running
`D.toOracleAdversary n n n q c` against `f` is running `D.toOracleAdversary n m₁ m₂ q c` against
`f` with its inputs and outputs read at the widths `m₁`, `m₂`:
`(D^{n,n} c).eval f = (D^{m₁,m₂} c).eval (fun x => padFin m₂ ⟦f (padFin n ⟦x⟧)⟧)`.

**Proof sketch.** Substitute `m₁ = n` and `m₂ = n`; the readings are identities (`padFin_ofFn`). -/
theorem eval_toOracleAdversary_width₂ (D : NUPPT) (n q : ℕ) (c : D.Coins n) {m₁ m₂ : ℕ}
    (h₁ : m₁ = n) (h₂ : m₂ = n) (f : (Fin n → Bool) → (Fin n → Bool)) :
    (D.toOracleAdversary n n n q c).eval f =
      (D.toOracleAdversary n m₁ m₂ q c).eval
        (fun x => padFin m₂ (List.ofFn (f (padFin n (List.ofFn x))))) := by
  subst h₁ h₂
  simp only [padFin_ofFn]

/-- The functions `{0,1}^n → {0,1}^n` read at the widths `m₁ = n` and `m₂ = n`: `R` becomes
`fun x => padFin m₂ ⟦R (padFin n ⟦x⟧)⟧`. -/
private def padFunEquiv {n m₁ m₂ : ℕ} (h₁ : m₁ = n) (h₂ : m₂ = n) :
    ((Fin n → Bool) → (Fin n → Bool)) ≃ ((Fin m₁ → Bool) → (Fin m₂ → Bool)) where
  toFun R x := padFin m₂ (List.ofFn (R (padFin n (List.ofFn x))))
  invFun R' y := padFin n (List.ofFn (R' (padFin m₁ (List.ofFn y))))
  left_inv R := by
    funext y
    simp only
    rw [ofFn_padFin_of_length (by rw [List.length_ofFn]; omega), padFin_ofFn,
      ofFn_padFin_of_length (by rw [List.length_ofFn]; omega), padFin_ofFn]
  right_inv R' := by
    funext x
    simp only
    rw [ofFn_padFin_of_length (by rw [List.length_ofFn]; omega), padFin_ofFn,
      ofFn_padFin_of_length (by rw [List.length_ofFn]; omega), padFin_ofFn]

/-- **The bound of the PRF-MAC reduction** [PS10, Theorem 135.4, proof, step 5]: let `M` be a
MAC with `n`-bit messages and tags (`hℓ`, `ht`) and `F` a keyed family, with a bijection `key n`
from the generator's coins to `n`-bit keys, such that tagging `m` on the key of `rg` returns
`F_{key rg}(m)` (`htag`) and verification accepts `(m, σ)` iff `F_{key rg}(m) = σ` (`hacc`), the
messages read at `n` bits. Then for every forger `A` and budget `q` there is a next-query machine
`D` with, at every `n`,
`Pr[forgeGame A q(n) n] ≤ prfAdv (F n) (D.toOracleAdversary n n n (q(n) · 1 + 1)) + 2⁻ⁿ`.

**Proof sketch.** `D` is `exists_macReduction` at the widths `msgLen`, `tagLen`.
1. *With `F_k`.* The tag is deterministic, so the forgery probability is the average over `rg`
   of the forgery probability against `fnImpl (g rg)`, `g rg` being `F_{key rg}` read at the
   scheme's widths (`accept_forgeGame_eq`); by `exists_macReduction` it is `D`'s acceptance
   probability against `g rg`, which is `D`'s against `F_{key rg}` at `n` bits
   (`eval_toOracleAdversary_width₂`); `key` relabels the coins (`expect_sample_equiv`).
2. *With a random function.* `D`'s acceptance probability against a uniform `R` is, through the
   widths (`padFunEquiv`, `expect_sample_equiv`) and `exists_macReduction`, the average over `A`'s
   coins (`expect_sample_comm`) of the forgery probability against a random function, at most
   `2^{-n}` (`expect_fnForge_random_le`).
3. *The PRF advantage* is the absolute gap between the two (`prfAdv_def`, `distAdv_def`,
   `Bridge.acceptProb_eq`, `Bridge.acceptGame_eq`, `oracleDist_apply`); this is the published
   `TCSlib.Cryptography.prfAdv_eq_expect`. -/
theorem exists_forgeGame_le (M : MAC) (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (hℓ : ∀ n, M.msgLen.eval n = n) (ht : ∀ n, M.tagLen.eval n = n)
    (key : ∀ n, M.gen.Coins n ≃ (Fin n → Bool))
    (htag : ∀ n rg (m : Fin (M.msgLen.eval n) → Bool) (rt : M.tag.Coins n),
      M.tag.runAt n (pairEncode (M.gen.runAt n [] rg) (List.ofFn m)) rt =
        List.ofFn (F n (key n rg) (padFin n (List.ofFn m))))
    (hacc : ∀ n rg (m : Fin (M.msgLen.eval n) → Bool) (σ : Fin (M.tagLen.eval n) → Bool),
      M.Accepts n (M.gen.runAt n [] rg) m σ ↔
        List.ofFn (F n (key n rg) (padFin n (List.ofFn m))) = List.ofFn σ)
    (A : NUPPT) (q : PolyExpr) :
    ∃ D : NUPPT, ∀ n, accept (M.forgeGame A (q.eval n) n) ≤
      prfAdv (F n) (D.toOracleAdversary n n n ((macBudget q).eval n)) + (2 : ℝ)⁻¹ ^ n := by
  obtain ⟨D, hD⟩ := exists_macReduction M.msgLen M.tagLen q A
  refine ⟨D, fun n => ?_⟩
  -- The tag function at the scheme's widths.
  let g : M.gen.Coins n → (Fin (M.msgLen.eval n) → Bool) → (Fin (M.tagLen.eval n) → Bool) :=
    fun rg m => padFin _ (List.ofFn (F n (key n rg) (padFin n (List.ofFn m))))
  have hg_tag : ∀ rg (m : Fin (M.msgLen.eval n) → Bool) (rt : M.tag.Coins n),
      padFin (M.tagLen.eval n) (M.tag.runAt n (pairEncode (M.gen.runAt n [] rg) (List.ofFn m))
        rt) = g rg m := fun rg m rt => by
    rw [htag]
  have hg_acc : ∀ rg (m : Fin (M.msgLen.eval n) → Bool) (σ : Fin (M.tagLen.eval n) → Bool),
      M.Accepts n (M.gen.runAt n [] rg) m σ ↔ g rg m = σ := fun rg m σ => by
    rw [hacc]
    constructor
    · intro h
      show padFin _ (List.ofFn (F n (key n rg) (padFin n (List.ofFn m)))) = σ
      rw [h, padFin_ofFn]
    · intro h
      rw [← h]
      exact (ofFn_padFin_of_length (by rw [List.length_ofFn, ht])).symm
  -- With `F_k`: the forgery probability.
  have hreal : accept (M.forgeGame A (q.eval n) n) =
      expect (sample (Fin n → Bool)) fun k => expect (sample (D.Coins n)) fun c =>
        if (D.toOracleAdversary n n n ((macBudget q).eval n) c).eval (F n k) = true
        then (1 : ℝ) else 0 := by
    rw [accept_forgeGame_eq M A (q.eval n) n g hg_tag hg_acc, ← expect_sample_equiv (key n)]
    refine congrArg _ (funext fun rg => ?_)
    rw [← hD n (g rg)]
    refine congrArg _ (funext fun c => ?_)
    rw [eval_toOracleAdversary_width₂ D n _ c (hℓ n) (ht n) (F n (key n rg))]
  -- With a random function: at most `2⁻ⁿ`.
  have hrand : expect (sample ((Fin n → Bool) → (Fin n → Bool))) (fun R =>
      expect (sample (D.Coins n)) fun c =>
        if (D.toOracleAdversary n n n ((macBudget q).eval n) c).eval R = true
        then (1 : ℝ) else 0) ≤ (2 : ℝ)⁻¹ ^ n := by
    have he : ∀ R : (Fin n → Bool) → (Fin n → Bool),
        (expect (sample (D.Coins n)) fun c =>
          if (D.toOracleAdversary n n n ((macBudget q).eval n) c).eval R = true
          then (1 : ℝ) else 0) =
        expect (sample (D.Coins n)) fun c =>
          if (D.toOracleAdversary n (M.msgLen.eval n) (M.tagLen.eval n) ((macBudget q).eval n)
            c).eval (padFunEquiv (hℓ n) (ht n) R) = true then (1 : ℝ) else 0 := fun R => by
      refine congrArg _ (funext fun c => ?_)
      rw [eval_toOracleAdversary_width₂ D n _ c (hℓ n) (ht n) R]
      rfl
    simp only [he]
    rw [expect_sample_equiv (padFunEquiv (hℓ n) (ht n)) (fun R' =>
      expect (sample (D.Coins n)) fun c =>
        if (D.toOracleAdversary n (M.msgLen.eval n) (M.tagLen.eval n) ((macBudget q).eval n)
          c).eval R' = true then (1 : ℝ) else 0)]
    simp only [hD n]
    rw [expect_sample_comm]
    refine (expect_mono _ fun r => expect_fnForge_random_le _).trans (le_of_eq ?_)
    rw [expect_const, ht n, inv_pow]
  -- The PRF advantage is the gap.
  rw [hreal, TCSlib.Cryptography.prfAdv_eq_expect (F n) (D.toOracleAdversary n n n _)]
  linarith [le_abs_self ((expect (sample (Fin n → Bool)) fun k => expect (sample (D.Coins n))
    fun c => if (D.toOracleAdversary n n n ((macBudget q).eval n) c).eval (F n k) = true
      then (1 : ℝ) else 0) -
    expect (sample ((Fin n → Bool) → (Fin n → Bool))) (fun R =>
      expect (sample (D.Coins n)) fun c =>
        if (D.toOracleAdversary n n n ((macBudget q).eval n) c).eval R = true
        then (1 : ℝ) else 0))]

end TCSlib.Cryptography.Authentication.PRFMAC
