/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.HardcoreBit.GoldreichLevin

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Goldreich–Levin on an encoded finite domain

The concrete Goldreich–Levin theorem `HardcoreBit.invProb_guessInverter` [Gar26, Theorem 2.3]
draws `x` uniformly from the cube `{0,1}^n`. The collection form of [PS10, Theorem 87.3]
(needed by [PS10, Theorem 104.4] and by Chapter 4) draws `x` uniformly from a finite domain
`D_i` [PS10, Definition 41.1] that is only *encoded* into `{0,1}^m` by an injective `encD_i`:
the image is in general a strict subset of the cube (`Z_N^*`, `QR_N`, a subgroup `G_q`), the
predictor's behaviour off the image is uncontrolled, and the uniform element of `D_i` is not a
uniform element of the cube. So the cube theorem cannot be transferred to collections, and the
run-2 sketch of `Collection.OneWay.glPad_hardCore`, which "identified `D_i` with `{0,1}^m`
through the injective encoding", was invalid (run-3 audit, finding P4-2).

This file proves the statement that is actually needed. For any finite type `α`, any map
`enc : α → {0,1}^m` (injectivity is not needed to *recover* `enc x`; it is needed downstream
to decode `x` from it), any `f : α → β` and any predictor `A` of `⟨enc x, r⟩` from `(f x, r)`
with success `1/2 + ε` over uniform `x : α`, `r ∈ {0,1}^m` and coins, the recovery procedure
of [PS10, Algorithm 89.6] (`HardcoreBit.guessRecover`) outputs `enc x` with probability at
least `ε/(4·2^k)` whenever `2m ≤ ε²(2^k − 1)`. The proof is the proof of
`invProb_guessInverter`: the good set is `half_le_uprob_threshold` over `α` (already general),
and the per-`x` analysis (`uprob_idealRecover_ne_le`, `one_sub_sum_le_uprob_eq`,
`uprob_guessRecover_ge`) is applied, for each fixed `x`, to the *constant* function
`fun _ => f x` at the point `enc x` — those lemmas only ever evaluate `f` at the point under
analysis, so no uniformity of the point on the cube is used.

## Main definitions

None: the file proves lemmas about the existing `HardcoreBit.guessRecover`.

## Main results

* `TCSlib.Cryptography.HardcoreBit.invProb_guessInverter_enc` — the encoded-domain
  Goldreich–Levin bound.
* `TCSlib.Cryptography.HardcoreBit.invProb_guessInverter_enc_pad` — the same bound on the
  sample space `(α × {0,1}^m) × coins` of the padded collection (the padding `r` is carried
  along unused), the form consumed by `Collection.OneWay.glPad_hardCore`
  (`Asymptotic/HardCore.lean`).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.4.3: Definition 41.1; §3.4.2–3.4.3: Theorem 87.3, Algorithm 89.6.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.5 (Theorem 2.3, Figure 2.5).
* [GL89] O. Goldreich, L. Levin, *A hard-core predicate for all one-way functions*, STOC 1989.
-/

namespace TCSlib.Cryptography.HardcoreBit

open Finset TCSlib.Cryptography

/-- **Goldreich–Levin on an encoded finite domain** [PS10, Theorem 87.3, collection form;
Gar26, Theorem 2.3, real case]: let `x` be uniform on a finite type `α`, `enc : α → {0,1}^m`,
`f : α → β`, and let the predictor `A` output `⟨enc x, r⟩` on `(f x, r)` with probability at
least `1/2 + ε` (`ε > 0`) over uniform `x`, `r ∈ {0,1}^m` and its coins. If the number `k` of
guessed bits satisfies `2m ≤ ε²(2^k − 1)`, then the recovery procedure of
[PS10, Algorithm 89.6] (`guessRecover A k`, run on `f x` with fresh coins) outputs the string
`enc x` with probability at least `ε/(4·2^k)` over uniform `x` and its coins. This is the
cube theorem `invProb_guessInverter` with the uniform cube element replaced by an arbitrary
uniformly distributed encoded element; in particular `x` uniform on a collection domain `D_i`
encoded by `encD_i` (run-3 audit P4-2).

**Deviation:** none beyond those of `invProb_guessInverter` (explicit `k`, nonempty subsets,
bound `ε/(4·2^k)` instead of the text's `ε³/(32n)`, source error 37).

**Proof sketch.** Let `q x := Pr_{r, c}[A(f x, r; c) = ⟨enc x, r⟩]`, which is the per-point
success `secProb (fun _ => f x) A (enc x)` of the concrete layer; by Fubini
(`uprob_comp_equiv` with `Equiv.prodAssoc`, `uprob_prod`) the hypothesis says
`1/2 + ε ≤ uexp q` (in particular `α` is nonempty). The good set
`{x | 1/2 + ε/2 ≤ q x}` has probability at least `ε/2` (`half_le_uprob_threshold`). For a good
`x`, every bit of the ideal procedure for the constant function `fun _ => f x` at the point
`enc x` is wrong with probability at most `1/(ε²(2^k − 1)) ≤ 1/(2m)`
(`uprob_idealRecover_ne_le`), so by the union bound (`one_sub_sum_le_uprob_eq`) the ideal
procedure outputs `enc x` with probability at least `1/2`, and the guessing procedure does so
with probability at least `2^{-k} · 1/2` (`uprob_guessRecover_ge`), its output on
`(fun _ => f x) (enc x) = f x` being `guessRecover A k (f x)`. Averaging over `x`
(`uprob_prod`, `uprob_mul_le_uexp`) gives `(ε/2)(2^{-k}/2) = ε/(4·2^k)`. -/
theorem invProb_guessInverter_enc {α β ρ : Type*} [Fintype α] [Fintype ρ] [Nonempty ρ] {m : ℕ}
    (enc : α → Fin m → Bool) (f : α → β) (A : β × (Fin m → Bool) → ρ → Bool) {k : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hk : 2 * (m : ℝ) ≤ ε ^ 2 * ((2 : ℝ) ^ k - 1))
    (h : 1 / 2 + ε ≤ uprob fun z : (α × (Fin m → Bool)) × ρ =>
      A (f z.1.1, z.1.2) z.2 = ip (enc z.1.1) z.1.2) :
    ε / (4 * 2 ^ k) ≤ uprob fun z : α × GuessCoins m k ρ =>
      guessRecover A k (f z.1) z.2 = enc z.1 := by
  classical
  set q : α → ℝ := fun x => secProb (fun _ : Fin m → Bool => f x) A (enc x) with hq
  have hexp : uprob (fun z : (α × (Fin m → Bool)) × ρ =>
      A (f z.1.1, z.1.2) z.2 = ip (enc z.1.1) z.1.2) = uexp q := by
    rw [← uprob_comp_equiv (Equiv.prodAssoc α (Fin m → Bool) ρ).symm, uprob_prod]
    rfl
  haveI : Nonempty α := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have h0 : uexp q = 0 := by simp [uexp]
    rw [hexp, h0] at h
    linarith
  have hG := half_le_uprob_threshold q (fun x => uprob_le_one _) (by norm_num) hε.le (hexp ▸ h)
  have hgood : ∀ x, 1 / 2 + ε / 2 ≤ q x →
      1 / 2 ^ k * (1 / 2) ≤ uprob fun c : GuessCoins m k ρ =>
        guessRecover A k (f x) c = enc x := by
    intro x hx
    refine le_trans ?_ (uprob_guessRecover_ge (fun _ => f x) A (enc x))
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine le_trans ?_ (one_sub_sum_le_uprob_eq
      (fun ω : (Fin k → Fin m → Bool) × (Fin m → NESubset k → ρ) =>
        idealRecover (fun _ => f x) A (enc x) ω.1 ω.2) (enc x))
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; norm_num
    have hpos : (0 : ℝ) < (2 : ℝ) ^ k - 1 := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      nlinarith [sq_nonneg ε]
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0; norm_num at hpos
      · exact h0
    have hsum : ∑ i : Fin m, uprob (fun ω : (Fin k → Fin m → Bool) ×
        (Fin m → NESubset k → ρ) =>
          idealRecover (fun _ => f x) A (enc x) ω.1 ω.2 i ≠ enc x i) ≤
        ∑ _i : Fin m, 1 / (ε ^ 2 * ((2 : ℝ) ^ k - 1)) :=
      sum_le_sum fun i _ => uprob_idealRecover_ne_le (fun _ => f x) A hk0 (enc x) i hε hx
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    have : (m : ℝ) * (1 / (ε ^ 2 * ((2 : ℝ) ^ k - 1))) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_iff₀ (by positivity)]
      linarith
    linarith
  rw [uprob_prod]
  have hcomb := uprob_mul_le_uexp (G := fun x => 1 / 2 + ε / 2 ≤ q x)
    (q := fun x => uprob fun c : GuessCoins m k ρ => guessRecover A k (f x) c = enc x)
    (fun x => uprob_nonneg _) hgood
  calc ε / (4 * 2 ^ k) = ε / 2 * (1 / 2 ^ k * (1 / 2)) := by field_simp; ring
    _ ≤ uprob (fun x => 1 / 2 + ε / 2 ≤ q x) * (1 / 2 ^ k * (1 / 2)) := by gcongr
    _ ≤ _ := hcomb

/-- **Goldreich–Levin on an encoded domain, with the padding carried along**: the bound of
`invProb_guessInverter_enc` on the sample space `(α × {0,1}^m) × coins` of the padded
collection `g_i(x, r) = (f_i(x), r)` of [PS10, Theorem 87.3] — the element `(x, r)` of the
padded domain together with the recovery coins, the padding `r` being unused by the recovery
procedure. This is the shape of the inner probability of `Collection.invProbAt` for
`Collection.glPad` and the form consumed by `Collection.OneWay.glPad_hardCore`
(run-3 audit P4-2). The proof is `invProb_guessInverter_enc` and the reshuffling of an
independent unused component (`uprob_fst`, `uprob_comp_equiv`). -/
theorem invProb_guessInverter_enc_pad {α β ρ : Type*} [Fintype α] [Fintype ρ] [Nonempty ρ]
    {m : ℕ} (enc : α → Fin m → Bool) (f : α → β) (A : β × (Fin m → Bool) → ρ → Bool) {k : ℕ}
    {ε : ℝ} (hε : 0 < ε) (hk : 2 * (m : ℝ) ≤ ε ^ 2 * ((2 : ℝ) ^ k - 1))
    (h : 1 / 2 + ε ≤ uprob fun z : (α × (Fin m → Bool)) × ρ =>
      A (f z.1.1, z.1.2) z.2 = ip (enc z.1.1) z.1.2) :
    ε / (4 * 2 ^ k) ≤ uprob fun z : (α × (Fin m → Bool)) × GuessCoins m k ρ =>
      guessRecover A k (f z.1.1) z.2 = enc z.1.1 := by
  refine le_trans (invProb_guessInverter_enc enc f A hε hk h) (le_of_eq ?_)
  let e : (α × GuessCoins m k ρ) × (Fin m → Bool) ≃ (α × (Fin m → Bool)) × GuessCoins m k ρ :=
    { toFun := fun w => ((w.1.1, w.2), w.1.2)
      invFun := fun z => ((z.1.1, z.2), z.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc uprob (fun z : α × GuessCoins m k ρ => guessRecover A k (f z.1) z.2 = enc z.1)
      = uprob (fun w : (α × GuessCoins m k ρ) × (Fin m → Bool) =>
          guessRecover A k (f w.1.1) w.1.2 = enc w.1.1) :=
        (uprob_fst (fun z : α × GuessCoins m k ρ => guessRecover A k (f z.1) z.2 = enc z.1)).symm
    _ = _ := uprob_comp_equiv e fun z : (α × (Fin m → Bool)) × GuessCoins m k ρ =>
          guessRecover A k (f z.1.1) z.2 = enc z.1.1

end TCSlib.Cryptography.HardcoreBit
