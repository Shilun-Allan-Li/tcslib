/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Reductions.LPN
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Reductions.PRG
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Stretch

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Explicit JLS security inequalities and their corollaries

## Main definitions

* `Params.Realizable`: the conjunction of the shared realiser obligations.

## Main results

* `lemma42`, `prop41`: explicit every-realiser advantage bounds.
* `theorem41` and its negligible/subexponential existence corollaries on Raw.

## References

* [JLS26] A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Well-Founded Assumptions*, J. ACM 73(1), Article 1, February 2026, §§2-4.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
  3rd ed., January 2010, Definition 26.8 (non-uniform PPT adversaries).
-/

namespace TCSlib.Cryptography.Obfuscation.StructuredSeed

open Complexity
open TCSlib.Cryptography.Games

namespace Params

/-- Realisability supplies a NUPPT for each explicit reduction and advice family
[JLS26, Proposition 4.1, pp. 18-19]. Dv14 leaves this Phase B obligation as a
hypothesis; targets discharge it through the shared preTarget theorem. Dv16:
the shared RealizesOn constrains only encoded challenges and layout-length coins,
which weakens the predicate and strengthens every-realiser security inequalities. -/
def Realizable (P : Params) (π : PrimeSchedule) : Prop :=
  P.LPNRealizable π ∧ P.PRGRealizable π

/-- Realisability is the conjunction of the two shared-realiser propositions; glue. -/
theorem realizable_iff (P : Params) (π : PrimeSchedule) :
    P.Realizable π ↔ P.LPNRealizable π ∧ P.PRGRealizable π := Iff.rfl

end Params

/-- The initial real-tail distribution and final uniform-tail distribution differ by at
most κ LPN advantages plus one Boolean PRG advantage [JLS26, Lemma 4.2, p. 19].
Dv8 includes independent buckets; Dv12 hardwires averaging choices; Dv14 states the
bound for every realising NUPPT, with no machine construction.

**Proof sketch.** Choose the largest gap in the real-tail chain, hardwire its other draws
in LPN advice at every inverse-indexed dimension, and apply the every-realiser hop lemma.
Use the PRG hop on the all-uniform public vectors, then the existing hybrid inequality. -/
theorem lemma42 (P : Params) (π : PrimeSchedule) (A : NUPPT) :
    ∃ (ωL : ∀ L, P.LPNAdvice π L) (ωG : ∀ N, P.PRGAdvice π N),
      ∀ BL BG : NUPPT,
        BL.RealizesOn (P.lpnEnc π) (A.coins.subst .var)
          (fun L x r => P.lpnRed π A L (ωL L) x r) →
        BG.RealizesOn P.prgEnc (A.coins.subst .var)
          (fun N x r => P.prgRed π A N (ωG N) x r) →
        ∀ κ, advantage (P.chainGame A true 0 κ (π κ))
          (P.chainGame A false κ κ (π κ)) ≤
            (κ : ℝ) * (P.lpnFamily_raw π).adv BL (P.ℓ κ) + P.G.adv BG (P.n κ) := by
  classical
  have hselect : ∀ κ : ℕ, ∃ i : Fin (κ + 1),
      0 < κ → i.val < κ ∧
        advantage (P.chainGame A true 0 κ (π κ))
          (P.chainGame A true κ κ (π κ)) ≤
            (κ : ℝ) * advantage (P.chainGame A true i.val κ (π κ))
              (P.chainGame A true (i.val + 1) κ (π κ)) := ?_
  swap
  · intro κ
    by_cases hκ : 0 < κ
    · obtain ⟨i, hi, hgap⟩ := exists_advantage_hybrid_gap
        (fun j : ℕ => P.chainGame A true j κ (π κ)) hκ
      refine ⟨⟨i, hi.trans_le (Nat.le_succ κ)⟩, ?_⟩
      intro _
      refine ⟨hi, ?_⟩
      have hκR : 0 < (κ : ℝ) := Nat.cast_pos.mpr hκ
      exact ((div_le_iff₀ hκR).mp hgap).trans_eq (mul_comm _ _)
    · exact ⟨⟨0, Nat.succ_pos κ⟩, fun h => False.elim (hκ h)⟩
  choose hops hhops using hselect
  obtain ⟨ωL, hL⟩ := P.lpn_hop π A (fun _ => true) hops
  obtain ⟨ωG, hG⟩ := P.prg_hop π A
  refine ⟨ωL, ωG, ?_⟩
  intro BL BG hBL hBG κ
  have hreal : advantage (P.chainGame A true 0 κ (π κ))
      (P.chainGame A true κ κ (π κ)) ≤
        (κ : ℝ) * (P.lpnFamily_raw π).adv BL (P.ℓ κ) := ?_
  swap
  · by_cases hκ : 0 < κ
    · have hs := hhops κ hκ
      exact hs.2.trans
        (mul_le_mul_of_nonneg_left (hL BL hBL κ hs.1) (Nat.cast_nonneg κ))
    · have hz : κ = 0 := Nat.eq_zero_of_not_pos hκ
      subst κ
      simpa only [Nat.cast_zero, zero_mul, advantage_self] using
        (le_rfl : (0 : ℝ) ≤ 0)
  have hprg := hG BG hBG κ
  exact (advantage_triangle
    (P.chainGame A true 0 κ (π κ))
    (P.chainGame A true κ κ (π κ))
    (P.chainGame A false κ κ (π κ))).trans (add_le_add hreal hprg)

/-- The raw sPRG advantage is at most 2κ LPN advantages, one PRG advantage and twice
the exact error probability [JLS26, Proposition 4.1, pp. 18-19]. Dv1 fixes the schedule;
Dv9 quantifies every prime schedule; Dv12 hardwires averaging choices; Dv18 uses Raw.
Dv16: RealizesOn constrains only encoded challenges and layout-length coins, so its
weaker predicate makes this every-realiser inequality stronger.

**Proof sketch.** Bound H0-H1 and H2-H3 by the error event. Connect H1 to H2 by the
real-tail LPN chain, the PRG hop, and the reversed uniform-tail LPN chain. At each κ
choose the largest of the 2κ LPN gaps and hardwire the remaining draws. The shared
realiser readers identify every realiser's verdict, and the existing hybrid inequalities
sum the gaps. At κ=0 only the PRG hop and the explicit error slack remain. -/
theorem prop41 (P : Params) (π : PrimeSchedule) (A : NUPPT) :
    ∃ (ωL : ∀ L, P.LPNAdvice π L) (ωG : ∀ N, P.PRGAdvice π N),
      ∀ BL BG : NUPPT,
        BL.RealizesOn (P.lpnEnc π) (A.coins.subst .var)
          (fun L x r => P.lpnRed π A L (ωL L) x r) →
        BG.RealizesOn P.prgEnc (A.coins.subst .var)
          (fun N x r => P.prgRed π A N (ωG N) x r) →
        ∀ κ, (jlsSPRG_raw P π).adv A κ ≤
          2 * (κ : ℝ) * (P.lpnFamily_raw π).adv BL (P.ℓ κ) +
            P.G.adv BG (P.n κ) + 2 * P.errProb κ (π κ) := by
  classical
  let gap : ℕ → Bool → ℕ → ℝ := fun κ b i =>
    advantage (P.chainGame A b i κ (π κ))
      (P.chainGame A b (i + 1) κ (π κ))
  have hselect : ∀ κ : ℕ, ∃ b : Bool, ∃ i : Fin (κ + 1),
      0 < κ → i.val < κ ∧
        ∀ (tail : Bool) (j : ℕ), j < κ → gap κ tail j ≤ gap κ b i.val := ?_
  swap
  · intro κ
    by_cases hκ : 0 < κ
    · have hne : (Finset.univ : Finset (Bool × Fin κ)).Nonempty :=
        ⟨(true, ⟨0, hκ⟩), Finset.mem_univ _⟩
      obtain ⟨q, _, hmax⟩ := Finset.exists_max_image
        (Finset.univ : Finset (Bool × Fin κ))
        (fun q : Bool × Fin κ => gap κ q.1 q.2.val) hne
      refine ⟨q.1, ⟨q.2.val, q.2.isLt.trans_le (Nat.le_succ κ)⟩, ?_⟩
      intro _
      refine ⟨q.2.isLt, ?_⟩
      intro tail j hj
      exact hmax (tail, ⟨j, hj⟩) (Finset.mem_univ _)
    · exact ⟨true, ⟨0, Nat.succ_pos κ⟩, fun h => False.elim (hκ h)⟩
  choose tails hops hmax using hselect
  obtain ⟨ωL, hL⟩ := P.lpn_hop π A tails hops
  obtain ⟨ωG, hG⟩ := P.prg_hop π A
  refine ⟨ωL, ωG, ?_⟩
  intro BL BG hBL hBG κ
  let aL : ℝ := (P.lpnFamily_raw π).adv BL (P.ℓ κ)
  let aG : ℝ := P.G.adv BG (P.n κ)
  have hstep : 0 < κ → ∀ (b : Bool) (j : ℕ), j < κ → gap κ b j ≤ aL := ?_
  swap
  · intro hκ b j hj
    have hs := hmax κ hκ
    exact (hs.2 b j hj).trans (hL BL hBL κ hs.1)
  have hchain : ∀ b : Bool,
      advantage (P.chainGame A b 0 κ (π κ))
        (P.chainGame A b κ κ (π κ)) ≤ (κ : ℝ) * aL := ?_
  swap
  · intro b
    by_cases hκ : 0 < κ
    · calc
        advantage (P.chainGame A b 0 κ (π κ))
            (P.chainGame A b κ κ (π κ)) ≤
          Finset.sum (Finset.range κ) (fun j => gap κ b j) :=
            advantage_hybrid (fun j : ℕ => P.chainGame A b j κ (π κ)) κ
        _ ≤ Finset.sum (Finset.range κ) (fun _j => aL) :=
          Finset.sum_le_sum (fun j hj => hstep hκ b j (Finset.mem_range.mp hj))
        _ = (κ : ℝ) * aL := ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    · have hz : κ = 0 := Nat.eq_zero_of_not_pos hκ
      subst κ
      simpa only [Nat.cast_zero, zero_mul, advantage_self] using
        (le_rfl : (0 : ℝ) ≤ 0)
  have hreverse : advantage (P.chainGame A false κ κ (π κ))
      (P.chainGame A false 0 κ (π κ)) ≤ (κ : ℝ) * aL :=
    (advantage_comm (P.chainGame A false κ κ (π κ))
      (P.chainGame A false 0 κ (π κ))).le.trans (hchain false)
  have hprg : advantage (P.chainGame A true κ κ (π κ))
      (P.chainGame A false κ κ (π κ)) ≤ aG := hG BG hBG κ
  have hlink : advantage (P.hyb A .prg κ (π κ)) (P.hyb A .uniform κ (π κ)) =
      advantage (P.chainGame A true 0 κ (π κ))
        (P.chainGame A false 0 κ (π κ)) := ?_
  swap
  · simp only [advantage_eq, P.hyb_prg_accept_eq_chain_zero,
      P.hyb_uniform_accept_eq_chain_zero]
  have hmiddle : advantage (P.hyb A .prg κ (π κ))
      (P.hyb A .uniform κ (π κ)) ≤ 2 * (κ : ℝ) * aL + aG := ?_
  swap
  · calc
      advantage (P.hyb A .prg κ (π κ)) (P.hyb A .uniform κ (π κ)) =
        advantage (P.chainGame A true 0 κ (π κ))
          (P.chainGame A false 0 κ (π κ)) := hlink
      _ ≤ advantage (P.chainGame A true 0 κ (π κ))
          (P.chainGame A true κ κ (π κ)) +
          advantage (P.chainGame A true κ κ (π κ))
            (P.chainGame A false 0 κ (π κ)) :=
        advantage_triangle _ _ _
      _ ≤ advantage (P.chainGame A true 0 κ (π κ))
          (P.chainGame A true κ κ (π κ)) +
          (advantage (P.chainGame A true κ κ (π κ))
            (P.chainGame A false κ κ (π κ)) +
            advantage (P.chainGame A false κ κ (π κ))
              (P.chainGame A false 0 κ (π κ))) :=
        add_le_add_left (advantage_triangle _ _ _) _
      _ ≤ (κ : ℝ) * aL + (aG + (κ : ℝ) * aL) :=
        add_le_add (hchain true) (add_le_add hprg hreverse)
      _ = 2 * (κ : ℝ) * aL + aG := ?_
    ring
  have hraw : (jlsSPRG_raw P π).adv A κ =
      advantage (P.hyb A .real κ (π κ)) (P.hyb A .random κ (π κ)) := ?_
  swap
  · rw [SPRG.Raw.adv_eq, ← P.hyb_real_eq_raw π A κ, ← P.hyb_random_eq_raw π A κ]
  change (jlsSPRG_raw P π).adv A κ ≤
    2 * (κ : ℝ) * aL + aG + 2 * P.errProb κ (π κ)
  calc
    (jlsSPRG_raw P π).adv A κ =
      advantage (P.hyb A .real κ (π κ)) (P.hyb A .random κ (π κ)) := hraw
    _ ≤ advantage (P.hyb A .real κ (π κ)) (P.hyb A .prg κ (π κ)) +
        advantage (P.hyb A .prg κ (π κ)) (P.hyb A .random κ (π κ)) :=
      advantage_triangle _ _ _
    _ ≤ P.errProb κ (π κ) +
        (advantage (P.hyb A .prg κ (π κ)) (P.hyb A .uniform κ (π κ)) +
          advantage (P.hyb A .uniform κ (π κ)) (P.hyb A .random κ (π κ))) :=
      add_le_add (P.hyb_real_prg_le A κ (π κ)) (advantage_triangle _ _ _)
    _ ≤ P.errProb κ (π κ) +
        ((2 * (κ : ℝ) * aL + aG) + P.errProb κ (π κ)) :=
      add_le_add_left (add_le_add hmiddle (P.hyb_uniform_random_le A κ (π κ))) _
    _ = 2 * (κ : ℝ) * aL + aG + 2 * P.errProb κ (π κ) := ?_
  ring

/-- Under realisability and the two assumptions, the raw construction is secure
[JLS26, Theorem 4.1, p. 11]. Dv3 uses the construction's own LPN family; Dv13 uses
NUPPT adversaries; Dv14 retains realisability as the Phase B obligation, and Dv18 uses Raw.

**Proof sketch.** Instantiate the advice from prop41 and the realisers from Realizable.
Reindex negligible LPN and PRG advantages along ℓ≥κ and n≥κ. Multiply by the polynomial
2κ, add the Claim 4.2 slack, and use the shared negligibility closure lemmas. -/
theorem jls_secure (P : Params) (π : PrimeSchedule) {cLoc : ℕ}
    (hLoc : P.R.HasLocality cLoc) (hR : P.Realizable π)
    (hG : P.G.Secure) (hLPN : (P.lpnFamily_raw π).Assumption) :
    (jlsSPRG_raw P π).Secure := by
  apply (SPRG.Raw.secure_iff _).2
  intro A
  obtain ⟨ωL, ωG, hprop⟩ := prop41 P π A
  have hreal := (Params.realizable_iff P π).1 hR
  obtain ⟨BL, hBL⟩ := (P.LPNRealizable_iff π).1 hreal.1 A ωL
  obtain ⟨BG, hBG⟩ := (P.PRGRealizable_iff π).1 hreal.2 A ωG
  have hL := ((LPNFamily.Raw.assumption_iff _).1 hLPN) BL
  have hG' := ((BoolPRG.secure_iff _).1 hG) BG
  have hℓ : ∀ κ, κ ≤ P.ℓ κ := ?_
  swap
  · intro κ
    rw [P.ℓ_eq]
    exact Nat.le_pow (lt_of_lt_of_le (Nat.zero_lt_succ 0) P.one_le_E)
  have hn : ∀ κ, κ ≤ P.n κ := P.le_n
  have hLcomp := hL.comp_of_le P.ℓ hℓ
  have hGcomp := hG'.comp_of_le P.n hn
  have hLfactor : Negligible
      (fun κ => 2 * (κ : ℝ) * (P.lpnFamily_raw π).adv BL (P.ℓ κ)) := ?_
  swap
  · simpa only [pow_one, mul_assoc] using (hLcomp.mul_pow 1).const_mul 2
  have hsum := (hLfactor.add hGcomp).add (negligible_two_pow_neg.const_mul 2)
  apply hsum.mono
  obtain ⟨κ₀, herr⟩ := P.claim42 hLoc
  refine ⟨κ₀, ?_⟩
  intro κ hκ
  have hbd := (hprop BL BG hBL hBG κ).trans
    (add_le_add_left
      (mul_le_mul_of_nonneg_left (herr κ hκ (π κ)) zero_le_two) _)
  have hnonneg : 0 ≤ (jlsSPRG_raw P π).adv A κ := ?_
  swap
  · rw [SPRG.Raw.adv_eq]
    exact Games.advantage_nonneg _ _
  rw [abs_of_nonneg hnonneg, abs_of_nonneg (hnonneg.trans hbd)]
  exact hbd

/-- The raw advantage has explicit subexponential exponent
min(E*cL,min(E*D*cG,1))/2 [JLS26, Theorem 4.1, p. 11]. Dv13 uses the shared
SubexpSmall API against NUPPT; Dv14 assumes realisability; Dv18 uses Raw.

**Proof sketch.** Reindex the LPN term by κ^E and PRG term by κ^(E*D). Use the shared
polynomial-factor and constant-factor closure lemmas at an intermediate exponent below
the common minimum. Claim 4.2 controls the error term by 2^(-κ). Two applications of
sum closure yield half the minimum, then prop41 gives domination of the advantage. -/
theorem jls_subexpSmall (P : Params) (π : PrimeSchedule) {cLoc : ℕ}
    (hLoc : P.R.HasLocality cLoc) (hR : P.Realizable π) {cL cG : ℝ}
    (hcL : 0 < cL) (hcG : 0 < cG)
    (hG : ∀ B : NUPPT, SubexpSmall cG (P.G.adv B))
    (hLPN : ∀ B : NUPPT, SubexpSmall cL ((P.lpnFamily_raw π).adv B)) (A : NUPPT) :
    SubexpSmall (min ((P.E : ℝ) * cL) (min ((P.E : ℝ) * P.D * cG) 1) / 2)
      ((jlsSPRG_raw P π).adv A) := by
  obtain ⟨ωL, ωG, hprop⟩ := prop41 P π A
  rcases (P.realizable_iff π).mp hR with ⟨hRL, hRG⟩
  obtain ⟨BL, hBL⟩ := ((P.LPNRealizable_iff π).mp hRL) A ωL
  obtain ⟨BG, hBG⟩ := ((P.PRGRealizable_iff π).mp hRG) A ωG
  have hbound := hprop BL BG hBL hBG
  have hEpos : 0 < (P.E : ℝ) :=
    Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one P.one_le_E)
  have hDpos : 0 < (P.D : ℝ) := Nat.cast_pos.mpr P.D_pos
  have hℓ : ∃ κ₀ : ℕ, ∀ κ ≥ κ₀, (κ : ℝ) ^ (P.E : ℝ) ≤ (P.ℓ κ : ℝ) := ?_
  swap
  · refine ⟨0, ?_⟩
    intro κ _
    rw [P.ℓ_eq, Nat.cast_pow, Real.rpow_natCast]
  have hn : ∃ κ₀ : ℕ, ∀ κ ≥ κ₀,
      (κ : ℝ) ^ ((P.E : ℝ) * P.D) ≤ (P.n κ : ℝ) := ?_
  swap
  · refine ⟨0, ?_⟩
    intro κ _
    rw [P.n_eq, P.ℓ_eq, Nat.cast_pow, Nat.cast_pow,
      Real.rpow_mul (Nat.cast_nonneg κ), Real.rpow_natCast, Real.rpow_natCast]
  have hL0 := (hLPN BL).comp_of_rpow_le (a := (P.E : ℝ)) (ℓ := P.ℓ)
    hcL.le hEpos hℓ
  have hG0 := (hG BG).comp_of_rpow_le (a := (P.E : ℝ) * (P.D : ℝ)) (ℓ := P.n)
    hcG.le (mul_pos hEpos hDpos) hn
  let M : ℝ := min ((P.E : ℝ) * cL) (min ((P.E : ℝ) * P.D * cG) 1)
  have hML : M ≤ (P.E : ℝ) * cL := min_le_left _ _
  have hMG : M ≤ (P.E : ℝ) * P.D * cG :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hM1 : M ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  have hM : 0 < M := lt_min_iff.mpr
    ⟨mul_pos hEpos hcL, lt_min_iff.mpr ⟨mul_pos (mul_pos hEpos hDpos) hcG, zero_lt_one⟩⟩
  have h78pos : 0 < 7 * M / 8 := ?_
  swap
  · linarith
  have h34pos : 0 < 3 * M / 4 := ?_
  swap
  · linarith
  have h58pos : 0 < 5 * M / 8 := ?_
  swap
  · linarith
  have h78lt : 7 * M / 8 < M := ?_
  swap
  · linarith
  have h34lt78 : 3 * M / 4 < 7 * M / 8 := ?_
  swap
  · linarith
  have h34leM : 3 * M / 4 ≤ M := ?_
  swap
  · linarith
  have h34lt1 : 3 * M / 4 < 1 := ?_
  swap
  · linarith
  have h58lt34 : 5 * M / 8 < 3 * M / 4 := ?_
  swap
  · linarith
  have h12lt58 : M / 2 < 5 * M / 8 := ?_
  swap
  · linarith
  have hLp := (hL0.mono_exponent hML).mul_pow hM h78lt 1
  have hLc := hLp.const_mul h78pos h34lt78 2
  have hGc := hG0.mono_exponent (h34leM.trans hMG)
  have hEc := subexpSmall_two_pow_neg.const_mul zero_lt_one h34lt1 2
  have hLG := hLc.add hGc h34pos h58lt34
  have hEw := hEc.mono_exponent h58lt34.le
  have hsum := hLG.add hEw h58pos h12lt58
  change SubexpSmall (M / 2) ((jlsSPRG_raw P π).adv A)
  apply hsum.mono
  obtain ⟨κ₀, hκ₀⟩ := P.claim42 hLoc
  refine ⟨κ₀, ?_⟩
  intro κ hκ
  have hb := (hbound κ).trans (add_le_add_left
    (mul_le_mul_of_nonneg_left (hκ₀ κ hκ (π κ)) zero_le_two) _)
  have hb' : (jlsSPRG_raw P π).adv A κ ≤
      (2 * ((κ : ℝ) ^ (1 : ℕ) * (P.lpnFamily_raw π).adv BL (P.ℓ κ)) +
        P.G.adv BG (P.n κ)) + 2 * (2 : ℝ)⁻¹ ^ κ := ?_
  swap
  · simpa only [pow_one, mul_assoc] using hb
  have ha : 0 ≤ (jlsSPRG_raw P π).adv A κ := ?_
  swap
  · rw [SPRG.Raw.adv_eq]
    exact advantage_nonneg _ _
  rw [abs_of_nonneg ha, abs_of_nonneg (ha.trans hb')]
  exact hb'

/-- Subexponential hardness of both assumptions gives subexponential raw sPRG security
[JLS26, Theorem 4.1, p. 11]. Dv13 quantifies a common exponent before every adversary;
Dv14 assumes the Phase B realisability obligation; Dv18 uses Raw.

**Proof sketch.** Read the two shared SubexpHard witnesses, use jls_subexpSmall, and
observe that its positive exponent depends only on the assumption exponents and P. -/
theorem jls_subexpSecure (P : Params) (π : PrimeSchedule) {cLoc : ℕ}
    (hLoc : P.R.HasLocality cLoc) (hR : P.Realizable π)
    (hG : SubexpHard P.G.adv) (hLPN : SubexpHard (P.lpnFamily_raw π).adv) :
    SubexpHard (jlsSPRG_raw P π).adv := by
  obtain ⟨cG, hcG, hGs⟩ := (subexpHard_iff _).mp hG
  obtain ⟨cL, hcL, hLs⟩ := (subexpHard_iff _).mp hLPN
  have hEpos : 0 < (P.E : ℝ) :=
    Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one P.one_le_E)
  have hDpos : 0 < (P.D : ℝ) := Nat.cast_pos.mpr P.D_pos
  have hm : 0 < min ((P.E : ℝ) * cL) (min ((P.E : ℝ) * P.D * cG) 1) :=
    lt_min_iff.mpr ⟨mul_pos hEpos hcL,
      lt_min_iff.mpr ⟨mul_pos (mul_pos hEpos hDpos) hcG, zero_lt_one⟩⟩
  apply (subexpHard_iff _).mpr
  refine ⟨min ((P.E : ℝ) * cL) (min ((P.E : ℝ) * P.D * cG) 1) / 2,
    div_pos hm zero_lt_two, ?_⟩
  intro A
  exact jls_subexpSmall P π hLoc hR hcL hcG hGs hLs A

/-- The raw construction is secure, has public degree d and private degree two, and
polynomial stretch [JLS26, Theorem 4.1, p. 11]. Dv1 fixes a sufficiently large schedule;
Dv3 uses its own LPN family; Dv6 uses composite bidegree; Dv9 allows every prime schedule;
Dv10 follows p. 17's degree d; Dv14 assumes realisability; Dv18 uses Raw.

The noise exponent is rational so that the rounded noise schedule is uniformly computable. This is
the computable-parameter version of the construction; no bridge from the paper's arbitrary-real
assumption is proved here.

**Proof sketch.** Combine raw security, the G4 correctness/degree theorem, and Claim 4.1. -/
theorem theorem41 (P : Params) (π : PrimeSchedule) {cLoc : ℕ} {τ : ℝ}
    (hLoc : P.R.HasLocality cLoc) (hτ : 1 < τ) (hs : P.G.HasStretch τ)
    (hE : E0 P.d (P.δ : ℝ) τ ≤ P.E) (hR : P.Realizable π)
    (hG : P.G.Secure) (hLPN : (P.lpnFamily_raw π).Assumption) :
    (jlsSPRG_raw P π).Secure ∧ (jlsSPRG_raw P π).HasComplexity P.d 2 ∧
      (jlsSPRG_raw P π).HasPolyStretch :=
  ⟨jls_secure P π hLoc hR hG hLPN,
    jls_hasComplexity P π,
    jls_hasPolyStretch P π hτ hs hE⟩

/-- The raw construction has the same complexity/stretch and subexponential security
[JLS26, Theorem 4.1, p. 11]. Dv13 means advantage against NUPPT, Dv14 assumes realisability, and
Dv18 leaves the primitive assembly to the targets.

The noise exponent is rational so that the rounded noise schedule is uniformly computable. This is
the computable-parameter version of the construction; no bridge from the paper's arbitrary-real
assumption is proved here.

**Proof sketch.** Combine jls_subexpSecure, G4 correctness/degree, and Claim 4.1. -/
theorem theorem41_subexp (P : Params) (π : PrimeSchedule) {cLoc : ℕ} {τ : ℝ}
    (hLoc : P.R.HasLocality cLoc) (hτ : 1 < τ) (hs : P.G.HasStretch τ)
    (hE : E0 P.d (P.δ : ℝ) τ ≤ P.E) (hR : P.Realizable π)
    (hG : SubexpHard P.G.adv) (hLPN : SubexpHard (P.lpnFamily_raw π).adv) :
    SubexpHard (jlsSPRG_raw P π).adv ∧ (jlsSPRG_raw P π).HasComplexity P.d 2 ∧
      (jlsSPRG_raw P π).HasPolyStretch :=
  ⟨jls_subexpSecure P π hLoc hR hG hLPN,
    jls_hasComplexity P π,
    jls_hasPolyStretch P π hτ hs hE⟩

/-- A secure raw structured-seed generator exists for every prime schedule
[JLS26, Theorem 4.1, p. 11]. Dv1 chooses a polynomial schedule; Dv3 assumes LPN
only for the construction's own families; Dv14 assumes realisability; Dv18 returns Raw.

The noise exponent is rational so that the rounded noise schedule is uniformly computable. This is
the computable-parameter version of the construction; no bridge from the paper's arbitrary-real
assumption is proved here.
This statement also does not claim a literal Definition 2.3 bridge.

**Proof sketch.** Choose E=max 1 E0, build Params from the given G and representation,
and apply theorem41 with the supplied family assumption and realisability. -/
theorem exists_sprg_raw {d cLoc : ℕ} (hd : 1 ≤ d) {δ : ℚ} {τ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hτ : 1 < τ) (G : BoolPRG)
    (R : G.MultilinearRep d) (hLoc : R.HasLocality cLoc) (hs : G.HasStretch τ)
    (hG : G.Secure) (π : PrimeSchedule)
    (hLPN : ∀ (E : ℕ) (hE : 1 ≤ E),
      (Params.lpnFamily_raw ⟨d, hd, δ, hδ, hδ1, E, hE, G, R⟩ π).Assumption)
    (hR : ∀ (E : ℕ) (hE : 1 ≤ E),
      (Params.Realizable ⟨d, hd, δ, hδ, hδ1, E, hE, G, R⟩ π)) :
    ∃ S : SPRG.Raw, (∀ κ, S.modulus κ = (π κ).p) ∧ S.Secure ∧
      S.HasComplexity d 2 ∧ S.HasPolyStretch := by
  let E := max 1 (E0 d (δ : ℝ) τ)
  have hE1 : 1 ≤ E := le_max_left _ _
  let P : Params := ⟨d, hd, δ, hδ, hδ1, E, hE1, G, R⟩
  refine ⟨jlsSPRG_raw P π, ?_, ?_⟩
  · intro κ
    exact jlsSPRG_raw_modulus P π κ
  · exact theorem41 P π hLoc hτ hs (le_max_right _ _) (hR E hE1) hG (hLPN E hE1)

/-- A subexponentially secure raw generator exists for every prime schedule
[JLS26, Theorem 4.1, p. 11]. Dv13 uses a common subexponential advantage exponent;
Dv14 assumes realisability; Dv18 returns the raw bundle.

The noise exponent is rational so that the rounded noise schedule is uniformly computable. This is
the computable-parameter version of the construction; no bridge from the paper's arbitrary-real
assumption is proved here.

**Proof sketch.** Choose the same sufficiently large schedule exponent and apply
 theorem41_subexp to the supplied family hardness and realisability. -/
theorem exists_sprg_raw_subexp {d cLoc : ℕ} (hd : 1 ≤ d) {δ : ℚ} {τ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hτ : 1 < τ) (G : BoolPRG)
    (R : G.MultilinearRep d) (hLoc : R.HasLocality cLoc) (hs : G.HasStretch τ)
    (hG : SubexpHard G.adv) (π : PrimeSchedule)
    (hLPN : ∀ (E : ℕ) (hE : 1 ≤ E),
      SubexpHard (Params.lpnFamily_raw ⟨d, hd, δ, hδ, hδ1, E, hE, G, R⟩ π).adv)
    (hR : ∀ (E : ℕ) (hE : 1 ≤ E),
      (Params.Realizable ⟨d, hd, δ, hδ, hδ1, E, hE, G, R⟩ π)) :
    ∃ S : SPRG.Raw, (∀ κ, S.modulus κ = (π κ).p) ∧ SubexpHard S.adv ∧
      S.HasComplexity d 2 ∧ S.HasPolyStretch := by
  let E := max 1 (E0 d (δ : ℝ) τ)
  have hE1 : 1 ≤ E := le_max_left _ _
  let P : Params := ⟨d, hd, δ, hδ, hδ1, E, hE1, G, R⟩
  refine ⟨jlsSPRG_raw P π, ?_, ?_⟩
  · intro κ
    exact jlsSPRG_raw_modulus P π κ
  · exact theorem41_subexp P π hLoc hτ hs (le_max_right _ _)
      (hR E hE1) hG (hLPN E hE1)

end TCSlib.Cryptography.Obfuscation.StructuredSeed
