/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Pairing.MatrixDH.Defs
import TCSlib.Cryptography.Foundations.Subexponential
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Mathematical closure of matrix-DH advantage bounds

## Main definitions

No runtime definition, reduction, realiser, machine, or sampler is introduced.

## Main results

* BilinearGen.mddhCorrection_subexpSmall: the explicit `4d/p` correction bound.
* BilinearGen.mddh_subexpHard_of_adv_le: common-exponent hardness from a machine-wise bound.
* BilinearGen.mddh_negligible_of_adv_le: negligible advantage from the same bound shape.

## References

* [Wee20] H. Wee, Functional Encryption for Quadratic Functions from k-Lin, Revisited,
  TCC 2020; full version, ePrint 2020/1420, Section 2.1. The explicit `4d/p` correction
  belongs to the polynomial-loss column-hybrid implementation, rather than its tight citation.
* [JLS26] A. Jain, H. Lin, A. Sahai, Indistinguishability Obfuscation from Well-Founded
  Assumptions, J. ACM 73(1), Article 1, 2026, Section 1.1 (one common security exponent).

These mathematical adapters assume the quantitative reduction inequality; they do not
construct it or any realising machine.
-/

namespace TCSlib.Cryptography.Pairing.BilinearGen

open Complexity TCSlib.Cryptography.Games

/-- The explicit matrix-reduction correction `4*d(κ)/p(κ)` is subexponentially small
at every exponent strictly between zero and one when `p(κ) ≥ 2^κ`. This scalar bound
is technical glue for the column-hybrid implementation of the matrix-DH consequence
[Wee20, §2.1, p. 4]; the constant records the implementation's rank-failure bound.
The schedule need not be prime, and no algorithm evaluates it.

**Proof sketch.** Bound `4d(κ)/p(κ)` by `4d(κ)2⁻κ`, dominate `d` by its fixed
polynomial majorant, and use subexpSmall_two_pow_neg with mul_pow and const_mul.
Pointwise domination gives every target exponent strictly below one. -/
theorem mddhCorrection_subexpSmall (p : ℕ → ℕ) (d : PolyExpr) (hpb : ∀ κ, 2 ^ κ ≤ p κ)
    {c : ℝ} (hc₀ : 0 < c) (hc₁ : c < 1) :
    SubexpSmall c (fun κ => (d.eval κ : ℝ) * (4 / (p κ : ℝ))) := by
  obtain ⟨C, k, hC⟩ := d.eval_le
  have he₀ : 0 < (c + 1) / 2 := ?_
  swap
  · linarith only [hc₀]
  have he₁ : (c + 1) / 2 < 1 := ?_
  swap
  · linarith only [hc₁]
  have hce : c < (c + 1) / 2 := ?_
  swap
  · linarith only [hc₁]
  have hbase := (subexpSmall_two_pow_neg.mul_pow zero_lt_one he₁ k).const_mul
    he₀ hce (4 * (C : ℝ) * 2 ^ k)
  refine hbase.mono ⟨1, ?_⟩
  intro κ hκ
  have hκ₁ : (1 : ℝ) ≤ κ := Nat.one_le_cast.mpr hκ
  have hd : (d.eval κ : ℝ) ≤ (C : ℝ) * ((κ : ℝ) + 1) ^ k := ?_
  swap
  · exact_mod_cast hC κ
  have hstep : (κ : ℝ) + 1 ≤ 2 * (κ : ℝ) := ?_
  swap
  · linarith only [hκ₁]
  have hpoly : (d.eval κ : ℝ) ≤ (C : ℝ) * 2 ^ k * (κ : ℝ) ^ k := ?_
  swap
  · calc
      _ ≤ (C : ℝ) * (2 * (κ : ℝ)) ^ k :=
        hd.trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (add_nonneg (Nat.cast_nonneg _) zero_le_one) hstep k)
          (Nat.cast_nonneg _))
      _ = (C : ℝ) * 2 ^ k * (κ : ℝ) ^ k := ?_
    rw [_root_.mul_pow, mul_assoc]
  have hcast : (2 : ℝ) ^ κ ≤ (p κ : ℝ) := ?_
  swap
  · exact_mod_cast hpb κ
  have hdiv : (4 : ℝ) / (p κ : ℝ) ≤ 4 * (2 : ℝ)⁻¹ ^ κ := ?_
  swap
  · simpa only [div_eq_mul_inv, inv_pow] using
      (div_le_div_of_nonneg_left (a := (4 : ℝ)) zero_le_four
        (pow_pos two_pos κ) hcast)
  rw [abs_mul, Nat.abs_cast,
    abs_of_nonneg (div_nonneg zero_le_four (Nat.cast_nonneg _))]
  calc
    _ ≤ (d.eval κ : ℝ) * (4 * (2 : ℝ)⁻¹ ^ κ) :=
      mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg _)
    _ ≤ ((C : ℝ) * 2 ^ k * (κ : ℝ) ^ k) * (4 * (2 : ℝ)⁻¹ ^ κ) :=
      mul_le_mul_of_nonneg_right hpoly
        (mul_nonneg zero_le_four (pow_nonneg (inv_nonneg.mpr zero_le_two) κ))
    _ = (4 * (C : ℝ) * 2 ^ k) * ((κ : ℝ) ^ k * (2 : ℝ)⁻¹ ^ κ) := ?_
    _ ≤ |(4 * (C : ℝ) * 2 ^ k) * ((κ : ℝ) ^ k * (2 : ℝ)⁻¹ ^ κ)| := le_abs_self _
  ring

/-- A machine-wise bound by a fixed polynomial times one DLIN advantage plus a common
subexponentially small correction transfers subexponential DLIN hardness to uniform-matrix
MDDH. The resulting positive exponent is fixed before the MDDH adversary is chosen.
Each chosen DLIN machine must satisfy the bound at all security parameters.

**Proof sketch.** Read DLIN's common exponent `a>0` and choose `η=min(a,1)/4` before D.
Use the fixed polynomial majorant and mul_pow/const_mul to reach exponent `2η` for the
weighted DLIN advantage. The correction has that same exponent; add at exponent `η`
and use pointwise domination. No generic polynomial-closure lemma is introduced. -/
theorem mddh_subexpHard_of_adv_le (G : BilinearGen) (d ℓ : PolyExpr) (β : ℕ → ℝ)
    (hβ : ∀ c : ℝ, 0 < c → c < 1 → SubexpSmall c β)
    (hBound : ∀ D : NUPPT, ∃ B : NUPPT, ∀ κ,
      G.mddhAdv d ℓ D κ ≤ (d.eval κ : ℝ) * G.dlinAdv B κ + β κ)
    (h : G.SubexpDLIN) : SubexpHard (G.mddhAdv d ℓ) := by
  obtain ⟨a, ha, hA⟩ := (subexpHard_iff G.dlinAdv).1 (G.subexpDLIN_iff.1 h)
  let η : ℝ := min a 1 / 4
  have hmin₀ : 0 < min a (1 : ℝ) := lt_min ha zero_lt_one
  have hη₀ : 0 < η := ?_
  swap
  · dsimp only [η]
    linarith only [hmin₀]
  have h3a : 3 * η < a := ?_
  swap
  · have hmin := min_le_left a (1 : ℝ)
    dsimp only [η]
    linarith only [hmin, ha]
  have h21 : 2 * η < 1 := ?_
  swap
  · have hmin := min_le_right a (1 : ℝ)
    dsimp only [η]
    linarith only [hmin]
  have h3₀ : 0 < 3 * η := ?_
  swap
  · linarith only [hη₀]
  have h2₀ : 0 < 2 * η := ?_
  swap
  · linarith only [hη₀]
  have h23 : 2 * η < 3 * η := ?_
  swap
  · linarith only [hη₀]
  have hη2 : η < 2 * η := ?_
  swap
  · linarith only [hη₀]
  obtain ⟨C, k, hC⟩ := d.eval_le
  refine (subexpHard_iff _).2 ⟨η, hη₀, ?_⟩
  intro D
  obtain ⟨B, hB⟩ := hBound D
  have hbase := ((hA B).mul_pow ha h3a k).const_mul h3₀ h23 ((C : ℝ) * 2 ^ k)
  have hweighted : SubexpSmall (2 * η)
      (fun κ => (d.eval κ : ℝ) * G.dlinAdv B κ) := ?_
  swap
  · refine hbase.mono ⟨1, ?_⟩
    intro κ hκ
    have hκ₁ : (1 : ℝ) ≤ κ := Nat.one_le_cast.mpr hκ
    have hd : (d.eval κ : ℝ) ≤ (C : ℝ) * ((κ : ℝ) + 1) ^ k := ?_
    swap
    · exact_mod_cast hC κ
    have hstep : (κ : ℝ) + 1 ≤ 2 * (κ : ℝ) := ?_
    swap
    · linarith only [hκ₁]
    have hpoly : (d.eval κ : ℝ) ≤ (C : ℝ) * 2 ^ k * (κ : ℝ) ^ k := ?_
    swap
    · calc
        _ ≤ (C : ℝ) * (2 * (κ : ℝ)) ^ k :=
          hd.trans (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (add_nonneg (Nat.cast_nonneg _) zero_le_one) hstep k)
            (Nat.cast_nonneg _))
        _ = (C : ℝ) * 2 ^ k * (κ : ℝ) ^ k := ?_
      rw [_root_.mul_pow, mul_assoc]
    have hAdv : 0 ≤ G.dlinAdv B κ := ?_
    swap
    · rw [G.dlinAdv_eq B κ]
      exact advantage_nonneg _ _
    have hbase₀ : 0 ≤ ((C : ℝ) * 2 ^ k) * ((κ : ℝ) ^ k * G.dlinAdv B κ) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg zero_le_two _))
        (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hAdv)
    rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hAdv), abs_of_nonneg hbase₀]
    calc
      _ ≤ ((C : ℝ) * 2 ^ k * (κ : ℝ) ^ k) * G.dlinAdv B κ :=
        mul_le_mul_of_nonneg_right hpoly hAdv
      _ = _ := mul_assoc _ _ _
  have hsum := hweighted.add (hβ (2 * η) h2₀ h21) h2₀ hη2
  refine hsum.mono ⟨0, ?_⟩
  intro κ _
  have hM : 0 ≤ G.mddhAdv d ℓ D κ := ?_
  swap
  · rw [G.mddhAdv_eq d ℓ D κ]
    exact advantage_nonneg _ _
  rw [abs_of_nonneg hM]
  exact (hB κ).trans (le_abs_self _)

/-- A machine-wise bound by a fixed polynomial times one negligible DLIN advantage plus
a common negligible correction gives negligible uniform-matrix MDDH advantage for every
machine adversary. Each chosen DLIN machine works at all security parameters.

**Proof sketch.** Read dlinAssumption_iff for the chosen machine. Reuse
EnsembleLemmas.negligible_polyExpr_mul, Negligible.add and pointwise domination through
mddhAdv_eq/advantage_nonneg. No machine or new negligible-closure theorem is constructed. -/
theorem mddh_negligible_of_adv_le (G : BilinearGen) (d ℓ : PolyExpr) (β : ℕ → ℝ)
    (hβ : Negligible β)
    (hBound : ∀ D : NUPPT, ∃ B : NUPPT, ∀ κ,
      G.mddhAdv d ℓ D κ ≤ (d.eval κ : ℝ) * G.dlinAdv B κ + β κ)
    (h : G.DLINAssumption) : ∀ D : NUPPT, Negligible (G.mddhAdv d ℓ D) := by
  intro D
  obtain ⟨B, hB⟩ := hBound D
  have hmain : Negligible (fun κ => (d.eval κ : ℝ) * G.dlinAdv B κ) :=
    EnsembleLemmas.negligible_polyExpr_mul d ((G.dlinAssumption_iff).mp h B)
  refine (hmain.add hβ).mono ⟨0, ?_⟩
  intro κ _
  have hnonneg : 0 ≤ G.mddhAdv d ℓ D κ :=
    (G.mddhAdv_eq d ℓ D κ).symm ▸ advantage_nonneg _ _
  rw [abs_of_nonneg hnonneg]
  exact (hB κ).trans (le_abs_self _)

end TCSlib.Cryptography.Pairing.BilinearGen
