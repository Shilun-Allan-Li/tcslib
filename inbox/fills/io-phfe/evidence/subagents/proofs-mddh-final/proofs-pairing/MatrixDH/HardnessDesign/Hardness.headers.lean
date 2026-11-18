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
    SubexpSmall c (fun κ => (d.eval κ : ℝ) * (4 / (p κ : ℝ))) := sorry

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
    (h : G.SubexpDLIN) : SubexpHard (G.mddhAdv d ℓ) := sorry

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
    (h : G.DLINAssumption) : ∀ D : NUPPT, Negligible (G.mddhAdv d ℓ D) := sorry

end TCSlib.Cryptography.Pairing.BilinearGen
