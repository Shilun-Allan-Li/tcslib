/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Theorems

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The four uniform-matrix losses in the DLIN composition

## Main definitions

* `Wee20.Quadratic.hopCols`, `hopRows`: exact dimensions of the four MDDH challenges.
* `Wee20.Quadratic.quadraticSlack`: ONE exact Π rank loss and the four column-hybrid losses.

## Main results

* `Wee20.Quadratic.mddh_sum_le`: simultaneous composition through the shared explicit
  dlinToMddh reduction, with one realiser per fixed-advice machine reduction.

These machine-realiser statements apply after the typed core has selected its explicit
reductions. They assert no machine realization for arbitrary typed adversaries.

## References

* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive 2020/1420, §2.1, p. 4 and §3.3, pp. 7–8.
* [JLS26] A. Jain, H. Lin, and A. Sahai, *Indistinguishability Obfuscation from
  Well-Founded Assumptions*, J. ACM full version, 2026, §1.1, PDF p. 3 (canonical DLIN).
  The direct canonical column reduction already accounts for zero-coordinate failures.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic

open Complexity TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
open scoped BigOperators

/-- The four response-column counts are 1,ell,1,1
[Wee20, Appendix B, Lemmas 2/4 and §3.3, pp. 7–8]. -/
def hopCols (ℓ : PolyExpr) (i : Fin 4) : PolyExpr := if i.val = 1 then ℓ else .const 1

/-- The response-column count is ell only for the adaptive Π-key hop. -/
theorem hopCols_eq (ℓ : PolyExpr) (i : Fin 4) :
    hopCols ℓ i = if i.val = 1 then ℓ else .const 1 := rfl

/-- The base-row counts are 3,mBound*q,n1,n2, in core-bound order
[Wee20, Appendix B, Lemmas 2/4 and §3.3, pp. 7–8, with uniform query padding]. -/
def hopRows {ℓ : PolyExpr} (n1 n2 q : PolyExpr) {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) (i : Fin 4) : PolyExpr :=
  if i.val = 0 then .const 3 else if i.val = 1 then PG.mBound.mul q
    else if i.val = 2 then n1 else n2

/-- The base-row count is its displayed four-case formula. -/
theorem hopRows_eq {ℓ : PolyExpr} (n1 n2 q : PolyExpr) {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) (i : Fin 4) : hopRows n1 n2 q PG i =
      if i.val = 0 then .const 3 else if i.val = 1 then PG.mBound.mul q
        else if i.val = 2 then n1 else n2 := rfl

/-- The combined statistical loss is one exact Π rank failure, three one-column MDDH
losses and one ell-column MDDH loss. The direct canonical JLS reduction includes the
zero-coordinate failure, so no additional DLIN matrix-presentation discrepancy is added. -/
noncomputable def quadraticSlack (G : BilinearGen) (ℓ : PolyExpr) (p : ℕ → ℕ) (κ : ℕ) : ℝ :=
  Linear.linearSlack G κ + 3 * BilinearGen.mddhSlack p (PolyExpr.const 1) κ +
    BilinearGen.mddhSlack p ℓ κ

/-- The total correction exposes its single rank term and four matrix losses. -/
theorem quadraticSlack_eq (G : BilinearGen) (ℓ : PolyExpr) (p : ℕ → ℕ) (κ : ℕ) :
    quadraticSlack G ℓ p κ = Linear.linearSlack G κ +
      3 * BilinearGen.mddhSlack p (PolyExpr.const 1) κ + BilinearGen.mddhSlack p ℓ κ := rfl

/-- Four machine MDDH advantages have a simultaneous explicit canonical-DLIN bound.
Each machine's reduction has one fixed-advice family, and EVERY realising DLIN machine
works [Wee20, §2.1, p. 4, explicit polynomial-loss implementation].

**Proof sketch.** Apply the shared mddhAdv_le separately to each of the four fixed NUPPT
machines, selecting its advice before the DLIN realiser. Sum the four inequalities using
the finite-sum order lemma. Read hopCols: three factors are one and the adaptive Π-key
factor is ell. The corresponding correction sum is 3*mddhSlack(1)+mddhSlack(ell).
The matrix randomization already accounts for the canonical DLIN exceptional coordinates;
there is no second Linear.dlinMatrixSlack term. -/
theorem mddh_sum_le (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 q : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (D : Fin 4 → NUPPT) :
    ∃ η : ∀ i : Fin 4, ∀ κ,
      BilinearGen.MddhAdvice p (hopCols ℓ i) (hopRows n1 n2 q PG i) κ,
    ∀ B : Fin 4 → NUPPT,
      (∀ i, (B i).RealizesOn G.dlinEnc (D i).coins
        (G.dlinToMddh p hp (hopCols ℓ i) (hopRows n1 n2 q PG i) (D i) (η i))) →
      ∀ κ, (∑ i : Fin 4, G.mddhAdv (hopCols ℓ i) (hopRows n1 n2 q PG i) (D i) κ) ≤
        (∑ i : Fin 4, ((hopCols ℓ i).eval κ : ℝ) * G.dlinAdv (B i) κ) +
        3 * BilinearGen.mddhSlack p (PolyExpr.const 1) κ + BilinearGen.mddhSlack p ℓ κ := sorry

/-- Every typed quadratic adversary has explicit fixed-advice L2 reductions for which
EVERY four realising MDDH machines, and then EVERY four realising canonical-DLIN machines,
satisfy the actual raw simulation bound with ONE rank loss and all four matrix corrections
[Wee20, §3, p. 6, main claim with §3.3, pp. 7–8].

**Proof sketch.** Choose the outer and Π advice using quadratic_saSimAdv_le, before any
MDDH realiser. For each subsequent four machine realisers, use mddh_sum_le to select the
four L1 advice families before their DLIN realisers. Sum the machine bounds and read
quadraticSlack_eq. The finite response-column factors are 1,ell,1,1. This is a polynomial
loss implementation of the source implication, not a claim of its cited tight reduction.
Neither exact PG privacy nor the outer mask replacements add a second rank term. -/
theorem quadratic_saSimAdv_dlin_le (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (A : SAAdv G n1 n2 PG) :
    ∃ φ : ∀ κ, MaskAdvice n1 n2 p κ,
    ∃ ωPi : Fin 2 → ∀ κ, Linear.Advice PG (piDim n1 n2) A.budget p κ,
    ∃ ωOuter : Fin 2 → ∀ κ, Advice n1 n2 A.budget PG p κ,
    ∀ D : Fin 4 → NUPPT,
      (D 0).RealizesOn (G.mddhEnc (PolyExpr.const 1) (PolyExpr.const 3)) A.coins
        (Linear.red0 G PG (piDim n1 n2) p hp (toLinear G n1 n2 PG p hp A φ) (ωPi 0)) →
      (D 1).RealizesOn (G.mddhEnc ℓ (PG.mBound.mul A.budget)) A.coins
        (Linear.red1 G PG (piDim n1 n2) p hp (toLinear G n1 n2 PG p hp A φ) (ωPi 1)) →
      (D 2).RealizesOn (G.mddhEnc (PolyExpr.const 1) n1) A.coins
        (red2 G n1 n2 PG p hp A (ωOuter 0)) →
      (D 3).RealizesOn (G.mddhEnc (PolyExpr.const 1) n2) A.coins
        (red3 G n1 n2 PG p hp A (ωOuter 1)) →
    ∃ η : ∀ i : Fin 4, ∀ κ,
      BilinearGen.MddhAdvice p (hopCols ℓ i) (hopRows n1 n2 A.budget PG i) κ,
    ∀ B : Fin 4 → NUPPT,
      (∀ i, (B i).RealizesOn G.dlinEnc (D i).coins
        (G.dlinToMddh p hp (hopCols ℓ i) (hopRows n1 n2 A.budget PG i) (D i) (η i))) →
      ∀ κ, freshSaSimAdv G n1 n2 PG A κ ≤
        (∑ i : Fin 4, ((hopCols ℓ i).eval κ : ℝ) * G.dlinAdv (B i) κ) +
        quadraticSlack G ℓ p κ := sorry

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic
