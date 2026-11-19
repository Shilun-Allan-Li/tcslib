/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Adapter
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.CommittedSimulator
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Compose
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Slack
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive.Security
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Simulation.Security

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Raw PHFE security with explicit realisers

The core inequality applies to every typed wire adversary. Replay preserves original
noncanonical input words, while the outer quadratic theorem supplies four explicit
reductions with exactly one rank loss. The committed inequality uses the actual
TwoStage.toSA conversion; it assumes no abstract machine security implication.

## Main definitions

* `Wee20RealizableSA`: L2 realisability only for oracle-machine-derived adversaries.
* `Wee20Realizable43`: L2 realisability only for committed machine pairs.

## Main results

* `wee20PHFE_saSimAdv_le`, `wee20PHFE_simAdv_le`: four explicit MDDH advantages and rank loss.
* Raw negligible and subexponential security under machine-restricted realisability.

## References

* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive 2020/1420, Section 3, main claim,
  p.6, with Section 3.3, pp.7-8 and Appendix B, Theorem 1.
* [GJLS21] R. Gay, A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Simple-to-State Hard Problems: New Assumptions, New Techniques, and Simplification*,
  EUROCRYPT 2021; full version, Cryptology ePrint Archive, Report 2020/764,
  revision of 3 January 2025, Definition 4.3, Remark 4.6 and Section 9.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20

open Complexity TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing

section

variable (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
variable (PG : PartialGarbling.Raw ℓ (n.mul n) (PHFE.TensorFn ℓ n d))

local notation "S" => wee20PHFE_raw G ℓ n d PG
local notation "Q" => PHFE.toQuadratic G ℓ n d PG

/-- Every typed wire adversary has fixed scalar advice for which EVERY four realising
machines satisfy the actual PHFE bound [Wee20, Section 3, p.6, with Section 3.3].
Only encoded challenges and layout-length coins constrain each shared realiser. The sole
statistical term is the unconditioned basis failure; partial-garbling privacy is exact.

**Proof sketch.** Apply PHFE.saSimAdv_eq_fresh and Quadratic.quadratic_saSimAdv_le to the
explicit PHFE.toQuadratic adversary. Read its coins and TOTAL budget through the adapter
readers and transport the four realisation hypotheses through those equalities. The
outer theorem chooses all scalar advice before any realiser. No efficiency is assumed.
-/
theorem wee20PHFE_saSimAdv_le (hPG : PHFE.PGSound PG) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (A : (S).SAAdv) :
    ∃ φ : ∀ κ, Quadratic.MaskAdvice n n p κ,
    ∃ ωPi : Fin 2 → ∀ κ, Linear.Advice PG (Quadratic.piDim n n) A.budget p κ,
    ∃ ωOuter : Fin 2 → ∀ κ, Quadratic.Advice n n A.budget PG p κ,
    ∀ D : Fin 4 → NUPPT,
      (D 0).RealizesOn (G.mddhEnc (PolyExpr.const 1) (PolyExpr.const 3)) A.coins
        (Linear.red0 G PG (Quadratic.piDim n n) p hp
          (Quadratic.toLinear G n n PG p hp (Q A) φ) (ωPi 0)) →
      (D 1).RealizesOn (G.mddhEnc ℓ (PG.mBound.mul A.budget)) A.coins
        (Linear.red1 G PG (Quadratic.piDim n n) p hp
          (Quadratic.toLinear G n n PG p hp (Q A) φ) (ωPi 1)) →
      (D 2).RealizesOn (G.mddhEnc (PolyExpr.const 1) n) A.coins
        (Quadratic.red2 G n n PG p hp (Q A) (ωOuter 0)) →
      (D 3).RealizesOn (G.mddhEnc (PolyExpr.const 1) n) A.coins
        (Quadratic.red3 G n n PG p hp (Q A) (ωOuter 1)) →
      ∀ κ, (S).saSimAdv (wee20SASim_raw G ℓ n d PG) A κ ≤
        G.mddhAdv (PolyExpr.const 1) (PolyExpr.const 3) (D 0) κ +
        G.mddhAdv ℓ (PG.mBound.mul A.budget) (D 1) κ +
        G.mddhAdv (PolyExpr.const 1) n (D 2) κ + G.mddhAdv (PolyExpr.const 1) n (D 3) κ +
        Linear.linearSlack G κ := sorry

/-- Every committed machine pair has the same explicit raw bound through its actual
TwoStage.toSA conversion [GJLS21, Definition 4.3, epsilon one; Remark 4.6]. Only encoded
challenges and layout-length coins constrain the realisers; the budget includes q keys
AND the single challenge, hence q+1 TOTAL calls.

**Proof sketch.** Read wee20Sim_raw_eq, then simAdv_eq_saSimAdv for the concrete raw
semi-adaptive simulator. Apply wee20PHFE_saSimAdv_le to A.toSA q and read toSA_coins and
toSA_budget. No oracle machine is built and no abstract secure-to-secure implication is
used. The advice is chosen before all four machine realisers.
-/
theorem wee20PHFE_simAdv_le (hPG : PHFE.PGSound PG) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (A : TwoStage) (q : PolyExpr) :
    let B := A.toSA («S» := S) q
    ∃ φ : ∀ κ, Quadratic.MaskAdvice n n p κ,
    ∃ ωPi : Fin 2 → ∀ κ, Linear.Advice PG (Quadratic.piDim n n) B.budget p κ,
    ∃ ωOuter : Fin 2 → ∀ κ, Quadratic.Advice n n B.budget PG p κ,
    ∀ D : Fin 4 → NUPPT,
      (D 0).RealizesOn (G.mddhEnc (PolyExpr.const 1) (PolyExpr.const 3)) B.coins
        (Linear.red0 G PG (Quadratic.piDim n n) p hp
          (Quadratic.toLinear G n n PG p hp (Q B) φ) (ωPi 0)) →
      (D 1).RealizesOn (G.mddhEnc ℓ (PG.mBound.mul B.budget)) B.coins
        (Linear.red1 G PG (Quadratic.piDim n n) p hp
          (Quadratic.toLinear G n n PG p hp (Q B) φ) (ωPi 1)) →
      (D 2).RealizesOn (G.mddhEnc (PolyExpr.const 1) n) B.coins
        (Quadratic.red2 G n n PG p hp (Q B) (ωOuter 0)) →
      (D 3).RealizesOn (G.mddhEnc (PolyExpr.const 1) n) B.coins
        (Quadratic.red3 G n n PG p hp (Q B) (ωOuter 1)) →
      ∀ κ, (S).simAdv (wee20Sim_raw G ℓ n d PG) A q κ ≤
        G.mddhAdv (PolyExpr.const 1) (PolyExpr.const 3) (D 0) κ +
        G.mddhAdv ℓ (PG.mBound.mul B.budget) (D 1) κ +
        G.mddhAdv (PolyExpr.const 1) n (D 2) κ + G.mddhAdv (PolyExpr.const 1) n (D 3) κ +
        Linear.linearSlack G κ := sorry

/-- Every fixed-advice L2 reduction of a MACHINE-DERIVED adversary has realising machines.
This is the reduction realisability hypothesis for [Wee20, Section 3.3], not an
honest-algorithm efficiency condition. It quantifies only over oracle NUPPTs.
The shared realiser constrains only encoded challenges and layout-length coins. -/
def Wee20RealizableSA (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) : Prop :=
  ∀ (A : NUPPT) (q : PolyExpr),
    let B := toSAAdv («S» := S) A q
    ∀ φ : ∀ κ, Quadratic.MaskAdvice n n p κ,
    ∀ ωPi : Fin 2 → ∀ κ, Linear.Advice PG (Quadratic.piDim n n) B.budget p κ,
    ∀ ωOuter : Fin 2 → ∀ κ, Quadratic.Advice n n B.budget PG p κ,
    ∃ D : Fin 4 → NUPPT,
      ((D 0).RealizesOn (G.mddhEnc (PolyExpr.const 1) (PolyExpr.const 3)) B.coins
        (Linear.red0 G PG (Quadratic.piDim n n) p hp
          (Quadratic.toLinear G n n PG p hp (Q B) φ) (ωPi 0))) ∧
      ((D 1).RealizesOn (G.mddhEnc ℓ (PG.mBound.mul B.budget)) B.coins
        (Linear.red1 G PG (Quadratic.piDim n n) p hp
          (Quadratic.toLinear G n n PG p hp (Q B) φ) (ωPi 1))) ∧
      ((D 2).RealizesOn (G.mddhEnc (PolyExpr.const 1) n) B.coins
        (Quadratic.red2 G n n PG p hp (Q B) (ωOuter 0))) ∧
      ((D 3).RealizesOn (G.mddhEnc (PolyExpr.const 1) n) B.coins
        (Quadratic.red3 G n n PG p hp (Q B) (ωOuter 1)))

/-- The realisability hypothesis has exactly the displayed machine and advice quantifiers. 

**Proof sketch.** The defining case and record projections reduce to the displayed expression
by reflexivity. -/
theorem wee20RealizableSA_iff (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) :
    Wee20RealizableSA G ℓ n d PG p hp ↔
  ∀ (A : NUPPT) (q : PolyExpr),
    let B := toSAAdv («S» := S) A q
    ∀ φ : ∀ κ, Quadratic.MaskAdvice n n p κ,
    ∀ ωPi : Fin 2 → ∀ κ, Linear.Advice PG (Quadratic.piDim n n) B.budget p κ,
    ∀ ωOuter : Fin 2 → ∀ κ, Quadratic.Advice n n B.budget PG p κ,
    ∃ D : Fin 4 → NUPPT,
      ((D 0).RealizesOn (G.mddhEnc (PolyExpr.const 1) (PolyExpr.const 3)) B.coins
        (Linear.red0 G PG (Quadratic.piDim n n) p hp
          (Quadratic.toLinear G n n PG p hp (Q B) φ) (ωPi 0))) ∧
      ((D 1).RealizesOn (G.mddhEnc ℓ (PG.mBound.mul B.budget)) B.coins
        (Linear.red1 G PG (Quadratic.piDim n n) p hp
          (Quadratic.toLinear G n n PG p hp (Q B) φ) (ωPi 1))) ∧
      ((D 2).RealizesOn (G.mddhEnc (PolyExpr.const 1) n) B.coins
        (Quadratic.red2 G n n PG p hp (Q B) (ωOuter 0))) ∧
      ((D 3).RealizesOn (G.mddhEnc (PolyExpr.const 1) n) B.coins
        (Quadratic.red3 G n n PG p hp (Q B) (ωOuter 1))) := Iff.rfl

/-- Every fixed-advice L2 reduction of a MACHINE-DERIVED adversary has realising machines.
This is the reduction realisability hypothesis for [Wee20, Section 3.3], not an
honest-algorithm efficiency condition. It quantifies only over committed machine pairs.
The shared realiser constrains only encoded challenges and layout-length coins. -/
def Wee20Realizable43 (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) : Prop :=
  ∀ (A : TwoStage) (q : PolyExpr),
    let B := A.toSA («S» := S) q
    ∀ φ : ∀ κ, Quadratic.MaskAdvice n n p κ,
    ∀ ωPi : Fin 2 → ∀ κ, Linear.Advice PG (Quadratic.piDim n n) B.budget p κ,
    ∀ ωOuter : Fin 2 → ∀ κ, Quadratic.Advice n n B.budget PG p κ,
    ∃ D : Fin 4 → NUPPT,
      ((D 0).RealizesOn (G.mddhEnc (PolyExpr.const 1) (PolyExpr.const 3)) B.coins
        (Linear.red0 G PG (Quadratic.piDim n n) p hp
          (Quadratic.toLinear G n n PG p hp (Q B) φ) (ωPi 0))) ∧
      ((D 1).RealizesOn (G.mddhEnc ℓ (PG.mBound.mul B.budget)) B.coins
        (Linear.red1 G PG (Quadratic.piDim n n) p hp
          (Quadratic.toLinear G n n PG p hp (Q B) φ) (ωPi 1))) ∧
      ((D 2).RealizesOn (G.mddhEnc (PolyExpr.const 1) n) B.coins
        (Quadratic.red2 G n n PG p hp (Q B) (ωOuter 0))) ∧
      ((D 3).RealizesOn (G.mddhEnc (PolyExpr.const 1) n) B.coins
        (Quadratic.red3 G n n PG p hp (Q B) (ωOuter 1)))

/-- The realisability hypothesis has exactly the displayed machine and advice quantifiers. 

**Proof sketch.** The defining case and record projections reduce to the displayed expression
by reflexivity. -/
theorem wee20Realizable43_iff (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) :
    Wee20Realizable43 G ℓ n d PG p hp ↔
  ∀ (A : TwoStage) (q : PolyExpr),
    let B := A.toSA («S» := S) q
    ∀ φ : ∀ κ, Quadratic.MaskAdvice n n p κ,
    ∀ ωPi : Fin 2 → ∀ κ, Linear.Advice PG (Quadratic.piDim n n) B.budget p κ,
    ∀ ωOuter : Fin 2 → ∀ κ, Quadratic.Advice n n B.budget PG p κ,
    ∃ D : Fin 4 → NUPPT,
      ((D 0).RealizesOn (G.mddhEnc (PolyExpr.const 1) (PolyExpr.const 3)) B.coins
        (Linear.red0 G PG (Quadratic.piDim n n) p hp
          (Quadratic.toLinear G n n PG p hp (Q B) φ) (ωPi 0))) ∧
      ((D 1).RealizesOn (G.mddhEnc ℓ (PG.mBound.mul B.budget)) B.coins
        (Linear.red1 G PG (Quadratic.piDim n n) p hp
          (Quadratic.toLinear G n n PG p hp (Q B) φ) (ωPi 1))) ∧
      ((D 2).RealizesOn (G.mddhEnc (PolyExpr.const 1) n) B.coins
        (Quadratic.red2 G n n PG p hp (Q B) (ωOuter 0))) ∧
      ((D 3).RealizesOn (G.mddhEnc (PolyExpr.const 1) n) B.coins
        (Quadratic.red3 G n n PG p hp (Q B) (ωOuter 1))) := Iff.rfl

/-- The raw PHFE bound composes its four explicit L2 reductions with the four L1
canonical-DLIN reductions, retaining one basis failure and all matrix corrections
[Wee20, Sections 2.1 and 3.3]. EVERY realiser is quantified after its scalar advice,
and shared realisers are constrained only on encoded challenges and layout-length coins.

**Proof sketch.** Use PHFE.saSimAdv_eq_fresh and Quadratic.quadratic_saSimAdv_dlin_le for the
explicit
adapter. Read toQuadratic_coins/toQuadratic_budget. The response-column factors are
1,ell,1,1, and quadraticSlack exposes the single basis loss and four 4*columns/p terms.
-/
theorem wee20PHFE_saSimAdv_dlin_le (hPG : PHFE.PGSound PG) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (A : (S).SAAdv) :
    ∃ φ : ∀ κ, Quadratic.MaskAdvice n n p κ,
    ∃ ωPi : Fin 2 → ∀ κ, Linear.Advice PG (Quadratic.piDim n n) A.budget p κ,
    ∃ ωOuter : Fin 2 → ∀ κ, Quadratic.Advice n n A.budget PG p κ,
    ∀ D : Fin 4 → NUPPT,
      (D 0).RealizesOn (G.mddhEnc (PolyExpr.const 1) (PolyExpr.const 3)) A.coins
        (Linear.red0 G PG (Quadratic.piDim n n) p hp
          (Quadratic.toLinear G n n PG p hp (Q A) φ) (ωPi 0)) →
      (D 1).RealizesOn (G.mddhEnc ℓ (PG.mBound.mul A.budget)) A.coins
        (Linear.red1 G PG (Quadratic.piDim n n) p hp
          (Quadratic.toLinear G n n PG p hp (Q A) φ) (ωPi 1)) →
      (D 2).RealizesOn (G.mddhEnc (PolyExpr.const 1) n) A.coins
        (Quadratic.red2 G n n PG p hp (Q A) (ωOuter 0)) →
      (D 3).RealizesOn (G.mddhEnc (PolyExpr.const 1) n) A.coins
        (Quadratic.red3 G n n PG p hp (Q A) (ωOuter 1)) →
    ∃ η : ∀ i : Fin 4, ∀ κ,
      BilinearGen.MddhAdvice p (Quadratic.hopCols ℓ i)
        (Quadratic.hopRows n n A.budget PG i) κ,
    ∀ B : Fin 4 → NUPPT,
      (∀ i, (B i).RealizesOn G.dlinEnc (D i).coins
        (G.dlinToMddh p hp (Quadratic.hopCols ℓ i)
          (Quadratic.hopRows n n A.budget PG i) (D i) (η i))) →
      ∀ κ, (S).saSimAdv (wee20SASim_raw G ℓ n d PG) A κ ≤
        (∑ i : Fin 4, ((Quadratic.hopCols ℓ i).eval κ : ℝ) * G.dlinAdv (B i) κ) +
        Quadratic.quadraticSlack G ℓ p κ := sorry

/-- The raw PHFE bound composes its four explicit L2 reductions with the four L1
canonical-DLIN reductions, retaining one basis failure and all matrix corrections
[Wee20, Sections 2.1 and 3.3]. EVERY realiser is quantified after its scalar advice,
and shared realisers are constrained only on encoded challenges and layout-length coins.

**Proof sketch.** Read wee20Sim_raw_eq and simAdv_eq_saSimAdv, then apply the SA composition.
-/
theorem wee20PHFE_simAdv_dlin_le (hPG : PHFE.PGSound PG) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (A : TwoStage) (q : PolyExpr) :
    let W := A.toSA («S» := S) q
    ∃ φ : ∀ κ, Quadratic.MaskAdvice n n p κ,
    ∃ ωPi : Fin 2 → ∀ κ, Linear.Advice PG (Quadratic.piDim n n) W.budget p κ,
    ∃ ωOuter : Fin 2 → ∀ κ, Quadratic.Advice n n W.budget PG p κ,
    ∀ D : Fin 4 → NUPPT,
      (D 0).RealizesOn (G.mddhEnc (PolyExpr.const 1) (PolyExpr.const 3)) W.coins
        (Linear.red0 G PG (Quadratic.piDim n n) p hp
          (Quadratic.toLinear G n n PG p hp (Q W) φ) (ωPi 0)) →
      (D 1).RealizesOn (G.mddhEnc ℓ (PG.mBound.mul W.budget)) W.coins
        (Linear.red1 G PG (Quadratic.piDim n n) p hp
          (Quadratic.toLinear G n n PG p hp (Q W) φ) (ωPi 1)) →
      (D 2).RealizesOn (G.mddhEnc (PolyExpr.const 1) n) W.coins
        (Quadratic.red2 G n n PG p hp (Q W) (ωOuter 0)) →
      (D 3).RealizesOn (G.mddhEnc (PolyExpr.const 1) n) W.coins
        (Quadratic.red3 G n n PG p hp (Q W) (ωOuter 1)) →
    ∃ η : ∀ i : Fin 4, ∀ κ,
      BilinearGen.MddhAdvice p (Quadratic.hopCols ℓ i)
        (Quadratic.hopRows n n W.budget PG i) κ,
    ∀ B : Fin 4 → NUPPT,
      (∀ i, (B i).RealizesOn G.dlinEnc (D i).coins
        (G.dlinToMddh p hp (Quadratic.hopCols ℓ i)
          (Quadratic.hopRows n n W.budget PG i) (D i) (η i))) →
      ∀ κ, (S).simAdv (wee20Sim_raw G ℓ n d PG) A q κ ≤
        (∑ i : Fin 4, ((Quadratic.hopCols ℓ i).eval κ : ℝ) * G.dlinAdv (B i) κ) +
        Quadratic.quadraticSlack G ℓ p κ := sorry

/-- The specified raw simulator gives negligible advantage under machine-restricted
L2 realisability and shared L1 matrix realisability [Wee20, Section 3.3; GJLS21,
Definition 4.3 for the committed case]. No honest efficiency target is assumed.

**Proof sketch.** Read the raw SASimSecureWith predicate. For its oracle NUPPT, use the
corresponding core inequality to choose advice, then the matching realisability reader
to obtain four machine realisers. Apply mddhAdv_negligible to each fixed machine and
polynomial dimension pair. Sum with the shared Negligible.add/mono API. The one rank
failure is negligible by the published Linear.linearSlack_negligible bound. No new
negligible or subexponential notion, rank-counting formula, or closure result is proved.
-/
theorem wee20PHFE_raw_saSimSecureWith (hPG : PHFE.PGSound PG) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (hpb : ∀ κ, 2 ^ κ ≤ p κ)
    (hR : Wee20RealizableSA G ℓ n d PG p hp)
    (hM : ∀ d' ℓ' : PolyExpr, G.MDDHRealizable p hp d' ℓ')
    (h : G.DLINAssumption) : (S).SASimSecureWith (wee20SASim_raw G ℓ n d PG) := sorry

/-- The specified raw simulator gives negligible advantage under machine-restricted
L2 realisability and shared L1 matrix realisability [Wee20, Section 3.3; GJLS21,
Definition 4.3 for the committed case]. No honest efficiency target is assumed.

**Proof sketch.** Read the raw SimSecureWith predicate. For its machine pair, use the
corresponding core inequality to choose advice, then the matching realisability reader
to obtain four machine realisers. Apply mddhAdv_negligible to each fixed machine and
polynomial dimension pair. Sum with the shared Negligible.add/mono API. The one rank
failure is negligible by the published Linear.linearSlack_negligible bound. No new
negligible or subexponential notion, rank-counting formula, or closure result is proved.
-/
theorem wee20PHFE_raw_simSecureWith (hPG : PHFE.PGSound PG) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (hpb : ∀ κ, 2 ^ κ ≤ p κ)
    (hR : Wee20Realizable43 G ℓ n d PG p hp)
    (hM : ∀ d' ℓ' : PolyExpr, G.MDDHRealizable p hp d' ℓ')
    (h : G.DLINAssumption) : (S).SimSecureWith (wee20Sim_raw G ℓ n d PG) := sorry

/-- The specified raw simulator gives one common positive subexponential exponent under
machine-restricted L2 realisability and shared L1 matrix realisability [Wee20, Section 3.3; GJLS21,
Definition 4.3 for the committed case]. No honest efficiency target is assumed.

**Proof sketch.** Read SubexpDLIN and choose one positive exponent below its common
exponent and one BEFORE the adversary and budget. For each oracle machine and budget,
apply wee20PHFE_saSimAdv_dlin_le. The machine-restricted L2 hypothesis supplies four MDDH
realisers, and hM supplies the subsequent four L1 DLIN realisers. Each DLIN advantage has
the original common exponent; absorb its fixed polynomial factor at the previously
chosen smaller exponent using the shared growth and SubexpSmall APIs. Apply the published
Linear.linearSlack_subexpSmall and mddhSlack_subexpSmall at that same exponent. Sum and
use the shared monotonicity reader. Do not choose an exponent from a per-dimension
existential mddh_subexpHard result, since that would not establish budget uniformity.
-/
theorem wee20PHFE_raw_subexpSASimSecureWith (hPG : PHFE.PGSound PG) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (hpb : ∀ κ, 2 ^ κ ≤ p κ)
    (hR : Wee20RealizableSA G ℓ n d PG p hp)
    (hM : ∀ d' ℓ' : PolyExpr, G.MDDHRealizable p hp d' ℓ')
    (h : G.SubexpDLIN) : (S).SubexpSASimSecureWith (wee20SASim_raw G ℓ n d PG) := sorry

/-- The specified raw simulator gives one common positive subexponential exponent under
machine-restricted L2 realisability and shared L1 matrix realisability [Wee20, Section 3.3; GJLS21,
Definition 4.3 for the committed case]. No honest efficiency target is assumed.

**Proof sketch.** Read SubexpDLIN and choose one positive exponent below its common
exponent and one BEFORE the adversary and budget. For each committed machine pair and key count,
apply wee20PHFE_simAdv_dlin_le. The machine-restricted L2 hypothesis supplies four MDDH
realisers, and hM supplies the subsequent four L1 DLIN realisers. Each DLIN advantage has
the original common exponent; absorb its fixed polynomial factor at the previously
chosen smaller exponent using the shared growth and SubexpSmall APIs. Apply the published
Linear.linearSlack_subexpSmall and mddhSlack_subexpSmall at that same exponent. Sum and
use the shared monotonicity reader. Do not choose an exponent from a per-dimension
existential mddh_subexpHard result, since that would not establish budget uniformity.
-/
theorem wee20PHFE_raw_subexpSimSecureWith (hPG : PHFE.PGSound PG) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (hpb : ∀ κ, 2 ^ κ ≤ p κ)
    (hR : Wee20Realizable43 G ℓ n d PG p hp)
    (hM : ∀ d' ℓ' : PolyExpr, G.MDDHRealizable p hp d' ℓ')
    (h : G.SubexpDLIN) : (S).SubexpSimSecureWith (wee20Sim_raw G ℓ n d PG) := sorry


end

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20
