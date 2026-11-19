/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Fresh
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Reduction
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticCorrect

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The explicit quadratic semi-adaptive security bound

## Main definitions

This module introduces no alternate realisation or efficiency predicate.

## Main results

* `Wee20.Quadratic.derived_run_endpoint`, `game0_game1_le`: the actual derived Π adversary.
* `Wee20.Quadratic.game1_game2_accept`: exact source-group leakage rewrite.
* `Wee20.Quadratic.game2_game3_le`, `game3_game4_le`: the two outer MDDH hops.
* `Wee20.Quadratic.saGame_eq_freshSaGame`: actual fresh stateful raw endpoint laws.
* `Wee20.Quadratic.quadratic_saSimAdv_le`: four explicit realisers and ONE Π rank loss.

The core quantifies over every typed adversary and then every realiser of the displayed
four reductions. It assumes no realisability statement about all typed adversaries.

## References

* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive 2020/1420, §3, main claim, p. 6;
  §3.3, pp. 7–8, Games 0–4; §4; Appendix B, Theorem 1, p. 12 and Appendix B, pp. 12–14.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic

open Complexity TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
open scoped Matrix

/-- The mask advice used by the derived Π adversary has its explicit polynomial word
bound. Fixed-advice bookkeeping.

**Proof sketch.** Read maskAdviceEnc_eq and maskAdviceMeta_eq. Apply the shared pair-length,
modular-vector-length and numeral-length readers; the count is maskCount and the scalar
width is G.wG. Evaluate maskAdviceLen and use the elementary numeral bound already present
in the library. No new scalar encoder or dimension evaluator is introduced. -/
theorem length_maskAdviceEnc_le (G : BilinearGen) (n1 n2 : PolyExpr) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (κ : ℕ) (ω : MaskAdvice n1 n2 p κ) :
    (maskAdviceEnc G n1 n2 p hp κ ω).length ≤ (maskAdviceLen G n1 n2).eval κ := by
  letI : NeZero (p κ) := orderSchedule_neZero G p hp κ
  have hn1 := Turing.length_bits_le_self (n1.eval κ)
  have hn2 := Turing.length_bits_le_self (n2.eval κ)
  rw [Nat.size_eq_bits_len] at hn1 hn2
  rw [maskAdviceEnc_eq, maskAdviceMeta_eq, maskAdviceLen_eq]
  simp only [Turing.length_pairEncode, List.length_replicate, Candidates.length_natToList,
    Encoding.Modular.encodeVector_length, PolyExpr.eval_add, PolyExpr.eval_mul,
    PolyExpr.eval_var, PolyExpr.eval_const]
  omega

/-- The derived adversary's mask advice word is injective. Fixed-advice bookkeeping.

**Proof sketch.** Separate the fixed metadata by pairEncode_injective, then reuse the
published modular-vector encoder injectivity with orderSchedule_neZero and the existing
order_le_two_pow bound. This is the outer vector analogue of Linear.adviceEnc_injective. -/
theorem maskAdviceEnc_injective (G : BilinearGen) (n1 n2 : PolyExpr) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (κ : ℕ) :
    Function.Injective (maskAdviceEnc G n1 n2 p hp κ) := by
  letI : NeZero (p κ) := orderSchedule_neZero G p hp κ
  intro a b h
  have hWidth := orderSchedule_le_two_pow G p hp κ
  simp only [maskAdviceEnc_eq] at h
  exact Encoding.Modular.encodeVector_injective (q := p κ)
    (length := (maskCount n1 n2).eval κ) (G.wG.eval κ) hWidth
    ((pairEncode_eq_iff _ _ _ _).mp h).2

/-- Outer advice encoding is polynomially bounded. Fixed-advice bookkeeping.

**Proof sketch.** Read maskAdviceEnc/adviceEnc and their header readers. Reuse the shared
pair-length, modular-vector-length and numeral-length results, then Linear's corresponding
advice bound. The separate numeric n1,n2 headers require no hardwired polynomial evaluator. -/
theorem length_adviceEnc_le (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 q : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (κ : ℕ) (ω : Advice n1 n2 q PG p κ) :
    (adviceEnc G n1 n2 q PG p hp κ ω).length ≤ (adviceLen G n1 n2 q PG).eval κ := by
  have hMask := length_maskAdviceEnc_le G n1 n2 p hp κ ω.1
  have hLinear := Linear.length_adviceEnc_le G PG (piDim n1 n2) q p hp κ ω.2
  rw [adviceEnc_eq, Turing.length_pairEncode, adviceLen_eq]
  simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
  omega

/-- Full advice encoding is injective. Fixed-advice bookkeeping.

**Proof sketch.** Separate the two components using pairEncode_injective. Use the modular
vector encoder's published injectivity with the shared prime schedule and existing width
bound, and Linear.adviceEnc_injective for the second component. -/
theorem adviceEnc_injective (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 q : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (κ : ℕ) :
    Function.Injective (adviceEnc G n1 n2 q PG p hp κ) := by
  intro a b h
  simp only [adviceEnc_eq] at h
  obtain ⟨hMask, hLinear⟩ := (pairEncode_eq_iff _ _ _ _).mp h
  exact Prod.ext (maskAdviceEnc_injective G n1 n2 p hp κ hMask)
    (Linear.adviceEnc_injective G PG (piDim n1 n2) q p hp κ hLinear)

/-- Left mixed leakage equals the scalar tensor leakage whenever the supplied group
vector is the encoding of a KNOWN scalar vector [Wee20, §3.3, pp. 7–8].

**Proof sketch.** Read crossLeakLeft_eq and value_eq. Reuse the groupDot and exponent
multiplication transport laws and the canonical privateTensor coordinate reader. The
scalar y1 is supplied as a theorem parameter; no algorithm computes it from group y1. -/
theorem crossLeakLeft_known (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (κ : ℕ) (pp : PublicParams G κ) (f : Fn κ pp.orderParam)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (y1 : Fin (n1.eval κ) → ZMod pp.group.order)
    (y2 : Fin (n2.eval κ) → ZMod pp.group.order) (mu : pp.group.G) :
    crossLeakLeft G n1 n2 PG κ pp f x (pp.group.expVec pp.generator y1) y2 mu =
      pp.generator ^ (value G n1 n2 PG κ pp f x y1 y2).val * mu⁻¹ := by
  have hTensor :
      (fun i : Fin (n1.eval κ * n2.eval κ) =>
        pp.group.expVec pp.generator y1 (finProdFinEquiv.symm i).1 ^
          (y2 (finProdFinEquiv.symm i).2).val) =
        pp.group.expVec pp.generator (privateTensor (p := pp.orderParam) y1 y2) := ?_
  swap
  · funext i
    have h := congrFun (pp.group.expVec_tensor_left pp.generator y1 y2)
      (finProdFinEquiv.symm i)
    simpa only [pp.group.expVec_apply, privateTensor_eq, Matrix.kroneckerMap_apply] using h
  rw [crossLeakLeft_eq, hTensor, pp.group.groupDot_expVec, value_eq]

/-- Right mixed leakage equals the scalar tensor leakage for a KNOWN scalar y2
[Wee20, §3.3, pp. 7–8].

**Proof sketch.** Use the same published exponent/tensor laws as crossLeakLeft_known,
with scalar multiplication commuted in the tensor coordinate. No new generic group law
is proved and no scalar is extracted from a group element. -/
theorem crossLeakRight_known (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (κ : ℕ) (pp : PublicParams G κ) (f : Fn κ pp.orderParam)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (y1 : Fin (n1.eval κ) → ZMod pp.group.order)
    (y2 : Fin (n2.eval κ) → ZMod pp.group.order) (mu : pp.group.G) :
    crossLeakRight G n1 n2 PG κ pp f x y1 (pp.group.expVec pp.generator y2) mu =
      pp.generator ^ (value G n1 n2 PG κ pp f x y1 y2).val * mu⁻¹ := by
  have hTensor :
      (fun i : Fin (n1.eval κ * n2.eval κ) =>
        pp.group.expVec pp.generator y2 (finProdFinEquiv.symm i).2 ^
          (y1 (finProdFinEquiv.symm i).1).val) =
        pp.group.expVec pp.generator (privateTensor (p := pp.orderParam) y1 y2) := ?_
  swap
  · funext i
    have h := congrFun (pp.group.expVec_tensor_right pp.generator y1 y2)
      (finProdFinEquiv.symm i)
    simpa only [pp.group.expVec_apply, privateTensor_eq, Matrix.kroneckerMap_apply] using h
  rw [crossLeakRight_eq, hTensor, pp.group.groupDot_expVec, value_eq]

/-- The pure derived adversary exactly reproduces the honest or Π-simulated outer
endpoint for every fixed tape and coin string [Wee20, §3.3, Game 0 to Game 1, p. 7].

**Proof sketch.** Use the shared runDet successor/zero readers and replayLinear's cases.
Relate histories by wrapLinearCT/wrapLinearKey; challenge queries use the known scalar
signal, whose group encoding agrees with signalGroup by signalGroup_exp. Key queries use
the same fixed public M. Both handlers refuse pre-challenge keys and repeated challenges,
and both count total calls identically. Induct along the common bounded interpreter;
malformed-history defaults never occur on related reachable histories. Ideal leakage is
Linear.leak of the supplied scalar signal by definition. No probability argument or basis
condition is used in this pointwise identity. -/
theorem derived_run_endpoint (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (A : SAAdv G n1 n2 PG)
    (φ : ∀ κ, MaskAdvice n1 n2 p κ) (ideal : Bool) (κ : ℕ) (pp : PublicParams G κ)
    (ω : Linear.SecurityDraw G PG (piDim n1 n2) A.budget κ pp) (r : List Bool) :
    runGameDet G n1 n2 PG A (if ideal then 1 else 0) κ pp
      (maskAdviceDraw G n1 n2 p hp κ pp (φ κ), ω) r =
    Linear.runGameDet G PG (piDim n1 n2) (toLinear G n1 n2 PG p hp A φ)
      (if ideal then 5 else 0) false κ pp ω r := sorry

/-- Fixing only outer scalar masks gives an explicit derived Π adversary whose ACTUAL
fresh-law simulation advantage bounds the first outer hop [Wee20, §3.3, pp. 7–8].

**Proof sketch.** Couple the padded deterministic endpoints by derived_run_endpoint.
Transport the common outer draw to the fixed-prime advice type by ringEquivCongr. Apply
abs_expect_sub_le_expect and the existing exists_expect_sample_le to select one mask tape
at each parameter, before choosing any realiser. Use Linear.saSimAdv_eq_freshSaSimAdv to
obtain the actual fresh raw Π advantage. This keeps all coins and the TOTAL budget. -/
theorem game0_game1_le (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (A : SAAdv G n1 n2 PG) :
    ∃ φ : ∀ κ, MaskAdvice n1 n2 p κ, ∀ κ,
      advantage (game G n1 n2 PG A 0 κ) (game G n1 n2 PG A 1 κ) ≤
        Linear.freshSaSimAdv G PG (piDim n1 n2) (toLinear G n1 n2 PG p hp A φ) κ := sorry

/-- Equation (5) rewrites the actual source-group signal leakage without changing any
transcript [Wee20, §3.1, (5), p. 6; §3.3, Game 1 to Game 2, p. 7].

**Proof sketch.** Apply the existing tensor/mixing identity from QuadraticCorrect to the
known sampled A1,A2,s1,s2,z1,z2. Read group leakage through Linear.leak_eq and reuse
mixGroup_exp and exponent transport. The resulting source-group value equals crossLeak.
Couple adaptive key calls pointwise using the shared relational simulation reader. -/
theorem game1_game2_accept (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (A : SAAdv G n1 n2 PG) (κ : ℕ) :
    accept (game G n1 n2 PG A 1 κ) = accept (game G n1 n2 PG A 2 κ) := sorry

/-- One MDDH¹_{2,n1} realiser bounds the first outer mask replacement
[Wee20, §3.3, Game 2 to Game 3, p. 8].

**Proof sketch.** In red2 the challenge base is GROUP A1 and the response plus z1 is GROUP
y1. Known advice supplies scalar A2,s2 and Π setup/key coins, so every later adaptive
cross-term query is computed by crossLeakLeft, without unknown scalar multiplication.
The real response gives the honest y1; the random response remains uniform after adding
the challenge chosen from the fixed public history (Equiv.addRight). Couple the typed
protocols, fix the remaining finite scalar tape by the shared averaging lemma, and
transfer every realiser's verdict with RealizesOn.distinguisherL_eq. No rank term occurs. -/
theorem game2_game3_le (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (A : SAAdv G n1 n2 PG) :
    ∃ ω : ∀ κ, Advice n1 n2 A.budget PG p κ, ∀ D : NUPPT,
      D.RealizesOn (G.mddhEnc (PolyExpr.const 1) n1) A.coins (red2 G n1 n2 PG p hp A ω) →
      ∀ κ, advantage (game G n1 n2 PG A 2 κ) (game G n1 n2 PG A 3 κ) ≤
        G.mddhAdv (PolyExpr.const 1) n1 D κ := sorry

/-- One MDDH¹_{2,n2} realiser bounds the second outer mask replacement
[Wee20, §3.3, Game 3 to Game 4, p. 8].

**Proof sketch.** Red3 knows the already-uniform scalar y1 as advice and receives GROUP
A2,y2 from the challenge. Use crossLeakRight for every adaptive key. Translate the
independent random response by the selected z2 through Equiv.addRight, couple the exact
protocols, fix advice by averaging, and apply the shared realiser verdict reader.
The ideal Π setup is total, including singular H, so no further bad event is introduced. -/
theorem game3_game4_le (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (A : SAAdv G n1 n2 PG) :
    ∃ ω : ∀ κ, Advice n1 n2 A.budget PG p κ, ∀ D : NUPPT,
      D.RealizesOn (G.mddhEnc (PolyExpr.const 1) n2) A.coins (red3 G n1 n2 PG p hp A ω) →
      ∀ κ, advantage (game G n1 n2 PG A 3 κ) (game G n1 n2 PG A 4 κ) ≤
        G.mddhAdv (PolyExpr.const 1) n2 D κ := sorry

/-- The two padded outer endpoints have the acceptance laws of the ACTUAL fresh raw
setup/encryption/key generation and stateful simulator [Wee20, §3.1–§3.2, pp. 6–7].

**Proof sketch.** Read all honest/simulator core-plus-draw laws. Reindex disjoint outer
mask coordinates to actual A1,A2,s1,s2 or fresh y1,y2 draws, discarding unused blocks.
For adaptive key randomness reuse the same coordinate restriction and Games.Tapes route
as Linear.saGame_eq_freshSaGame, using mCount_le_mBound for each function. Relate the ideal
state to its stored y1,y2 after the accepted challenge; before it, every key is refused.
Use the published runDet/buildComp bridge and relational state-abstraction theorem, then
average public parameters and adversary coins. Neither side adds a rank filter. -/
theorem saGame_eq_freshSaGame (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (A : SAAdv G n1 n2 PG) (ideal : Bool) (κ : ℕ) :
    accept (saGame G n1 n2 PG A ideal κ) =
      accept (freshSaGame G n1 n2 PG A ideal κ) := sorry

/-- The actual fresh and padded outer advantages coincide [Wee20, §3.3, pp. 7–8].

**Proof sketch.** Substitute both endpoint acceptance equalities into the shared
advantage/acceptance reader after reading the two named advantage definitions. -/
theorem saSimAdv_eq_freshSaSimAdv (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (A : SAAdv G n1 n2 PG) (κ : ℕ) :
    saSimAdv G n1 n2 PG A κ = freshSaSimAdv G n1 n2 PG A κ := sorry

/-- For every typed outer adversary, fixed scalar advice makes EVERY four realising
machines satisfy the explicit ACTUAL raw semi-adaptive simulation bound
[Wee20, §3, p. 6, main security claim with §3.3, pp. 7–8 and Appendix B, Theorem 1].
The single statistical term is Π's exact unconditioned-basis failure probability.

**Proof sketch.** Fix outer masks for game0_game1_le, then apply
Linear.linear_freshSaSimAdv_le to that one explicit derived adversary, choosing its two
advice families. Independently choose the two outer computational-hop advice families.
Use game1_game2_accept and the shared triangle inequality for the five actual games.
Transfer the endpoints to the actual fresh laws. All four realisers are quantified after
these choices; toLinear_coins/toLinear_budget preserve their layouts exactly. Retain the
one Linear.linearSlack from Π; the two outer MDDH replacements add no rank loss. -/
theorem quadratic_saSimAdv_le (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
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
      ∀ κ, freshSaSimAdv G n1 n2 PG A κ ≤
        G.mddhAdv (PolyExpr.const 1) (PolyExpr.const 3) (D 0) κ +
        G.mddhAdv ℓ (PG.mBound.mul A.budget) (D 1) κ +
        G.mddhAdv (PolyExpr.const 1) n1 (D 2) κ + G.mddhAdv (PolyExpr.const 1) n2 (D 3) κ +
        Linear.linearSlack G κ := sorry

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic
