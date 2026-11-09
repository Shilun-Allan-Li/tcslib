/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.Closure
import TCSlib.Complexity.Randomized.Repetition
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.OneWayFunctions.Basic
import Mathlib.Logic.Equiv.Fin.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Predictor support for trapdoor encryption

This module develops the predictor used for the security of Algorithm 104.3.
It gives the predictor's polynomial-time machine, coin split and probability identity.

## Main definitions

* `TCSlib.Cryptography.tdpPredFun` computes the predictor's output from a
  distinguisher verdict and its extra coin.
* `TCSlib.Cryptography.tdpPredictor` is the predictor machine and
  `TCSlib.Cryptography.predCoins` is its coin bijection.

## Main results

* `TCSlib.Cryptography.tdpPredictor_runAtL` gives the machine's run equation.
* `TCSlib.Cryptography.uprob_tdpPredictor` gives the probability identity used in
  the prediction lemma. `TCSlib.Cryptography.uexp_half_add` and
  `TCSlib.Cryptography.uexp_half_sub` evaluate the corresponding averages.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Theorem 104.4.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Theorem 3.2 (the predictor from a distinguisher).
-/

namespace TCSlib.Cryptography

open Complexity Turing

/-! ## The predictor machine of Theorem 104.4 -/

/-- The raw function of the predictor `A_flip` of [PS10, Theorem 104.4, proof] on the layout
`⟨⟨⟨1^n, ⟨i, y⟩⟩, α⟩, c :: ρ⟩`: run `D` on `⟨1^n, ⟨i, ⟨y, [c]⟩⟩⟩` with advice `α` and coins `ρ`,
and output `[c ⊕ ¬verdict ⊕ flip]` (`c` if `D` accepts, `1 − c` otherwise, negated when `flip`). -/
def tdpPredFun (D : NUPPT) (flip : Bool) (z : List Bool) : List Bool :=
  [xor (xor ((NUPPT.inCoins z).headD false)
    (!decide (D.output (NUPPT.layout (NUPPT.inParam z)
      (pairEncode (pairFstD (NUPPT.inArg z))
        (pairEncode (pairSndD (NUPPT.inArg z)) [(NUPPT.inCoins z).headD false]))
      (NUPPT.inAdvice z) (NUPPT.inCoins z).tail) = [true]))) flip]

/-- The raw predictor is polynomial-time (`polyTimeComputable_headD`, `Complexity.polyTimeComputable_tail`,
`polyTimeComputable_pairEq` for the verdict,
`BinArith.polyTimeComputable_xor`/`polyTimeComputable_not`).

**Proof sketch.** The first coin `c` is the head of the coin projection; `D` runs on the
layout with argument `⟨fst y, ⟨snd y, [c]⟩⟩`, the advice and the remaining coins (the tail,
`polyTimeComputable_tail` through `List.drop_one`), which is `D.polyTimeComputable_output`
after `NUPPT.polyTimeComputable_layout`; the verdict `[D's output = [true]]` is
`polyTimeComputable_pairEq`; the output `c ⊕ ¬verdict ⊕ flip` is two
`BinArith.polyTimeComputable_xor` with `polyTimeComputable_not` and a constant. -/
theorem tdpPredFun_poly (D : NUPPT) (flip : Bool) : PolyTimeComputable (tdpPredFun D flip) := by
  have hc : PolyTimeComputable fun z => [(NUPPT.inCoins z).headD false] :=
    polyTimeComputable_headD.comp NUPPT.polyTimeComputable_inCoins
  have hout := D.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
    NUPPT.polyTimeComputable_inParam
    ((polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg).pairEncode
      ((polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg).pairEncode hc))
    NUPPT.polyTimeComputable_inAdvice
      ((polyTimeComputable_tail.congr fun _ => List.drop_one).comp
        NUPPT.polyTimeComputable_inCoins))
  have hv : PolyTimeComputable fun z => [decide (D.output (NUPPT.layout (NUPPT.inParam z)
      (pairEncode (pairFstD (NUPPT.inArg z))
        (pairEncode (pairSndD (NUPPT.inArg z)) [(NUPPT.inCoins z).headD false]))
      (NUPPT.inAdvice z) (NUPPT.inCoins z).tail) = [true])] := by
    convert polyTimeComputable_pairEq.comp (hout.pairEncode (polyTimeComputable_const [true]))
      using 1
    funext z
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  exact BinArith.polyTimeComputable_xor (BinArith.polyTimeComputable_xor hc
      (polyTimeComputable_not hv))
    (polyTimeComputable_const [flip])

/-- **The predictor machine** `A_flip` of [PS10, Theorem 104.4, proof]: `D`'s advice, coins
`1 + D.coins` (the extra bit `c` first). -/
noncomputable def tdpPredictor (D : NUPPT) (flip : Bool) : NUPPT :=
  NUPPT.ofPolyTime (tdpPredFun_poly D flip) (.add (.const 1) D.coins) D.adv D.advice
    D.advice_length

/-- The coin polynomial of the predictor machine. -/
@[simp] theorem tdpPredictor_coins (D : NUPPT) (flip : Bool) :
    (tdpPredictor D flip).coins = .add (.const 1) D.coins := by
  unfold tdpPredictor
  exact NUPPT.coins_ofPolyTime _ _ _ _ _

/-- The coin count of the predictor machine: `1 + |D's coins at n|`. -/
theorem tdpPredictor_coinLen (D : NUPPT) (n : ℕ) :
    1 + D.coinLen n = (PolyExpr.add (.const 1) D.coins).eval n := by
  rw [NUPPT.coinLen_eq, PolyExpr.eval_add, PolyExpr.eval_const]

/-- Unfolding of the predictor machine: on `⟨i, y⟩` with coins `c :: ρ` it outputs
`[c ⊕ ¬[D(1^n, ⟨i, ⟨y, [c]⟩⟩; ρ) = 1] ⊕ flip]`. -/
theorem tdpPredictor_runAtL (D : NUPPT) (flip : Bool) (n : ℕ) (i y : List Bool) (c : Bool)
    (ρ : List Bool) :
    (tdpPredictor D flip).runAtL n (pairEncode i y) (c :: ρ) =
      [xor (xor c (!decide (D.runAtL n (pairEncode i (pairEncode y [c])) ρ = [true]))) flip] := by
  unfold tdpPredictor
  rw [NUPPT.runAtL_ofPolyTime]
  simp [tdpPredFun, NUPPT.inCoins_eq, NUPPT.inParam_eq, NUPPT.inArg_eq, NUPPT.inAdvice_eq,
      NUPPT.advInput_eq,
    NUPPT.layout_eq, NUPPT.runAtL_eq]

/-- The coins of the predictor machine: the bit `c` followed by the coins of `D`. -/
noncomputable def predCoins (D : NUPPT) (flip : Bool) (n : ℕ) :
    Bool × D.Coins n ≃ (tdpPredictor D flip).Coins n :=
  ((Equiv.funUnique (Fin 1) Bool).symm.prodCongr (Equiv.refl _)).trans
    ((Fin.appendEquiv 1 (D.coinLen n)).trans
      ((Equiv.arrowCongr (finCongr (tdpPredictor_coinLen D n)) (Equiv.refl Bool)).trans
        (NUPPT.coinsEquivPoly (tdpPredictor_coins D flip) n).symm))

/-- The coin string of `predCoins (c, ρ)` is `c :: ρ`. -/
theorem ofFn_predCoins (D : NUPPT) (flip : Bool) (n : ℕ) (c : Bool) (ρ : D.Coins n) :
    List.ofFn (predCoins D flip n (c, ρ)) = c :: List.ofFn ρ := by
  unfold predCoins
  rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply, NUPPT.coinsEquivPoly_symm_ofFn]
  refine (List.ofFn_congr (tdpPredictor_coinLen D n) (Fin.appendEquiv 1 (D.coinLen n)
    (((Equiv.funUnique (Fin 1) Bool).symm.prodCongr (Equiv.refl (D.Coins n))) (c, ρ)))).symm.trans
    ?_
  exact (List.ofFn_fin_append _ _).trans rfl

/-- `if v then c else ¬c` is `c ⊕ ¬v`. -/
theorem ite_eq_xor_not (v c : Bool) : (if v = true then c else !c) = xor c (!v) := by
  cases v <;> cases c <;> rfl

/-- The verdict convention on a one-bit output: `[b] = [true]` iff `b`. -/
theorem decide_singleton_eq_true (b : Bool) : decide ([b] = [true]) = b := by
  cases b <;> rfl

/-- **The prediction experiment of the predictor machine** is the concrete predictor
experiment: over uniform `x` and the coins `c :: ρ`, `A_flip(1^n, ⟨i, enc (f x)⟩) = h x` has the
probability that `(if D(⟨i, ⟨enc (f x), [c]⟩⟩; ρ) then c else ¬c) ⊕ flip = h x`
(`uprob_comp_equiv` along `predCoins`, `tdpPredictor_runAtL`). -/
theorem uprob_tdpPredictor {α : Type*} [Fintype α] (D : NUPPT) (flip : Bool) (n : ℕ)
    (i : List Bool) (f : α → α) (h : α → Bool) (enc : α → List Bool) :
    uprob (fun z : α × (tdpPredictor D flip).Coins n =>
        (tdpPredictor D flip).distinguisherL n (pairEncode i (enc (f z.1))) z.2 = h z.1) =
      uprob (fun z : α × (Bool × D.Coins n) =>
        xor (if D.distinguisherL n (pairEncode i (pairEncode (enc (f z.1)) [z.2.1])) z.2.2
          then z.2.1 else !z.2.1) flip = h z.1) := by
  rw [← uprob_comp_equiv ((Equiv.refl α).prodCongr (predCoins D flip n))]
  congr 1
  funext z
  obtain ⟨x, c, ρ⟩ := z
  simp only [Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply, NUPPT.distinguisherL_eq,
    NUPPT.runAt_eq, ofFn_predCoins, tdpPredictor_runAtL, decide_singleton_eq_true, ite_eq_xor_not]

/-! ## Averages -/

/-- The average of `1/2 + (a − b)/2` is `1/2 + (E a − E b)/2` (`OneWay.uexp_add`,
`OneWay.uexp_const_mul`, `HardcoreBit.uexp_sub`). -/
theorem uexp_half_add {κ : Type*} [Fintype κ] [Nonempty κ] (a b : κ → ℝ) :
    uexp (fun r => 1 / 2 + (a r - b r) / 2) = 1 / 2 + (uexp a - uexp b) / 2 := by
  have e : (fun r => 1 / 2 + (a r - b r) / 2) = fun r => 1 / 2 + (1 / 2) * (a r - b r) := by
    funext r; ring
  rw [e, OneWay.uexp_add, OneWay.uexp_const, OneWay.uexp_const_mul, HardcoreBit.uexp_sub]
  ring

/-- The average of `1/2 − (a − b)/2` is `1/2 − (E a − E b)/2`. -/
theorem uexp_half_sub {κ : Type*} [Fintype κ] [Nonempty κ] (a b : κ → ℝ) :
    uexp (fun r => 1 / 2 - (a r - b r) / 2) = 1 / 2 - (uexp a - uexp b) / 2 := by
  have e : (fun r => 1 / 2 - (a r - b r) / 2) = fun r => 1 / 2 + (b r - a r) / 2 := by
    funext r; ring
  rw [e, uexp_half_add]
  ring

end TCSlib.Cryptography
