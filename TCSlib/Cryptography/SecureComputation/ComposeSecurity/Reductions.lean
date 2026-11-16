/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Complexity.Randomized.Closure

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machines with advice-dependent pre- and post-processing and extra coins

Two closure properties of non-uniform PPT machines used by the simulators and reductions of the
composition theorem [Gol04, §7.3.1, proof of Theorem 7.3.3]: a machine may hand its argument,
together with an advice string and a block of extra coins, to a polynomial-time pre-processor
before running another machine (`ComposeSim.exists_pre`: a reduction `D ∘ Ψ`), or post-process
another machine's output with an advice string and extra coins (`ComposeSim.exists_post`: a
simulator that runs a simulator and then completes its output). Both combine the closure
catalogue of `Complexity/Randomized/Closure.lean` (`exists_split`, `exists_withAdvice`,
`exists_seq`) in one raw function of the layout (`NUPPT.ofPolyTime`).

## Main results

* `ComposeSim.exists_pre`, `ComposeSim.exists_post`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §2.1 (closure of non-uniform PPT machines under composition, Definition 26.8).
-/

namespace TCSlib.Cryptography.SecureComputation.ComposeSim

open Complexity Turing Complexity.NUPPT

/-- **Pre-processing with advice and extra coins**: for an `NUPPT` `D`, a polynomial-time `Ψ`, a
polynomially bounded advice family `α` and a coin polynomial `p`, there is an `NUPPT` `B` with
coins `p + D.coins` such that `B(1^n, y; r) = D(1^n, Ψ ⟨⟨1^n, α n⟩, ⟨y, r_{<p(n)}⟩⟩; r_{≥p(n)})`.

**Proof sketch.** Advice `⟨D.advice n, α n⟩`; the raw function reads `1^n`, the argument, the two
advice halves and the coins from the layout (`inParam`, `inArg`, `inAdvice`, `inCoins`), cuts the
coins at `p(n)` (`polyTimeComputable_pairTakePoly`, `polyTimeComputable_pairDropPoly`), applies
`Ψ` and runs `D.output` (`NUPPT.polyTimeComputable_output`); the equation is `runAtL_ofPolyTime`
with the projection identities. -/
theorem exists_pre (D : NUPPT) {Ψ : List Bool → List Bool} (hΨ : PolyTimeComputable Ψ)
    (α : ℕ → List Bool) (a : PolyExpr) (hα : ∀ n, (α n).length ≤ a.eval n) (p : PolyExpr) :
    ∃ B : NUPPT, B.coins = .add p D.coins ∧ ∀ n y r, B.runAtL n y r =
      D.runAtL n (Ψ (pairEncode (pairEncode (List.replicate n true) (α n))
        (pairEncode y (r.take (p.eval n))))) (r.drop (p.eval n)) := by
  have hcut := polyTimeComputable_inParam.pairEncode polyTimeComputable_inCoins
  have hpre := hΨ.comp' ((polyTimeComputable_inParam.pairEncode
      (polyTimeComputable_pairSndD.comp' polyTimeComputable_inAdvice)).pairEncode
    (polyTimeComputable_inArg.pairEncode ((polyTimeComputable_pairTakePoly p).comp' hcut)))
  have hF := D.polyTimeComputable_output.comp' (polyTimeComputable_layout polyTimeComputable_inParam
    hpre (polyTimeComputable_pairFstD.comp' polyTimeComputable_inAdvice)
    ((polyTimeComputable_pairDropPoly p).comp' hcut))
  have hadv : ∀ n, (pairEncode (D.advice n) (α n)).length ≤
      (PolyExpr.add (.add (.mul (.const 2) D.adv) (.const 2)) a).eval n := fun n => by
    rw [length_pairEncode]
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    have h₁ := D.advice_length n
    have h₂ := hα n
    omega
  refine ⟨ofPolyTime hF (.add p D.coins) _ (fun n => pairEncode (D.advice n) (α n)) hadv,
    coins_ofPolyTime _ _ _ _ _, fun n y r => ?_⟩
  rw [runAtL_ofPolyTime, runAtL_eq_output_layout]
  simp only [advInput_eq, ← layout_eq, inParam_layout, inArg_layout, inAdvice_layout,
    inCoins_layout, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]

/-- **Post-processing with advice and extra coins**: for an `NUPPT` `A`, a polynomial-time `Ψ`,
a polynomially bounded advice family `α` and a coin polynomial `p`, there is an `NUPPT` `B` with
coins `A.coins + p` such that
`B(1^n, y; r) = Ψ ⟨⟨1^n, α n⟩, ⟨A(1^n, y; r_{<A.coins(n)}), r_{≥A.coins(n)}⟩⟩`.

**Proof sketch.** Advice `⟨A.advice n, α n⟩`; the raw function cuts the coins at `A.coins(n)`,
runs `A.output` on the layout with the first advice half and the head of the coins, and applies
`Ψ` to the parameter, the second advice half, `A`'s output and the tail of the coins
(`runAtL_ofPolyTime` with the projection identities). -/
theorem exists_post (A : NUPPT) {Ψ : List Bool → List Bool} (hΨ : PolyTimeComputable Ψ)
    (α : ℕ → List Bool) (a : PolyExpr) (hα : ∀ n, (α n).length ≤ a.eval n) (p : PolyExpr) :
    ∃ B : NUPPT, B.coins = .add A.coins p ∧ ∀ n y r, B.runAtL n y r =
      Ψ (pairEncode (pairEncode (List.replicate n true) (α n))
        (pairEncode (A.runAtL n y (r.take (A.coinLen n))) (r.drop (A.coinLen n)))) := by
  have hcut := polyTimeComputable_inParam.pairEncode polyTimeComputable_inCoins
  have hout := A.polyTimeComputable_output.comp' (polyTimeComputable_layout
    polyTimeComputable_inParam polyTimeComputable_inArg
    (polyTimeComputable_pairFstD.comp' polyTimeComputable_inAdvice)
    ((polyTimeComputable_pairTakePoly A.coins).comp' hcut))
  have hF := hΨ.comp' ((polyTimeComputable_inParam.pairEncode
      (polyTimeComputable_pairSndD.comp' polyTimeComputable_inAdvice)).pairEncode
    (hout.pairEncode ((polyTimeComputable_pairDropPoly A.coins).comp' hcut)))
  have hadv : ∀ n, (pairEncode (A.advice n) (α n)).length ≤
      (PolyExpr.add (.add (.mul (.const 2) A.adv) (.const 2)) a).eval n := fun n => by
    rw [length_pairEncode]
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    have h₁ := A.advice_length n
    have h₂ := hα n
    omega
  refine ⟨ofPolyTime hF (.add A.coins p) _ (fun n => pairEncode (A.advice n) (α n)) hadv,
    coins_ofPolyTime _ _ _ _ _, fun n y r => ?_⟩
  rw [runAtL_ofPolyTime, runAtL_eq_output_layout, coinLen_eq]
  simp only [advInput_eq, ← layout_eq, inParam_layout, inArg_layout, inAdvice_layout,
    inCoins_layout, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]

end TCSlib.Cryptography.SecureComputation.ComposeSim
