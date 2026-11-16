/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.SequentialZK.ComputationalReduction
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Typed advantage of the one-phase reduction

## Main definitions

This module introduces no definitions or computational hosts.

## Main results

* `distAdv_phaseReduction`: the reduction's exact raw activation equation identifies its
  advantage with the typed independent phase-table and final-distinguisher coin experiment.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 175.1.
-/

namespace TCSlib.Cryptography.SequentialZK

open Complexity

/-- For fixed machines `S,D,Red`, phase polynomials `k,B,Q`, orientation `verifierFirst`,
parameter `n`, and metadata `x,z,rV,j,pre`, suppose `Red` has coins `Q*S.coins+D.coins` and
its raw activation normalizes the candidate, simulates the suffix, and then invokes `D`.
For any raw-output samplers `X,Y`, its distinguishing advantage equals that of the typed
experiment with independent coins `(Fin (Q.eval n) → S.Coins n) × D.Coins n`, flattened by
`FunFamily.blocks.symm` for the suffix. No metadata validity or witness premise is needed.
[PS10, Theorem 175.1, one-phase computational hybrid reduction].

**Proof sketch.**
First read the reduction's exact coin polynomial at the fixed parameter.
Its numerical coin length is the sum of the simulator-table and distinguisher lengths.
The canonical block equivalence flattens the independent simulator table.
The published `coinsEquiv` then concatenates it with the distinguisher coins.
Their composition is a bijection from the typed independent coins to `Red.Coins n`.
The published take reader identifies the entire simulator-table tape.
The published drop reader identifies the independent final-distinguisher tape.
These equations require no positivity of either coin length or the number of phases.
Read both machine distinguishers through their published verdict equations.
Read their typed activations through the public `runAt_eq` equation.
Apply the assumed exact raw activation equation to every candidate word and tape.
The two tape readers identify that verdict with the claimed typed local experiment.
Reindex acceptance probabilities along the constructed bijection for sampler `X`.
Do the same independently for sampler `Y`.
Finally read the absolute acceptance gap through `distAdv_def` and substitute both
probability equalities. The sample spaces may differ and need only be finite. -/
theorem distAdv_phaseReduction {σ τ : Type*} [Fintype σ] [Fintype τ]
    (S D Red : NUPPT) (k B Q : PolyExpr) (verifierFirst : Bool) (n : ℕ)
    (x z rV : List Bool) (j : ℕ) (pre : List (List Bool))
    (hcoins : Red.coins = .add (.mul Q S.coins) D.coins)
    (hrun : ∀ raw r, Red.runAtL n raw r = D.runAtL n
      (phaseContinuation S k B Q verifierFirst x z rV j pre raw
        (r.take ((PolyExpr.mul Q S.coins).eval n)))
      (r.drop ((PolyExpr.mul Q S.coins).eval n)))
    (X : σ → List Bool) (Y : τ → List Bool) :
    distAdv X Y (Red.distinguisherL n) =
      distAdv X Y (fun raw (c : (Fin (Q.eval n) → S.Coins n) × D.Coins n) =>
        D.distinguisherL n
          (phaseContinuation S k B Q verifierFirst x z rV j pre raw
            (List.ofFn ((FunFamily.blocks (Q.eval n) (S.coinLen n)).symm c.1))) c.2) := by
  -- The published coin readers identify the canonical independent product space.
  have hlen : Red.coinLen n = Q.eval n * S.coinLen n + D.coinLen n := by
    rw [NUPPT.coinLen_eq, hcoins, PolyExpr.eval_add, PolyExpr.eval_mul,
      NUPPT.coinLen_eq, NUPPT.coinLen_eq]
  let e : ((Fin (Q.eval n) → S.Coins n) × D.Coins n) ≃ Red.Coins n :=
    ((FunFamily.blocks (Q.eval n) (S.coinLen n)).symm.prodCongr
      (Equiv.refl (D.Coins n))).trans (EnsembleLemmas.coinsEquiv hlen)
  -- Expand the local equivalence before evaluating the scalar coin cut.
  have he (c : (Fin (Q.eval n) → S.Coins n) × D.Coins n) :
      e c = EnsembleLemmas.coinsEquiv hlen
        (((FunFamily.blocks (Q.eval n) (S.coinLen n)).symm c.1), c.2) := by
    rcases c with ⟨cS, cD⟩
    simp only [e, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply]
  have hcut : (PolyExpr.mul Q S.coins).eval n = Q.eval n * S.coinLen n := by
    rw [PolyExpr.eval_mul, NUPPT.coinLen_eq]
  have htake (c : (Fin (Q.eval n) → S.Coins n) × D.Coins n) :
      (List.ofFn (e c)).take ((PolyExpr.mul Q S.coins).eval n) =
        List.ofFn ((FunFamily.blocks (Q.eval n) (S.coinLen n)).symm c.1) := by
    rw [he, hcut]
    exact EnsembleLemmas.take_ofFn_coinsEquiv hlen
      (((FunFamily.blocks (Q.eval n) (S.coinLen n)).symm c.1), c.2)
  have hdrop (c : (Fin (Q.eval n) → S.Coins n) × D.Coins n) :
      (List.ofFn (e c)).drop ((PolyExpr.mul Q S.coins).eval n) = List.ofFn c.2 := by
    rw [he, hcut]
    exact EnsembleLemmas.drop_ofFn_coinsEquiv hlen
      (((FunFamily.blocks (Q.eval n) (S.coinLen n)).symm c.1), c.2)
  -- Compare the exact verdicts, then reindex each acceptance probability.
  have key (raw : List Bool) (c : (Fin (Q.eval n) → S.Coins n) × D.Coins n) :
      Red.distinguisherL n raw (e c) = D.distinguisherL n
        (phaseContinuation S k B Q verifierFirst x z rV j pre raw
          (List.ofFn ((FunFamily.blocks (Q.eval n) (S.coinLen n)).symm c.1))) c.2 := by
    rw [NUPPT.distinguisherL_eq, NUPPT.distinguisherL_eq, NUPPT.runAt_eq,
      NUPPT.runAt_eq, hrun, htake, hdrop]
  have hX := EnsembleLemmas.acceptProb_coins_equiv e X (Red.distinguisherL n)
  have hY := EnsembleLemmas.acceptProb_coins_equiv e Y (Red.distinguisherL n)
  simp only [key] at hX hY
  rw [distAdv_def, distAdv_def, ← hX, ← hY]

end TCSlib.Cryptography.SequentialZK
