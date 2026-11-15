/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.SequentialZK.SuffixLaws
import TCSlib.Cryptography.Composability.SequentialZK.ComputationalReduction
import TCSlib.Cryptography.Pseudorandom.Indistinguishability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Acceptance potentials for simulated continuations

## Main definitions

* `continuationProb` is the acceptance probability after the remaining normalized phases.

## Main results

* `acceptProb_prod` averages acceptance over the first sampler-seed coordinate.
* `acceptProb_update_tuple` specializes the published uniform-coordinate replacement law.
* `continuationProb_bellman` separates a fresh normalized simulator call from its suffix.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 175.1 (sequential repetition of zero knowledge).
-/

namespace TCSlib.Cryptography.SequentialZK

open Complexity

/-- Acceptance over sampler seeds `A×B` is the average over `a:A` of acceptance over `B`. -/
theorem acceptProb_prod {A B O C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (F : A × B → O) (D : O → C → Bool) :
    acceptProb F D = uexp (fun a => acceptProb (fun b => F (a, b)) D) := by
  rw [acceptProb_def, ← uprob_comp_equiv (Equiv.prodAssoc A B C).symm, uprob_prod]
  rfl

/-- Replacing coordinate `i` of a uniform tuple by an independent uniform value leaves
acceptance unchanged: `Pr[D(F(update table i fresh))] = Pr[D(F table)]`. -/
theorem acceptProb_update_tuple {I A O C : Type*} [DecidableEq I] [Fintype I]
    [Fintype A] [Nonempty A] [Fintype C] (i : I) (F : (I → A) → O)
    (D : O → C → Bool) :
    acceptProb (fun r : A × (I → A) => F (Function.update r.2 i r.1)) D =
      acceptProb F D := by
  have hupdate := acceptProb_update (τ := Unit) i (fun table _ => F table) D
  have hleft :
      acceptProb (fun r : (A × (I → A)) × Unit =>
        F (Function.update r.1.2 i r.1.1)) D =
      acceptProb (fun r : A × ((I → A) × Unit) =>
        F (Function.update r.2.1 i r.1)) D :=
    acceptProb_comp_equiv (Equiv.prodAssoc A (I → A) Unit)
      (fun r : A × ((I → A) × Unit) => F (Function.update r.2.1 i r.1)) D
  rw [acceptProb_fst] at hleft
  exact hleft.trans (hupdate.trans (acceptProb_fst F D))

/-- If `post (raw (a,z)) b = F a b` and `Z` is nonempty, post-processing `raw` with fresh
`B` coins and applying `D` has acceptance `E_a[acceptProb (F a) D]`. -/
theorem acceptProb_postprocess_fst {A Z B Raw O C : Type*}
    [Fintype A] [Fintype Z] [Nonempty Z] [Fintype B] [Fintype C]
    (raw : A × Z → Raw) (post : Raw → B → O) (F : A → B → O)
    (hpoint : ∀ a z b, post (raw (a, z)) b = F a b) (D : O → C → Bool) :
    acceptProb raw (fun out (r : B × C) => D (post out r.1) r.2) =
      uexp (fun a => acceptProb (F a) D) := by
  rw [acceptProb_bind, acceptProb_prod]
  have hfunctions : (fun r : A × Z => acceptProb (fun b => post (raw r) b) D) =
      (fun r : A × Z => acceptProb (F r.1) D) := by
    funext r
    congr 1
    funext b
    exact hpoint r.1 r.2 b
  rw [hfunctions, HardcoreBit.uexp_fst]

/-- `continuationProb … D i pre` is acceptance by `D` after simulating phases
`i,…,Q(|x|)-1` from `pre`, with an independent full table of `Q(|x|)` simulator tapes.
Only the suffix's own blocks are used. [PS10, Theorem 175.1, hybrid continuation potential].
-/
noncomputable def continuationProb {C : Type*} [Fintype C]
    (S : NUPPT) (k B Q : PolyExpr) (verifierFirst : Bool) (x z rV : List Bool)
    (D : List Bool → C → Bool) (i : ℕ) (pre : List (List Bool)) : ℝ :=
  acceptProb (fun coins : Fin (Q.eval x.length) → S.Coins x.length =>
    View.encode ⟨x, z, rV, phaseSuffix S k B verifierFirst x z rV
      (List.ofFn ((FunFamily.blocks (Q.eval x.length) (S.coinLen x.length)).symm coins))
      i pre (Q.eval x.length - i)⟩) D

/-- The defining equation of `continuationProb` is the acceptance of the canonical view
whose message list is the remaining `phaseSuffix`, sampled from the full typed coin table. -/
theorem continuationProb_eq {C : Type*} [Fintype C]
    (S : NUPPT) (k B Q : PolyExpr) (verifierFirst : Bool) (x z rV : List Bool)
    (D : List Bool → C → Bool) (i : ℕ) (pre : List (List Bool)) :
    continuationProb S k B Q verifierFirst x z rV D i pre =
      acceptProb (fun coins : Fin (Q.eval x.length) → S.Coins x.length =>
        View.encode ⟨x, z, rV, phaseSuffix S k B verifierFirst x z rV
          (List.ofFn ((FunFamily.blocks (Q.eval x.length) (S.coinLen x.length)).symm coins))
          i pre (Q.eval x.length - i)⟩) D := rfl

/-- For `i<Q(|x|)`, the continuation potential equals acceptance after one fresh typed
simulator update at `i`, then the remaining suffix on an independent full simulator table.

**Proof sketch.** Reseed table entry `i` independently using the published uniform-update
law. The front-step suffix reader makes that entry the current normalized update. Every
later suffix block has index greater than `i`, so overwriting entry `i` leaves the remaining
suffix unchanged. The resulting sampler is the desired independent current coin and suffix.
-/
theorem continuationProb_bellman {C : Type*} [Fintype C]
    (S : NUPPT) (k B Q : PolyExpr) (verifierFirst : Bool) (x z rV : List Bool)
    (D : List Bool → C → Bool) (i : ℕ) (hi : i < Q.eval x.length)
    (pre : List (List Bool)) :
    continuationProb S k B Q verifierFirst x z rV D i pre =
      acceptProb (fun r : S.Coins x.length × (Fin (Q.eval x.length) → S.Coins x.length) =>
        View.encode ⟨x, z, rV, phaseSuffix S k B verifierFirst x z rV
          (List.ofFn ((FunFamily.blocks (Q.eval x.length) (S.coinLen x.length)).symm r.2))
          (i + 1)
          (simStep S x z rV (k.eval x.length) (B.eval x.length)
            (if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2)
            i pre r.1) (Q.eval x.length - (i + 1))⟩) D := by
  let F : (Fin (Q.eval x.length) → S.Coins x.length) → List Bool := fun coins =>
    View.encode ⟨x, z, rV, phaseSuffix S k B verifierFirst x z rV
      (List.ofFn ((FunFamily.blocks (Q.eval x.length) (S.coinLen x.length)).symm coins))
      i pre (Q.eval x.length - i)⟩
  have hupdate := acceptProb_update_tuple (⟨i, hi⟩ : Fin (Q.eval x.length)) F D
  have hpoint (r : S.Coins x.length × (Fin (Q.eval x.length) → S.Coins x.length)) :
      F (Function.update r.2 ⟨i, hi⟩ r.1) =
        View.encode ⟨x, z, rV, phaseSuffix S k B verifierFirst x z rV
          (List.ofFn ((FunFamily.blocks (Q.eval x.length) (S.coinLen x.length)).symm r.2))
          (i + 1)
          (simStep S x z rV (k.eval x.length) (B.eval x.length)
            (if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2)
            i pre r.1) (Q.eval x.length - (i + 1))⟩ := by
    have hblock := FunFamily.ofFn_blocks (Q.eval x.length) (S.coinLen x.length)
      ((FunFamily.blocks (Q.eval x.length) (S.coinLen x.length)).symm
        (Function.update r.2 ⟨i, hi⟩ r.1)) ⟨i, hi⟩
    rw [Equiv.apply_symm_apply, Function.update_same] at hblock
    have hcoin : coinBlock (S.coinLen x.length) i
        (List.ofFn ((FunFamily.blocks (Q.eval x.length) (S.coinLen x.length)).symm
          (Function.update r.2 ⟨i, hi⟩ r.1))) = List.ofFn r.1 :=
      (coinBlock_eq _ _ _).trans hblock.symm
    dsimp only [F]
    rw [show Q.eval x.length - i = (Q.eval x.length - (i + 1)) + 1 by omega,
      phaseSuffix_front, phaseStep_eq_simStep S k B verifierFirst x z rV _ i pre r.1 hcoin,
      phaseSuffix_update_before S k B verifierFirst x z rV (Q.eval x.length) r.2
        ⟨i, hi⟩ r.1 (i + 1) _ (Q.eval x.length - (i + 1)) (by omega) (by omega)]
  rw [continuationProb_eq]
  exact hupdate.symm.trans (congrArg (fun sampler => acceptProb sampler D) (funext hpoint))

end TCSlib.Cryptography.SequentialZK
