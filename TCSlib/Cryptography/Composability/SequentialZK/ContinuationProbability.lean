/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.SequentialZK.SuffixLaws
import TCSlib.Cryptography.Composability.SequentialZK.ComputationalReduction
import TCSlib.Cryptography.Composability.SequentialZK.NormalizedStep
import TCSlib.Cryptography.Composability.SequentialZK.PaddedProverSpec
import TCSlib.Cryptography.Pseudorandom.Indistinguishability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Acceptance potentials for simulated continuations

## Main definitions

* `continuationProb` is the acceptance probability after the remaining normalized phases.
* `phaseGap` is the local raw real-view/simulator gap through the normalized continuation.

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

/-- Acceptance over sampler seeds `A×B` is the average over `a:A` of acceptance over `B`.
`acceptProb F D = uexp (fun a => acceptProb (fun b => F (a, b)) D)`. -/
theorem acceptProb_prod {A B O C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (F : A × B → O) (D : O → C → Bool) :
    acceptProb F D = uexp (fun a => acceptProb (fun b => F (a, b)) D) := by
  rw [acceptProb_def, ← uprob_comp_equiv (Equiv.prodAssoc A B C).symm, uprob_prod]
  simp only [acceptProb_def, Equiv.prodAssoc_symm_apply]

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
  rw [acceptProb_fst (τ := Unit)
    (fun r : A × (I → A) => F (Function.update r.2 i r.1)) D] at hleft
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
  rw [hfunctions]
  exact HardcoreBit.uexp_fst (β := Z) (fun a : A => acceptProb (F a) D)

/-- `continuationProb … D i pre` is acceptance by `D` after simulating phases
`i,…,Q(|x|)-1` from `pre`, with an independent full table of `Q(|x|)` simulator tapes.
Only the suffix's own blocks are used. [PS10, Theorem 175.1, hybrid continuation potential].
`continuationProb S k B Q verifierFirst x z rV D i pre = acceptProb (fun coins : Fin (Q.eval
x.length) → S.Coins x.length => View.encode ⟨x, z, rV, phaseSuffix S k B verifierFirst x z rV
(List.ofFn ((FunFamily.blocks (Q.eval x.length) …`.
-/
noncomputable def continuationProb {C : Type*} [Fintype C]
    (S : NUPPT) (k B Q : PolyExpr) (verifierFirst : Bool) (x z rV : List Bool)
    (D : List Bool → C → Bool) (i : ℕ) (pre : List (List Bool)) : ℝ :=
  acceptProb (fun coins : Fin (Q.eval x.length) → S.Coins x.length =>
    View.encode ⟨x, z, rV, phaseSuffix S k B verifierFirst x z rV
      (List.ofFn ((FunFamily.blocks (Q.eval x.length) (S.coinLen x.length)).symm coins))
      i pre (Q.eval x.length - i)⟩) D

/-- The defining equation of `continuationProb` is the acceptance of the canonical view
whose message list is the remaining `phaseSuffix`, sampled from the full typed coin table.
`continuationProb S k B Q verifierFirst x z rV D i pre = acceptProb (fun coins : Fin (Q.eval
x.length) → S.Coins x.length => View.encode ⟨x, z, rV, phaseSuffix S k B verifierFirst x z rV
(List.ofFn ((FunFamily.blocks (Q.eval x.length) …`. -/
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
  -- Independently reseed the current table entry without changing its uniform law.
  have hupdate := acceptProb_update_tuple (⟨i, hi⟩ : Fin (Q.eval x.length)) F D
  -- Separate that entry as the current update; all future blocks ignore the overwrite.
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
    rw [Equiv.apply_symm_apply, Function.update_self] at hblock
    have hcoin : coinBlock (S.coinLen x.length) i
        (List.ofFn ((FunFamily.blocks (Q.eval x.length) (S.coinLen x.length)).symm
          (Function.update r.2 ⟨i, hi⟩ r.1))) = List.ofFn r.1 :=
      (coinBlock_eq _ _ _).trans hblock.symm
    dsimp only [F]
    rw [show Q.eval x.length - i = (Q.eval x.length - (i + 1)) + 1 by omega,
      phaseSuffix_front, phaseStep_eq_simStep S k B verifierFirst x z rV _ i pre r.1 hcoin,
      phaseSuffix_update_before S k B verifierFirst x z rV (Q.eval x.length) r.2
        ⟨i, hi⟩ r.1 (i + 1) _ (Q.eval x.length - (i + 1))
        (by change i < i + 1; omega) (by omega)]
  rw [continuationProb_eq]
  exact hupdate.symm.trans (congrArg (fun sampler => acceptProb sampler D) (funext hpoint))

/-- For a bounded honest prover and padded-prover specification `d`, the raw original
phase view, normalized and passed to `phaseContinuation`, has acceptance equal to the
average next continuation potential of `realStep`. The wrapper's zero verifier coins
are removed through the public uniform-product laws.
`acceptProb (fun r : (π.withV (phaseVerifier V)).ExecCoins (π.withV (phaseVerifier V)).P x =>
((π.withV (phaseVerifier V)).viewV x y (phaseAux z rV i pre) r).encode) (fun raw (r : (Fin (Q.eval
x.length) → S.Coins x.length) × C) => D …`.

**Proof sketch.** The published real-view fixed point identifies normalized messages with
the original phase's verifier history. The specification supplies its exact message count;
the caller supplies the uniform prover-message bound. The continuation then starts from
exactly `realStep`. Its value is independent of the wrapper's zero-bit verifier tape, so
averaging and projecting that factor leaves the expectation over the original prover coins.
-/
theorem continuationProb_real {C : Type*} [Fintype C] {π ρ : Protocol}
    (S : NUPPT) (B Q : PolyExpr) {x : List Bool} {p : ℕ}
    (d : PaddedProverSpec π ρ x (Q.eval x.length) p) (V : Strategy)
    (y z rV : List Bool) (D : List Bool → C → Bool)
    (hp : p = if π.verifierFirst then π.rounds.eval x.length / 2
      else (π.rounds.eval x.length + 1) / 2)
    (hbound : ∀ r hist, (π.P.next x y r hist).length ≤ B.eval x.length)
    (i : ℕ) (pre : List (List Bool)) :
    acceptProb
      (fun r : (π.withV (phaseVerifier V)).ExecCoins (π.withV (phaseVerifier V)).P x =>
        ((π.withV (phaseVerifier V)).viewV x y (phaseAux z rV i pre) r).encode)
      (fun raw (r : (Fin (Q.eval x.length) → S.Coins x.length) × C) =>
        D (phaseContinuation S π.rounds B Q π.verifierFirst x z rV i pre raw
          (List.ofFn ((FunFamily.blocks (Q.eval x.length) (S.coinLen x.length)).symm r.1)))
          r.2) =
      uexp (fun coin : π.P.Coins x.length =>
        continuationProb S π.rounds B Q π.verifierFirst x z rV D (i + 1)
          (realStep π V x y z rV p i pre coin)) := by
  let aux := phaseAux z rV i pre
  -- Build the seed conversion from public field readers, without reducing `withV`.
  let eP : π.P.Coins x.length ≃ (π.withV (phaseVerifier V)).P.Coins x.length :=
    Equiv.arrowCongr (finCongr (by rw [Protocol.withV_P])) (Equiv.refl Bool)
  let eV := (π.withV_vCoinsEquiv (phaseVerifier V) x.length).symm
  let e : π.P.Coins x.length × (phaseVerifier V).Coins x.length ≃
      (π.withV (phaseVerifier V)).ExecCoins (π.withV (phaseVerifier V)).P x :=
    eP.prodCongr eV
  have heP (a : π.P.Coins x.length) (v : (phaseVerifier V).Coins x.length) :
      List.ofFn (e (a, v)).1 = List.ofFn a := by
    change List.ofFn (eP a) = List.ofFn a
    exact (List.ofFn_congr (show π.P.coinLen x.length =
      (π.withV (phaseVerifier V)).P.coinLen x.length by rw [Protocol.withV_P]) a).symm
  have heV (a : π.P.Coins x.length) (v : (phaseVerifier V).Coins x.length) :
      List.ofFn (e (a, v)).2 = List.ofFn v := by
    change List.ofFn (eV v) = List.ofFn v
    have hv := π.withV_vCoinsEquiv_ofFn (phaseVerifier V) x.length
      ((π.withV_vCoinsEquiv (phaseVerifier V) x.length).symm v)
    rw [Equiv.apply_symm_apply] at hv
    exact hv.symm
  let raw : π.P.Coins x.length × (phaseVerifier V).Coins x.length → List Bool :=
    fun r => ((π.withV (phaseVerifier V)).viewV x y aux (e r)).encode
  have hraw (a : π.P.Coins x.length) (v : (phaseVerifier V).Coins x.length) :
      raw (a, v) =
        View.encode ⟨x, aux, List.ofFn v,
          (exec π.P (phaseVerifier V) π.verifierFirst x y aux (List.ofFn a)
            (List.ofFn v) (π.rounds.eval x.length)).2⟩ := by
    dsimp only [raw]
    rw [Protocol.viewV_withV, heP a v, heV a v]
  -- Normalize at the converted actual seed, then read both tapes through their equations.
  have hfixed (a : π.P.Coins x.length) (v : (phaseVerifier V).Coins x.length) :
      normalizePhaseMsgs x aux p (B.eval x.length)
          (View.encode ⟨x, aux, List.ofFn v,
            (exec π.P (phaseVerifier V) π.verifierFirst x y aux (List.ofFn a)
              (List.ofFn v) (π.rounds.eval x.length)).2⟩) =
        (exec π.P (phaseVerifier V) π.verifierFirst x y aux (List.ofFn a) []
          (π.rounds.eval x.length)).2 := by
    have hc : (π.withV (phaseVerifier V)).V.coinLen x.length = 0 := by
      rw [Protocol.withV_V, phaseVerifier_coinLen]
    have hb : ∀ r hist,
        ((π.withV (phaseVerifier V)).P.next x y r hist).length ≤ B.eval x.length := by
      simpa only [Protocol.withV_P] using hbound
    have hn (rP : List Bool) :
        (exec (π.withV (phaseVerifier V)).P (π.withV (phaseVerifier V)).V
          (π.withV (phaseVerifier V)).verifierFirst x y aux rP []
          ((π.withV (phaseVerifier V)).rounds.eval x.length)).2.length = p := by
      simp only [Protocol.withV_P, Protocol.withV_V, Protocol.withV_verifierFirst,
        Protocol.withV_rounds]
      exact d.original_count (phaseVerifier V) y aux rP []
    have hf := normalizePhaseMsgs_viewV (π.withV (phaseVerifier V)) x y aux p
      (B.eval x.length) hc hb hn (e (a, v))
    change normalizePhaseMsgs x aux p (B.eval x.length) (raw (a, v)) = _ at hf
    rw [hraw a v, heP a v] at hf
    simpa only [Protocol.withV_P, Protocol.withV_V, Protocol.withV_verifierFirst,
      Protocol.withV_rounds] using hf
  let post := fun out (coins : Fin (Q.eval x.length) → S.Coins x.length) =>
    phaseContinuation S π.rounds B Q π.verifierFirst x z rV i pre out
      (List.ofFn ((FunFamily.blocks (Q.eval x.length) (S.coinLen x.length)).symm coins))
  let F := fun (a : π.P.Coins x.length)
      (coins : Fin (Q.eval x.length) → S.Coins x.length) =>
    View.encode ⟨x, z, rV, phaseSuffix S π.rounds B π.verifierFirst x z rV
      (List.ofFn ((FunFamily.blocks (Q.eval x.length) (S.coinLen x.length)).symm coins))
      (i + 1) (realStep π V x y z rV p i pre a) (Q.eval x.length - (i + 1))⟩
  have hpoint (a : π.P.Coins x.length) (v : (phaseVerifier V).Coins x.length)
      (coins : Fin (Q.eval x.length) → S.Coins x.length) : post (raw (a, v)) coins =
      F a coins := by
    dsimp only [post, F]
    rw [phaseContinuation_eq, realStep_eq]
    dsimp only
    rw [← hp, hraw a v, hfixed a v]
  -- Reindex the actual execution law before removing the unused wrapper-tape factor.
  have hindex := acceptProb_comp_equiv e
    (fun r : (π.withV (phaseVerifier V)).ExecCoins (π.withV (phaseVerifier V)).P x =>
      ((π.withV (phaseVerifier V)).viewV x y aux r).encode)
    (fun out (r : (Fin (Q.eval x.length) → S.Coins x.length) × C) => D (post out r.1) r.2)
  have hreal := acceptProb_postprocess_fst raw post F hpoint D
  simpa only [continuationProb_eq] using hindex.symm.trans hreal

/-- For `i<Q(|x|)`, the simulated raw phase passed to `phaseContinuation` has acceptance
exactly `continuationProb … i pre`, with an independent full table of suffix coins.

**Proof sketch.** Move the independent suffix coins into the simulated sampler. The
published continuation equation is exactly one typed normalized simulator step followed
by the remaining suffix. The Bellman reader identifies this sampler's acceptance with
the original continuation potential. -/
theorem continuationProb_sim {C : Type*} [Fintype C]
    (S : NUPPT) (k B Q : PolyExpr) (verifierFirst : Bool) (x z rV : List Bool)
    (D : List Bool → C → Bool) (i : ℕ) (hi : i < Q.eval x.length)
    (pre : List (List Bool)) :
    acceptProb (S.simulate x (phaseAux z rV i pre))
      (fun raw (r : (Fin (Q.eval x.length) → S.Coins x.length) × C) =>
        D (phaseContinuation S k B Q verifierFirst x z rV i pre raw
          (List.ofFn ((FunFamily.blocks (Q.eval x.length) (S.coinLen x.length)).symm r.1)))
          r.2) = continuationProb S k B Q verifierFirst x z rV D i pre := by
  -- Expose the fresh simulator coin and the independent full suffix table.
  rw [acceptProb_bind (S.simulate x (phaseAux z rV i pre))
    (fun raw (coins : Fin (Q.eval x.length) → S.Coins x.length) =>
      phaseContinuation S k B Q verifierFirst x z rV i pre raw
        (List.ofFn ((FunFamily.blocks (Q.eval x.length) (S.coinLen x.length)).symm coins))) D]
  let F := fun r : S.Coins x.length × (Fin (Q.eval x.length) → S.Coins x.length) =>
    View.encode ⟨x, z, rV, phaseSuffix S k B verifierFirst x z rV
      (List.ofFn ((FunFamily.blocks (Q.eval x.length) (S.coinLen x.length)).symm r.2))
      (i + 1)
      (simStep S x z rV (k.eval x.length) (B.eval x.length)
        (if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2)
        i pre r.1) (Q.eval x.length - (i + 1))⟩
  have hpoint :
      (fun r : S.Coins x.length × (Fin (Q.eval x.length) → S.Coins x.length) =>
        phaseContinuation S k B Q verifierFirst x z rV i pre
          (S.simulate x (phaseAux z rV i pre) r.1)
          (List.ofFn ((FunFamily.blocks (Q.eval x.length) (S.coinLen x.length)).symm r.2))) =
        F := by
    funext r
    dsimp only [F]
    rw [phaseContinuation_eq, simStep_eq]
  rw [hpoint]
  exact (continuationProb_bellman S k B Q verifierFirst x z rV D i hi pre).symm

/-- The local raw-view gap at `i,pre`: original `π.P` against the fixed-tape phase verifier
versus `S.simulate`, tested by the normalized `phaseContinuation` with independent full
simulator-table coins and `D` coins. The witness `y` appears only in the mathematical real
sampler. [PS10, Theorem 175.1, one-phase hybrid gap].
`phaseGap π V S B Q x y z rV D i pre = distAdv (fun r : (π.withV (phaseVerifier V)).ExecCoins
(π.withV (phaseVerifier V)).P x => ((π.withV (phaseVerifier V)).viewV x y (phaseAux z rV i pre)
r).encode) (S.simulate x (phaseAux z rV i pre)) …`. -/
noncomputable def phaseGap {C : Type*} [Fintype C] (π : Protocol) (V : Strategy)
    (S : NUPPT) (B Q : PolyExpr) (x y z rV : List Bool) (D : List Bool → C → Bool)
    (i : ℕ) (pre : List (List Bool)) : ℝ :=
  distAdv
    (fun r : (π.withV (phaseVerifier V)).ExecCoins (π.withV (phaseVerifier V)).P x =>
      ((π.withV (phaseVerifier V)).viewV x y (phaseAux z rV i pre) r).encode)
    (S.simulate x (phaseAux z rV i pre))
    (fun raw (r : (Fin (Q.eval x.length) → S.Coins x.length) × C) =>
      D (phaseContinuation S π.rounds B Q π.verifierFirst x z rV i pre raw
        (List.ofFn ((FunFamily.blocks (Q.eval x.length) (S.coinLen x.length)).symm r.1))) r.2)

/-- The defining equation of `phaseGap` is the displayed raw real-view/simulator
`distAdv` after `phaseContinuation`, using a full independent typed simulator table.
`phaseGap π V S B Q x y z rV D i pre = distAdv (fun r : (π.withV (phaseVerifier V)).ExecCoins
(π.withV (phaseVerifier V)).P x => ((π.withV (phaseVerifier V)).viewV x y (phaseAux z rV i pre)
r).encode) (S.simulate x (phaseAux z rV i pre)) …`. -/
theorem phaseGap_eq {C : Type*} [Fintype C] (π : Protocol) (V : Strategy)
    (S : NUPPT) (B Q : PolyExpr) (x y z rV : List Bool) (D : List Bool → C → Bool)
    (i : ℕ) (pre : List (List Bool)) :
    phaseGap π V S B Q x y z rV D i pre =
      distAdv
        (fun r : (π.withV (phaseVerifier V)).ExecCoins (π.withV (phaseVerifier V)).P x =>
          ((π.withV (phaseVerifier V)).viewV x y (phaseAux z rV i pre) r).encode)
        (S.simulate x (phaseAux z rV i pre))
        (fun raw (r : (Fin (Q.eval x.length) → S.Coins x.length) × C) =>
          D (phaseContinuation S π.rounds B Q π.verifierFirst x z rV i pre raw
            (List.ofFn ((FunFamily.blocks (Q.eval x.length) (S.coinLen x.length)).symm r.1)))
            r.2) := rfl

/-- For a bounded real prover, the local raw-view gap `phaseGap` is exactly the absolute
drift of `continuationProb` under the real next phase, for `i<Q(|x|)`. -/
theorem phaseGap_eq_drift {C : Type*} [Fintype C] {π ρ : Protocol}
    (S : NUPPT) (B Q : PolyExpr) {x : List Bool} {p : ℕ}
    (d : PaddedProverSpec π ρ x (Q.eval x.length) p) (V : Strategy)
    (y z rV : List Bool) (D : List Bool → C → Bool)
    (hp : p = if π.verifierFirst then π.rounds.eval x.length / 2
      else (π.rounds.eval x.length + 1) / 2)
    (hbound : ∀ r hist, (π.P.next x y r hist).length ≤ B.eval x.length)
    (i : ℕ) (hi : i < Q.eval x.length) (pre : List (List Bool)) :
    phaseGap π V S B Q x y z rV D i pre =
      |uexp (fun coin : π.P.Coins x.length =>
        continuationProb S π.rounds B Q π.verifierFirst x z rV D (i + 1)
          (realStep π V x y z rV p i pre coin)) -
        continuationProb S π.rounds B Q π.verifierFirst x z rV D i pre| := by
  rw [phaseGap_eq, distAdv_def,
    continuationProb_real S B Q d V y z rV D hp hbound i pre,
    continuationProb_sim S π.rounds B Q π.verifierFirst x z rV D i hi pre]

end TCSlib.Cryptography.SequentialZK
