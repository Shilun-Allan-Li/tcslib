/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.SequentialZK.ContinuationProbability
import TCSlib.Cryptography.Composability.SequentialZK.HybridRecursion
import TCSlib.Cryptography.Composability.SequentialZK.EndpointSampling

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Computational prefix hybrids and actual-view endpoint transfer

## Main definitions

This module introduces no definitions.

## Main results

* `prefix_distAdv_le` converts local raw-view continuation gaps into a `Q(|x|)*ε` bound.
* `prefix_distAdv_joint_le` averages this bound over the verifier's independent tape.
* `distAdv_view_endpoints` reindexes typed joint prefixes as actual real/simulator views.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 175.1 (sequential repetition of zero knowledge).
-/

namespace TCSlib.Cryptography.SequentialZK

open Complexity

/-- At fixed verifier tape `rV`, suppose every actual real prefix before phase `i<Q(|x|)`
has `phaseGap … i pre ≤ ε`, where `0≤ε`. For a bounded honest prover and the padded-prover
contract, the canonical real and simulated prefix views have distinguishing advantage at
most `Q(|x|)*ε`. No metadata validity or finite witness assumption appears in this theorem.
[PS10, Theorem 175.1, conditional computational hybrid argument].

**Proof sketch.** Use suffix acceptance as the continuation potential. Its drift under
one real step is exactly the raw-view gap by the published real/simulated continuation
identities. The generic conditional hybrid bound gives `Q(|x|)*ε`. At the final phase the
suffix is empty, so averaging the potential is acceptance of the real prefix. At phase
zero the suffix starts from the empty history and is exactly the typed simulated prefix.
-/
theorem prefix_distAdv_le {C : Type*} [Fintype C] {π ρ : Protocol}
    (S : NUPPT) (B Q : PolyExpr) {x : List Bool} {p : ℕ}
    (d : PaddedProverSpec π ρ x (Q.eval x.length) p) (V : Strategy)
    (y z rV : List Bool) (D : List Bool → C → Bool)
    (hp : p = if π.verifierFirst then π.rounds.eval x.length / 2
      else (π.rounds.eval x.length + 1) / 2)
    (hbound : ∀ r hist, (π.P.next x y r hist).length ≤ B.eval x.length)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hlocal : ∀ i < Q.eval x.length, ∀ coins : Fin i → π.P.Coins x.length,
      phaseGap π V S B Q x y z rV D i
        (realPrefix π V x y z rV p i coins) ≤ ε) :
    distAdv
      (fun coins : Fin (Q.eval x.length) → π.P.Coins x.length =>
        View.encode ⟨x, z, rV, realPrefix π V x y z rV p (Q.eval x.length) coins⟩)
      (fun coins : Fin (Q.eval x.length) → S.Coins x.length =>
        View.encode ⟨x, z, rV, simPrefix S x z rV (π.rounds.eval x.length)
          (B.eval x.length) p (Q.eval x.length) coins⟩) D ≤
      (Q.eval x.length : ℝ) * ε := by
  -- At the final phase the suffix is empty, so the potential is real-prefix acceptance.
  let realView := fun coins : Fin (Q.eval x.length) → π.P.Coins x.length =>
    View.encode ⟨x, z, rV, realPrefix π V x y z rV p (Q.eval x.length) coins⟩
  have hfinal :
      uexp (fun coins : Fin (Q.eval x.length) → π.P.Coins x.length =>
        continuationProb S π.rounds B Q π.verifierFirst x z rV D (Q.eval x.length)
          (realPrefix π V x y z rV p (Q.eval x.length) coins)) =
        acceptProb realView D := by
    have hinner (coins : Fin (Q.eval x.length) → π.P.Coins x.length) :
        continuationProb S π.rounds B Q π.verifierFirst x z rV D (Q.eval x.length)
            (realPrefix π V x y z rV p (Q.eval x.length) coins) =
          acceptProb (fun _ : Fin (Q.eval x.length) → S.Coins x.length => realView coins) D := by
      rw [continuationProb_eq, Nat.sub_self]
      simp only [phaseSuffix_zero]
      rfl
    have hmean := congrArg (fun f : (Fin (Q.eval x.length) → π.P.Coins x.length) → ℝ =>
      uexp f) (funext hinner)
    have havg := acceptProb_prod
      (fun r : (Fin (Q.eval x.length) → π.P.Coins x.length) ×
        (Fin (Q.eval x.length) → S.Coins x.length) => realView r.1) D
    rw [acceptProb_fst realView D] at havg
    exact hmean.trans havg.symm
  -- At phase zero the same suffix is the complete simulated prefix.
  have hinitial : continuationProb S π.rounds B Q π.verifierFirst x z rV D 0 [] =
      acceptProb
        (fun coins : Fin (Q.eval x.length) → S.Coins x.length =>
          View.encode ⟨x, z, rV, simPrefix S x z rV (π.rounds.eval x.length)
            (B.eval x.length) p (Q.eval x.length) coins⟩) D := by
    rw [continuationProb_eq, Nat.sub_zero]
    congr 1
    funext coins
    rw [phaseSuffix_zero_nil, hp]
    have hprefix := simPrefix_eq_phasePrefix S π.rounds B π.verifierFirst x z rV
      (List.ofFn ((FunFamily.blocks (Q.eval x.length) (S.coinLen x.length)).symm coins))
      (Q.eval x.length) coins (fun i => by
        have hb := FunFamily.ofFn_blocks (Q.eval x.length) (S.coinLen x.length)
          ((FunFamily.blocks (Q.eval x.length) (S.coinLen x.length)).symm coins) i
        rw [Equiv.apply_symm_apply] at hb
        exact (coinBlock_eq _ _ _).trans hb.symm)
    rw [hprefix]
  -- Average the local raw-view gaps and apply the published conditional hybrid theorem.
  have hgap := hybrid_recursion_gap_le
    (fun i => realPrefix π V x y z rV p i) ([] : List (List Bool))
    (realStep π V x y z rV p)
    (fun r => realPrefix_zero π V x y z rV p r)
    (fun i r a => realPrefix_snoc π V x y z rV p i r a)
    (continuationProb S π.rounds B Q π.verifierFirst x z rV D)
    (Q.eval x.length) ε hε (fun i hi coins => by
      rw [← phaseGap_eq_drift S B Q d V y z rV D hp hbound i hi
        (realPrefix π V x y z rV p i coins)]
      exact hlocal i hi coins)
  rw [hfinal, hinitial] at hgap
  simpa only [distAdv_def] using hgap

/-- If the fixed-verifier-tape local gaps satisfy the same bound for every verifier tape,
the joint canonical real/simulated prefix views have advantage at most `Q(|x|)*ε`.
[PS10, Theorem 175.1, averaging the verifier tape].
`distAdv (fun r : V.Coins x.length × (Fin (Q.eval x.length) → π.P.Coins x.length) => View.encode ⟨x,
z, List.ofFn r.1, realPrefix π V x y z (List.ofFn r.1) p (Q.eval x.length) r.2⟩) (fun r : V.Coins
x.length × (Fin (Q.eval x.length) → …`. -/
theorem prefix_distAdv_joint_le {C : Type*} [Fintype C] {π ρ : Protocol}
    (S : NUPPT) (B Q : PolyExpr) {x : List Bool} {p : ℕ}
    (d : PaddedProverSpec π ρ x (Q.eval x.length) p) (V : Strategy)
    (y z : List Bool) (D : List Bool → C → Bool)
    (hp : p = if π.verifierFirst then π.rounds.eval x.length / 2
      else (π.rounds.eval x.length + 1) / 2)
    (hbound : ∀ r hist, (π.P.next x y r hist).length ≤ B.eval x.length)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hlocal : ∀ rV : V.Coins x.length, ∀ i < Q.eval x.length,
      ∀ coins : Fin i → π.P.Coins x.length,
      phaseGap π V S B Q x y z (List.ofFn rV) D i
        (realPrefix π V x y z (List.ofFn rV) p i coins) ≤ ε) :
    distAdv
      (fun r : V.Coins x.length × (Fin (Q.eval x.length) → π.P.Coins x.length) =>
        View.encode ⟨x, z, List.ofFn r.1,
          realPrefix π V x y z (List.ofFn r.1) p (Q.eval x.length) r.2⟩)
      (fun r : V.Coins x.length × (Fin (Q.eval x.length) → S.Coins x.length) =>
        View.encode ⟨x, z, List.ofFn r.1,
          simPrefix S x z (List.ofFn r.1) (π.rounds.eval x.length)
            (B.eval x.length) p (Q.eval x.length) r.2⟩) D ≤
      (Q.eval x.length : ℝ) * ε := by
  rw [distAdv_def, acceptProb_prod, acceptProb_prod]
  apply abs_uexp_sub_le (mul_nonneg (Nat.cast_nonneg _) hε)
  intro rV
  simpa only [distAdv_def] using
    prefix_distAdv_le S B Q d V y z (List.ofFn rV) D hp hbound ε hε (hlocal rV)

/-- Reindexing two samplers by equivalences and supplied pointwise endpoint readers
preserves the distinguishing advantage of any fixed `D`.
`distAdv F' G' D = distAdv F G D`. -/
theorem distAdv_reindex {A B A' B' O C : Type*}
    [Fintype A] [Fintype B] [Fintype A'] [Fintype B'] [Fintype C]
    (F : A → O) (G : B → O) (F' : A' → O) (G' : B' → O) (D : O → C → Bool)
    (eA : A' ≃ A) (eB : B' ≃ B)
    (hF : ∀ a, F' a = F (eA a)) (hG : ∀ b, G' b = G (eB b)) :
    distAdv F' G' D = distAdv F G D := by
  have hleft : acceptProb F' D = acceptProb F D :=
    (congrArg (fun sampler => acceptProb sampler D) (funext hF)).trans
      (acceptProb_comp_equiv eA F D)
  have hright : acceptProb G' D = acceptProb G D :=
    (congrArg (fun sampler => acceptProb sampler D) (funext hG)).trans
      (acceptProb_comp_equiv eB G D)
  rw [distAdv_def, distAdv_def, hleft, hright]

/-- The actual encoded repeated view and `SQ.simulate` have exactly the advantage of the
joint typed real/simulated prefix views, assuming their published padded-prover and raw
simulator endpoint equations. [PS10, Theorem 175.1, computational endpoint transfer].
`distAdv (fun r => ((ρ.withV V).viewV x y z r).encode) (SQ.simulate x z) D = distAdv (fun r :
V.Coins x.length × (Fin q → π.P.Coins x.length) => View.encode ⟨x, z, List.ofFn r.1, realPrefix π V
x y z (List.ofFn r.1) p q r.2⟩) (fun r : …`. -/
theorem distAdv_view_endpoints {C : Type*} [Fintype C] {π ρ : Protocol}
    {x : List Bool} {q p : ℕ} (d : PaddedProverSpec π ρ x q p) (V : Strategy)
    (y z : List Bool) (S SQ : NUPPT) (B : PolyExpr)
    (hp : p = if π.verifierFirst then π.rounds.eval x.length / 2
      else (π.rounds.eval x.length + 1) / 2)
    (hlen : SQ.coinLen x.length = V.coinLen x.length + q * S.coinLen x.length)
    (hsim : ∀ r : SQ.Coins x.length, SQ.simulate x z r =
      View.encode ⟨x, z, (List.ofFn r).take (V.coinLen x.length),
        phasePrefix S π.rounds B π.verifierFirst x z
          ((List.ofFn r).take (V.coinLen x.length))
          ((List.ofFn r).drop (V.coinLen x.length)) q⟩) (D : List Bool → C → Bool) :
    distAdv (fun r => ((ρ.withV V).viewV x y z r).encode) (SQ.simulate x z) D =
      distAdv
        (fun r : V.Coins x.length × (Fin q → π.P.Coins x.length) =>
          View.encode ⟨x, z, List.ofFn r.1,
            realPrefix π V x y z (List.ofFn r.1) p q r.2⟩)
        (fun r : V.Coins x.length × (Fin q → S.Coins x.length) =>
          View.encode ⟨x, z, List.ofFn r.1,
            simPrefix S x z (List.ofFn r.1) (π.rounds.eval x.length)
              (B.eval x.length) p q r.2⟩) D := by
  apply distAdv_reindex _ _ _ _ D (d.realCoinsEquiv V)
    (coinBlocksEquiv (V.coinLen x.length) q (S.coinLen x.length) hlen)
  · exact fun r => d.viewV_eq_realPrefix V y z r
  · intro r
    simpa only [hp] using
      simulate_eq_simPrefix S SQ π.rounds B π.verifierFirst x z q (V.coinLen x.length)
        hlen hsim r

end TCSlib.Cryptography.SequentialZK
