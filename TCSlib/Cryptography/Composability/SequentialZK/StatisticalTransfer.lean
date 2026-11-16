/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.SequentialZK.StatisticalPrefix
import TCSlib.Cryptography.Composability.SequentialZK.EndpointSampling
import TCSlib.Cryptography.ZeroKnowledge.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Statistical zero knowledge from the padded-prover contract

## Main definitions

This module introduces no definitions or computational hosts.

## Main results

* `statZK_of_padded_spec`: a padded repetition satisfying the published prover contract
  preserves statistical zero knowledge with the exact sum of the phase errors.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 175.1.
-/

namespace TCSlib.Cryptography.SequentialZK

open Complexity

/-- For protocols `π,ρ`, relation `R`, error `δ`, bound `B`, and phase polynomial `Q`, if
`π` is statistically zero knowledge with error `δ`, has prover bound `B`, and `ρ` satisfies
`PaddedProverSpec π ρ x (Q.eval |x|) p` at every `x`, with the original mover-dependent
real-message count `p`, then `ρ` is statistically zero knowledge with error `Q(n)*δ(n)`.
[PS10, Theorem 175.1; Gol01, §4.3.4].
`StatZK ρ R (fun n => Q.eval n * δ n)`.

**Proof sketch.** Apply the original statistical hypothesis to the efficient fixed-tape
phase verifier. The existing uniform prefix machine supplies one strict-PPT simulator using
one global verifier tape and independent phase simulator coins. At each witnessed input the
original comparison makes its error nonnegative. The normalized phase-recursion theorem
bounds each fixed-tape prefix comparison by the sum of the phase errors. Pair the prefixes
with the common verifier tape and average. The canonical endpoint readers reindex both
finite coin spaces and identify the real view and the constructed simulator exactly.
Zero phases and zero rounds require no separate positivity premise. -/
theorem statZK_of_padded_spec {π ρ : Protocol} {R : List Bool → List Bool → Prop}
    {δ : ℕ → ℝ} {B : PolyExpr} (h : StatZK π R δ) (hB : π.ProverBounded R B)
    (Q : PolyExpr)
    (hspec : ∀ x, PaddedProverSpec π ρ x (Q.eval x.length)
      (if π.verifierFirst then π.rounds.eval x.length / 2
        else (π.rounds.eval x.length + 1) / 2)) :
    StatZK ρ R (fun n => Q.eval n * δ n) := by
  apply (StatZK_iff ρ R _).2
  intro V hV
  -- Choose one phase simulator and realize its repeated normalized prefix machine.
  obtain ⟨S, hS, hclose⟩ := (StatZK_iff π R δ).1 h (phaseVerifier V)
    (phaseVerifier_efficient (V := V) hV)
  obtain ⟨SQ, hSQ, hcoins, hsim⟩ :=
    exists_phaseSimulator S hS π.rounds B Q V.coins π.verifierFirst
  refine ⟨SQ, hSQ, ?_⟩
  intro x y z hxy
  let p := if π.verifierFirst then π.rounds.eval x.length / 2
    else (π.rounds.eval x.length + 1) / 2
  have hδ : 0 ≤ δ x.length := by
    with_reducible exact ((hclose x y [] hxy).nonneg)

  have hprefix (rV : V.Coins x.length) :
      StatClose (realPrefix π V x y z (List.ofFn rV) p (Q.eval x.length))
        (simPrefix S x z (List.ofFn rV) (π.rounds.eval x.length) (B.eval x.length)
          p (Q.eval x.length)) ((Q.eval x.length : ℝ) * δ x.length) := by
    with_reducible exact ((hspec x).statClose_prefix V S y z (List.ofFn rV) (B.eval x.length)
      (δ x.length)
      (fun r hist => (Protocol.proverBounded_iff π R B).1 hB x y r hist hxy)
      (fun aux => hclose x y aux hxy))
  -- Pair both prefixes with their common verifier tape and average over that tape.
  have hpair (rV : V.Coins x.length) : StatClose
      (fun r : Fin (Q.eval x.length) → π.P.Coins x.length =>
        (rV, realPrefix π V x y z (List.ofFn rV) p (Q.eval x.length) r))
      (fun r : Fin (Q.eval x.length) → S.Coins x.length =>
        (rV, simPrefix S x z (List.ofFn rV) (π.rounds.eval x.length)
          (B.eval x.length) p (Q.eval x.length) r))
      ((Q.eval x.length : ℝ) * δ x.length) := by
    with_reducible exact (StatClose.map
      (σ := Fin (Q.eval x.length) → π.P.Coins x.length)
      (τ := Fin (Q.eval x.length) → S.Coins x.length)
      (γ := List (List Bool)) (γ' := V.Coins x.length × List (List Bool))
      (X := realPrefix π V x y z (List.ofFn rV) p (Q.eval x.length))
      (Y := simPrefix S x z (List.ofFn rV) (π.rounds.eval x.length)
        (B.eval x.length) p (Q.eval x.length)) (hprefix rV) (fun pre => (rV, pre)))
  have hjoint : StatClose
      (fun r : V.Coins x.length × (Fin (Q.eval x.length) → π.P.Coins x.length) =>
        (r.1, realPrefix π V x y z (List.ofFn r.1) p (Q.eval x.length) r.2))
      (fun r : V.Coins x.length × (Fin (Q.eval x.length) → S.Coins x.length) =>
        (r.1, simPrefix S x z (List.ofFn r.1) (π.rounds.eval x.length)
          (B.eval x.length) p (Q.eval x.length) r.2))
      ((Q.eval x.length : ℝ) * δ x.length) := by
    with_reducible exact (statClose_average
      (α := V.Coins x.length)
      (β := Fin (Q.eval x.length) → π.P.Coins x.length)
      (γ := Fin (Q.eval x.length) → S.Coins x.length)
      (O := V.Coins x.length × List (List Bool))
      (mul_nonneg (Nat.cast_nonneg _) hδ) hpair)
  -- The exact coin equivalences identify the actual real and simulated view laws.
  have hlen : SQ.coinLen x.length =
      V.coinLen x.length + Q.eval x.length * S.coinLen x.length := by
    rw [NUPPT.coinLen_eq, hcoins, PolyExpr.eval_add, PolyExpr.eval_mul,
      Strategy.coinLen_eq, NUPPT.coinLen_eq]
  with_reducible exact (statClose_view_endpoints (hspec x) V y z S SQ B rfl hlen
    (fun r => by simpa only [Strategy.coinLen_eq] using hsim x z r)
    ((Q.eval x.length : ℝ) * δ x.length) hjoint)

end TCSlib.Cryptography.SequentialZK
