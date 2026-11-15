/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.SequentialZK.ComputationalPhaseBound
import TCSlib.Cryptography.Composability.SequentialZK.ComputationalHybrid
import TCSlib.Cryptography.Composability.SequentialZK.RealPrefixBounds
import TCSlib.Cryptography.ZeroKnowledge.Defs
import TCSlib.Cryptography.Asymptotic.ReductionSupport

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Computational zero knowledge from the padded-prover contract

## Main definitions

This module introduces no definitions or computational hosts.

## Main results

* `zk_of_padded_spec`: a protocol satisfying the padded-prover contract preserves
  computational zero knowledge under the original prover-message bound.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 175.1.
* [Gol01] O. Goldreich, *Foundations of Cryptography, Volume I: Basic Tools*, Cambridge
  University Press, 2001, §4.3.4.
-/

namespace TCSlib.Cryptography.SequentialZK

open Complexity

/-- For protocols `π,ρ`, relation `R`, prover bound `B`, and phase polynomial `Q`, if
`ZK π R`, `π.ProverBounded R B`, and `ρ` satisfies the padded-prover specification with
`Q(|x|)` phases and the original mover-dependent real-message count at every `x`, then
`ZK ρ R`. [PS10, Theorem 175.1; Gol01, §4.3.4].

**Proof sketch.** Apply the original zero-knowledge hypothesis to the efficient fixed-tape
phase verifier, and realize its uniform normalized repeated simulator with one global
verifier tape. For each auxiliary-input polynomial and distinguisher, the public bounded
metadata reduction supplies one negligible bound for all local phase gaps, uniformly over
all witnesses. The actual real-prefix encoding bound places every reached prefix in that
metadata domain. The conditional hybrid theorem and averaging over verifier tapes multiply
the common bound by the phase count. Its absolute value is negligible, and multiplication
by the syntactic polynomial remains negligible. Exact endpoint equivalences identify the
actual real view and the uniform simulator without changing the advantage or its bound.
The selector's zero-phase metadata remains nonempty, and all empty-history cases are covered
by the same endpoint readers. No witness is encoded in advice or used by the simulator. -/
theorem zk_of_padded_spec {π ρ : Protocol} {R : List Bool → List Bool → Prop}
    {B : PolyExpr} (h : ZK π R) (hB : π.ProverBounded R B) (Q : PolyExpr)
    (hspec : ∀ x, PaddedProverSpec π ρ x (Q.eval x.length)
      (if π.verifierFirst then π.rounds.eval x.length / 2
        else (π.rounds.eval x.length + 1) / 2)) : ZK ρ R := by
  apply (ZK_iff ρ R).2
  intro V hV
  -- Choose one simulator before the auxiliary bound and distinguisher are supplied.
  obtain ⟨S, hS, hclose⟩ := (ZK_iff π R).1 h (phaseVerifier V)
    (phaseVerifier_efficient (V := V) hV)
  obtain ⟨SQ, hSQ, hcoins, hsim⟩ :=
    exists_phaseSimulator S hS π.rounds B Q V.coins π.verifierFirst
  refine ⟨SQ, hSQ, ?_⟩
  intro Lz D
  obtain ⟨ε, hε, hphase⟩ := exists_negligible_phase_bound π R V S hS hclose Lz D Q B
  have habs : Negligible (fun n => |ε n|) := hε.mono ⟨0, fun n _ => by rw [abs_abs]⟩
  refine ⟨(fun n => (Q.eval n : ℝ) * |ε n|), habs.polyExpr_mul Q, ?_⟩
  intro x y z hxy hz
  have hbound : ∀ r hist, (π.P.next x y r hist).length ≤ B.eval x.length :=
    fun r hist => (Protocol.proverBounded_iff π R B).1 hB x y r hist hxy
  -- Every actual real prefix lies in the polynomial encoded-prefix envelope.
  have hlocal (rV : V.Coins x.length) (i : ℕ) (hi : i < Q.eval x.length)
      (coins : Fin i → π.P.Coins x.length) :
      phaseGap π V S B Q x y z (List.ofFn rV) (D.distinguisherL x.length) i
        (realPrefix π V x y z (List.ofFn rV)
          (if π.verifierFirst then π.rounds.eval x.length / 2
            else (π.rounds.eval x.length + 1) / 2) i coins) ≤ |ε x.length| := by
    apply hphase x y z (List.ofFn rV) i _ hxy hz
    · rw [List.length_ofFn]
    · exact hi
    · have hb := (hspec x).realPrefix_bounds V y z (List.ofFn rV) i hi.le
        (B.eval x.length) hbound coins
      exact hb.2.2.trans (Nat.mul_le_mul_right (2 * B.eval x.length + 2)
        (Nat.mul_le_mul_right (π.rounds.eval x.length) hi.le))
  have hprefix := prefix_distAdv_joint_le S B Q (hspec x) V y z
    (D.distinguisherL x.length) rfl hbound |ε x.length| (abs_nonneg _) hlocal
  -- Reindex the actual real and simulator tapes using their published endpoint equations.
  have hlen : SQ.coinLen x.length =
      V.coinLen x.length + Q.eval x.length * S.coinLen x.length := by
    rw [NUPPT.coinLen_eq, hcoins, PolyExpr.eval_add, PolyExpr.eval_mul,
      Strategy.coinLen_eq, NUPPT.coinLen_eq]
  with_reducible exact ((distAdv_view_endpoints (hspec x) V y z S SQ B rfl hlen
    (fun r => by simpa only [Strategy.coinLen_eq] using hsim x z r)
    (D.distinguisherL x.length)).trans_le hprefix)

end TCSlib.Cryptography.SequentialZK
