/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.SequentialZK.EndpointSampling
import TCSlib.Cryptography.Composability.SequentialZK.ExecutionBounds
import TCSlib.Cryptography.Composability.SequentialZK.ProofTransfers

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bounds for actual real phase prefixes

The endpoint reader identifies a typed real-prefix fold with an execution of the padded
prover. The construction specification then gives its exact message count, while the
original prover's uniform message bound also bounds every padded-prover reply. Existing
execution and word-encoding bounds finish the advice-size estimate. [PS10, Theorem 175.1].

## Main definitions

There are no new definitions.

## Main results

* `PaddedProverSpec.realPrefix_bounds`: exact count, bounded messages, and encoded-size bound.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.2.1, Theorem 175.1.
* [Gol01] O. Goldreich, *Foundations of Cryptography, Volume I: Basic Tools*, Cambridge
  University Press, 2001, §4.3.4.
-/

namespace TCSlib.Cryptography.SequentialZK.PaddedProverSpec

open Complexity

/-- For `d : PaddedProverSpec π ρ x q p`, verifier `V`, inputs `y,z`, tape `rV`, index
`j≤q`, message cap `B`, uniform original-prover bound `hbound`, and independent phase coins
`coins`, put `pre = realPrefix π V x y z rV p j coins` and `k = π.rounds.eval |x|`. Then
`pre.length = j*k`, every `m ∈ pre` has `m.length ≤ B`, and
`(Strategy.encodeMsgs pre).length ≤ (j*k)*(2*B+2)`.
[PS10, Theorem 175.1; Gol01, §4.3.4, bounded real-prefix reduction advice].

**Proof sketch.** The public coin-table equivalence supplies a raw tape with exactly the
requested independent phase blocks. The real-prefix endpoint reader identifies the fold
with the repeated execution on that tape. Its boundary reader gives exactly `j*k` received
messages. Each repeated-prover reply is either an original bounded message or an empty
filler, by the specification's public reply equation. This is the
public theorem `next_length_le`. The public execution-message bound
therefore controls every received message. Finally reuse the execution encoding bound,
which already invokes the generic public encoded-word length theorem. -/
theorem realPrefix_bounds {π ρ : Protocol} {x : List Bool} {q p : ℕ}
    (d : PaddedProverSpec π ρ x q p) (V : Strategy) (y z rV : List Bool)
    (j : ℕ) (hj : j ≤ q) (B : ℕ)
    (hbound : ∀ r hist, (π.P.next x y r hist).length ≤ B)
    (coins : Fin j → π.P.Coins x.length) :
    (realPrefix π V x y z rV p j coins).length = j * π.rounds.eval x.length ∧
    (∀ m ∈ realPrefix π V x y z rV p j coins, m.length ≤ B) ∧
    (Strategy.encodeMsgs (realPrefix π V x y z rV p j coins)).length ≤
      (j * π.rounds.eval x.length) * (2 * B + 2) := by
  -- Reconstruct one raw tape whose blocks are the supplied typed phase coins.
  let e : (Fin (j * π.P.coinLen x.length) → Bool) ≃ (Fin j → π.P.Coins x.length) :=
    coinTableEquiv rfl
  let tape := List.ofFn (e.symm coins)
  have hblocks (i : Fin j) :
      coinBlock (π.P.coinLen x.length) i tape = List.ofFn (coins i) := by
    have hblock := coinTableEquiv_block (m := j * π.P.coinLen x.length)
      (q := j) (c := π.P.coinLen x.length) rfl (e.symm coins) i
    have hinverse := congrArg (fun table : Fin j → π.P.Coins x.length =>
      List.ofFn (table i)) (e.apply_symm_apply coins)
    exact hblock.trans hinverse
  have hend : realPrefix π V x y z rV p j coins =
      (exec ρ.P V π.verifierFirst x y z tape rV
        (2 * π.rounds.eval x.length * j)).2 :=
    d.realPrefix_eq_exec V y z tape rV j hj coins hblocks
  have hcount : (realPrefix π V x y z rV p j coins).length =
      j * π.rounds.eval x.length := by
    rw [hend]
    exact (d.boundary V y z tape rV j).2
  -- Empty fillers satisfy the same cap as the original real replies.
  have hsource (hist : List (List Bool)) : (ρ.P.next x y tape hist).length ≤ B :=
    d.next_length_le y B hbound tape hist
  have hmessages : ∀ m ∈ realPrefix π V x y z rV p j coins, m.length ≤ B := by
    rw [hend]
    exact exec_snd_bounded ρ.P V π.verifierFirst x y z tape rV B
      (2 * π.rounds.eval x.length * j) hsource
  -- Reuse the existing execution-specific encoded-history estimate.
  have hencoding : (Strategy.encodeMsgs (realPrefix π V x y z rV p j coins)).length ≤
      (j * π.rounds.eval x.length) * (2 * B + 2) := by
    rw [hend]
    have hencoded := length_encodeMsgs_exec_snd_le ρ.P V π.verifierFirst x y z tape rV B
      (2 * π.rounds.eval x.length * j) hsource
    rw [(d.boundary V y z tape rV j).2] at hencoded
    exact hencoded
  exact ⟨hcount, hmessages, hencoding⟩

end TCSlib.Cryptography.SequentialZK.PaddedProverSpec
