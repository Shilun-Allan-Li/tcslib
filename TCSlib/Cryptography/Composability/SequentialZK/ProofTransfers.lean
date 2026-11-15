/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.SequentialZK.PaddedProverSpec
import TCSlib.Cryptography.ZeroKnowledge.InteractiveProofs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Completeness transfer through a padded-prover contract

## Main definitions

This module introduces no definitions.

## Main results

* `PaddedProverSpec.next_length_le`: repeated replies keep an original message-length bound.
* `PaddedProverSpec.complete`: pointwise acceptance transfer preserves the bounded
  completeness clause, using the published witness-completeness constructor.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 175.1 (sequential repetition of interactive proofs).
-/

namespace TCSlib.Cryptography.SequentialZK.PaddedProverSpec

open Complexity

/-- For `d : PaddedProverSpec π ρ x q p`, auxiliary input `y`, bound `B`, and an original
reply bound `∀ r hist, |π.P.next x y r hist| ≤ B`, every repeated reply has length at most
`B`: `∀ r hist, |ρ.P.next x y r hist| ≤ B`. [PS10, Theorem 175.1]. -/
theorem next_length_le {π ρ : Protocol} {x : List Bool} {q p : ℕ}
    (d : PaddedProverSpec π ρ x q p) (y : List Bool) (B : ℕ)
    (hB : ∀ r hist, (π.P.next x y r hist).length ≤ B) :
    ∀ r hist, (ρ.P.next x y r hist).length ≤ B := by
  intro r hist
  rw [d.next]
  dsimp only
  split_ifs <;> first | exact hB _ _ | exact Nat.zero_le _

/-- For pointwise construction contracts `d`, if acceptance on every `x,y,z` transfers
from `π` to `ρ`, then a bounded completeness witness for each `x ∈ L` in `π` is also one
in `ρ`, with the same polynomial bound. [PS10, Theorem 175.1].

**Proof sketch.** Use the original reply bound and perfect acceptance together as a witness
relation. The padded next-message reader preserves that bound. The published bounded-witness
completeness constructor then uses the transferred acceptance on every such witness. -/
theorem complete {π ρ : Protocol} {L : Language Bool} {q p : List Bool → ℕ}
    (d : ∀ x, PaddedProverSpec π ρ x (q x) (p x))
    (haccept : ∀ x y z, (uprob (fun r : π.ExecCoins π.P x =>
      π.outV π.P x y z r = [true]) = 1) →
        uprob (fun r : ρ.ExecCoins ρ.P x => ρ.outV ρ.P x y z r = [true]) = 1)
    (hc : ∃ B : PolyExpr, ∀ x ∈ L, ∃ y : List Bool,
      (∀ r hist, (π.P.next x y r hist).length ≤ B.eval x.length) ∧
        ∀ z, uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1) :
    ∃ B : PolyExpr, ∀ x ∈ L, ∃ y : List Bool,
      (∀ r hist, (ρ.P.next x y r hist).length ≤ B.eval x.length) ∧
        ∀ z, uprob (fun r : ρ.ExecCoins ρ.P x => ρ.outV ρ.P x y z r = [true]) = 1 := by
  obtain ⟨B, hcomplete⟩ := hc
  let R : List Bool → List Bool → Prop := fun x y =>
    (∀ r hist, (π.P.next x y r hist).length ≤ B.eval x.length) ∧
      ∀ z, uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1
  have hbounded : ρ.ProverBounded R B := by
    rw [Protocol.proverBounded_iff]
    intro x y r hist hR
    exact (d x).next_length_le y (B.eval x.length) hR.1 r hist
  exact hbounded.exists_complete hcomplete (fun x y hR z => haccept x y z (hR.2 z))

end TCSlib.Cryptography.SequentialZK.PaddedProverSpec
