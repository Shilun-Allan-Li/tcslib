/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.SequentialZK.Congruence
import TCSlib.Cryptography.Asymptotic.Adversary

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Earlier coin blocks determine an earlier padded execution

## Main definitions

This module introduces no definitions.

## Main results

* `Composability.exec_eq_of_verifier_blocks`: a padded verifier reads only the first `j`
  coin blocks before move `2*k*j`, so tapes agreeing on those blocks have the same earlier
  transcript against any prover.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 175.1 (sequential composition and conditioning on earlier phases).
-/

namespace TCSlib.Cryptography.Composability

/-- For prover `P`, padded verifier `S`, original verifier `V`, first-mover flag `vFirst`,
inputs `x`, `y`, `z`, prover tape `rP`, verifier tapes `rV`, `rV2`, phase length `k`, phase
count `q`, coin-block length `c`, cutoff `j < q`, and arbitrary terminal function `terminal`,
suppose `S` follows the displayed padded-verifier equation and recovers the actual move
index from its received-history length. If `coinBlock c i rV = coinBlock c i rV2` for all
`i < j`, then
`exec P S vFirst x y z rP rV (2*k*j) = exec P S vFirst x y z rP rV2 (2*k*j)`.
[PS10, Theorem 175.1, earlier phases depend only on earlier coin blocks].

**Proof sketch.** With zero real moves both executions are empty. Otherwise compare the
replies on the source run's reached histories. At a verifier move `t < 2*k*j`, the recovered
index implies twice the received-history length is at most `t+1`. Since `j < q`, this
excludes the terminal history of length `q*k`. The phase index is `t/(2*k) < j`, so both
tapes provide the same coin block. The padded-verifier equation therefore gives the same
reply; prover replies agree because the prover tape is fixed. Reached-history execution
congruence finishes the comparison. -/
theorem exec_eq_of_verifier_blocks (P S V : Strategy) (vFirst : Bool)
    (x y z rP rV rV2 : List Bool) (k q c j : ℕ)
    (terminal : List Bool → List (List Bool) → List Bool)
    (hnext : ∀ r hist, S.next x z r hist =
      if hist.length = q * k then terminal r hist
      else
        let idx := if vFirst then 2 * hist.length else 2 * hist.length - 1
        if idx % (2 * k) < k then
          V.next x z (coinBlock c (idx / (2 * k)) r)
            (hist.drop (idx / (2 * k) * k))
        else [])
    (hj : j < q)
    (hindex : ∀ t < 2 * k * j, moverIsV vFirst t = true →
      (if vFirst then 2 * (exec P S vFirst x y z rP rV t).2.length
        else 2 * (exec P S vFirst x y z rP rV t).2.length - 1) = t)
    (hblocks : ∀ i < j, coinBlock c i rV = coinBlock c i rV2) :
    exec P S vFirst x y z rP rV (2 * k * j) =
      exec P S vFirst x y z rP rV2 (2 * k * j) := by
  by_cases hk : k = 0
  · subst k
    simp only [Nat.mul_zero, Nat.zero_mul, exec_zero]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    apply exec_congr_reachable P S P S vFirst x y z rP rV rP rV2 (2 * k * j)
    · intro _ _ _
      rfl
    · intro t ht hm
      -- A pre-cutoff verifier move cannot already have the terminal history length.
      have hi := hindex t ht hm
      have hlen : 2 * (exec P S vFirst x y z rP rV t).2.length ≤ t + 1 := by
        cases vFirst <;> simp only [Bool.false_eq_true, if_false, if_true] at hi <;> omega
      have hne : (exec P S vFirst x y z rP rV t).2.length ≠ q * k := by
        intro heq
        rw [heq] at hlen
        have hjk := Nat.mul_le_mul_right k hj
        nlinarith
      -- Only a block before j can contribute to this reply.
      rw [hnext, hnext, if_neg hne, if_neg hne]
      dsimp only
      rw [hi, hblocks (t / (2 * k)) (Nat.div_lt_of_lt_mul ht)]

end TCSlib.Cryptography.Composability
