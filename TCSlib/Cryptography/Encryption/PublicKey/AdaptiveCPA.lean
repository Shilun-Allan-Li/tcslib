/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveSecurity
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Hybrid
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Handler
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Games
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Reduction
import TCSlib.Cryptography.Games.Advantage
import TCSlib.Cryptography.Games.Efficiency
import TCSlib.Cryptography.Asymptotic.ReductionSupport

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# From one challenge to adaptively many under chosen-plaintext attack

For a public-key scheme, security in the single-challenge CPA game of [PS10, Definition 171.5]
implies security in the adaptive left-or-right game with a polynomial number of fresh
challenges (`FixedLengthPKScheme.AdaptiveINDSecure`). The argument is the single-to-many hybrid
lifting of [PS10, p. 103] and [Pas09, Theorem 2], stated there for fixed message vectors and
extended here to adaptively chosen challenges: the adversary holds the public key, so a
reduction can produce every challenge but one itself.

## Main results

* `Composability.FixedLengthPKScheme.INDSecure.adaptive_cpa`: single-challenge CPA security
  gives adaptive multi-challenge CPA security.

## Contents

* `AdaptiveCPA/Hybrid`: the hybrid challenge oracles, transport along equal lengths, simulation
  through a state abstraction, and coins in advance against lazy coins.
* `AdaptiveCPA/Handler`: the reduction's handler for T2 and its call equations.
* `AdaptiveCPA/Games`: the hybrid games; the end hybrids are the adaptive games.
* `AdaptiveCPA/Reduction`: the reduction's single-challenge game is a hybrid.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Definition 171.5 (book p. 171) and the single-to-many hybrid argument (book p. 103).
* [Pas09] R. Pass, *Cornell CS 6830, lecture 13* (2009), §1 and Theorem 2.
-/

namespace TCSlib.Cryptography.Composability.FixedLengthPKScheme

open Complexity Turing TCSlib.Cryptography.Games

/-- **Single-challenge CPA security gives adaptive multi-challenge CPA security**: if every
efficient adversary has negligible advantage in the CPA game with one challenge, then every
efficient adversary has negligible advantage in the adaptive left-or-right CPA game with a
polynomial challenge cap `cap(n)` and query budget `q(n)` [PS10, Definition 171.5; the
single-to-many hybrid argument of p. 103, extended to adaptive challenges].

**Proof sketch.**
1. Fix `A`, `q` and `cap`. For `i ≤ cap(n)` let `H_i` be the adaptive CPA experiment in which the
   first `i` fresh challenges encrypt the right message and the later ones the left message
   (`AdaptiveCPA.acHyb` with the selector `j ↦ [j < i]`, run on T2's codec). Then `H_0` is the
   experiment with `b = false` and `H_{cap(n)}` the one with `b = true`
   (`AdaptiveCPA.acHyb_lt_zero`, `AdaptiveCPA.acHyb_lt_cap`): the adaptive oracles are the
   hybrid with a constant selector (`AdaptiveCPA.castImpl_adaptiveIndImpl`, from
   `adaptiveIndImpl_challenge_encrypt`, `_full`, `_zero`, `_dec_issued`, `_dec_other` and
   `indImpl_dec_onSpec`), and the selector matters only below the cap
   (`AdaptiveCPA.acHyb_congr`).
2. By `Games.exists_advantage_hybrid_gap`, at each `n` with `cap(n) > 0` some `i⋆(n) < cap(n)`
   has `advantage(H_{i⋆}, H_{i⋆+1}) ≥ advantage(H_0, H_{cap(n)}) / cap(n)`; the case `cap(n) = 0`
   has advantage `0`, and there `i⋆(n) = 0`.
3. The single-challenge adversary `B` is T2's machine (`Games.exists_interactiveHandlerMachine`)
   for the handler `AdaptiveCPA.acHandler S cap i⋆`: its state holds the challenge count, the
   latest ciphertext and `i⋆(n)` (its initial state), its seed is `cap(n)` encryption tapes, it
   answers `Dec` with `⊥`, the `j`-th fresh challenge with its own encryption of `m_{[j < i⋆]}`
   for `j ≠ i⋆`, forwards the `i⋆`-th to its one outer `Challenge` call (`perCall = 1`), repeats
   the latest ciphertext past the cap, and outputs `A`'s bit (`finCall = 0`). Its round function
   is polynomial-time because `Enc` is uniform and polynomial-time. `B`'s game with bit `b`
   accepts with the probability of `H_{i⋆+b}` (`AdaptiveCPA.accept_indGame_acHyb`): the
   handler composed with the outer oracles is, through an abstraction of its states, the hybrid
   with the handler's tapes as coins in advance, and uniform tapes give the lazy hybrid
   (`AdaptiveCPA.expect_tapeImpl`).
4. `B` makes at most `q(n)·perCall + finCall` outer queries, a polynomial, so `h` bounds its
   advantage by a negligible `ε`. Hence `A`'s advantage is at most `cap(n) · ε(n)`, negligible
   by `Negligible.polyExpr_mul` (`Asymptotic/ReductionSupport`) with the polynomial `cap`. -/
theorem INDSecure.adaptive_cpa {S : FixedLengthPKScheme} (h : S.INDSecure .cpa) :
    S.AdaptiveINDSecure .cpa := by
  rw [S.adaptiveINDSecure_iff]
  rw [S.INDSecure_iff] at h
  intro A q cap
  -- Step 2: at each `n` the hybrid lemma advises an index `i⋆(n) ≤ cap(n)`.
  have hgap : ∀ n, ∃ i, i ≤ cap.eval n ∧
      advantage (AdaptiveCPA.acHyb S A (q.eval n) (cap.eval n) n fun j => decide (j < 0))
          (AdaptiveCPA.acHyb S A (q.eval n) (cap.eval n) n fun j => decide (j < cap.eval n)) ≤
        (cap.eval n : ℝ) *
          advantage (AdaptiveCPA.acHyb S A (q.eval n) (cap.eval n) n fun j => decide (j < i))
            (AdaptiveCPA.acHyb S A (q.eval n) (cap.eval n) n fun j => decide (j < i + 1)) := by
    intro n
    rcases Nat.eq_zero_or_pos (cap.eval n) with h0 | hpos
    · refine ⟨0, Nat.zero_le _, ?_⟩
      rw [h0, advantage_self, Nat.cast_zero, zero_mul]
    · obtain ⟨i, hi, hle⟩ := exists_advantage_hybrid_gap
        (fun i => AdaptiveCPA.acHyb S A (q.eval n) (cap.eval n) n fun j => decide (j < i)) hpos
      refine ⟨i, hi.le, ?_⟩
      rw [div_le_iff₀ (Nat.cast_pos.2 hpos)] at hle
      rw [mul_comm]
      exact hle
  choose ist hist hgap using hgap
  -- Step 3: the reduction is T2's machine for the handler with the advised index.
  obtain ⟨B, hB⟩ := exists_interactiveHandlerMachine A q (AdaptiveCPA.acDin S)
    (AdaptiveCPA.acDout S) (AdaptiveCPA.acDin S) (AdaptiveCPA.acDout S) (.const 1)
    (AdaptiveCPA.acHandler S cap ist)
  -- Step 4: single-challenge security bounds `B`'s advantage at the polynomial outer budget.
  obtain ⟨ε, hε, hεB⟩ := h B ((q.mul (AdaptiveCPA.acHandler S cap ist).perCall).add
    (AdaptiveCPA.acHandler S cap ist).finCall)
  refine ⟨fun n => (cap.eval n : ℝ) * ε n, hε.polyExpr_mul cap, fun n => ?_⟩
  obtain ⟨φ, hφ⟩ := hB n
  have hred : ∀ b : Bool, accept (S.indGame .cpa B
      (((q.mul (AdaptiveCPA.acHandler S cap ist).perCall).add
        (AdaptiveCPA.acHandler S cap ist).finCall).eval n) b n) =
      accept (AdaptiveCPA.acHyb S A (q.eval n) (cap.eval n) n
        fun j => decide (j < ist n + b.toNat)) := by
    intro b
    rw [PolyExpr.eval_add, PolyExpr.eval_mul]
    exact AdaptiveCPA.accept_indGame_acHyb S cap ist A q n B φ (hist n) hφ b
  have hB' : advantage
      (AdaptiveCPA.acHyb S A (q.eval n) (cap.eval n) n fun j => decide (j < ist n))
      (AdaptiveCPA.acHyb S A (q.eval n) (cap.eval n) n fun j => decide (j < ist n + 1)) ≤ ε n := by
    have hb := hεB n
    rw [advantage_eq, hred false, hred true, Bool.toNat_false, Bool.toNat_true,
      Nat.add_zero] at hb
    rw [advantage_eq]
    exact hb
  calc advantage (S.adaptiveIndGame .cpa A (q.eval n) (cap.eval n) false n)
        (S.adaptiveIndGame .cpa A (q.eval n) (cap.eval n) true n) =
      advantage (AdaptiveCPA.acHyb S A (q.eval n) (cap.eval n) n fun j => decide (j < 0))
        (AdaptiveCPA.acHyb S A (q.eval n) (cap.eval n) n fun j => decide (j < cap.eval n)) := by
        rw [AdaptiveCPA.acHyb_lt_zero, AdaptiveCPA.acHyb_lt_cap]
    _ ≤ _ := hgap n
    _ ≤ (cap.eval n : ℝ) * ε n := mul_le_mul_of_nonneg_left hB' (Nat.cast_nonneg _)

end TCSlib.Cryptography.Composability.FixedLengthPKScheme
