/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.SequentialZK.Phases
import TCSlib.Cryptography.ZeroKnowledge.InteractiveProofs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Acceptance bounds from explicit soundness error

## Main definitions

This module introduces no definitions.

## Main results

* `InteractiveProofErr.uprob_accept_le`: acceptance on a no-instance has probability at
  most the stated soundness error.
* `InteractiveProofErr.sound_nonneg`: the stated error is nonnegative on a no-instance.
* `Composability.prefixProver_accept_le`: a fixed earlier transcript and prover tape give
  acceptance at most the stated error over a fresh original verifier tape alone.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §4.5 (interactive-proof soundness) and Theorem 175.1 (sequential repetition).
-/

namespace TCSlib.Cryptography

/-- For `h : InteractiveProofErr π L s`, a no-instance `x ∉ L`, a prover `P'`, and verifier
auxiliary input `z`, `Pr[π.outV P' x [] z = [true]] ≤ s |x|`.
[PS10, §4.5, acceptance form of soundness]. -/
theorem InteractiveProofErr.uprob_accept_le {π : Protocol} {L : Language Bool} {s : ℕ → ℝ}
    (h : InteractiveProofErr π L s) (x : List Bool) (hx : x ∉ L)
    (P' : Strategy) (z : List Bool) :
    uprob (fun r : π.ExecCoins P' x => π.outV P' x [] z r = [true]) ≤ s x.length := by
  have hle : uprob (fun r : π.ExecCoins P' x => π.outV P' x [] z r = [true]) ≤
      uprob (fun r : π.ExecCoins P' x => ¬ π.outV P' x [] z r = [false]) :=
    uprob_mono fun r hr => by rw [hr]; decide
  rw [uprob_not] at hle
  linarith [h.sound x hx P' z]

/-- For `h : InteractiveProofErr π L s` and a no-instance `x ∉ L`, `0 ≤ s |x|`.
[PS10, §4.5, a probability bound has nonnegative error]. -/
theorem InteractiveProofErr.sound_nonneg {π : Protocol} {L : Language Bool} {s : ℕ → ℝ}
    (h : InteractiveProofErr π L s) (x : List Bool) (hx : x ∉ L) : 0 ≤ s x.length :=
  (sub_le_self_iff (1 : ℝ)).mp ((h.sound x hx π.P []).trans (uprob_le_one _))

namespace Composability

/-- For `h : InteractiveProofErr π L s`, a no-instance `x ∉ L`, a strategy `P`, its fixed
auxiliary input `y`, tape `rP`, earlier received history `prior`, and verifier auxiliary
input `z`, the probability over `rV : π.V.Coins |x|` that `π.V.next` accepts the execution
of `prefixProver P y rP prior` on prover tape `[]` and verifier tape `List.ofFn rV` is at
most `s |x|`. [PS10, Theorem 175.1, soundness with an earlier transcript fixed].
`uprob (fun rV : π.V.Coins x.length => π.V.next x z (List.ofFn rV) (exec (prefixProver P y rP prior)
π.V π.verifierFirst x [] z [] (List.ofFn rV) (π.rounds.eval x.length)).2 = [true]) ≤ s x.length`.

**Proof sketch.** Apply the explicit-error acceptance bound to the prefix-hardwired prover.
Its coin polynomial is zero, so every one of its coin strings is empty. Read the verifier
output and transcript through their published equations and replace this prover coin
string by `[]`. The acceptance event then depends only on the verifier's tape; the public
uniform-product and constant-average laws remove the unused prover coins. -/
theorem prefixProver_accept_le {π : Protocol} {L : Language Bool} {s : ℕ → ℝ}
    (h : InteractiveProofErr π L s) (x : List Bool) (hx : x ∉ L)
    (P : Strategy) (y rP : List Bool) (prior : List (List Bool)) (z : List Bool) :
    uprob (fun rV : π.V.Coins x.length =>
      π.V.next x z (List.ofFn rV)
        (exec (prefixProver P y rP prior) π.V π.verifierFirst x [] z []
          (List.ofFn rV) (π.rounds.eval x.length)).2 = [true]) ≤ s x.length := by
  have hnil (r : (prefixProver P y rP prior).Coins x.length) : List.ofFn r = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [List.length_ofFn, Strategy.coinLen_eq, prefixProver_coins,
      Complexity.PolyExpr.eval_const]
  have hb := h.uprob_accept_le x hx (prefixProver P y rP prior) z
  simp only [Protocol.outV_eq, Protocol.transcriptWith_eq, hnil] at hb
  rw [uprob_prod] at hb
  simpa only [HardcoreBit.uexp_const] using hb

end Composability

end TCSlib.Cryptography
