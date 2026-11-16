/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.AliceSimulator
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.OTAnswerWords
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SimulationBound
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TwoMoveViews

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Statistical simulation of the sender's two-message view

In an Alice-first, two-message bit-transfer hybrid, the sender receives no ideal answers.
If Bob's output is the shared functionality output outside a bounded bad event in Alice's
tape, the copying simulator has that same statistical simulation bound.

## Main definitions

There are no new definitions.

## Main results

* `distAdv_real_ideal_le`: a generic protocol correctness bound yields Alice simulation.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Theorem 163.7 (Alice's simulator in the OT-hybrid model).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceStatistical

open Complexity Turing

/-- Suppose a bit-transfer hybrid main phase has two moves with Alice first and Alice's
coin polynomial is `p`. If both functionality outputs are the same word, and Bob outputs
that word outside an Alice-tape event of probability at most `δ(n)`, then the fixed copying
simulator with polynomial `p` has advantage at most `δ(n)` for all inputs and tests.
[PS10, Theorem 163.7]
`∀ (D : NUPPT) n x y, distAdv (H.realA F n x y) (F.idealA (AliceSimulator.simulator p) n x y)
(D.distinguisherL n) ≤ δ n`.

**Proof sketch.** Normalize Alice's tape with a bit-word-preserving equivalence and lift
its bad-event bound to the actual tape type. The two-move view and output readers identify
Alice's sole received message with Bob's output. Bit transfer gives Alice no ideal answers.
Outside the bad event, correctness and equality of the functionality output words identify
the real view with the copying simulator view. Apply the proved copying-simulator coupling.
No encryption or circuit definition is used. -/
theorem distAdv_real_ideal_le (H : HybridProtocol otFunctionality) (F : Functionality)
    (p : PolyExpr) (hCoins : H.main.P.coins = p)
    (hRounds : H.main.rounds = .const 2) (hFirst : H.main.verifierFirst = false)
    (BadWord : ℕ → List Bool → Prop) (δ : ℕ → ℝ)
    (hBad : ∀ n, uprob (fun r : Fin (p.eval n) → Bool => BadWord n (List.ofFn r)) ≤ δ n)
    (hOutputs : ∀ n x y, List.ofFn (F.f n x y).1 = List.ofFn (F.f n x y).2)
    (hCorrect : ∀ n x y (r : H.Coins n), ¬ BadWord n (List.ofFn r.1) →
      H.main.outV H.main.P (List.replicate n true)
        (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
        (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2)) r =
          List.ofFn (F.f n x y).2) :
    ∀ (D : NUPPT) n x y,
      distAdv (H.realA F n x y) (F.idealA (AliceSimulator.simulator p) n x y)
        (D.distinguisherL n) ≤ δ n := by
  intro D n x y
  let σ := H.main.P.Coins (List.replicate n true).length
  have hLen : H.main.P.coinLen (List.replicate n true).length = p.eval n := by
    rw [Strategy.coinLen_eq, hCoins, List.length_replicate]
  let e₀ := strategyTapeEquiv H.main.P (List.replicate n true).length (p.eval n) hLen
  let e := e₀.trans (NUPPT.coinsEquivPoly (AliceSimulator.simulator_coins p) n).symm
  have he₀ (r : σ) : List.ofFn (e₀ r) = List.ofFn r :=
    strategyTapeEquiv_ofFn _ _ _ hLen r
  have he (r : σ) : List.ofFn (e r) = List.ofFn r := by
    rw [Equiv.trans_apply, NUPPT.coinsEquivPoly_symm_ofFn, he₀]
  have hBad' : uprob (fun r : σ => BadWord n (List.ofFn r)) ≤ δ n := by
    have hb := hBad n
    rw [← uprob_comp_equiv e₀] at hb
    simpa only [he₀] using hb
  apply AliceSimulator.distAdv_real_ideal_le p F n x y e (H.realA F n x y)
    (fun r : σ => BadWord n (List.ofFn r)) (δ n) hBad'
  intro r hr
  have hv := hCorrect n x y r hr
  let first := fun w z r => H.main.P.next w z r []
  let reply := fun w z r a => H.main.V.next w z r [a]
  rw [TwoMoveViews.outV_eq H.main first reply hRounds hFirst
    (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)] at hv
  rw [TwoMoveViews.realA_eq first reply H hRounds hFirst
    (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)]
  simp only [HybridProtocol.privA_eq, OTAnswerWords.answersA_nil] at hv ⊢
  rw [hv]
  simp only [View.encode_mk, he, hOutputs n x y]

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceStatistical
