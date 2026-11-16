/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SimulationBound

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Statistical switching of the receiver's paired output

For any hybrid protocol, an event on Alice's bit tape can control replacement
of the outer Alice output in Bob's real experiment. Bob's actual complete
encoded view is retained. The canonical tape probability is transported by
the existing strategy-tape equivalence and independent-tape marginal reader.

## Main definitions

None.

## Main results

* `statClose_real_output_switch`: an off-bad Alice-output equation gives the
  statistical bound uniformly in the parameter and private inputs.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Theorem 163.7 (statistical correctness switch for Bob's view).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobStatistical

open Complexity Turing TCSlib.Cryptography

/-- If Alice's actual output is her functionality output outside an event on
her tape of probability at most `δ(n)`, Bob's real experiment is `δ(n)`-close
to his unchanged actual encoded view paired with that functionality output.
The tape bound is stated on the canonical polynomial-length bit tape, and
Bob's independent tape can have any length. [PS10, Theorem 163.7]
`∀ n x y, StatClose (H.realB F n x y) (fun r => pairEncode (H.main.viewV (List.replicate n true)
(H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2)) (H.privB n (List.ofFn x)
(List.ofFn y) (List.ofFn r.1) (List.ofFn r.2)) r).encode (List.ofFn (F.f n x y).1)) (δ n)`.

**Proof sketch.** Use the sender's coin-polynomial equation to normalize her
actual tape to the canonical bit tape without changing its word. Pull back
the supplied bad-event bound through that equivalence and drop the independent
Bob tape by the existing marginal equation. The published real-output switch
then applies directly with the supplied off-bad output equality. No new
probability inequality, simulator or protocol definition is introduced. -/
theorem statClose_real_output_switch {G : Functionality} (H : HybridProtocol G)
    (F : Functionality) (p : PolyExpr) (hCoins : H.main.P.coins = p)
    (BadWord : ℕ → List Bool → Prop) (δ : ℕ → ℝ)
    (hBad : ∀ n, uprob (fun r : Fin (p.eval n) → Bool => BadWord n (List.ofFn r)) ≤ δ n)
    (hCorrect : ∀ n x y (r : H.Coins n), ¬ BadWord n (List.ofFn r.1) →
      H.main.outP (List.replicate n true)
        (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
        (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2)) r =
          List.ofFn (F.f n x y).1) :
    ∀ n x y, StatClose (H.realB F n x y)
      (fun r => pairEncode
        (H.main.viewV (List.replicate n true)
          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2)) r).encode
        (List.ofFn (F.f n x y).1)) (δ n) := by
  intro n x y
  refine realB_output_switch H F n x y
    (fun r => BadWord n (List.ofFn r.1)) (δ n) ?_ (hCorrect n x y)
  rw [uprob_fst (β := H.main.V.Coins (List.replicate n true).length)
    (fun r : H.main.P.Coins (List.replicate n true).length => BadWord n (List.ofFn r))]
  have hLen : H.main.P.coinLen (List.replicate n true).length = p.eval n := by
    rw [Strategy.coinLen_eq, hCoins, List.length_replicate]
  have h := hBad n
  rw [← uprob_comp_equiv (strategyTapeEquiv
    H.main.P (List.replicate n true).length (p.eval n) hLen)] at h
  simpa only [strategyTapeEquiv_ofFn] using h

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobStatistical
