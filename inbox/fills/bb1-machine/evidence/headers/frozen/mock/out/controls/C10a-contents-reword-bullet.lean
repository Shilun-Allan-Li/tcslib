/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyen
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenMachine.Draws
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenMachine.Handler
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenMachine.Oracles
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenMachine.Reduction
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenMachine.Words
import TCSlib.Cryptography.Pairing.Assumptions
import TCSlib.Cryptography.Pairing.Operations

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The BB1 simulator as a Decision BDH distinguisher

Step 3 of the security proof of [BB04, Theorem 4.1] at depth `ℓ = 1`; the other steps and the
assembled theorem `bb1_sidSecure` are in
`AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean`. The paper's algorithm `B`
[BB04, pp. 7–8] is efficient: given `(g, g^a, g^b, g^c, T)` it runs the adversary with the
simulated `Setup`, private keys and challenge, using only group operations, exponent arithmetic
modulo `p` and fresh random exponents. Here the simulation game
`bb1SimGame` (defined beside the scheme in `AdvancedEncryption/IdentityBased/BonehBoyen.lean`)
uses ideal uniform exponents, and the step shows that it is, up to a negligible statistical term,
the Decision BDH experiment of a non-uniform PPT distinguisher (the machine step: handler theorem
T1 with exponents drawn from coin blocks).

This step is its own module so that it can be filled independently of the coupling steps
`bb1_sim_real` and `bb1_sim_random` (ruling Q11 of `PairingCryptographyPlan.md`).

## Main definitions

None.

## Contents

The machine is built in helper modules:

* `BonehBoyenMachine.Draws`: the exponents drawn from coin blocks, their distance from uniform,
  and the simulator with exponents read from a tape.
* `BonehBoyenMachine.Words`: the polynomial-time string functions of the handler.
* `BonehBoyenMachine.Handler`: the handler and its runs.
* `BonehBoyenMachine.Reduction`: the acceptance of the T1 machine and the comparison of the drawn
  with the ideal exponents.
* `BonehBoyenMachine.Oracles`: the simulator's oracles as `drawStep` with fresh exponents, call by
  call, and the comparison of the simulation with the machine on one Decision BDH tuple.

## Main results

* `exists_bb1_distinguisher` — the simulation is a Decision BDH distinguisher (step 3).

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §4.2 (pp. 6–8): Theorem 4.1 and
  its proof.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Definition 26.8, non-uniform PPT.)
-/

namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
  TCSlib.Cryptography.Composability

variable (G : BilinearGen) (ℓ : PolyExpr)

/-- **Step 3: the simulation is a Decision BDH distinguisher** [BB04, §4.2, the algorithm `B`
in the proof of Theorem 4.1, whose cost is the theorem's `Θ(τ ℓ q_S)` with the paper's hierarchy
depth `ℓ = 1`]: with efficient group operations `O` and the arithmetic bundle `H`, for every
adversary `A` and polynomial budget `q` there are non-uniform PPT distinguishers `D_b` and a
negligible `σ` with `|Pr[bb1SimGame … b real = 1] − Pr[dbdhGame (D_b) real = 1]| ≤ σ(κ)` for
both tuple distributions.

**Proof sketch.** MOCK sketch paragraph (placeholder text, not the fill's): the
distinguisher runs the simulator with drawn exponents; each draw is close to uniform,
and a hybrid over the `q(κ) + 1` draws bounds the difference by `σ(κ)`. -/
theorem exists_bb1_distinguisher (H : Candidates.ArithmeticFP) (O : G.Ops) (A : NUPPT)
    (q : PolyExpr) :
    ∃ D : Bool → NUPPT, ∃ σ : ℕ → ℝ, Negligible σ ∧ ∀ (b real : Bool) (κ : ℕ),
      advantage (bb1SimGame G ℓ A (q.eval κ) b real κ) (G.dbdhGame (D b) real κ) ≤ σ κ := by
  -- MOCK body (placeholder, never elaborated)
  obtain ⟨D, hD⟩ := mock_machine G ℓ H O A q
  refine ⟨D, fun κ => ((q.eval κ : ℝ) + 1) * (1 / 2) ^ κ, mock_negl q, ?_⟩
  intro b real κ
  calc _ ≤ _ := hD b real κ
    _ ≤ _ := le_rfl

end TCSlib.Cryptography.AdvancedEncryption.IdentityBased
