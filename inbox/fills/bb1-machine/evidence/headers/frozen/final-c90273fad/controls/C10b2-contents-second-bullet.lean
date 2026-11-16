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
* `BonehBoyenMachine.Handler`: the handler and its run.
* `BonehBoyenMachine.Reduction`: the acceptance of the T1 machine and the comparison of the drawn
  with the ideal exponents.
* `BonehBoyenMachine.Oracles`: the simulator's oracles as `drawStep` with fresh exponents, call by
  call, and the comparison of the simulation with the machine on one Decision BDH tuple.
* `BonehBoyenMachine.Glue`: further glue.

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

**Proof sketch.** `D_b` is the machine that the handler theorem T1 (`Games.exists_handlerMachine`)
gives for `BB1Machine.handler … b q`, run on the adversary `A'` obtained from `A` by
`Games.exists_toCompOn_of_toComp` (its `toCompOn` interface, with a coin bijection). The handler is
the paper's algorithm `B` on encodings: it parses `⟨d, ⟨g, ⟨X, ⟨Y, ⟨Z, T⟩⟩⟩⟩⟩` and answers `A`'s
queries with group operations by `O` (`O.mulG`, `O.powG`, `O.mulT`, membership by `O.memT`) and
exponent arithmetic modulo `p = O.orderStr d` with `H` (negation and differences of residues as
`(p − x) mod p` and `(x + (p − y)) mod p`, the field inverse by `xgcdStr`, with `0 ↦ 0`). Let
`n = κ + wG(κ) + 1`; the exponent of the `j`-th query is
`(Candidates.sampleBelowL p (Nat.size p) n n w).getD 0` on the `j`-th block `w` of `n²` coin bits.
Take `σ(κ) = (q(κ) + 1) · 2^{−κ}`, negligible (`EnsembleLemmas.negligible_polyExpr_mul`,
`negligible_two_pow_neg`). Written as expectations (`advantage_eq`, `accept_eq`, `bb1SimGame_eq`,
`BilinearGen.dbdhGame_eq`), both games draw the generator's coins, the generator, the exponents
`a, b, c` and the randomness of `T` in the same way, so four applications of
`ProbComp.abs_expect_sub_le` reduce the bound to one tuple `(g, X, Y, Z, T)`
(`BB1Machine.abs_expect_bb1Sim_sub_distinguisherL_le`). On that tuple, call by call, `bb1SimImpl`
has the law of `drawStep` with a fresh uniform exponent per query, read on the game's lengths: the
readers `IBEScheme.oracleImpl_{zero,one,two}_onSpec`, `ofFn_bb1Scheme_encPP`,
`ofFn_bb1Scheme_encSK`, `bb1Scheme_msgSpace_iff` and `ofFn_bb1SimCt` identify the answers word by
word. Fresh exponents have the law of a uniform tape of `q(κ)` exponents drawn in advance, and T1
makes `D_b`'s output `A`'s guess against the tape of drawn exponents. Since `encG` is injective,
`0 < p ≤ 2^{wG(κ)} < 2^n`, so `statClose_sampleBelowL` puts each draw within `(1/2)^n` of uniform on
`Z_p`; the run is deterministic given the tape, so the two probabilities differ by at most
`q(κ) · (1/2)^n ≤ (q(κ) + 1) · 2^{−κ} = σ(κ)`. -/
theorem exists_bb1_distinguisher (H : Candidates.ArithmeticFP) (O : G.Ops) (A : NUPPT)
    (q : PolyExpr) :
    ∃ D : Bool → NUPPT, ∃ σ : ℕ → ℝ, Negligible σ ∧ ∀ (b real : Bool) (κ : ℕ),
      advantage (bb1SimGame G ℓ A (q.eval κ) b real κ) (G.dbdhGame (D b) real κ) ≤ σ κ := by
  obtain ⟨A', -, hA'⟩ := exists_toCompOn_of_toComp A
  -- the machines `D_b` of T1, for the handler with challenge bit `b`
  have hT1 := fun b : Bool => exists_handlerMachine A' q (BB1Machine.qLen G ℓ)
    (BB1Machine.aLen G ℓ) (.const 1) (BB1Machine.handler G ℓ O b q H)
  choose D hD using hT1
  refine ⟨D, fun κ => ((q.add (.const 1)).eval κ : ℝ) * (2 : ℝ)⁻¹ ^ κ,
    EnsembleLemmas.negligible_polyExpr_mul _ negligible_two_pow_neg, fun b real κ => ?_⟩
  obtain ⟨φ, hφ⟩ := hD b κ
  obtain ⟨φ', hφ'⟩ := hA' κ
  -- the draws' bound: `q(κ) · (1/2)^n ≤ σ(κ)`, as `κ ≤ n`
  have hbound : (q.eval κ : ℝ) * (1 / 2 : ℝ) ^ (BB1Machine.blockLen G).eval κ ≤
      ((q.add (.const 1)).eval κ : ℝ) * (2 : ℝ)⁻¹ ^ κ := by
    rw [PolyExpr.eval_add, PolyExpr.eval_const, BB1Machine.blockLen_eval, one_div]
    push_cast
    refine mul_le_mul (by linarith) (pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (by omega)) (by positivity) (by positivity)
  refine le_trans ?_ hbound
  -- both games as expectations; four averaging steps down to one tuple
  rw [advantage_eq, accept_eq, accept_eq, bb1SimGame_eq, BilinearGen.dbdhGame_eq,
    ProbComp.prob_eq_expect, ProbComp.prob_eq_expect]
  simp only [ProbComp.expect_bind, ProbComp.expect_pure]
  refine ProbComp.abs_expect_sub_le _ fun r => ?_
  rw [G.inst_eq κ r]
  refine ProbComp.abs_expect_sub_le _ fun g => ?_
  refine ProbComp.abs_expect_sub_le _ fun abc => ?_
  refine ProbComp.abs_expect_sub_le _ fun t => ?_
  exact BB1Machine.abs_expect_bb1Sim_sub_distinguisherL_le G ℓ H O A A' q b κ φ' hφ' (D b) φ hφ r
    g.1 _ _ _ _

end TCSlib.Cryptography.AdvancedEncryption.IdentityBased
