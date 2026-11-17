/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyen
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenMachine
import TCSlib.Cryptography.Pairing.Assumptions
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Lazy
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Real
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Coupling
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Random
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Chain

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Selective-identity security of BB1 under Decision BDH

[BB04, Theorem 4.1] at depth `ℓ = 1`: if Decision BDH holds in `G`, the BB1 system is
IND-sID-CPA secure. The proof [BB04, pp. 7–8] builds a Decision BDH algorithm `B` that, given
`(g, g^a, g^b, g^c, T)`, plays the selective-identity game with the adversary without knowing the
master key `g^{ab}`:
* **Setup**, once `ID*` is committed: a random `α_1 ∈ Z_p`, `h = g_1^{−ID*} g^{α_1}`,
  `params = (g, g_1 = g^a, g_2 = g^b, h)`, so that `F(x) = g_1^{x − ID*} g^{α_1}`;
* **private keys** for `ID ≠ ID*`: a random `r ∈ Z_p`,
  `(g_2^{−α_1/(ID − ID*)} F(ID)^r, g_2^{−1/(ID − ID*)} g^r)`;
* **the challenge**: `(M_b · T, g^c, (g^c)^{α_1})`.

**The simulation game.** `bb1SimGame` (defined beside the scheme in
`AdvancedEncryption/IdentityBased/BonehBoyen.lean`) is that simulator as a game of the `Games`
framework, with ideal uniform exponents, run against the adversary machine on a Decision BDH
tuple drawn from `P_BDH` (`real`) or `R_BDH`. The security proof has three named steps:
1. `bb1_sim_real`: on `P_BDH`, the simulation is the real game, except when distinct
   identities collide in `Z_p` (the generator's coins with `p < 2^ℓ`);
2. `bb1_sim_random`: on `R_BDH`, the simulation does not depend on the challenge bit;
3. `exists_bb1_distinguisher`: the simulation is, up to a negligible statistical term, the
   Decision BDH experiment of a non-uniform PPT distinguisher (the machine step: handler theorem
   T1 with exponents drawn from coin blocks). It is stated in its own module,
   `AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean`, so that it can be filled
   independently of steps 1 and 2 (ruling Q11 of `PairingCryptographyPlan.md`).
`bb1_sidSecure` assembles them by the triangle inequality.

**Deviation:** the paper's `B` draws the challenge bit itself and outputs `[b = b']`; here there
is one simulation per value of `b`, and the advantage of the two-experiment form is bounded by
the sum of two Decision BDH advantages; the paper's statement is concrete (`t' < t − Θ(τ ℓ q_S)`).

## Main definitions

None: the simulator (`bb1SimImpl`, `bb1SimGame`) is defined beside the scheme, in
`AdvancedEncryption.IdentityBased.BonehBoyen`.

## Contents

Steps 1 and 2 are proved in helper modules:

* `BonehBoyenSecurity.Lazy`: the simulator with its challenge coins drawn at the first valid
  `Challenge`, and its eager step.
* `BonehBoyenSecurity.Real`: the output of `Setup`, read; the real game with `h` recorded, and
  with `h` drawn at the first `Init`.
* `BonehBoyenSecurity.Coupling`: step M, the real game against the simulator call by call, on
  good coins.
* `BonehBoyenSecurity.Random`: on a random `T`, the simulator does not depend on the challenge
  bit.
* `BonehBoyenSecurity.Chain`: on good coins, the real game is the simulation on `P_BDH`.

## Main results

* `bb1_sim_real`, `bb1_sim_random` — steps 1 and 2 (step 3, `exists_bb1_distinguisher`, is in
  `AdvancedEncryption.IdentityBased.BonehBoyenMachine`).
* `bb1_sidSecure` — [BB04, Theorem 4.1] at depth one.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §4.2 (pp. 6–8): Theorem 4.1 and
  its proof; §4.4 (p. 8).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Definition 26.8, non-uniform PPT.)
-/

namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
  TCSlib.Cryptography.Composability

variable (G : BilinearGen) (ℓ : PolyExpr)

/-- **Step 1: on `P_BDH` the simulation is the real game** [BB04, proof of Theorem 4.1, "When
the input 5-tuple is sampled from `P_BDH` … `A`'s view is identical to its view in a real attack
game"], except on the generator's coins where `p < 2^ℓ`, where distinct identities may collide
in `Z_p`.

**Proof sketch.** Read `Setup` through `BB1Sim.setup_out` and condition both games on the
generator's coins `r` (`prob_bind`). On coins with `p < 2^ℓ` the two conditional acceptances are
probabilities, so they differ by at most `1`; averaging this pointwise bound
(`ProbComp.abs_expect_sub_le_expect`) gives `Pr_r[p < 2^ℓ]` (`Bridge.prob_sample_eq_uprob`). On
coins with `2^ℓ ≤ p` they are equal (`BB1Sim.prob_sidGame_coins`), by coupling the two games:
* the real `Setup` draws `h` before `ID*` exists; move it past `g_2` and the adversary's coins and
  draw it at the first `Init` (`ProbComp.expect_simulate_rel` with `h` recorded beside `ID*`, then
  `Games.expect_simulate_eager`);
* map `α ↦ a` and read `g_2` as `g^{b'}` (`pow_val_bijective_of_ne_one`, `expect_sample_equiv`);
* the real game and the simulator then agree call by call on states related by
  `h = g_1^{−ID*} g^{α_1}` (`ProbComp.expect_simulate_rel`, `ProbComp.expect_sample_rel`): at
  `Init`, `h ↦ α_1` is a bijection for each `ID*`, so `h` is uniform and the answers agree; for
  `ID ≠ ID*`, which stay distinct in `Z_p` because `idToZ` is injective on `ℓ`-bit strings
  (`bitsToNat_lt`, `bitsToNat_injective`, `CharP.natCast_injOn_Iio`), the simulated key with
  exponent `r` is the real key with exponent `r̃ = r − b'/(ID − ID*)`, a bijection of `Z_p` (the
  paper's computation, `pow_val_add`, `pow_val_neg`, `pow_val_mul`); the challenge is `Encrypt`
  with `s = c`, since `F(ID*) = g^{α_1}` and `e(g, g)^{ab'c} = e(g_1, g_2)^c` (`bilinear_pow`);
* finally the challenge coin `c` is drawn in advance (`Games.expect_simulate_eager`) and
  `(a, b', c)` merges into one draw (`Bridge.expect_sample_pair`); the unused `T` drops out. -/
theorem bb1_sim_real (A : NUPPT) (q : ℕ) (b : Bool) (κ : ℕ) :
    advantage ((bb1Scheme G ℓ).sidGame A q b κ) (bb1SimGame G ℓ A q b true κ) ≤
      uprob (fun r : G.gen.Coins κ => (G.inst κ r).order < 2 ^ ℓ.eval κ) := by
  obtain ⟨o, hset, hR⟩ := BB1Sim.setup_out G ℓ κ
  rw [advantage_eq, accept_eq, accept_eq, IBEScheme.sidGame_eq, hset, bb1SimGame_eq,
    ProbComp.prob_bind, ProbComp.prob_bind]
  -- average the pointwise bound `|F₀ r − F₁ r| ≤ 1[p < 2^ℓ]` over the generator's coins
  calc _ ≤ ProbComp.expect (ProbComp.sample (G.gen.Coins κ))
          (fun r => if (G.inst κ r).order < 2 ^ ℓ.eval κ then 1 else 0) :=
        ProbComp.abs_expect_sub_le_expect _ fun r => ?_
    _ = uprob (fun r : G.gen.Coins κ => (G.inst κ r).order < 2 ^ ℓ.eval κ) := by
        rw [← ProbComp.prob_eq_expect, Bridge.prob_sample_eq_uprob]
  have h01 : ∀ x y : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → |x - y| ≤ 1 := fun x y _ _ _ _ =>
    abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  by_cases hr : (G.inst κ r).order < 2 ^ ℓ.eval κ
  -- bad coins: two probabilities differ by at most `1`
  · rw [if_pos hr]
    exact h01 _ _ (ProbComp.prob_nonneg _ _) (ProbComp.prob_le_one _ _)
      (ProbComp.prob_nonneg _ _) (ProbComp.prob_le_one _ _)
  -- good coins: the chain of `BB1Sim.prob_sidGame_coins`
  · rw [if_neg hr]
    exact (abs_eq_zero.2 (sub_eq_zero.2 (BB1Sim.prob_sidGame_coins G ℓ A q b κ o hR r hr))).le

/-- **Step 2: on `R_BDH` the simulation does not depend on the challenge bit** [BB04, proof of
Theorem 4.1, "when `T` is uniform and independent in `G_1` … `C` is independent of `b` in the
adversary's view"].

**Proof sketch.** In the `R_BDH` game, `T` is uniform in `G_T` and is used only at the first
valid `Challenge`, in the first component `M_b · T` of the challenge. Exchange the sample of `T`
with the adversary's coins (`expect_sample_comm`) and draw it at that call
(`BB1Sim.expect_simulate_bb1SimLazy`, an instance of `expect_simulate_eager`). The simulators
with `b = 0` and `b = 1` then agree call by call (`ProbComp.expect_simulate_congr`): every other
call is the same for both bits, and at the first valid `Challenge` the bijection
`T ↦ M_1^{−1} M_0 · T` of `G_T` turns the answer `M_0 · T` into `M_1 · T'`
(`ProbComp.expect_sample_rel`). Challenges outside the message space are refused in both games.
So the acceptance probabilities are equal (`advantage_eq`). -/
theorem bb1_sim_random (A : NUPPT) (q : ℕ) (κ : ℕ) :
    advantage (bb1SimGame G ℓ A q false false κ) (bb1SimGame G ℓ A q true false κ) = 0 := by
  rw [advantage_eq, abs_eq_zero, sub_eq_zero, accept_eq, accept_eq, bb1SimGame_eq, bb1SimGame_eq]
  simp only [ProbComp.prob_bind, Bool.false_eq_true, if_false]
  refine congrArg _ (funext fun r => congrArg _ (funext fun g => congrArg _ (funext fun abc => ?_)))
  -- `T` is drawn before `A`'s coins: exchange them, then compare the two bits for each `ρ`
  conv_lhs => rw [ProbComp.expect_sample_comm]
  conv_rhs => rw [ProbComp.expect_sample_comm]
  exact congrArg _ (funext fun ρ => BB1Sim.expect_bb1SimImpl_random G ℓ κ _ _ _ _ _
    (A.toComp ((bb1Scheme G ℓ).sidCodec κ) κ q ρ) (fun a => ProbComp.prob (.pure (a 0)) (· = true)))

/-- **BB1 is IND-sID-CPA secure under Decision BDH** [BB04, Theorem 4.1, at depth `ℓ = 1`]: if
the generator's groups have efficient operations, the arithmetic bundle holds, the order is at
least `2^{ℓ(κ)}` except with negligible probability, and Decision BDH holds, then the BB1 system
for `ℓ(κ)`-bit identities is IND-sID-CPA secure.

**Deviation:** asymptotic form of the paper's concrete bound (`(t', q_S, ε)`-security from
`(t, ε)`-Decision BDH); the efficiency hypotheses `O` and `H` make the paper's simulator a
non-uniform PPT; `hN` makes distinct `ℓ`-bit identities distinct in `Z_p` (the condition
`2^b < p` of [BB04, §4.4]); the advantage is bounded by two Decision BDH advantages, one per
challenge bit, instead of one.

**Proof sketch.** By the triangle inequality through the simulation games and the Decision BDH
experiments of the two distinguishers `D_0`, `D_1` of step 3,
`advantage (sidGame … false) (sidGame … true)` is at most
`2 Pr_r[p < 2^ℓ] + 4σ(κ) + dbdhAdv D_0 κ + dbdhAdv D_1 κ` (steps 1 and 3 for each bit, step 2
in the middle). Each term is negligible (`hN`, step 3, `h`). -/
theorem bb1_sidSecure (H : Candidates.ArithmeticFP) (O : G.Ops)
    (hN : ∃ δ : ℕ → ℝ, Negligible δ ∧ G.OrderAtLeastExcept (fun κ => 2 ^ ℓ.eval κ) δ)
    (h : G.DBDHAssumption) : (bb1Scheme G ℓ).SIDSecure := by
  rw [IBEScheme.sidSecure_iff]
  intro A q
  obtain ⟨δ, hδ, hN⟩ := hN
  obtain ⟨D, σ, hσ, hD⟩ := exists_bb1_distinguisher G ℓ H O A q
  refine ⟨fun κ => 2 * δ κ + 4 * σ κ + (G.dbdhAdv (D false) κ + G.dbdhAdv (D true) κ),
    ((hδ.const_mul 2).add (hσ.const_mul 4)).add
      ((G.dbdhAssumption_iff.1 h (D false)).add (G.dbdhAssumption_iff.1 h (D true))), fun κ => ?_⟩
  have hu := (G.orderAtLeastExcept_iff _ δ).1 hN κ
  have t := fun G₀ G₁ G₂ : ProbComp Bool => advantage_triangle G₀ G₁ G₂
  have hc := fun G₀ G₁ : ProbComp Bool => advantage_comm G₀ G₁
  have s0 := bb1_sim_real G ℓ A (q.eval κ) false κ
  have s1 := bb1_sim_real G ℓ A (q.eval κ) true κ
  have s2 := bb1_sim_random G ℓ A (q.eval κ) κ
  have d0T := hD false true κ
  have d0F := hD false false κ
  have d1T := hD true true κ
  have d1F := hD true false κ
  have a0 := G.dbdhAdv_eq (D false) κ
  have a1 := G.dbdhAdv_eq (D true) κ
  set S0 := (bb1Scheme G ℓ).sidGame A (q.eval κ) false κ
  set S1 := (bb1Scheme G ℓ).sidGame A (q.eval κ) true κ
  set M0T := bb1SimGame G ℓ A (q.eval κ) false true κ
  set M0F := bb1SimGame G ℓ A (q.eval κ) false false κ
  set M1T := bb1SimGame G ℓ A (q.eval κ) true true κ
  set M1F := bb1SimGame G ℓ A (q.eval κ) true false κ
  set E0T := G.dbdhGame (D false) true κ
  set E0F := G.dbdhGame (D false) false κ
  set E1T := G.dbdhGame (D true) true κ
  set E1F := G.dbdhGame (D true) false κ
  have := t S0 M0T S1
  have := t M0T E0T S1
  have := t E0T E0F S1
  have := t E0F M0F S1
  have := t M0F M1F S1
  have := t M1F E1F S1
  have := t E1F E1T S1
  have := t E1T M1T S1
  have := hc E0T E0F
  have := hc E0F M0F
  have := hc E1T M1T
  have := hc M1T S1
  linarith

end TCSlib.Cryptography.AdvancedEncryption.IdentityBased
