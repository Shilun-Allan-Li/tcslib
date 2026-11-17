/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Coupling
import TCSlib.Cryptography.Games.Bridges.Experiments

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# On good coins, the real BB1 game is the simulation on `P_BDH`

Helper module of `AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean` (step 1 of
[BB04, proof of Theorem 4.1] at depth `ℓ = 1`): "When the input 5-tuple is sampled from
`P_BDH` (where `T = e(g, g)^{abc}`) then `A`'s view is identical to its view in a real attack
game" [BB04, proof of Theorem 4.1, *Phase 2, Guess and the advantage*]. For generator coins `r`
with `2^ℓ ≤ p`, the chain of design r1 §3.1 equates the real game's acceptance, conditioned on
`r`, with the simulation game's on `P_BDH`:
1. move the setup's `h` past `g_2` and the adversary's coins, and draw it at the first `Init`
   (`expect_sample_sidImpl`: steps R1 and E-h);
2. read `g_2` as `g^{b'}` (`BilinearGroup.pow_val_bijective_of_ne_one`, `expect_sample_equiv`);
3. step M (`expect_simulate_bb1RealLazy`);
4. draw the challenge coin `c` in advance (`expect_simulate_bb1SimLazy`, step E-c), and merge
   `(a, b', c)` (`Bridge.expect_sample_pair`); the unused `T` drops out (`expect_const`).

## Main definitions

None.

## Main results

* `BB1Sim.prob_sidGame_coins` — on good coins, the real game's acceptance, conditioned on the
  generator's coins, is the simulation game's on `P_BDH`.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §4.2 (pp. 6–8): the proof of
  Theorem 4.1.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
  TCSlib.Cryptography.Composability

namespace BB1Sim

variable (G : BilinearGen) (ℓ : PolyExpr)

/-- **On good coins, the real game is the simulation on `P_BDH`** [BB04, proof of Theorem 4.1,
*Phase 2, Guess and the advantage*, "When the input 5-tuple is sampled from `P_BDH` … `A`'s view
is identical to its view in a real attack game"]: let `o` be the setup's output map, read as in
`setup_out`. For generator coins `r` with `2^{ℓ(κ)} ≤ p`, the real game after `r`
(`g ∈ G^*`, `α`, `h`, `g_2`, `A`'s coins, the game's oracles on `o r g α h g_2`) and the
simulation game after `r` on `P_BDH` (`g ∈ G^*`, `(a, b', c)`, `T`, `A`'s coins, the simulator
on `(g, g^a, g^{b'}, g^c, e(g, g)^{a b' c})`) accept with the same probability.

**Proof sketch.** Expand both probabilities into expectations (`prob_bind`) and fix `g` and
`α = a`. Move `h` inside past `g_2` and `A`'s coins (`expect_sample_comm`) and draw it at the
first `Init` (`expect_sample_sidImpl`). Read `g_2 = g^{b'}` (`expect_sample_equiv` along
`pow_val_bijective_of_ne_one`), so that `o … h (g^{b'})` reads as `(g, g^a, g^{b'}, h)`
(`setup_out`'s `RealReads`). Step M (`expect_simulate_bb1RealLazy`, with
`natCast`-injectivity of identities from `2^ℓ ≤ p`) and E-c (`expect_simulate_bb1SimLazy`) give
the simulator on `g^c`, `e(g, g)^{a b' c}` with `c` drawn in advance. On the simulation side,
`T` is unused (`expect_const`) and `(a, b', c)` splits into three draws
(`Bridge.expect_sample_pair`); `c` moves past `A`'s coins (`expect_sample_comm`). -/
theorem prob_sidGame_coins (A : NUPPT) (q : ℕ) (b : Bool) (κ : ℕ)
    (o : (r : G.gen.Coins κ) → {x : (G.group κ (G.desc κ r)).G // x ≠ 1} →
        ZMod (G.group κ (G.desc κ r)).order → (G.group κ (G.desc κ r)).G →
        (G.group κ (G.desc κ r)).G → (bb1Scheme G ℓ).PP κ × (bb1Scheme G ℓ).MSK κ)
    (hR : ∀ r g α h g2, RealReads G ℓ κ (G.desc κ r) g.1 α g2 h (o r g α h g2))
    (r : G.gen.Coins κ) (hr : ¬ (G.inst κ r).order < 2 ^ ℓ.eval κ) :
    ProbComp.prob ((ProbComp.sample {x : (G.group κ (G.desc κ r)).G // x ≠ 1}).bind fun g =>
      (ProbComp.sample (ZMod (G.group κ (G.desc κ r)).order)).bind fun α =>
      (ProbComp.sample (G.group κ (G.desc κ r)).G).bind fun h =>
      (ProbComp.sample (G.group κ (G.desc κ r)).G).bind fun g2 =>
      (ProbComp.sample (A.Coins κ)).bind fun ρ =>
      (simulate ((bb1Scheme G ℓ).sidImpl b κ (o r g α h g2).1 (o r g α h g2).2)
        (A.toComp ((bb1Scheme G ℓ).sidCodec κ) κ q ρ) (none, none)).bind
        fun res => .pure (res.1 0)) (· = true) =
    ProbComp.prob ((ProbComp.sample {x : (G.group κ (G.desc κ r)).G // x ≠ 1}).bind fun g =>
      (ProbComp.sample (ZMod (G.group κ (G.desc κ r)).order ×
        ZMod (G.group κ (G.desc κ r)).order × ZMod (G.group κ (G.desc κ r)).order)).bind
        fun abc =>
      (ProbComp.sample (G.group κ (G.desc κ r)).GT).bind fun t =>
      (ProbComp.sample (A.Coins κ)).bind fun ρ =>
      (simulate (bb1SimImpl G ℓ b κ (G.desc κ r) g.1 (g.1 ^ abc.1.val) (g.1 ^ abc.2.1.val)
          (g.1 ^ abc.2.2.val)
          (if true then (G.group κ (G.desc κ r)).pair g.1 g.1 ^ (abc.1 * abc.2.1 * abc.2.2).val
            else t))
        (A.toComp ((bb1Scheme G ℓ).sidCodec κ) κ q ρ) (none, none)).bind
        fun res => .pure (res.1 0)) (· = true) := by
  sorry

end BB1Sim

end TCSlib.Cryptography.AdvancedEncryption.IdentityBased
