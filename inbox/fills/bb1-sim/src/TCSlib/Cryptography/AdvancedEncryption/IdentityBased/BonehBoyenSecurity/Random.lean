/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Lazy
import TCSlib.Cryptography.Games.Relational

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The BB1 simulator on a random `T` does not depend on the challenge bit

Helper module of `AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean` (step 2 of
[BB04, proof of Theorem 4.1] at depth `ℓ = 1`): "when `T` is uniform and independent in `G_1`
… `C` is independent of `b` in the adversary's view" [BB04, proof of Theorem 4.1, *Challenge*].
`T` is used only at the first valid `Challenge`, so it can be drawn there
(`expect_simulate_bb1SimLazy`, step E-T); at that call, `T ↦ M_1^{−1} M_0 T` turns the answer
`M_0 · T` of the simulator with challenge bit `0` into the answer `M_1 · T'` of the one with
challenge bit `1`, and every other call is the same for both bits.

## Main definitions

None.

## Main results

* `BB1Sim.bb1SimLazy_random_call` — the lazy simulators with challenge bits `0` and `1` and
  `T` drawn at the challenge give equal expectations, call by call.
* `BB1Sim.expect_bb1SimImpl_random` — on a uniform `T`, the simulators with challenge bits `0`
  and `1` simulate alike.

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

variable (G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) (d : List Bool) (g X Y Z : (G.group κ d).G)

/-- **The challenge bit is hidden by a random `T`, call by call** [BB04, proof of Theorem 4.1,
*Challenge*]: with `T` drawn at the first valid `Challenge` (`zt T = (Z, T)`), every call of the
lazy simulators with challenge bits `0` and `1` gives the same expectation to every `F`:
`𝔼[F] (bb1SimLazy false … i x s) = 𝔼[F] (bb1SimLazy true … i x s)`.

**Proof sketch.** `Init` and `KeyGen` do not depend on the bit (`bb1SimLazy_zero`,
`bb1SimLazy_one`, `bb1SimImpl_eq`, `IBEScheme.oracleImpl_zero_onSpec`,
`IBEScheme.oracleImpl_one_onSpec`). A `Challenge` other than the first valid one answers `⊥` or
repeats the recorded challenge (`bb1SimLazy_two_of_not`, `bb1SimChal_none`, `bb1SimChal_repeat`,
`bb1SimChal_invalid`). At the first valid one, `ProbComp.expect_sample_rel` with `R := Eq` along
`T ↦ decodeT(M_1)^{−1} decodeT(M_0) T` (`bb1SimLazy_two_fresh`, `bb1SimChal_fresh`,
`ofFn_bb1SimCt`). -/
theorem bb1SimLazy_random_call (i : Fin 3) (x : ((bb1Scheme G ℓ).sidSpec κ).dom i)
    (s : BB1SimState G ℓ κ d) (F : ((bb1Scheme G ℓ).sidSpec κ).rng i × BB1SimState G ℓ κ d → ℝ) :
    ProbComp.expect (bb1SimLazy G ℓ false κ d g X Y (fun T : (G.group κ d).GT => (Z, T)) i x s) F =
      ProbComp.expect
        (bb1SimLazy G ℓ true κ d g X Y (fun T : (G.group κ d).GT => (Z, T)) i x s) F := by
  sorry

/-- **On a random `T`, the simulator does not depend on the challenge bit** [BB04, proof of
Theorem 4.1, *Challenge*, "when `T` is uniform and independent in `G_1` … `C` is independent of
`b` in the adversary's view"]: for every computation `c` and every `F` of its output,
`𝔼_{T ← G_T} 𝔼[F ∘ fst] (simulate (bb1SimImpl false … Z T) c (none, none)) =
𝔼_{T ← G_T} 𝔼[F ∘ fst] (simulate (bb1SimImpl true … Z T) c (none, none))`.

**Proof sketch.** Draw `T` at the first valid `Challenge` on both sides
(`expect_simulate_bb1SimLazy`, step E-T), then compare the lazy simulators call by call
(`ProbComp.expect_simulate_congr` with `bb1SimLazy_random_call`). -/
theorem expect_bb1SimImpl_random {β : Type} (c : OracleComp ((bb1Scheme G ℓ).sidSpec κ) β)
    (F : β → ℝ) :
    ProbComp.expect (ProbComp.sample (G.group κ d).GT) (fun T => ProbComp.expect
        (simulate (bb1SimImpl G ℓ false κ d g X Y Z T) c (none, none)) (fun p => F p.1)) =
      ProbComp.expect (ProbComp.sample (G.group κ d).GT) (fun T => ProbComp.expect
        (simulate (bb1SimImpl G ℓ true κ d g X Y Z T) c (none, none)) (fun p => F p.1)) := by
  rw [← expect_simulate_bb1SimLazy G ℓ false κ d g X Y (fun T : (G.group κ d).GT => (Z, T)) c _
    rfl, ← expect_simulate_bb1SimLazy G ℓ true κ d g X Y (fun T : (G.group κ d).GT => (Z, T)) c _
    rfl]
  exact ProbComp.expect_simulate_congr _ _
    (fun i x s F => bb1SimLazy_random_call G ℓ κ d g X Y Z i x s F) c _ _

end BB1Sim

end TCSlib.Cryptography.AdvancedEncryption.IdentityBased
