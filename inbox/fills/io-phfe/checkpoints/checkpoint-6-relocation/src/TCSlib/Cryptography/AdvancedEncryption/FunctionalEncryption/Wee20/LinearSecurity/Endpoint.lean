/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Fresh
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Theorems

import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FiniteRandomness

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The linear security bound for the actual fresh raw algorithms

## Main definitions

This module adds no algorithm or alternate security predicate.

## Main results

* `Wee20.Linear.saGame_eq_freshSaGame`: a substantive acceptance-law equivalence from the
  padded unfiltered endpoints to actual fresh setup/encryption/key generation.
* `Wee20.Linear.saSimAdv_eq_freshSaSimAdv`: transfer of simulation advantage.
* `Wee20.Linear.linear_freshSaSimAdv_le`: the explicit two-reduction bound for those raw laws.

## References

* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive 2020/1420, §2.2, p. 5, §4.2,
  pp. 9–10, and Appendix B, Theorem 1, pp. 12–14.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear

open Complexity TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing

/-- Both unfiltered padded endpoints have EXACTLY the acceptance laws of actual fresh
setup, encryption and adaptive key generation [Wee20, §4.2, pp. 9–10]. This is a fresh-law
coupling statement, not a relabelling of the two padded endpoint definitions.

**Proof sketch.** Read the actual setup/enc/keyGen and simSetup/simEnc/simKey laws through
their published equation readers. Reindex the independent setup coordinates in the common
scalar tape; real setup ignores c,w,v and the simulator ignores the encryption seed.
For each function adaptively chosen from the past transcript, restrict a fresh padded
block by injective mCoord/tCoord and the disjoint final-output offset. The restriction of
uniform scalar functions is uniform on the actual function-dependent draw type, using
shared coordinate-sampling and equivalence readers. Reuse Games.expect_simulate_tapeImpl,
then Games.expect_simulate_abs_inv to discard unused blocks and relate the accepted-key
counter to fresh key calls; refusals preserve the invariant and sample no actual draw.
The honest encryption seed is independent of the selected challenge and all key blocks.
Use simulate_buildComp_detImpl_eq_pure for the padded interpreter and buildComp's published
query-cost bound for its TOTAL budget. Average pp and adversary coins. No rank condition
is imposed, so the singular total-inverse branch is coupled on the ideal side as well. -/
theorem saGame_eq_freshSaGame (G : BilinearGen) {ℓ n' : PolyExpr}
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr)
    (A : SAAdv G PG zDim) (ideal : Bool) (κ : ℕ) :
    accept (saGame G PG zDim A ideal κ) = accept (freshSaGame G PG zDim A ideal κ) := sorry

/-- The padded and actual fresh raw simulation advantages coincide
[Wee20, §2.2, p. 5; Appendix B, Theorem 1, p. 12].

**Proof sketch.** Read both advantage definitions, substitute both acceptance equalities
from saGame_eq_freshSaGame, and use the published advantage/acceptance reader. -/
theorem saSimAdv_eq_freshSaSimAdv (G : BilinearGen) {ℓ n' : PolyExpr}
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr)
    (A : SAAdv G PG zDim) (κ : ℕ) :
    saSimAdv G PG zDim A κ = freshSaSimAdv G PG zDim A κ := sorry

/-- Every typed adversary against the ACTUAL fresh raw laws has one advice family for
which every pair of realising machines satisfies the two-MDDH bound with one exact rank
loss [Wee20, Appendix B, Theorem 1, pp. 12–14].

**Proof sketch.** Use linear_saSimAdv_le with its existing explicit reduction functions,
then transfer its left side using saSimAdv_eq_freshSaSimAdv. This introduces no new
realisability premise and no extra statistical loss. -/
theorem linear_freshSaSimAdv_le (G : BilinearGen) {ℓ n' : PolyExpr}
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr)
    (p : ℕ → ℕ) (hp : ∀ κ r, (G.inst κ r).order = p κ) (A : SAAdv G PG zDim) :
    ∃ ω : Fin 2 → ∀ κ, Advice PG zDim A.budget p κ, ∀ D : Fin 2 → NUPPT,
      (D 0).RealizesOn (G.mddhEnc (PolyExpr.const 1) (PolyExpr.const 3)) A.coins
        (red0 G PG zDim p hp A (ω 0)) →
      (D 1).RealizesOn (G.mddhEnc ℓ (PG.mBound.mul A.budget)) A.coins
        (red1 G PG zDim p hp A (ω 1)) →
      ∀ κ, freshSaSimAdv G PG zDim A κ ≤
        G.mddhAdv (PolyExpr.const 1) (PolyExpr.const 3) (D 0) κ +
        G.mddhAdv ℓ (PG.mBound.mul A.budget) (D 1) κ + linearSlack G κ := sorry

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear
