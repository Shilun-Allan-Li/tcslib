/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.HardcoreBit.Basic
import TCSlib.Cryptography.OneWayFunctions.Basic
import Mathlib.Data.Fin.Tuple.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Marginals of the keys and coins of nested encryption

## Main definitions

This module adds no definitions.

## Main results

* `SecureComputation.GarblingCoins.pushesUniform_position_keys_coin`: two distinct key
  choices at one position and either nonce are an independent uniform triple.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.2, Claim 157.a (ii).
-/

namespace TCSlib.Cryptography.SecureComputation.GarblingCoins

open TCSlib.Cryptography

/-- Two distinct choices at one position and either coin form a uniform triple:
`(ks,(r₀,r₁)) ↦ (ks j b,ks j b',if c then r₁ else r₀)` pushes uniform to uniform,
for `b ≠ b'`. -/
theorem pushesUniform_position_keys_coin {K : Type} [Fintype K] [Nonempty K]
    {len : ℕ} (j : Fin len) {b b' : Bool} (hb : b ≠ b') (c : Bool) :
    HardcoreBit.PushesUniform (fun t : (Fin len → Bool → K) × (K × K) =>
      (t.1 j b, t.1 j b', if c then t.2.2 else t.2.1)) := by
  have hk := (HardcoreBit.pushesUniform_eval j).comp
    (HardcoreBit.pushesUniform_eval_pair (γ := K) hb)
  cases c
  · exact (hk.prodMap HardcoreBit.pushesUniform_fst).comp
      (HardcoreBit.pushesUniform_equiv (Equiv.prodAssoc K K K))
  · exact (hk.prodMap HardcoreBit.pushesUniform_snd).comp
      (HardcoreBit.pushesUniform_equiv (Equiv.prodAssoc K K K))

/-- A failure probability greater than `1-ε` bounds success strictly by `ε`:
`1-ε < Pr[X = none] → Pr[X.isSome = true] < ε`. -/
theorem uprob_isSome_lt_of_none {Ω α : Type} [Fintype Ω] [Nonempty Ω]
    (X : Ω → Option α) {ε : ℝ} (h : 1 - ε < uprob (fun t => X t = none)) :
    uprob (fun t => (X t).isSome = true) < ε := by
  rw [OneWay.uprob_congr (fun t : Ω => Option.isSome_iff_ne_none), uprob_not]
  linarith

end TCSlib.Cryptography.SecureComputation.GarblingCoins
