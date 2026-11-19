/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Pairing.MatrixDH.Parameters
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenMachine.Draws

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Scalar word widths for fixed order schedules

## Main definitions

This module introduces no definitions.

## Main results

* `orderSchedule_le_two_pow`: every scheduled order fits the public source-group width.

## References

* TCSlib contributors, *TCSlib*, `Pairing/Group.lean`, generated group descriptions,
  and `IdentityBased/BonehBoyenMachine/Draws.lean`, `order_le_two_pow`.

This proof adapter keeps the description-width argument separate from public parameter types.
-/

namespace TCSlib.Cryptography.Pairing

open Complexity

/-- A fixed schedule agreeing with every generated group order fits the source-group
encoding width: `p(κ) ≤ 2^{wG(κ)}`. This is scalar-word width transport from the existing
injective group-encoding bound.

**Proof sketch.** Use the all-false generator coins at κ. Read the schedule hypothesis
and the generated-instance equation, then apply the existing whole group-order bound
for that generated description. -/
theorem orderSchedule_le_two_pow (G : BilinearGen) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (κ : ℕ) :
    p κ ≤ 2 ^ (G.wG.eval κ) := by
  rw [← hp κ (fun _ => false), G.inst_eq κ (fun _ => false)]
  exact TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Machine.order_le_two_pow
    G κ (G.desc κ (fun _ => false))

end TCSlib.Cryptography.Pairing
