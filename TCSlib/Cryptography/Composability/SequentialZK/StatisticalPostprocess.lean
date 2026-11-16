/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Asymptotic.Sampling

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Statistical post-processing with an unused product coordinate

## Main definitions

This module introduces no definitions.

## Main results

* `statClose_map_fst` post-processes close samplers and removes a product coordinate
  on which the processed first sampler does not depend.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 175.1 (sequential repetition of zero knowledge).
-/

namespace TCSlib.Cryptography.Composability

/-- Suppose `X : α × β → γ` and `Y : τ → γ` are `ε`-close, and
`f (X r) = H r.1` for every `r : α × β`. If `β` is nonempty, then
`H` and `fun t => f (Y t)` are `ε`-close.
[PS10, Theorem 175.1, statistical post-processing of one phase].

**Proof sketch.** Apply the published statistical post-processing theorem to `f`.
For each output test, pointwise equality changes the first processed event to an event
of the first coordinate alone. The uniform-product projection law removes the unused
second coordinate, giving exactly the desired test bound. -/
theorem statClose_map_fst {α β τ γ δ : Type*} [Fintype α] [Fintype β] [Fintype τ]
    [Nonempty β] (X : α × β → γ) (Y : τ → γ) (f : γ → δ) (H : α → δ) (ε : ℝ)
    (hclose : StatClose X Y ε) (hfixed : ∀ r : α × β, f (X r) = H r.1) :
    StatClose H (fun t => f (Y t)) ε := by
  have hmap : StatClose (fun r : α × β => f (X r)) (fun t : τ => f (Y t)) ε :=
    StatClose.map (X := X) (Y := Y) hclose f
  apply (statClose_iff H (fun t : τ => f (Y t)) ε).2
  intro T
  have htest : |uprob (fun r : α × β => T (f (X r))) -
      uprob (fun t : τ => T (f (Y t)))| ≤ ε :=
    (statClose_iff (fun r : α × β => f (X r)) (fun t : τ => f (Y t)) ε).1 hmap T
  have hreal : uprob (fun r : α × β => T (f (X r))) =
      uprob (fun a : α => T (H a)) := by
    have hpoint : uprob (fun r : α × β => T (f (X r))) =
        uprob (fun r : α × β => T (H r.1)) :=
      OneWay.uprob_congr fun r => Iff.of_eq (congrArg T (hfixed r))
    exact hpoint.trans (uprob_fst (β := β) (fun a : α => T (H a)))
  rw [hreal] at htest
  exact htest

end TCSlib.Cryptography.Composability
