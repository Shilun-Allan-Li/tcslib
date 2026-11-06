/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.SavitchARM.Correct
import TCSlib.Complexity.SpaceComplexity.SavitchARM.Window
import TCSlib.Complexity.SpaceComplexity.Machines.ARMLoops

/-! The deepening fill's overlay (maintainer, pre-ship only): the owned file with its imports and
the pinned statements, `sorry` where the fill proves them. Not library code. -/

set_option autoImplicit false

namespace Complexity.LogProg.SavitchARM

open Turing Codec

/-- The deepening machine's contract: the hypothesis of `arm_decides_SPACE`, with registers of
`O((sp |x| + logSpace |x| + 1)²)` digits. -/
def DeepenContract (L : Language Bool) (sp : ℕ → ℕ) : Prop :=
  ∃ (m d : ℕ) (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (D : ARM m d Λ) (l₀ : Λ)
    (As : Fin d → Language Bool), (∀ j, As j ∈ LOGSPACE) ∧ ∃ C : ℕ, ∀ x : List Bool,
      AHalt D (fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V) x
        (fun a => PreS D x a ∧ ∀ r, (Nat.bits (a.2.1 r + 1)).length ≤
          C * (sp x.length + logSpace x.length + 1) ^ 2)
        (some l₀, fun _ => 0, none) (MultiTapeTM.indicator (L : Set (List Bool)) x)

/-- The fill's main theorem (pinned). -/
theorem deepen_contract {N : FinNDTM Bool} {L : Language Bool} {sp : ℕ → ℕ}
    (h : N.DecidesInSpace L sp) : DeepenContract L sp := sorry

end Complexity.LogProg.SavitchARM
