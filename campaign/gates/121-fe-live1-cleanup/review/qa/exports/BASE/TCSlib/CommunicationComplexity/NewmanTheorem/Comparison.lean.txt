/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.DeterministicCC.DetComplexity
import TCSlib.CommunicationComplexity.DeterministicCC.FiniteMessage
import TCSlib.CommunicationComplexity.NewmanTheorem.PrivateCoinComplexity
import TCSlib.CommunicationComplexity.NewmanTheorem.PublicCoinBasic
import TCSlib.CommunicationComplexity.NewmanTheorem.PublicCoinFiniteMessage

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Comparison Between Communication Complexity Models

## Main definitions

- `PublicCoin.Protocol.toDeterministic`, `PublicCoin.FiniteMessage.Protocol.toDeterministic`:
  fix the public randomness of a public-coin protocol, giving a deterministic protocol
- `Deterministic.FiniteMessage.Protocol.toPrivateCoin`: view a deterministic
  finite-message protocol as a private-coin protocol that ignores its coins

## Main results

- `PrivateCoin.communicationComplexity_le_deterministic`: private-coin communication
  complexity is at most deterministic communication complexity for any non-negative error

## References

* [RY20] A. Rao, A. Yehudayoff, *Communication Complexity and Applications*,
  Cambridge University Press, 2020.
* [KN97] E. Kushilevitz, N. Nisan, *Communication Complexity*, Cambridge University
  Press, 1997.

Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal.
-/

namespace CommunicationComplexity

open MeasureTheory ProbabilityTheory

/-- Fix the randomness of a binary public-coin protocol, producing a
deterministic protocol with the same complexity (via comap). -/
abbrev PublicCoin.Protocol.toDeterministic
    {Ω X Y α : Type*}
    (p : PublicCoin.Protocol Ω X Y α) (ω : Ω) :
    Deterministic.Protocol X Y α :=
  p.comap (Prod.mk ω) (Prod.mk ω)

/-- Running the deterministic protocol obtained by fixing the randomness `ω` on `(x, y)`
gives the same output as running the public-coin protocol on `(x, y)` with randomness
`ω`. -/
@[simp]
theorem PublicCoin.Protocol.toDeterministic_run
    {Ω X Y α : Type*}
    (p : PublicCoin.Protocol Ω X Y α) (ω : Ω)
    (x : X) (y : Y) :
    (p.toDeterministic ω).run x y = p.rrun x y ω := by
  simp [toDeterministic, PublicCoin.Protocol.rrun]

/-- Fixing the randomness of a public-coin protocol does not change its complexity (the
protocol tree is unchanged). -/
@[simp]
theorem PublicCoin.Protocol.toDeterministic_complexity
    {Ω X Y α : Type*}
    (p : PublicCoin.Protocol Ω X Y α) (ω : Ω) :
    (p.toDeterministic ω).complexity = p.complexity := by
  simp [toDeterministic]

/-- Convert a deterministic finite-message protocol to a private-coin
finite-message protocol by ignoring both coin spaces (via comap). -/
abbrev Deterministic.FiniteMessage.Protocol.toPrivateCoin
    {X Y α Ω_X Ω_Y : Type*}
    (p : Deterministic.FiniteMessage.Protocol X Y α) :
    PrivateCoin.FiniteMessage.Protocol Ω_X Ω_Y X Y α :=
  p.comap Prod.snd Prod.snd

/-- A deterministic finite-message protocol viewed as a private-coin protocol outputs, on
`(x, y)` and any coins `ω_x`, `ω_y`, the same value as the deterministic protocol on
`(x, y)`. -/
@[simp]
theorem Deterministic.FiniteMessage.Protocol.toPrivateCoin_rrun
    {X Y α Ω_X Ω_Y : Type*}
    (p : Deterministic.FiniteMessage.Protocol X Y α)
    (x : X) (y : Y) (ω_x : Ω_X) (ω_y : Ω_Y) :
    PrivateCoin.FiniteMessage.Protocol.rrun
      (p.toPrivateCoin (Ω_X := Ω_X) (Ω_Y := Ω_Y)) x y ω_x ω_y =
      p.run x y := by
  simp [toPrivateCoin, PrivateCoin.FiniteMessage.Protocol.rrun,
    Deterministic.FiniteMessage.Protocol.comap_run]

/-- Viewing a deterministic finite-message protocol as a private-coin protocol does not
change its complexity. -/
@[simp]
theorem Deterministic.FiniteMessage.Protocol.toPrivateCoin_complexity
    {X Y α Ω_X Ω_Y : Type*}
    (p : Deterministic.FiniteMessage.Protocol X Y α) :
    (p.toPrivateCoin (Ω_X := Ω_X) (Ω_Y := Ω_Y)).complexity =
      p.complexity := by
  simp [toPrivateCoin]

/-- Fix the randomness of a public-coin finite-message protocol,
producing a deterministic finite-message protocol with the same
complexity (via comap). -/
abbrev PublicCoin.FiniteMessage.Protocol.toDeterministic
    {Ω X Y α : Type*}
    (p : PublicCoin.FiniteMessage.Protocol Ω X Y α) (ω : Ω) :
    Deterministic.FiniteMessage.Protocol X Y α :=
  p.comap (Prod.mk ω) (Prod.mk ω)

/-- Running the deterministic finite-message protocol obtained by fixing the randomness
`ω` on `(x, y)` gives the same output as running the public-coin finite-message protocol
on `(x, y)` with randomness `ω`. -/
@[simp]
theorem PublicCoin.FiniteMessage.Protocol.toDeterministic_run
    {Ω X Y α : Type*}
    (p : PublicCoin.FiniteMessage.Protocol Ω X Y α) (ω : Ω)
    (x : X) (y : Y) :
    (p.toDeterministic ω).run x y = p.rrun x y ω := by
  simp [toDeterministic, rrun,
    Deterministic.FiniteMessage.Protocol.comap_run]

/-- Fixing the randomness of a public-coin finite-message protocol does not change its
complexity. -/
@[simp]
theorem PublicCoin.FiniteMessage.Protocol.toDeterministic_complexity
    {Ω X Y α : Type*}
    (p : PublicCoin.FiniteMessage.Protocol Ω X Y α) (ω : Ω) :
    (p.toDeterministic ω).complexity = p.complexity := by
  simp [toDeterministic]

/-- Private-coin communication complexity at any nonnegative error `ε` is at most
deterministic communication complexity: a deterministic protocol is a private-coin
protocol that ignores its coins and errs with probability `0 ≤ ε`.
[RY20, Ch. 3, §Variants of Randomized Protocols] ('every private-coin protocol is
simulable by a public-coin protocol'; likewise a deterministic protocol is a private-coin
protocol that ignores its coins).

**Proof sketch.** If the deterministic complexity is infinite there is nothing to prove;
otherwise it is some natural number `n`. (1) Pick a deterministic protocol `p` computing `f`
with complexity at most `n`. (2) Convert it to a finite-message protocol with the same run
and complexity. (3) By the finite-message characterisation of private-coin complexity it
suffices to view that protocol as a private-coin protocol over zero-bit coin tapes: it
computes `f` exactly, so its error `0` is at most `ε`, and its complexity is at most `n`. -/
theorem PrivateCoin.communicationComplexity_le_deterministic
    {X Y α} (f : X → Y → α) (ε : ℝ) (hε : 0 ≤ ε) :
    PrivateCoin.communicationComplexity f ε ≤
      Deterministic.communicationComplexity f := by
  match h : Deterministic.communicationComplexity f with
  | ⊤ => exact le_top
  | (n : ℕ) =>
    -- Get a deterministic protocol with complexity ≤ n
    obtain ⟨p, hp, hc⟩ :=
      (Deterministic.communicationComplexity_le_iff f n).mp (le_of_eq h)
    -- Convert to FiniteMessage, then to PrivateCoin via comap
    obtain ⟨pfm, hpfm_run, hpfm_comp⟩ :=
      Deterministic.FiniteMessage.Protocol.ofProtocol_equiv p
    rw [PrivateCoin.communicationComplexity_le_iff_finiteMessage]
    refine ⟨0, 0,
      pfm.toPrivateCoin (Ω_X := CoinTape 0) (Ω_Y := CoinTape 0), ?_, ?_⟩
    · -- ApproxComputes: error is 0 since protocol is deterministic
      intro x y
      have hp' : pfm.run x y = f x y := by
        have := congr_fun₂ hpfm_run x y
        rw [this]; exact congr_fun₂ hp x y
      simp [PrivateCoin.FiniteMessage.Protocol.rrun,
        Deterministic.FiniteMessage.Protocol.comap_run, hp', hε]
    · simp [hpfm_comp, hc]

end CommunicationComplexity
