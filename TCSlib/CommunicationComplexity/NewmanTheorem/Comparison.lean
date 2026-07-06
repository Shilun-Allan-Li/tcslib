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

## Main results

- `PrivateCoin.communicationComplexity_le_deterministic`: private-coin communication complexity
  is at most deterministic communication complexity for any non-negative error

## References

- Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal
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

@[simp]
theorem PublicCoin.Protocol.toDeterministic_run
    {Ω X Y α : Type*}
    (p : PublicCoin.Protocol Ω X Y α) (ω : Ω)
    (x : X) (y : Y) :
    (p.toDeterministic ω).run x y = p.rrun x y ω := by
  simp [toDeterministic, PublicCoin.Protocol.rrun]

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

@[simp]
theorem PublicCoin.FiniteMessage.Protocol.toDeterministic_run
    {Ω X Y α : Type*}
    (p : PublicCoin.FiniteMessage.Protocol Ω X Y α) (ω : Ω)
    (x : X) (y : Y) :
    (p.toDeterministic ω).run x y = p.rrun x y ω := by
  simp [toDeterministic, rrun,
    Deterministic.FiniteMessage.Protocol.comap_run]

@[simp]
theorem PublicCoin.FiniteMessage.Protocol.toDeterministic_complexity
    {Ω X Y α : Type*}
    (p : PublicCoin.FiniteMessage.Protocol Ω X Y α) (ω : Ω) :
    (p.toDeterministic ω).complexity = p.complexity := by
  simp [toDeterministic]

/-- Private-coin communication complexity is at most deterministic
communication complexity (for any non-negative error). -/
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
