/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.DeterministicCC.OneWay
import TCSlib.CommunicationComplexity.NewmanTheorem.FiniteProbabilitySpace
import TCSlib.CommunicationComplexity.NewmanTheorem.CoinTape
import Mathlib.Data.ENat.Lattice

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# One-Way Public-Coin Protocols and Complexity

## Main results

- `PublicCoin.OneWay.Protocol`: One-way public-coin protocols defined as deterministic one-way
  protocols over shared randomness × input spaces.
- `PublicCoin.OneWay.Protocol.ApproxComputes`: A protocol ε-computes a function if for every
  input pair, the error probability over shared randomness is at most ε.
- `PublicCoin.OneWay.communicationComplexity`: The ε-error one-way public-coin communication
  complexity of a function, as the minimum one-way message cost over all approximating protocols.
- `PublicCoin.OneWay.communicationComplexity_mono`: Communication complexity is monotone in ε.

## References

- Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

namespace CommunicationComplexity
namespace PublicCoin
namespace OneWay

open MeasureTheory ProbabilityTheory

abbrev Protocol (Ω : Type*) (X Y α : Type*) :=
  CommunicationComplexity.Deterministic.OneWay.Protocol (Ω × X) (Ω × Y) α

namespace Protocol

variable {Ω X Y α : Type*}

/-- Execute a one-way public-coin protocol on inputs `x`, `y` with
shared randomness `ω`. -/
def rrun (p : Protocol Ω X Y α) (x : X) (y : Y) (ω : Ω) : α :=
  p.decode (p.send (ω, x)) (ω, y)

/-- A one-way public-coin protocol `ε`-computes `f` if for every input
pair `(x, y)`, the error probability over shared randomness is at most `ε`. -/
noncomputable def ApproxComputes
    [MeasureSpace Ω]
    (p : Protocol Ω X Y α) (f : X → Y → α) (ε : ℝ) : Prop :=
  ∀ x y,
    (volume {ω : Ω | p.rrun x y ω ≠ f x y}).toReal ≤ ε

end Protocol

/-- The `ε`-error one-way public-coin communication complexity of `f`,
defined as the minimum one-way message cost over all shared-randomness
protocols that compute `f` with error at most `ε` on every input. -/
noncomputable def communicationComplexity
    {X Y α} (f : X → Y → α) (ε : ℝ) : ENat :=
  ⨅ (n : ℕ)
    (p : Protocol (CoinTape n) X Y α)
    (_ : Protocol.ApproxComputes p f ε),
    (p.cost : ENat)

theorem communicationComplexity_le_iff
    {X Y α} (f : X → Y → α) (ε : ℝ) (m : ℕ) :
    communicationComplexity f ε ≤ m ↔
      ∃ (n : ℕ) (p : Protocol (CoinTape n) X Y α),
        Protocol.ApproxComputes p f ε ∧
        p.cost ≤ m := by
  unfold communicationComplexity
  simp only [Internal.enat_iInf_le_coe_iff, Nat.cast_le, exists_prop]

theorem le_communicationComplexity_iff
    {X Y α} (f : X → Y → α) (ε : ℝ) (m : ℕ) :
    (m : ENat) ≤ communicationComplexity f ε ↔
      ∀ (n : ℕ) (p : Protocol (CoinTape n) X Y α),
        Protocol.ApproxComputes p f ε →
        m ≤ p.cost := by
  unfold communicationComplexity
  simp only [le_iInf_iff, Nat.cast_le]

theorem communicationComplexity_mono
    {X Y α} (f : X → Y → α) {ε ε' : ℝ} (h : ε' ≤ ε) :
    communicationComplexity f ε ≤ communicationComplexity f ε' := by
  match hm : communicationComplexity f ε' with
  | ⊤ => exact le_top
  | (m : ℕ) =>
    obtain ⟨n, p, hp, hc⟩ :=
      (communicationComplexity_le_iff f ε' m).mp (le_of_eq hm)
    exact (communicationComplexity_le_iff f ε m).mpr
      ⟨n, p, fun x y => le_trans (hp x y) h, hc⟩

end OneWay
end PublicCoin
end CommunicationComplexity
