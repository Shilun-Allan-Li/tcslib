/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import Mathlib.Data.ENat.Lattice
import TCSlib.CommunicationComplexity.DeterministicCC.DetBasic
import TCSlib.CommunicationComplexity.DeterministicCC.FiniteMessage

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Deterministic Communication Complexity

## Main results

- `Deterministic.communicationComplexity`: Definition of deterministic communication complexity
  as the infimum of complexities over all protocols that compute a given function.
- `Deterministic.communicationComplexity_le_iff`: The complexity is at most `n` iff there exists
  a protocol computing the function with complexity at most `n`.
- `Deterministic.communicationComplexity_le_iff_finiteMessage`: Equivalent characterization using
  finite-message protocols.

## References

- Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

namespace CommunicationComplexity

namespace Internal

@[simp]
theorem enat_iInf_le_coe_iff {ι : Sort*} {f : ι → ENat} {n : ℕ} :
    iInf f ≤ ↑n ↔ ∃ i, f i ≤ ↑n := by
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    apply not_lt.mpr h
    have : ∀ i, (↑(n + 1) : ENat) ≤ f i := fun i => by
      match f i, hne i with
      | none, _ => exact le_top
      | some m, hi =>
        exact WithTop.coe_le_coe.mpr
          (Nat.succ_le_of_lt (WithTop.coe_lt_coe.mp hi))
    exact lt_of_lt_of_le
      (WithTop.coe_lt_coe.mpr (Nat.lt_succ_self n))
      (le_iInf this)
  · rintro ⟨i, hi⟩
    exact (iInf_le f i).trans hi

end Internal

namespace Deterministic

noncomputable def communicationComplexity
    {X Y α : Type*} (f : X → Y → α) : ENat :=
  ⨅ (p : Protocol X Y α) (_ : p.Computes f),
    (p.complexity : ENat)

theorem communicationComplexity_le_iff
    {X Y α : Type*} (f : X → Y → α) (n : ℕ) :
    communicationComplexity f ≤ n ↔
      ∃ p : Protocol X Y α,
        p.Computes f ∧ p.complexity ≤ n := by
  simp only [communicationComplexity,
    Internal.enat_iInf_le_coe_iff, Nat.cast_le, exists_prop]

theorem communicationComplexity_le_iff_finiteMessage
    {X Y α : Type*} (f : X → Y → α) (n : ℕ) :
    communicationComplexity f ≤ n ↔
      ∃ p : FiniteMessage.Protocol X Y α,
        p.run = f ∧ p.complexity ≤ n := by
  rw [communicationComplexity_le_iff]
  constructor
  · rintro ⟨p, hp, hc⟩
    obtain ⟨P, hP_run, hP_comp⟩ :=
      FiniteMessage.Protocol.ofProtocol_equiv p
    exact ⟨P, hP_run.trans hp, hP_comp ▸ hc⟩
  · rintro ⟨p, hp, hc⟩
    exact ⟨p.toProtocol,
      (FiniteMessage.Protocol.toProtocol_run p).trans hp,
      FiniteMessage.Protocol.toProtocol_complexity p ▸ hc⟩

theorem le_communicationComplexity_iff
    {X Y α : Type*} (f : X → Y → α) (n : ℕ) :
    (n : ENat) ≤ communicationComplexity f ↔
      ∀ p : Protocol X Y α,
        p.Computes f → n ≤ p.complexity := by
  simp only [communicationComplexity,
    le_iInf_iff, Nat.cast_le]

end Deterministic

end CommunicationComplexity
