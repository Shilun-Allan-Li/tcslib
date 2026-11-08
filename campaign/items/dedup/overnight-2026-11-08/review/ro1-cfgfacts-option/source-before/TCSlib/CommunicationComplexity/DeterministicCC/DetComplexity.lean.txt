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

The deterministic communication complexity `D(f)` of a function `f : X → Y → α`
[RY20, Ch. 1]: the least complexity of a protocol computing `f`, taken as an `ENat`
infimum so that it is `⊤` when no protocol computes `f`.

## Main definitions

- `Deterministic.communicationComplexity`: deterministic communication complexity as the
  infimum of complexities over all protocols that compute a given function.

## Main results

- `Deterministic.communicationComplexity_le_iff`: the complexity is at most `n` iff there exists
  a protocol computing the function with complexity at most `n`.
- `Deterministic.communicationComplexity_le_iff_finiteMessage`: equivalent characterization using
  finite-message protocols.
- `Deterministic.le_communicationComplexity_iff`: `n ≤ D(f)` iff every protocol computing `f`
  has complexity at least `n`.
- `Internal.enat_iInf_le_coe_iff`: an `ENat` infimum is at most a natural number `n` iff some
  term is.

## References

* [RY20] A. Rao, A. Yehudayoff, *Communication Complexity and Applications*,
  Cambridge University Press, 2020.
* [KN97] E. Kushilevitz, N. Nisan, *Communication Complexity*, Cambridge University
  Press, 1997.
* [Yao79] A. C.-C. Yao, "Some complexity questions related to distributive computing",
  *STOC 1979*, pp. 209–213.

Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal.
-/

namespace CommunicationComplexity

namespace Internal

/-- An infimum of extended naturals is at most a natural number `n` if and only if some term
of the family is at most `n`. (This uses that `n` is finite: an infimum of values all `≥ n + 1`
is `≥ n + 1`.) -/
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

/-- The deterministic communication complexity of `f : X → Y → α`: the minimum, over all
protocols computing `f`, of the protocol's complexity (worst-case number of bits exchanged).
[RY20, Ch. 1, Definition (computing a function, complexity, rounds)]. Deviation: defined as an
`ENat` infimum over protocols, so it is `⊤` when no protocol computes `f`; for finite nonempty
`X`, `Y` the value is finite (`UpperBounds.communicationComplexity_le_clog_card`). -/
noncomputable def communicationComplexity
    {X Y α : Type*} (f : X → Y → α) : ENat :=
  ⨅ (p : Protocol X Y α) (_ : p.Computes f),
    (p.complexity : ENat)

/-- The deterministic communication complexity of `f` is at most `n` if and only if some
protocol computes `f` using at most `n` bits. -/
theorem communicationComplexity_le_iff
    {X Y α : Type*} (f : X → Y → α) (n : ℕ) :
    communicationComplexity f ≤ n ↔
      ∃ p : Protocol X Y α,
        p.Computes f ∧ p.complexity ≤ n := by
  simp only [communicationComplexity,
    Internal.enat_iInf_le_coe_iff, Nat.cast_le, exists_prop]

/-- The deterministic communication complexity of `f` is at most `n` if and only if some
finite-message protocol (messages from arbitrary finite alphabets, charged `⌈log₂ |β|⌉` bits
each) computes `f` with complexity at most `n`. Both directions go through the translations
`FiniteMessage.Protocol.toProtocol` and `FiniteMessage.Protocol.ofProtocol`, which preserve
the outcome and the complexity. -/
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

/-- The deterministic communication complexity of `f` is at least `n` if and only if every
protocol computing `f` uses at least `n` bits. This is the form in which lower bounds are
proved. -/
theorem le_communicationComplexity_iff
    {X Y α : Type*} (f : X → Y → α) (n : ℕ) :
    (n : ENat) ≤ communicationComplexity f ↔
      ∀ p : Protocol X Y α,
        p.Computes f → n ≤ p.complexity := by
  simp only [communicationComplexity,
    le_iInf_iff, Nat.cast_le]

end Deterministic

end CommunicationComplexity
