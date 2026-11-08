/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.DeterministicCC.DetComplexity
import Mathlib.SetTheory.Cardinal.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Upper Bounds for Deterministic Communication Complexity

The trivial upper bounds on deterministic communication complexity, obtained from the
protocols in which one party sends its entire input and the other party either sends its
own input or computes and announces the answer [RY20, Ch. 1, §Equality: 'Alice sending her
input yields an (n+1)-bit protocol'], [Rou16, §1.7]. All three bounds are one application
each of a private lemma turning a finite-message protocol computing `f` into an upper
bound on `communicationComplexity f`.

## Main definitions

None.

## Main results

- `Deterministic.communicationComplexity_le_clog_card`: the deterministic communication
  complexity of any function on finite inputs is at most `⌈log₂ |X|⌉ + ⌈log₂ |Y|⌉`.
- `Deterministic.communicationComplexity_le_clog_card_X_alpha`: the deterministic
  communication complexity of `f : X → Y → α` is at most `⌈log₂ |X|⌉ + ⌈log₂ |α|⌉`.
- `Deterministic.communicationComplexity_le_clog_card_Y_alpha`: the deterministic
  communication complexity of `f : X → Y → α` is at most `⌈log₂ |Y|⌉ + ⌈log₂ |α|⌉`.

## References

* [RY20] A. Rao, A. Yehudayoff, *Communication Complexity and Applications*,
  Cambridge University Press, 2020.
* [Rou16] T. Roughgarden, *Communication Complexity (for Algorithm Designers)*,
  Foundations and Trends in Theoretical Computer Science 11(3–4), 2016; arXiv:1509.06257.
* [KN97] E. Kushilevitz, N. Nisan, *Communication Complexity*, Cambridge University
  Press, 1997.
* [Yao79] A. C.-C. Yao, "Some complexity questions related to distributive computing",
  *STOC 1979*, pp. 209–213.

Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal.
-/

namespace CommunicationComplexity

namespace Deterministic

/-- Any finite-message protocol `p` that computes `f` witnesses the upper bound
`communicationComplexity f ≤ c` for every `c` dominating `p.complexity`. Each of the three
public bounds in this file is a single application of this lemma to an explicit
two-message protocol. -/
private theorem communicationComplexity_le_of_finiteMessage_protocol
    {X Y α : Type} {f : X → Y → α} (p : FiniteMessage.Protocol X Y α)
    (hrun : p.run = f) {c : ℕ∞} (hc : (p.complexity : ℕ∞) ≤ c) :
    communicationComplexity f ≤ c :=
  -- Go through `p.toProtocol` directly (rather than `communicationComplexity_le_iff_finiteMessage`),
  -- which keeps the axiom footprint minimal (historically `ofProtocol_complexity` used
  -- `native_decide`; it no longer does, but the direct route is also the shorter one).
  ((communicationComplexity_le_iff f p.complexity).2
    ⟨p.toProtocol, (FiniteMessage.Protocol.toProtocol_run p).trans hrun,
      (FiniteMessage.Protocol.toProtocol_complexity p).le⟩).trans hc

/-- For finite input types, the deterministic communication complexity of any function
is at most `⌈log₂ |X|⌉ + ⌈log₂ |Y|⌉`, achieved by Alice sending her entire input
followed by Bob sending his [RY20, Ch. 1, §Equality: 'Alice sending her input yields an
(n+1)-bit protocol'], [Rou16, §1.7]. Deviation: [RY20] only states the trivial protocol
for specific functions (equality, disjointness); here it is stated for an arbitrary
function on finite inputs, and the protocol has both parties send their inputs. -/
theorem communicationComplexity_le_clog_card
    {X Y α : Type} [Finite X] [Finite Y] [Nonempty X] [Nonempty Y]
    (f : X → Y → α) :
    communicationComplexity f ≤
      Nat.clog 2 (Nat.card X) + Nat.clog 2 (Nat.card Y) := by
  haveI := Fintype.ofFinite X; haveI := Fintype.ofFinite Y
  exact communicationComplexity_le_of_finiteMessage_protocol
    (FiniteMessage.Protocol.alice id fun x =>
      FiniteMessage.Protocol.bob id fun y =>
        FiniteMessage.Protocol.output (f x y))
    -- Step 1: the protocol computes `f`
    (by ext x y; unfold FiniteMessage.Protocol.run; rfl)
    -- Step 2: its complexity is the claimed bound
    (by simp [FiniteMessage.Protocol.complexity, Nat.card_eq_fintype_card, Finset.sup_const])

/-- The deterministic communication complexity of `f` is at most `⌈log₂ |X|⌉ + ⌈log₂ |α|⌉`,
achieved by Alice sending her input, then Bob computing and sending the output
[RY20, Ch. 1, §Equality: 'Alice sending her input yields an (n+1)-bit protocol'],
[Rou16, §1.7]. Deviation: [RY20] only states the trivial protocol for specific functions
(equality, disjointness); here it is stated for an arbitrary function with finite `X` and
`α`. -/
theorem communicationComplexity_le_clog_card_X_alpha
    {X Y α : Type} [Finite X] [Finite α] [Nonempty X] [Nonempty α]
    (f : X → Y → α) :
    communicationComplexity f ≤
      Nat.clog 2 (Nat.card X) + Nat.clog 2 (Nat.card α) := by
  haveI := Fintype.ofFinite X; haveI := Fintype.ofFinite α
  exact communicationComplexity_le_of_finiteMessage_protocol
    (FiniteMessage.Protocol.alice id fun x =>
      FiniteMessage.Protocol.bob (f x) fun a =>
        FiniteMessage.Protocol.output a)
    -- Step 1: the protocol computes `f`
    (by ext x y; unfold FiniteMessage.Protocol.run; rfl)
    -- Step 2: its complexity is the claimed bound
    (by simp [FiniteMessage.Protocol.complexity, Nat.card_eq_fintype_card, Finset.sup_const])

/-- The deterministic communication complexity of `f` is at most `⌈log₂ |Y|⌉ + ⌈log₂ |α|⌉`,
achieved by Bob sending his input, then Alice computing and sending the output; the mirror
image of `communicationComplexity_le_clog_card_X_alpha`
[RY20, Ch. 1, §Equality: 'Alice sending her input yields an (n+1)-bit protocol'],
[Rou16, §1.7]. Deviation: [RY20] only states the trivial protocol for specific functions
(equality, disjointness); here it is stated for an arbitrary function with finite `Y` and
`α`. -/
theorem communicationComplexity_le_clog_card_Y_alpha
    {X Y α : Type} [Finite Y] [Finite α] [Nonempty Y] [Nonempty α]
    (f : X → Y → α) :
    communicationComplexity f ≤
      Nat.clog 2 (Nat.card Y) + Nat.clog 2 (Nat.card α) := by
  haveI := Fintype.ofFinite Y; haveI := Fintype.ofFinite α
  exact communicationComplexity_le_of_finiteMessage_protocol
    (FiniteMessage.Protocol.bob id fun y =>
      FiniteMessage.Protocol.alice (fun x => f x y) fun a =>
        FiniteMessage.Protocol.output a)
    -- Step 1: the protocol computes `f`
    (by ext x y; unfold FiniteMessage.Protocol.run; rfl)
    -- Step 2: its complexity is the claimed bound
    (by simp [FiniteMessage.Protocol.complexity, Nat.card_eq_fintype_card, Finset.sup_const])

end Deterministic

end CommunicationComplexity
