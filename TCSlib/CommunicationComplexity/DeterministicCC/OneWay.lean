/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.DeterministicCC.FiniteMessage
import TCSlib.CommunicationComplexity.DeterministicCC.DetComplexity
import Mathlib.Data.ENat.Lattice

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# One-Way Deterministic Communication Protocols

## Main results

- `Deterministic.OneWay.communicationComplexity`: One-way deterministic communication complexity
  of a function, defined as the infimum of bit costs over all one-way protocols computing it.
- `Deterministic.OneWay.deterministic_communicationComplexity_le_of_oneWay_le`: A one-way upper
  bound implies a deterministic upper bound with additive `⌈log₂ |α|⌉` overhead.

## References

- Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

namespace CommunicationComplexity
namespace Deterministic
namespace OneWay

variable {X Y α : Type*}

/-- A one-way deterministic communication protocol.

`Message` is the protocol's message codebook (language): the finite set of
admissible full one-shot messages Alice may send. It is not the base symbol
alphabet/signature (for example, bits), but whole message values (codewords). -/
structure Protocol (X Y α : Type*) where
  /-- The message codebook/language: all admissible complete one-shot messages. -/
  Message : Type
  /-- Finiteness of the message codebook, needed to assign a bit cost. -/
  [instFintypeMessage : Fintype Message]
  /-- Nonemptiness of the codebook (mirrors existing finite-message conventions). -/
  [instNonemptyMessage : Nonempty Message]
  /-- Alice's encoder: picks a codeword/message from the protocol codebook. -/
  send : X → Message
  /-- Bob's local decoder from received message and Bob's input. -/
  decode : Message → Y → α

attribute [instance] Protocol.instFintypeMessage Protocol.instNonemptyMessage

namespace Protocol

/-- Execute a one-way protocol on input `(x, y)`. -/
def run (p : Protocol X Y α) (x : X) (y : Y) : α :=
  p.decode (p.send x) y

/-- Protocol-level communication cost in bits:
`⌈log₂ |Message|⌉`, where `Message` is the protocol codebook/language. -/
def cost (p : Protocol X Y α) : ℕ :=
  Nat.clog 2 (Fintype.card p.Message)

/-- A one-way protocol computes `f` when its execution agrees with `f` everywhere. -/
def Computes (p : Protocol X Y α) (f : X → Y → α) : Prop :=
  p.run = f

/-- Embed a one-way protocol into the finite-message interactive model by
having Alice send the one-way message, then Bob send the decoded output. -/
noncomputable def toFiniteMessage [Fintype α] [Nonempty α]
    (p : Protocol X Y α) :
    Deterministic.FiniteMessage.Protocol X Y α :=
  .alice p.send (fun m =>
    .bob (β := Fin (Fintype.card α))
      (fun y => Fintype.equivFin α (p.decode m y))
      (fun a => .output ((Fintype.equivFin α).symm a)))

@[simp] theorem toFiniteMessage_run [Fintype α] [Nonempty α]
    (p : Protocol X Y α) (x : X) (y : Y) :
    Deterministic.FiniteMessage.Protocol.run (p.toFiniteMessage) x y = p.run x y := by
  simp [toFiniteMessage, run, Deterministic.FiniteMessage.Protocol.run]

@[simp] theorem toFiniteMessage_complexity [Fintype α] [Nonempty α]
    (p : Protocol X Y α) :
    (p.toFiniteMessage).complexity = p.cost + Nat.clog 2 (Fintype.card α) := by
  simp [toFiniteMessage, cost, Deterministic.FiniteMessage.Protocol.complexity,
    Finset.sup_const, Finset.univ_nonempty]

end Protocol

/-- One-way deterministic communication complexity of `f`:
the infimum, over one-way protocols computing `f`, of protocol bit cost. -/
noncomputable def communicationComplexity (f : X → Y → α) : ENat :=
  ⨅ (p : Protocol X Y α) (_ : Protocol.Computes p f), (Protocol.cost p : ENat)

/-- Characterization of one-way communication complexity bounds by existence of
a one-way protocol with bounded cost. -/
theorem communicationComplexity_le_iff (f : X → Y → α) (n : ℕ) :
    communicationComplexity f ≤ n ↔
      ∃ p : Protocol X Y α,
        Protocol.Computes p f ∧ Protocol.cost p ≤ n := by
  simp only [communicationComplexity,
    CommunicationComplexity.Internal.enat_iInf_le_coe_iff, Nat.cast_le, exists_prop]

theorem le_communicationComplexity_iff (f : X → Y → α) (k : ℕ) :
    (k : ENat) ≤ communicationComplexity f ↔
      ∀ p : Protocol X Y α, Protocol.Computes p f → k ≤ Protocol.cost p := by
  simp [communicationComplexity, le_iInf_iff, Nat.cast_le]

/-- A one-way upper bound yields a deterministic upper bound, with additive
`⌈log₂ |α|⌉` to let Bob send the decoded output in the interactive model. -/
theorem deterministic_communicationComplexity_le_of_oneWay_le
    [Fintype α] [Nonempty α]
    (f : X → Y → α) (n : ℕ)
    (h : communicationComplexity f ≤ n) :
    Deterministic.communicationComplexity f ≤ n + Nat.clog 2 (Fintype.card α) := by
  rcases (communicationComplexity_le_iff f n).mp h with ⟨p, hp, hcost⟩
  rw [← Nat.cast_add, Deterministic.communicationComplexity_le_iff_finiteMessage]
  refine ⟨p.toFiniteMessage, ?_, ?_⟩
  · ext x y
    calc
      Deterministic.FiniteMessage.Protocol.run (p.toFiniteMessage) x y
          = Protocol.run p x y := by
            simp
      _ = f x y := by
            simpa [Protocol.Computes] using congrFun (congrFun hp x) y
  · calc
      (p.toFiniteMessage).complexity
          = Protocol.cost p + Nat.clog 2 (Fintype.card α) := by
              simp
      _ ≤ n + Nat.clog 2 (Fintype.card α) :=
          Nat.add_le_add_right hcost _

/-- Same as `deterministic_communicationComplexity_le_of_oneWay_le` but specialized
to Bool. -/
theorem deterministic_communicationComplexity_le_of_oneWay_le_bool
    (f : X → Y → Bool) (n : ℕ)
    (h : OneWay.communicationComplexity f ≤ n) :
    Deterministic.communicationComplexity f ≤ n + 1 := by
  have h1 : Nat.clog 2 (Fintype.card Bool) = 1 := by native_decide
  have := OneWay.deterministic_communicationComplexity_le_of_oneWay_le (f := f) (n := n) h
  rw [h1] at this
  exact this



end OneWay
end Deterministic
end CommunicationComplexity
