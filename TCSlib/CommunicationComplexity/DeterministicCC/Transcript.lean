/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.DeterministicCC.DetRectangle
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Syntactic Transcripts for Deterministic Protocols

## Main results

- `Deterministic.Protocol.Transcript`: The syntactic transcript type for a deterministic protocol,
  recording the full message sequence on a given execution path.
- `Deterministic.Protocol.card_transcript_le_two_pow_complexity`: A protocol has at most
  `2 ^ complexity` syntactic transcripts.

## References

- Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

namespace CommunicationComplexity

namespace Deterministic.Protocol

variable {X Y α : Type*}

/-- The syntactic transcript of a deterministic protocol.

For a fixed protocol, this is exactly the message sequence: terminal protocols have one
transcript, and each communication node contributes one Boolean plus the remaining child
transcript. -/
def Transcript : Protocol X Y α → Type _
  | .output _ => Unit
  | .alice _ P => Σ b : Bool, Transcript (P b)
  | .bob _ P => Σ b : Bool, Transcript (P b)

namespace Transcript

/-- The protocol output attached to a syntactic transcript. -/
def output : {p : Protocol X Y α} → Transcript p → α
  | .output val, _ => val
  | .alice _ _, t => output t.2
  | .bob _ _, t => output t.2

/-- The rectangle of inputs that follow a syntactic transcript. -/
def inputSet : {p : Protocol X Y α} → Transcript p → Set (X × Y)
  | .output _, _ => Set.univ
  | .alice f _, t => {xy | f xy.1 = t.1 ∧ inputSet t.2 xy}
  | .bob f _, t => {xy | f xy.2 = t.1 ∧ inputSet t.2 xy}

/-- The rectangle represented by a syntactic transcript is a rectangle. -/
theorem inputSet_isRectangle : {p : Protocol X Y α} → (t : Transcript p) →
    Rectangle.IsRectangle (inputSet t)
  | .output _, _ => ⟨Set.univ, Set.univ, by ext xy; simp [inputSet]⟩
  | .alice f P, t => by
      rcases t with ⟨b, t⟩
      rcases inputSet_isRectangle t with ⟨A, B, hAB⟩
      refine ⟨A ∩ {x | f x = b}, B, ?_⟩
      ext xy
      rcases xy with ⟨x, y⟩
      constructor
      · rintro ⟨hfx, ht⟩
        have hABmem : (x, y) ∈ A ×ˢ B := by
          simpa [hAB] using ht
        exact ⟨⟨hABmem.1, hfx⟩, hABmem.2⟩
      · rintro ⟨⟨hA, hfx⟩, hB⟩
        exact ⟨hfx, by simpa [hAB] using (show (x, y) ∈ A ×ˢ B from ⟨hA, hB⟩)⟩
  | .bob f P, t => by
      rcases t with ⟨b, t⟩
      rcases inputSet_isRectangle t with ⟨A, B, hAB⟩
      refine ⟨A, B ∩ {y | f y = b}, ?_⟩
      ext xy
      rcases xy with ⟨x, y⟩
      constructor
      · rintro ⟨hfy, ht⟩
        have hABmem : (x, y) ∈ A ×ˢ B := by
          simpa [hAB] using ht
        exact ⟨hABmem.1, hABmem.2, hfy⟩
      · rintro ⟨hA, hB, hfy⟩
        exact ⟨hfy, by simpa [hAB] using (show (x, y) ∈ A ×ˢ B from ⟨hA, hB⟩)⟩

end Transcript

noncomputable instance transcriptFintype : (p : Protocol X Y α) → Fintype (Transcript p)
  | .output _ => inferInstanceAs (Fintype Unit)
  | .alice _ P =>
      haveI : (b : Bool) → Fintype (Transcript (P b)) := fun b => transcriptFintype (P b)
      inferInstanceAs (Fintype (Σ b : Bool, Transcript (P b)))
  | .bob _ P =>
      haveI : (b : Bool) → Fintype (Transcript (P b)) := fun b => transcriptFintype (P b)
      inferInstanceAs (Fintype (Σ b : Bool, Transcript (P b)))

instance transcriptMeasurableSpace (p : Protocol X Y α) : MeasurableSpace (Transcript p) := ⊤

/-- Execute a protocol and return the syntactic transcript reached by the input. -/
def transcript : (p : Protocol X Y α) → X × Y → Transcript p
  | .output _, _ => ()
  | .alice f P, xy => ⟨f xy.1, transcript (P (f xy.1)) xy⟩
  | .bob f P, xy => ⟨f xy.2, transcript (P (f xy.2)) xy⟩

/-- The input follows its own transcript. -/
theorem mem_transcript : (p : Protocol X Y α) → (xy : X × Y) →
    xy ∈ Transcript.inputSet (p.transcript xy)
  | .output _, xy => by simp [Transcript.inputSet]
  | .alice f P, xy => by
      exact ⟨rfl, mem_transcript (P (f xy.1)) xy⟩
  | .bob f P, xy => by
      exact ⟨rfl, mem_transcript (P (f xy.2)) xy⟩

/-- If an input follows a syntactic transcript, then this is its computed transcript. -/
theorem transcript_eq_of_mem : {p : Protocol X Y α} → (t : Transcript p) → {xy : X × Y} →
    xy ∈ Transcript.inputSet t → p.transcript xy = t
  | .output _, _, _, _ => rfl
  | .alice f P, t, xy, hxy => by
      rcases t with ⟨b, t⟩
      rcases hxy with ⟨hb, ht⟩
      cases b
      · change ⟨f xy.1, (P (f xy.1)).transcript xy⟩ = (⟨false, t⟩ :
          Σ b : Bool, Transcript (P b))
        rw [hb]
        exact congrArg (Sigma.mk false) (transcript_eq_of_mem t ht)
      · change ⟨f xy.1, (P (f xy.1)).transcript xy⟩ = (⟨true, t⟩ :
          Σ b : Bool, Transcript (P b))
        rw [hb]
        exact congrArg (Sigma.mk true) (transcript_eq_of_mem t ht)
  | .bob f P, t, xy, hxy => by
      rcases t with ⟨b, t⟩
      rcases hxy with ⟨hb, ht⟩
      cases b
      · change ⟨f xy.2, (P (f xy.2)).transcript xy⟩ = (⟨false, t⟩ :
          Σ b : Bool, Transcript (P b))
        rw [hb]
        exact congrArg (Sigma.mk false) (transcript_eq_of_mem t ht)
      · change ⟨f xy.2, (P (f xy.2)).transcript xy⟩ = (⟨true, t⟩ :
          Σ b : Bool, Transcript (P b))
        rw [hb]
        exact congrArg (Sigma.mk true) (transcript_eq_of_mem t ht)

/-- The output attached to the reached transcript is the protocol output. -/
theorem run_eq_transcript_output : (p : Protocol X Y α) → (xy : X × Y) →
    p.run xy.1 xy.2 = Transcript.output (p.transcript xy)
  | .output _, xy => by rfl
  | .alice f P, xy => by
      exact run_eq_transcript_output (P (f xy.1)) xy
  | .bob f P, xy => by
      exact run_eq_transcript_output (P (f xy.2)) xy

/-- Inputs with the same transcript have the same protocol output. -/
theorem run_eq_of_transcript_eq
    (p : Protocol X Y α) {xy xy' : X × Y}
    (h : p.transcript xy = p.transcript xy') :
    p.run xy.1 xy.2 = p.run xy'.1 xy'.2 := by
  rw [run_eq_transcript_output p xy, run_eq_transcript_output p xy']
  exact congrArg Transcript.output h

private theorem card_transcript_le_two_pow_complexity_aux
    (a b ca cb : ℕ) (ha : a ≤ 2 ^ ca) (hb : b ≤ 2 ^ cb) :
    a + b ≤ 2 ^ (1 + max ca cb) := by
  have hac : 2 ^ ca ≤ 2 ^ max ca cb := Nat.pow_le_pow_right (by omega) (Nat.le_max_left ca cb)
  have hbc : 2 ^ cb ≤ 2 ^ max ca cb := Nat.pow_le_pow_right (by omega) (Nat.le_max_right ca cb)
  calc
    a + b ≤ 2 ^ max ca cb + 2 ^ max ca cb := Nat.add_le_add (ha.trans hac) (hb.trans hbc)
    _ = 2 ^ (1 + max ca cb) := by
      rw [show 1 + max ca cb = Nat.succ (max ca cb) by omega, pow_succ]
      omega

/-- A protocol has at most `2 ^ complexity` syntactic transcripts. -/
theorem card_transcript_le_two_pow_complexity : (p : Protocol X Y α) →
    Fintype.card (Transcript p) ≤ 2 ^ p.complexity
  | .output _ => by
      simp [Transcript, complexity]
  | .alice f P => by
      have hfalse := card_transcript_le_two_pow_complexity (P false)
      have htrue := card_transcript_le_two_pow_complexity (P true)
      rw [show Fintype.card (Transcript (Protocol.alice f P)) =
          Fintype.card (Transcript (P true)) + Fintype.card (Transcript (P false)) by
        change Fintype.card (Σ b : Bool, Transcript (P b)) =
          Fintype.card (Transcript (P true)) + Fintype.card (Transcript (P false))
        rw [Fintype.card_sigma, Fintype.sum_bool]]
      simpa [complexity, Nat.max_comm] using
        card_transcript_le_two_pow_complexity_aux
          (Fintype.card (Transcript (P true))) (Fintype.card (Transcript (P false)))
          (P true).complexity (P false).complexity htrue hfalse
  | .bob f P => by
      have hfalse := card_transcript_le_two_pow_complexity (P false)
      have htrue := card_transcript_le_two_pow_complexity (P true)
      rw [show Fintype.card (Transcript (Protocol.bob f P)) =
          Fintype.card (Transcript (P true)) + Fintype.card (Transcript (P false)) by
        change Fintype.card (Σ b : Bool, Transcript (P b)) =
          Fintype.card (Transcript (P true)) + Fintype.card (Transcript (P false))
        rw [Fintype.card_sigma, Fintype.sum_bool]]
      simpa [complexity, Nat.max_comm] using
        card_transcript_le_two_pow_complexity_aux
          (Fintype.card (Transcript (P true))) (Fintype.card (Transcript (P false)))
          (P true).complexity (P false).complexity htrue hfalse

/-- Swap a syntactic transcript by swapping Alice and Bob throughout the protocol. -/
def transcriptSwap : {p : Protocol X Y α} → Transcript p → Transcript p.swap
  | .output _, _ => ()
  | .alice _ _, t => ⟨t.1, transcriptSwap t.2⟩
  | .bob _ _, t => ⟨t.1, transcriptSwap t.2⟩

/-- Swapping Alice and Bob preserves the message sequence injectively. -/
theorem transcriptSwap_injective (p : Protocol X Y α) :
    Function.Injective (@transcriptSwap X Y α p) := by
  induction p with
  | output val =>
      intro a b h
      cases a
      cases b
      rfl
  | alice f P ih =>
      intro a b h
      rcases a with ⟨ba, ta⟩
      rcases b with ⟨bb, tb⟩
      cases ba <;> cases bb
      · have hchild : transcriptSwap ta = transcriptSwap tb := eq_of_heq (Sigma.mk.inj_iff.mp h).2
        exact congrArg (Sigma.mk false) (ih false hchild)
      · exact False.elim (Bool.noConfusion (Sigma.mk.inj_iff.mp h).1)
      · exact False.elim (Bool.noConfusion (Sigma.mk.inj_iff.mp h).1)
      · have hchild : transcriptSwap ta = transcriptSwap tb := eq_of_heq (Sigma.mk.inj_iff.mp h).2
        exact congrArg (Sigma.mk true) (ih true hchild)
  | bob f P ih =>
      intro a b h
      rcases a with ⟨ba, ta⟩
      rcases b with ⟨bb, tb⟩
      cases ba <;> cases bb
      · have hchild : transcriptSwap ta = transcriptSwap tb := eq_of_heq (Sigma.mk.inj_iff.mp h).2
        exact congrArg (Sigma.mk false) (ih false hchild)
      · exact False.elim (Bool.noConfusion (Sigma.mk.inj_iff.mp h).1)
      · exact False.elim (Bool.noConfusion (Sigma.mk.inj_iff.mp h).1)
      · have hchild : transcriptSwap ta = transcriptSwap tb := eq_of_heq (Sigma.mk.inj_iff.mp h).2
        exact congrArg (Sigma.mk true) (ih true hchild)

theorem transcriptSwap_transcript (p : Protocol X Y α) (x : X) (y : Y) :
    transcriptSwap (p.transcript (x, y)) = p.swap.transcript (y, x) := by
  induction p with
  | output val =>
      rfl
  | alice f P ih =>
      simp [transcript, transcriptSwap, swap, ih]
  | bob f P ih =>
      simp [transcript, transcriptSwap, swap, ih]

/-- Pull a syntactic transcript back along maps on Alice's and Bob's inputs. -/
def transcriptComap {X' Y' : Type*} : (p : Protocol X Y α) → (fX : X' → X) → (fY : Y' → Y) →
    Transcript p → Transcript (p.comap fX fY)
  | .output _, _, _, _ => ()
  | .alice _ P, fX, fY, t => ⟨t.1, transcriptComap (P t.1) fX fY t.2⟩
  | .bob _ P, fX, fY, t => ⟨t.1, transcriptComap (P t.1) fX fY t.2⟩

/-- Pulling a transcript back along input maps preserves the message sequence injectively. -/
theorem transcriptComap_injective {X' Y' : Type*} (p : Protocol X Y α) (fX : X' → X) (fY : Y' → Y) :
    Function.Injective (transcriptComap p fX fY) := by
  induction p with
  | output val =>
      intro a b h
      cases a
      cases b
      rfl
  | alice f P ih =>
      intro a b h
      rcases a with ⟨ba, ta⟩
      rcases b with ⟨bb, tb⟩
      cases ba <;> cases bb
      · have hchild : transcriptComap (P false) fX fY ta =
            transcriptComap (P false) fX fY tb :=
          eq_of_heq (Sigma.mk.inj_iff.mp h).2
        exact congrArg (Sigma.mk false) (ih false hchild)
      · exact False.elim (Bool.noConfusion (Sigma.mk.inj_iff.mp h).1)
      · exact False.elim (Bool.noConfusion (Sigma.mk.inj_iff.mp h).1)
      · have hchild : transcriptComap (P true) fX fY ta =
            transcriptComap (P true) fX fY tb :=
          eq_of_heq (Sigma.mk.inj_iff.mp h).2
        exact congrArg (Sigma.mk true) (ih true hchild)
  | bob f P ih =>
      intro a b h
      rcases a with ⟨ba, ta⟩
      rcases b with ⟨bb, tb⟩
      cases ba <;> cases bb
      · have hchild : transcriptComap (P false) fX fY ta =
            transcriptComap (P false) fX fY tb :=
          eq_of_heq (Sigma.mk.inj_iff.mp h).2
        exact congrArg (Sigma.mk false) (ih false hchild)
      · exact False.elim (Bool.noConfusion (Sigma.mk.inj_iff.mp h).1)
      · exact False.elim (Bool.noConfusion (Sigma.mk.inj_iff.mp h).1)
      · have hchild : transcriptComap (P true) fX fY ta =
            transcriptComap (P true) fX fY tb :=
          eq_of_heq (Sigma.mk.inj_iff.mp h).2
        exact congrArg (Sigma.mk true) (ih true hchild)

theorem transcriptComap_transcript {X' Y' : Type*} (p : Protocol X Y α) (fX : X' → X) (fY : Y' → Y)
    (x' : X') (y' : Y') :
    transcriptComap p fX fY (p.transcript (fX x', fY y')) =
      (p.comap fX fY).transcript (x', y') := by
  induction p with
  | output val =>
      rfl
  | alice f P ih =>
      simp [transcript, transcriptComap, comap, ih]
  | bob f P ih =>
      simp [transcript, transcriptComap, comap, ih]

end Deterministic.Protocol

end CommunicationComplexity
