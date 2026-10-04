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

The syntactic transcript of a deterministic protocol on an input is the sequence of bits sent
along the root-to-leaf path that the input follows [RY20, Ch. 1, Definition (outcome)]. This
file defines the type of transcripts of a protocol, the map sending an input to its transcript,
the set of inputs sharing a transcript (a combinatorial rectangle), and the transport of
transcripts along `Protocol.swap` and `Protocol.comap`. The main counting result is that a
protocol of complexity `c` has at most `2 ^ c` transcripts.

## Main definitions

- `Deterministic.Protocol.Transcript`: the type of syntactic transcripts of a protocol, i.e.
  the possible message sequences along a root-to-leaf path.
- `Deterministic.Protocol.Transcript.inputSet`: the set of inputs that follow a given
  transcript; `Deterministic.Protocol.Transcript.output` is the output at its leaf.
- `Deterministic.Protocol.transcript`: the transcript reached by an input.
- `Deterministic.Protocol.transcriptSwap`, `Deterministic.Protocol.transcriptComap`: transport
  of transcripts along `Protocol.swap` and `Protocol.comap`.

## Main results

- `Deterministic.Protocol.Transcript.inputSet_isRectangle`: the inputs following a transcript
  form a combinatorial rectangle.
- `Deterministic.Protocol.mem_transcript`, `Deterministic.Protocol.transcript_eq_of_mem`: the
  input sets of transcripts are exactly the fibres of `transcript`.
- `Deterministic.Protocol.card_transcript_le_two_pow_complexity`: a protocol has at most
  `2 ^ complexity` syntactic transcripts.
- `Deterministic.Protocol.transcriptSwap_injective`,
  `Deterministic.Protocol.transcriptComap_injective`: the transports are injective.

## References

* [RY20] A. Rao, A. Yehudayoff, *Communication Complexity and Applications*,
  Cambridge University Press, 2020.
* [Rou16] T. Roughgarden, *Communication Complexity (for Algorithm Designers)*,
  Foundations and Trends in Theoretical Computer Science 11(3–4), 2016; arXiv:1509.06257.
* [KN97] E. Kushilevitz, N. Nisan, *Communication Complexity*, Cambridge University Press,
  1997.

Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal.
-/

namespace CommunicationComplexity

namespace Deterministic.Protocol

variable {X Y α : Type*}

/-- The type of syntactic transcripts of a deterministic protocol: one transcript for each
root-to-leaf path of the protocol tree, recording the bit sent at every communication node
along that path [RY20, Ch. 1, Definition (outcome)] (the transcript is the message sequence of
an execution; see also [Rou16, §4.2.4]).

For a fixed protocol, this is exactly the message sequence: terminal protocols have one
transcript, and each communication node contributes one Boolean plus the remaining child
transcript. -/
def Transcript : Protocol X Y α → Type _
  | .output _ => Unit
  | .alice _ P => Σ b : Bool, Transcript (P b)
  | .bob _ P => Σ b : Bool, Transcript (P b)

namespace Transcript

/-- The output value at the leaf reached by a syntactic transcript. -/
def output : {p : Protocol X Y α} → Transcript p → α
  | .output val, _ => val
  | .alice _ _, t => output t.2
  | .bob _ _, t => output t.2

/-- The set of inputs `(x, y)` on which the protocol sends exactly the bits recorded in a
syntactic transcript `t`; by `inputSet_isRectangle` it is a combinatorial rectangle. -/
def inputSet : {p : Protocol X Y α} → Transcript p → Set (X × Y)
  | .output _, _ => Set.univ
  | .alice f _, t => {xy | f xy.1 = t.1 ∧ inputSet t.2 xy}
  | .bob f _, t => {xy | f xy.2 = t.1 ∧ inputSet t.2 xy}

/-- For every syntactic transcript `t` of a protocol, the set of inputs that follow `t` is a
combinatorial rectangle `A ×ˢ B` [RY20, Lemma 1.6] / [Rou16, Lemma 4.1]. This is the
rectangle half of the leaf-partition lemma; the partition and monochromaticity statements are
`Deterministic.Protocol.rectangle_partition`.

**Proof sketch.** Induction on the protocol, with the transcript split as a first bit `b`
followed by a transcript `t'` of the child reached on `b`. Step 1: a terminal protocol has
the single transcript `()`, whose input set is everything, i.e. `univ ×ˢ univ`. Step 2: at an
Alice node with message function `f`, the input set of `(b, t')` consists of the pairs
`(x, y)` with `f x = b` that follow `t'`; by the induction hypothesis the latter form a
rectangle `A ×ˢ B`, so the input set is `(A ∩ {x | f x = b}) ×ˢ B`, checked by the two
pointwise inclusions. Step 3: at a Bob node the same argument refines the second factor to
`B ∩ {y | f y = b}`. -/
theorem inputSet_isRectangle : {p : Protocol X Y α} → (t : Transcript p) →
    Rectangle.IsRectangle (inputSet t)
  -- Step 1: terminal protocol, input set `univ ×ˢ univ`.
  | .output _, _ => ⟨Set.univ, Set.univ, by ext xy; simp [inputSet]⟩
  -- Step 2: Alice node; refine the first factor of the child's rectangle by `f x = b`.
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
  -- Step 3: Bob node; refine the second factor of the child's rectangle by `f y = b`.
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

/-- The syntactic transcript reached by an input `(x, y)`: run the protocol on `(x, y)` and
record the bit sent at every communication node along the way
[RY20, Ch. 1, Definition (outcome)] / [Rou16, §4.2.4]. -/
def transcript : (p : Protocol X Y α) → X × Y → Transcript p
  | .output _, _ => ()
  | .alice f P, xy => ⟨f xy.1, transcript (P (f xy.1)) xy⟩
  | .bob f P, xy => ⟨f xy.2, transcript (P (f xy.2)) xy⟩

/-- Every input lies in the input set of the transcript it reaches. -/
theorem mem_transcript : (p : Protocol X Y α) → (xy : X × Y) →
    xy ∈ Transcript.inputSet (p.transcript xy)
  | .output _, xy => by simp [Transcript.inputSet]
  | .alice f P, xy => by
      exact ⟨rfl, mem_transcript (P (f xy.1)) xy⟩
  | .bob f P, xy => by
      exact ⟨rfl, mem_transcript (P (f xy.2)) xy⟩

/-- If an input `xy` lies in the input set of a syntactic transcript `t`, then the transcript
reached by `xy` is `t`. Together with `mem_transcript`, the input sets of transcripts are
exactly the fibres of `transcript`.

**Proof sketch.** Induction on the protocol. Step 1: a terminal protocol has a unique
transcript, so both sides are `()`. Step 2: at an Alice node, write `t = (b, t')`; the
hypothesis says `f x = b` and that `xy` follows `t'`. Splitting on `b`, rewrite the first
component of the reached transcript with `f x = b` and apply the induction hypothesis to the
second component, so both components of the dependent pair agree. Step 3: at a Bob node the
same argument applies with the bit `f y`. -/
theorem transcript_eq_of_mem : {p : Protocol X Y α} → (t : Transcript p) → {xy : X × Y} →
    xy ∈ Transcript.inputSet t → p.transcript xy = t
  -- Step 1: terminal protocol, unique transcript.
  | .output _, _, _, _ => rfl
  -- Step 2: Alice node; rewrite the bit with `f x = b`, then use the induction hypothesis.
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
  -- Step 3: Bob node; same with the bit `f y`.
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

/-- The protocol output on an input equals the output at the leaf of the transcript that the
input reaches. -/
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

/-- Arithmetic step for `card_transcript_le_two_pow_complexity`: if `a ≤ 2 ^ ca` and
`b ≤ 2 ^ cb`, then `a + b ≤ 2 ^ (1 + max ca cb)`. -/
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

/-- A protocol of communication complexity `c` has at most `2 ^ c` syntactic transcripts,
equivalently at most `2 ^ c` leaves [RY20, Lemma 1.2].

**Proof sketch.** Induction on the protocol. Step 1: a terminal protocol has one transcript
and complexity `0`. Step 2: at an Alice node the transcripts are the disjoint union of the
transcripts of the two children, so their number is the sum of the two children's counts
(the cardinality of a sigma type over `Bool`). Step 3: bound each summand by the induction
hypothesis and combine with the arithmetic fact `2 ^ c₀ + 2 ^ c₁ ≤ 2 ^ (1 + max c₀ c₁)`,
whose right-hand side is `2 ^` the complexity of the node. Step 4: a Bob node is handled
identically. -/
theorem card_transcript_le_two_pow_complexity : (p : Protocol X Y α) →
    Fintype.card (Transcript p) ≤ 2 ^ p.complexity
  -- Step 1: terminal protocol, one transcript.
  | .output _ => by
      simp [Transcript, complexity]
  | .alice f P => by
      have hfalse := card_transcript_le_two_pow_complexity (P false)
      have htrue := card_transcript_le_two_pow_complexity (P true)
      -- Step 2: the transcript count is the sum of the two children's counts.
      rw [show Fintype.card (Transcript (Protocol.alice f P)) =
          Fintype.card (Transcript (P true)) + Fintype.card (Transcript (P false)) by
        change Fintype.card (Σ b : Bool, Transcript (P b)) =
          Fintype.card (Transcript (P true)) + Fintype.card (Transcript (P false))
        rw [Fintype.card_sigma, Fintype.sum_bool]]
      -- Step 3: induction hypotheses plus `2 ^ c₀ + 2 ^ c₁ ≤ 2 ^ (1 + max c₀ c₁)`.
      simpa [complexity, Nat.max_comm] using
        card_transcript_le_two_pow_complexity_aux
          (Fintype.card (Transcript (P true))) (Fintype.card (Transcript (P false)))
          (P true).complexity (P false).complexity htrue hfalse
  -- Step 4: Bob node, identical to Steps 2–3.
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

/-- The transcript of the swapped protocol `p.swap` carrying the same message sequence as a
given transcript of `p`; since swapping only exchanges the roles of the two players, the
bits sent along a path are unchanged. -/
def transcriptSwap : {p : Protocol X Y α} → Transcript p → Transcript p.swap
  | .output _, _ => ()
  | .alice _ _, t => ⟨t.1, transcriptSwap t.2⟩
  | .bob _ _, t => ⟨t.1, transcriptSwap t.2⟩

/-- Injectivity of a `Bool`-indexed family of maps lifts to the map on `Σ b : Bool, _` that keeps
the index and applies the family fibrewise. -/
private theorem sigma_map_bool_injective {β γ : Bool → Type*} (g : (b : Bool) → β b → γ b)
    (hg : ∀ b, Function.Injective (g b)) :
    Function.Injective (fun t : Σ b : Bool, β b => (⟨t.1, g t.1 t.2⟩ : Σ b : Bool, γ b)) := by
  rintro ⟨ba, ta⟩ ⟨bb, tb⟩ h
  cases ba <;> cases bb
  · exact congrArg (Sigma.mk false) (hg false (eq_of_heq (Sigma.mk.inj_iff.mp h).2))
  · exact False.elim (Bool.noConfusion (Sigma.mk.inj_iff.mp h).1)
  · exact False.elim (Bool.noConfusion (Sigma.mk.inj_iff.mp h).1)
  · exact congrArg (Sigma.mk true) (hg true (eq_of_heq (Sigma.mk.inj_iff.mp h).2))

/-- `transcriptSwap` is injective: two transcripts of `p` with the same swapped transcript
are equal.

**Proof sketch.** Induction on the protocol. Step 1: a terminal protocol has a single
transcript. Step 2: at a communication node the map keeps the first bit and applies the
recursive map to the tail, so injectivity follows from the children's injectivity by the
general fact that a fibrewise-injective map on a `Bool`-indexed sigma type is injective. -/
theorem transcriptSwap_injective (p : Protocol X Y α) :
    Function.Injective (@transcriptSwap X Y α p) := by
  induction p with
  -- Step 1: a terminal protocol has the single transcript `()`.
  | output val => intro a b _; cases a; cases b; rfl
  -- Step 2: at a communication node `transcriptSwap` keeps the bit and recurses on the child,
  -- so injectivity follows from the children by `sigma_map_bool_injective`.
  | alice f P ih => exact sigma_map_bool_injective (fun b => transcriptSwap) ih
  | bob f P ih => exact sigma_map_bool_injective (fun b => transcriptSwap) ih

/-- The transcript that the swapped protocol `p.swap` reaches on `(y, x)` is the swap of the
transcript that `p` reaches on `(x, y)`. -/
theorem transcriptSwap_transcript (p : Protocol X Y α) (x : X) (y : Y) :
    transcriptSwap (p.transcript (x, y)) = p.swap.transcript (y, x) := by
  induction p with
  | output val =>
      rfl
  | alice f P ih =>
      simp [transcript, transcriptSwap, swap, ih]
  | bob f P ih =>
      simp [transcript, transcriptSwap, swap, ih]

/-- The transcript of the pulled-back protocol `p.comap fX fY` carrying the same message
sequence as a given transcript of `p`; precomposing the message functions with `fX` and `fY`
does not change the shape of the protocol tree. -/
def transcriptComap {X' Y' : Type*} : (p : Protocol X Y α) → (fX : X' → X) → (fY : Y' → Y) →
    Transcript p → Transcript (p.comap fX fY)
  | .output _, _, _, _ => ()
  | .alice _ P, fX, fY, t => ⟨t.1, transcriptComap (P t.1) fX fY t.2⟩
  | .bob _ P, fX, fY, t => ⟨t.1, transcriptComap (P t.1) fX fY t.2⟩

/-- `transcriptComap p fX fY` is injective: two transcripts of `p` with the same pulled-back
transcript are equal.

**Proof sketch.** Induction on the protocol. Step 1: a terminal protocol has a single
transcript. Step 2: at a communication node the map keeps the first bit and applies the
recursive map to the tail, so injectivity follows from the children's injectivity by the
general fact that a fibrewise-injective map on a `Bool`-indexed sigma type is injective. -/
theorem transcriptComap_injective {X' Y' : Type*} (p : Protocol X Y α) (fX : X' → X) (fY : Y' → Y) :
    Function.Injective (transcriptComap p fX fY) := by
  induction p with
  -- Step 1: a terminal protocol has the single transcript `()`.
  | output val => intro a b _; cases a; cases b; rfl
  -- Step 2: at a communication node `transcriptComap` keeps the bit and recurses on the child,
  -- so injectivity follows from the children by `sigma_map_bool_injective`.
  | alice f P ih => exact sigma_map_bool_injective (fun b => transcriptComap (P b) fX fY) ih
  | bob f P ih => exact sigma_map_bool_injective (fun b => transcriptComap (P b) fX fY) ih

/-- The transcript that the pulled-back protocol `p.comap fX fY` reaches on `(x', y')` is
the pullback of the transcript that `p` reaches on `(fX x', fY y')`. -/
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
