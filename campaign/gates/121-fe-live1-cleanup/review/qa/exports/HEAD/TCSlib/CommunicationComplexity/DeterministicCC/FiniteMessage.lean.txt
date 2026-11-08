/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.DeterministicCC.DetBasic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.Inv
import Mathlib.Data.Nat.Bitwise

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Finite-Message Deterministic Communication Protocols

A variant of the deterministic model of [RY20, Ch. 1] in which each message is an element of
an arbitrary finite type `β` rather than a single bit, charged `⌈log₂ |β|⌉` bits. The two
models are equivalent: a finite-message protocol can be compiled into a binary protocol of
the same complexity by encoding each message in binary (folklore; no textbook counterpart
was located), and a binary protocol is a finite-message protocol with `β = Bool`.

## Main definitions

- `Deterministic.FiniteMessage.Protocol`: finite-message protocols as an inductive tree with
  `output`, `alice` and `bob` nodes
- `Deterministic.FiniteMessage.Protocol.run`, `Deterministic.FiniteMessage.Protocol.complexity`:
  the outcome and the cost `Σ ⌈log₂ |β|⌉` along the worst root-to-leaf path
- `Deterministic.FiniteMessage.Protocol.toProtocol`: converts a finite-message protocol to an
  equivalent binary protocol with the same run behavior and complexity
- `Deterministic.FiniteMessage.Protocol.ofProtocol`: embeds a binary protocol into a
  generalized finite-message protocol (using `β = Bool` at each step)
- `Deterministic.FiniteMessage.Protocol.comap`: pull back a protocol along input maps

## Main results

- `Deterministic.FiniteMessage.Protocol.toProtocol_run`,
  `Deterministic.FiniteMessage.Protocol.toProtocol_complexity`: the converted binary protocol
  has the same outcome and the same complexity as the original finite-message protocol
- `Deterministic.FiniteMessage.Protocol.ofProtocol_run`,
  `Deterministic.FiniteMessage.Protocol.ofProtocol_complexity`,
  `Deterministic.FiniteMessage.Protocol.ofProtocol_equiv`: the embedding of binary protocols
  preserves outcome and complexity
- `Deterministic.FiniteMessage.Protocol.comap_run`,
  `Deterministic.FiniteMessage.Protocol.comap_complexity`: pulling back preserves the outcome
  (composed with the input maps) and the complexity

## References

* [RY20] A. Rao, A. Yehudayoff, *Communication Complexity and Applications*,
  Cambridge University Press, 2020.
* [KN97] E. Kushilevitz, N. Nisan, *Communication Complexity*, Cambridge University
  Press, 1997.
* [Yao79] A. C.-C. Yao, "Some complexity questions related to distributive computing",
  *STOC 1979*, pp. 209–213.

Original formalization by Lucy Horowitz, Timothe Kasriel, and Mihir Singhal.
-/

namespace CommunicationComplexity

/-- A generalized deterministic two-party communication protocol where at each step,
a player sends an element of an arbitrary finite type `β` (rather than just a `Bool`).
[RY20, Ch. 1, Definition (2-party deterministic protocol)]. Deviation: messages come from an
arbitrary nonempty finite alphabet `β` (which may vary from node to node) instead of bits.
Equivalent to `Deterministic.Protocol` up to complexity (see `toProtocol`)
where sending a `β`-valued message costs `⌈log₂ |β|⌉` bits. -/
inductive Deterministic.FiniteMessage.Protocol (X Y α : Type*) where
  | output (val : α) : Protocol X Y α
  | alice {β : Type} [Fintype β] [Nonempty β]
      (f : X → β) (P : β → Protocol X Y α) :
      Protocol X Y α
  | bob {β : Type} [Fintype β] [Nonempty β]
      (f : Y → β) (P : β → Protocol X Y α) :
      Protocol X Y α

namespace Deterministic.FiniteMessage.Protocol

variable {X Y α : Type*}

/-- Executes the generalized protocol on inputs `x` and `y`, returning the output value: the
owner of the current node evaluates its message function on its own input and both parties
descend to the child indexed by that message, until a leaf is reached. -/
def run (p : Protocol X Y α) (x : X) (y : Y) : α :=
  match p with
  | Deterministic.FiniteMessage.Protocol.output val => val
  | Deterministic.FiniteMessage.Protocol.alice f P => (P (f x)).run x y
  | Deterministic.FiniteMessage.Protocol.bob f P => (P (f y)).run x y

/-- The communication complexity of a generalized protocol. Sending a `β`-valued message
costs `⌈log₂ |β|⌉` bits, reflecting the number of bits needed to encode an element of `β`. -/
def complexity : Protocol X Y α → ℕ
  | Deterministic.FiniteMessage.Protocol.output _ => 0
  | Deterministic.FiniteMessage.Protocol.alice (β := β) _ P =>
      Nat.clog 2 (Fintype.card β) +
        Finset.univ.sup (fun i => (P i).complexity)
  | Deterministic.FiniteMessage.Protocol.bob (β := β) _ P =>
      Nat.clog 2 (Fintype.card β) +
        Finset.univ.sup (fun i => (P i).complexity)

/-- The complete binary protocol tree of depth `d` in which Alice sends the `d` bits
`query 0 x, …, query (d-1) x` in order and the protocol then continues as `Q bits`, where
`bits` is the vector of bits sent. -/
private def completeTreeAlice (d : ℕ) (query : Fin d → X → Bool)
    (Q : (Fin d → Bool) → Deterministic.Protocol X Y α) : Deterministic.Protocol X Y α :=
  match d with
  | 0 => Q Fin.elim0
  | d + 1 => Deterministic.Protocol.alice (query 0) (fun b =>
      completeTreeAlice d (query ∘ Fin.succ) (fun bits => Q (Fin.cons b bits)))

/-- Running the complete tree of depth `d` on `(x, y)` is the same as running the
continuation `Q` at the bit vector `i ↦ query i x` on `(x, y)`. -/
private theorem completeTreeAlice_run (d : ℕ) (query : Fin d → X → Bool)
    (Q : (Fin d → Bool) → Deterministic.Protocol X Y α) (x : X) (y : Y) :
    (completeTreeAlice d query Q).run x y = (Q (fun i => query i x)).run x y := by
  induction d with
  | zero =>
    simp only [completeTreeAlice]
    congr; ext i; exact i.elim0
  | succ d ih =>
    simp only [completeTreeAlice, Deterministic.Protocol.run]
    rw [ih]
    -- Goal: (Q (Fin.cons (query 0 x) ...)).run x y = (Q (fun i => query i x)).run x y
    -- Suffices to show the arguments to Q are equal
    have :
        Fin.cons (query 0 x) (fun i => (query ∘ Fin.succ) i x) =
        fun i => query i x := by
      simpa [Function.comp] using (Fin.cons_self_tail (fun i => query i x))
    rw [this]

/-- The complexity of the complete tree of depth `d` is `d` plus the maximum complexity of
the continuations `Q bits` over all bit vectors `bits : Fin d → Bool`.

**Proof sketch.** Induction on `d`. For `d = 0` the tree is just `Q Fin.elim0`, and the
supremum over the one-element type `Fin 0 → Bool` is that single value. For `d + 1` the root
is an Alice node, so the complexity is `1 + max` of the two subtrees, each of which is a
complete tree of depth `d` with continuation `bits ↦ Q (Fin.cons b bits)`; applying the
induction hypothesis twice reduces the claim to the identity "the supremum over all vectors
in `Fin (d + 1) → Bool` is the maximum of the suprema over the vectors starting with `false`
and over those starting with `true`", which is proved by splitting `univ` as the union of the
images of `Fin.cons false` and `Fin.cons true`. -/
private theorem completeTreeAlice_complexity (d : ℕ) (query : Fin d → X → Bool)
    (Q : (Fin d → Bool) → Deterministic.Protocol X Y α) :
    (completeTreeAlice d query Q).complexity =
      d + Finset.univ.sup (fun bits => (Q bits).complexity) := by
  induction d with
  | zero =>
    -- Step 1: base case, the supremum over the singleton type `Fin 0 → Bool`
    simp only [completeTreeAlice, Nat.zero_add]
    have : (Finset.univ : Finset (Fin 0 → Bool)) = {Fin.elim0} := by
      simpa using (univ_eq_singleton_of_card_one Fin.elim0 (by simp))
    rw [this, Finset.sup_singleton]
  | succ d ih =>
    -- Unfold to 1 + max (rec false).complexity (rec true).complexity
    simp only [completeTreeAlice, Deterministic.Protocol.complexity]
    rw [ih, ih, Nat.succ_add, Nat.add_max_add_left]
    -- Step 2: split the supremum over `Fin (d + 1) → Bool` by the first bit
    have hsplit : Finset.univ.sup (fun bits : Fin (d + 1) → Bool => (Q bits).complexity) =
        max (Finset.univ.sup (fun bits : Fin d → Bool => (Q (Fin.cons false bits)).complexity))
            (Finset.univ.sup (fun bits : Fin d → Bool => (Q (Fin.cons true bits)).complexity)) := by
      have hdec : (Finset.univ : Finset (Fin (d + 1) → Bool)) =
          (Finset.univ.image (Fin.cons false)) ∪ (Finset.univ.image (Fin.cons true)) := by
        ext bits
        simp only [Finset.mem_univ, Finset.mem_union,
          Finset.mem_image, true_and, true_iff]
        by_cases h : bits 0 = true
        · right; exact ⟨Fin.tail bits, by
            ext i; simp only [Fin.cons]
            refine Fin.cases ?_ ?_ i <;> simp [Fin.tail, h]⟩
        · left; exact ⟨Fin.tail bits, by
            ext i; refine Fin.cases ?_ ?_ i <;>
              simp [Fin.cons, Fin.tail, Bool.eq_false_iff.mpr h]⟩
      rw [hdec, Finset.sup_union, Finset.sup_image, Finset.sup_image]; rfl
    linarith [hsplit]

/-- Given a function `f : X → β` and binary protocols `Q b` for each `b : β`, there is
a single binary protocol `R` that behaves like `Q (f x)` on every input and whose complexity
is exactly `⌈log₂ |β|⌉` plus the maximum complexity of the `Q b`: Alice sends `f x` encoded in
`⌈log₂ |β|⌉` bits via a complete binary tree, then the parties continue with `Q (f x)`.

**Proof sketch.** Let `d = ⌈log₂ |β|⌉`. (1) Encode `β` injectively into `Fin d → Bool` by
composing `Fintype.equivFin` with the binary digits: injectivity holds because
`|β| ≤ 2 ^ d`, so bits at positions `≥ d` are all zero. (2) Let Alice's `i`-th query on
input `x` be the `i`-th bit of `encode (f x)`. (3) Define the continuation at a bit
vector: if the vector encodes some (necessarily unique) `b`, continue with `Q b`, otherwise
with `Q b₀` for a fixed `b₀`. Take `R` to be the complete Alice tree of depth `d` with these
queries and continuations. (4) Outcome: by `completeTreeAlice_run` the tree reaches the
continuation at `encode (f x)`, which is `Q (f x)` by injectivity. (5) Complexity: by
`completeTreeAlice_complexity` it is `d + sup` over bit vectors of the continuation's
complexity, and that supremum equals `sup_b (Q b).complexity` because every continuation is
some `Q b` and every `Q b` occurs (at `encode b`). -/
private theorem encode_alice {X Y α β : Type*} [Fintype β] [Nonempty β] (f : X → β)
    (Q : β → Deterministic.Protocol X Y α) :
    ∃ R : Deterministic.Protocol X Y α,
      (∀ x y, R.run x y = (Q (f x)).run x y) ∧
      R.complexity = Nat.clog 2 (Fintype.card β) +
        Finset.univ.sup (fun b => (Q b).complexity) := by
  have hcard : 0 < Fintype.card β := Fintype.card_pos
  let b₀ : β := (Fintype.equivFin β).symm ⟨0, hcard⟩
  let d := Nat.clog 2 (Fintype.card β)
  -- Step 1: binary encoding `β → (Fin d → Bool)` via `Fintype.equivFin` then `testBit`,
  -- injective because `|β| ≤ 2 ^ d`
  let encode : β → (Fin d → Bool) := fun b =>
    fun i => (Fintype.equivFin β b).val.testBit i.val
  have hencode_inj : Function.Injective encode := by
    intro a b hab
    apply (Fintype.equivFin β).injective; apply Fin.ext
    apply Nat.eq_of_testBit_eq; intro i
    by_cases hi : i < d
    · exact congr_fun hab ⟨i, hi⟩
    · have hd : Fintype.card β ≤ 2 ^ d := Nat.le_pow_clog (by norm_num) _
      have hle := hd.trans
        (Nat.pow_le_pow_right (by norm_num) (not_lt.mp hi))
      rw [Nat.testBit_eq_false_of_lt
            (lt_of_lt_of_le (Fintype.equivFin β a).isLt hle),
          Nat.testBit_eq_false_of_lt
            (lt_of_lt_of_le (Fintype.equivFin β b).isLt hle)]
  -- Upgrade ∃ to ∃! using injectivity, for use with Fintype.choose
  have hencode_unique : ∀ bits, (∃ b, encode b = bits) → ∃! b, encode b = bits := by
    intro bits ⟨b, hb⟩; exact ⟨b, hb, fun c hc => hencode_inj (hc.trans hb.symm)⟩
  -- Step 2: Alice's queries are the bits of `encode (f x)`
  let query : Fin d → X → Bool := fun i x => encode (f x) i
  -- Step 3: the continuation at each bit pattern, decoding via `Fintype.choose` when possible
  let leafQ : (Fin d → Bool) → Deterministic.Protocol X Y α :=
    fun bits => if h : ∃ b, encode b = bits then
      Q (Fintype.choose (fun b => encode b = bits) (hencode_unique bits h))
    else Q b₀
  refine ⟨completeTreeAlice d query leafQ, ?_, ?_⟩
  · -- Step 4: outcome — the tree reaches the continuation at `encode (f x)`, i.e. `Q (f x)`
    intro x y
    rw [completeTreeAlice_run]
    have hquery : (fun i => query i x) = encode (f x) := rfl
    rw [hquery]
    have hexists : ∃ b, encode b = encode (f x) := ⟨f x, rfl⟩
    simp only [leafQ, hexists, dite_true]
    -- Fintype.choose picks the unique b with encode b = encode (f x); by injectivity it's f x
    have hch := Fintype.choose_spec (fun b => encode b = encode (f x)) (hencode_unique _ hexists)
    rw [hencode_inj hch]
  · -- Step 5: complexity — the supremum over bit patterns equals the supremum over `β`
    rw [completeTreeAlice_complexity]
    congr 1
    apply le_antisymm
    · apply Finset.sup_le; intro bits _
      by_cases h : ∃ b, encode b = bits
      · simp only [leafQ, h, dite_true]
        exact Finset.le_sup (f := fun b => (Q b).complexity) (Finset.mem_univ _)
      · simp only [leafQ, h, dite_false]
        exact Finset.le_sup (f := fun b => (Q b).complexity) (Finset.mem_univ _)
    · apply Finset.sup_le; intro b _
      have hleafQ : leafQ (encode b) = Q b := by
        have hexb : ∃ b', encode b' = encode b := ⟨b, rfl⟩
        simp only [leafQ, hexb, dite_true]
        congr 1
        have hch := Fintype.choose_spec (fun b' => encode b' = encode b) (hencode_unique _ hexb)
        exact hencode_inj hch
      calc (Q b).complexity
          = (leafQ (encode b)).complexity := by rw [hleafQ]
        _ ≤ Finset.univ.sup (fun bits => (leafQ bits).complexity) :=
            Finset.le_sup (f := fun bits => (leafQ bits).complexity) (Finset.mem_univ _)

/-- Every finite-message protocol is simulated by a binary protocol with the same outcome
function and the same complexity. The Alice case is `encode_alice`; the Bob case is reduced
to it by swapping the players.

**Proof sketch.** Induction on the protocol. An output leaf is its own binary protocol. At an
Alice node, the induction hypothesis chooses a binary continuation for every message;
encoding the message (`encode_alice`) gives a binary protocol whose run and complexity agree
with the node's. At a Bob node, swap the players in every continuation, apply the Alice case,
and swap the result back; swapping preserves both run and complexity. -/
private theorem toProtocol_exists
    (p : Protocol X Y α) :
    ∃ (P : Deterministic.Protocol X Y α),
      P.run = p.run ∧ P.complexity = p.complexity := by
  induction p with
  | output val => exact ⟨Deterministic.Protocol.output val, rfl, rfl⟩
  | @alice β _ _ f P ih =>
    choose Q hQ_run hQ_comp using ih
    obtain ⟨R, hR_run, hR_comp⟩ := encode_alice f Q
    exact ⟨R,
      funext₂ fun x y => by rw [hR_run, hQ_run, Deterministic.FiniteMessage.Protocol.run],
      by rw [hR_comp]; simp [Deterministic.FiniteMessage.Protocol.complexity, hQ_comp]⟩
  | @bob β _ _ f P ih =>
    choose Q hQ_run hQ_comp using ih
    obtain ⟨R, hR_run, hR_comp⟩ := encode_alice f (fun b => (Q b).swap)
    exact ⟨R.swap,
      funext₂ fun x y => by
        simp [Deterministic.FiniteMessage.Protocol.run,
          Deterministic.Protocol.swap_run, hR_run, hQ_run],
      by simp [Deterministic.FiniteMessage.Protocol.complexity,
          Deterministic.Protocol.swap_complexity, hR_comp,
          Deterministic.Protocol.swap_complexity, hQ_comp]⟩

/-- Convert a finite-message protocol to a binary protocol with the same
run behavior and complexity, encoding each `β`-valued message as
`⌈log₂ |β|⌉` bits. This is folklore (a `|β|`-ary message costs `⌈log₂ |β|⌉` bits); no
textbook counterpart was located, so no citation is attached. The protocol is obtained
noncomputably from the existence proof `toProtocol_exists`. -/
noncomputable def toProtocol (p : Protocol X Y α) : Deterministic.Protocol X Y α :=
  (toProtocol_exists p).choose

/-- The binary protocol obtained from a finite-message protocol has the same outcome
function. -/
@[simp]
theorem toProtocol_run (p : Protocol X Y α) :
    (toProtocol p).run = p.run :=
  (toProtocol_exists p).choose_spec.1

/-- The binary protocol obtained from a finite-message protocol has the same complexity:
encoding each `β`-valued message in binary costs exactly `⌈log₂ |β|⌉` bits. Folklore; no
textbook counterpart was located, so no citation is attached. -/
@[simp]
theorem toProtocol_complexity (p : Protocol X Y α) :
    (toProtocol p).complexity = p.complexity :=
  (toProtocol_exists p).choose_spec.2

/-- Embed a binary protocol into a generalized protocol (with `β = Bool` at each step). -/
def ofProtocol : Deterministic.Protocol X Y α → Protocol X Y α
  | Deterministic.Protocol.output val => Deterministic.FiniteMessage.Protocol.output val
  | Deterministic.Protocol.alice f P =>
      Deterministic.FiniteMessage.Protocol.alice f (fun b => ofProtocol (P b))
  | Deterministic.Protocol.bob f P =>
      Deterministic.FiniteMessage.Protocol.bob f (fun b => ofProtocol (P b))

/-- Viewing a binary protocol as a finite-message protocol does not change its outcome on any
input. -/
theorem ofProtocol_run (p : Deterministic.Protocol X Y α) (x : X) (y : Y) :
    (ofProtocol p).run x y = p.run x y := by
  induction p <;> simp [ofProtocol, run, Deterministic.Protocol.run, *]

/-- `Nat.clog 2 2 = 1`, kernel-checked (replaces a former `native_decide`). -/
private theorem clog_two_two : Nat.clog 2 2 = 1 := Nat.clog_eq_one le_rfl le_rfl

/-- Viewing a binary protocol as a finite-message protocol does not change its complexity:
each `Bool`-valued message costs `⌈log₂ 2⌉ = 1` bit. -/
theorem ofProtocol_complexity (p : Deterministic.Protocol X Y α) :
    (ofProtocol p).complexity = p.complexity := by
  induction p <;> simp only [ofProtocol, complexity,
    Deterministic.Protocol.complexity, Fintype.univ_bool,
    Finset.sup_insert, Finset.sup_singleton,
    Fintype.card_bool, clog_two_two,
    Nat.max_comm, *]

/-- Every binary protocol can be viewed as a generalized protocol with the same
run behavior and complexity (using `β = Bool` at each step). -/
theorem ofProtocol_equiv (p : Deterministic.Protocol X Y α) :
    ∃ (P : Protocol X Y α), P.run = p.run ∧ P.complexity = p.complexity :=
  ⟨ofProtocol p, funext₂ (ofProtocol_run p), ofProtocol_complexity p⟩

/-- Pull back a finite-message protocol along functions `fX : X' → X`
and `fY : Y' → Y`, composing each message function with the maps. -/
def comap {X' Y' : Type*} (p : Protocol X Y α) (fX : X' → X) (fY : Y' → Y) :
    Protocol X' Y' α :=
  match p with
  | .output a => .output a
  | Protocol.alice f P =>
      Protocol.alice (f ∘ fX) (fun b => (P b).comap fX fY)
  | Protocol.bob f P =>
      Protocol.bob (f ∘ fY) (fun b => (P b).comap fX fY)

/-- Running the pulled-back protocol on `(x', y')` gives the same output as running the
original protocol on `(fX x', fY y')`. -/
@[simp]
theorem comap_run {X' Y' : Type*} (p : Protocol X Y α) (fX : X' → X) (fY : Y' → Y)
    (x' : X') (y' : Y') :
    (p.comap fX fY).run x' y' = p.run (fX x') (fY y') := by
  induction p <;> simp [comap, run, *]

/-- Pulling a finite-message protocol back along input maps does not change its
complexity. -/
@[simp]
theorem comap_complexity {X' Y' : Type*} (p : Protocol X Y α) (fX : X' → X) (fY : Y' → Y) :
    (p.comap fX fY).complexity = p.complexity := by
  induction p <;> simp [comap, complexity, *]

end Deterministic.FiniteMessage.Protocol

end CommunicationComplexity
