/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.ConfigGraph
import TCSlib.Complexity.SpaceComplexity.Machines.Parse

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A configuration codec for nondeterministic machines

Configuration-graph algorithms in small space — Savitch's midpoint recursion, the `PATH`
reduction, the inductive counting of Immerman and Szelepcsényi [AB09, §4.1.1, §4.2, §4.3]
— store configurations of a fixed machine `N` on the real input `x` as numbers in
registers. This file fixes that representation: the **code** of a configuration whose work
heads and nonblank work cells lie in the window `[-s, s]` is a word of `O(s + log |x|)` bits,
read as a little-endian number.

## Layout

The code word `Complexity.Codec.cfgWord N s C` is

* `2s + 1` **chunks**, one per work-tape cell `z ∈ [-s, s]` in increasing order, each of the
  fixed width `Complexity.Codec.W N`: a one-hot *header slot* (nonzero only in the leftmost
  chunk, where it names the control state and the output summary), then three bits per work
  tape (`nonblank`, `symbol`, `head here`), then a constant `1`;
* the input head position in binary, little-endian, padded to the fixed width
  `|bits (|x| + 1)|`;
* a final `1`, so that the word is the binary word of its value.

Fixed widths make field extraction position arithmetic, and the cell-major order makes one
machine step a *local* relation between neighbouring chunks (the checks of
`TCSlib.Complexity.SpaceComplexity.Codec.Checks`). The code records exactly the
configuration-graph vertex `Turing.NDTM.coreSum` (state, input position, windowed work tapes,
work heads, output summary), so it is injective on window-bounded configurations up to that
vertex, and that is all the graph algorithms need.

This codec is configuration-graph infrastructure, not a result of [AB09]; its conventions
(window `[-s, s]`, the output summary) are those of `TCSlib.Complexity.SpaceComplexity.ConfigGraph`.

## Main definitions

* `Complexity.Codec.InWin` — heads and nonblank work cells lie in `[-s, s]`.
* `Complexity.Codec.CellV`, `Complexity.Codec.encChunk` — cell values and their chunks.
* `Complexity.Codec.cfgWord`, `Complexity.Codec.cfgCode` — the code word and the code.
* `Complexity.Codec.decodeCfg` — the decoder.

## Main results

* `Complexity.Codec.bits_cfgCode` — the binary word of the code is the code word.
* `Complexity.Codec.cfgWord_congr` — the code depends only on the vertex `coreSum`.
* `Complexity.Codec.coreSum_eq_of_cfgWord_eq` — on window-bounded configurations the code
  determines the vertex.
* `Complexity.Codec.length_cfgWord`, `Complexity.Codec.cfgCode_lt` — the code has at most
  `codeK N · (s + logSpace |x| + 1)` bits.
* `Complexity.Codec.decodeCfg_cfgCode` — decoding a code recovers the vertex.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1: configurations and configuration graphs.)
-/

namespace Complexity.Codec

open Turing LogProg

variable (N : FinNDTM Bool)

/-! ## Words -/

/-- The window predicate at radius `s`: every work head and every nonblank work cell lies in
`[-s, s]`. (The coding window of the configuration graph, [AB09, Claim 4.4(1)].) -/
def InWin {x : List Bool} (s : ℕ) (C : Cfg N.k Bool N.State x) : Prop :=
  ∀ i, |C.workTapePos i| ≤ s ∧ ∀ z, C.workTapes i z ≠ none → |z| ≤ s

/-- The index of an output summary. -/
def sumIdx : OutSummary → Fin 3
  | .empty => 0
  | .accept => 1
  | .dead => 2

/-- Distinct summaries have distinct indices. -/
lemma sumIdx_injective : Function.Injective sumIdx := by
  intro a b h; cases a <;> cases b <;> simp_all [sumIdx]

/-- The header datum of a configuration: its control state and output-summary index. -/
abbrev Hd := Option N.State × Fin 3

/-- A cell value: the header (present only in the leftmost cell) and, per work tape, the
symbol in the cell and whether the head is on it. -/
abbrev CellV := Option (Hd N) × (Fin N.k → Option Bool × Bool)

set_option synthInstance.maxSize 1000 in
/-- Cell values have decidable equality. -/
instance CellV.instDecidableEq : DecidableEq (CellV N) := inferInstance

/-- The width of the header slot: the number of header data. -/
def hH : ℕ := Fintype.card (Hd N)

/-- The width of a chunk: header slot, three bits per work tape, a final `1`. -/
def W : ℕ := hH N + 3 * N.k + 1

/-- The position of a header datum in the one-hot header slot. -/
noncomputable def hdNum (h : Hd N) : ℕ := (Fintype.equivFin (Hd N) h).val

/-- Header positions lie in the slot. -/
lemma hdNum_lt (h : Hd N) : hdNum N h < hH N := (Fintype.equivFin (Hd N) h).isLt

/-- Distinct header data have distinct positions. -/
lemma hdNum_injective : Function.Injective (hdNum N) := by
  intro a b h
  exact (Fintype.equivFin (Hd N)).injective (Fin.ext h)

/-- Bit `t` of the chunk of a cell value: the one-hot header slot, then per tape `nonblank`,
`symbol`, `head here`, then `1`. -/
noncomputable def chunkBit (cv : CellV N) (t : ℕ) : Bool :=
  if t < hH N then decide (cv.1.map (hdNum N) = some t)
  else if h : (t - hH N) / 3 < N.k then
    if (t - hH N) % 3 = 0 then (cv.2 ⟨(t - hH N) / 3, h⟩).1.isSome
    else if (t - hH N) % 3 = 1 then (cv.2 ⟨(t - hH N) / 3, h⟩).1.getD false
    else (cv.2 ⟨(t - hH N) / 3, h⟩).2
  else true

/-- The chunk of a cell value. -/
noncomputable def encChunk (cv : CellV N) : List Bool :=
  List.ofFn fun t : Fin (W N) => chunkBit N cv t

/-- Chunks have the fixed width `W N`. -/
@[simp] lemma length_encChunk (cv : CellV N) : (encChunk N cv).length = W N := by
  simp only [encChunk, List.length_ofFn]

/-- Bits of a chunk below its width are `chunkBit`. -/
lemma getD_encChunk (cv : CellV N) (t : ℕ) (ht : t < W N) :
    (encChunk N cv).getD t false = chunkBit N cv t := by
  simp only [encChunk, List.getD_eq_getElem?_getD, List.getElem?_ofFn, ht, dite_true,
    Option.getD_some]

/-- The header-slot bits of a chunk. -/
lemma chunkBit_slot (cv : CellV N) (t : ℕ) (ht : t < hH N) :
    chunkBit N cv t = decide (cv.1.map (hdNum N) = some t) := by
  simp [chunkBit, ht]

/-- The three bits of tape `i` in a chunk. -/
lemma chunkBit_tape (cv : CellV N) (i : Fin N.k) (r : ℕ) (hr : r < 3) :
    chunkBit N cv (hH N + 3 * i + r) =
      if r = 0 then (cv.2 i).1.isSome else if r = 1 then (cv.2 i).1.getD false
      else (cv.2 i).2 := by
  have e1 : (hH N + 3 * i + r - hH N) / 3 = i := by omega
  have e2 : (hH N + 3 * i + r - hH N) % 3 = r := by omega
  have hi : (hH N + 3 * i + r - hH N) / 3 < N.k := by rw [e1]; exact i.isLt
  simp only [chunkBit, show ¬ hH N + 3 * i + r < hH N by omega, ↓reduceIte, dif_pos hi, e2]
  have : (⟨(hH N + 3 * i + r - hH N) / 3, hi⟩ : Fin N.k) = i := Fin.ext e1
  rw [this]

/-- **Chunks are injective**: a cell value is determined by its chunk.

**Proof sketch.** Compare the chunks bit by bit (`getD_encChunk`): the one-hot header slot
determines the header (positions are injective, `hdNum_injective`), and the three bits of each
tape determine the optional symbol and the head flag (`chunkBit_tape`). -/
theorem encChunk_injective : Function.Injective (encChunk N) := by
  intro a b h
  have hb : ∀ t < W N, chunkBit N a t = chunkBit N b t := by
    intro t ht
    rw [← getD_encChunk N a t ht, ← getD_encChunk N b t ht, h]
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  have slot : a1 = b1 := by
    have key : ∀ (u v : Option (Hd N)), (∀ t < hH N, decide (u.map (hdNum N) = some t) =
        decide (v.map (hdNum N) = some t)) → ∀ h, u = some h → v = some h := by
      intro u v hu h hh
      have := hu (hdNum N h) (hdNum_lt N h)
      subst hh
      simp only [Option.map_some, decide_true] at this
      cases v with
      | none => simp at this
      | some g =>
        simp at this
        rw [hdNum_injective N this]
    have hs : ∀ t < hH N, decide (a1.map (hdNum N) = some t) =
        decide (b1.map (hdNum N) = some t) := by
      intro t ht
      have := hb t (by simp only [W]; omega)
      rwa [chunkBit_slot N _ t ht, chunkBit_slot N _ t ht] at this
    cases a1 with
    | some hd => exact (key _ _ hs hd rfl).symm
    | none =>
      cases b1 with
      | none => rfl
      | some g => exact absurd (key _ _ (fun t ht => (hs t ht).symm) g rfl) (by simp)
  subst slot
  congr 1
  funext i
  have bit (r : ℕ) (hr : r < 3) := hb (hH N + 3 * i + r) (by simp only [W]; omega)
  have e0 := bit 0 (by omega)
  have e1 := bit 1 (by omega)
  have e2 := bit 2 (by omega)
  simp only [chunkBit_tape N _ i _ (by omega : (0 : ℕ) < 3),
    chunkBit_tape N _ i _ (by omega : (1 : ℕ) < 3),
    chunkBit_tape N _ i _ (by omega : (2 : ℕ) < 3)] at e0 e1 e2
  simp only [↓reduceIte, one_ne_zero, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one] at e0 e1 e2
  revert e0 e1 e2
  obtain ⟨o, hh⟩ := a2 i
  obtain ⟨o', hh'⟩ := b2 i
  intro e0 e1 e2
  simp only at e0 e1 e2
  subst e2
  congr 1
  cases o <;> cases o' <;> simp_all

/-- Concatenated fixed-width blocks: block `j` is recovered by dropping `W · j` letters and
taking `W`. -/
lemma take_drop_flatten {α : Type} (L : List (List α)) (w : ℕ)
    (hL : ∀ b ∈ L, b.length = w) (j : ℕ) (hj : j < L.length) :
    ((L.flatten).drop (w * j)).take w = L[j] := by
  induction L generalizing j with
  | nil => simp at hj
  | cons b L ih =>
    have hb := hL b (by simp)
    cases j with
    | zero => simp [← hb]
    | succ j =>
      simp only [List.flatten_cons, List.getElem_cons_succ]
      rw [show w * (j + 1) = b.length + w * j by rw [hb]; ring, ← List.drop_drop,
        List.drop_left]
      exact ih (fun c hc => hL c (by simp [hc])) j (by simpa using hj)

/-- Concatenated blocks of width `w` have length `w` times their number. -/
lemma length_flatten_const {α : Type} (L : List (List α)) (w : ℕ)
    (hL : ∀ b ∈ L, b.length = w) : (L.flatten).length = w * L.length := by
  induction L with
  | nil => simp
  | cons b L ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons,
      hL b (by simp), ih (fun c hc => hL c (by simp [hc]))]
    ring

/-- The word of `m` chunks with cell values `f 0, …, f (m - 1)`. -/
noncomputable def chunksWord (f : ℕ → CellV N) (m : ℕ) : List Bool :=
  (List.ofFn fun j : Fin m => encChunk N (f j)).flatten

/-- A chunk word has `W N` letters per chunk. -/
lemma length_chunksWord (f : ℕ → CellV N) (m : ℕ) :
    (chunksWord N f m).length = W N * m := by
  rw [chunksWord, length_flatten_const _ (W N) (by simp)]
  simp

/-- Equal chunk words have equal cell values. -/
lemma chunksWord_inj {f g : ℕ → CellV N} {m : ℕ} (h : chunksWord N f m = chunksWord N g m)
    (j : ℕ) (hj : j < m) : f j = g j := by
  have e1 := take_drop_flatten (List.ofFn fun j : Fin m => encChunk N (f j)) (W N)
    (by simp) j (by simpa using hj)
  have e2 := take_drop_flatten (List.ofFn fun j : Fin m => encChunk N (g j)) (W N)
    (by simp) j (by simpa using hj)
  have e : (List.ofFn fun j : Fin m => encChunk N (f j))[j]'(by simpa using hj) =
      (List.ofFn fun j : Fin m => encChunk N (g j))[j]'(by simpa using hj) := by
    rw [← e1, ← e2]
    exact congrArg (fun w => (w.drop (W N * j)).take (W N)) h
  simp only [List.getElem_ofFn] at e
  exact encChunk_injective N e

/-! ## The code of a configuration -/

variable {N} {x : List Bool}

/-- The cell value of cell `j` (work position `j - s`) of a configuration: the header in the
leftmost cell, then per tape the symbol at `j - s` and whether the head is there. -/
def cellOf (s : ℕ) (C : Cfg N.k Bool N.State x) (j : ℕ) : CellV N :=
  (if j = 0 then some (C.state, sumIdx (outSummary C.output)) else none,
    fun i => (C.workTapes i ((j : ℤ) - s), decide (C.workTapePos i = (j : ℤ) - s)))

/-- The width of the input-position field on inputs of length `n`: `|bits (n + 1)|`. -/
def wP (n : ℕ) : ℕ := (Nat.bits (n + 1)).length

/-- The binary word of `v` padded with `0`s to width `w`. -/
def padBits (w v : ℕ) : List Bool := Nat.bits v ++ List.replicate (w - (Nat.bits v).length) false

/-- **The code word** of a configuration at window radius `s`: the `2s + 1` cell chunks, the
padded input position, and a final `1`. -/
noncomputable def cfgWord (s : ℕ) (C : Cfg N.k Bool N.State x) : List Bool :=
  chunksWord N (cellOf s C) (2 * s + 1) ++ padBits (wP x.length) C.inputPos.val ++ [true]

/-- **The code** of a configuration at window radius `s`: the value of its code word. -/
noncomputable def cfgCode (s : ℕ) (C : Cfg N.k Bool N.State x) : ℕ := bitsVal (cfgWord s C)

/-- The value of a word does not see trailing `0`s. -/
lemma bitsVal_append_replicate (w : List Bool) (z : ℕ) :
    bitsVal (w ++ List.replicate z false) = bitsVal w := by
  induction w with
  | nil =>
    induction z with
    | zero => rfl
    | succ z ih => simp [List.replicate_succ, bitsVal] at ih ⊢; exact ih
  | cons b w ih => simp [bitsVal, ih]

/-- Every word is the binary word of its value followed by `0`s.

**Proof sketch.** Induction on the word: a leading letter `b` contributes `b + 2 v`; the
binary word of that value is `b` followed by that of `v`, unless both vanish, when the word
is all `0`s. -/
lemma eq_bits_append_replicate (w : List Bool) :
    w = Nat.bits (bitsVal w) ++
      List.replicate (w.length - (Nat.bits (bitsVal w)).length) false := by
  induction w with
  | nil => simp [bitsVal, Nat.zero_bits]
  | cons b w ih =>
    have hl : (Nat.bits (bitsVal w)).length ≤ w.length := by
      have := congrArg List.length ih
      simp only [List.length_append, List.length_replicate] at this
      omega
    simp only [bitsVal, List.length_cons]
    rw [show b.toNat + 2 * bitsVal w = 2 * bitsVal w + b.toNat by ring]
    by_cases hz : bitsVal w = 0 ∧ b = false
    · obtain ⟨h0, rfl⟩ := hz
      rw [h0] at ih ⊢
      simp only [Nat.zero_bits, List.length_nil, Nat.sub_zero, List.nil_append] at ih ⊢
      simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero, Nat.zero_bits, List.length_nil,
        Nat.sub_zero, List.nil_append, List.replicate_succ]
      rw [← ih]
    · rw [bits_two_mul_add _ _ (fun h0 => by
          cases b
          · exact absurd ⟨h0, rfl⟩ hz
          · rfl)]
      simp only [List.length_cons, List.cons_append, List.cons.injEq, true_and]
      rw [show w.length + 1 - ((Nat.bits (bitsVal w)).length + 1) =
        w.length - (Nat.bits (bitsVal w)).length by omega]
      exact ih

/-- A padded word has the padding width when the value fits. -/
lemma length_padBits {w v : ℕ} (h : (Nat.bits v).length ≤ w) : (padBits w v).length = w := by
  simp [padBits]; omega

/-- The value of a padded word. -/
@[simp] lemma bitsVal_padBits (w v : ℕ) : bitsVal (padBits w v) = v := by
  rw [padBits, bitsVal_append_replicate, bitsVal_bits]

/-- A word of length `w` is the padding of its value to width `w`. -/
lemma eq_padBits (p : List Bool) : p = padBits p.length (bitsVal p) := by
  conv_lhs => rw [eq_bits_append_replicate p]
  rfl

/-- Input positions fit their field. -/
lemma length_bits_pos_le (v n : ℕ) (hv : v ≤ n + 1) : (Nat.bits v).length ≤ wP n :=
  length_bits_mono hv

/-- The number of letters of the code word. -/
lemma length_cfgWord (s : ℕ) (C : Cfg N.k Bool N.State x) :
    (cfgWord s C).length = W N * (2 * s + 1) + wP x.length + 1 := by
  have := C.inputPos.isLt
  simp only [cfgWord, List.length_append, length_chunksWord, List.length_singleton]
  rw [length_padBits (length_bits_pos_le _ _ (by omega))]

/-- The code word ends with `1`, so it is the binary word of its value. -/
lemma canon_cfgWord (s : ℕ) (C : Cfg N.k Bool N.State x) : Canon (cfgWord s C) := by
  intro h
  simp [cfgWord]

/-- **The binary word of the code is the code word.** -/
theorem bits_cfgCode (s : ℕ) (C : Cfg N.k Bool N.State x) :
    Nat.bits (cfgCode s C) = cfgWord s C :=
  (canon_eq_bits _ (canon_cfgWord s C)).symm

/-- The cell values depend only on the configuration-graph vertex. -/
lemma cellOf_congr {s : ℕ} {C D : Cfg N.k Bool N.State x} (h : NDTM.coreSum C = NDTM.coreSum D) :
    cellOf s C = cellOf s D := by
  simp only [NDTM.coreSum, MultiTapeTM.ConfigCount.core, Prod.mk.injEq] at h
  obtain ⟨⟨hs, -, hw, hp⟩, ho⟩ := h
  funext j
  simp only [cellOf, hs, hw, hp, ho]

/-- **The code depends only on the configuration-graph vertex** `coreSum`. -/
theorem cfgWord_congr {s : ℕ} {C D : Cfg N.k Bool N.State x}
    (h : NDTM.coreSum C = NDTM.coreSum D) : cfgWord s C = cfgWord s D := by
  have hi : C.inputPos = D.inputPos := by
    simp only [NDTM.coreSum, MultiTapeTM.ConfigCount.core, Prod.mk.injEq] at h
    exact h.1.2.1
  simp only [cfgWord, cellOf_congr h, hi]

/-- **On window-bounded configurations the code determines the vertex**: equal code words
give equal `coreSum`.

**Proof sketch.** The two words have the same length, so their chunk prefixes, position
fields and final letters align. Equal chunks give equal cell values (`chunksWord_inj`):
the leftmost cell yields the state and the summary (`sumIdx` is injective, and summaries
determine the vertex component), every cell yields the tape symbols and head flags at its
position, and outside `[-s, s]` both tapes are blank and no head lies there (window
hypotheses). Equal position fields have equal values (`bitsVal_padBits`). -/
theorem coreSum_eq_of_cfgWord_eq {s : ℕ} {C D : Cfg N.k Bool N.State x}
    (hC : InWin N s C) (hD : InWin N s D) (h : cfgWord s C = cfgWord s D) :
    NDTM.coreSum C = NDTM.coreSum D := by
  have hlen : (chunksWord N (cellOf s C) (2 * s + 1)).length =
      (chunksWord N (cellOf s D) (2 * s + 1)).length := by simp [length_chunksWord]
  simp only [cfgWord, List.append_assoc] at h
  obtain ⟨hc, hrest⟩ := List.append_inj h hlen
  have hpos := congrArg bitsVal (List.append_inj_left' hrest rfl)
  simp only [bitsVal_padBits] at hpos
  have cell := chunksWord_inj N hc
  have c0 := cell 0 (by omega)
  simp only [cellOf, ↓reduceIte, Prod.mk.injEq, Option.some.injEq] at c0
  obtain ⟨⟨hst, hsum⟩, -⟩ := c0
  have hsum' := sumIdx_injective hsum
  have tape : ∀ i (z : ℤ), |z| ≤ s → C.workTapes i z = D.workTapes i z ∧
      (C.workTapePos i = z ↔ D.workTapePos i = z) := by
    intro i z hz
    have := cell (z + s).toNat (by rw [abs_le] at hz; omega)
    simp only [cellOf, Prod.mk.injEq] at this
    have e := congrFun this.2 i
    simp only [Prod.mk.injEq, decide_eq_decide] at e
    have hz' : (((z + s).toNat : ℕ) : ℤ) - s = z := by rw [abs_le] at hz; omega
    rwa [hz'] at e
  simp only [NDTM.coreSum, MultiTapeTM.ConfigCount.core, Prod.mk.injEq]
  refine ⟨⟨hst, Fin.ext hpos, ?_, ?_⟩, hsum'⟩
  · funext i z
    by_cases hz : |z| ≤ s
    · exact (tape i z hz).1
    · have h1 : C.workTapes i z = none := by
        by_contra hne; exact hz ((hC i).2 z hne)
      have h2 : D.workTapes i z = none := by
        by_contra hne; exact hz ((hD i).2 z hne)
      rw [h1, h2]
  · funext i
    exact ((tape i _ (hC i).1).2.mp rfl).symm

/-- The constant of the code length: `2 W + 2`. -/
def codeK (N : FinNDTM Bool) : ℕ := 2 * W N + 2

/-- **The code is short**: the code word has at most `codeK N · (s + logSpace |x| + 1)`
letters, so the code is below `2 ^ (codeK N · (s + logSpace |x| + 1))`. The input field
has `|bits (|x| + 1)| ≤ logSpace |x| + 1` letters.

**Proof sketch.** Count `W (2s + 1)` chunk letters, the position field, and the final `1`;
`|bits (n + 1)| ≤ ⌊log₂ (n + 1)⌋ + 1 ≤ logSpace n + 1` and `W ≥ 1`. -/
theorem length_cfgWord_le (s : ℕ) (C : Cfg N.k Bool N.State x) :
    (cfgWord s C).length ≤ codeK N * (s + logSpace x.length + 1) := by
  rw [length_cfgWord]
  have h1 : wP x.length ≤ logSpace x.length + 1 := by
    have e := length_bits_le_log (x.length + 1)
    have e2 : Nat.log 2 (x.length + 1) ≤ Nat.log 2 x.length + 1 := by
      rcases Nat.eq_zero_or_pos x.length with h | h
      · rw [h]; simp
      · have := Nat.log_mul_base (b := 2) (n := x.length) (by norm_num) (by omega)
        have := Nat.log_mono_right (b := 2) (show x.length + 1 ≤ x.length * 2 by omega)
        omega
    simp only [wP, logSpace]; omega
  have hW : 1 ≤ W N := by simp [W]
  simp only [codeK]
  have e1 : W N * (2 * s + 1) = 2 * (W N * s) + W N := by ring
  have e2 : (2 * W N + 2) * (s + logSpace x.length + 1) =
      2 * (W N * s) + 2 * (W N * logSpace x.length) + 2 * W N + 2 * s +
        2 * logSpace x.length + 2 := by ring
  rw [e1, e2]
  omega

/-- A word of `L` letters has value below `2 ^ L`. -/
lemma bitsVal_lt_two_pow (w : List Bool) : bitsVal w < 2 ^ w.length := by
  induction w with
  | nil => simp [bitsVal]
  | cons b w ih =>
    simp only [bitsVal, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

/-- **The code is below `2 ^ (codeK N · (s + logSpace |x| + 1))`.** -/
theorem cfgCode_lt (s : ℕ) (C : Cfg N.k Bool N.State x) :
    cfgCode s C < 2 ^ (codeK N * (s + logSpace x.length + 1)) :=
  (bitsVal_lt_two_pow _).trans_le
    (Nat.pow_le_pow_right (by norm_num) (length_cfgWord_le s C))

/-! ## Decoding -/

open Classical in
/-- **The decoder**: a window-bounded configuration with code `c` at radius `s`, if any
(chosen; it is determined up to the configuration-graph vertex,
`decodeCfg_cfgCode`). -/
noncomputable def decodeCfg (x : List Bool) (s c : ℕ) : Option (Cfg N.k Bool N.State x) :=
  if h : ∃ C : Cfg N.k Bool N.State x, InWin N s C ∧ cfgCode s C = c then some (Classical.choose h)
  else none

/-- **Decoding a code recovers the vertex**: the decoder succeeds on the code of a
window-bounded configuration, with a window-bounded result of the same code and vertex.

**Proof sketch.** The chosen configuration has the same code, hence the same code word
(`bits_cfgCode`), hence the same vertex (`coreSum_eq_of_cfgWord_eq`). -/
theorem decodeCfg_cfgCode (s : ℕ) (C : Cfg N.k Bool N.State x) (hC : InWin N s C) :
    ∃ D, decodeCfg x s (cfgCode s C) = some D ∧ InWin N s D ∧ cfgCode s D = cfgCode s C ∧
      NDTM.coreSum D = NDTM.coreSum C := by
  classical
  have h : ∃ D : Cfg N.k Bool N.State x, InWin N s D ∧ cfgCode s D = cfgCode s C := ⟨C, hC, rfl⟩
  refine ⟨Classical.choose h, by simp [decodeCfg, h], (Classical.choose_spec h).1,
    (Classical.choose_spec h).2, ?_⟩
  apply coreSum_eq_of_cfgWord_eq (Classical.choose_spec h).1 hC
  rw [← bits_cfgCode, ← bits_cfgCode, (Classical.choose_spec h).2]

/-- The decoder fails exactly on numbers that are not codes. -/
theorem decodeCfg_eq_none (s c : ℕ) :
    decodeCfg (N := N) x s c = none ↔
      ¬ ∃ C : Cfg N.k Bool N.State x, InWin N s C ∧ cfgCode s C = c := by
  classical
  unfold decodeCfg
  split_ifs with h <;> simp [h]

end Complexity.Codec
