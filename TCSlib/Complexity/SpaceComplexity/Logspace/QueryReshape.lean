/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.Logspace.PreimageHost

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Reshaping implicit queries

To compose implicitly logspace computable functions [AB09, Lemma 4.17's proof], a query
`⟨x, bits i⟩` about `g (f x)` is reshaped into the query `⟨f x, bits i⟩` about `g`. This is
`Complexity.compQ f`, and it is itself implicitly logspace computable. Both query languages of
`g ∘ f` are then preimages of `g`'s along it (`Complexity.mem_indexLang_compQ_iff`), hence in
`L` by `Complexity.mem_LOGSPACE_preimage`.

Deciding `compQ f`'s own languages needs `f`'s queries at `⟨x, bits j⟩`. An abstract register
machine on the host `⟨⟨x, bits i⟩, bits p⟩` can only present `⟨⟨⟨x, bits i⟩, bits p⟩, bits j⟩`
(a `whole`-mode call). The index-dropping map `Complexity.dropIdx` takes
`⟨⟨w, b⟩, b'⟩ ↦ ⟨w, b'⟩`; applied twice it recovers `⟨x, bits j⟩`.

Phase P4.4b of `AroraBarakChapters3-4Plan.md`; see `audits/ch4-p44-resolutions-addendum.md`.

## Main definitions

* `Complexity.dropIdx` — `⟨⟨w, b⟩, b'⟩ ↦ ⟨w, b'⟩`, and `[]` off that shape.
* `Complexity.compQ` — `⟨x, b⟩ ↦ ⟨f x, b⟩` for canonical `b`, and `[]` otherwise.

## Main results

* `Complexity.dropIdx_pairEncode`, `Complexity.dropIdx_length_le` — the map on nested pairs;
  its length bound.
* `Complexity.compQ_pairEncode`, `Complexity.mem_indexLang_compQ_iff`,
  `Complexity.compQ_length_le` — the map on queries; the preimage identity; the length bound.
* `Complexity.implicitlyLogspaceComputable_dropIdx`,
  `Complexity.ImplicitlyLogspaceComputable.compQ` — both maps are implicitly logspace
  computable (sorried; phase-P4.4b statements).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, Definition 4.16, Lemma 4.17 and its proof.)
-/

namespace Complexity

open Turing

/-- **Dropping the middle index**: `⟨⟨w, b⟩, b'⟩ ↦ ⟨w, b'⟩`, and `[]` on words not of that
shape. -/
def dropIdx (z : List Bool) : List Bool :=
  match pairDecode z with
  | some (u, b') =>
    match pairDecode u with
    | some (w, _) => pairEncode w b'
    | none => []
  | none => []

/-- `dropIdx` on a nested pair. -/
theorem dropIdx_pairEncode (w b b' : List Bool) :
    dropIdx (pairEncode (pairEncode w b) b') = pairEncode w b' := by
  simp [dropIdx, pairDecode_pairEncode]

/-- `dropIdx` never lengthens a word. -/
theorem dropIdx_length_le (z : List Bool) : (dropIdx z).length ≤ z.length := by
  unfold dropIdx
  split
  · rename_i u b' hz
    split
    · rename_i w b hu
      rw [eq_pairEncode_of_pairDecode _ _ _ hz, eq_pairEncode_of_pairDecode _ _ _ hu]
      simp only [length_pairEncode]
      omega
    · simp
  · simp

/-- **The query reshaping of a composition**: `⟨x, b⟩ ↦ ⟨f x, b⟩` when `b` is a canonical
binary word (some `Nat.bits i`), and `[]` otherwise. -/
def compQ (f : List Bool → List Bool) (w : List Bool) : List Bool :=
  match pairDecode w with
  | some (x, b) => if Nat.bits (LogProg.bitsVal b) = b then pairEncode (f x) b else []
  | none => []

/-- `compQ f` on a genuine query. -/
theorem compQ_pairEncode (f : List Bool → List Bool) (x : List Bool) (i : ℕ) :
    compQ f (pairEncode x (Nat.bits i)) = pairEncode (f x) (Nat.bits i) := by
  simp [compQ, pairDecode_pairEncode, LogProg.bitsVal_bits]

/-- **The preimage identity of composition**: a word is in `{⟨x, i⟩ | p (f x) i}` iff its
reshaping is in `{⟨y, i⟩ | p y i}`. Malformed and non-canonical queries go to `[]`, which no
index language contains. -/
theorem mem_indexLang_compQ_iff (f : List Bool → List Bool) (p : List Bool → ℕ → Prop)
    (w : List Bool) :
    w ∈ indexLang (fun x i => p (f x) i) ↔ compQ f w ∈ indexLang p := by
  constructor
  · rintro ⟨x, i, rfl, hp⟩
    exact ⟨f x, i, compQ_pairEncode f x i, hp⟩
  · rintro ⟨y, i, h, hp⟩
    unfold compQ at h
    split at h
    · rename_i x b hw
      split_ifs at h with hb
      · have := pairEncode_injective (a₁ := (f x, b)) (a₂ := (y, Nat.bits i)) h
        simp only [Prod.mk.injEq] at this
        obtain ⟨rfl, rfl⟩ := this
        exact ⟨x, i, eq_pairEncode_of_pairDecode _ _ _ hw, hp⟩
      · exact absurd h.symm (pairEncode_ne_nil _ _)
    · exact absurd h.symm (pairEncode_ne_nil _ _)

/-- `compQ f` is polynomially bounded when `f` is: `|compQ f w| ≤ (2C + 3)(|w| + 1)^{c+1}`
from `|f x| ≤ C (|x| + 1)^c`. -/
theorem compQ_length_le {f : List Bool → List Bool} {C c : ℕ}
    (hf : ∀ x, (f x).length ≤ C * (x.length + 1) ^ c) (w : List Bool) :
    (compQ f w).length ≤ (2 * C + 3) * (w.length + 1) ^ (c + 1) := by
  unfold compQ
  split
  · rename_i x b hw
    split_ifs
    · have hw' := eq_pairEncode_of_pairDecode _ _ _ hw
      have hl : w.length = 2 * x.length + 2 + b.length := by rw [hw', length_pairEncode]
      have e1 : (w.length + 1) ^ c ≤ (w.length + 1) ^ (c + 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have e2 : w.length + 1 ≤ (w.length + 1) ^ (c + 1) := by
        calc w.length + 1 = (w.length + 1) ^ 1 := (pow_one _).symm
          _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
      have e3 : (f x).length ≤ C * (w.length + 1) ^ c :=
        (hf x).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
      have e4 : C * (w.length + 1) ^ c ≤ C * (w.length + 1) ^ (c + 1) :=
        Nat.mul_le_mul_left _ e1
      rw [length_pairEncode]
      have e5 : (2 * C + 3) * (w.length + 1) ^ (c + 1) =
          2 * (C * (w.length + 1) ^ (c + 1)) + 3 * (w.length + 1) ^ (c + 1) := by ring
      omega
    · simp
  · simp

/-- The kept prefix of `dropIdx` is read at stride four in its paired query host.
The discarded middle field and the retained suffix are arbitrary words.

**Proof sketch.** The two enclosing first-field encodings each double addresses. Below
the separator of the innermost pair, changing its second field does not change a bit. -/
private lemma dropIdx_prefix_address (w b b' tail : List Bool) (j : ℕ)
    (hj : j < 2 * w.length + 2) :
    (dropIdx (pairEncode (pairEncode w b) b')).getD j false =
      (pairEncode (pairEncode (pairEncode w b) b') tail).getD (4 * j) false := by
  have hu := length_pairEncode w b
  have hz := length_pairEncode (pairEncode w b) b'
  have h₁ : (pairEncode (pairEncode (pairEncode w b) b') tail).getD (4 * j) false =
      (pairEncode (pairEncode w b) b').getD (2 * j) false := by
    rw [pairEncode_getD, if_pos (by omega)]
    congr 1
    omega
  have h₂ : (pairEncode (pairEncode w b) b').getD (2 * j) false =
      (pairEncode w b).getD j false := by
    rw [pairEncode_getD, if_pos (by omega)]
    congr 1
    omega
  rw [h₁, h₂, dropIdx_pairEncode, pairEncode_getD, pairEncode_getD]
  split_ifs <;> first | rfl | omega

/-- A retained suffix bit is read after the doubled outer separator. This address is
used only within the suffix; an out-of-range query must be rejected before making it.

**Proof sketch.** Remove the host's outer doubling, then the discarded pair's doubled
first field and separator. The remaining address is exactly the suffix index. -/
private lemma dropIdx_suffix_address (w b b' tail : List Bool) (j : ℕ) (hj : j < b'.length) :
    (dropIdx (pairEncode (pairEncode w b) b')).getD (2 * w.length + 2 + j) false =
      (pairEncode (pairEncode (pairEncode w b) b') tail).getD
        (4 * (pairEncode w b).length + 4 + 2 * j) false := by
  have hz := length_pairEncode (pairEncode w b) b'
  have h₁ : (pairEncode (pairEncode (pairEncode w b) b') tail).getD
        (4 * (pairEncode w b).length + 4 + 2 * j) false =
      (pairEncode (pairEncode w b) b').getD (2 * (pairEncode w b).length + 2 + j) false := by
    rw [pairEncode_getD, if_pos (by omega)]
    congr 1
    omega
  rw [h₁, dropIdx_pairEncode, pairEncode_getD, pairEncode_getD]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  congr 1
  omega

/-- Passing a binary-width check bounds the decoded value by twice the cap, including a
zero cap. This also bounds every partial value in a most-significant-bit-first decoder.

**Proof sketch.** The value is below `2 ^ size n`. For positive `n`, its top binary place
is at most `n`, hence `2 ^ size n ≤ 2*n`; at zero both canonical representations are empty. -/
private lemma query_index_bound (r n : ℕ)
    (hwidth : (Nat.bits r).length ≤ (Nat.bits n).length) : r ≤ 2 * n := by
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len] at hwidth
  have hr := Nat.size_le.mp hwidth
  by_cases hn : n = 0
  · subst n
    simp only [Nat.size_zero, pow_zero] at hr
    omega
  · have hs : 0 < n.size := Nat.size_pos.mpr (Nat.pos_of_ne_zero hn)
    have htop : 2 ^ (n.size - 1) ≤ n := Nat.lt_size.mp (by omega)
    have hpow : 2 ^ n.size = 2 * 2 ^ (n.size - 1) := by
      conv_lhs => rw [show n.size = (n.size - 1) + 1 by omega, pow_succ]
      omega
    rw [hpow] at hr
    omega

/-- Discarding low-order digits cannot increase a binary word's value. -/
private lemma query_suffix_value_le (w : List Bool) (j : ℕ) :
    LogProg.bitsVal (w.drop j) ≤ LogProg.bitsVal w := by
  induction j generalizing w with
  | zero => simp
  | succ j ih =>
    cases w with
    | nil => simp [LogProg.bitsVal]
    | cons b w =>
      have h := ih w
      simp only [List.drop_succ_cons, LogProg.bitsVal]
      omega

/-- The width test bounds every accumulator of the reverse tail scan before decoding it.
Canonicality is required only of the query index, never of `dropIdx`'s payload fields. -/
private lemma query_accumulator_bound (w : List Bool) (n j : ℕ) (hc : LogProg.Canon w)
    (hwidth : w.length ≤ (Nat.bits n).length) : LogProg.bitsVal (w.drop j) ≤ 2 * n := by
  apply (query_suffix_value_le w j).trans
  apply query_index_bound
  simpa only [← LogProg.canon_eq_bits w hc] using hwidth

/-- The canonical-index length overflow test makes both queries false before its
numerical value is accumulated. -/
private lemma dropIdx_query_overflow (z : List Bool) (r : ℕ)
    (hlarge : (Nat.bits ((pairEncode z (Nat.bits r)).length)).length < (Nat.bits r).length) :
    (dropIdx z).getD r false = false ∧ ¬ r < (dropIdx z).length := by
  have hr : (pairEncode z (Nat.bits r)).length < r := by
    by_contra h
    have hb := LogProg.length_bits_mono (Nat.le_of_not_gt h)
    omega
  have hz := length_pairEncode z (Nat.bits r)
  have hd := dropIdx_length_le z
  have hout : (dropIdx z).length ≤ r := by omega
  exact ⟨by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hout], by omega⟩

/-! ## The bounded index-dropping ARM -/

open LogProg Classical

/-- Finite control of the one index-dropping ARM. The mode parameter selects bit or length
answers only at a successful lookup. Registers hold the physical pointer, host end,
first-field end, retained-suffix start, inner-field end, prefix end, query, scratch/candidate,
and query-tail start, in that order. -/
private inductive DropState where
  | lengthTest | lengthInc
  | copy (stage : Fin 8) (bump : Bool)
  | scan (layer : Fin 3) | first (layer : Fin 3)
  | second (layer : Fin 3) (bit : Bool) | readSecond (layer : Fin 3) (bit : Bool)
  | scanInc (layer : Fin 3) (choice : Fin 4) (step : Fin 4)
  | tailTest (last : Bool) | tailCheck | tailRead | tailHalf (bit : Bool) | tailInc (bit : Bool)
  | tailDone | clearPtr (stage : Fin 5)
  | zDec (step : Fin 2) | uDec (step : Fin 4)
  | decode | decodeDown | decodeRead | decodeCopy (bit : Bool) | decodeCopyInc (bit : Bool)
  | decodeClear (bit : Bool) | decodeScale (bit : Bool) | decodeTake (bit : Bool)
  | decodeInc (bit : Bool) (second : Bool) | decodeAdd (bit : Bool)
  | seek (suffix : Bool) | matchIndex (suffix : Bool) | nextIndex (suffix : Bool)
  | walk (suffix : Bool) (step : Fin 4) | hit | answer (bit : Bool)
  deriving DecidableEq, Fintype

/-- Each copy stage names its destination, source, and continuation. -/
private def dropCopy : Fin 8 → Fin 9 × Fin 9 × DropState
  | 0 => (8, 0, .copy 1 false)
  | 1 => (7, 1, .tailTest true)
  | 2 => (0, 1, .decode)
  | 3 => (2, 8, .zDec 0)
  | 4 => (3, 0, .copy 5 false)
  | 5 => (4, 0, .uDec 0)
  | 6 => (5, 0, .clearPtr 3)
  | 7 => (0, 3, .seek true)

/-- The three pair scans read the host, its first field, and that field's first field. -/
private def dropStride (layer : Fin 3) : ℕ := ![1, 2, 4] layer

/-- End registers for those scans, all in physical host coordinates. -/
private def dropLimit (layer : Fin 3) : Fin 9 := ![1, 2, 4] layer

/-- A successful scan stores its boundary before the next phase. -/
private def dropScanDone (layer : Fin 3) : DropState :=
  .copy (![0, 4, 6] layer) false

/-- Shared finite increment chains for the received aligned scan. -/
private def dropAdvance (layer : Fin 3) (choice : Fin 4) (i : ℕ) : DropState :=
  if h : i < dropStride layer then .scanInc layer choice ⟨i, by
    have : dropStride layer ≤ 4 := (by decide : ∀ l, dropStride l ≤ 4) layer
    omega⟩
  else ![.second layer false, .second layer true, .scan layer, dropScanDone layer] choice

/-- A one-cell advance of the outer query tail. -/
private def dropTailAdvance (b : Bool) (i : ℕ) : DropState :=
  if i = 0 then .tailInc b else .tailTest b

/-- Two increments implement the decoder's doubling transfer. -/
private def dropDecodeAdvance (b : Bool) (i : ℕ) : DropState :=
  if i = 0 then .decodeInc b false else if i = 1 then .decodeInc b true else .decodeScale b

/-- Lookup walks use stride four in the kept prefix and stride two in the retained suffix. -/
private def dropWalk (suffix : Bool) (i : ℕ) : DropState :=
  if h : i < (if suffix then 2 else 4) then
    .walk suffix ⟨i, by
      cases suffix with
      | false => exact h
      | true => have : i < 2 := h; omega⟩
  else .seek suffix

/-- The complete index-dropping table, assembled from the bounded shared fragments.
Only the outer query tail is required to be canonical. The two payloads scanned inside
its first field are arbitrary words. -/
private def dropARM (lengthMode : Bool) : ARM 9 2 DropState
  | .lengthTest => .call 1 .whole [1] .lengthInc (.scan 0)
  | .lengthInc => .inc 1 .lengthTest
  | .copy s false => .jeq (dropCopy s).1 (dropCopy s).2.1 (dropCopy s).2.2 (.copy s true)
  | .copy s true => .inc (dropCopy s).1 (.copy s false)
  | .scan layer => .jeq 0 (dropLimit layer) (.answer false) (.first layer)
  | .first layer => .call 0 .whole [0] (dropAdvance layer 1 0) (dropAdvance layer 0 0)
  | .second layer b => .jeq 0 (dropLimit layer) (.answer false) (.readSecond layer b)
  | .readSecond layer b => .call 0 .whole [0]
      (if b then dropAdvance layer 2 0 else dropAdvance layer 3 0)
      (if b then .answer false else dropAdvance layer 2 0)
  | .scanInc layer choice i => .inc 0 (dropAdvance layer choice (i.val + 1))
  | .tailTest b => .jeq 0 1 (if b then .tailDone else .answer false) .tailCheck
  | .tailCheck => .jz 7 (.answer false) .tailRead
  | .tailRead => .call 0 .whole [0] (.tailHalf true) (.tailHalf false)
  | .tailHalf b => .half 7 (.tailInc b)
  | .tailInc b => .inc 0 (.tailTest b)
  | .tailDone => .clr 7 (.clearPtr 0)
  | .clearPtr s => .clr 0 (![.copy 2 false, .scan 1, .scan 2, .seek false, .copy 7 false] s)
  | .zDec i => .dec 2 (if i = 0 then .zDec 1 else .clearPtr 1)
  | .uDec i => .dec 4 (if h : i.val + 1 < 4 then .uDec ⟨i.val + 1, h⟩ else .clearPtr 2)
  | .decode => .jeq 0 8 (.copy 3 false) .decodeDown
  | .decodeDown => .dec 0 .decodeRead
  | .decodeRead => .call 0 .whole [0] (.decodeCopy true) (.decodeCopy false)
  | .decodeCopy b => .jeq 7 6 (.decodeClear b) (.decodeCopyInc b)
  | .decodeCopyInc b => .inc 7 (.decodeCopy b)
  | .decodeClear b => .clr 6 (.decodeScale b)
  | .decodeScale b => .jz 7 (.decodeAdd b) (.decodeTake b)
  | .decodeTake b => .dec 7 (.decodeInc b false)
  | .decodeInc b false => .inc 6 (.decodeInc b true)
  | .decodeInc b true => .inc 6 (.decodeScale b)
  | .decodeAdd b => if b then .inc 6 .decode else .jz 7 .decode .decode
  | .seek suffix => .jeq 0 (if suffix then 2 else 5)
      (if suffix then .answer false else .clearPtr 4) (.matchIndex suffix)
  | .matchIndex suffix => .jeq 7 6 .hit (.nextIndex suffix)
  | .nextIndex suffix => .inc 7 (dropWalk suffix 0)
  | .walk suffix i => .inc 0 (dropWalk suffix (i.val + 1))
  | .hit => if lengthMode then .ret true else .call 0 .whole [0] (.answer true) (.answer false)
  | .answer b => .ret b

/-- The access bank is independent of the mode. -/
private def dropBank : Fin 2 → Language Bool := ![inputBitLang, inputLenLang]

/-- Both modes use the same language expression and the same table. -/
private def dropLang (lengthMode : Bool) : Language Bool :=
  indexLang fun z q => if lengthMode then q < (dropIdx z).length else (dropIdx z).getD q false = true

/-- Every reachable instruction's syntactic side conditions already hold for this table.
There are no format-specific input instructions, and every call has one argument. -/
private lemma drop_preS (mode : Bool) (h : List Bool) (c : AConf 9 DropState) :
    PreS (dropARM mode) h c := by
  rcases c with ⟨l, v, ans⟩
  cases l with
  | none => trivial
  | some l =>
    cases l <;> simp only [PreS, dropARM] <;> try decide
    case copy stage bump =>
      cases bump
      · exact (by decide : ∀ s, (dropCopy s).1 ≠ (dropCopy s).2.1) stage
      · trivial
    case scan layer => exact (by decide : ∀ l, (0 : Fin 9) ≠ dropLimit l) layer
    case second layer bit => exact (by decide : ∀ l, (0 : Fin 9) ≠ dropLimit l) layer
    case decodeAdd bit => cases bit <;> trivial
    case seek suffix => cases suffix <;> decide
    case decodeInc bit second => cases second <;> trivial
    case hit => cases mode <;> simp

/-- Truthful calls to the fixed two-language access bank. -/
private noncomputable def dropOracle (j : Fin 2) (w : List Bool) : Bool :=
  MultiTapeTM.indicator (dropBank j : Set (List Bool)) w

/-- The common bounded guard uses exactly the brief's linear register bound. -/
private abbrev DropGood (mode : Bool) (h : List Bool) (a : AConf 9 DropState) :=
  PreS (dropARM mode) h a ∧ ∀ r, a.2.1 r ≤ 4 * h.length + 4

/-- Bounded reachability is the received relation, with the fixed table and oracle. -/
private abbrev DropReach (mode : Bool) (h : List Bool) :=
  AReach (dropARM mode) dropOracle h (DropGood mode h)

/-- Halting uses the same received relation and guard. -/
private abbrev DropHalt (mode : Bool) (h : List Bool) :=
  AHalt (dropARM mode) dropOracle h (DropGood mode h)

/-- A register vector for the phase boundaries of the index-dropping machine. -/
private def dropValues (n : ℕ) (ptr zend retained inner kept query temp tail : ℕ := 0) : Fin 9 → ℕ :=
  ![ptr, n, zend, retained, inner, kept, query, temp, tail]

/-- A bit call reads the corresponding host position, including its false default. -/
private lemma drop_bit (h : List Bool) (i : ℕ) :
    dropOracle 0 (pairEncode h (Nat.bits i)) = h.getD i false := by
  change MultiTapeTM.indicator (inputBitLang : Set (List Bool)) _ = _
  simp [inputBitLang, indicator_indexLang_pairEncode]

/-- A length call tests a host position. -/
private lemma drop_len (h : List Bool) (i : ℕ) :
    dropOracle 1 (pairEncode h (Nat.bits i)) = decide (i < h.length) := by
  simp [dropOracle, dropBank, inputLenLang, indicator_indexLang_pairEncode]

/-- Returning a bit halts in one bounded step. -/
private lemma drop_ret (mode b : Bool) (h : List Bool) (v : Fin 9 → ℕ)
    (hv : ∀ r, v r ≤ 4 * h.length + 4) :
    DropHalt mode h (some (.answer b), v, none) b :=
  AHalt.ret rfl ⟨drop_preS mode h _, hv⟩

/-- At a matching index the length mode accepts; the bit mode calls the access bank. -/
private lemma drop_hit (mode : Bool) (h : List Bool) (v : Fin 9 → ℕ)
    (hv : ∀ r, v r ≤ 4 * h.length + 4) :
    DropHalt mode h (some .hit, v, none) (if mode then true else h.getD (v 0) false) := by
  cases mode
  · apply AHalt.step ⟨drop_preS false h _, hv⟩
    simp only [astep, dropARM, Bool.false_eq_true, ↓reduceIte, vword_whole₁, drop_bit]
    cases hb : h.getD (v 0) false <;> simpa [hb] using drop_ret false _ h v hv
  · exact AHalt.ret rfl ⟨drop_preS true h _, hv⟩

/-- Every copy stage instantiates the one shared bounded copy loop. -/
private lemma drop_copy_run (mode : Bool) (h : List Bool) (stage : Fin 8) (v : Fin 9 → ℕ)
    (hv : ∀ r, v r ≤ 4 * h.length + 4)
    (hle : v (dropCopy stage).1 ≤ v (dropCopy stage).2.1) :
    DropReach mode h (some (.copy stage false), v, none)
      (some (dropCopy stage).2.2,
        Function.update v (dropCopy stage).1 (v (dropCopy stage).2.1), none) := by
  exact registerCopy_loop (dropARM mode) dropOracle h _ _
    ((by decide : ∀ s, (dropCopy s).1 ≠ (dropCopy s).2.1) stage)
    _ _ _ rfl rfl _ v hv hle

/-- Every nested pair scan is an instance of the received strided pair validator. -/
private lemma drop_pair_run (mode : Bool) (h : List Bool) (layer : Fin 3)
    (w : List Bool) (v : Fin 9 → ℕ) (hv : ∀ r, v r ≤ 4 * h.length + 4)
    (hl : v (dropLimit layer) = v 0 + dropStride layer * w.length)
    (ho : ∀ i < w.length, h.getD (v 0 + dropStride layer * i) false = w.getD i false) :
    match pairDecode w with
    | none => ∃ t ≤ w.length, DropReach mode h (some (.scan layer), v, none)
        (some (.answer false), Function.update v 0 (v 0 + dropStride layer * t), none)
    | some (a, _) => DropReach mode h (some (.scan layer), v, none)
        (some (dropScanDone layer),
          Function.update v 0 (v 0 + dropStride layer * (2 * a.length + 2)), none) := by
  apply alignedPair_loop (dropARM mode) dropOracle h 0 (dropLimit layer) 0
    (.scan layer) (.first layer) (.second layer) (.readSecond layer)
    (.answer false) (dropScanDone layer) (dropAdvance layer) (dropStride layer) _
    ((by decide : ∀ l, 0 < dropStride l) layer)
    ((by decide : ∀ l, (0 : Fin 9) ≠ dropLimit l) layer) rfl rfl
    (fun _ => rfl) (fun _ => rfl)
  · intro choice i hi
    simp only [dropAdvance, dif_pos hi, dropARM]
  · simp [dropAdvance]
  · exact hv
  · exact hl
  · intro i hi
    rw [drop_bit]
    exact ho i hi

/-- The canonicality flag used by the tail loop is exactly `Canon`, including zero. -/
private lemma drop_canon (w : List Bool) : w.getLastD true = true ↔ Canon w := by
  by_cases hw : w = []
  · subst w; simp [Canon]
  · simp only [List.getLastD_eq_getLast?, List.getLast?_eq_getLast hw, Option.getD_some, Canon]
    exact ⟨fun h _ => h, fun h => h hw⟩

/-- Lookup exposes a phase-boundary vector only when its register is supplied. -/
@[simp] private lemma dropValues_apply (n p z s u f q t a : ℕ) (r : Fin 9) :
    dropValues n p z s u f q t a r = ![p, n, z, s, u, f, q, t, a] r := rfl

/-- One register update preserves the boundary-vector representation. -/
@[simp] private lemma dropValues_update (n p z s u f q t a : ℕ) (r : Fin 9) (b : ℕ) :
    Function.update (dropValues n p z s u f q t a) r b =
      dropValues (if 1 = r then b else n) (if 0 = r then b else p)
        (if 2 = r then b else z) (if 3 = r then b else s) (if 4 = r then b else u)
        (if 5 = r then b else f) (if 6 = r then b else q) (if 7 = r then b else t)
        (if 8 = r then b else a) := by
  apply funext
  simp [Fin.forall_fin_succ, dropValues, Function.update_apply]

/-- Bounds on a boundary vector are the nine scalar bounds. -/
private lemma dropValues_bound (n p z s u f q t a B : ℕ)
    (hn : n ≤ B) (hp : p ≤ B) (hz : z ≤ B) (hs : s ≤ B) (hu : u ≤ B)
    (hf : f ≤ B) (hq : q ≤ B) (ht : t ≤ B) (ha : a ≤ B) :
    ∀ r, dropValues n p z s u f q t a r ≤ B := by
  simpa [Fin.forall_fin_succ] using ⟨hp, hn, hz, hs, hu, hf, hq, ht, ha⟩

/-- Successful outer validation decodes the bounded query; either failed test rejects.
The proof uses the shared tail scanner before the shared reverse decoder.

**Proof sketch.** Save the tail start and copy the host length into the width cap. The tail
scan either rejects or establishes canonicality and the width bound. Clear its scratch,
restore the pointer to the host end, and invoke bounded decoding. Its accumulator bounds
come from the frozen suffix-value lemma. No arbitrary payload is decoded numerically. -/
private lemma drop_tail_decode (mode : Bool) (z tail : List Bool) :
    let h := pairEncode z tail
    let p := 2 * z.length + 2
    if Canon tail ∧ tail.length ≤ (Nat.bits h.length).length then
      DropReach mode h
        (some (.copy 0 false), dropValues h.length (ptr := p), none)
        (some (.copy 3 false), dropValues h.length (ptr := p) (query := bitsVal tail) (tail := p), none)
    else DropHalt mode h
      (some (.copy 0 false), dropValues h.length (ptr := p), none) false := by
  dsimp only
  let h := pairEncode z tail
  let p := 2 * z.length + 2
  have len : h.length = p + tail.length := length_pairEncode z tail
  have pn : p ≤ h.length := by omega
  let v₀ := dropValues h.length (ptr := p)
  let v₁ := dropValues h.length (ptr := p) (tail := p)
  let v₂ := dropValues h.length (ptr := p) (temp := h.length) (tail := p)
  have bounds : ∀ (ptr temp : ℕ), ptr ≤ h.length → temp ≤ h.length →
      ∀ r, (dropValues h.length (ptr := ptr) (temp := temp) (tail := p)) r ≤ 4 * h.length + 4 := by
    intro ptr temp hp ht
    apply dropValues_bound <;> omega
  have b₀ : ∀ r, v₀ r ≤ 4 * h.length + 4 := by
    dsimp [v₀]; apply dropValues_bound <;> omega
  have b₁ := bounds p 0 pn (Nat.zero_le _)
  have b₂ := bounds p h.length pn le_rfl
  have c₀ : DropReach mode h (some (.copy 0 false), v₀, none)
      (some (.copy 1 false), v₁, none) := by
    simpa [v₀, v₁, dropCopy] using drop_copy_run mode h 0 v₀ b₀ (by simp [v₀, dropCopy])
  have c₁ : DropReach mode h (some (.copy 1 false), v₁, none)
      (some (.tailTest true), v₂, none) := by
    simpa [v₁, v₂, dropCopy] using drop_copy_run mode h 1 v₁ b₁ (by simp [v₁, dropCopy])
  have reads : ∀ i < tail.length,
      dropOracle 0 (pairEncode h (Nat.bits (v₂ 0 + 1 * i))) = tail.getD i false := by
    intro i hi
    rw [drop_bit]
    simp only [v₂, dropValues_apply, Matrix.cons_val_zero, one_mul]
    rw [show p + i = 2 * z.length + 2 + i by rfl]
    rw [show h = pairEncode z tail by rfl, pairEncode_getD]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    congr 1
    omega
  obtain ⟨v, bv, vp, frame, scan⟩ := canonicalTail_loop (dropARM mode) dropOracle h
    0 1 7 (by decide) (by decide) (by decide) 0 DropState.tailTest
    .tailCheck .tailRead (.answer false) .tailDone DropState.tailHalf dropTailAdvance 1
    (4 * h.length + 4) (by omega) (fun _ => rfl) rfl rfl
    (fun _ => rfl)
    (by
      intro b i hi
      have hi0 : i = 0 := by omega
      subst i
      rfl)
    (fun _ => rfl) tail true v₂ b₂
    (by simpa [v₂] using len) reads
  have fn : v 1 = h.length := by simpa [v₂] using frame 1 (by decide) (by decide)
  have ft : v 8 = p := by simpa [v₂] using frame 8 (by decide) (by decide)
  by_cases good : Canon tail ∧ tail.length ≤ (Nat.bits h.length).length
  · rw [if_pos good]
    have flag := (drop_canon tail).mpr good.1
    have scan' : DropReach mode h (some (.tailTest true), v₂, none) (some .tailDone, v, none) := by
      have ss := scan
      simp only [flag, ↓reduceIte] at ss
      simpa [v₂, good.2] using ss
    have reset : DropReach mode h (some .tailDone, v, none)
        (some (.copy 2 false), dropValues h.length (tail := p), none) := by
      apply AReach.step ⟨drop_preS mode h _, bv⟩
      simp only [astep, dropARM]
      apply AReach.step ⟨drop_preS mode h _, register_update_le v 7 _ 0 bv (by omega)⟩
      simp only [astep, dropARM]
      have ve : Function.update (Function.update v 7 0) 0 0 = dropValues h.length (tail := p) := by
        apply funext
        have fr := frame
        simp only [Fin.forall_fin_succ] at fr ⊢
        simp_all [v₂, Function.update_apply]
      rw [ve]
      exact AReach.refl _
    let vd := dropValues h.length (ptr := h.length) (tail := p)
    have bd : ∀ r, vd r ≤ 4 * h.length + 4 := bounds h.length 0 le_rfl (Nat.zero_le _)
    have cp : DropReach mode h (some (.copy 2 false), dropValues h.length (tail := p), none)
        (some .decode, vd, none) := by
      simpa [vd, dropCopy] using drop_copy_run mode h 2 (dropValues h.length (tail := p))
        (bounds 0 0 (Nat.zero_le _) (Nat.zero_le _)) (by simp [dropCopy])
    have vals : ∀ i ≤ tail.length, bitsVal (tail.drop i) ≤ 4 * h.length + 4 := by
      intro i _
      have := query_accumulator_bound tail h.length i good.1 good.2
      omega
    have dread : ∀ i < tail.length,
        dropOracle 0 (pairEncode h (Nat.bits (vd 8 + i))) = tail.getD i false := by
      simpa only [vd, v₂, dropValues_apply, Matrix.cons_val_succ, Matrix.cons_val_zero,
        Nat.one_mul] using reads
    obtain ⟨vf, bf, ep, ea, et, ef, dec⟩ := boundedDecode_loop (dropARM mode) dropOracle h
      0 8 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      0 .decode .decodeDown .decodeRead (.copy 3 false)
      DropState.decodeCopy DropState.decodeCopyInc DropState.decodeClear
      DropState.decodeScale DropState.decodeTake DropState.decodeAdd dropDecodeAdvance
      rfl rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl)
      (by
        intro b i hi
        have hi01 : i = 0 ∨ i = 1 := by omega
        rcases hi01 with rfl | rfl <;> rfl)
      (fun _ => rfl) (fun _ => rfl) tail (4 * h.length + 4) vals tail.length le_rfl vd bd
      (by simpa [vd] using len) (by simp [vd, bitsVal]) (by simp [vd]) dread
    have endpoint : vf = dropValues h.length (ptr := p) (query := bitsVal tail) (tail := p) := by
      apply funext
      simp only [Fin.forall_fin_succ] at ef ⊢
      simp_all [vd]
    rw [endpoint] at dec
    exact (c₀.trans c₁).trans (scan'.trans (reset.trans (cp.trans dec)))
  · rw [if_neg good]
    have stop : DropReach mode h (some (.tailTest true), v₂, none)
        (some (.answer false), v, none) := by
      by_cases width : tail.length ≤ (Nat.bits h.length).length
      · have nc : ¬ Canon tail := fun hc => good ⟨hc, width⟩
        have flag : tail.getLastD true = false := Bool.eq_false_iff.mpr (fun ht => nc ((drop_canon tail).mp ht))
        have ss := scan
        simp only [flag, Bool.false_eq_true, ↓reduceIte, ite_self] at ss
        exact ss
      · simpa [v₂, width] using scan
    exact ((c₀.trans c₁).trans stop).halt (drop_ret mode false h v bv)

/-- Both lookup segments instantiate the same bounded indexing fragment. -/
private lemma drop_seek_run (mode suffix : Bool) (h : List Bool) (count : ℕ) (v : Fin 9 → ℕ)
    (hv : ∀ r, v r ≤ 4 * h.length + 4)
    (hl : v (if suffix then 2 else 5) = v 0 + (if suffix then 2 else 4) * count)
    (hb : v 7 + count ≤ 4 * h.length + 4) (hq : v 7 ≤ v 6) :
    if v 6 < v 7 + count then
      DropReach mode h (some (.seek suffix), v, none)
        (some .hit, Function.update (Function.update v 0
          (v 0 + (if suffix then 2 else 4) * (v 6 - v 7))) 7 (v 6), none)
    else
      DropReach mode h (some (.seek suffix), v, none)
        (some (if suffix then .answer false else .clearPtr 4),
          Function.update (Function.update v 0 (v (if suffix then 2 else 5))) 7 (v 7 + count), none) := by
  apply indexedSeek_loop (dropARM mode) dropOracle h 0 (if suffix then 2 else 5) 7 6
    (by cases suffix <;> decide) (by decide) (by decide)
    (by cases suffix <;> decide) (by cases suffix <;> decide) (by decide)
    (.seek suffix) (.matchIndex suffix) (.nextIndex suffix) .hit
    (if suffix then .answer false else .clearPtr 4) (dropWalk suffix)
    (if suffix then 2 else 4) _ (by cases suffix <;> decide) rfl rfl rfl
  · intro i hi
    simp only [dropWalk, dif_pos hi, dropARM]
  · simp [dropWalk]
  · exact hv
  · exact hl
  · exact hb
  · exact hq

/-- The final lookup reads the kept prefix at stride four, then the retained suffix at
stride two. The discarded and retained fields have no canonicality hypothesis.

**Proof sketch.** The shared bounded seek either hits inside the kept prefix or reaches
its end. On a miss, relocate the pointer to the retained suffix and use the same seek
again. The frozen prefix/suffix address lemmas identify each hit with the output bit;
the end-of-suffix branch is precisely an out-of-range query. -/
private lemma drop_lookup (mode : Bool) (w b b' : List Bool) (q : ℕ) (v : Fin 9 → ℕ)
    (hv : ∀ r, v r ≤ 4 * (pairEncode (pairEncode (pairEncode w b) b') (Nat.bits q)).length + 4)
    (hp : v 0 = 0) (hk : v 5 = 4 * (2 * w.length + 2))
    (hs : v 3 = 4 * (pairEncode w b).length + 4)
    (he : v 2 = 4 * (pairEncode w b).length + 4 + 2 * b'.length)
    (hq : v 6 = q) (hi : v 7 = 0) :
    DropHalt mode (pairEncode (pairEncode (pairEncode w b) b') (Nat.bits q))
      (some (.seek false), v, none)
      (if mode then decide (q < (dropIdx (pairEncode (pairEncode w b) b')).length)
        else (dropIdx (pairEncode (pairEncode w b) b')).getD q false) := by
  let h := pairEncode (pairEncode (pairEncode w b) b') (Nat.bits q)
  change ∀ r, v r ≤ 4 * h.length + 4 at hv
  let n := 2 * w.length + 2
  let out := dropIdx (pairEncode (pairEncode w b) b')
  have outlen : out.length = n + b'.length := by simp [out, n, dropIdx_pairEncode, length_pairEncode]
  have nb : n ≤ 4 * h.length + 4 := by have := hv 5; change v 5 = 4 * n at hk; omega
  have total : n + b'.length ≤ 4 * h.length + 4 := by simp only [h, n, length_pairEncode]; omega
  have first := drop_seek_run mode false h n v hv (by simpa [hp, n] using hk)
    (by simpa [hi] using nb) (by simp [hi])
  by_cases lt : q < n
  · have cond : v 6 < v 7 + n := by omega
    simp only [if_pos cond, Bool.false_eq_true, ↓reduceIte] at first
    let vh := Function.update (Function.update v 0 (4 * q)) 7 q
    have run : DropReach mode h (some (.seek false), v, none) (some .hit, vh, none) := by
      simpa [hp, hq, hi, vh] using first
    have pos : 4 * q ≤ 4 * h.length + 4 := by have := hv 5; change v 5 = 4 * n at hk; omega
    have bv : ∀ r, vh r ≤ 4 * h.length + 4 := register_update_le _ 7 _ q
      (register_update_le v 0 _ _ hv pos) (by simpa [hq] using hv 6)
    have bit := dropIdx_prefix_address w b b' (Nat.bits q) q lt
    have ans : (if mode then true else h.getD (vh 0) false) =
        (if mode then decide (q < out.length) else out.getD q false) := by
      have inside : q < out.length := by omega
      cases mode with
      | false =>
        change h.getD (4 * q) false = out.getD q false
        exact bit.symm
      | true => simp [inside]
    rw [← ans]
    exact run.halt (drop_hit mode h vh bv)
  · have cond : ¬ v 6 < v 7 + n := by omega
    simp only [if_neg cond, Bool.false_eq_true, ↓reduceIte] at first
    let vm := Function.update (Function.update v 0 (v 5)) 7 n
    have run : DropReach mode h (some (.seek false), v, none) (some (.clearPtr 4), vm, none) := by
      simpa [hi, vm] using first
    have bm : ∀ r, vm r ≤ 4 * h.length + 4 := register_update_le _ 7 _ n
      (register_update_le v 0 _ _ hv (hv 5)) nb
    let vs := Function.update vm 0 (v 3)
    have bs : ∀ r, vs r ≤ 4 * h.length + 4 := register_update_le vm 0 _ _ bm (hv 3)
    have move : DropReach mode h (some (.clearPtr 4), vm, none) (some (.seek true), vs, none) := by
      apply AReach.step ⟨drop_preS mode h _, bm⟩
      simp only [astep, dropARM]
      have copy := drop_copy_run mode h 7 (Function.update vm 0 0)
        (register_update_le vm 0 _ 0 bm (by omega)) (by simp [dropCopy])
      simpa [dropCopy, vs, vm] using copy
    have vp : vs 0 = 4 * (pairEncode w b).length + 4 := by simp [vs, hs]
    have ve : vs 2 = 4 * (pairEncode w b).length + 4 + 2 * b'.length := by simp [vs, vm, he]
    have vi : vs 7 = n := by simp [vs, vm]
    have vq : vs 6 = q := by simp [vs, vm, hq]
    have second := drop_seek_run mode true h b'.length vs bs
      (by simpa [vp] using ve) (by simpa [vi] using total) (by rw [vi, vq]; omega)
    by_cases inrange : q < n + b'.length
    · have cond' : vs 6 < vs 7 + b'.length := by omega
      simp only [if_pos cond', ↓reduceIte] at second
      let addr := 4 * (pairEncode w b).length + 4 + 2 * (q - n)
      let vh := Function.update (Function.update vs 0 addr) 7 q
      have hit : DropReach mode h (some (.seek true), vs, none) (some .hit, vh, none) := by
        simpa [vp, vq, vi, addr, vh] using second
      have pos : addr ≤ 4 * h.length + 4 := by have := hv 2; dsimp [addr]; omega
      have bh : ∀ r, vh r ≤ 4 * h.length + 4 := register_update_le _ 7 _ q
        (register_update_le vs 0 _ _ bs pos) (by simpa [hq] using hv 6)
      have jlt : q - n < b'.length := by omega
      have bit := dropIdx_suffix_address w b b' (Nat.bits q) (q - n) jlt
      have qeq : 2 * w.length + 2 + (q - n) = q := by dsimp [n] at *; omega
      rw [qeq] at bit
      have ans : (if mode then true else h.getD (vh 0) false) =
          (if mode then decide (q < out.length) else out.getD q false) := by
        have inside : q < out.length := by omega
        cases mode with
        | false =>
          change h.getD addr false = out.getD q false
          exact bit.symm
        | true => simp [inside]
      rw [← ans]
      exact (run.trans (move.trans hit)).halt (drop_hit mode h vh bh)
    · have cond' : ¬ vs 6 < vs 7 + b'.length := by omega
      simp only [if_neg cond', ↓reduceIte] at second
      let vf := Function.update (Function.update vs 0 (vs 2)) 7 (vs 7 + b'.length)
      have bf : ∀ r, vf r ≤ 4 * h.length + 4 := register_update_le _ 7 _ _
        (register_update_le vs 0 _ _ bs (bs 2)) (by rw [vi]; exact total)
      have bit : out.getD q false = false := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show out.length ≤ q by omega)]
      have ans : (if mode then decide (q < out.length) else out.getD q false) = false := by
        cases mode with
        | false => exact bit
        | true => simp [show ¬ q < out.length by omega]
      rw [ans]
      exact (run.trans (move.trans second)).halt (drop_ret mode false h vf bf)

/-- Reading an even position in a paired first field removes one doubling. -/
private lemma drop_first_read (a b : List Bool) (i : ℕ) (hi : i < a.length) :
    (pairEncode a b).getD (2 * i) false = a.getD i false := by
  rw [pairEncode_getD, if_pos (by omega)]
  congr 1
  omega

/-- A finite subtraction chain preserves the common register bound. The two nested-pair
preparations use this same argument for their physical separator widths. -/
private lemma drop_decrement_run (mode : Bool) (h : List Bool) (r : Fin 9) (count : ℕ)
    (path : ℕ → DropState) (v : Fin 9 → ℕ) (hv : ∀ j, v j ≤ 4 * h.length + 4)
    (steps : ∀ i < count, dropARM mode (path i) = .dec r (path (i + 1))) :
    DropReach mode h (some (path 0), v, none)
      (some (path count), Function.update v r (v r - count), none) := by
  induction count generalizing path v with
  | zero => simpa using AReach.refl (some (path 0), v, none)
  | succ count ih =>
    apply AReach.step ⟨drop_preS mode h _, hv⟩
    simp only [astep, steps 0 (by omega)]
    have bound := register_update_le v r (4 * h.length + 4) (v r - 1) hv
      (by have := hv r; omega)
    have rest := ih (fun i => path (i + 1)) (Function.update v r (v r - 1)) bound
      (fun i hi => steps (i + 1) (by omega))
    simpa [Function.update_idem, Nat.sub_sub, Nat.add_comm] using rest

/-- After decoding the query, prepare the physical end of its first field and restart its
pair-shape scan. This stores no payload value.

**Proof sketch.** Copy the saved tail start, subtract the two separator cells, and clear
only the physical pointer before entering the received scan. -/
private lemma drop_z_prepare (mode : Bool) (h : List Bool) (zlen q : ℕ)
    (hz : 2 * zlen + 2 ≤ h.length) (hq : q ≤ 2 * h.length) :
    DropReach mode h
      (some (.copy 3 false), dropValues h.length (ptr := 2 * zlen + 2)
        (query := q) (tail := 2 * zlen + 2), none)
      (some (.scan 1), dropValues h.length (zend := 2 * zlen)
        (query := q) (tail := 2 * zlen + 2), none) := by
  have bv : ∀ r, (dropValues h.length (ptr := 2 * zlen + 2)
      (query := q) (tail := 2 * zlen + 2)) r ≤ 4 * h.length + 4 := by
    apply dropValues_bound <;> omega
  have cp := drop_copy_run mode h 3 _ bv (by simp [dropCopy])
  simp [dropCopy] at cp
  apply cp.trans
  have dec := drop_decrement_run mode h 2 2
    (fun i => if i = 0 then .zDec 0 else if i = 1 then .zDec 1 else .clearPtr 1)
    (dropValues h.length (ptr := 2 * zlen + 2) (zend := 2 * zlen + 2)
      (query := q) (tail := 2 * zlen + 2))
    (by apply dropValues_bound <;> omega)
    (by intro i hi; have : i = 0 ∨ i = 1 := by omega
        rcases this with rfl | rfl <;> rfl)
  simp at dec
  apply dec.trans
  apply AReach.step ⟨drop_preS mode h _, by apply dropValues_bound <;> omega⟩
  simp [astep, dropARM]
  exact AReach.refl _

/-- Save the retained suffix start, derive the inner first-field end, and restart the
stride-four pair scan. Both offsets remain in host coordinates.

**Proof sketch.** Copy the separator end into the retained-start and inner-end registers,
subtract its four physical separator cells from the latter, and clear the pointer. -/
private lemma drop_u_prepare (mode : Bool) (h : List Bool) (zlen ulen q : ℕ)
    (hz : 2 * zlen + 2 ≤ h.length) (hu : 2 * ulen + 2 ≤ zlen) (hq : q ≤ 2 * h.length) :
    DropReach mode h
      (some (.copy 4 false), dropValues h.length (ptr := 4 * ulen + 4) (zend := 2 * zlen)
        (query := q) (tail := 2 * zlen + 2), none)
      (some (.scan 2), dropValues h.length (zend := 2 * zlen) (retained := 4 * ulen + 4)
        (inner := 4 * ulen) (query := q) (tail := 2 * zlen + 2), none) := by
  have bv : ∀ r, (dropValues h.length (ptr := 4 * ulen + 4) (zend := 2 * zlen)
      (query := q) (tail := 2 * zlen + 2)) r ≤ 4 * h.length + 4 := by
    apply dropValues_bound <;> omega
  have c₄ := drop_copy_run mode h 4 _ bv (by simp [dropCopy])
  simp [dropCopy] at c₄
  apply c₄.trans
  have bv' : ∀ r, (dropValues h.length (ptr := 4 * ulen + 4) (zend := 2 * zlen)
      (retained := 4 * ulen + 4) (query := q) (tail := 2 * zlen + 2)) r ≤ 4 * h.length + 4 := by
    apply dropValues_bound <;> omega
  have c₅ := drop_copy_run mode h 5 _ bv' (by simp [dropCopy])
  simp [dropCopy] at c₅
  apply c₅.trans
  have dec := drop_decrement_run mode h 4 4
    (fun i => if hi : i < 4 then .uDec ⟨i, hi⟩ else .clearPtr 2)
    (dropValues h.length (ptr := 4 * ulen + 4) (zend := 2 * zlen)
      (retained := 4 * ulen + 4) (inner := 4 * ulen + 4)
      (query := q) (tail := 2 * zlen + 2))
    (by apply dropValues_bound <;> omega)
    (by intro i hi; have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
        rcases this with rfl | rfl | rfl | rfl <;> rfl)
  simp at dec
  apply dec.trans
  apply AReach.step ⟨drop_preS mode h _, by apply dropValues_bound <;> omega⟩
  simp [astep, dropARM]
  exact AReach.refl _

/-- Save the last pair boundary and restart the final segmented lookup. -/
private lemma drop_lookup_prepare (mode : Bool) (h : List Bool) (zlen ulen wlen q : ℕ)
    (hz : 2 * zlen + 2 ≤ h.length) (hu : 2 * ulen + 2 ≤ zlen)
    (hw : 2 * wlen + 2 ≤ ulen) (hq : q ≤ 2 * h.length) :
    DropReach mode h
      (some (.copy 6 false), dropValues h.length (ptr := 8 * wlen + 8) (zend := 2 * zlen)
        (retained := 4 * ulen + 4) (inner := 4 * ulen) (query := q) (tail := 2 * zlen + 2), none)
      (some (.seek false), dropValues h.length (zend := 2 * zlen) (retained := 4 * ulen + 4)
        (inner := 4 * ulen) (kept := 8 * wlen + 8) (query := q) (tail := 2 * zlen + 2), none) := by
  have bv : ∀ r, (dropValues h.length (ptr := 8 * wlen + 8) (zend := 2 * zlen)
      (retained := 4 * ulen + 4) (inner := 4 * ulen) (query := q)
      (tail := 2 * zlen + 2)) r ≤ 4 * h.length + 4 := by
    apply dropValues_bound <;> omega
  have cp := drop_copy_run mode h 6 _ bv (by simp [dropCopy])
  simp [dropCopy] at cp
  apply cp.trans
  apply AReach.step ⟨drop_preS mode h _, by apply dropValues_bound <;> omega⟩
  simp [astep, dropARM]
  exact AReach.refl _

/-- Scan the inner pair after the outer payload pair has been recognized.

**Proof sketch.** Derive the inner end from the saved separator address, then instantiate
the received stride-four scan. A failed decode gives an empty output. A successful decode
saves the final prefix boundary and enters the proved segmented lookup. -/
private lemma drop_inner_run (mode : Bool) (u b' : List Bool) (q : ℕ)
    (hq : q ≤ 2 * (pairEncode (pairEncode u b') (Nat.bits q)).length) :
    let h := pairEncode (pairEncode u b') (Nat.bits q)
    let zlen := (pairEncode u b').length
    DropHalt mode h
      (some (.copy 4 false), dropValues h.length (ptr := 4 * u.length + 4) (zend := 2 * zlen)
        (query := q) (tail := 2 * zlen + 2), none)
      (if mode then decide (q < (dropIdx (pairEncode u b')).length)
        else (dropIdx (pairEncode u b')).getD q false) := by
  dsimp only
  let h := pairEncode (pairEncode u b') (Nat.bits q)
  let zlen := (pairEncode u b').length
  change q ≤ 2 * h.length at hq
  have hz : 2 * zlen + 2 ≤ h.length := by simp [h, zlen, length_pairEncode]
  have hu : 2 * u.length + 2 ≤ zlen := by simp [zlen, length_pairEncode]
  let v := dropValues h.length (zend := 2 * zlen) (retained := 4 * u.length + 4)
    (inner := 4 * u.length) (query := q) (tail := 2 * zlen + 2)
  have bv : ∀ r, v r ≤ 4 * h.length + 4 := by dsimp [v]; apply dropValues_bound <;> omega
  have prep := drop_u_prepare mode h zlen u.length q hz hu hq
  have reads : ∀ i < u.length, h.getD (v 0 + dropStride 2 * i) false = u.getD i false := by
    intro i hi
    have outer := drop_first_read (pairEncode u b') (Nat.bits q) (2 * i)
      (by rw [length_pairEncode]; omega)
    have inner := drop_first_read u b' i hi
    simpa [v, dropStride, h, show 2 * (2 * i) = 4 * i by omega] using outer.trans inner
  have scan := drop_pair_run mode h 2 u v bv (by simp [v, dropLimit, dropStride]) reads
  cases dec : pairDecode u with
  | none =>
    simp only [dec] at scan
    obtain ⟨t, ht, run⟩ := scan
    have bp : v 0 + dropStride 2 * t ≤ 4 * h.length + 4 := by simp only [v, dropValues_apply]; simp [dropStride]; omega
    have br := register_update_le v 0 _ _ bv bp
    have ans : (if mode then decide (q < (dropIdx (pairEncode u b')).length)
        else (dropIdx (pairEncode u b')).getD q false) = false := by
      simp [dropIdx, pairDecode_pairEncode, dec]
    rw [ans]
    exact (prep.trans run).halt (drop_ret mode false h _ br)
  | some pair =>
    rcases pair with ⟨w, b⟩
    have ue := eq_pairEncode_of_pairDecode u w b dec
    subst u
    have hw : 2 * w.length + 2 ≤ (pairEncode w b).length := by simp [length_pairEncode]
    simp only [pairDecode_pairEncode] at scan
    have scan' : DropReach mode h (some (.scan 2), v, none)
        (some (.copy 6 false), dropValues h.length (ptr := 8 * w.length + 8) (zend := 2 * zlen)
          (retained := 4 * (pairEncode w b).length + 4) (inner := 4 * (pairEncode w b).length)
          (query := q) (tail := 2 * zlen + 2), none) := by
      simpa [v, dropStride, dropScanDone, show 4 * (2 * w.length + 2) = 8 * w.length + 8 by omega] using scan
    have last := drop_lookup_prepare mode h zlen (pairEncode w b).length w.length q hz hu hw hq
    let vf := dropValues h.length (zend := 2 * zlen) (retained := 4 * (pairEncode w b).length + 4)
      (inner := 4 * (pairEncode w b).length) (kept := 8 * w.length + 8)
      (query := q) (tail := 2 * zlen + 2)
    have bf : ∀ r, vf r ≤ 4 * h.length + 4 := by dsimp [vf]; apply dropValues_bound <;> omega
    have lookup := drop_lookup mode w b b' q vf bf (by simp [vf])
      (by simp [vf]; omega) (by simp [vf]) (by simp [vf, zlen, length_pairEncode]; omega)
      (by simp [vf]) (by simp [vf])
    exact (prep.trans (scan'.trans last)).halt lookup

/-- Scan the outer payload pair after the bounded query value is available.

**Proof sketch.** Prepare the physical first-field end and cite the received stride-two
pair scan. Malformed payloads have empty output. Otherwise the scan's boundary is precisely
the retained suffix start, and the inner-pair run completes the computation. -/
private lemma drop_nested_run (mode : Bool) (z : List Bool) (q : ℕ)
    (hq : q ≤ 2 * (pairEncode z (Nat.bits q)).length) :
    let h := pairEncode z (Nat.bits q)
    DropHalt mode h
      (some (.copy 3 false), dropValues h.length (ptr := 2 * z.length + 2)
        (query := q) (tail := 2 * z.length + 2), none)
      (if mode then decide (q < (dropIdx z).length) else (dropIdx z).getD q false) := by
  dsimp only
  let h := pairEncode z (Nat.bits q)
  change q ≤ 2 * h.length at hq
  have hz : 2 * z.length + 2 ≤ h.length := by simp [h, length_pairEncode]
  let v := dropValues h.length (zend := 2 * z.length) (query := q) (tail := 2 * z.length + 2)
  have bv : ∀ r, v r ≤ 4 * h.length + 4 := by dsimp [v]; apply dropValues_bound <;> omega
  have prep := drop_z_prepare mode h z.length q hz hq
  have scan := drop_pair_run mode h 1 z v bv (by simp [v, dropLimit, dropStride])
    (by intro i hi; simpa [v, dropStride, h] using drop_first_read z (Nat.bits q) i hi)
  cases dec : pairDecode z with
  | none =>
    simp only [dec] at scan
    obtain ⟨t, ht, run⟩ := scan
    have bp : v 0 + dropStride 1 * t ≤ 4 * h.length + 4 := by simp [v, dropStride]; omega
    have br := register_update_le v 0 _ _ bv bp
    have ans : (if mode then decide (q < (dropIdx z).length) else (dropIdx z).getD q false) = false := by
      simp [dropIdx, dec]
    rw [ans]
    exact (prep.trans run).halt (drop_ret mode false h _ br)
  | some pair =>
    rcases pair with ⟨u, b'⟩
    have ze := eq_pairEncode_of_pairDecode z u b' dec
    subst z
    simp only [pairDecode_pairEncode] at scan
    have scan' : DropReach mode h (some (.scan 1), v, none)
        (some (.copy 4 false), dropValues h.length (ptr := 4 * u.length + 4)
          (zend := 2 * (pairEncode u b').length) (query := q)
          (tail := 2 * (pairEncode u b').length + 2), none) := by
      simpa [v, dropStride, dropScanDone, show 2 * (2 * u.length + 2) = 4 * u.length + 4 by omega] using scan
    exact (prep.trans scan').halt (drop_inner_run mode u b' q hq)

/-- The mode-parametrized language has the intended answer on every canonical query. -/
private lemma drop_lang_pair (mode : Bool) (z : List Bool) (q : ℕ) :
    MultiTapeTM.indicator (dropLang mode : Set (List Bool)) (pairEncode z (Nat.bits q)) =
      (if mode then decide (q < (dropIdx z).length) else (dropIdx z).getD q false) := by
  cases mode <;> simp [dropLang, indicator_indexLang_pairEncode]

/-- A failed outer pair decode excludes membership in either query language. -/
private lemma drop_bad_shape (mode : Bool) (h : List Bool) (hh : pairDecode h = none) :
    MultiTapeTM.indicator (dropLang mode : Set (List Bool)) h = false := by
  have no : h ∉ dropLang mode := by
    rintro ⟨z, q, rfl, _⟩
    simp [pairDecode_pairEncode] at hh
  simp [MultiTapeTM.indicator, no]

/-- A noncanonical index tail excludes membership in either query language. -/
private lemma drop_bad_tail (mode : Bool) (z tail : List Bool) (hc : ¬ Canon tail) :
    MultiTapeTM.indicator (dropLang mode : Set (List Bool)) (pairEncode z tail) = false := by
  have no : pairEncode z tail ∉ dropLang mode := by
    rintro ⟨w, q, eq, _⟩
    have fields := pairEncode_injective (a₁ := (z, tail)) (a₂ := (w, Nat.bits q)) eq
    have ht : tail = Nat.bits q := congrArg Prod.snd fields
    exact hc (ht ▸ canon_bits q)
  simp [MultiTapeTM.indicator, no]

/-- Rejection by canonicality or by the pre-decode width check is semantically correct. -/
private lemma drop_rejected_tail (mode : Bool) (z tail : List Bool)
    (bad : ¬ (Canon tail ∧ tail.length ≤ (Nat.bits (pairEncode z tail).length).length)) :
    MultiTapeTM.indicator (dropLang mode : Set (List Bool)) (pairEncode z tail) = false := by
  by_cases hc : Canon tail
  · obtain ⟨q, rfl⟩ : ∃ q, tail = Nat.bits q := ⟨bitsVal tail, canon_eq_bits tail hc⟩
    have width : (Nat.bits (pairEncode z (Nat.bits q)).length).length < (Nat.bits q).length := by
      have notle : ¬ (Nat.bits q).length ≤ (Nat.bits (pairEncode z (Nat.bits q)).length).length :=
        fun hw => bad ⟨hc, hw⟩
      omega
    obtain ⟨bit, len⟩ := dropIdx_query_overflow z q width
    rw [drop_lang_pair]
    cases mode with
    | false => exact bit
    | true => simp [len]
  · exact drop_bad_tail mode z tail hc

/-- The single table decides both index-dropping query languages on all host strings.

**Proof sketch.** Count the host length and validate the outer aligned pair. A malformed
host rejects. On a pair, the canonical-width validator either rejects correctly or supplies
a bounded index to the reverse decoder. The two nested shape scans and segmented lookup
then produce the query answer. Every composed segment has the same linear register bound. -/
private lemma drop_run (mode : Bool) (h : List Bool) :
    DropHalt mode h (some .lengthTest, fun _ => 0, none)
      (MultiTapeTM.indicator (dropLang mode : Set (List Bool)) h) := by
  have count := inputLength_loop (dropARM mode) dropOracle h 1 1 .lengthTest .lengthInc (.scan 0)
    rfl rfl (fun i _ => drop_len h i) (4 * h.length + 4) (by omega) (fun _ => 0)
    (by intro r; exact Nat.zero_le _) (by exact Nat.zero_le _)
  have vec : Function.update (fun _ : Fin 9 => 0) 1 h.length = dropValues h.length := by
    apply funext
    simp [Fin.forall_fin_succ, Function.update_apply]
  rw [vec] at count
  have bv : ∀ r, (dropValues h.length) r ≤ 4 * h.length + 4 := by
    apply dropValues_bound <;> omega
  have scan := drop_pair_run mode h 0 h (dropValues h.length) bv
    (by simp [dropLimit, dropStride]) (by intro i _; simp [dropStride])
  cases hd : pairDecode h with
  | none =>
    simp only [hd] at scan
    obtain ⟨t, ht, path⟩ := scan
    have bp : (dropValues h.length) 0 + dropStride 0 * t ≤ 4 * h.length + 4 := by
      simp [dropStride]; omega
    have br := register_update_le (dropValues h.length) 0 _ _ bv bp
    rw [drop_bad_shape mode h hd]
    exact (count.trans path).halt (drop_ret mode false h _ br)
  | some pair =>
    rcases pair with ⟨z, tail⟩
    have eq := eq_pairEncode_of_pairDecode h z tail hd
    subst h
    simp only [pairDecode_pairEncode] at scan
    have start : DropReach mode (pairEncode z tail) (some .lengthTest, fun _ => 0, none)
        (some (.copy 0 false), dropValues (pairEncode z tail).length (ptr := 2 * z.length + 2), none) := by
      apply count.trans
      simpa [dropStride, dropScanDone] using scan
    have decode := drop_tail_decode mode z tail
    by_cases good : Canon tail ∧ tail.length ≤ (Nat.bits (pairEncode z tail).length).length
    · simp only [if_pos good] at decode
      obtain ⟨q, rfl⟩ : ∃ q, tail = Nat.bits q := ⟨bitsVal tail, canon_eq_bits tail good.1⟩
      have qb := query_index_bound q (pairEncode z (Nat.bits q)).length good.2
      simp only [bitsVal_bits] at decode
      rw [drop_lang_pair]
      exact (start.trans decode).halt (drop_nested_run mode z q qb)
    · simp only [if_neg good] at decode
      rw [drop_rejected_tail mode z tail good]
      exact start.halt decode

/-- Compile the one bounded table against the proved input-access bank. -/
private lemma drop_mem (mode : Bool) : dropLang mode ∈ LOGSPACE := by
  have bank : ∀ j, dropBank j ∈ LOGSPACE := by
    intro j
    have cases : j = 0 ∨ j = 1 := by omega
    rcases cases with rfl | rfl
    · exact inputBitLang_mem
    · exact inputLenLang_mem
  apply arm_decides_poly (dropARM mode) .lengthTest dropBank bank 4 1
  intro h
  exact (drop_run mode h).mono (fun a ⟨hs, hv⟩ =>
    ⟨hs, fun r => by simpa [Nat.mul_add] using hv r⟩)

/-- **Dropping the middle index is implicitly logspace computable** (phase P4.4b; proved).

**Proof sketch.**

* **Bound.** `Complexity.dropIdx_length_le`.
* **The ARM.** Both query languages come from one abstract register machine with a mode bit
  over the access bank `![inputBitLang, inputLenLang]` (`inputBitLang_mem`,
  `inputLenLang_mem`), by `LogProg.arm_decides_poly`. A `whole` call on `[r]` reads the host's
  bit at `v r` (`LogProg.vword_whole₁`, `indicator_indexLang_pairEncode`).
* **The run, on a host `h = ⟨z, bits q⟩`.**
  * Validate `h` and its canonical tail.
  * Before accumulating `q`, compare the tail's length with `|bits |h||`. If longer, then
    `q ≥ |h| ≥ |dropIdx z|` and the answer is `false`.
  * Decode `z = ⟨u, b'⟩` and `u = ⟨w, b⟩` by aligned scans at strides 2 and 4 of `h`. A failed
    decode means `dropIdx z = []`, and the answer is `false`.
  * Answer by position arithmetic: positions below `2|w| + 2` come from `u`, the rest from
    `b'`.
* **Registers** are at most `4|h| + 4`. -/
theorem implicitlyLogspaceComputable_dropIdx : ImplicitlyLogspaceComputable dropIdx := by
  refine ⟨⟨1, 1, fun z => ?_⟩, ?_, ?_⟩
  · simpa using (dropIdx_length_le z).trans (Nat.le_succ z.length)
  · simpa only [dropLang, Bool.false_eq_true, ↓reduceIte] using drop_mem false
  · simpa only [dropLang, ↓reduceIte] using drop_mem true

/-! ## The composition oracle bank -/

/-- The query languages of `f` lifted through the two discarded host indices. -/
private def compLift (f : List Bool → List Bool) (lengthMode : Bool) : Language Bool :=
  {z | dropIdx (dropIdx z) ∈ indexLang (fun x i =>
    if lengthMode then i < (f x).length else (f x).getD i false = true)}

/-- Both lifted languages are in logspace by two applications of the proved preimage
construction along the now-proved index-dropping map. -/
private lemma compLift_mem {f : List Bool → List Bool} (hf : ImplicitlyLogspaceComputable f)
    (mode : Bool) : compLift f mode ∈ LOGSPACE := by
  have query : indexLang (fun x i => if mode then i < (f x).length
      else (f x).getD i false = true) ∈ LOGSPACE := by
    cases mode
    · exact hf.2.1
    · exact hf.2.2
  exact mem_LOGSPACE_preimage implicitlyLogspaceComputable_dropIdx
    (mem_LOGSPACE_preimage implicitlyLogspaceComputable_dropIdx query)

/-- The four-oracle bank for query reshaping: physical bit/length, then lifted bit/length. -/
private def compBank (f : List Bool → List Bool) : Fin 4 → Language Bool :=
  ![inputBitLang, inputLenLang, compLift f false, compLift f true]

/-- Each of the four oracle languages is proved to belong to logspace. -/
private lemma compBank_mem {f : List Bool → List Bool} (hf : ImplicitlyLogspaceComputable f) :
    ∀ j, compBank f j ∈ LOGSPACE := by
  intro j
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hj with rfl | rfl | rfl | rfl
  · exact inputBitLang_mem
  · exact inputLenLang_mem
  · exact compLift_mem hf false
  · exact compLift_mem hf true

/-- A lifted call from the twice-paired host is a genuine query about `f x`. The retained
inner payload may be arbitrary here: canonicality is a separate validation obligation. -/
private lemma compLift_query (f : List Bool → List Bool) (mode : Bool)
    (x b : List Bool) (p j : ℕ) :
    MultiTapeTM.indicator (compLift f mode : Set (List Bool))
        (pairEncode (pairEncode (pairEncode x b) (Nat.bits p)) (Nat.bits j)) =
      (if mode then decide (j < (f x).length) else (f x).getD j false) := by
  have transport : MultiTapeTM.indicator (compLift f mode : Set (List Bool))
        (pairEncode (pairEncode (pairEncode x b) (Nat.bits p)) (Nat.bits j)) =
      MultiTapeTM.indicator (indexLang (fun y i =>
        if mode then i < (f y).length else (f y).getD i false = true) : Set (List Bool))
        (pairEncode x (Nat.bits j)) := by
    simp only [compLift, MultiTapeTM.indicator, Set.mem_setOf_eq, dropIdx_pairEncode]
  rw [transport, indicator_indexLang_pairEncode]
  cases mode <;> simp

/-- The full composition output cap can be computed from the physical query-host length.
It also covers malformed inner inputs, through the landed total output-length bound. -/
private lemma compQ_host_cap {f : List Bool → List Bool} {C e : ℕ}
    (hf : ∀ x, (f x).length ≤ C * (x.length + 1) ^ e) (w tail : List Bool) :
    (compQ f w).length ≤ (2 * C + 3) * ((pairEncode w tail).length + 1) ^ (e + 1) := by
  apply (compQ_length_le hf w).trans
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  simp only [length_pairEncode]
  omega

/-- A canonical index wider than the full composition cap is rejected before decoding.
This uses the composition bound, rather than the shorter index-dropping bound. -/
private lemma compQ_query_overflow {f : List Bool → List Bool} {C e : ℕ}
    (hf : ∀ x, (f x).length ≤ C * (x.length + 1) ^ e) (w : List Bool) (p : ℕ)
    (wide : (Nat.bits ((2 * C + 3) * ((pairEncode w (Nat.bits p)).length + 1) ^ (e + 1))).length <
      (Nat.bits p).length) :
    (compQ f w).getD p false = false ∧ ¬ p < (compQ f w).length := by
  have large : (2 * C + 3) * ((pairEncode w (Nat.bits p)).length + 1) ^ (e + 1) < p :=
    Nat.lt_of_not_ge (fun h => (Nat.not_lt_of_ge (length_bits_mono h)) wide)
  have outside : (compQ f w).length ≤ p := (compQ_host_cap hf w (Nat.bits p)).trans (Nat.le_of_lt large)
  constructor
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none outside]
  · exact Nat.not_lt.mpr outside

/-- **`comp`'s query reshaping is implicitly logspace computable** (phase P4.4b; spec, fill
pending): if `f` is, so is `compQ f`.

**Proof sketch.**

* **Bound.** `Complexity.compQ_length_le`.
* **The ARM.** Both query languages come from one abstract register machine with a mode bit
  over a four-oracle bank (`LogProg.arm_decides_poly`):
  * `inputBitLang` and `inputLenLang`;
  * `{z | dropIdx (dropIdx z) ∈ L}` for `L` each of `f`'s two query languages. These are in
    `L` by `Complexity.mem_LOGSPACE_preimage` twice along
    `Complexity.implicitlyLogspaceComputable_dropIdx`.

  A `whole` call on `[j]` from the host `h = ⟨w, bits p⟩` presents
  `⟨⟨w, bits p⟩, bits j⟩`, which two `dropIdx` turn into `⟨x, bits j⟩` (`dropIdx_pairEncode`).
* **The run** ([AB09, Lemma 4.17's proof]; the P4.4 audit's question-2 ledger):
  * (i) Validate `h`, with the overflow test before storing `p`.
  * (ii) Validate `w = ⟨x, b⟩` with `b` canonical: empty (the representation of `0`) or
    ending in `true`, using `LogProg.canon_eq_bits` and `LogProg.canon_bits`.
  * (iii) Find `F := |f x|` by lifted length queries at `j = 0, 1, …` while `j` is below the
    cap `C (|x| + 1)^e`. `F` is the first `j` whose query fails, or the cap itself when every
    query below it succeeds, since `|f x|` is at most the cap. A cap of `0` gives `F = 0`
    with no query.
  * (iv) Answer:
    * `p < 2F`: the lifted bit at `⌊p/2⌋`;
    * `p ∈ {2F, 2F + 1}`: the separator `[false, true]`;
    * otherwise: `b`'s bit at `p − 2F − 2`, read from `h` at its doubled position;
    * length: `p < 2F + 2 + |b|`. -/
theorem ImplicitlyLogspaceComputable.compQ {f : List Bool → List Bool}
    (hf : ImplicitlyLogspaceComputable f) : ImplicitlyLogspaceComputable (compQ f) := by
  sorry

end Complexity
