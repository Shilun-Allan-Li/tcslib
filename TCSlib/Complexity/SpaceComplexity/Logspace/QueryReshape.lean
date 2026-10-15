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
  computable (proved; phase-P4.4b statements).

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
  exact indicator_inputBitLang h i

/-- A length call tests a host position. -/
private lemma drop_len (h : List Bool) (i : ℕ) :
    dropOracle 1 (pairEncode h (Nat.bits i)) = decide (i < h.length) := by
  change MultiTapeTM.indicator (inputLenLang : Set (List Bool)) _ = _
  exact indicator_inputLenLang h i

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

/-! ## B7 continuation 3: the composition-query machine -/

set_option synthInstance.maxSize 2000 in
/-- Finite control for the one composition-query ARM. The two polynomial evaluations
share their multiplication and fixed-scaling code; all input access goes through the
four proved oracle languages. -/
private inductive CompState (C e : ℕ) where
  | count | countInc
  | copy (stage : Fin 8) (bump : Bool)
  | scan (inner : Bool) | first (inner : Bool)
  | second (inner bit : Bool) | readSecond (inner bit : Bool)
  | scanInc (inner : Bool) (choice : Fin 4) (step : Fin 2)
  | outerDec (second : Bool) | baseInc
  | polyStart (outer : Bool) | power (outer : Bool) (remaining : Fin (e + 2))
  | productCopy (outer : Bool) (remaining : Fin (e + 2)) (bump : Bool)
  | productClear (outer : Bool) (remaining : Fin (e + 2))
  | productTest (outer : Bool) (remaining : Fin (e + 2))
  | productAddCopy (outer : Bool) (remaining : Fin (e + 2)) (bump : Bool)
  | productAdd (outer : Bool) (remaining : Fin (e + 2))
  | productTake (outer : Bool) (remaining : Fin (e + 2))
  | productInc (outer : Bool) (remaining : Fin (e + 2))
  | productNext (outer : Bool) (remaining : Fin (e + 2))
  | productClean (outer : Bool) (remaining : Fin (e + 2)) (second : Bool)
  | factorCopy (outer bump : Bool) | factorClear (outer : Bool)
  | factorTest (outer : Bool) | factorDown (outer : Bool)
  | factorInc (outer : Bool) (step : Fin (2 * C + 3))
  | tailTest (last : Bool) | tailCheck | tailRead | tailHalf (bit : Bool) | tailInc (bit : Bool)
  | tailDone | resetDecode
  | decode | decodeDown | decodeRead | decodeCopy (bit bump : Bool)
  | decodeClear (bit : Bool) | decodeScale (bit : Bool) | decodeTake (bit : Bool)
  | decodeInc (bit second : Bool) | decodeAdd (bit : Bool) | decodeDone
  | canonical | canonicalReset | canonicalDec (second : Bool) | canonicalRead
  | innerPrepare | innerHalf (second : Bool)
  | lengthBound | lengthQuery | lengthInc
  | doubleTest | doubleDown | doubleInc (second : Bool) | lookupReset
  | seek (suffix : Bool) | probe (suffix : Bool) | next (suffix : Bool)
  | walk (suffix second : Bool) | prefixHit | prefixBit | suffixHit
  | separator (second : Bool) | separatorInc (second : Bool) | suffixReset
  | answer (bit : Bool)
  deriving DecidableEq, Fintype

/-- Saved boundaries and base values use the received bounded copy loop. -/
private def compCopy (C e : ℕ) : Fin 8 → Fin 14 × Fin 14 × CompState C e
  | 0 => (2, 0, .copy 1 false)
  | 1 => (3, 2, .outerDec false)
  | 2 => (8, 1, .baseInc)
  | 3 => (0, 1, .decode)
  | 4 => (4, 0, .canonical)
  | 5 => (0, 3, .canonicalDec false)
  | 6 => (8, 4, .innerHalf false)
  | 7 => (0, 4, .seek true)

/-- The outer query uses stride one; its first field uses stride two. -/
private def compStride (inner : Bool) : ℕ := if inner then 2 else 1

/-- Each shape validator stops at its previously saved physical boundary. -/
private def compLimit (inner : Bool) : Fin 14 := if inner then 3 else 1

/-- The finite chains instantiate the public aligned-pair validator. -/
private def compAdvance (C e : ℕ) (inner : Bool) (choice : Fin 4) (i : ℕ) : CompState C e :=
  if h : i < compStride inner then .scanInc inner choice ⟨i, by
    cases inner <;> simp_all [compStride]⟩
  else ![.second inner false, .second inner true, .scan inner,
    .copy (if inner then 4 else 0) false] choice

/-- The coefficient is fixed in the control, and can be zero on the inner evaluation. -/
private def compFactor (C : ℕ) (outer : Bool) : ℕ := if outer then 2 * C + 3 else C

/-- Fixed scaling uses the public transfer loop, including a zero multiplier. -/
private def compFactorAdvance (C e : ℕ) (outer : Bool) (i : ℕ) : CompState C e :=
  if h : i < compFactor C outer then .factorInc outer ⟨i, by
    cases outer <;> simp_all [compFactor]
    omega⟩ else .factorTest outer

/-- The reverse decoder has its standard two increments per transferred unit. -/
private def compDecodeAdvance (C e : ℕ) (b : Bool) (i : ℕ) : CompState C e :=
  match dropDecodeAdvance b i with
  | .decodeInc bit second => .decodeInc bit second
  | _ => .decodeScale b

/-- A single finite ARM supplies both composition-query languages. Registers 0--5 are
pointer, host length, outer-tail start, inner end, inner-tail start, and bounded query;
6--8 and 10--11 are arithmetic scratch; 12 is the searched output length and 13 the
output-position counter. Register 9 is unused. -/
private def compARM (C e : ℕ) (mode : Bool) : ARM 14 4 (CompState C e)
  | .count => .call 1 .whole [1] .countInc (.scan false)
  | .countInc => .inc 1 .count
  | .copy s false => .jeq (compCopy C e s).1 (compCopy C e s).2.1
      (compCopy C e s).2.2 (.copy s true)
  | .copy s true => .inc (compCopy C e s).1 (.copy s false)
  | .scan inner => .jeq 0 (compLimit inner) (.answer false) (.first inner)
  | .first inner => .call 0 .whole [0] (compAdvance C e inner 1 0) (compAdvance C e inner 0 0)
  | .second inner b => .jeq 0 (compLimit inner) (.answer false) (.readSecond inner b)
  | .readSecond inner b => .call 0 .whole [0]
      (if b then compAdvance C e inner 2 0 else compAdvance C e inner 3 0)
      (if b then .answer false else compAdvance C e inner 2 0)
  | .scanInc inner choice i => .inc 0 (compAdvance C e inner choice (i.val + 1))
  | .outerDec false => .dec 3 (.outerDec true)
  | .outerDec true => .dec 3 (.copy 2 false)
  | .baseInc => .inc 8 (.polyStart true)
  | .polyStart outer => .inc 7 (.power outer ⟨if outer then e + 1 else e, by
      cases outer <;> simp⟩)
  | .power outer k => .jz 6 (if k.val = 0 then .factorCopy outer false
      else .productCopy outer k false) (.answer false)
  | .productCopy outer k false => .jeq 11 7 (.productClear outer k) (.productCopy outer k true)
  | .productCopy outer k true => .inc 11 (.productCopy outer k false)
  | .productClear outer k => .clr 7 (.productTest outer k)
  | .productTest outer k => .jeq 10 8 (.productClean outer k false) (.productAddCopy outer k false)
  | .productAddCopy outer k false => .jeq 6 11 (.productAdd outer k) (.productAddCopy outer k true)
  | .productAddCopy outer k true => .inc 6 (.productAddCopy outer k false)
  | .productAdd outer k => .jz 6 (.productNext outer k) (.productTake outer k)
  | .productTake outer k => .dec 6 (.productInc outer k)
  | .productInc outer k => .inc 7 (.productAdd outer k)
  | .productNext outer k => .inc 10 (.productTest outer k)
  | .productClean outer k false => .clr 11 (.productClean outer k true)
  | .productClean outer k true => .clr 10 (.power outer ⟨k.val - 1, by omega⟩)
  | .factorCopy outer false => .jeq 11 7 (.factorClear outer) (.factorCopy outer true)
  | .factorCopy outer true => .inc 11 (.factorCopy outer false)
  | .factorClear outer => .clr 7 (.factorTest outer)
  | .factorTest outer => .jz 11 (if outer then .tailTest true else .lengthBound) (.factorDown outer)
  | .factorDown outer => .dec 11 (compFactorAdvance C e outer 0)
  | .factorInc outer i => .inc 7 (compFactorAdvance C e outer (i.val + 1))
  | .tailTest b => .jeq 0 1 (if b then .tailDone else .answer false) .tailCheck
  | .tailCheck => .jz 7 (.answer false) .tailRead
  | .tailRead => .call 0 .whole [0] (.tailHalf true) (.tailHalf false)
  | .tailHalf b => .half 7 (.tailInc b)
  | .tailInc b => .inc 0 (.tailTest b)
  | .tailDone => .clr 7 .resetDecode
  | .resetDecode => .clr 0 (.copy 3 false)
  | .decode => .jeq 0 2 .decodeDone .decodeDown
  | .decodeDown => .dec 0 .decodeRead
  | .decodeRead => .call 0 .whole [0] (.decodeCopy true false) (.decodeCopy false false)
  | .decodeCopy b false => .jeq 6 5 (.decodeClear b) (.decodeCopy b true)
  | .decodeCopy b true => .inc 6 (.decodeCopy b false)
  | .decodeClear b => .clr 5 (.decodeScale b)
  | .decodeScale b => .jz 6 (.decodeAdd b) (.decodeTake b)
  | .decodeTake b => .dec 6 (.decodeInc b false)
  | .decodeInc b false => .inc 5 (.decodeInc b true)
  | .decodeInc b true => .inc 5 (.decodeScale b)
  | .decodeAdd b => if b then .inc 5 .decode else .jz 6 .decode .decode
  | .decodeDone => .clr 0 (.scan true)
  | .canonical => .jeq 4 3 .innerPrepare .canonicalReset
  | .canonicalReset => .clr 0 (.copy 5 false)
  | .canonicalDec false => .dec 0 (.canonicalDec true)
  | .canonicalDec true => .dec 0 .canonicalRead
  | .canonicalRead => .call 0 .whole [0] .innerPrepare (.answer false)
  | .innerPrepare => .clr 8 (.copy 6 false)
  | .innerHalf false => .half 8 (.innerHalf true)
  | .innerHalf true => .half 8 (.polyStart false)
  | .lengthBound => .jeq 12 7 .doubleTest .lengthQuery
  | .lengthQuery => .call 3 .whole [12] .lengthInc .doubleTest
  | .lengthInc => .inc 12 .lengthBound
  | .doubleTest => .jz 12 .lookupReset .doubleDown
  | .doubleDown => .dec 12 (.doubleInc false)
  | .doubleInc false => .inc 11 (.doubleInc true)
  | .doubleInc true => .inc 11 .doubleTest
  | .lookupReset => .clr 0 (.seek false)
  | .seek suffix => .jeq 0 (if suffix then 3 else 11)
      (if suffix then .answer false else .separator false) (.probe suffix)
  | .probe suffix => .jeq 13 5 (if suffix then .suffixHit else .prefixHit) (.next suffix)
  | .next suffix => .inc 13 (.walk suffix false)
  | .walk suffix false => .inc 0 (if suffix then .walk suffix true else .seek suffix)
  | .walk suffix true => .inc 0 (.seek suffix)
  | .prefixHit => if mode then .ret true else .half 0 .prefixBit
  | .prefixBit => .call 2 .whole [0] (.answer true) (.answer false)
  | .suffixHit => if mode then .ret true else .call 0 .whole [0] (.answer true) (.answer false)
  | .separator false => .jeq 13 5 (.answer mode) (.separatorInc false)
  | .separator true => .jeq 13 5 (.answer true) (.separatorInc true)
  | .separatorInc false => .inc 13 (.separator true)
  | .separatorInc true => .inc 13 .suffixReset
  | .suffixReset => .clr 0 (.copy 7 false)
  | .answer b => .ret b

/-- The actual four-oracle answers, independent of the machine mode and polynomial witness. -/
private noncomputable def compOracle (f : List Bool → List Bool) (j : Fin 4) (w : List Bool) : Bool :=
  MultiTapeTM.indicator (compBank f j : Set (List Bool)) w

/-- The register bound covers both the full output cap and twice that cap for decoding. -/
private def compBound (C e n : ℕ) : ℕ := 8 * (2 * C + 3) * (n + 1) ^ (e + 1)

/-- All syntactic side conditions are independent of the input and register values.

**Proof sketch.** Inspect each finite control constructor. Calls have singleton register
lists, and copy, transfer, decoder, and comparison registers are distinct. -/
private lemma comp_preS (C e : ℕ) (mode : Bool) (h : List Bool) (a : AConf 14 (CompState C e)) :
    PreS (compARM C e mode) h a := by
  rcases a with ⟨l, v, ans⟩
  cases l with
  | none => trivial
  | some l =>
    cases l <;> simp only [PreS, compARM] <;> try decide
    case copy stage bump =>
      cases bump
      · change (compCopy C e stage).1 ≠ (compCopy C e stage).2.1
        exact (show ∀ s, (compCopy C e s).1 ≠ (compCopy C e s).2.1 by
          simp [Fin.forall_fin_succ, compCopy]) stage
      · simp
    case scan inner => cases inner <;> simp [compLimit]
    case second inner bit => cases inner <;> simp [compLimit]
    case outerDec b => cases b <;> simp
    case productCopy outer k b => cases b <;> simp
    case productAddCopy outer k b => cases b <;> simp
    case productClean outer k b => cases b <;> simp
    case factorCopy outer b => cases b <;> simp
    case decodeCopy bit b => cases b <;> simp
    case decodeInc bit b => cases b <;> simp
    case decodeAdd bit => cases bit <;> simp
    case canonicalDec b => cases b <;> simp
    case innerHalf b => cases b <;> simp
    case doubleInc b => cases b <;> simp
    case seek suffix => cases suffix <;> simp
    case walk suffix b => cases b <;> simp
    case prefixHit => cases mode <;> simp
    case suffixHit => cases mode <;> simp
    case separator b => cases b <;> simp
    case separatorInc b => cases b <;> simp

/-- A physical input bit uses exactly the already-proved access-bank law. -/
private lemma comp_bit (f : List Bool → List Bool) (h : List Bool) (i : ℕ) :
    compOracle f 0 (pairEncode h (Nat.bits i)) = h.getD i false :=
  drop_bit h i

/-- A physical input length call uses the same proved access-bank law. -/
private lemma comp_len (f : List Bool → List Bool) (h : List Bool) (i : ℕ) :
    compOracle f 1 (pairEncode h (Nat.bits i)) = decide (i < h.length) :=
  drop_len h i

/-- A genuine lifted call is answered by the received two-drop identity. -/
private lemma comp_lifted (f : List Bool → List Bool) (mode : Bool) (x b : List Bool) (p i : ℕ) :
    compOracle f (if mode then 3 else 2)
      (pairEncode (pairEncode (pairEncode x b) (Nat.bits p)) (Nat.bits i)) =
        if mode then decide (i < (f x).length) else (f x).getD i false := by
  cases mode <;> exact compLift_query f _ x b p i


/-- One common guard supplies the syntactic and register conditions to both received
run relations. -/
private abbrev CompGood (C e : ℕ) (mode : Bool) (h : List Bool) (B : ℕ) (a : AConf 14 (CompState C e)) :=
  PreS (compARM C e mode) h a ∧ ∀ r, a.2.1 r ≤ B

/-- Bounded runs use the received reachability relation, with no extra semantic assumption. -/
private abbrev CompReach (C e : ℕ) (mode : Bool) (f : List Bool → List Bool) (h : List Bool) (B : ℕ) :=
  AReach (compARM C e mode) (compOracle f) h (CompGood C e mode h B)

/-- The corresponding bounded halting assertion. -/
private abbrev CompHalt (C e : ℕ) (mode : Bool) (f : List Bool → List Bool) (h : List Bool) (B : ℕ) :=
  AHalt (compARM C e mode) (compOracle f) h (CompGood C e mode h B)

/-- The multiplication body repeatedly adds the saved multiplicand, preserving the base.

**Proof sketch.** Induct on the remaining repetition count. Each iteration invokes the
public counting copy and the public unit transfer. The final sum bounds every temporary
sum; the scratch is zero at both boundaries. -/
private lemma comp_product (C e : ℕ) (mode outer : Bool) (f : List Bool → List Bool)
    (h : List Bool) (k : Fin (e + 2)) (B : ℕ) (v : Fin 14 → ℕ)
    (hv : ∀ r, v r ≤ B) (ht : v 6 = 0) (hi : v 10 ≤ v 8)
    (hb : v 7 + (v 8 - v 10) * v 11 ≤ B) :
    CompReach C e mode f h B (some (.productTest outer k), v, none)
      (some (.productClean outer k false),
        Function.update (Function.update v 10 (v 8)) 7
          (v 7 + (v 8 - v 10) * v 11), none) := by
  generalize he : v 8 - v 10 = left
  induction left generalizing v with
  | zero =>
    have eq : v 10 = v 8 := by omega
    have up : Function.update v 10 (v 8) = v := by rw [← eq, Function.update_eq_self]
    simp only [Nat.zero_mul, Nat.add_zero, up, Function.update_eq_self]
    simpa [astep, compARM, eq] using
      (AReach.single (A := compARM C e mode) (oracle := compOracle f) (x := h)
        (a := (some (.productTest outer k), v, none)) ⟨comp_preS C e mode h _, hv⟩)
  | succ left ih =>
    have lt : v 10 < v 8 := by omega
    have total : v 7 + v 11 + left * v 11 ≤ B := by
      rw [he, Nat.succ_mul] at hb
      omega
    let vc := Function.update v 6 (v 11)
    let va := Function.update v 7 (v 7 + v 11)
    let vn := Function.update va 10 (v 10 + 1)
    have bc : ∀ r, vc r ≤ B := register_update_le v 6 B _ hv (hv 11)
    have ba : ∀ r, va r ≤ B := register_update_le v 7 B _ hv (by omega)
    have bn : ∀ r, vn r ≤ B := register_update_le va 10 B _ ba (by have := hv 8; omega)
    have cp := registerCopy_loop (compARM C e mode) (compOracle f) h 6 11 (by decide)
      (.productAddCopy outer k false) (.productAddCopy outer k true) (.productAdd outer k)
      rfl rfl B v hv (by rw [ht]; exact Nat.zero_le _)
    have add := registerScale_loop (compARM C e mode) (compOracle f) h 6 7 (by decide)
      (.productAdd outer k) (.productTake outer k) (.productNext outer k)
      (fun i => if i = 0 then .productInc outer k else .productAdd outer k) 1
      rfl rfl (by
        intro i hi
        have hz : i = 0 := by omega
        subst i
        rfl) rfl B vc bc
      (by simp [vc]; omega)
    have addend : Function.update (Function.update vc 6 0) 7 (vc 7 + 1 * vc 6) = va := by
      simp [vc, va, ← ht, Function.update_eq_self]
    rw [addend] at add
    have rest := ih vn bn (by simp [vn, va, ht]) (by simp [vn, va]; omega)
      (by simp only [vn, va, Function.update_self, Function.update_of_ne (by decide : (8 : Fin 14) ≠ 10),
          Function.update_of_ne (by decide : (8 : Fin 14) ≠ 7),
          Function.update_of_ne (by decide : (7 : Fin 14) ≠ 10),
          Function.update_of_ne (by decide : (11 : Fin 14) ≠ 10),
          Function.update_of_ne (by decide : (11 : Fin 14) ≠ 7)]
          have eq : v 8 - (v 10 + 1) = left := by omega
          rw [eq]; exact total)
      (by simp [vn, va]; omega)
    have endeq : Function.update (Function.update vn 10 (vn 8)) 7
        (vn 7 + left * vn 11) =
        Function.update (Function.update v 10 (v 8)) 7
          (v 7 + (left + 1) * v 11) := by
      funext r
      by_cases h7 : r = 7
      · subst r; simp [vn, va, Nat.succ_mul]; omega
      · by_cases h10 : r = 10
        · subst r; simp [vn, va]
        · simp [vn, va, Function.update_of_ne, h7, h10]
    rw [endeq] at rest
    apply AReach.step ⟨comp_preS C e mode h _, hv⟩
    simp only [astep, compARM, if_neg (Nat.ne_of_lt lt)]
    apply cp.trans
    apply add.trans
    apply AReach.step ⟨comp_preS C e mode h _, ba⟩
    simpa only [astep, compARM, va, Function.update_of_ne (by decide : (10 : Fin 14) ≠ 7)] using rest


/-- One power round multiplies the accumulator by its base and restores all scratch.

**Proof sketch.** Save the old accumulator with the shared copy, clear the destination,
invoke the proved repeated-addition loop, and clear its two counters. -/
private lemma comp_multiply (C e : ℕ) (mode outer : Bool) (f : List Bool → List Bool)
    (h : List Bool) (k : Fin (e + 2)) (B : ℕ) (v : Fin 14 → ℕ)
    (hv : ∀ r, v r ≤ B) (ht : v 6 = 0) (hi : v 10 = 0) (hs : v 11 = 0)
    (hb : v 7 * v 8 ≤ B) :
    CompReach C e mode f h B (some (.productCopy outer k false), v, none)
      (some (.power outer ⟨k.val - 1, by omega⟩), Function.update v 7 (v 7 * v 8), none) := by
  let vc := Function.update v 11 (v 7)
  let vz := Function.update vc 7 0
  let ve := Function.update (Function.update vz 10 (v 8)) 7 (v 7 * v 8)
  have bc : ∀ r, vc r ≤ B := register_update_le v 11 B _ hv (hv 7)
  have bz : ∀ r, vz r ≤ B := register_update_le vc 7 B 0 bc (Nat.zero_le _)
  have be : ∀ r, ve r ≤ B := register_update_le _ 7 B _
    (register_update_le vz 10 B _ bz (hv 8)) hb
  have cp := registerCopy_loop (compARM C e mode) (compOracle f) h 11 7 (by decide)
    (.productCopy outer k false) (.productCopy outer k true) (.productClear outer k)
    rfl rfl B v hv (by rw [hs]; exact Nat.zero_le _)
  have body : CompReach C e mode f h B (some (.productTest outer k), vz, none)
      (some (.productClean outer k false), ve, none) := by
    simpa [vz, vc, ve, hi, Nat.mul_comm] using
      comp_product C e mode outer f h k B vz bz (by simp [vz, vc, ht])
        (by simp [vz, vc, hi]) (by simpa [vz, vc, hi, Nat.mul_comm] using hb)
  have clean : CompReach C e mode f h B (some (.productClean outer k false), ve, none)
      (some (.power outer ⟨k.val - 1, by omega⟩), Function.update v 7 (v 7 * v 8), none) := by
    apply AReach.step ⟨comp_preS C e mode h _, be⟩
    simp only [astep, compARM]
    have bound := register_update_le ve 11 B 0 be (Nat.zero_le _)
    have last := AReach.single (A := compARM C e mode) (oracle := compOracle f) (x := h)
      (G := fun a => PreS (compARM C e mode) h a ∧ ∀ r, a.2.1 r ≤ B)
      (a := (some (.productClean outer k true), Function.update ve 11 0, none))
      ⟨comp_preS C e mode h _, bound⟩
    have eq : Function.update (Function.update ve 11 0) 10 0 = Function.update v 7 (v 7 * v 8) := by
      funext r
      by_cases h7 : r = 7
      · subst r; simp [ve]
      · by_cases h10 : r = 10
        · subst r; simp [hi]
        · by_cases h11 : r = 11
          · subst r; simp [hs]
          · simp [ve, vz, vc, Function.update_of_ne, h7, h10, h11]
    simpa only [astep, compARM, eq] using last
  apply cp.trans
  apply AReach.step ⟨comp_preS C e mode h _, bc⟩
  exact body.trans clean

/-- The final constant scaling shares the proved transfer loop, even when the coefficient
is zero. Scratch register 11 is restored to zero.

**Proof sketch.** Copy the accumulator to the saved multiplicand, clear its destination,
apply `registerScale_loop` at the fixed coefficient, and clear the remaining scratch. -/
private lemma comp_factor_run (C e : ℕ) (mode outer : Bool) (f : List Bool → List Bool)
    (h : List Bool) (B : ℕ) (v : Fin 14 → ℕ) (hv : ∀ r, v r ≤ B)
    (hs : v 11 = 0) (hb : compFactor C outer * v 7 ≤ B) :
    CompReach C e mode f h B (some (.factorCopy outer false), v, none)
      (some (if outer then .tailTest true else .lengthBound),
        Function.update v 7 (compFactor C outer * v 7), none) := by
  let vc := Function.update v 11 (v 7)
  let vz := Function.update vc 7 0
  have bc : ∀ r, vc r ≤ B := register_update_le v 11 B _ hv (hv 7)
  have bz : ∀ r, vz r ≤ B := register_update_le vc 7 B 0 bc (Nat.zero_le _)
  have cp := registerCopy_loop (compARM C e mode) (compOracle f) h 11 7 (by decide)
    (.factorCopy outer false) (.factorCopy outer true) (.factorClear outer)
    rfl rfl B v hv (by rw [hs]; exact Nat.zero_le _)
  have scale := registerScale_loop (compARM C e mode) (compOracle f) h 11 7 (by decide)
    (.factorTest outer) (.factorDown outer) (if outer then .tailTest true else .lengthBound)
    (compFactorAdvance C e outer) (compFactor C outer) rfl rfl
    (by intro i hi; simp only [compFactorAdvance, dif_pos hi, compARM])
    (by simp [compFactorAdvance]) B vz bz (by simpa [vz, vc] using hb)
  have eq : Function.update (Function.update vz 11 0) 7
      (vz 7 + compFactor C outer * vz 11) = Function.update v 7 (compFactor C outer * v 7) := by
    funext r
    by_cases h7 : r = 7
    · subst r; simp [vz, vc]
    · by_cases h11 : r = 11
      · subst r; simp [hs]
      · simp [vz, vc, Function.update_of_ne, h7, h11]
  rw [eq] at scale
  apply cp.trans
  apply AReach.step ⟨comp_preS C e mode h _, bc⟩
  exact scale

/-- The power subprogram has a polynomial bound on every intermediate value.

**Proof sketch.** Induct on the remaining exponent. A nonzero exponent invokes one
multiplication round; its result is no larger than the final power because the base is
at least one. At zero, apply the fixed-scaling contract. -/
private lemma comp_power_run (C e : ℕ) (mode outer : Bool) (f : List Bool → List Bool)
    (h : List Bool) (k : Fin (e + 2)) (B : ℕ) (v : Fin 14 → ℕ)
    (hv : ∀ r, v r ≤ B) (ht : v 6 = 0) (hi : v 10 = 0) (hs : v 11 = 0)
    (hbase : 1 ≤ v 8) (hp : v 7 * v 8 ^ k.val ≤ B)
    (hf : compFactor C outer * (v 7 * v 8 ^ k.val) ≤ B) :
    CompReach C e mode f h B (some (.power outer k), v, none)
      (some (if outer then .tailTest true else .lengthBound),
        Function.update v 7 (compFactor C outer * (v 7 * v 8 ^ k.val)), none) := by
  generalize hn : k.val = n
  induction n generalizing k v with
  | zero =>
    simp only [pow_zero, Nat.mul_one]
    apply AReach.step ⟨comp_preS C e mode h _, hv⟩
    simp only [astep, compARM, ht, ↓reduceIte, hn]
    exact comp_factor_run C e mode outer f h B v hv hs (by simpa [hn] using hf)
  | succ n ih =>
    let vn := Function.update v 7 (v 7 * v 8)
    have prod : v 7 * v 8 ≤ B := by
      apply Nat.le_trans _ hp
      apply Nat.mul_le_mul_left
      rw [hn]
      calc v 8 = v 8 ^ 1 := (pow_one _).symm
        _ ≤ v 8 ^ (n + 1) := Nat.pow_le_pow_right hbase (by omega)
    have bn : ∀ r, vn r ≤ B := register_update_le v 7 B _ hv prod
    have power : vn 7 * vn 8 ^ n = v 7 * v 8 ^ (n + 1) := by
      simp only [vn, Function.update_self, Function.update_of_ne (by decide : (8 : Fin 14) ≠ 7), pow_succ]
      ring
    let kn : Fin (e + 2) := ⟨k.val - 1, by omega⟩
    have knv : kn.val = n := by dsimp [kn]; omega
    have rest := ih kn vn bn (by simp [vn, ht]) (by simp [vn, hi]) (by simp [vn, hs])
      (by simpa [vn] using hbase)
      (by rw [knv, power, ← hn]; exact hp)
      (by rw [knv, power, ← hn]; exact hf) knv
    have endeq : Function.update vn 7 (compFactor C outer * (vn 7 * vn 8 ^ n)) =
        Function.update v 7 (compFactor C outer * (v 7 * v 8 ^ (n + 1))) := by
      rw [power]; simp only [vn, Function.update_idem]
    rw [endeq] at rest
    apply AReach.step ⟨comp_preS C e mode h _, hv⟩
    simp only [astep, compARM, ht, hn, Nat.succ_ne_zero, ↓reduceIte]
    exact (comp_multiply C e mode outer f h k B v hv ht hi hs prod).trans rest


/-- Starting from cleared scratch, the shared polynomial routine computes its exact cap.
The inner coefficient may be zero; the routine still halts and returns zero. -/
private lemma comp_poly_run (C e : ℕ) (mode outer : Bool) (f : List Bool → List Bool)
    (h : List Bool) (B : ℕ) (v : Fin 14 → ℕ) (hv : ∀ r, v r ≤ B)
    (ht : v 6 = 0) (ha : v 7 = 0) (hi : v 10 = 0) (hs : v 11 = 0)
    (hbase : 1 ≤ v 8) (hp : v 8 ^ (if outer then e + 1 else e) ≤ B)
    (hf : compFactor C outer * v 8 ^ (if outer then e + 1 else e) ≤ B) :
    CompReach C e mode f h B (some (.polyStart outer), v, none)
      (some (if outer then .tailTest true else .lengthBound),
        Function.update v 7 (compFactor C outer * v 8 ^ (if outer then e + 1 else e)), none) := by
  let vn := Function.update v 7 1
  have hb : 1 ≤ B := (Nat.one_le_pow _ _ hbase).trans hp
  have bn := register_update_le v 7 B 1 hv hb
  have run := comp_power_run C e mode outer f h
    ⟨if outer then e + 1 else e, by cases outer <;> simp⟩ B vn bn
    (by simp [vn, ht]) (by simp [vn, hi]) (by simp [vn, hs])
    (by simpa [vn] using hbase) (by simpa [vn] using hp) (by simpa [vn] using hf)
  apply AReach.step ⟨comp_preS C e mode h _, hv⟩
  simpa [astep, compARM, ha, vn] using run

/-- Every required power, at either base and coefficient, fits the full output cap. -/
private lemma comp_power_bound (C e n base exponent : ℕ) (outer : Bool)
    (hb : base ≤ n + 1) (he : exponent ≤ e + 1) :
    base ^ exponent ≤ compBound C e n ∧
      compFactor C outer * base ^ exponent ≤ compBound C e n := by
  have pp : base ^ exponent ≤ (n + 1) ^ (e + 1) :=
    (Nat.pow_le_pow_left hb _).trans (Nat.pow_le_pow_right (by omega) he)
  have cf : compFactor C outer ≤ 8 * (2 * C + 3) := by
    cases outer <;> simp only [compFactor, Bool.false_eq_true, ↓reduceIte] <;> omega
  constructor
  · exact pp.trans (Nat.le_mul_of_pos_left _ (by omega))
  · exact Nat.mul_le_mul cf pp

/-- Twice the full cap and all physical addresses fit the common polynomial bound. -/
private lemma comp_bound_room (C e n : ℕ) :
    n + 1 ≤ compBound C e n ∧ 2 * ((2 * C + 3) * (n + 1) ^ (e + 1)) ≤ compBound C e n := by
  constructor
  · have base : n + 1 ≤ (n + 1) ^ (e + 1) := by
      calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
        _ ≤ (n + 1) ^ (e + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    exact base.trans (Nat.le_mul_of_pos_left _ (by omega))
  · unfold compBound
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ (by omega)

/-- A capped length search never queries the cap itself. It stops at the first false
answer, or returns the cap if every smaller answer is true.

**Proof sketch.** The current counter is at most the true length, itself at most the cap.
If the counter equals the cap, it equals the length and exits without a query. Otherwise,
the truthful length query either exits at equality or permits one bounded increment.
Induct on the distance to the true length. This includes cap zero. -/
private lemma comp_length_search (C e : ℕ) (mode : Bool) (f : List Bool → List Bool)
    (h : List Bool) (B F : ℕ) (v : Fin 14 → ℕ) (hv : ∀ r, v r ≤ B)
    (hi : v 12 ≤ F) (hc : F ≤ v 7)
    (ho : ∀ i < v 7, compOracle f 3 (pairEncode h (Nat.bits i)) = decide (i < F)) :
    CompReach C e mode f h B (some .lengthBound, v, none)
      (some .doubleTest, Function.update v 12 F, none) := by
  generalize he : F - v 12 = left
  induction left generalizing v with
  | zero =>
    have eq : v 12 = F := by omega
    have vu : Function.update v 12 F = v := by rw [← eq, Function.update_eq_self]
    rw [vu]
    apply AReach.step ⟨comp_preS C e mode h _, hv⟩
    simp only [astep, compARM]
    by_cases cap : v 12 = v 7
    · simp only [if_pos cap]; exact AReach.refl _
    · simp only [if_neg cap]
      have ans := ho (v 12) (by omega)
      simp only [eq, lt_self_iff_false, decide_false] at ans
      simpa [astep, compARM, eq, ans, vword_whole₁] using
        (AReach.single (A := compARM C e mode) (oracle := compOracle f) (x := h)
          (a := (some .lengthQuery, v, none)) ⟨comp_preS C e mode h _, hv⟩)
  | succ left ih =>
    have lt : v 12 < F := by omega
    have cap : v 12 ≠ v 7 := by omega
    let vn := Function.update v 12 (v 12 + 1)
    have bn : ∀ r, vn r ≤ B := register_update_le v 12 B _ hv (by have := hv 7; omega)
    have rest := ih vn bn (by simp [vn]; omega) (by simpa [vn] using hc)
      (by simpa [vn] using ho) (by simp [vn]; omega)
    have ans := ho (v 12) (by omega)
    simp only [lt, decide_true] at ans
    apply AReach.step ⟨comp_preS C e mode h _, hv⟩
    simp only [astep, compARM, if_neg cap]
    apply AReach.step ⟨comp_preS C e mode h _, hv⟩
    simp only [astep, compARM, vword_whole₁, ans, ↓reduceIte]
    apply AReach.step ⟨comp_preS C e mode h _, hv⟩
    simpa only [astep, compARM, vn, Function.update_idem] using rest


/-- Boundary vectors keep the physical positions separate from the bounded query and
arithmetic scratch. -/
private def compValues (n : ℕ) (ptr tail stop inner query temp cap base spare iter old len idx : ℕ := 0) :
    Fin 14 → ℕ := ![ptr, n, tail, stop, inner, query, temp, cap, base, spare, iter, old, len, idx]

/-- Coordinate lookup exposes the vector without unfolding it under an update. -/
@[simp] private lemma compValues_apply (n p a w b q t c x s i y l j : ℕ) (r : Fin 14) :
    compValues n p a w b q t c x s i y l j r = ![p, n, a, w, b, q, t, c, x, s, i, y, l, j] r := rfl

/-- A single update changes just the named coordinate of a boundary vector. -/
@[simp] private lemma compValues_update (n p a w b q t c x s i y l j : ℕ) (r : Fin 14) (v : ℕ) :
    Function.update (compValues n p a w b q t c x s i y l j) r v =
      compValues (if 1 = r then v else n) (if 0 = r then v else p)
        (if 2 = r then v else a) (if 3 = r then v else w) (if 4 = r then v else b)
        (if 5 = r then v else q) (if 6 = r then v else t) (if 7 = r then v else c)
        (if 8 = r then v else x) (if 9 = r then v else s) (if 10 = r then v else i)
        (if 11 = r then v else y) (if 12 = r then v else l) (if 13 = r then v else j) := by
  revert r
  simp [Fin.forall_fin_succ, compValues, Matrix.vecCons, Fin.update_cons_zero, ← Fin.cons_update]

/-- The copy stages are all instances of the proved counting copy. -/
private lemma comp_copy_run (C e : ℕ) (mode : Bool) (f : List Bool → List Bool)
    (h : List Bool) (B : ℕ) (stage : Fin 8) (v : Fin 14 → ℕ)
    (hv : ∀ r, v r ≤ B) (hle : v (compCopy C e stage).1 ≤ v (compCopy C e stage).2.1) :
    CompReach C e mode f h B (some (.copy stage false), v, none)
      (some (compCopy C e stage).2.2,
        Function.update v (compCopy C e stage).1 (v (compCopy C e stage).2.1), none) := by
  have ne : ∀ s, (compCopy C e s).1 ≠ (compCopy C e s).2.1 := by
    simp [Fin.forall_fin_succ, compCopy]
  apply registerCopy_loop (compARM C e mode) (compOracle f) h _ _ (ne stage)
    _ _ _ rfl rfl B v hv hle

/-- Both shape scans cite the same public strided validator; no field canonicality is
imposed by this fragment.

**Proof sketch.** Instantiate `alignedPair_loop` at the selected stride and saved end
register. The finite increment chains discharge its transition equations. -/
private lemma comp_pair_run (C e : ℕ) (mode inner : Bool) (f : List Bool → List Bool)
    (h w : List Bool) (B : ℕ) (v : Fin 14 → ℕ) (hv : ∀ r, v r ≤ B)
    (hl : v (compLimit inner) = v 0 + compStride inner * w.length)
    (ho : ∀ i < w.length, h.getD (v 0 + compStride inner * i) false = w.getD i false) :
    match pairDecode w with
    | none => ∃ t ≤ w.length, CompReach C e mode f h B (some (.scan inner), v, none)
        (some (.answer false), Function.update v 0 (v 0 + compStride inner * t), none)
    | some (a, _) => CompReach C e mode f h B (some (.scan inner), v, none)
        (some (.copy (if inner then 4 else 0) false),
          Function.update v 0 (v 0 + compStride inner * (2 * a.length + 2)), none) := by
  apply alignedPair_loop (compARM C e mode) (compOracle f) h 0 (compLimit inner) 0
    (.scan inner) (.first inner) (.second inner) (.readSecond inner)
    (.answer false) (.copy (if inner then 4 else 0) false) (compAdvance C e inner)
    (compStride inner) B (by cases inner <;> decide) (by cases inner <;> decide)
    rfl rfl (fun _ => rfl) (fun _ => rfl)
  · intro choice i hi
    simp only [compAdvance, dif_pos hi, compARM]
  · simp [compAdvance]
  · exact hv
  · exact hl
  · intro i hi
    rw [comp_bit]
    exact ho i hi

/-- Returning at an answer node takes one bounded step. -/
private lemma comp_ret (C e : ℕ) (mode b : Bool) (f : List Bool → List Bool)
    (h : List Bool) (B : ℕ) (v : Fin 14 → ℕ) (hv : ∀ r, v r ≤ B) :
    CompHalt C e mode f h B (some (.answer b), v, none) b :=
  AHalt.ret rfl ⟨comp_preS C e mode h _, hv⟩

/-- The suffix of the inner pair is read at doubled physical addresses. -/
private lemma comp_suffix_address (x b tail : List Bool) (j : ℕ) (hj : j < b.length) :
    (pairEncode (pairEncode x b) tail).getD (4 * x.length + 4 + 2 * j) false = b.getD j false := by
  have len := length_pairEncode x b
  rw [pairEncode_getD, if_pos (by omega)]
  have div : (4 * x.length + 4 + 2 * j) / 2 = 2 * x.length + 2 + j := by omega
  rw [div, pairEncode_getD_snd]

/-- For a nonempty inner field, its final physical bit is exactly its canonicality flag.
The field's represented number is never computed. -/
private lemma comp_last_address (x b tail : List Bool) (hb : b ≠ []) :
    (pairEncode (pairEncode x b) tail).getD (2 * (pairEncode x b).length - 2) false =
      b.getLastD true := by
  have pos : 0 < b.length := List.length_pos_iff.mpr hb
  have addr : 2 * (pairEncode x b).length - 2 = 4 * x.length + 4 + 2 * (b.length - 1) := by
    rw [length_pairEncode]; omega
  rw [addr, comp_suffix_address x b tail _ (by omega)]
  simp [List.getD_eq_getElem?_getD, List.getLastD_eq_getLast?, List.getLast?_eq_getElem?,
    List.getElem?_eq_getElem (by omega : b.length - 1 < b.length)]

/-- The inner canonicality check inspects the empty-field boundary or its last bit.
Only the physical pointer changes; no numerical bound is imposed on the inner payload.

**Proof sketch.** Equality of the saved boundaries accepts the empty field. Otherwise,
copy the inner end, move back two physical cells, and read the last suffix bit. Its value
is exactly the empty-or-final-true canonicality predicate. -/
private lemma comp_canonical_run (C e : ℕ) (mode : Bool) (f : List Bool → List Bool)
    (x b tail : List Bool) (B : ℕ) (v : Fin 14 → ℕ) (hv : ∀ r, v r ≤ B)
    (he : v 3 = 2 * (pairEncode x b).length) (hb : v 4 = 4 * x.length + 4) :
    ∃ v', (∀ r, v' r ≤ B) ∧ (∀ r, r ≠ 0 → v' r = v r) ∧
      CompReach C e mode f (pairEncode (pairEncode x b) tail) B
        (some .canonical, v, none)
        (some (if Canon b then .innerPrepare else .answer false), v', none) := by
  let h := pairEncode (pairEncode x b) tail
  by_cases empty : b = []
  · subst b
    have eq : v 4 = v 3 := by rw [hb, he, length_pairEncode]; simp only [List.length_nil]; omega
    refine ⟨v, hv, fun _ _ => rfl, ?_⟩
    simpa [astep, compARM, eq, Canon] using
      (AReach.single (A := compARM C e mode) (oracle := compOracle f) (x := h)
        (a := (some .canonical, v, none)) ⟨comp_preS C e mode h _, hv⟩)
  · have pos : 0 < b.length := List.length_pos_iff.mpr empty
    have ne : v 4 ≠ v 3 := by rw [hb, he, length_pairEncode]; omega
    let vz := Function.update v 0 0
    let vc := Function.update v 0 (v 3)
    let vd := Function.update v 0 (v 3 - 1)
    let vf := Function.update v 0 (v 3 - 2)
    have bz := register_update_le v 0 B 0 hv (Nat.zero_le _)
    have bc := register_update_le v 0 B (v 3) hv (hv 3)
    have bd := register_update_le v 0 B (v 3 - 1) hv (by have := hv 3; omega)
    have bf := register_update_le v 0 B (v 3 - 2) hv (by have := hv 3; omega)
    refine ⟨vf, bf, fun r hr => Function.update_of_ne hr _ _, ?_⟩
    have cp : CompReach C e mode f h B (some (.copy 5 false), vz, none)
        (some (.canonicalDec false), vc, none) := by
      simpa [vz, vc, compCopy] using comp_copy_run C e mode f h B 5 vz bz (by simp [vz, compCopy])
    have read : compOracle f 0 (pairEncode h (Nat.bits (vf 0))) = b.getLastD true := by
      rw [comp_bit]
      simpa [vf, h, he] using comp_last_address x b tail empty
    have last : CompReach C e mode f h B (some .canonicalRead, vf, none)
        (some (if Canon b then .innerPrepare else .answer false), vf, none) := by
      have step := AReach.single (A := compARM C e mode) (oracle := compOracle f) (x := h)
        (G := fun a => PreS (compARM C e mode) h a ∧ ∀ r, a.2.1 r ≤ B)
        (a := (some .canonicalRead, vf, none)) ⟨comp_preS C e mode h _, bf⟩
      simpa only [astep, compARM, vword_whole₁, read, drop_canon] using step
    apply AReach.step ⟨comp_preS C e mode h _, hv⟩
    simp only [astep, compARM, if_neg ne]
    apply AReach.step ⟨comp_preS C e mode h _, hv⟩
    simp only [astep, compARM]
    apply cp.trans
    apply AReach.step ⟨comp_preS C e mode h _, bc⟩
    simp only [astep, compARM, vc, Function.update_self, Function.update_idem]
    apply AReach.step ⟨comp_preS C e mode h _, bd⟩
    simpa only [astep, compARM, vd, vf, Function.update_self, Function.update_idem,
      Nat.sub_sub, Nat.reduceAdd] using last


/-- After the outer shape scan, save its boundaries and construct the full output cap.

**Proof sketch.** The separator end gives the outer tail and, after two decrements, the
inner end. Copy the physical host length and increment to obtain the power base. The
shared polynomial routine supplies the full composition cap before any index decoding. -/
private lemma comp_outer_prepare (C e : ℕ) (mode : Bool) (f : List Bool → List Bool)
    (z tail : List Bool) :
    let h := pairEncode z tail
    let a := 2 * z.length + 2
    CompReach C e mode f h (compBound C e h.length)
      (some (.copy 0 false), compValues h.length (ptr := a), none)
      (some (.tailTest true), compValues h.length (ptr := a) (tail := a)
        (stop := 2 * z.length) (cap := (2 * C + 3) * (h.length + 1) ^ (e + 1))
        (base := h.length + 1), none) := by
  dsimp only
  let h := pairEncode z tail
  let a := 2 * z.length + 2
  let B := compBound C e h.length
  have room := (comp_bound_room C e h.length).1
  have ab : a ≤ h.length := by dsimp [a, h]; rw [length_pairEncode]; omega
  have bounds : ∀ p t w b, p ≤ h.length + 1 → t ≤ h.length + 1 → w ≤ h.length + 1 →
      b ≤ h.length + 1 → ∀ r, (compValues h.length (ptr := p) (tail := t) (stop := w) (base := b)) r ≤ B := by
    intro p t w b hp ht hw hb
    simp [Fin.forall_fin_succ, compValues]
    dsimp [B] at *
    omega
  let v₀ := compValues h.length (ptr := a)
  let v₁ := compValues h.length (ptr := a) (tail := a)
  let v₂ := compValues h.length (ptr := a) (tail := a) (stop := a)
  let v₃ := compValues h.length (ptr := a) (tail := a) (stop := a - 1)
  let v₄ := compValues h.length (ptr := a) (tail := a) (stop := 2 * z.length)
  let v₅ := compValues h.length (ptr := a) (tail := a) (stop := 2 * z.length) (base := h.length)
  let v₆ := compValues h.length (ptr := a) (tail := a) (stop := 2 * z.length) (base := h.length + 1)
  have b₀ : ∀ r, v₀ r ≤ B := bounds a 0 0 0 (by omega) (by omega) (by omega) (by omega)
  have b₁ : ∀ r, v₁ r ≤ B := bounds a a 0 0 (by omega) (by omega) (by omega) (by omega)
  have b₂ : ∀ r, v₂ r ≤ B := bounds a a a 0 (by omega) (by omega) (by omega) (by omega)
  have b₃ : ∀ r, v₃ r ≤ B := bounds a a (a-1) 0 (by omega) (by omega) (by omega) (by omega)
  have b₄ : ∀ r, v₄ r ≤ B := bounds a a (2*z.length) 0 (by omega) (by omega) (by dsimp [a] at ab; omega) (by omega)
  have b₅ : ∀ r, v₅ r ≤ B := bounds a a (2*z.length) h.length (by omega) (by omega) (by dsimp [a] at ab; omega) (by omega)
  have b₆ : ∀ r, v₆ r ≤ B := bounds a a (2*z.length) (h.length+1) (by omega) (by omega) (by dsimp [a] at ab; omega) le_rfl
  have c₀ : CompReach C e mode f h B (some (.copy 0 false), v₀, none)
      (some (.copy 1 false), v₁, none) := by
    simpa [v₀, v₁, compCopy] using comp_copy_run C e mode f h B 0 v₀ b₀ (by simp [v₀, compCopy])
  have c₁ : CompReach C e mode f h B (some (.copy 1 false), v₁, none)
      (some (.outerDec false), v₂, none) := by
    simpa [v₁, v₂, compCopy] using comp_copy_run C e mode f h B 1 v₁ b₁ (by simp [v₁, compCopy])
  have c₂ : CompReach C e mode f h B (some (.outerDec false), v₂, none)
      (some (.copy 2 false), v₄, none) := by
    apply AReach.step ⟨comp_preS C e mode h _, b₂⟩
    simp only [astep, compARM]
    rw [show Function.update v₂ 3 (v₂ 3 - 1) = v₃ by simp [v₂, v₃]]
    apply AReach.step ⟨comp_preS C e mode h _, b₃⟩
    simpa [astep, compARM, v₃, v₄, a] using
      (AReach.refl (A := compARM C e mode) (oracle := compOracle f) (x := h)
        (G := fun a => PreS (compARM C e mode) h a ∧ ∀ r, a.2.1 r ≤ B)
        (some (.copy 2 false), v₄, none))
  have c₃ : CompReach C e mode f h B (some (.copy 2 false), v₄, none)
      (some .baseInc, v₅, none) := by
    simpa [v₄, v₅, compCopy] using comp_copy_run C e mode f h B 2 v₄ b₄ (by simp [v₄, compCopy])
  have pp := comp_power_bound C e h.length (h.length + 1) (e + 1) true le_rfl le_rfl
  have pol := comp_poly_run C e mode true f h B v₆ b₆
    (by simp [v₆, compValues]) (by simp [v₆, compValues]) (by simp [v₆, compValues])
    (by simp [v₆, compValues]) (by simp [v₆, compValues])
    (by simpa [v₆, compValues] using pp.1) (by simpa [v₆, compValues] using pp.2)
  apply (c₀.trans (c₁.trans (c₂.trans c₃))).trans
  apply AReach.step ⟨comp_preS C e mode h _, b₅⟩
  simpa [astep, compARM, v₅, v₆, compFactor] using pol

/-- The bounded outer tail is validated before its numeric value is accumulated.

**Proof sketch.** Apply the shared canonical tail scan against the full composition cap.
Failure returns false. On success, clear the consumed cap, restore the pointer to the
host end, and invoke the shared reverse decoder. The frozen suffix-value bound applies
at every decode step. Finally clear the pointer for the inner shape scan. -/
private lemma comp_outer_decode (C e : ℕ) (mode : Bool) (f : List Bool → List Bool)
    (z tail : List Bool) :
    let h := pairEncode z tail
    let a := 2 * z.length + 2
    let cap := (2 * C + 3) * (h.length + 1) ^ (e + 1)
    let v := compValues h.length (ptr := a) (tail := a) (stop := 2 * z.length)
      (cap := cap) (base := h.length + 1)
    if Canon tail ∧ tail.length ≤ (Nat.bits cap).length then
      CompReach C e mode f h (compBound C e h.length) (some (.tailTest true), v, none)
        (some (.scan true), compValues h.length (tail := a) (stop := 2 * z.length)
          (query := bitsVal tail) (base := h.length + 1), none)
    else CompHalt C e mode f h (compBound C e h.length) (some (.tailTest true), v, none) false := by
  dsimp only
  let h := pairEncode z tail
  let a := 2 * z.length + 2
  let cap := (2 * C + 3) * (h.length + 1) ^ (e + 1)
  let B := compBound C e h.length
  let v₀ := compValues h.length (ptr := a) (tail := a) (stop := 2 * z.length)
    (cap := cap) (base := h.length + 1)
  have len : h.length = a + tail.length := length_pairEncode z tail
  have room := comp_bound_room C e h.length
  have b₀ : ∀ r, v₀ r ≤ B := by
    simp [v₀, compValues, Fin.forall_fin_succ]
    dsimp [a, B, cap] at *
    omega
  have reads : ∀ i < tail.length, compOracle f 0 (pairEncode h (Nat.bits (v₀ 0 + 1 * i))) = tail.getD i false := by
    intro i hi
    rw [comp_bit]
    simp only [v₀, compValues, Matrix.cons_val_zero, Nat.one_mul]
    rw [show h = pairEncode z tail by rfl, pairEncode_getD]
    rw [if_neg (by dsimp [a]; omega), if_neg (by dsimp [a]; omega), if_neg (by dsimp [a]; omega)]
    congr 1
    dsimp [a]; omega
  obtain ⟨vs, bs, ps, frame, scan⟩ := canonicalTail_loop (compARM C e mode) (compOracle f) h
    0 1 7 (by decide) (by decide) (by decide) 0 CompState.tailTest
    .tailCheck .tailRead (.answer false) .tailDone CompState.tailHalf
    (fun b i => if i = 0 then .tailInc b else .tailTest b) 1 B (by omega)
    (fun _ => rfl) rfl rfl (fun _ => rfl)
    (by
      intro b i hi
      have hz : i = 0 := by omega
      subst i
      rfl)
    (fun _ => rfl) tail true v₀ b₀ (by simpa [v₀, compValues] using len) reads
  by_cases good : Canon tail ∧ tail.length ≤ (Nat.bits cap).length
  · rw [if_pos good]
    have scan' : CompReach C e mode f h B (some (.tailTest true), v₀, none) (some .tailDone, vs, none) := by
      have flag := (drop_canon tail).mpr good.1
      simp only [flag, ↓reduceIte] at scan
      simpa [v₀, good.2] using scan
    let vz := compValues h.length (tail := a) (stop := 2*z.length) (base := h.length+1)
    let vd := compValues h.length (ptr := h.length) (tail := a) (stop := 2*z.length) (base := h.length+1)
    have bz : ∀ r, vz r ≤ B := by
      simp [vz, compValues, Fin.forall_fin_succ]; dsimp [a, B] at *; omega
    have bd : ∀ r, vd r ≤ B := by
      simp [vd, compValues, Fin.forall_fin_succ]; dsimp [a, B] at *; omega
    have reset : CompReach C e mode f h B (some .tailDone, vs, none) (some (.copy 3 false), vz, none) := by
      apply AReach.step ⟨comp_preS C e mode h _, bs⟩
      simp only [astep, compARM]
      apply AReach.step ⟨comp_preS C e mode h _, register_update_le vs 7 B 0 bs (Nat.zero_le _)⟩
      simp only [astep, compARM]
      have ve : Function.update (Function.update vs 7 0) 0 0 = vz := by
        apply funext
        simp only [Fin.forall_fin_succ] at frame ⊢
        simp_all [vz, v₀, compValues, Function.update_apply]
      rw [ve]
      exact AReach.refl _
    have copy : CompReach C e mode f h B (some (.copy 3 false), vz, none) (some .decode, vd, none) := by
      simpa [vz, vd, compCopy] using comp_copy_run C e mode f h B 3 vz bz (by simp [vz, compCopy])
    have values : ∀ i ≤ tail.length, bitsVal (tail.drop i) ≤ B := by
      intro i _
      exact (query_accumulator_bound tail cap i good.1 good.2).trans room.2
    have dread : ∀ i < tail.length, compOracle f 0 (pairEncode h (Nat.bits (vd 2 + i))) = tail.getD i false := by
      simpa [vd, v₀, compValues] using reads
    obtain ⟨vf, bf, fp, fq, ft, ff, dec⟩ := boundedDecode_loop (compARM C e mode) (compOracle f) h
      0 2 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      0 .decode .decodeDown .decodeRead .decodeDone
      (fun b => .decodeCopy b false) (fun b => .decodeCopy b true) CompState.decodeClear
      CompState.decodeScale CompState.decodeTake CompState.decodeAdd (compDecodeAdvance C e)
      rfl rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (by
        intro b i hi
        have cases : i = 0 ∨ i = 1 := by omega
        rcases cases with rfl | rfl <;> rfl)
      (fun _ => rfl) (fun _ => rfl) tail B values tail.length le_rfl vd bd
      (by simpa [vd, compValues] using len) (by simp [vd, compValues, bitsVal])
      (by simp [vd, compValues]) dread
    have endv : Function.update vf 0 0 = compValues h.length (tail := a) (stop := 2*z.length)
        (query := bitsVal tail) (base := h.length+1) := by
      apply funext
      simp only [Fin.forall_fin_succ] at ff ⊢
      simp_all [vd, compValues]
    apply (scan'.trans (reset.trans (copy.trans dec))).trans
    simpa only [astep, compARM, endv] using
      (AReach.single (A := compARM C e mode) (oracle := compOracle f) (x := h)
        (a := (some .decodeDone, vf, none)) ⟨comp_preS C e mode h _, bf⟩)
  · rw [if_neg good]
    have scan' : CompReach C e mode f h B (some (.tailTest true), v₀, none) (some (.answer false), vs, none) := by
      by_cases width : tail.length ≤ (Nat.bits cap).length
      · have canon : ¬ Canon tail := fun hc => good ⟨hc, width⟩
        have last : tail.getLastD true = false := Bool.eq_false_iff.mpr (fun hc => canon ((drop_canon tail).mp hc))
        simp only [last, Bool.false_eq_true, ↓reduceIte, ite_self] at scan
        simpa [v₀] using scan
      · simpa [v₀, compValues, width] using scan
    exact scan'.halt (comp_ret C e mode false f h B vs bs)


/-- The inner cap is computed from the saved first-field separator: dividing its physical
position by four gives exactly `|x| + 1`. No bit of the inner payload is decoded.

**Proof sketch.** Copy the saved boundary and halve it twice. Instantiate the shared
polynomial routine with the inner coefficient and exponent at this exact base. -/
private lemma comp_inner_prepare (C e : ℕ) (mode : Bool) (f : List Bool → List Bool)
    (h : List Bool) (n : ℕ) (v : Fin 14 → ℕ) (hv : ∀ r, v r ≤ compBound C e h.length)
    (hb : v 4 = 4 * n + 4) (ht : v 6 = 0) (ha : v 7 = 0) (hi : v 10 = 0) (hs : v 11 = 0)
    (hn : n ≤ h.length) :
    CompReach C e mode f h (compBound C e h.length) (some .innerPrepare, v, none)
      (some .lengthBound, Function.update (Function.update v 8 (n + 1)) 7 (C * (n + 1) ^ e), none) := by
  let B := compBound C e h.length
  let vz := Function.update v 8 0
  let vc := Function.update v 8 (4*n+4)
  let vd := Function.update v 8 (2*n+2)
  let vp := Function.update v 8 (n+1)
  have bz : ∀ r, vz r ≤ B := register_update_le v 8 B 0 hv (Nat.zero_le _)
  have bound : 4*n+4 ≤ B := by simpa [hb] using hv 4
  have bc : ∀ r, vc r ≤ B := register_update_le v 8 B _ hv bound
  have bd : ∀ r, vd r ≤ B := register_update_le v 8 B _ hv (by omega)
  have bp : ∀ r, vp r ≤ B := register_update_le v 8 B _ hv (by omega)
  have cp : CompReach C e mode f h B (some (.copy 6 false), vz, none) (some (.innerHalf false), vc, none) := by
    simpa [vz, vc, compCopy, hb] using comp_copy_run C e mode f h B 6 vz bz (by simp [vz, compCopy])
  have power := comp_power_bound C e h.length (n+1) e false (by omega) (by omega)
  have pol := comp_poly_run C e mode false f h B vp bp
    (by simp [vp, ht]) (by simp [vp, ha]) (by simp [vp, hi]) (by simp [vp, hs])
    (by simp [vp]) (by simpa [vp] using power.1) (by simpa [vp] using power.2)
  apply AReach.step ⟨comp_preS C e mode h _, hv⟩
  simp only [astep, compARM]
  apply cp.trans
  apply AReach.step ⟨comp_preS C e mode h _, bc⟩
  simp only [astep, compARM, vc, Function.update_self, Function.update_idem]
  rw [show (4*n+4)/2 = 2*n+2 by omega]
  apply AReach.step ⟨comp_preS C e mode h _, bd⟩
  simpa [astep, compARM, vd, vp, compFactor, show (2*n+2)/2 = n+1 by omega] using pol

/-- The two lookup segments use the received indexing loop at strides one and two. -/
private def compWalk (C e : ℕ) (suffix : Bool) (i : ℕ) : CompState C e :=
  if i = 0 then .walk suffix false else if suffix && (i == 1) then .walk suffix true else .seek suffix

/-- A virtual-prefix or physical-suffix seek is a direct shared-fragment instantiation.

**Proof sketch.** Invoke `indexedSeek_loop` with stride one or two and the selected segment
boundary. Its hit and miss endpoints are precisely the corresponding ARM states. -/
private lemma comp_seek_run (C e : ℕ) (mode suffix : Bool) (f : List Bool → List Bool)
    (h : List Bool) (B count : ℕ) (v : Fin 14 → ℕ) (hv : ∀ r, v r ≤ B)
    (hl : v (if suffix then 3 else 11) = v 0 + compStride suffix * count)
    (hb : v 13 + count ≤ B) (hq : v 13 ≤ v 5) :
    if v 5 < v 13 + count then
      CompReach C e mode f h B (some (.seek suffix), v, none)
        (some (if suffix then .suffixHit else .prefixHit),
          Function.update (Function.update v 0 (v 0 + compStride suffix * (v 5 - v 13))) 13 (v 5), none)
    else
      CompReach C e mode f h B (some (.seek suffix), v, none)
        (some (if suffix then .answer false else .separator false),
          Function.update (Function.update v 0 (v (if suffix then 3 else 11))) 13 (v 13 + count), none) := by
  apply indexedSeek_loop (compARM C e mode) (compOracle f) h 0 (if suffix then 3 else 11) 13 5
    (by cases suffix <;> decide) (by decide) (by decide) (by cases suffix <;> decide)
    (by cases suffix <;> decide) (by decide)
    (.seek suffix) (.probe suffix) (.next suffix) (if suffix then .suffixHit else .prefixHit)
    (if suffix then .answer false else .separator false) (compWalk C e suffix) (compStride suffix) B
    (by cases suffix <;> decide) rfl rfl rfl
  · intro i hi
    cases suffix with
    | false =>
      have iz : i = 0 := by simp [compStride] at hi; omega
      subst i; rfl
    | true =>
      have iz : i = 0 ∨ i = 1 := by simp [compStride] at hi; omega
      rcases iz with rfl | rfl <;> rfl
  · cases suffix <;> rfl
  · exact hv
  · exact hl
  · exact hb
  · exact hq

/-- An oracle-return node returns exactly its answer, preserving every register. -/
private lemma comp_call_return (C e : ℕ) (mode : Bool) (f : List Bool → List Bool)
    (h : List Bool) (B : ℕ) (v : Fin 14 → ℕ) (hv : ∀ r, v r ≤ B)
    (l : CompState C e) (j : Fin 4) (r : Fin 14)
    (hc : compARM C e mode l = .call j .whole [r] (.answer true) (.answer false)) :
    CompHalt C e mode f h B (some l, v, none) (compOracle f j (pairEncode h (Nat.bits (v r)))) := by
  apply AHalt.step ⟨comp_preS C e mode h _, hv⟩
  simp only [astep, hc, vword_whole₁]
  cases ans : compOracle f j (pairEncode h (Nat.bits (v r))) <;>
    simpa [ans] using comp_ret C e mode _ f h B v hv

/-- A matching suffix position accepts in length mode and reads the physical bit in bit mode. -/
private lemma comp_suffix_hit (C e : ℕ) (mode : Bool) (f : List Bool → List Bool)
    (h : List Bool) (B : ℕ) (v : Fin 14 → ℕ) (hv : ∀ r, v r ≤ B) :
    CompHalt C e mode f h B (some .suffixHit, v, none) (if mode then true else h.getD (v 0) false) := by
  cases mode with
  | false => simpa only [comp_bit] using comp_call_return C e false f h B v hv .suffixHit 0 0 rfl
  | true => exact AHalt.ret rfl ⟨comp_preS C e true h _, hv⟩

/-- A matching prefix position reads the lifted `f` bit after halving the virtual address. -/
private lemma comp_prefix_hit (C e : ℕ) (mode : Bool) (f : List Bool → List Bool)
    (x b : List Bool) (p B : ℕ) (v : Fin 14 → ℕ) (hv : ∀ r, v r ≤ B) :
    CompHalt C e mode f (pairEncode (pairEncode x b) (Nat.bits p)) B (some .prefixHit, v, none)
      (if mode then true else (f x).getD (v 0 / 2) false) := by
  cases mode with
  | true => exact AHalt.ret rfl ⟨comp_preS C e true _ _, hv⟩
  | false =>
    let vn := Function.update v 0 (v 0 / 2)
    have bn : ∀ r, vn r ≤ B := register_update_le v 0 B _ hv ((Nat.div_le_self _ _).trans (hv 0))
    have next := comp_call_return C e false f (pairEncode (pairEncode x b) (Nat.bits p)) B vn bn .prefixBit 2 0 rfl
    have answer := comp_lifted f false x b p (vn 0)
    simp only [Bool.false_eq_true, ↓reduceIte] at answer
    rw [answer] at next
    apply AHalt.step ⟨comp_preS C e false _ _, hv⟩
    simpa [astep, compARM, vn] using next


/-- A suffix lookup reads exactly the retained payload bit or rejects past its end.

**Proof sketch.** Invoke the shared indexed seek at physical stride two. Its hit address
is the proved nested-pair suffix address. A miss means the default bit and length answer
are both false. -/
private lemma comp_suffix_run (C e : ℕ) (mode : Bool) (f : List Bool → List Bool)
    (x b : List Bool) (p B : ℕ) (v : Fin 14 → ℕ) (hv : ∀ r, v r ≤ B)
    (hp : v 0 = 4*x.length+4) (he : v 3 = 2*(pairEncode x b).length)
    (hi : v 13 = 2*(f x).length+2) (hq : v 5 = p)
    (le : 2*(f x).length+2 ≤ p) (total : 2*(f x).length+2+b.length ≤ B) :
    CompHalt C e mode f (pairEncode (pairEncode x b) (Nat.bits p)) B (some (.seek true), v, none)
      (if mode then decide (p < 2*(f x).length+2+b.length)
        else b.getD (p-(2*(f x).length+2)) false) := by
  let h := pairEncode (pairEncode x b) (Nat.bits p)
  let n := 2*(f x).length+2
  have endpos : v 3 = v 0 + 2*b.length := by rw [he, hp, length_pairEncode]; omega
  have seek := comp_seek_run C e mode true f h B b.length v hv
    (by simpa [compStride] using endpos) (by simpa [hi] using total) (by omega)
  by_cases inside : p < n + b.length
  · have cond : v 5 < v 13 + b.length := by simpa [hq, hi, n] using inside
    simp only [if_pos cond, ↓reduceIte] at seek
    let addr := 4*x.length+4+2*(p-n)
    let vh := Function.update (Function.update v 0 addr) 13 p
    have path : CompReach C e mode f h B (some (.seek true), v, none) (some .suffixHit, vh, none) := by
      simpa [vh, addr, hp, hi, hq, n, compStride] using seek
    have ab : addr ≤ B := by have := hv 3; dsimp [addr, n] at *; omega
    have bh : ∀ r, vh r ≤ B := register_update_le _ 13 B p (register_update_le v 0 B addr hv ab)
      (by simpa [hq] using hv 5)
    have bit : h.getD (vh 0) false = b.getD (p-n) false := by
      simpa [vh, addr, h] using comp_suffix_address x b (Nat.bits p) (p-n) (by omega)
    have hit := comp_suffix_hit C e mode f h B vh bh
    rw [bit] at hit
    have truth : decide (p < n+b.length) = true := decide_eq_true inside
    change CompHalt C e mode f h B (some (.seek true), v, none)
      (if mode then decide (p < n+b.length) else b.getD (p-n) false)
    rw [truth]
    exact path.halt hit
  · have cond : ¬ v 5 < v 13 + b.length := by simpa [hq, hi, n] using inside
    simp only [if_neg cond, ↓reduceIte] at seek
    let vf := Function.update (Function.update v 0 (v 3)) 13 (v 13+b.length)
    have bf : ∀ r, vf r ≤ B := register_update_le _ 13 B _
      (register_update_le v 0 B _ hv (hv 3)) (by simpa [hi] using total)
    have bit : b.getD (p-n) false = false := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : b.length ≤ p-n)]
    have ans : (if mode then decide (p < n+b.length) else b.getD (p-n) false) = false := by
      simp only [inside, decide_false, bit, ite_self]
    rw [ans]
    exact seek.halt (comp_ret C e mode false f h B vf bf)

/-- Both separator cells and the following suffix have the exact paired-output semantics.

**Proof sketch.** Test the current output position, then the following position, returning
`false,true` for bit queries and accepting both for length queries. If neither matches,
advance past the separator and seek the retained suffix at its saved physical start. -/
private lemma comp_separator_run (C e : ℕ) (mode : Bool) (f : List Bool → List Bool)
    (x b : List Bool) (p B : ℕ) (v : Fin 14 → ℕ) (hv : ∀ r, v r ≤ B)
    (he : v 3 = 2*(pairEncode x b).length) (hb : v 4 = 4*x.length+4)
    (hi : v 13 = 2*(f x).length) (hq : v 5 = p) (le : 2*(f x).length ≤ p)
    (total : (pairEncode (f x) b).length ≤ B) :
    CompHalt C e mode f (pairEncode (pairEncode x b) (Nat.bits p)) B (some (.separator false), v, none)
      (if mode then decide (p < (pairEncode (f x) b).length) else (pairEncode (f x) b).getD p false) := by
  let h := pairEncode (pairEncode x b) (Nat.bits p)
  let n := 2*(f x).length
  have outlen : (pairEncode (f x) b).length = n+2+b.length := length_pairEncode _ _
  have firsteq : (if mode then decide (n < (pairEncode (f x) b).length)
      else (pairEncode (f x) b).getD n false) = mode := by
    have lt : n < (pairEncode (f x) b).length := by omega
    cases mode with
    | false =>
      change (pairEncode (f x) b).getD n false = false
      rw [pairEncode_getD, if_neg (by dsimp [n]; omega), if_pos rfl]
    | true => simp [lt]
  by_cases first : p = n
  · have eq : v 13 = v 5 := by omega
    have ans : (if mode then decide (p < (pairEncode (f x) b).length)
        else (pairEncode (f x) b).getD p false) = mode := by simpa only [first] using firsteq
    rw [ans]
    apply AHalt.step ⟨comp_preS C e mode h _, hv⟩
    simpa only [astep, compARM, if_pos eq] using comp_ret C e mode mode f h B v hv
  · have ne : v 13 ≠ v 5 := by omega
    let v₁ := Function.update v 13 (n+1)
    have b₁ : ∀ r, v₁ r ≤ B := register_update_le v 13 B _ hv (by omega)
    have headRun : CompReach C e mode f h B (some (.separator false), v, none)
        (some (.separator true), v₁, none) := by
      apply AReach.step ⟨comp_preS C e mode h _, hv⟩
      simp only [astep, compARM, if_neg ne]
      simpa only [astep, compARM, hi] using
        (AReach.single (A := compARM C e mode) (oracle := compOracle f) (x := h)
          (a := (some (.separatorInc false), v, none)) ⟨comp_preS C e mode h _, hv⟩)
    by_cases second : p = n+1
    · have eq : v₁ 13 = v₁ 5 := by simp [v₁, hq, second]
      have ans : (if mode then decide (p < (pairEncode (f x) b).length)
          else (pairEncode (f x) b).getD p false) = true := by
        have lt : p < (pairEncode (f x) b).length := by omega
        cases mode with
        | false =>
          change (pairEncode (f x) b).getD p false = true
          rw [pairEncode_getD, if_neg (by dsimp [n] at second; omega),
            if_neg (by dsimp [n] at second; omega), if_pos (by dsimp [n] at second; omega)]
        | true => simp [lt]
      rw [ans]
      apply headRun.halt
      apply AHalt.step ⟨comp_preS C e mode h _, b₁⟩
      simpa only [astep, compARM, if_pos eq] using comp_ret C e mode true f h B v₁ b₁
    · have beyond : n+2 ≤ p := by omega
      have ne₁ : v₁ 13 ≠ v₁ 5 := by simp [v₁, hq]; omega
      let v₂ := Function.update v 13 (n+2)
      let vz := Function.update v₂ 0 0
      let vs := Function.update v₂ 0 (v 4)
      have b₂ : ∀ r, v₂ r ≤ B := register_update_le v 13 B _ hv (by omega)
      have bz : ∀ r, vz r ≤ B := register_update_le v₂ 0 B 0 b₂ (Nat.zero_le _)
      have bs : ∀ r, vs r ≤ B := register_update_le v₂ 0 B _ b₂ (hv 4)
      have copy : CompReach C e mode f h B (some (.copy 7 false), vz, none) (some (.seek true), vs, none) := by
        simpa [vz, vs, v₂, compCopy] using comp_copy_run C e mode f h B 7 vz bz (by simp [vz, compCopy])
      have move : CompReach C e mode f h B (some (.separator true), v₁, none) (some (.seek true), vs, none) := by
        apply AReach.step ⟨comp_preS C e mode h _, b₁⟩
        simp only [astep, compARM, if_neg ne₁]
        apply AReach.step ⟨comp_preS C e mode h _, b₁⟩
        simp only [astep, compARM, v₁, Function.update_self, Function.update_idem]
        change CompReach C e mode f h B (some .suffixReset, v₂, none) _
        apply AReach.step ⟨comp_preS C e mode h _, b₂⟩
        exact copy
      have suffix := comp_suffix_run C e mode f x b p B vs bs (by simp [vs, hb])
        (by simp [vs, v₂, he]) (by simp [vs, v₂, n]) (by simp [vs, v₂, hq]) beyond
        (by simpa [outlen, n] using total)
      have bit : (pairEncode (f x) b).getD p false = b.getD (p-(n+2)) false := by
        rw [pairEncode_getD, if_neg (by dsimp [n] at beyond; omega),
          if_neg (by dsimp [n] at beyond; omega), if_neg (by dsimp [n] at beyond; omega)]
        congr 1
      simpa only [outlen, bit] using (headRun.trans move).halt suffix

/-- Lookup first seeks within the doubled virtual output of `f`, then delegates the two
separator cells and the retained suffix to their common continuation.

**Proof sketch.** The prefix seek is virtual stride one, so a hit is answered by the
lifted bit at half its index. A miss has index exactly twice the output length. This
includes an empty `f` output and flows into the proved separator/suffix continuation. -/
private lemma comp_lookup_run (C e : ℕ) (mode : Bool) (f : List Bool → List Bool)
    (x b : List Bool) (p B : ℕ) (v : Fin 14 → ℕ) (hv : ∀ r, v r ≤ B)
    (hp : v 0 = 0) (he : v 3 = 2*(pairEncode x b).length) (hb : v 4 = 4*x.length+4)
    (hf : v 11 = 2*(f x).length) (hi : v 13 = 0) (hq : v 5 = p)
    (total : (pairEncode (f x) b).length ≤ B) :
    CompHalt C e mode f (pairEncode (pairEncode x b) (Nat.bits p)) B (some (.seek false), v, none)
      (if mode then decide (p < (pairEncode (f x) b).length) else (pairEncode (f x) b).getD p false) := by
  let h := pairEncode (pairEncode x b) (Nat.bits p)
  let n := 2*(f x).length
  have nb : n ≤ B := by rw [length_pairEncode] at total; omega
  have seek := comp_seek_run C e mode false f h B n v hv
    (by simpa [hp, compStride, n] using hf) (by simpa [hi] using nb) (by simp [hi])
  by_cases inside : p < n
  · have cond : v 5 < v 13+n := by omega
    simp only [if_pos cond, Bool.false_eq_true, ↓reduceIte] at seek
    let vh := Function.update (Function.update v 0 p) 13 p
    have bh : ∀ r, vh r ≤ B := register_update_le _ 13 B p
      (register_update_le v 0 B p hv (by omega)) (by omega)
    have path : CompReach C e mode f h B (some (.seek false), v, none) (some .prefixHit, vh, none) := by
      simpa [vh, hp, hi, hq, compStride] using seek
    have ans : (if mode then true else (f x).getD (vh 0/2) false) =
        (if mode then decide (p < (pairEncode (f x) b).length) else (pairEncode (f x) b).getD p false) := by
      have lt : p < (pairEncode (f x) b).length := by rw [length_pairEncode]; dsimp [n] at inside; omega
      cases mode with
      | false =>
        change (f x).getD (p/2) false = (pairEncode (f x) b).getD p false
        rw [pairEncode_getD, if_pos inside]
      | true => simp [lt]
    rw [← ans]
    exact path.halt (comp_prefix_hit C e mode f x b p B vh bh)
  · have cond : ¬ v 5 < v 13+n := by omega
    simp only [if_neg cond, Bool.false_eq_true, ↓reduceIte] at seek
    let vm := Function.update (Function.update v 0 (v 11)) 13 n
    have bm : ∀ r, vm r ≤ B := register_update_le _ 13 B n (register_update_le v 0 B _ hv (hv 11)) nb
    have path : CompReach C e mode f h B (some (.seek false), v, none) (some (.separator false), vm, none) := by
      simpa [vm, hi] using seek
    exact path.halt (comp_separator_run C e mode f x b p B vm bm (by simp [vm, he])
      (by simp [vm, hb]) (by simp [vm, n]) (by simp [vm, hq]) (by omega) total)


/-- The canonicality predicate exactly matches the frozen reshaping definition. -/
private lemma compQ_field (f : List Bool → List Bool) (x b : List Bool) :
    compQ f (pairEncode x b) = if Canon b then pairEncode (f x) b else [] := by
  have canon : (Nat.bits (bitsVal b) = b) ↔ Canon b :=
    ⟨fun eq => eq ▸ canon_bits _, fun hc => (canon_eq_bits b hc).symm⟩
  simp only [compQ, pairDecode_pairEncode, canon]

/-- The two query languages share the program's mode bit. -/
private def compLang (f : List Bool → List Bool) (mode : Bool) : Language Bool :=
  indexLang fun z p => if mode then p < (compQ f z).length else (compQ f z).getD p false = true

/-- On a genuine outer query, the indicator is exactly the requested output bit or boundary test. -/
private lemma comp_lang_pair (f : List Bool → List Bool) (mode : Bool) (z : List Bool) (p : ℕ) :
    MultiTapeTM.indicator (compLang f mode : Set (List Bool)) (pairEncode z (Nat.bits p)) =
      if mode then decide (p < (compQ f z).length) else (compQ f z).getD p false := by
  rw [compLang, indicator_indexLang_pairEncode]
  cases mode <;> simp

/-- A word with no canonical paired representation is rejected in either mode. -/
private lemma comp_bad_query (f : List Bool → List Bool) (mode : Bool) (h : List Bool)
    (bad : ∀ z p, h ≠ pairEncode z (Nat.bits p)) :
    MultiTapeTM.indicator (compLang f mode : Set (List Bool)) h = false := by
  apply Bool.eq_false_iff.mpr
  intro accepts
  rw [indicator_eq_decide, decide_eq_true_eq] at accepts
  obtain ⟨z, p, eq, _⟩ := accepts
  exact bad z p eq

/-- Both outer-tail failure modes have false answers. Width rejection uses the full
composition bound; no unbounded numerical query is stored. -/
private lemma comp_rejected_tail {f : List Bool → List Bool} {C e : ℕ}
    (hf : ∀ x, (f x).length ≤ C * (x.length+1)^e) (mode : Bool) (z tail : List Bool)
    (bad : ¬ (Canon tail ∧ tail.length ≤ (Nat.bits ((2*C+3)*((pairEncode z tail).length+1)^(e+1))).length)) :
    MultiTapeTM.indicator (compLang f mode : Set (List Bool)) (pairEncode z tail) = false := by
  by_cases canonical : Canon tail
  · obtain ⟨p, rfl⟩ : ∃ p, tail = Nat.bits p := ⟨bitsVal tail, canon_eq_bits tail canonical⟩
    have wide : (Nat.bits ((2*C+3)*((pairEncode z (Nat.bits p)).length+1)^(e+1))).length <
        (Nat.bits p).length := Nat.lt_of_not_ge (fun width => bad ⟨canon_bits p, width⟩)
    have overflow := compQ_query_overflow hf z p wide
    rw [comp_lang_pair]
    cases mode with
    | false => exact overflow.1
    | true => simp only [↓reduceIte, overflow.2, decide_false]
  · apply comp_bad_query
    intro w p eq
    have fields := pairEncode_injective (a₁ := (z, tail)) (a₂ := (w, Nat.bits p)) eq
    have word : tail = Nat.bits p := congrArg Prod.snd fields
    exact canonical (word.symm ▸ canon_bits p)

/-- After valid inner syntax, compute the capped length and perform the output lookup.

**Proof sketch.** Compute the exact polynomial cap at `|x|+1`; the capped truthful search
returns `|f x|`, including equality with the cap and cap zero. The public fixed transfer
doubles this length into the virtual prefix boundary. Clear the pointer and use the
proved output-layout run. The full composition bound covers every output counter. -/
private lemma comp_valid_inner (C e : ℕ) (mode : Bool) (f : List Bool → List Bool)
    (bound : ∀ x, (f x).length ≤ C*(x.length+1)^e) (x b : List Bool) (p : ℕ)
    (canonical : Canon b) (v : Fin 14 → ℕ)
    (hv : ∀ r, v r ≤ compBound C e (pairEncode (pairEncode x b) (Nat.bits p)).length)
    (he : v 3 = 2*(pairEncode x b).length) (hb : v 4 = 4*x.length+4) (hq : v 5 = p)
    (ht : v 6 = 0) (ha : v 7 = 0) (hi : v 10 = 0) (hs : v 11 = 0)
    (hf : v 12 = 0) (hj : v 13 = 0) :
    CompHalt C e mode f (pairEncode (pairEncode x b) (Nat.bits p))
      (compBound C e (pairEncode (pairEncode x b) (Nat.bits p)).length)
      (some .innerPrepare, v, none)
      (if mode then decide (p < (pairEncode (f x) b).length) else (pairEncode (f x) b).getD p false) := by
  let h := pairEncode (pairEncode x b) (Nat.bits p)
  let B := compBound C e h.length
  have xn : x.length ≤ h.length := by simp only [h, length_pairEncode]; omega
  have room := comp_bound_room C e h.length
  have output : (pairEncode (f x) b).length ≤ B := by
    have cap := compQ_host_cap bound (pairEncode x b) (Nat.bits p)
    rw [compQ_field, if_pos canonical] at cap
    change (pairEncode (f x) b).length ≤ (2*C+3)*(h.length+1)^(e+1) at cap
    dsimp [B]
    omega
  have dbl : 2*(f x).length ≤ B := by rw [length_pairEncode] at output; omega
  let vp := Function.update (Function.update v 8 (x.length+1)) 7 (C*(x.length+1)^e)
  let vs := Function.update vp 12 (f x).length
  let vd := Function.update (Function.update vs 12 0) 11 (2*(f x).length)
  let vl := Function.update vd 0 0
  have powers := comp_power_bound C e h.length (x.length+1) e false (by omega) (by omega)
  have bp : ∀ r, vp r ≤ B := register_update_le _ 7 B _
    (register_update_le v 8 B _ hv (by omega)) (by simpa [compFactor] using powers.2)
  have bs : ∀ r, vs r ≤ B := register_update_le vp 12 B _ bp (by omega)
  have bd : ∀ r, vd r ≤ B := register_update_le _ 11 B _
    (register_update_le vs 12 B 0 bs (Nat.zero_le _)) dbl
  have bl : ∀ r, vl r ≤ B := register_update_le vd 0 B 0 bd (Nat.zero_le _)
  have polynomial := comp_inner_prepare C e mode f h x.length v hv hb ht ha hi hs xn
  have search := comp_length_search C e mode f h B (f x).length vp bp
    (by simp [vp, hf]) (by simpa [vp] using bound x)
    (by intro i _; simpa [h] using comp_lifted f true x b p i)
  have double : CompReach C e mode f h B (some .doubleTest, vs, none) (some .lookupReset, vd, none) := by
    have move := registerScale_loop (compARM C e mode) (compOracle f) h 12 11 (by decide)
      .doubleTest .doubleDown .lookupReset
      (fun i => if i = 0 then .doubleInc false else if i = 1 then .doubleInc true else .doubleTest)
      2 rfl rfl
      (by
        intro i hi
        have cases : i = 0 ∨ i = 1 := by omega
        rcases cases with rfl | rfl <;> rfl)
      rfl B vs bs (by simpa [vs, vp, hs] using dbl)
    simpa [vd, vs, vp, hs] using move
  have lookup := comp_lookup_run C e mode f x b p B vl bl (by simp [vl])
    (by simp [vl, vd, vs, vp, he]) (by simp [vl, vd, vs, vp, hb])
    (by simp [vl, vd]) (by simp [vl, vd, vs, vp, hj]) (by simp [vl, vd, vs, vp, hq]) output
  apply (polynomial.trans (search.trans double)).halt
  apply AHalt.step ⟨comp_preS C e mode h _, bd⟩
  exact lookup

/-- Inner shape and canonicality validation lead either to false or to the proved valid
inner computation. Arbitrary first fields and arbitrarily large canonical suffixes are
allowed.

**Proof sketch.** The received stride-two pair scan locates the inner suffix. A malformed
pair gives the empty reshaping. Save the suffix boundary and invoke the independent
last-bit canonicality check; its failure also gives the empty reshaping. Otherwise all
scratch is still clear, so the valid-inner computation applies. -/
private lemma comp_inner_run (C e : ℕ) (mode : Bool) (f : List Bool → List Bool)
    (bound : ∀ x, (f x).length ≤ C*(x.length+1)^e) (z : List Bool) (p : ℕ)
    (pb : p ≤ compBound C e (pairEncode z (Nat.bits p)).length) :
    CompHalt C e mode f (pairEncode z (Nat.bits p)) (compBound C e (pairEncode z (Nat.bits p)).length)
      (some (.scan true), compValues (pairEncode z (Nat.bits p)).length
        (tail := 2*z.length+2) (stop := 2*z.length) (query := p)
        (base := (pairEncode z (Nat.bits p)).length+1), none)
      (if mode then decide (p < (compQ f z).length) else (compQ f z).getD p false) := by
  let h := pairEncode z (Nat.bits p)
  let B := compBound C e h.length
  let v := compValues h.length (tail := 2*z.length+2) (stop := 2*z.length) (query := p) (base := h.length+1)
  change p ≤ B at pb
  have room := (comp_bound_room C e h.length).1
  have len : h.length = 2*z.length+2+(Nat.bits p).length := length_pairEncode _ _
  have bv : ∀ r, v r ≤ B := by simp [v, compValues, Fin.forall_fin_succ]; dsimp [B] at *; omega
  have scan := comp_pair_run C e mode true f h z B v bv (by simp [v, compLimit, compStride])
    (by intro i hi; simpa [v, compStride] using drop_first_read z (Nat.bits p) i hi)
  cases shape : pairDecode z with
  | none =>
    simp only [shape] at scan
    obtain ⟨t, tl, path⟩ := scan
    have bp : v 0 + compStride true*t ≤ B := by simp [v, compStride]; dsimp [B] at *; omega
    have out : compQ f z = [] := by simp [compQ, shape]
    simp only [out, List.length_nil, Nat.not_lt_zero, decide_false, List.getD_nil, ite_self]
    exact path.halt (comp_ret C e mode false f h B _ (register_update_le v 0 B _ bv bp))
  | some pair =>
    rcases pair with ⟨x, b⟩
    have eq := eq_pairEncode_of_pairDecode z x b shape
    subst z
    simp only [pairDecode_pairEncode] at scan
    let va := Function.update v 0 (4*x.length+4)
    let vb := Function.update va 4 (4*x.length+4)
    have addr : 4*x.length+4 ≤ B := by
      have vl : 2*(pairEncode x b).length ≤ B := by simpa [v] using bv 3
      rw [length_pairEncode] at vl
      omega
    have ba : ∀ r, va r ≤ B := register_update_le v 0 B _ bv addr
    have bb : ∀ r, vb r ≤ B := register_update_le va 4 B _ ba addr
    have scanned : CompReach C e mode f h B (some (.scan true), v, none) (some (.copy 4 false), va, none) := by
      simpa [va, v, compStride, Nat.mul_add, ← Nat.mul_assoc] using scan
    have save : CompReach C e mode f h B (some (.copy 4 false), va, none) (some .canonical, vb, none) := by
      simpa [vb, va, compCopy] using comp_copy_run C e mode f h B 4 va ba (by simp [va, v, compCopy])
    obtain ⟨vc, bc, frame, canonical⟩ := comp_canonical_run C e mode f x b (Nat.bits p) B vb bb
      (by simp [vb, va, v]) (by simp [vb])
    by_cases canon : Canon b
    · simp only [if_pos canon] at canonical
      rw [compQ_field, if_pos canon]
      apply (scanned.trans (save.trans canonical)).halt
      apply comp_valid_inner C e mode f bound x b p canon vc bc
      all_goals first
        | (rw [frame _ (by decide)]; simp [vb, va, v])
    · simp only [if_neg canon] at canonical
      rw [compQ_field, if_neg canon]
      simp only [List.length_nil, Nat.not_lt_zero, decide_false, List.getD_nil, ite_self]
      exact (scanned.trans (save.trans canonical)).halt (comp_ret C e mode false f h B vc bc)


/-- The composition-query ARM halts correctly on every physical input within one fixed
polynomial register bound.

**Proof sketch.** Count the host and validate its outer pair. Save the pair boundaries,
construct the full output cap, and validate the canonical outer index before decoding.
Malformed or over-width queries reject by the proved language laws. The bounded decoded
query then enters the complete inner validation, capped search, and output-layout run. -/
private lemma comp_run (C e : ℕ) (mode : Bool) (f : List Bool → List Bool)
    (bound : ∀ x, (f x).length ≤ C*(x.length+1)^e) (h : List Bool) :
    CompHalt C e mode f h (compBound C e h.length) (some .count, fun _ => 0, none)
      (MultiTapeTM.indicator (compLang f mode : Set (List Bool)) h) := by
  have room := (comp_bound_room C e h.length).1
  have count := inputLength_loop (compARM C e mode) (compOracle f) h 1 1 .count .countInc (.scan false)
    rfl rfl (fun i _ => comp_len f h i) (compBound C e h.length) (by omega) (fun _ => 0)
    (by intro r; exact Nat.zero_le _) (Nat.zero_le _)
  have vec : Function.update (fun _ : Fin 14 => 0) 1 h.length = compValues h.length := by
    have zero : (fun _ : Fin 14 => 0) = compValues 0 := by
      simp only [compValues, Matrix.vec_single_eq_const, Matrix.vecCons_const]
    rw [zero]
    simp
  rw [vec] at count
  have bv : ∀ r, (compValues h.length) r ≤ compBound C e h.length := by
    simp [compValues, Fin.forall_fin_succ]; omega
  have scan := comp_pair_run C e mode false f h h (compBound C e h.length) (compValues h.length) bv
    (by simp [compLimit, compStride]) (by intro i _; simp [compStride])
  cases shape : pairDecode h with
  | none =>
    simp only [shape] at scan
    obtain ⟨t, ht, path⟩ := scan
    have bp : (compValues h.length) 0 + compStride false*t ≤ compBound C e h.length := by
      simp [compStride]; omega
    have answer := comp_bad_query f mode h (by
      intro z p eq
      rw [eq, pairDecode_pairEncode] at shape
      contradiction)
    rw [answer]
    exact (count.trans path).halt (comp_ret C e mode false f h (compBound C e h.length) _
      (register_update_le (compValues h.length) 0 _ _ bv bp))
  | some pair =>
    rcases pair with ⟨z, tail⟩
    have eq := eq_pairEncode_of_pairDecode h z tail shape
    subst h
    simp only [pairDecode_pairEncode] at scan
    have start : CompReach C e mode f (pairEncode z tail) (compBound C e (pairEncode z tail).length)
        (some .count, fun _ => 0, none)
        (some (.copy 0 false), compValues (pairEncode z tail).length (ptr := 2*z.length+2), none) := by
      apply count.trans
      simpa [compStride] using scan
    have prepare := comp_outer_prepare C e mode f z tail
    have decode := comp_outer_decode C e mode f z tail
    dsimp only at prepare decode
    by_cases good : Canon tail ∧ tail.length ≤
        (Nat.bits ((2*C+3)*((pairEncode z tail).length+1)^(e+1))).length
    · simp only [if_pos good] at decode
      obtain ⟨p, rfl⟩ : ∃ p, tail = Nat.bits p := ⟨bitsVal tail, canon_eq_bits tail good.1⟩
      have pb := query_index_bound p ((2*C+3)*((pairEncode z (Nat.bits p)).length+1)^(e+1)) good.2
      have bounded : p ≤ compBound C e (pairEncode z (Nat.bits p)).length :=
        pb.trans (comp_bound_room C e (pairEncode z (Nat.bits p)).length).2
      simp only [bitsVal_bits] at decode
      rw [comp_lang_pair]
      exact (start.trans (prepare.trans decode)).halt (comp_inner_run C e mode f bound z p bounded)
    · simp only [if_neg good] at decode
      rw [comp_rejected_tail bound mode z tail good]
      exact (start.trans prepare).halt decode

/-- Compile the single mode-parametrized construction against the four proved languages. -/
private lemma comp_mem {f : List Bool → List Bool} (hf : ImplicitlyLogspaceComputable f)
    (C e : ℕ) (bound : ∀ x, (f x).length ≤ C*(x.length+1)^e) (mode : Bool) :
    compLang f mode ∈ LOGSPACE := by
  apply arm_decides_poly (compARM C e mode) .count (compBank f) (compBank_mem hf)
    (8*(2*C+3)) (e+1)
  intro h
  exact comp_run C e mode f bound h

/-- **`comp`'s query reshaping is implicitly logspace computable** (phase P4.4b; proved): if `f` is, so is `compQ f`.

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
  obtain ⟨C, e, bound⟩ := hf.1
  refine ⟨⟨2*C+3, e+1, compQ_length_le bound⟩, ?_, ?_⟩
  · simpa only [compLang, Bool.false_eq_true, ↓reduceIte] using comp_mem hf C e bound false
  · simpa only [compLang, ↓reduceIte] using comp_mem hf C e bound true

end Complexity
