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

/-- **Dropping the middle index is implicitly logspace computable** (phase P4.4b; spec, fill
pending).

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
  sorry

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
