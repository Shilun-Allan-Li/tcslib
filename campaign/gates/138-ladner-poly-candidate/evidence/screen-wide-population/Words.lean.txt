/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.ClassP.BinaryArith.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Lists of words in polynomial time

Infrastructure for [AB09 §7.2]; not itself a result of the book. A list of words
`[w₁, …, wₖ]` is the word `⟨w₁, ⟨w₂, … ⟨wₖ, []⟩ …⟩⟩` (`Complexity.BinArith.encWords`). Every word
is read as a list by `Complexity.BinArith.decWords`, which peels first components until the
empty word, so the loops below are specified on all words. Vectors and matrices of numbers
(the determinant of `TCSlib.Complexity.ClassP.BinaryArith.DetMod`) are lists of such lists.

## Main definitions

* `Complexity.BinArith.encWords`, `Complexity.BinArith.decWords` — encoding and reading.
* `Complexity.BinArith.mapW`, `Complexity.BinArith.zipWithW` — map (with a shared parameter)
  and zip of word-level functions over encoded lists.
* `Complexity.BinArith.countW` — the number of entries, in unary.

## Main results

* `Complexity.BinArith.polyTimeComputable_mapW`, `Complexity.BinArith.mapW_pairEncode`.
* `Complexity.BinArith.polyTimeComputable_zipWithW`, `Complexity.BinArith.zipWithW_pairEncode`.
* `Complexity.BinArith.polyTimeComputable_countW`, `Complexity.BinArith.countW_eq`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.2.)
-/

namespace Complexity

namespace BinArith

open Turing LogProg

/-! ### Encoding and reading -/

/-- A list of words, as the concatenation of the pairs `⟨w, []⟩`. -/
def encWords (L : List (List Bool)) : List Bool := L.flatMap (fun w => pairEncode w [])

/-- A pair with empty second component, followed by `b`, is the pair `⟨a, b⟩`. -/
theorem pairEncode_nil_append (a b : List Bool) : pairEncode a [] ++ b = pairEncode a b := by
  simp [pairEncode]

/-- The empty list is the empty word. -/
@[simp] theorem encWords_nil : encWords [] = [] := rfl

/-- `encWords (w :: L) = ⟨w, encWords L⟩`. -/
@[simp] theorem encWords_cons (w : List Bool) (L : List (List Bool)) :
    encWords (w :: L) = pairEncode w (encWords L) := by
  simp [encWords, pairEncode_nil_append]

/-- Appending one word at the end of an encoded list. -/
theorem encWords_append_singleton (L : List (List Bool)) (w : List Bool) :
    encWords (L ++ [w]) = encWords L ++ pairEncode w [] := by
  simp [encWords]

/-- The length of an encoded list. -/
theorem length_encWords (L : List (List Bool)) :
    (encWords L).length = (L.map (fun w => 2 * w.length + 2)).sum := by
  induction L with
  | nil => rfl
  | cons w L ih => simp [length_pairEncode, ih]

/-- An encoded list of `k` words of length at most `c` has length at most `k(2c + 2)`. -/
theorem length_encWords_le (L : List (List Bool)) (c : ℕ) (h : ∀ w ∈ L, w.length ≤ c) :
    (encWords L).length ≤ L.length * (2 * c + 2) := by
  induction L with
  | nil => simp
  | cons w L ih =>
    simp only [encWords_cons, length_pairEncode, List.length_cons]
    have h1 := h w (by simp)
    have h2 := ih (fun v hv => h v (by simp [hv]))
    nlinarith

/-- The second projection of a nonempty word is strictly shorter. -/
theorem length_pairSndD_lt {w : List Bool} (h : w ≠ []) : (pairSndD w).length < w.length := by
  cases hd : pairDecode w with
  | none => simp [pairSndD, hd]; exact List.length_pos_iff.mpr h
  | some ab =>
    obtain ⟨a, b⟩ := ab
    have hz := eq_pairEncode_of_pairDecode w a b hd
    rw [hz, pairSndD_pairEncode, length_pairEncode]
    omega

/-- Read a word as a list of words: peel first components until the empty word. -/
def decWords (w : List Bool) : List (List Bool) :=
  if _h : w = [] then [] else pairFstD w :: decWords (pairSndD w)
termination_by w.length
decreasing_by exact length_pairSndD_lt ‹_›

/-- The reading of the empty word. -/
@[simp] theorem decWords_nil : decWords [] = [] := by rw [decWords]; simp

/-- The reading of a nonempty word. -/
theorem decWords_of_ne {w : List Bool} (h : w ≠ []) :
    decWords w = pairFstD w :: decWords (pairSndD w) := by
  rw [decWords]; simp [h]

/-- Reading an encoded list gives the list back. -/
@[simp] theorem decWords_encWords (L : List (List Bool)) : decWords (encWords L) = L := by
  induction L with
  | nil => simp
  | cons w L ih =>
    rw [encWords_cons, decWords_of_ne (by simp [pairEncode]), pairFstD_pairEncode,
      pairSndD_pairEncode, ih]

/-- A word holds at most as many list entries as it has letters. -/
theorem length_decWords_le (w : List Bool) : (decWords w).length ≤ w.length := by
  by_cases hw : w = []
  · simp [hw]
  · rw [decWords_of_ne hw, List.length_cons]
    have := length_pairSndD_lt hw
    have := length_decWords_le (pairSndD w)
    omega
termination_by w.length
decreasing_by exact length_pairSndD_lt hw

/-- Every entry of a word's list is no longer than the word. -/
theorem length_le_of_mem_decWords {w x : List Bool} (hx : x ∈ decWords w) :
    x.length ≤ w.length := by
  by_cases hw : w = []
  · simp [hw] at hx
  · rw [decWords_of_ne hw, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact length_pairFstD_le w
    · have := length_pairSndD_lt hw
      have := length_le_of_mem_decWords hx
      omega
termination_by w.length
decreasing_by exact length_pairSndD_lt hw

/-! ### The list loop -/

/-- Iterated second projections stay inside the word. -/
theorem length_iterate_pairSndD_le (w : List Bool) (i : ℕ) :
    (pairSndD^[i] w).length ≤ w.length := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply']; exact (length_pairSndD_le _).trans ih

/-- The emptiness of iterated second projections of the empty word. -/
theorem iterate_pairSndD_nil (i : ℕ) : pairSndD^[i] ([] : List Bool) = [] :=
  Function.iterate_fixed rfl i

/-- **The list loop**: over `N ≥ |w|` rounds, emitting `c x` for the head `x` of each nonempty
suffix `pairSndD^[i] w` outputs the concatenation of `c` over the list read from `w`. -/
theorem flatMap_listLoop (c : List Bool → List Bool) :
    ∀ (N : ℕ) (w : List Bool), w.length ≤ N →
      (List.range N).flatMap (fun i => if pairSndD^[i] w = [] then []
        else c (pairFstD (pairSndD^[i] w))) = (decWords w).flatMap c := by
  intro N
  induction N with
  | zero => intro w hw; simp [List.eq_nil_of_length_eq_zero (by omega : w.length = 0)]
  | succ N ih =>
    intro w hw
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [Function.iterate_zero_apply, Nat.succ_eq_add_one, Function.iterate_succ_apply]
    by_cases h : w = []
    · subst h
      have := ih [] (by simp)
      simp only [pairSndD, pairDecode, Option.map_none, Option.getD_none, if_true,
        List.nil_append] at this ⊢
      simpa using this
    · rw [if_neg h, ih (pairSndD w) (by have := length_pairSndD_lt h; omega),
        decWords_of_ne h, List.flatMap_cons]

/-! ### Map -/

/-- One round of the map loop on `⟨q, list⟩`: drop the head entry. -/
private def listStep (S : List Bool) : List Bool := pairEncode (pairFstD S) (pairSndD (pairSndD S))

/-- The chunk of the map loop on `⟨q, list⟩`: `⟨g ⟨q, head⟩, []⟩` for a nonempty list. -/
private def mapChunk (g : List Bool → List Bool) (S : List Bool) : List Bool :=
  if pairSndD S = [] then []
  else pairEncode (g (pairEncode (pairFstD S) (pairFstD (pairSndD S)))) []

/-- The map loop on `⟨q, list⟩` applying `g ⟨q, ·⟩` to every entry. -/
def mapW (g : List Bool → List Bool) (S : List Bool) : List Bool :=
  (List.range (1 * (S.length + 1) ^ 1 + 1)).flatMap (fun i => mapChunk g (listStep^[i] S))

/-- The iterates of the map loop from `⟨q, w⟩`. -/
private theorem iterate_listStep (q w : List Bool) (i : ℕ) :
    listStep^[i] (pairEncode q w) = pairEncode q (pairSndD^[i] w) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    simp [listStep]

/-- **The map loop maps**: on `⟨q, w⟩` it outputs the encoded list `g ⟨q, x⟩` over the entries
`x` read from `w`. -/
theorem mapW_pairEncode (g : List Bool → List Bool) (q w : List Bool) :
    mapW g (pairEncode q w) = encWords ((decWords w).map (fun x => g (pairEncode q x))) := by
  unfold mapW
  simp only [iterate_listStep, mapChunk, pairSndD_pairEncode, pairFstD_pairEncode]
  rw [flatMap_listLoop (fun x => pairEncode (g (pairEncode q x)) []) _ w
    (by simp [length_pairEncode]; omega)]
  simp [encWords, List.flatMap_map]

/-- **The map loop is polynomial-time** for a polynomial-time `g`.

**Proof sketch.** The round drops the head entry and the emitted chunk is `g` of it; after
`i` rounds the state is `⟨q, l⟩` with `l` a suffix of the input list (`iterate_listStep`), so
the emit loop `Complexity.polyTimeComputable_emitIter` applies with a linear bound. -/
theorem polyTimeComputable_mapW {g : List Bool → List Bool} (hg : PolyTimeComputable g) :
    PolyTimeComputable (mapW g) := by
  have hs : PolyTimeComputable listStep :=
    polyTimeComputable_pairFstD.pairEncode polyTimeComputable_slot3
  have he : PolyTimeComputable (mapChunk g) := by
    unfold mapChunk
    convert polyTimeComputable_ite (polyTimeComputable_isNil.comp polyTimeComputable_pairSndD)
      (polyTimeComputable_const [])
      ((hg.comp (polyTimeComputable_pairFstD.pairEncode polyTimeComputable_slot2)).pairEncode
        (polyTimeComputable_const [])) using 1
    funext S; simp
  refine polyTimeComputable_emitIter hs he 1 1 2 1 (fun w i => ?_)
  cases i with
  | zero => simp; omega
  | succ i =>
    rw [Function.iterate_succ_apply, show listStep w = pairEncode (pairFstD w) (pairSndD
      (pairSndD w)) from rfl, iterate_listStep, length_pairEncode]
    have h1 := length_iterate_pairSndD_le (pairSndD (pairSndD w)) i
    have h2 := length_pair_components_le w
    have h3 := length_pairSndD_le (pairSndD w)
    simp; omega

/-! ### Zip -/

/-- One round of the zip loop on `⟨q, ⟨l₁, l₂⟩⟩`: drop the head entries of both lists. -/
private def zipStep (S : List Bool) : List Bool :=
  pairEncode (pairFstD S)
    (pairEncode (pairSndD (pairFstD (pairSndD S))) (pairSndD (pairSndD (pairSndD S))))

/-- The chunk of the zip loop: `⟨g ⟨q, ⟨x, y⟩⟩, []⟩` for the heads `x`, `y` of two nonempty
lists. -/
private def zipChunk (g : List Bool → List Bool) (S : List Bool) : List Bool :=
  if pairFstD (pairSndD S) = [] ∨ pairSndD (pairSndD S) = [] then []
  else pairEncode (g (pairEncode (pairFstD S) (pairEncode (pairFstD (pairFstD (pairSndD S)))
    (pairFstD (pairSndD (pairSndD S)))))) []

/-- The zip loop on `⟨q, ⟨l₁, l₂⟩⟩` applying `g ⟨q, ⟨x, y⟩⟩` to paired entries. -/
def zipWithW (g : List Bool → List Bool) (S : List Bool) : List Bool :=
  (List.range (1 * (S.length + 1) ^ 1 + 1)).flatMap (fun i => zipChunk g (zipStep^[i] S))

/-- The iterates of the zip loop from `⟨q, ⟨l₁, l₂⟩⟩`. -/
private theorem iterate_zipStep (q l₁ l₂ : List Bool) (i : ℕ) :
    zipStep^[i] (pairEncode q (pairEncode l₁ l₂)) =
      pairEncode q (pairEncode (pairSndD^[i] l₁) (pairSndD^[i] l₂)) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply',
      Function.iterate_succ_apply']
    simp [zipStep]

/-- The zip loop body over `N ≥ |l₁|` rounds zips the two lists read from `l₁`, `l₂`.

**Proof sketch.** Induction on `N`: round `0` emits `c` of the two head entries, or nothing
when a list is empty, and the remaining rounds are the statement for the tails
(`decWords_of_ne`). -/
private theorem flatMap_zipLoop (c : List Bool → List Bool → List Bool) :
    ∀ (N : ℕ) (l₁ l₂ : List Bool), l₁.length ≤ N →
      (List.range N).flatMap (fun i =>
        if pairSndD^[i] l₁ = [] ∨ pairSndD^[i] l₂ = [] then []
        else c (pairFstD (pairSndD^[i] l₁)) (pairFstD (pairSndD^[i] l₂))) =
        (List.zipWith c (decWords l₁) (decWords l₂)).flatMap id := by
  intro N
  induction N with
  | zero =>
    intro l₁ l₂ h
    simp [List.eq_nil_of_length_eq_zero (by omega : l₁.length = 0)]
  | succ N ih =>
    intro l₁ l₂ h
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [Function.iterate_zero_apply, Nat.succ_eq_add_one, Function.iterate_succ_apply]
    have hlen : (pairSndD l₁).length ≤ N := by
      by_cases h1 : l₁ = []
      · subst h1; simp [pairSndD, pairDecode]
      · have := length_pairSndD_lt h1; omega
    rw [ih (pairSndD l₁) (pairSndD l₂) hlen]
    by_cases h1 : l₁ = []
    · subst h1; simp [show pairSndD ([] : List Bool) = [] from rfl]
    by_cases h2 : l₂ = []
    · subst h2; simp [show pairSndD ([] : List Bool) = [] from rfl]
    rw [if_neg (by tauto), decWords_of_ne h1, decWords_of_ne h2]
    simp

/-- **The zip loop zips**: on `⟨q, ⟨l₁, l₂⟩⟩` it outputs the encoded list of `g ⟨q, ⟨x, y⟩⟩`
over the paired entries read from `l₁` and `l₂` (truncated to the shorter list). -/
theorem zipWithW_pairEncode (g : List Bool → List Bool) (q l₁ l₂ : List Bool) :
    zipWithW g (pairEncode q (pairEncode l₁ l₂)) =
      encWords (List.zipWith (fun x y => g (pairEncode q (pairEncode x y)))
        (decWords l₁) (decWords l₂)) := by
  unfold zipWithW
  simp only [iterate_zipStep, zipChunk, pairSndD_pairEncode, pairFstD_pairEncode]
  rw [flatMap_zipLoop (fun x y => pairEncode (g (pairEncode q (pairEncode x y))) []) _ l₁ l₂
    (by simp [length_pairEncode]; omega)]
  simp [encWords, List.flatMap_def, List.map_zipWith]

/-- **The zip loop is polynomial-time** for a polynomial-time `g`.

**Proof sketch.** As for `polyTimeComputable_mapW`: the round drops the head entries of both
lists, the chunk is `g` of them, and the iterates keep suffixes of the input
(`iterate_zipStep`), so `Complexity.polyTimeComputable_emitIter` applies. -/
theorem polyTimeComputable_zipWithW {g : List Bool → List Bool} (hg : PolyTimeComputable g) :
    PolyTimeComputable (zipWithW g) := by
  have hl1 : PolyTimeComputable (fun S => pairFstD (pairSndD S)) := polyTimeComputable_slot2
  have hl2 : PolyTimeComputable (fun S => pairSndD (pairSndD S)) := polyTimeComputable_slot3
  have hs : PolyTimeComputable zipStep :=
    polyTimeComputable_pairFstD.pairEncode ((polyTimeComputable_pairSndD.comp hl1).pairEncode
      (polyTimeComputable_pairSndD.comp hl2))
  have he : PolyTimeComputable (zipChunk g) := by
    unfold zipChunk
    convert polyTimeComputable_ite
      (polyTimeComputable_or (polyTimeComputable_isNil.comp hl1)
        (polyTimeComputable_isNil.comp hl2)) (polyTimeComputable_const [])
      ((hg.comp (polyTimeComputable_pairFstD.pairEncode
        ((polyTimeComputable_pairFstD.comp hl1).pairEncode
          (polyTimeComputable_pairFstD.comp hl2)))).pairEncode (polyTimeComputable_const []))
      using 1
    funext S; simp
  refine polyTimeComputable_emitIter hs he 1 1 5 1 (fun w i => ?_)
  cases i with
  | zero => simp; omega
  | succ i =>
    rw [Function.iterate_succ_apply, show zipStep w = pairEncode (pairFstD w)
      (pairEncode (pairSndD (pairFstD (pairSndD w))) (pairSndD (pairSndD (pairSndD w))))
      from rfl, iterate_zipStep, length_pairEncode, length_pairEncode]
    have h1 := length_iterate_pairSndD_le (pairSndD (pairFstD (pairSndD w))) i
    have h2 := length_iterate_pairSndD_le (pairSndD (pairSndD (pairSndD w))) i
    have h3 := length_pair_components_le w
    have h4 := length_pair_components_le (pairSndD w)
    have h5 := length_pairSndD_le (pairFstD (pairSndD w))
    have h6 := length_pairSndD_le (pairSndD (pairSndD w))
    simp; omega

/-! ### Counting -/

/-- The number of entries of the list read from `w`, in unary. -/
def countW (w : List Bool) : List Bool :=
  (List.range (1 * (w.length + 1) ^ 1 + 1)).flatMap
    (fun i => if pairSndD^[i] w = [] then [] else [true])

/-- `countW w` is `1^k` for the number `k` of entries read from `w`. -/
theorem countW_eq (w : List Bool) : countW w = List.replicate (decWords w).length true := by
  unfold countW
  rw [flatMap_listLoop (fun _ => [true]) _ w (by simp; omega)]
  induction decWords w with
  | nil => rfl
  | cons x L ih => simp [ih, List.replicate_succ]

/-- **Counting the entries is polynomial-time.** -/
theorem polyTimeComputable_countW : PolyTimeComputable countW := by
  have he : PolyTimeComputable (fun w : List Bool => if w = [] then [] else [true]) := by
    convert polyTimeComputable_ite polyTimeComputable_isNil (polyTimeComputable_const [])
      (polyTimeComputable_const [true]) using 1
    funext w; simp
  exact polyTimeComputable_emitIter polyTimeComputable_pairSndD he 1 1 1 1 (fun w i => by
    have := length_iterate_pairSndD_le w i; simp; omega)

end BinArith

end Complexity
