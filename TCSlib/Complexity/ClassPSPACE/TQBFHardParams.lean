/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.ClassPSPACE.TQBFHardBridge
import TCSlib.Complexity.Formulas.QBFEncoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Parameters of the `TQBF` reduction, and its quantifier prefix

For a machine `N` deciding a language in space `d (n^c + 1)`, the reduction uses the radius
`2d (n + 1)^c` and blocks (and levels) of width `w = A (n + 1)^(c + 1)` with the machine
constant `A = wCoef N d`. This file proves that this width holds a code word
(`vlen_le_vwid`) and that `2^w` steps suffice to reach every configuration
(`configBound_le_two_pow`), and that the bits of the level part of the quantifier prefix
(`w` levels of `∃^w ∀^w ∀^w`) are polynomial-time computable (`polyTimeComputable_levelBits`,
a round loop over `Complexity.polyTimeComputable_of_loop`).

Infrastructure for `Complexity.TQBF_PSPACEHard`; not itself a book result.

## Main definitions

* `Complexity.TQBFHard.wCoef` — the width coefficient.
* `Complexity.TQBFHard.levelBits` — the prefix bits of `r` levels.

## Main results

* `Complexity.TQBFHard.vlen_le_vwid`, `Complexity.TQBFHard.configBound_le_two_pow` — the
  width suffices. [AB09, Claim 4.4(1): `2^{O(s(n))}` configurations]
* `Complexity.TQBFHard.map_quantBit_levelQuants` — the prefix bits of the levels.
* `Complexity.TQBFHard.polyTimeComputable_levelBits` — they are polynomial-time.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1, Claim 4.4; §4.2, Theorem 4.13.)
-/

namespace Complexity

namespace TQBFHard

open Turing Codec QBF

/-! ### The width -/

variable (N : FinNDTM Bool) (d c : ℕ)

/-- **The width coefficient** of a machine `N` with space constant `d`. -/
def wCoef : ℕ := 4 * d * W N + W N + 12 * N.k * d + 3 * N.k + 2 * Fintype.card N.State + 8

/-- The binary length of `n + 1` is at most `n + 1`. -/
theorem wP_le (n : ℕ) : wP n ≤ n + 1 :=
  LogProg.length_bits_le (Nat.lt_two_pow_self)

/-- **The width holds a code word**: `codeLen ≤ wCoef · (n + 1)^(c + 1)`. -/
theorem vlen_le_vwid (n : ℕ) : vlen N d c n ≤ vwid (wCoef N d) (c + 1) n := by
  have hQP : (n + 1) ^ c ≤ (n + 1) ^ (c + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hP1 : 1 ≤ (n + 1) ^ c := Nat.one_le_pow _ _ (by omega)
  have hnP : n + 1 ≤ (n + 1) ^ (c + 1) := by
    calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  have hw := wP_le n
  set P := (n + 1) ^ (c + 1)
  set Q := (n + 1) ^ c
  have h1 : 4 * d * W N * Q ≤ 4 * d * W N * P := Nat.mul_le_mul_left _ hQP
  have h2 : W N ≤ W N * P := Nat.le_mul_of_pos_right _ (by omega)
  have h4 : 2 * P ≤ (12 * N.k * d + 3 * N.k + 2 * Fintype.card N.State + 8) * P :=
    Nat.mul_le_mul_right _ (by omega)
  have e1 : vlen N d c n = 4 * d * W N * Q + W N + wP n + 1 := by
    simp only [vlen, codeLen, vrad, Q]; ring
  have e2 : vwid (wCoef N d) (c + 1) n = 4 * d * W N * P + W N * P +
      (12 * N.k * d + 3 * N.k + 2 * Fintype.card N.State + 8) * P := by
    simp only [vwid, wCoef, P]; ring
  rw [e1, e2]
  omega

/-- `3m ≤ 2^(2m)`. -/
private theorem three_mul_le (m : ℕ) : 3 * m ≤ 2 ^ (2 * m) := by
  have h1 : m + 1 ≤ 2 ^ m := Nat.lt_two_pow_self
  have h2 : 2 ^ (2 * m) = 2 ^ m * 2 ^ m := by rw [two_mul, pow_add]
  have h3 : 3 * m ≤ (m + 1) * (m + 1) := by nlinarith [Nat.le_mul_self m]
  rw [h2]
  exact h3.trans (Nat.mul_le_mul h1 h1)

/-- **`2^w` steps suffice** ([AB09, Claim 4.4(1)]): the vertex count at radius
`2d (n + 1)^c` is at most `2^w`.

**Proof sketch.** `3(Q + 1) ≤ 2^{2(Q+1)}`, `n + 2 ≤ 2^{n+1}`, `3^e ≤ 2^{2e}` and
`(2s + 1)^k ≤ 2^{k(2s+1)}`, so the count is at most `2^X` with
`X = 2(Q + 1) + (n + 1) + 3k(2s + 1) ≤ w`. -/
theorem configBound_le_two_pow (n : ℕ) :
    N.configBound n (vrad d c n) ≤ 2 ^ vwid (wCoef N d) (c + 1) n := by
  set s := vrad d c n
  set e := N.k * (2 * s + 1)
  have b1 : 3 * (Fintype.card N.State + 1) ≤ 2 ^ (2 * (Fintype.card N.State + 1)) :=
    three_mul_le _
  have b2 : n + 2 ≤ 2 ^ (n + 1) := Nat.lt_two_pow_self
  have key3 : ∀ m : ℕ, 3 ^ m ≤ 2 ^ (2 * m) := fun m => by
    rw [pow_mul]; exact Nat.pow_le_pow_left (by norm_num) m
  have b3 : 3 ^ e ≤ 2 ^ (2 * e) := key3 e
  have b4 : (2 * s + 1) ^ N.k ≤ 2 ^ e := by
    have : 2 * s + 1 < 2 ^ (2 * s + 1) := Nat.lt_two_pow_self
    calc (2 * s + 1) ^ N.k ≤ (2 ^ (2 * s + 1)) ^ N.k := Nat.pow_le_pow_left this.le _
      _ = 2 ^ e := by rw [← pow_mul]; congr 1; simp only [e]; ring
  have hX : 2 * (Fintype.card N.State + 1) + (n + 1) + 2 * e + e ≤
      vwid (wCoef N d) (c + 1) n := by
    have hQP : (n + 1) ^ c ≤ (n + 1) ^ (c + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hnP : n + 1 ≤ (n + 1) ^ (c + 1) := by
      calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
        _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
    have hP1 : 1 ≤ (n + 1) ^ (c + 1) := by omega
    set P := (n + 1) ^ (c + 1)
    set Q := (n + 1) ^ c
    have h1 : 12 * N.k * d * Q ≤ 12 * N.k * d * P := Nat.mul_le_mul_left _ hQP
    have e1 : 2 * (Fintype.card N.State + 1) + (n + 1) + 2 * e + e =
        2 * Fintype.card N.State + 3 + n + 12 * N.k * d * Q + 3 * N.k := by
      simp only [e, s, vrad, Q]; ring
    have e2 : vwid (wCoef N d) (c + 1) n = 4 * d * W N * P + W N * P + 12 * N.k * d * P +
        3 * N.k * P + 2 * Fintype.card N.State * P + 8 * P := by
      simp only [vwid, wCoef, P]; ring
    have h3 : 3 * N.k ≤ 3 * N.k * P := Nat.le_mul_of_pos_right _ (by omega)
    have h5 : 2 * Fintype.card N.State ≤ 2 * Fintype.card N.State * P :=
      Nat.le_mul_of_pos_right _ (by omega)
    rw [e1, e2]
    omega
  calc N.configBound n s
      = (3 * (Fintype.card N.State + 1)) * (n + 2) * 3 ^ e * (2 * s + 1) ^ N.k := by
        simp only [FinNDTM.configBound, e]; ring
    _ ≤ 2 ^ (2 * (Fintype.card N.State + 1)) * 2 ^ (n + 1) * 2 ^ (2 * e) * 2 ^ e := by
        gcongr
    _ = 2 ^ (2 * (Fintype.card N.State + 1) + (n + 1) + 2 * e + e) := by
        simp only [pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hX

/-! ### The prefix bits of the levels -/

/-- The prefix bits of `r` levels of width `w`: per level `1^w 0^{2w}` (`∃` is `1`). -/
def levelBits (w r : ℕ) : List Bool :=
  (List.range r).flatMap fun _ => List.replicate w true ++ List.replicate (2 * w) false

/-- The levels' quantifiers are written as `levelBits`. (Proved, by induction on `r`.) -/
theorem map_quantBit_levelQuants (w r : ℕ) :
    (levelQuants w r).map quantBit = levelBits w r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [levelQuants, List.map_append, List.map_replicate, ih, levelBits,
      List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [quantBit, two_mul, List.replicate_add, List.append_assoc]

/-- The one-pass map writing a `0` for every letter. -/
def zeroes (l : List Bool) : List Bool :=
  transduce (σ := Unit) (fun _ _ => ()) (fun _ _ => some false) () l

/-- `zeroes` writes `|l|` zeroes. -/
theorem zeroes_eq (l : List Bool) : zeroes l = List.replicate l.length false := by
  induction l with
  | nil => rfl
  | cons b l ih => simp only [zeroes, transduce] at ih ⊢; simp [ih, List.replicate_succ]

/-- The round of the level-bit loop: drop one letter of the countdown. -/
def lbStep (s : List Bool) : List Bool := pairEncode (pairFstD s) ((pairSndD s).drop 1)

/-- The chunk of the level-bit loop: `1^w 0^{2w}` while the countdown is nonempty. -/
def lbChunk (s : List Bool) : List Bool :=
  if pairSndD s = [] then [] else pairFstD s ++ (zeroes (pairFstD s) ++ zeroes (pairFstD s))

/-- The round does not lengthen a state beyond `max |s| 2`. -/
private theorem length_lbStep (s : List Bool) : (lbStep s).length ≤ max s.length 2 := by
  cases hd : pairDecode s with
  | none =>
    have hf : pairFstD s = [] := by simp [pairFstD, hd]
    have hs : pairSndD s = [] := by simp [pairSndD, hd]
    simp [lbStep, hf, hs, length_pairEncode]
  | some uv =>
    obtain ⟨u, v⟩ := uv
    have he := eq_pairEncode_of_pairDecode s u v hd
    subst he
    simp only [lbStep, pairFstD_pairEncode, pairSndD_pairEncode, length_pairEncode,
      List.length_drop]
    omega

/-- Iterates of the round on a pair drop from the countdown. -/
private theorem lbStep_iterate (u v : List Bool) (i : ℕ) :
    lbStep^[i] (pairEncode u v) = pairEncode u (v.drop i) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    simp [lbStep, List.drop_drop]

/-- **The prefix bits of the levels are polynomial-time**: for a polynomial-time unary width
`w x`, the word `levelBits (w x) (w x)` is polynomial-time computable.

**Proof sketch.** `Complexity.polyTimeComputable_of_loop` on the state `⟨1^w, 1^w⟩`: each
round emits `1^w 0^{2w}` while the countdown is nonempty and drops one countdown letter
(`lbStep`, `lbChunk`); states never grow beyond `max |s| 2`, and the round budget
`|init| + 2` exceeds `w`. -/
theorem polyTimeComputable_levelBits {w : List Bool → ℕ}
    (hw : PolyTimeComputable fun x => List.replicate (w x) true) :
    PolyTimeComputable fun x => levelBits (w x) (w x) := by
  have hstep : PolyTimeComputable lbStep :=
    polyTimeComputable_pairFstD.pairEncode
      (polyTimeComputable_tail.comp polyTimeComputable_pairSndD)
  have hz : PolyTimeComputable zeroes := polyTimeComputable_transduce _ _ _
  have hchunk : PolyTimeComputable lbChunk := by
    have hne := polyTimeComputable_isNil.comp polyTimeComputable_pairSndD
    have := polyTimeComputable_ite hne (polyTimeComputable_const [])
      (polyTimeComputable_pairFstD.append ((hz.comp polyTimeComputable_pairFstD).append
        (hz.comp polyTimeComputable_pairFstD)))
    convert this using 1
    funext s
    simp only [lbChunk, Function.comp]
    by_cases h : pairSndD s = [] <;> simp [h]
  have hinit : PolyTimeComputable fun x =>
      pairEncode (List.replicate (w x) true) (List.replicate (w x) true) := hw.pairEncode hw
  refine BlockLoop.polyTimeComputable_of_loop hstep hchunk hinit 1 1 2 (fun s i => ?_) (fun x => ?_)
  · have key : ∀ j, (lbStep^[j] s).length ≤ max s.length 2 := by
      intro j
      induction j with
      | zero => exact le_max_left _ _
      | succ j ih =>
        rw [Function.iterate_succ_apply']
        exact (length_lbStep _).trans (max_le ih (le_max_right _ _))
    have := key i
    simp only [pow_one]
    omega
  · simp only [lbStep_iterate, length_pairEncode, List.length_replicate, pow_one, one_mul]
    set m := w x
    have hcnt : 2 * m + 2 + m + 1 + 1 = m + (2 * m + 4) := by ring
    rw [hcnt, List.range_add, List.flatMap_append]
    have h2 : ((List.range (2 * m + 4)).map (m + ·)).flatMap
        (fun i => lbChunk (pairEncode (List.replicate m true)
          ((List.replicate m true).drop i))) = [] := by
      simp only [List.flatMap_eq_nil_iff, List.mem_map, List.mem_range]
      rintro _ ⟨j, _, rfl⟩
      simp [lbChunk, List.drop_eq_nil_of_le]
    rw [h2, List.append_nil, levelBits]
    apply List.flatMap_congr
    intro i hi
    rw [List.mem_range] at hi
    have hne : (List.replicate m true).drop i ≠ [] := by
      simp; omega
    simp only [lbChunk, pairSndD_pairEncode, pairFstD_pairEncode, hne, if_false, zeroes_eq,
      List.length_replicate, two_mul, List.replicate_add]

end TQBFHard

end Complexity
