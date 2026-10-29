/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.ClassP.BinaryArith.Iterate
import TCSlib.Complexity.ClassNP.Transducer
import TCSlib.Complexity.SpaceComplexity.Machines.Bin

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Binary words in polynomial time: normalization and bit-serial scans

Infrastructure for [AB09 §7.2]; not itself a result of the book. Numbers are the
little-endian words `Nat.bits n`, read back by `Complexity.LogProg.bitsVal`, which accepts
every word (trailing zeros allowed). This file provides the word-level tools the arithmetic
of `TCSlib.Complexity.ClassP.BinaryArith` is assembled from.

## Main definitions

* `Complexity.BinArith.padZip` — the bit pairs of two words, padded with zeros.
* `Complexity.BinArith.serialOut`, `Complexity.BinArith.serialState` — the output and the
  final state of a finite-state scan over bit pairs (a carry or borrow chain).

## Main results

* `Complexity.BinArith.polyTimeComputable_normBits` — `w ↦ Nat.bits (bitsVal w)`
  (dropping trailing zeros) is polynomial-time.
* `Complexity.BinArith.polyTimeComputable_lastBit` — the last bit of a word.
* `Complexity.BinArith.polyTimeComputable_serial` — a finite-state scan over the
  `|z| + 2` zero-padded bit pairs of the components of `z` is polynomial-time.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.2.)
-/

namespace Complexity

namespace BinArith

open Turing LogProg

/-! ### Values of words -/

/-- The value of a word is its head bit plus twice the value of its tail (any word). -/
theorem bitsVal_eq_headD (w : List Bool) :
    bitsVal w = (w.headD false).toNat + 2 * bitsVal (w.drop 1) := by
  cases w <;> simp [bitsVal]

/-- Appending a top bit `b` to `w` adds `b · 2^|w|`. -/
theorem bitsVal_append_singleton (w : List Bool) (b : Bool) :
    bitsVal (w ++ [b]) = bitsVal w + b.toNat * 2 ^ w.length := by
  induction w with
  | nil => simp [bitsVal]
  | cons c w ih => simp only [List.cons_append, bitsVal, ih, List.length_cons, pow_succ]; ring

/-- A word has value `0` exactly when it has no `1`. -/
theorem bitsVal_eq_zero_iff (w : List Bool) : bitsVal w = 0 ↔ w.any id = false := by
  induction w with
  | nil => simp [bitsVal]
  | cons b w ih => cases b <;> simp [bitsVal, ih]

/-- The normalized word of a value fits in any word of that value: `|bits (bitsVal w)| ≤ |w|`. -/
theorem length_bits_bitsVal_le (w : List Bool) : (Nat.bits (bitsVal w)).length ≤ w.length :=
  length_bits_le (bitsVal_lt_two_pow w)

/-- If `n ≤ bitsVal w` and `|w| ≤ m`, then `Nat.bits n` has at most `m` letters. -/
theorem length_bits_le_of_le {n m : ℕ} (w : List Bool) (h : n ≤ bitsVal w) (hw : w.length ≤ m) :
    (Nat.bits n).length ≤ m :=
  (length_bits_mono h).trans ((length_bits_bitsVal_le w).trans hw)

/-! ### Small word maps -/

/-- Iterating `drop 1` drops a prefix. -/
theorem iterate_drop_one (w : List Bool) (i : ℕ) :
    (fun v : List Bool => v.drop 1)^[i] w = w.drop i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', ih, List.drop_drop]

/-- The one-bit test "`w` contains a `1`" is polynomial-time (a one-state filter transducer
followed by the emptiness test). -/
theorem polyTimeComputable_any : PolyTimeComputable (fun w : List Bool => [w.any id]) := by
  have ht := polyTimeComputable_transduce (σ := Unit) (fun _ _ => ())
    (fun _ b => if b then some true else none) ()
  have hnil : ∀ w : List Bool, (transduce (fun _ _ => ()) (fun _ b => if b then some true
      else none) () w = []) ↔ w.any id = false := by
    intro w
    induction w with
    | nil => simp [transduce]
    | cons b w ih => cases b <;> simp [transduce, ih]
  convert polyTimeComputable_not (polyTimeComputable_isNil.comp ht) using 1
  funext w
  simp only [List.cons.injEq, and_true]
  cases h : w.any id <;> simp_all

/-- The chunk of the normalization loop: the head bit, if a `1` is still to come. -/
private def normChunk (w : List Bool) : List Bool := if w.any id then w.take 1 else []

/-- The normalization loop over all suffixes outputs the normalized word.

**Proof sketch.** Induction on `w`: the first round emits the head bit exactly when a `1` is
still to come, and the remaining rounds output the normalized tail
(`Complexity.LogProg.bits_two_mul_add`). -/
private theorem flatMap_normChunk (w : List Bool) :
    ∀ N, w.length ≤ N →
      (List.range N).flatMap (fun i => normChunk (w.drop i)) = Nat.bits (bitsVal w) := by
  induction w with
  | nil =>
    intro N _
    simp [normChunk, bitsVal, Nat.zero_bits]
  | cons b w ih =>
    intro N hN
    obtain ⟨N, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by simp at hN; omega⟩
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [List.drop_zero, Nat.succ_eq_add_one, List.drop_succ_cons]
    rw [ih N (by simpa using hN)]
    cases hb : (b :: w).any id
    · have h0 : bitsVal (b :: w) = 0 := (bitsVal_eq_zero_iff _).mpr hb
      have hw : bitsVal w = 0 := by simp only [bitsVal] at h0; omega
      simp [normChunk, hb, h0, hw, Nat.zero_bits]
    · have hb' : bitsVal w = 0 → b = true := by
        intro h0
        have := (bitsVal_eq_zero_iff w).mp h0
        simpa [this] using hb
      simp only [normChunk, hb, if_true, List.take_succ_cons, List.take_zero, List.singleton_append]
      rw [show bitsVal (b :: w) = 2 * bitsVal w + b.toNat by simp [bitsVal]; ring,
        bits_two_mul_add _ _ hb']

/-- **Normalization is polynomial-time**: `w ↦ Nat.bits (bitsVal w)` (drop the trailing
zeros) is polynomial-time, by the emit loop over the suffixes of `w`. -/
theorem polyTimeComputable_normBits :
    PolyTimeComputable (fun w => Nat.bits (bitsVal w)) := by
  have he : PolyTimeComputable normChunk :=
    polyTimeComputable_ite polyTimeComputable_any polyTimeComputable_take1
      (polyTimeComputable_const [])
  have h := polyTimeComputable_emitIter polyTimeComputable_tail he 1 1 1 1 (fun w i => by
    rw [iterate_drop_one, List.length_drop]; simp; omega)
  convert h using 1
  funext w
  simp only [iterate_drop_one]
  exact (flatMap_normChunk w _ (by simp; omega)).symm

/-- The chunk of the last-bit loop: the head bit of a one-letter suffix. -/
private def lastChunk (w : List Bool) : List Bool := if w.drop 1 = [] then w.take 1 else []

/-- The last-bit loop over all suffixes outputs the last bit, if any. -/
private theorem flatMap_lastChunk (w : List Bool) :
    ∀ N, w.length ≤ N →
      (List.range N).flatMap (fun i => lastChunk (w.drop i)) = w.getLast?.toList := by
  induction w with
  | nil => intro N _; simp [lastChunk]
  | cons b w ih =>
    intro N hN
    obtain ⟨N, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by simp at hN; omega⟩
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [List.drop_zero, Nat.succ_eq_add_one, List.drop_succ_cons]
    rw [ih N (by simpa using hN)]
    cases w with
    | nil => simp [lastChunk]
    | cons c w => simp [lastChunk]

/-- **The last bit is polynomial-time**: `w ↦ [w.getLastD false]`. -/
theorem polyTimeComputable_lastBit :
    PolyTimeComputable (fun w : List Bool => [w.getLastD false]) := by
  have hnil : PolyTimeComputable (fun w : List Bool => [decide (w.drop 1 = [])]) :=
    polyTimeComputable_isNil.comp polyTimeComputable_tail
  have he : PolyTimeComputable lastChunk := by
    convert polyTimeComputable_ite hnil polyTimeComputable_take1 (polyTimeComputable_const [])
      using 1
    funext w
    simp [lastChunk]
  have h := polyTimeComputable_emitIter polyTimeComputable_tail he 1 1 1 1 (fun w i => by
    rw [iterate_drop_one, List.length_drop]; simp; omega)
  convert polyTimeComputable_headD.comp h using 1
  funext w
  simp only [Function.comp_apply, iterate_drop_one]
  rw [flatMap_lastChunk w _ (by simp; omega)]
  rcases h : w.getLast? with _ | v <;> simp [h]

/-! ### Slots, bits and Boolean helpers -/

/-- The second slot `B` of a state `⟨A, ⟨B, C⟩⟩` is polynomial-time. -/
theorem polyTimeComputable_slot2 : PolyTimeComputable (fun S => pairFstD (pairSndD S)) :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD

/-- The third slot `C` of a state `⟨A, ⟨B, C⟩⟩` is polynomial-time. -/
theorem polyTimeComputable_slot3 : PolyTimeComputable (fun S => pairSndD (pairSndD S)) :=
  polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD

/-- Prepending a computed bit to a computed word is polynomial-time. -/
theorem polyTimeComputable_cons {p : List Bool → Bool} {f : List Bool → List Bool}
    (hp : PolyTimeComputable (fun x => [p x])) (hf : PolyTimeComputable f) :
    PolyTimeComputable (fun x => p x :: f x) :=
  hp.append hf

/-- The fourth slot `q` of a state `⟨b, ⟨R, ⟨r, q⟩⟩⟩` is polynomial-time. -/
theorem polyTimeComputable_slot4 :
    PolyTimeComputable (fun S => pairSndD (pairSndD (pairSndD S))) :=
  polyTimeComputable_pairSndD.comp polyTimeComputable_slot3

/-- Exclusive or of two one-bit tests is polynomial-time. -/
theorem polyTimeComputable_xor {p q : List Bool → Bool}
    (hp : PolyTimeComputable (fun x => [p x])) (hq : PolyTimeComputable (fun x => [q x])) :
    PolyTimeComputable (fun x => [p x ^^ q x]) := by
  convert polyTimeComputable_ite hp (polyTimeComputable_not hq) hq using 1
  funext x
  cases p x <;> simp

/-- Dropping a fixed number of leading bits is polynomial-time. -/
theorem polyTimeComputable_drop (i : ℕ) : PolyTimeComputable (fun w : List Bool => w.drop i) := by
  induction i with
  | zero => exact polyTimeComputable_id
  | succ i ih =>
    convert polyTimeComputable_tail.comp ih using 1
    funext w
    simp

/-- Dropping the low bit halves the value. -/
theorem bitsVal_drop_one (w : List Bool) : bitsVal (w.drop 1) = bitsVal w / 2 := by
  have := bitsVal_eq_headD w; have := Bool.toNat_le (w.headD false); omega

/-- The parity of a word's value is its low bit. -/
theorem bitsVal_mod_two (w : List Bool) : bitsVal w % 2 = (w.headD false).toNat := by
  have := bitsVal_eq_headD w; have := Bool.toNat_le (w.headD false); omega

/-! ### Bit pairs and finite-state scans -/

/-- The first `N` bit pairs of `a` and `b`, each padded with zeros. -/
def padZip : List Bool → List Bool → ℕ → List (Bool × Bool)
  | _, _, 0 => []
  | a, b, N + 1 => (a.headD false, b.headD false) :: padZip (a.drop 1) (b.drop 1) N

/-- `padZip a b N` has `N` pairs. -/
@[simp] theorem length_padZip (a b : List Bool) (N : ℕ) : (padZip a b N).length = N := by
  induction N generalizing a b with
  | zero => rfl
  | succ N ih => simp [padZip, ih]

/-- The output of a finite-state scan over bit pairs: in state `s`, the pair `(x, y)` emits
`o s x y` and moves to `δ s x y`. -/
def serialOut {σ : Type} (δ : σ → Bool → Bool → σ) (o : σ → Bool → Bool → Bool) :
    σ → List (Bool × Bool) → List Bool
  | _, [] => []
  | s, p :: ps => o s p.1 p.2 :: serialOut δ o (δ s p.1 p.2) ps

/-- The final state of a finite-state scan over bit pairs. -/
def serialState {σ : Type} (δ : σ → Bool → Bool → σ) : σ → List (Bool × Bool) → σ
  | s, [] => s
  | s, p :: ps => serialState δ (δ s p.1 p.2) ps

/-- A scan emits one bit per pair. -/
@[simp] theorem length_serialOut {σ : Type} (δ : σ → Bool → Bool → σ)
    (o : σ → Bool → Bool → Bool) (s : σ) (ps : List (Bool × Bool)) :
    (serialOut δ o s ps).length = ps.length := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih => simp [serialOut, ih]

/-- When a scan emits its new state, its last output bit is its final state. -/
theorem getLastD_serialOut_self (δ : Bool → Bool → Bool → Bool) (s : Bool)
    (ps : List (Bool × Bool)) (hps : ps ≠ []) :
    (serialOut δ δ s ps).getLastD false = serialState δ s ps := by
  induction ps generalizing s with
  | nil => exact absurd rfl hps
  | cons p ps ih =>
    cases ps with
    | nil => simp [serialOut, serialState]
    | cons q qs =>
      have := ih (δ s p.1 p.2) (List.cons_ne_nil _ _)
      simp only [serialOut, serialState] at this ⊢
      simpa using this

/-- The transition of the bit-level transducer running a scan over pairs: the first bit of a
pair is buffered, the second one fires the scan's transition. -/
def pairδ {σ : Type} (δ : σ → Bool → Bool → σ) : Option Bool × σ → Bool → Option Bool × σ
  | (none, s), x => (some x, s)
  | (some x, s), y => (none, δ s x y)

/-- The emission of the bit-level transducer running a scan over pairs. -/
def pairO {σ : Type} (o : σ → Bool → Bool → Bool) : Option Bool × σ → Bool → Option Bool
  | (none, _), _ => none
  | (some x, s), y => some (o s x y)

/-- The bit-level transducer on the flattened pairs is the scan. -/
theorem transduce_pairs {σ : Type} (δ : σ → Bool → Bool → σ) (o : σ → Bool → Bool → Bool)
    (s : σ) (ps : List (Bool × Bool)) :
    transduce (pairδ δ) (pairO o) (none, s) (ps.flatMap fun p => [p.1, p.2]) =
      serialOut δ o s ps := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih => simp [transduce, pairδ, pairO, serialOut, ih]

/-- The emitted pairs of the zip loop over `N` rounds are the flattened padded pairs. -/
private theorem flatMap_zipChunk (a b : List Bool) (N : ℕ) :
    (List.range N).flatMap (fun i => [(a.drop i).headD false, (b.drop i).headD false]) =
      (padZip a b N).flatMap (fun p => [p.1, p.2]) := by
  induction N generalizing a b with
  | zero => rfl
  | succ N ih =>
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, padZip, List.flatMap_cons]
    simp only [List.drop_zero, Nat.succ_eq_add_one]
    rw [← ih (a.drop 1) (b.drop 1)]
    simp

/-- The round of the zip loop: drop the head of both components. -/
private def zipStep (w : List Bool) : List Bool :=
  pairEncode ((pairFstD w).drop 1) ((pairSndD w).drop 1)

/-- The iterates of the zip loop: after `i + 1` rounds both components lost `i + 1` bits. -/
private theorem iterate_zipStep (w : List Bool) (i : ℕ) :
    zipStep^[i + 1] w = pairEncode ((pairFstD w).drop (i + 1)) ((pairSndD w).drop (i + 1)) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    simp [zipStep]

/-- The flattened zero-padded bit pairs of the two components of `z`, `|z| + 2` pairs long,
are polynomial-time (an emit loop dropping one bit of each component per round).

**Proof sketch.** After `i` rounds the state is `⟨a.drop i, b.drop i⟩`, never longer than
`|z| + 2`, and round `i` emits the two `i`-th bits (`flatMap_zipChunk`). -/
theorem polyTimeComputable_zipStream :
    PolyTimeComputable (fun z => (padZip (pairFstD z) (pairSndD z) (z.length + 2)).flatMap
      (fun p => [p.1, p.2])) := by
  have hg : PolyTimeComputable zipStep :=
    (polyTimeComputable_tail.comp polyTimeComputable_pairFstD).pairEncode
      (polyTimeComputable_tail.comp polyTimeComputable_pairSndD)
  have he : PolyTimeComputable
      (fun w => [(pairFstD w).headD false] ++ [(pairSndD w).headD false]) :=
    (polyTimeComputable_headD.comp polyTimeComputable_pairFstD).append
      (polyTimeComputable_headD.comp polyTimeComputable_pairSndD)
  have h := polyTimeComputable_emitIter hg he 1 1 2 1 (fun w i => by
    cases i with
    | zero => simp; omega
    | succ i =>
      rw [iterate_zipStep, length_pairEncode, List.length_drop, List.length_drop]
      have := length_pair_components_le w
      simp; omega)
  convert h using 1
  funext z
  rw [← flatMap_zipChunk]
  simp only [one_mul, pow_one, Nat.add_assoc, Nat.reduceAdd]
  refine List.flatMap_congr (fun i _ => ?_)
  cases i with
  | zero => simp
  | succ i => rw [iterate_zipStep]; simp

/-- **Finite-state scans are polynomial-time**: the scan `(δ, o)` from state `s` over the
`|z| + 2` zero-padded bit pairs of the components of `z` (the transducer `pairδ`/`pairO`
after the zip loop). -/
theorem polyTimeComputable_serial {σ : Type} [Fintype σ] [DecidableEq σ]
    (δ : σ → Bool → Bool → σ) (o : σ → Bool → Bool → Bool) (s : σ) :
    PolyTimeComputable
      (fun z => serialOut δ o s (padZip (pairFstD z) (pairSndD z) (z.length + 2))) := by
  convert (polyTimeComputable_transduce (pairδ δ) (pairO o) (none, s)).comp
    polyTimeComputable_zipStream using 1
  funext z
  simp only [Function.comp_apply, transduce_pairs]

end BinArith

end Complexity
