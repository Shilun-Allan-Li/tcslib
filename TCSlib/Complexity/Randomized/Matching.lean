/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.MatchingMath
import TCSlib.Complexity.Randomized.Primality

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bipartite perfect matching is in `RP`

The class half of [AB09, §7.2.4]: Lovász's test is a polynomial-time verifier, so the
language of bipartite graphs with a perfect matching is in `RP`, hence in `BPP`, both in the
certificate form over `Randomized.polyTimeModel` and in the PTM form of [AB09, Def 7.2/7.6].
The probability analysis is `TCSlib.Complexity.Randomized.MatchingMath`; the arithmetic
(the prime, the determinant over `ZMod p`) is `TCSlib.Complexity.ClassP.BinaryArith`.

## Main definitions

* `Randomized.Matching.encodeBPM`, `Randomized.Matching.BipartitePerfectMatching` — the
  encoding `⟨1ⁿ, row-major n² adjacency bits⟩` and the language.
* `Randomized.Matching.matchingVerifier` — Lovász's test over `ZMod p`.
* `Randomized.Matching.lovaszRows`, `Randomized.Matching.lovaszRowW`,
  `Randomized.Matching.matchingTest` — its word-level implementation (building the matrix
  from blocks cut by `Complexity.BinArith.chunkW`, then `detModAlg`).

## Main results

* `Randomized.Matching.eff_matchingVerifier` — the verifier is polynomial-time.
* `Randomized.Matching.inRP_BipartitePerfectMatching`,
  `Randomized.Matching.inBPP_BipartitePerfectMatching` — certificate form.
* `Randomized.Matching.BipartitePerfectMatching_mem_RP_PTM`,
  `Randomized.Matching.BipartitePerfectMatching_mem_BPP_PTM` — PTM form.

## Divergences

* The graph is the `n × n` Boolean adjacency matrix with `n` in unary, as for `PATH`
  (`Complexity.encodePATH`); words that encode no graph are non-members.
* The determinant is evaluated over `ZMod p` for the least prime `p > 2^k`, `k = ⌈log₂ 2n⌉`
  (`Complexity.BinArith.lovaszPrime`), not over `ℤ`; each entry reads `k` fair coins
  (see `MatchingMath`). The verifier also rejects coin words shorter than `n²k`.
* One round has success probability `≥ 1/2`; membership in `RP` (threshold `2/3`) uses the
  error reduction of [AB09, Ex 7.4] (`Randomized.inRPWeak_iff_inRP`).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized.Matching

open Complexity Turing
open Complexity.LogProg (bitsVal bitsVal_bits)
open Complexity.BinArith (eqW eqW_pairEncode polyTimeComputable_eqW mulU length_mulU
  polyTimeComputable_mulU chunkW chunkList chunkW_pairEncode polyTimeComputable_chunkW
  lovaszBits lovaszBits_le two_mul_le_two_pow_lovaszBits)

variable {n : ℕ}

/-! ### The language -/

/-- The row-major adjacency word of `A`: `n²` bits, bit `i·n + j` is `A i j`. -/
def adjWord (A : Matrix (Fin n) (Fin n) Bool) : List Bool :=
  (List.finRange n).flatMap fun i => (List.finRange n).map (A i)

/-- The encoding of the bipartite graph of `A`: `⟨1ⁿ, adjWord A⟩`. -/
def encodeBPM (n : ℕ) (A : Matrix (Fin n) (Fin n) Bool) : List Bool :=
  pairEncode (List.replicate n true) (adjWord A)

/-- **Bipartite perfect matching** [AB09, §7.2.4]: the encodings of bipartite graphs with a
perfect matching. -/
def BipartitePerfectMatching : Language Bool :=
  {x | ∃ (n : ℕ) (A : Matrix (Fin n) (Fin n) Bool), x = encodeBPM n A ∧ HasPerfectMatching A}

/-- The matrix read off a word: entry `(i, j)` is bit `i·n + j`. -/
def adjOfWord (n : ℕ) (w : List Bool) : Matrix (Fin n) (Fin n) Bool :=
  Matrix.of fun i j => w.getD (i * n + j) false

/-- Reading a concatenation of `n`-bit rows at row `i`, column `j`.

**Proof sketch.** Induction on the list of rows: row `0` is the prefix of length `n`, and
row `i + 1` sits `n` bits further into the word than row `i` of the tail. -/
private theorem getD_adjWord (A : Matrix (Fin n) (Fin n) Bool) (i j : ℕ) (hi : i < n)
    (hj : j < n) : (adjWord A).getD (i * n + j) false = A ⟨i, hi⟩ ⟨j, hj⟩ := by
  unfold adjWord
  suffices h : ∀ (L : List (Fin n)) (i : ℕ) (hi : i < L.length),
      (L.flatMap fun i => (List.finRange n).map (A i)).getD (i * n + j) false = A L[i] ⟨j, hj⟩ by
    rw [h (List.finRange n) i (by simpa using hi)]
    simp
  intro L
  induction L with
  | nil => intro i hi; simp at hi
  | cons a L ih =>
    intro i hi
    rw [List.flatMap_cons]
    cases i with
    | zero =>
      rw [Nat.zero_mul, Nat.zero_add, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by simpa using hj), List.getElem?_map,
        List.getElem?_eq_getElem (by simpa using hj)]
      simp
    | succ i =>
      rw [show (i + 1) * n + j = n + (i * n + j) by rw [Nat.succ_mul]; omega,
        List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp),
        List.length_map, List.length_finRange, Nat.add_sub_cancel_left,
        ← List.getD_eq_getElem?_getD]
      exact ih i (by simpa using hi)

/-- `adjWord A` has `n²` bits. -/
theorem length_adjWord (A : Matrix (Fin n) (Fin n) Bool) : (adjWord A).length = n * n := by
  simp [adjWord, List.length_flatMap, List.sum_replicate]

/-- Decoding inverts encoding. -/
theorem adjOfWord_adjWord (A : Matrix (Fin n) (Fin n) Bool) : adjOfWord n (adjWord A) = A := by
  ext i j
  exact getD_adjWord A i j i.isLt j.isLt

/-- An `n²`-bit word is the adjacency word of the matrix it encodes. -/
theorem adjWord_adjOfWord {w : List Bool} (hw : w.length = n * n) :
    adjWord (adjOfWord n w) = w := by
  refine List.ext_getElem (by rw [length_adjWord, hw]) fun m h1 h2 => ?_
  have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp [hw] at h2)
  have hq : m / n < n := by rw [Nat.div_lt_iff_lt_mul hn]; omega
  have hm : m = m / n * n + m % n := (Nat.div_add_mod' m n).symm
  have e := getD_adjWord (adjOfWord n w) (m / n) (m % n) hq (Nat.mod_lt _ hn)
  rw [← hm, List.getD_eq_getElem _ _ h1] at e
  rw [e]
  simp [adjOfWord, ← hm, List.getElem?_eq_getElem h2]

/-- An encoded graph is in the language iff it has a perfect matching. -/
theorem encodeBPM_mem_iff (A : Matrix (Fin n) (Fin n) Bool) :
    encodeBPM n A ∈ BipartitePerfectMatching ↔ HasPerfectMatching A := by
  refine ⟨fun ⟨m, B, h, hB⟩ => ?_, fun h => ⟨n, A, rfl, h⟩⟩
  have hl := congrArg (fun x => (pairFstD x).length) h
  simp only [encodeBPM, pairFstD_pairEncode, List.length_replicate] at hl
  subst hl
  have hA := congrArg (fun x => adjOfWord n (pairSndD x)) h
  simp only [encodeBPM, pairSndD_pairEncode, adjOfWord_adjWord] at hA
  exact hA ▸ hB

/-! ### The verifier -/

/-- **Lovász's test** [AB09, §7.2.4] on `x = ⟨1ⁿ, A⟩` and coins `r`: check that `x` encodes a
graph and `|r| ≥ n²k`, then accept iff `det X ≠ 0` over `ZMod p` with entry `(i, j)` read off
block `n·i + j` of `k` coins, `k = lovaszBits n`, `p = lovaszPrime n`. -/
noncomputable def matchingVerifier (x r : List Bool) : Bool :=
  let n := (pairFstD x).length
  let A := adjOfWord n (pairSndD x)
  decide (x = encodeBPM n A) && decide (n * n * lovaszBits n ≤ r.length) &&
    decide ((lovaszMatrix A
      (lovaszSample (ZMod (BinArith.lovaszPrime n)) n (lovaszBits n) r)).det ≠ 0)

/-! ### Building the matrix -/

/-- An entry on `⟨q, ⟨a, b⟩⟩`: the value of the coin block `b` if the edge bit `a` is set,
else `0` (in binary). -/
def lovaszEntryW (S : List Bool) : List Bool :=
  if (pairFstD (pairSndD S)).headD false then Nat.bits (bitsVal (pairSndD (pairSndD S))) else []

/-- A row on `⟨K, ⟨a, c⟩⟩`: cut the edge bits `a` into single bits and the coins `c` into
`|K|`-bit blocks, and combine them entrywise. -/
def lovaszRowW (S : List Bool) : List Bool :=
  BinArith.zipWithW lovaszEntryW (pairEncode [] (pairEncode
    (chunkW (pairEncode [true] (pairFstD (pairSndD S))))
    (chunkW (pairEncode (pairFstD S) (pairSndD (pairSndD S))))))

/-- The rows of Lovász's matrix on edge bits `w` and coins `r`, as numbers. -/
def lovaszRows (n k : ℕ) (w r : List Bool) : List (List ℕ) :=
  (List.range n).map fun i => (List.range n).map fun j =>
    if w.getD (i * n + j) false then bitsVal ((r.drop ((n * i + j) * k)).take k) else 0

/-- **The matrix word**: on `⟨K, ⟨rows of w, rows of r⟩⟩` the row loop writes Lovász's
matrix (rows of `n` edge bits, rows of `n·|K|` coins).

**Proof sketch.** `chunkW_pairEncode` lists the `n` rows of `w` and of `r`; `zipWithW` pairs
them row by row. Inside row `i`, cutting again lists the edge bits `w[i·n + j]` and the coin
blocks, which are the `k`-bit blocks `n·i + j` of `r`; `lovaszEntryW` writes their value or `0`. -/
theorem zipWithW_lovaszRowW (K u w NK r : List Bool) (hw : w.length = u.length * u.length)
    (hNK : NK.length = u.length * K.length) (hr : r.length = u.length * NK.length)
    (hK : 0 < K.length ∨ u.length = 0) :
    BinArith.zipWithW lovaszRowW (pairEncode K (pairEncode (chunkW (pairEncode u w))
      (chunkW (pairEncode NK r)))) =
      BinArith.encMat (lovaszRows u.length K.length w r) := by
  set n := u.length
  set k := K.length
  rw [chunkW_pairEncode u w n hw (by omega), chunkW_pairEncode NK r n hr (by
    rcases hK with hK | hK
    · rcases Nat.eq_zero_or_pos n with h | h
      · exact Or.inr h
      · exact Or.inl (by rw [hNK]; positivity)
    · exact Or.inr hK), BinArith.zipWithW_pairEncode, BinArith.decWords_encWords,
    BinArith.decWords_encWords, chunkList, chunkList, List.zipWith_map, List.zipWith_self]
  simp only [BinArith.encMat, lovaszRows, List.map_map]
  refine congrArg BinArith.encWords ?_
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  have hrow : ((w.drop (i * n)).take n).length = n * [true].length := by
    simp [List.length_drop, hw]
    have : (i + 1) * n ≤ n * n := Nat.mul_le_mul_right _ hi
    rw [Nat.succ_mul] at this; omega
  have hcoin : ((r.drop (i * NK.length)).take NK.length).length = n * k := by
    simp [List.length_drop, hr, hNK]
    have : (i + 1) * (n * k) ≤ n * (n * k) := Nat.mul_le_mul_right _ hi
    rw [Nat.succ_mul] at this; omega
  simp only [Function.comp, lovaszRowW, pairFstD_pairEncode, pairSndD_pairEncode]
  rw [chunkW_pairEncode _ _ n hrow (Or.inl (by simp)), chunkW_pairEncode _ _ n (by rw [hcoin])
    (by omega), BinArith.zipWithW_pairEncode, BinArith.decWords_encWords,
    BinArith.decWords_encWords, chunkList, chunkList, List.zipWith_map, List.zipWith_self]
  simp only [BinArith.encRow, List.map_map]
  refine congrArg BinArith.encWords ?_
  refine List.map_congr_left fun j hj => ?_
  rw [List.mem_range] at hj
  simp only [Function.comp, lovaszEntryW, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_cons, List.length_nil, zero_add, mul_one]
  have hbit : (((w.drop (i * n)).take n).drop j).take 1 = [w.getD (i * n + j) false] := by
    have hlt : i * n + j < w.length := by
      rw [hw]; have : (i + 1) * n ≤ n * n := Nat.mul_le_mul_right _ hi
      rw [Nat.succ_mul] at this; omega
    rw [List.getD_eq_getElem _ _ hlt]
    simp only [List.drop_take, List.drop_drop]
    rw [List.take_take, show min 1 (n - j) = 1 by omega]
    exact List.take_one_drop_eq_of_lt_length hlt
  have hblk : (((r.drop (i * NK.length)).take NK.length).drop (j * k)).take k =
      (r.drop ((n * i + j) * k)).take k := by
    rw [List.drop_take, List.drop_drop, List.take_take, show min k (NK.length - j * k) = k by
      rw [hNK]; have : (j + 1) * k ≤ n * k := Nat.mul_le_mul_right _ hj
      rw [Nat.succ_mul] at this; omega, hNK]
    congr 2
    ring
  rw [hbit, hblk]
  cases w.getD (i * n + j) false <;> simp [Nat.zero_bits]

/-- The rows have the matrix of Lovász's test, over `ZMod p`. -/
theorem matOfRows_lovaszRows (p k : ℕ) (w r : List Bool) :
    BinArith.matOfRows p n (lovaszRows n k w r) =
      lovaszMatrix (adjOfWord n w) (lovaszSample (ZMod p) n k r) := by
  ext i j
  simp only [BinArith.matOfRows, lovaszRows, lovaszMatrix, lovaszSample, adjOfWord,
    Matrix.of_apply, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range i.isLt,
    List.getElem?_range j.isLt, Option.map_some, Option.getD_some]
  rw [blockVal, show ((finProdFinEquiv (i, j) : Fin (n * n)) : ℕ) = j + n * i from rfl,
    Nat.add_comm (j : ℕ)]
  split_ifs <;> simp

/-- The row-length hypothesis of `detModAlg_pairEncode` for `lovaszRows`. -/
theorem length_lovaszRows (k : ℕ) (w r : List Bool) :
    (lovaszRows n k w r).length = n ∧ ∀ row ∈ lovaszRows n k w r, row.length = n := by
  simp [lovaszRows]

/-! ### The word-level test -/

/-- The unary `n` of `z = ⟨⟨1ⁿ, w⟩, r⟩`. -/
private def tU (z : List Bool) : List Bool := pairFstD (pairFstD z)

/-- The edge bits `w` of `z = ⟨⟨1ⁿ, w⟩, r⟩`. -/
private def tW (z : List Bool) : List Bool := pairSndD (pairFstD z)

/-- A word of length `k = lovaszBits n` (the binary `2^k` of `dblLoop`, low bit dropped). -/
private def tK (z : List Bool) : List Bool := (pairFstD (BinArith.dblLoop (tU z))).drop 1

/-- A word of length `n·k`. -/
private def tNK (z : List Bool) : List Bool := mulU (pairEncode (tU z) (tK z))

/-- The first `n·n·k` coins. -/
private def tCoins (z : List Bool) : List Bool :=
  takePrefixByLen (pairEncode (mulU (pairEncode (tU z) (tNK z))) (pairSndD z))

/-- `det X mod p` in binary, for Lovász's matrix built from `w` and the coins. -/
private noncomputable def tDet (z : List Bool) : List Bool :=
  BinArith.detModAlg (pairEncode (Nat.bits (BinArith.lovaszPrime (tU z).length))
    (BinArith.zipWithW lovaszRowW (pairEncode (tK z) (pairEncode (chunkW (pairEncode (tU z) (tW z)))
      (chunkW (pairEncode (tNK z) (tCoins z)))))))

/-- The verifier on `z = ⟨x, r⟩`, assembled from polynomial-time pieces: the well-formedness
of `x`, the coin count, and the nonzero test of the determinant. -/
noncomputable def matchingTest (z : List Bool) : Bool :=
  (eqW (pairEncode (pairFstD z) (pairEncode (List.replicate (tU z).length true) (tW z))) &&
    decide ((mulU (pairEncode (tU z) (tU z))).length = (tW z).length)) &&
  decide ((mulU (pairEncode (tU z) (tNK z))).length ≤ (pairSndD z).length) &&
  !decide (bitsVal (tDet z) = 0)

/-- `x` encodes a graph iff it is `⟨1ⁿ, w⟩` with `|w| = n²`. -/
theorem eq_encodeBPM_iff (x : List Bool) :
    x = encodeBPM (pairFstD x).length (adjOfWord (pairFstD x).length (pairSndD x)) ↔
      x = pairEncode (List.replicate (pairFstD x).length true) (pairSndD x) ∧
        (pairFstD x).length * (pairFstD x).length = (pairSndD x).length := by
  constructor
  · intro h
    have hw : pairSndD x = adjWord (adjOfWord (pairFstD x).length (pairSndD x)) := by
      conv_lhs => rw [h]
      simp [encodeBPM]
    refine ⟨?_, ?_⟩
    · conv_lhs => rw [h]
      rw [encodeBPM, ← hw]
    · rw [hw, length_adjWord]
  · rintro ⟨h1, h2⟩
    rw [encodeBPM, adjWord_adjOfWord h2.symm]
    exact h1

/-- The implementation computes the verifier.

**Proof sketch.** The first two tests decide `x = ⟨1ⁿ, w⟩ ∧ |w| = n²`, i.e. that `x` encodes
`adjOfWord n w` (`eq_encodeBPM_iff`); the third is the coin count. Under both, the row loop
writes `lovaszRows` (`zipWithW_lovaszRowW`, with blocks of `n`, `n·k`, `1` and `k` bits),
`detModAlg_pairEncode` returns `(det M).val` for the prime `p`, `M` is Lovász's matrix on the
first `n²k` coins (`matOfRows_lovaszRows`), and those are all the coins it reads
(`lovaszSample_take`). -/
theorem matchingTest_pairEncode (x r : List Bool) :
    matchingTest (pairEncode x r) = matchingVerifier x r := by
  set n := (pairFstD x).length with hn
  set w := pairSndD x with hw
  set k := lovaszBits n with hk
  have hU : tU (pairEncode x r) = pairFstD x := by simp [tU]
  have hW : tW (pairEncode x r) = w := by simp [tW, hw]
  have hK : (tK (pairEncode x r)).length = k := by
    simp [tK, hU, BinArith.dblLoop_spec, hk, lovaszBits, hn]
  have hNK : (tNK (pairEncode x r)).length = n * k := by simp [tNK, length_mulU, hK, hU, hn]
  have hwf : (eqW (pairEncode (pairFstD (pairEncode x r)) (pairEncode
      (List.replicate (tU (pairEncode x r)).length true) (tW (pairEncode x r)))) &&
      decide ((mulU (pairEncode (tU (pairEncode x r)) (tU (pairEncode x r)))).length =
        (tW (pairEncode x r)).length)) = decide (x = encodeBPM n (adjOfWord n w)) := by
    rw [eqW_pairEncode, length_mulU, hU, hW, pairFstD_pairEncode, Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact (eq_encodeBPM_iff x).symm
  have hlen : decide ((mulU (pairEncode (tU (pairEncode x r)) (tNK (pairEncode x r)))).length ≤
      (pairSndD (pairEncode x r)).length) = decide (n * n * k ≤ r.length) := by
    rw [length_mulU, hNK, hU, ← hn, pairSndD_pairEncode, Nat.mul_assoc]
  unfold matchingTest
  rw [hwf, hlen]
  show _ = (decide (x = encodeBPM n (adjOfWord n w)) && decide (n * n * k ≤ r.length) &&
    decide ((lovaszMatrix (adjOfWord n w)
      (lovaszSample (ZMod (BinArith.lovaszPrime n)) n k r)).det ≠ 0))
  by_cases h1 : x = encodeBPM n (adjOfWord n w)
  · by_cases h2 : n * n * k ≤ r.length
    · have hwn : w.length = n * n := ((eq_encodeBPM_iff x).1 h1).2.symm
      haveI : Fact (BinArith.lovaszPrime n).Prime := ⟨BinArith.lovaszPrime_prime n⟩
      have hC : tCoins (pairEncode x r) = r.take (n * (n * k)) := by
        simp [tCoins, takePrefixByLen, length_mulU, hNK, hU, hn]
      have hrows := zipWithW_lovaszRowW (tK (pairEncode x r)) (pairFstD x) w (tNK (pairEncode x r))
        (r.take (n * (n * k))) hwn (by rw [hNK, hK]) (by
          rw [List.length_take, hNK, ← hn, min_eq_left (by rw [← Nat.mul_assoc]; exact h2)])
        (by
          rcases Nat.eq_zero_or_pos n with h | h
          · exact Or.inr h
          · exact Or.inl (by rw [hK]; exact Nat.clog_pos one_lt_two (by omega)))
      rw [← hn, hK] at hrows
      obtain ⟨hl, hsq⟩ := length_lovaszRows (n := n) k w (r.take (n * (n * k)))
      have hdet : tDet (pairEncode x r) = Nat.bits (lovaszMatrix (adjOfWord n w)
          (lovaszSample (ZMod (BinArith.lovaszPrime n)) n k r)).det.val := by
        rw [tDet, hC, hU, hW, hrows, BinArith.detModAlg_pairEncode _ _ (by rw [hl]; exact hsq),
          hl, matOfRows_lovaszRows, lovaszSample_take _ n k (by rw [Nat.mul_assoc])]
      rw [hdet, bitsVal_bits, decide_eq_true h1, decide_eq_true h2]
      simp [ZMod.val_eq_zero]
    · rw [decide_eq_false h2]
      simp
  · rw [decide_eq_false h1]
    simp

/-- The implementation is polynomial-time.

**Proof sketch.** Every piece is a composition of the closure kit: projections, `dblLoop`,
unary multiplication and cutting (counted loops, `Complexity.BinArith.forLoop`), the prefix
operations, the loops `zipWithW`, the prime finder, `detModAlg`, the zero test and the length
tests. -/
theorem polyTimeComputable_matchingTest : PolyTimeComputable (fun z => [matchingTest z]) := by
  have hU : PolyTimeComputable tU := polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD
  have hW : PolyTimeComputable tW := polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD
  have hK : PolyTimeComputable tK := by
    unfold tK
    have h := polyTimeComputable_tail.comp
      (polyTimeComputable_pairFstD.comp (BinArith.polyTimeComputable_dblLoop.comp hU))
    simp only [Function.comp_def] at h
    exact h
  have hNK : PolyTimeComputable tNK := by
    unfold tNK
    have h := polyTimeComputable_mulU.comp (hU.pairEncode hK)
    simp only [Function.comp_def] at h
    exact h
  have hC : PolyTimeComputable tCoins := by
    unfold tCoins
    have h := polyTimeComputable_takePrefixByLen.comp
      ((polyTimeComputable_mulU.comp (hU.pairEncode hNK)).pairEncode polyTimeComputable_pairSndD)
    simp only [Function.comp_def] at h
    exact h
  have hE : PolyTimeComputable lovaszEntryW := by
    unfold lovaszEntryW
    exact polyTimeComputable_ite (polyTimeComputable_headD.comp BinArith.polyTimeComputable_slot2)
      (BinArith.polyTimeComputable_normBits.comp BinArith.polyTimeComputable_slot3)
      (polyTimeComputable_const [])
  have hR : PolyTimeComputable lovaszRowW := by
    unfold lovaszRowW
    have h := (BinArith.polyTimeComputable_zipWithW hE).comp
      ((polyTimeComputable_const []).pairEncode ((polyTimeComputable_chunkW.comp
        ((polyTimeComputable_const [true]).pairEncode BinArith.polyTimeComputable_slot2)).pairEncode
        (polyTimeComputable_chunkW.comp (polyTimeComputable_pairFstD.pairEncode
          BinArith.polyTimeComputable_slot3))))
    simp only [Function.comp_def] at h
    exact h
  have hD : PolyTimeComputable tDet := by
    unfold tDet
    have h := BinArith.polyTimeComputable_detModAlg.comp
      ((BinArith.polyTimeComputable_lovaszPrime.comp hU).pairEncode
        ((BinArith.polyTimeComputable_zipWithW hR).comp (hK.pairEncode
          ((polyTimeComputable_chunkW.comp (hU.pairEncode hW)).pairEncode
            (polyTimeComputable_chunkW.comp (hNK.pairEncode hC))))))
    simp only [Function.comp_def] at h
    exact h
  have p1 : PolyTimeComputable (fun z => [eqW (pairEncode (pairFstD z)
      (pairEncode (List.replicate (tU z).length true) (tW z)))]) := by
    have h := polyTimeComputable_eqW.comp (polyTimeComputable_pairFstD.pairEncode
      ((polyTimeComputable_unary.comp hU).pairEncode hW))
    simp only [Function.comp_def] at h
    exact h
  have p2 : PolyTimeComputable (fun z =>
      [decide ((mulU (pairEncode (tU z) (tU z))).length = (tW z).length)]) := by
    have h := polyTimeComputable_lenEq.comp
      ((polyTimeComputable_mulU.comp (hU.pairEncode hU)).pairEncode hW)
    simp only [Function.comp_def, pairFstD_pairEncode, pairSndD_pairEncode] at h
    exact h
  have p3 : PolyTimeComputable (fun z =>
      [decide ((mulU (pairEncode (tU z) (tNK z))).length ≤ (pairSndD z).length)]) := by
    have h := polyTimeComputable_lenLe.comp (polyTimeComputable_pairSndD.pairEncode
      (polyTimeComputable_mulU.comp (hU.pairEncode hNK)))
    simp only [Function.comp_def, pairFstD_pairEncode, pairSndD_pairEncode] at h
    exact h
  have p4 : PolyTimeComputable (fun z => [!decide (bitsVal (tDet z) = 0)]) := by
    have h := polyTimeComputable_not (BinArith.polyTimeComputable_isZero.comp hD)
    exact h
  have h := polyTimeComputable_and (polyTimeComputable_and (polyTimeComputable_and p1 p2) p3) p4
  exact h

/-- **Lovász's verifier is polynomial-time.** [AB09, §7.2.4] -/
theorem eff_matchingVerifier : polyTimeModel.Eff (boolVerifier matchingVerifier) :=
  eff_boolVerifier_of_test polyTimeComputable_matchingTest matchingTest_pairEncode

/-! ### `BipartitePerfectMatching ∈ RP` -/

/-- On an encoded graph the verifier is Lovász's test, given enough coins. -/
theorem matchingVerifier_encodeBPM (A : Matrix (Fin n) (Fin n) Bool) (r : List Bool) :
    matchingVerifier (encodeBPM n A) r = (decide (n * n * lovaszBits n ≤ r.length) &&
      decide ((lovaszMatrix A
        (lovaszSample (ZMod (BinArith.lovaszPrime n)) n (lovaszBits n) r)).det ≠ 0)) := by
  unfold matchingVerifier
  dsimp only
  generalize hm : (pairFstD (encodeBPM n A)).length = m
  have hmn : m = n := by rw [← hm]; simp [encodeBPM]
  subst hmn
  simp [encodeBPM, adjOfWord_adjWord]

/-- **`BipartitePerfectMatching ∈ RP`**, certificate form. [AB09, §7.2.4]

**Proof sketch.** Coin words of length `(|x|+1)³ ≥ n²k`. On an encoded graph with a perfect
matching the verifier is Lovász's test (`matchingVerifier_encodeBPM`), which accepts with
probability `≥ 1/2` (`lovasz_test_zmod`, `2n ≤ 2^k < p`); since `|x| ≥ 2`, this meets the
weak threshold `min (2/3) (|x|+1)⁻¹` of [AB09, Ex 7.4] (`inRPWeak_iff_inRP`). On a
non-member the verifier rejects malformed words, and on a graph without a perfect matching
every determinant vanishes (`det_lovaszMatrix_eq_zero`). -/
theorem inRP_BipartitePerfectMatching : InRP polyTimeModel BipartitePerfectMatching := by
  refine (inRPWeak_iff_inRP polyTimeModel polyTimeModel_closedUnderAny 1 _).1
    ⟨matchingVerifier, 1, 3, eff_matchingVerifier, fun x => ⟨fun hx => ?_, fun hx r => ?_⟩⟩
  · obtain ⟨n, A, rfl, hA⟩ := hx
    have hx : (encodeBPM n A).length = 2 * n + 2 + n * n := by
      simp [encodeBPM, length_pairEncode, length_adjWord]
    have hm : n * n * lovaszBits n ≤ polyLen 1 3 (encodeBPM n A).length := by
      have hk := lovaszBits_le n
      set M := n * n + 2 * n + 3
      have h1 : n * n ≤ M := by omega
      have h2 : lovaszBits n ≤ M := by omega
      have h3 : 1 ≤ M := by omega
      calc n * n * lovaszBits n ≤ M * M * M :=
            Nat.mul_le_mul (h1.trans (Nat.le_mul_of_pos_right _ h3)) h2
        _ = polyLen 1 3 (encodeBPM n A).length := by
            simp only [polyLen, hx, M]; ring
    haveI : Fact (BinArith.lovaszPrime n).Prime := ⟨BinArith.lovaszPrime_prime n⟩
    have hT := lovasz_test_zmod A hA (two_mul_le_two_pow_lovaszBits n)
      (BinArith.two_pow_lt_lovaszPrime n).le hm
    rw [randProb_congr (B := fun l => (lovaszMatrix A (lovaszSample
        (ZMod (BinArith.lovaszPrime n)) n (lovaszBits n) l)).det ≠ 0) fun r => by
      rw [matchingVerifier_encodeBPM, List.length_ofFn, decide_eq_true hm, Bool.true_and,
        decide_eq_true_iff]]
    refine le_trans ?_ hT
    refine min_le_of_right_le ?_
    have h3 : (3 : ℚ) ≤ (encodeBPM n A).length + 1 := by
      rw [hx]; push_cast; nlinarith
    rw [pow_one]
    calc (((encodeBPM n A).length : ℚ) + 1)⁻¹ ≤ 3⁻¹ := inv_anti₀ (by norm_num) h3
      _ ≤ 1 / 2 := by norm_num
  · unfold matchingVerifier
    dsimp only
    by_cases hw : x = encodeBPM (pairFstD x).length
        (adjOfWord (pairFstD x).length (pairSndD x))
    · have hnot : ¬ HasPerfectMatching (adjOfWord (pairFstD x).length (pairSndD x)) :=
        fun h => hx ⟨_, _, hw, h⟩
      simp [det_lovaszMatrix_eq_zero _ hnot]
    · simp [hw]

/-- **`BipartitePerfectMatching ∈ BPP`**, certificate form. [AB09, §7.2.4] -/
theorem inBPP_BipartitePerfectMatching : InBPP polyTimeModel BipartitePerfectMatching :=
  inRP_BipartitePerfectMatching.inBPP

/-- **`BipartitePerfectMatching ∈ RP`**, PTM form. [AB09, §7.2.4] -/
theorem BipartitePerfectMatching_mem_RP_PTM : BipartitePerfectMatching ∈ RP_PTM :=
  (mem_RP_PTM_iff _).2 inRP_BipartitePerfectMatching

/-- **`BipartitePerfectMatching ∈ BPP`**, PTM form. [AB09, §7.2.4] -/
theorem BipartitePerfectMatching_mem_BPP_PTM : BipartitePerfectMatching ∈ BPP_PTM :=
  RP_PTM_subset_BPP_PTM BipartitePerfectMatching_mem_RP_PTM

end Randomized.Matching
