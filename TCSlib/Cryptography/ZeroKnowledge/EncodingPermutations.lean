/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.EncodingMachines
import TCSlib.Cryptography.Asymptotic.Permutations

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Numeric models of the permutation decoder and of the permutation sampler

The second half of the machine infrastructure behind the polynomial-time statements of
`TCSlib/Cryptography/ZeroKnowledge/Encoding.lean` (Inf-4.2). The decoder `decPerm` of an
encoded permutation and the rejection-sampled Fisher–Yates permutation `permFromCoins` of
`Asymptotic/Permutations.lean` are typed objects (`Equiv.Perm (Fin n)`, `Option`, `Fin.find`,
`Function.Bijective`); a machine computes with numbers in unary. This file defines **numeric
models** of both — plain functions `ℕ → ℕ` on the relation matrix `b : List Bool` of side `n`
(`rowFirst`, `rowMap`, `rowInv`, `isBij`, `permNum`, `permInvNum`) and on the coin tape
`r : List Bool` (`blockVal`, `trialIdx`, `offsetVal`, `fyFail`, `fyTarget`, `fyApply`,
`permFromCoinsNum`) — proves them polynomial-time in unary with the toolkit of
`EncodingMachines.lean` (bounded searches, counted loops, unary arithmetic), and identifies
the sampler model with the typed sampler (`permFromCoins_getD_val`). The identification of the
decoder model with `decPerm` lives in `Encoding.lean`, next to the decoder.

## Main definitions

* `TCSlib.Cryptography.EncodingMachines.rowFirst`, `rowMap`, `rowInv`, `isBij`, `permNum`,
  `permInvNum` — the numeric model of the permutation decoder: image and preimage of a vertex
  under the relation matrix, surjectivity test, and the decoded permutation with its inverse.
* `TCSlib.Cryptography.EncodingMachines.blockVal`, `trialIdx`, `offsetVal`, `fyFail`,
  `fyTarget`, `fyApply`, `permFromCoinsNum` — the numeric model of the permutation sampler:
  the value of a `k`-bit block of the tape, the first accepted trial of a position, its offset,
  the failure test, the Fisher–Yates target and the composed swaps.

## Main results

* `TCSlib.Cryptography.EncodingMachines.permNum_poly`, `permInvNum_poly` — the decoded
  permutation and its inverse are unary polynomial-time functions of `⟨1^n, b, 1^i⟩`.
* `TCSlib.Cryptography.EncodingMachines.permFromCoinsNum_poly` — the sampled permutation is a
  unary polynomial-time function of the tape and the parameters.
* `TCSlib.Cryptography.EncodingMachines.permFromCoins_getD_val` — the numeric model of the
  sampler agrees with `permFromCoins` (with the identity on failure) on every vertex.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.5 Protocols 118.3 and 120.6; §4.7 Protocol 127.5.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (Chapter 1, string encodings of combinatorial objects; §2.2, FP.)
-/

namespace TCSlib.Cryptography.EncodingMachines

open Complexity Turing

/-! ### The numeric model of the permutation decoder -/

/-- The least column `j < n` whose bit `(i, j)` (position `i n + j`) is set in the relation
matrix `b` of side `n`, or `n` if row `i` has no set bit. -/
noncomputable def rowFirst (n : ℕ) (b : List Bool) (i : ℕ) : ℕ :=
  firstIdx (fun j => b.getD (i * n + j) false) n

/-- The decoded image of row `i`: its first set column, or `i` itself if the row is empty (the
numeric form of the decoder's `(Fin.find _).getD i`). -/
noncomputable def rowMap (n : ℕ) (b : List Bool) (i : ℕ) : ℕ :=
  if rowFirst n b i = n then i else rowFirst n b i

/-- The least row `i < n` mapped to `u`, or `n` if there is none. -/
noncomputable def rowInv (n : ℕ) (b : List Bool) (u : ℕ) : ℕ :=
  firstIdx (fun i => decide (rowMap n b i = u)) n

/-- The surjectivity test of the decoded map: every `u < n` has a preimage. -/
noncomputable def isBij (n : ℕ) (b : List Bool) : Bool :=
  decide (firstIdx (fun u => decide (rowInv n b u = n)) n = n)

/-- The decoded permutation as a numeric function: the decoded map if it is bijective, the
identity otherwise (the numeric form of `decPerm`). -/
noncomputable def permNum (n : ℕ) (b : List Bool) (i : ℕ) : ℕ :=
  if isBij n b then rowMap n b i else i

/-- The inverse of the decoded permutation as a numeric function. -/
noncomputable def permInvNum (n : ℕ) (b : List Bool) (u : ℕ) : ℕ :=
  if isBij n b then rowInv n b u else u

/-- The decoded image of a row `i < n` is below `n`. -/
theorem rowMap_lt {n : ℕ} {b : List Bool} {i : ℕ} (hi : i < n) : rowMap n b i < n := by
  unfold rowMap
  split_ifs with h
  · exact hi
  · exact lt_of_le_of_ne firstIdx_le h

/-- The surjectivity test holds iff every `u < n` is the image of some row `i < n`. -/
theorem isBij_iff {n : ℕ} {b : List Bool} :
    isBij n b = true ↔ ∀ u < n, ∃ i < n, rowMap n b i = u := by
  unfold isBij
  rw [decide_eq_true_eq, firstIdx_eq_iff]
  refine forall_congr' fun u => forall_congr' fun _ => ?_
  rw [decide_eq_false_iff_not]
  unfold rowInv
  constructor
  · intro h
    obtain ⟨i, hi, hq⟩ := firstIdx_lt_iff.1 (lt_of_le_of_ne firstIdx_le h)
    exact ⟨i, hi, of_decide_eq_true hq⟩
  · rintro ⟨i, hi, hq⟩
    exact (firstIdx_lt_iff.2 ⟨i, hi, decide_eq_true hq⟩).ne

/-- The decoded permutation maps `i < n` below `n`. -/
theorem permNum_lt {n : ℕ} {b : List Bool} {i : ℕ} (hi : i < n) : permNum n b i < n := by
  unfold permNum
  split_ifs
  · exact rowMap_lt hi
  · exact hi

/-- `rowFirst` is a unary polynomial-time function of its unary arguments and the matrix
(`polyTimeComputable_firstIdx` with the bit test `getBit_poly`). -/
theorem rowFirst_poly {Nn I : List Bool → ℕ} {B : List Bool → List Bool}
    (hN : PolyTimeComputable fun z => List.replicate (Nn z) true) (hB : PolyTimeComputable B)
    (hI : PolyTimeComputable fun z => List.replicate (I z) true) :
    PolyTimeComputable fun z => List.replicate (rowFirst (Nn z) (B z) (I z)) true := by
  have hN' : PolyTimeComputable fun w => List.replicate (Nn (pairSndD w)) true :=
    hN.comp polyTimeComputable_pairSndD
  have hI' : PolyTimeComputable fun w => List.replicate (I (pairSndD w)) true :=
    hI.comp polyTimeComputable_pairSndD
  have hp : PolyTimeComputable fun w =>
      [(B (pairSndD w)).getD (I (pairSndD w) * Nn (pairSndD w) + (pairFstD w).length) false] :=
    getBit_poly (hB.comp polyTimeComputable_pairSndD)
      (unaryAdd_poly (unaryMul_poly hI' hN') (unaryLength_poly polyTimeComputable_pairFstD))
  exact polyTimeComputable_firstIdx (p := fun z j => (B z).getD (I z * Nn z + j) false) hp hN

/-- `rowMap` is a unary polynomial-time function. -/
theorem rowMap_poly {Nn I : List Bool → ℕ} {B : List Bool → List Bool}
    (hN : PolyTimeComputable fun z => List.replicate (Nn z) true) (hB : PolyTimeComputable B)
    (hI : PolyTimeComputable fun z => List.replicate (I z) true) :
    PolyTimeComputable fun z => List.replicate (rowMap (Nn z) (B z) (I z)) true := by
  unfold rowMap
  convert polyTimeComputable_ite (eqTest_poly (rowFirst_poly hN hB hI) hN) hI
    (rowFirst_poly hN hB hI) using 1
  funext z
  by_cases h : rowFirst (Nn z) (B z) (I z) = Nn z <;> simp [h]

/-- `rowInv` is a unary polynomial-time function (a search over the rows with the equality test
on `rowMap`). -/
theorem rowInv_poly {Nn U : List Bool → ℕ} {B : List Bool → List Bool}
    (hN : PolyTimeComputable fun z => List.replicate (Nn z) true) (hB : PolyTimeComputable B)
    (hU : PolyTimeComputable fun z => List.replicate (U z) true) :
    PolyTimeComputable fun z => List.replicate (rowInv (Nn z) (B z) (U z)) true := by
  have hN' : PolyTimeComputable fun w => List.replicate (Nn (pairSndD w)) true :=
    hN.comp polyTimeComputable_pairSndD
  have hU' : PolyTimeComputable fun w => List.replicate (U (pairSndD w)) true :=
    hU.comp polyTimeComputable_pairSndD
  have hp : PolyTimeComputable fun w =>
      [decide (rowMap (Nn (pairSndD w)) (B (pairSndD w)) (pairFstD w).length = U (pairSndD w))] :=
    eqTest_poly (rowMap_poly hN' (hB.comp polyTimeComputable_pairSndD)
      (unaryLength_poly polyTimeComputable_pairFstD)) hU'
  exact polyTimeComputable_firstIdx (p := fun z i => decide (rowMap (Nn z) (B z) i = U z)) hp hN

/-- The surjectivity test is polynomial-time (a search over the vertices for one without a
preimage). -/
theorem isBij_poly {Nn : List Bool → ℕ} {B : List Bool → List Bool}
    (hN : PolyTimeComputable fun z => List.replicate (Nn z) true) (hB : PolyTimeComputable B) :
    PolyTimeComputable fun z => [isBij (Nn z) (B z)] := by
  have hN' : PolyTimeComputable fun w => List.replicate (Nn (pairSndD w)) true :=
    hN.comp polyTimeComputable_pairSndD
  have hp : PolyTimeComputable fun w =>
      [decide (rowInv (Nn (pairSndD w)) (B (pairSndD w)) (pairFstD w).length = Nn (pairSndD w))] :=
    eqTest_poly (rowInv_poly hN' (hB.comp polyTimeComputable_pairSndD)
      (unaryLength_poly polyTimeComputable_pairFstD)) hN'
  exact eqTest_poly
    (polyTimeComputable_firstIdx (p := fun z u => decide (rowInv (Nn z) (B z) u = Nn z)) hp hN) hN

/-- The decoded permutation is a unary polynomial-time function. -/
theorem permNum_poly {Nn I : List Bool → ℕ} {B : List Bool → List Bool}
    (hN : PolyTimeComputable fun z => List.replicate (Nn z) true) (hB : PolyTimeComputable B)
    (hI : PolyTimeComputable fun z => List.replicate (I z) true) :
    PolyTimeComputable fun z => List.replicate (permNum (Nn z) (B z) (I z)) true := by
  unfold permNum
  convert polyTimeComputable_ite (isBij_poly hN hB) (rowMap_poly hN hB hI) hI using 1
  funext z
  by_cases h : isBij (Nn z) (B z) = true <;> simp [h]

/-- The inverse of the decoded permutation is a unary polynomial-time function. -/
theorem permInvNum_poly {Nn U : List Bool → ℕ} {B : List Bool → List Bool}
    (hN : PolyTimeComputable fun z => List.replicate (Nn z) true) (hB : PolyTimeComputable B)
    (hU : PolyTimeComputable fun z => List.replicate (U z) true) :
    PolyTimeComputable fun z => List.replicate (permInvNum (Nn z) (B z) (U z)) true := by
  unfold permInvNum
  convert polyTimeComputable_ite (isBij_poly hN hB) (rowInv_poly hN hB hU) hU using 1
  funext z
  by_cases h : isBij (Nn z) (B z) = true <;> simp [h]

/-! ### The numeric model of the permutation sampler -/

/-- The value of the `k`-bit block of the tape `r` starting at position `base` (most significant
bit first, missing bits read as `false`): the numeric form of `bitsToNat` on a block of the coin
table. -/
def blockVal (r : List Bool) (base k : ℕ) : ℕ :=
  (List.range k).foldl (fun a t => 2 * a + (r.getD (base + t) false).toNat) 0

/-- The empty block has value `0`. -/
@[simp] theorem blockVal_zero (r : List Bool) (base : ℕ) : blockVal r base 0 = 0 := rfl

/-- One more bit doubles the value and adds the bit. -/
theorem blockVal_succ (r : List Bool) (base k : ℕ) :
    blockVal r base (k + 1) = 2 * blockVal r base k + (r.getD (base + k) false).toNat := by
  unfold blockVal
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- A `k`-bit block has value below `2^k`. -/
theorem blockVal_lt (r : List Bool) (base : ℕ) : ∀ k, blockVal r base k < 2 ^ k
  | 0 => by simp
  | k + 1 => by
    rw [blockVal_succ, pow_succ]
    have h1 := blockVal_lt r base k
    have h2 := Bool.toNat_le (r.getD (base + k) false)
    omega

/-- `bitsToNat` of a block of the tape is `blockVal` (induction on the block length through
`List.ofFn_succ'`). -/
theorem bitsToNat_eq_blockVal (r : List Bool) (base : ℕ) :
    ∀ k, bitsToNat (fun j : Fin k => r.getD (base + j) false) = blockVal r base k
  | 0 => by simp [bitsToNat]
  | k + 1 => by
    rw [blockVal_succ, ← bitsToNat_eq_blockVal r base k]
    unfold bitsToNat
    rw [List.ofFn_succ', List.concat_eq_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [Fin.coe_castSucc, Fin.val_last]
    congr 1
    rw [show (r.getD (base + k) false).toNat = cond (r.getD (base + k) false) 1 0 from rfl,
      Bool.cond_eq_ite]

/-- The first trial `t < T` of position `i` whose block reads below `n - i`, or `T` if every
trial is rejected. -/
noncomputable def trialIdx (n k T : ℕ) (r : List Bool) (i : ℕ) : ℕ :=
  firstIdx (fun t => decide (blockVal r ((i * T + t) * k) k < n - i)) T

/-- The offset of position `i`: the value of its first accepted block. -/
noncomputable def offsetVal (n k T : ℕ) (r : List Bool) (i : ℕ) : ℕ :=
  blockVal r ((i * T + trialIdx n k T r i) * k) k

/-- The sampler fails iff some position `i < n` has no accepted trial. -/
noncomputable def fyFail (n k T : ℕ) (r : List Bool) : Bool :=
  decide (firstIdx (fun i => decide (trialIdx n k T r i = T)) n < n)

/-- The transposition `(a b)` on numbers. -/
def swapNum (a b y : ℕ) : ℕ := if y = a then b else if y = b then a else y

/-- The Fisher–Yates target of position `i`: `i + offset` when the position has an accepted
trial, `i` otherwise. -/
noncomputable def fyTarget (n k T : ℕ) (r : List Bool) (i : ℕ) : ℕ :=
  if trialIdx n k T r i < T then i + offsetVal n k T r i else i

/-- The composed swaps `s_{n-m} ∘ ⋯ ∘ s_{n-1}` applied to `x`: the state of the Fisher–Yates
loop after `m` rounds (the last position is applied first). -/
noncomputable def fyIter (n k T : ℕ) (r : List Bool) (x m : ℕ) : ℕ :=
  (List.range' (n - m) m).foldr (fun i y => swapNum i (fyTarget n k T r i) y) x

/-- The Fisher–Yates permutation `s_0 ∘ s_1 ∘ ⋯ ∘ s_{n-1}` applied to `x`. -/
noncomputable def fyApply (n k T : ℕ) (r : List Bool) (x : ℕ) : ℕ :=
  (List.range n).foldr (fun i y => swapNum i (fyTarget n k T r i) y) x

/-- The sampled permutation applied to `x`, with the identity on failure (the numeric form of
`(permFromCoins n k T b).getD 1`). -/
noncomputable def permFromCoinsNum (n k T : ℕ) (r : List Bool) (x : ℕ) : ℕ :=
  if fyFail n k T r then x else fyApply n k T r x

/-- The accepted offset of a position `i` is below `n - i`. -/
theorem offsetVal_lt {n k T : ℕ} {r : List Bool} {i : ℕ} (h : trialIdx n k T r i < T) :
    offsetVal n k T r i < n - i := by
  have := q_firstIdx h
  simpa [offsetVal, trialIdx] using this

/-- The Fisher–Yates target of a position `i < n` is below `n`. -/
theorem fyTarget_lt {n k T : ℕ} {r : List Bool} {i : ℕ} (hi : i < n) : fyTarget n k T r i < n := by
  unfold fyTarget
  split_ifs with h
  · have := offsetVal_lt h
    omega
  · exact hi

/-- A transposition of two numbers below `n` keeps a number `≤ n` at most `n`. -/
theorem swapNum_le {n a b y : ℕ} (ha : a < n) (hb : b < n) (hy : y ≤ n) : swapNum a b y ≤ n := by
  unfold swapNum
  split_ifs <;> omega

/-- The Fisher–Yates loop starts at `x`. -/
theorem fyIter_zero (n k T : ℕ) (r : List Bool) (x : ℕ) : fyIter n k T r x 0 = x := by
  simp [fyIter]

/-- One round of the Fisher–Yates loop applies the swap of position `n - 1 - m`. -/
theorem fyIter_succ {n : ℕ} (k T : ℕ) (r : List Bool) (x : ℕ) {m : ℕ} (hm : m < n) :
    fyIter n k T r x (m + 1) =
      swapNum (n - 1 - m) (fyTarget n k T r (n - 1 - m)) (fyIter n k T r x m) := by
  unfold fyIter
  rw [show n - (m + 1) = n - 1 - m by omega, List.range'_succ, List.foldr_cons,
    show n - 1 - m + 1 = n - m by omega]

/-- After `n` rounds the loop has applied the whole permutation. -/
theorem fyIter_self (n k T : ℕ) (r : List Bool) (x : ℕ) : fyIter n k T r x n = fyApply n k T r x := by
  unfold fyIter fyApply
  rw [Nat.sub_self, List.range_eq_range']

/-- The loop state stays at most `n` from a start `x ≤ n`. -/
theorem fyIter_le {n k T : ℕ} {r : List Bool} {x : ℕ} (hx : x ≤ n) :
    ∀ m, m ≤ n → fyIter n k T r x m ≤ n
  | 0, _ => by rw [fyIter_zero]; exact hx
  | m + 1, hm => by
    rw [fyIter_succ k T r x (by omega)]
    exact swapNum_le (by omega) (fyTarget_lt (by omega)) (fyIter_le hx m (by omega))

/-! ### The machines of the sampler model -/

/-- Composition of a unary function with a polynomial-time string function. -/
theorem unaryComp_poly {f : List Bool → ℕ}
    (hf : PolyTimeComputable fun x => List.replicate (f x) true) {g : List Bool → List Bool}
    (hg : PolyTimeComputable g) : PolyTimeComputable fun x => List.replicate (f (g x)) true :=
  hf.comp hg

/-- **Block values are unary polynomial-time** for blocks whose length `K z` is bounded by
`2^{K z} ≤ M z` with `M` a unary function.

**Proof sketch.** A counted loop (`polyTimeComputable_loopState`) of `K z` rounds from `1^0`
whose round `m` replaces the unary value `1^v` by `1^v ++ 1^v ++ [bit]` with the bit
`r.getD (base + m)` of the tape (`getBit_poly`), truncated to `M z` tokens (`truncate_poly`)
so that every update is bounded by `M z ≤ C(|z|+1)^c`. On the genuine orbit the truncation is
the identity since `blockVal … (m+1) < 2^{m+1} ≤ 2^{K z} ≤ M z` (`blockVal_lt`), so the state
after `m ≤ K z` rounds is `1^{blockVal (Rr z) (Base z) m}` (`blockVal_succ`,
`List.take_replicate`). -/
theorem blockVal_poly {Rr : List Bool → List Bool} {Base K M : List Bool → ℕ}
    (hR : PolyTimeComputable Rr) (hBase : PolyTimeComputable fun z => List.replicate (Base z) true)
    (hK : PolyTimeComputable fun z => List.replicate (K z) true)
    (hM : PolyTimeComputable fun z => List.replicate (M z) true) (hKM : ∀ z, 2 ^ K z ≤ M z) :
    PolyTimeComputable fun z => List.replicate (blockVal (Rr z) (Base z) (K z)) true := by
  let upd : List Bool → List Bool := fun w =>
    ((pairSndD (pairSndD w) ++ pairSndD (pairSndD w)) ++
      (if (Rr (pairFstD w)).getD (Base (pairFstD w) + (pairFstD (pairSndD w)).length) false = true
        then [true] else [])).take (M (pairFstD w))
  have hs : PolyTimeComputable fun w => pairSndD (pairSndD w) :=
    polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hbit : PolyTimeComputable fun w =>
      [(Rr (pairFstD w)).getD (Base (pairFstD w) + (pairFstD (pairSndD w)).length) false] :=
    getBit_poly (hR.comp polyTimeComputable_pairFstD)
      (unaryAdd_poly (unaryComp_poly hBase polyTimeComputable_pairFstD)
        (unaryLength_poly (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)))
  have hupd : PolyTimeComputable upd :=
    truncate_poly ((hs.append hs).append
      (polyTimeComputable_ite hbit (polyTimeComputable_const [true]) (polyTimeComputable_const [])))
      (unaryComp_poly hM polyTimeComputable_pairFstD)
  obtain ⟨C, c, hC⟩ := hM.output_length_le
  have hMC : ∀ x, M x ≤ (PolyExpr.normal C c).eval x.length := fun x => by
    have := hC x
    simpa [PolyExpr.eval_normal] using this
  have hloop := polyTimeComputable_loopState hupd (polyTimeComputable_const []) hK
    (PolyExpr.normal C c) (fun x => by simp) (fun x s => by
      show ((_ : List Bool).take (M (pairFstD (pairEncode x s)))).length ≤ _
      rw [pairFstD_pairEncode]
      exact (List.length_take_le _ _).trans (hMC x))
  convert hloop using 1
  funext z
  have key : ∀ m, m ≤ K z →
      loopState upd (fun _ => []) z m = List.replicate (blockVal (Rr z) (Base z) m) true := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      rw [loopState_succ, ih (Nat.le_of_succ_le hm)]
      simp only [upd, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
      have hle : 2 * blockVal (Rr z) (Base z) m + ((Rr z).getD (Base z + m) false).toNat ≤ M z := by
        have h1 := blockVal_lt (Rr z) (Base z) (m + 1)
        rw [blockVal_succ] at h1
        have h2 : 2 ^ (m + 1) ≤ 2 ^ K z := Nat.pow_le_pow_right (by norm_num) hm
        have h3 := hKM z
        omega
      have hrep : (List.replicate (blockVal (Rr z) (Base z) m) true ++
          List.replicate (blockVal (Rr z) (Base z) m) true) ++
          (if (Rr z).getD (Base z + m) false = true then [true] else []) =
          List.replicate (2 * blockVal (Rr z) (Base z) m +
            ((Rr z).getD (Base z + m) false).toNat) true := by
        rw [← List.replicate_add]
        cases (Rr z).getD (Base z + m) false
        · simp [two_mul]
        · rw [if_pos rfl, ← List.replicate_succ', Bool.toNat_true, two_mul]
      rw [hrep, List.take_replicate, min_eq_right hle, blockVal_succ]
  exact (key (K z) le_rfl).symm

/-- The first accepted trial of a position is a unary polynomial-time function.

**Proof sketch.** `polyTimeComputable_firstIdx` over the trials `t < T` with the test
`blockVal r ((i T + t) k) k < n - i`, itself polynomial-time by `blockVal_poly` on the unary block
start `(i T + t) k` (`unaryMul_poly`, `unaryAdd_poly`) and `ltTest_poly` against the unary
difference `n - i` (`unarySub_poly`); the parameters are read off the second component of
the search word `⟨1^t, z⟩`. -/
theorem trialIdx_poly {Nn K Tt I M : List Bool → ℕ} {Rr : List Bool → List Bool}
    (hN : PolyTimeComputable fun z => List.replicate (Nn z) true)
    (hK : PolyTimeComputable fun z => List.replicate (K z) true)
    (hT : PolyTimeComputable fun z => List.replicate (Tt z) true) (hR : PolyTimeComputable Rr)
    (hI : PolyTimeComputable fun z => List.replicate (I z) true)
    (hM : PolyTimeComputable fun z => List.replicate (M z) true) (hKM : ∀ z, 2 ^ K z ≤ M z) :
    PolyTimeComputable fun z => List.replicate (trialIdx (Nn z) (K z) (Tt z) (Rr z) (I z)) true := by
  have hp : PolyTimeComputable fun w =>
      [decide (blockVal (Rr (pairSndD w))
        ((I (pairSndD w) * Tt (pairSndD w) + (pairFstD w).length) * K (pairSndD w)) (K (pairSndD w)) <
          Nn (pairSndD w) - I (pairSndD w))] :=
    ltTest_poly (blockVal_poly (hR.comp polyTimeComputable_pairSndD)
      (unaryMul_poly (unaryAdd_poly (unaryMul_poly (unaryComp_poly hI polyTimeComputable_pairSndD)
        (unaryComp_poly hT polyTimeComputable_pairSndD))
          (unaryLength_poly polyTimeComputable_pairFstD))
        (unaryComp_poly hK polyTimeComputable_pairSndD))
      (unaryComp_poly hK polyTimeComputable_pairSndD) (unaryComp_poly hM polyTimeComputable_pairSndD)
      (fun w => hKM (pairSndD w)))
      (unarySub_poly (unaryComp_poly hN polyTimeComputable_pairSndD)
        (unaryComp_poly hI polyTimeComputable_pairSndD))
  exact polyTimeComputable_firstIdx
    (p := fun z t => decide (blockVal (Rr z) ((I z * Tt z + t) * K z) (K z) < Nn z - I z)) hp hT

/-- The accepted offset of a position is a unary polynomial-time function. -/
theorem offsetVal_poly {Nn K Tt I M : List Bool → ℕ} {Rr : List Bool → List Bool}
    (hN : PolyTimeComputable fun z => List.replicate (Nn z) true)
    (hK : PolyTimeComputable fun z => List.replicate (K z) true)
    (hT : PolyTimeComputable fun z => List.replicate (Tt z) true) (hR : PolyTimeComputable Rr)
    (hI : PolyTimeComputable fun z => List.replicate (I z) true)
    (hM : PolyTimeComputable fun z => List.replicate (M z) true) (hKM : ∀ z, 2 ^ K z ≤ M z) :
    PolyTimeComputable fun z => List.replicate (offsetVal (Nn z) (K z) (Tt z) (Rr z) (I z)) true :=
  blockVal_poly hR (unaryMul_poly (unaryAdd_poly (unaryMul_poly hI hT)
    (trialIdx_poly hN hK hT hR hI hM hKM)) hK) hK hM hKM

/-- The failure test of the sampler is polynomial-time (a search over the positions for one
whose every trial is rejected). -/
theorem fyFail_poly {Nn K Tt M : List Bool → ℕ} {Rr : List Bool → List Bool}
    (hN : PolyTimeComputable fun z => List.replicate (Nn z) true)
    (hK : PolyTimeComputable fun z => List.replicate (K z) true)
    (hT : PolyTimeComputable fun z => List.replicate (Tt z) true) (hR : PolyTimeComputable Rr)
    (hM : PolyTimeComputable fun z => List.replicate (M z) true) (hKM : ∀ z, 2 ^ K z ≤ M z) :
    PolyTimeComputable fun z => [fyFail (Nn z) (K z) (Tt z) (Rr z)] := by
  have hp : PolyTimeComputable fun w =>
      [decide (trialIdx (Nn (pairSndD w)) (K (pairSndD w)) (Tt (pairSndD w)) (Rr (pairSndD w))
        (pairFstD w).length = Tt (pairSndD w))] :=
    eqTest_poly (trialIdx_poly (unaryComp_poly hN polyTimeComputable_pairSndD)
      (unaryComp_poly hK polyTimeComputable_pairSndD) (unaryComp_poly hT polyTimeComputable_pairSndD)
      (hR.comp polyTimeComputable_pairSndD) (unaryLength_poly polyTimeComputable_pairFstD)
      (unaryComp_poly hM polyTimeComputable_pairSndD) (fun w => hKM (pairSndD w)))
      (unaryComp_poly hT polyTimeComputable_pairSndD)
  exact ltTest_poly (polyTimeComputable_firstIdx
    (p := fun z i => decide (trialIdx (Nn z) (K z) (Tt z) (Rr z) i = Tt z)) hp hN) hN

/-- The Fisher–Yates target is a unary polynomial-time function. -/
theorem fyTarget_poly {Nn K Tt I M : List Bool → ℕ} {Rr : List Bool → List Bool}
    (hN : PolyTimeComputable fun z => List.replicate (Nn z) true)
    (hK : PolyTimeComputable fun z => List.replicate (K z) true)
    (hT : PolyTimeComputable fun z => List.replicate (Tt z) true) (hR : PolyTimeComputable Rr)
    (hI : PolyTimeComputable fun z => List.replicate (I z) true)
    (hM : PolyTimeComputable fun z => List.replicate (M z) true) (hKM : ∀ z, 2 ^ K z ≤ M z) :
    PolyTimeComputable fun z => List.replicate (fyTarget (Nn z) (K z) (Tt z) (Rr z) (I z)) true := by
  unfold fyTarget
  convert polyTimeComputable_ite (ltTest_poly (trialIdx_poly hN hK hT hR hI hM hKM) hT)
    (unaryAdd_poly hI (offsetVal_poly hN hK hT hR hI hM hKM)) hI using 1
  funext z
  by_cases h : trialIdx (Nn z) (K z) (Tt z) (Rr z) (I z) < Tt z <;> simp [h]

/-- The transposition of unary functions is a unary polynomial-time function. -/
theorem swapNum_poly {A B Y : List Bool → ℕ}
    (hA : PolyTimeComputable fun z => List.replicate (A z) true)
    (hB : PolyTimeComputable fun z => List.replicate (B z) true)
    (hY : PolyTimeComputable fun z => List.replicate (Y z) true) :
    PolyTimeComputable fun z => List.replicate (swapNum (A z) (B z) (Y z)) true := by
  unfold swapNum
  convert polyTimeComputable_ite (eqTest_poly hY hA) hB
    (polyTimeComputable_ite (eqTest_poly hY hB) hA hY) using 1
  funext z
  simp only [decide_eq_true_eq]
  split_ifs <;> rfl

/-- **The Fisher–Yates permutation is unary polynomial-time** on a start `X z ≤ Nn z`.

**Proof sketch.** A counted loop (`polyTimeComputable_loopState`) of `Nn z` rounds from `1^{X z}`
whose round `m` applies the transposition of position `i = n - 1 - m` (`unarySub_poly`) with
target `fyTarget … i` (`fyTarget_poly`) to the current image `|s|` (`swapNum_poly`), truncated
to `n` tokens (`truncate_poly`) so that every update is bounded by `n ≤ C(|z|+1)^c`. On the
genuine orbit the truncation is the identity since the image stays at most `n` (`fyIter_le`,
`swapNum_le`, `fyTarget_lt`), so the state after `m ≤ n` rounds is `1^{fyIter … m}`
(`fyIter_succ`) and after `n` rounds `1^{fyApply …}` (`fyIter_self`). -/
theorem fyApply_poly {Nn K Tt X M : List Bool → ℕ} {Rr : List Bool → List Bool}
    (hN : PolyTimeComputable fun z => List.replicate (Nn z) true)
    (hK : PolyTimeComputable fun z => List.replicate (K z) true)
    (hT : PolyTimeComputable fun z => List.replicate (Tt z) true) (hR : PolyTimeComputable Rr)
    (hX : PolyTimeComputable fun z => List.replicate (X z) true)
    (hM : PolyTimeComputable fun z => List.replicate (M z) true) (hKM : ∀ z, 2 ^ K z ≤ M z)
    (hXN : ∀ z, X z ≤ Nn z) :
    PolyTimeComputable fun z => List.replicate (fyApply (Nn z) (K z) (Tt z) (Rr z) (X z)) true := by
  let I : List Bool → ℕ := fun w => Nn (pairFstD w) - 1 - (pairFstD (pairSndD w)).length
  let upd : List Bool → List Bool := fun w =>
    (List.replicate (swapNum (I w)
      (fyTarget (Nn (pairFstD w)) (K (pairFstD w)) (Tt (pairFstD w)) (Rr (pairFstD w)) (I w))
      (pairSndD (pairSndD w)).length) true).take (Nn (pairFstD w))
  have hI : PolyTimeComputable fun w => List.replicate (I w) true :=
    unarySub_poly (unarySub_poly (unaryComp_poly hN polyTimeComputable_pairFstD) (unaryConst_poly 1))
      (unaryLength_poly (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD))
  have hupd : PolyTimeComputable upd :=
    truncate_poly (swapNum_poly hI (fyTarget_poly (unaryComp_poly hN polyTimeComputable_pairFstD)
      (unaryComp_poly hK polyTimeComputable_pairFstD) (unaryComp_poly hT polyTimeComputable_pairFstD)
      (hR.comp polyTimeComputable_pairFstD) hI (unaryComp_poly hM polyTimeComputable_pairFstD)
      (fun w => hKM (pairFstD w)))
      (unaryLength_poly (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)))
      (unaryComp_poly hN polyTimeComputable_pairFstD)
  obtain ⟨C, c, hC⟩ := hN.output_length_le
  have hNC : ∀ x, Nn x ≤ (PolyExpr.normal C c).eval x.length := fun x => by
    have := hC x
    simpa [PolyExpr.eval_normal] using this
  have hloop := polyTimeComputable_loopState hupd hX hN (PolyExpr.normal C c)
    (fun x => by rw [List.length_replicate]; exact (hXN x).trans (hNC x))
    (fun x s => by
      show ((_ : List Bool).take (Nn (pairFstD (pairEncode x s)))).length ≤ _
      rw [pairFstD_pairEncode]
      exact (List.length_take_le _ _).trans (hNC x))
  convert hloop using 1
  funext z
  have key : ∀ m, m ≤ Nn z →
      loopState upd (fun z => List.replicate (X z) true) z m =
        List.replicate (fyIter (Nn z) (K z) (Tt z) (Rr z) (X z) m) true := by
    intro m
    induction m with
    | zero => intro _; simp [fyIter_zero]
    | succ m ih =>
      intro hm
      rw [loopState_succ, ih (Nat.le_of_succ_le hm), fyIter_succ (K z) (Tt z) (Rr z) (X z) hm]
      simp only [upd, I, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
      rw [List.take_replicate, min_eq_right]
      exact swapNum_le (by omega) (fyTarget_lt (by omega)) (fyIter_le (hXN z) m (by omega))
  rw [key (Nn z) le_rfl, fyIter_self]

/-- The sampled permutation (identity on failure) is a unary polynomial-time function. -/
theorem permFromCoinsNum_poly {Nn K Tt X M : List Bool → ℕ} {Rr : List Bool → List Bool}
    (hN : PolyTimeComputable fun z => List.replicate (Nn z) true)
    (hK : PolyTimeComputable fun z => List.replicate (K z) true)
    (hT : PolyTimeComputable fun z => List.replicate (Tt z) true) (hR : PolyTimeComputable Rr)
    (hX : PolyTimeComputable fun z => List.replicate (X z) true)
    (hM : PolyTimeComputable fun z => List.replicate (M z) true) (hKM : ∀ z, 2 ^ K z ≤ M z)
    (hXN : ∀ z, X z ≤ Nn z) :
    PolyTimeComputable fun z =>
      List.replicate (permFromCoinsNum (Nn z) (K z) (Tt z) (Rr z) (X z)) true := by
  unfold permFromCoinsNum
  convert polyTimeComputable_ite (fyFail_poly hN hK hT hR hM hKM) hX
    (fyApply_poly hN hK hT hR hX hM hKM hXN) using 1
  funext z
  by_cases h : fyFail (Nn z) (K z) (Tt z) (Rr z) = true <;> simp [h]

/-! ### Identification with the typed sampler -/

/-- `List.findSome?` over `List.range T` is the value at the first index with a `some`, if any
(`firstIdx` on the `isSome` test).

**Proof sketch.** Induction on `T` through `List.range_succ` and `List.findSome?_append`. If the
search over `range T` already succeeds, appending `T` changes neither the search index
(`firstIdx_eq_of`, `firstIdx_min`) nor the `findSome?` (`Option.or_of_isSome`). Otherwise every
`t < T` is rejected (`firstIdx_eq_iff`), the `findSome?` is `g T`, and the search index over
`T + 1` is `T` if `g T` is a `some` and `T + 1` (giving `none = g T`) if not. -/
theorem findSome?_range_eq {β : Type*} (g : ℕ → Option β) : ∀ T : ℕ,
    (List.range T).findSome? g =
      if firstIdx (fun t => (g t).isSome) T < T then g (firstIdx (fun t => (g t).isSome) T)
      else none
  | 0 => by simp
  | T + 1 => by
    have hsing : [T].findSome? g = g T := by
      cases h : g T <;> simp [h]
    rw [List.range_succ, List.findSome?_append, findSome?_range_eq g T, hsing]
    by_cases h : firstIdx (fun t => (g t).isSome) T < T
    · have hq := q_firstIdx h
      have heq : firstIdx (fun t => (g t).isSome) (T + 1) = firstIdx (fun t => (g t).isSome) T :=
        firstIdx_eq_of (by omega) hq (fun i hi => firstIdx_min hi)
      rw [if_pos h, heq, if_pos (by omega), Option.or_of_isSome hq]
    · have hT : firstIdx (fun t => (g t).isSome) T = T :=
        le_antisymm firstIdx_le (not_lt.1 h)
      have hall : ∀ i < T, (g i).isSome = false := firstIdx_eq_iff.1 hT
      rw [if_neg h, Option.none_or]
      by_cases hgT : (g T).isSome = true
      · have heq : firstIdx (fun t => (g t).isSome) (T + 1) = T :=
          firstIdx_eq_of (by omega) hgT hall
        rw [heq, if_pos (by omega)]
      · have heq : firstIdx (fun t => (g t).isSome) (T + 1) = T + 1 :=
          firstIdx_eq_of_forall fun i hi => by
            rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
            · exact hall i hi
            · exact Bool.eq_false_iff.2 hgT
        rw [heq, if_neg (lt_irrefl _)]
        exact Option.not_isSome_iff_eq_none.1 (by simpa using hgT)

/-- `List.findSome?` over `List.finRange T` as a `findSome?` over `List.range T`. -/
theorem findSome?_finRange_eq {β : Type*} {T : ℕ} (f : Fin T → Option β) :
    (List.finRange T).findSome? f =
      (List.range T).findSome? (fun t => if h : t < T then f ⟨t, h⟩ else none) := by
  rw [← List.map_coe_finRange, List.findSome?_map]
  congr 1
  funext t
  simp [Function.comp, t.isLt]

/-- The rejection sampler of position `i` on the blocks of the tape succeeds iff some trial is
accepted (`trialIdx < T`), and then returns the accepted offset `offsetVal`.

**Proof sketch.** `rejectionSample` is a `findSome?` over `List.finRange T`
(`findSome?_finRange_eq`, `findSome?_range_eq`), so it is the trial `uniformFromBits` at the
first index whose block reads below `n - i`; the `isSome` test of a trial is the comparison
`bitsToNat (c t) < n - i`, and `bitsToNat (c t) = blockVal r ((i T + t) k) k`
(`bitsToNat_eq_blockVal` with the block hypothesis `hc`), so the search index is `trialIdx`
(`firstIdx_congr`) and the accepted trial reads `offsetVal`. -/
theorem rejectionSample_eq_dite {n k T i : ℕ} {r : List Bool} {c : Fin T → Fin k → Bool}
    (hc : ∀ (t : Fin T) (j : Fin k), c t j = r.getD ((i * T + t) * k + j) false) :
    rejectionSample (n - i) k T c =
      if h : trialIdx n k T r i < T then some ⟨offsetVal n k T r i, offsetVal_lt h⟩ else none := by
  have hval : ∀ t : Fin T, bitsToNat (c t) = blockVal r ((i * T + t) * k) k := fun t => by
    rw [← bitsToNat_eq_blockVal]
    congr 1
    funext j
    exact hc t j
  unfold rejectionSample
  rw [findSome?_finRange_eq, findSome?_range_eq]
  have hq : firstIdx (fun t => (if h : t < T then uniformFromBits (n - i) k (c ⟨t, h⟩) else none).isSome) T =
      trialIdx n k T r i := by
    apply firstIdx_congr
    intro t ht
    rw [dif_pos ht]
    unfold uniformFromBits
    rw [hval]
    split_ifs with h <;> simp [h]
  rw [hq]
  by_cases h : trialIdx n k T r i < T
  · rw [if_pos h, dif_pos h, dif_pos h]
    unfold uniformFromBits
    rw [hval]
    split_ifs with h2
    · rfl
    · exact absurd (offsetVal_lt h) h2
  · rw [if_neg h, dif_neg h]

/-- The rejection sampler of position `i` succeeds iff `trialIdx < T`. -/
theorem rejectionSample_isSome_iff {n k T i : ℕ} {r : List Bool} {c : Fin T → Fin k → Bool}
    (hc : ∀ (t : Fin T) (j : Fin k), c t j = r.getD ((i * T + t) * k + j) false) :
    (rejectionSample (n - i) k T c).isSome ↔ trialIdx n k T r i < T := by
  rw [rejectionSample_eq_dite hc]
  split_ifs with h <;> simp [h]

/-- The value of a successful rejection sampler of position `i` is `offsetVal`. -/
theorem rejectionSample_get_val {n k T i : ℕ} {r : List Bool} {c : Fin T → Fin k → Bool}
    (hc : ∀ (t : Fin T) (j : Fin k), c t j = r.getD ((i * T + t) * k + j) false)
    (h : (rejectionSample (n - i) k T c).isSome) :
    ((rejectionSample (n - i) k T c).get h).val = offsetVal n k T r i := by
  have h' := (rejectionSample_isSome_iff hc).1 h
  have := rejectionSample_eq_dite (n := n) hc
  rw [dif_pos h'] at this
  simp [this]

/-- A transposition of `Fin n`, numerically. -/
theorem swap_val {n : ℕ} (a b y : Fin n) : ((Equiv.swap a b y : Fin n) : ℕ) = swapNum a b y := by
  rw [Equiv.swap_apply_def]
  unfold swapNum
  by_cases h1 : y = a
  · subst h1; simp
  · by_cases h2 : y = b
    · subst h2; simp [h1, Fin.val_eq_val]
    · have h1' : (y : ℕ) ≠ a := fun h => h1 (Fin.ext h)
      have h2' : (y : ℕ) ≠ b := fun h => h2 (Fin.ext h)
      simp [h1, h2, h1', h2']

/-- Folding transpositions over a list of positions, numerically: the composed permutation
applied to `x` is the fold of `swapNum` over the list of positions. -/
theorem foldr_swap_val {n : ℕ} (tg : Fin n → Fin n) (tgN : ℕ → ℕ)
    (htg : ∀ i : Fin n, (tg i : ℕ) = tgN i) :
    ∀ (l : List (Fin n)) (x : Fin n),
      ((l.foldr (fun i σ => Equiv.swap i (tg i) * σ) 1 x : Fin n) : ℕ) =
        (l.map Fin.val).foldr (fun i y => swapNum i (tgN i) y) x
  | [], x => by simp
  | i :: l, x => by
    rw [List.foldr_cons, List.map_cons, List.foldr_cons, Equiv.Perm.mul_apply, swap_val,
      ← foldr_swap_val tg tgN htg l x, htg]

/-- The Fisher–Yates permutation with the accepted offsets as offsets is `fyApply`
(`foldr_swap_val`; no modulus wraps since every accepted offset is below `n - i`). -/
theorem fisherYates_val_eq {n k T : ℕ} {r : List Bool} {c : Fin n → ℕ}
    (hok : ∀ i : Fin n, trialIdx n k T r i < T) (hc : ∀ i : Fin n, c i = offsetVal n k T r i)
    (x : Fin n) : ((fisherYates n c x : Fin n) : ℕ) = fyApply n k T r x := by
  unfold fisherYates fyApply
  rw [← List.map_coe_finRange]
  apply foldr_swap_val
  intro i
  have h1 := offsetVal_lt (hok i)
  have h2 := i.isLt
  show (↑i + c ↑i % (n - ↑i)) % n = fyTarget n k T r ↑i
  rw [fyTarget, if_pos (hok i), hc i, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (by omega)]

/-- **The numeric model agrees with the typed sampler:** on a coin table whose block `(i, t)`
reads the tape bits `(i T + t) k + j`, the permutation `permFromCoins n k T b` with the identity
on failure sends the vertex `x` to `permFromCoinsNum n k T r x`.

**Proof sketch.** Unfold `permFromCoins`: the success condition `∀ i, (rejectionSample …).isSome`
is `¬ fyFail` (`rejectionSample_isSome_iff`, `firstIdx_lt_iff`), the sampled offsets are the
`offsetVal`s (`rejectionSample_get_val`), and `fisherYates_val_eq` identifies the permutation;
on failure both sides are the identity. -/
theorem permFromCoins_getD_val {n k T : ℕ} {r : List Bool} {b : Fin n → Fin T → Fin k → Bool}
    (hb : ∀ (i : Fin n) (t : Fin T) (j : Fin k), b i t j = r.getD ((i * T + t) * k + j) false)
    (x : Fin n) :
    (((permFromCoins n k T b).getD 1 x : Fin n) : ℕ) = permFromCoinsNum n k T r x := by
  have hsome : ∀ i : Fin n,
      (rejectionSample (n - i) k T (b i)).isSome ↔ trialIdx n k T r i < T :=
    fun i => rejectionSample_isSome_iff (hb i)
  have hfail : fyFail n k T r = true ↔ ¬ ∀ i : Fin n, (rejectionSample (n - i) k T (b i)).isSome := by
    unfold fyFail
    rw [decide_eq_true_eq, firstIdx_lt_iff]
    constructor
    · rintro ⟨i, hi, hq⟩ hall
      have h1 := (hsome ⟨i, hi⟩).1 (hall ⟨i, hi⟩)
      rw [decide_eq_true_eq] at hq
      exact absurd h1 (by rw [Fin.val_mk, hq]; exact lt_irrefl _)
    · intro hnot
      obtain ⟨i, hi⟩ := not_forall.1 hnot
      refine ⟨i, i.isLt, ?_⟩
      rw [decide_eq_true_eq]
      exact le_antisymm firstIdx_le (not_lt.1 (mt (hsome i).2 hi))
  unfold permFromCoins permFromCoinsNum
  split_ifs with h1 h2 h2
  · exact absurd h1 (hfail.1 h2)
  · rw [Option.getD_some]
    exact fisherYates_val_eq (fun i => (hsome i).1 (h1 i))
      (fun i => rejectionSample_get_val (hb i) (h1 i)) x
  · simp
  · exact absurd (hfail.2 h1) h2

end TCSlib.Cryptography.EncodingMachines
