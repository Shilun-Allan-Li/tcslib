/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
import TCSlib.Cryptography.Asymptotic.HardCoreLoops
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The next-query machine for PRF encryption

The machine uses its coins for the query points and the distinguisher's coins.
Its advice carries the message vector. After receiving all answers, it applies the
distinguisher to the encoded vector of masked messages [PS10, Theorem 99.2, proof].

## Main definitions

* `MultiMsg.histBlock` and `MultiMsg.maskBlock` give the encodings of a history entry and a mask.
* `MultiMsg.preFun` and `MultiMsg.postFun` give the input and output processing for each move.
* `MultiMsg.histBlockOut`, `maskBlockOut`, `maskOfOut`, `histBlockLenOut`, `postCountOut`,
  `postOffsetOut`, `postQueryOut`, `postFunOut` and `adviceBoundOut`: the string layer at answer
  width `ℓ(n)` (ruling B3); the `n`-bit versions are their cases `ℓ = var`
  (`histBlock_eq_histBlockOut`, …).

## Main results

* `MultiMsg.zipWith_xor_histBlock_maskBlock` relates a masked history block to a ciphertext.
* `MultiMsg.polyTimeComputable_preFun` and `MultiMsg.polyTimeComputable_postFun` bound the
  processing by polynomial time.
* `MultiMsg.exists_queryChain_nuppt` packages the reduction and proves its agreement with
  the tuple experiment after relabelling its coins.
* `MultiMsg.exists_queryChainOut_nuppt` does so at `ℓ(n)`-bit answers and masks, and
  `MultiMsg.exists_oneQuery_nuppt` is its one-query case; `exists_queryChain_nuppt` is the case
  `ℓ = var`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.7, Definition 93.1, and §3.9, Algorithm 99.1 and Theorem 99.2.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4 (oracle adversaries and PRF advantage).
-/

namespace TCSlib.Cryptography.MultiMsg

open Complexity Turing Finset

/-! ### Strings: chunked encodings, history blocks, mask blocks -/

/-- **The history block at answer width `l`** (ruling B3): the self-delimited chunk
`histBlockOut p = ⟨⟨⟦p.1⟧, ⟦p.2⟧⟩, []⟩` of one pair of an `n`-bit query and an `l`-bit answer. -/
def histBlockOut {n l : ℕ} (p : (Fin n → Bool) × (Fin l → Bool)) : List Bool :=
  pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) []

/-- `histBlockOut p = ⟨⟨⟦p.1⟧, ⟦p.2⟧⟩, []⟩`. -/
theorem histBlockOut_eq {n l : ℕ} (p : (Fin n → Bool) × (Fin l → Bool)) :
    histBlockOut p = pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) [] := rfl

/-- A history block of an `n`-bit query and an `l`-bit answer has `4n + 2l + 6` bits:
`|histBlockOut p| = 4n + 2l + 6`. -/
theorem length_histBlockOut {n l : ℕ} (p : (Fin n → Bool) × (Fin l → Bool)) :
    (histBlockOut p).length = 4 * n + 2 * l + 6 := by
  simp only [histBlockOut, length_pairEncode, List.length_ofFn, List.length_nil]
  omega

/-- The encoded history is the concatenation of its blocks, at any widths:
`encodeHist h = h.flatMap histBlockOut`. -/
theorem encodeHist_eq_flatMapOut {ℓ₁ ℓ₂ : ℕ} : ∀ h : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)),
    encodeHist h = h.flatMap histBlockOut
  | [] => by rw [encodeHist_nil, List.flatMap_nil]
  | p :: h => by
    rw [encodeHist_cons, encodeHist_eq_flatMapOut h, List.flatMap_cons]
    simp [histBlockOut, pairEncode_eq]

/-- The block contributed to an encoded history by one (query, answer) pair of `n`-bit
strings: the self-delimited chunk `⟨⟨x, y⟩, []⟩`. -/
def histBlock {n : ℕ} (p : (Fin n → Bool) × (Fin n → Bool)) : List Bool :=
  pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) []

/-- The `n`-bit history block is the case `l = n` of `histBlockOut`:
`histBlock p = histBlockOut p` (`rfl`). -/
theorem histBlock_eq_histBlockOut {n : ℕ} (p : (Fin n → Bool) × (Fin n → Bool)) :
    histBlock p = histBlockOut p := rfl

/-- A history block of `n`-bit strings has length `6n + 6`. -/
theorem length_histBlock {n : ℕ} (p : (Fin n → Bool) × (Fin n → Bool)) :
    (histBlock p).length = 6 * n + 6 := by
  rw [histBlock_eq_histBlockOut, length_histBlockOut]
  omega

/-- The encoded history is the concatenation of its blocks. -/
theorem encodeHist_eq_flatMap {n : ℕ} : ∀ h : List ((Fin n → Bool) × (Fin n → Bool)),
    encodeHist h = h.flatMap histBlock
  | h => encodeHist_eq_flatMapOut h

/-- The syntactic block length `6n + 6` of a history block. -/
def histBlockLen : PolyExpr := .add (.mul (.const 6) .var) (.const 6)

/-- Evaluating the block length. -/
theorem eval_histBlockLen (n : ℕ) : histBlockLen.eval n = 6 * n + 6 := by
  simp only [histBlockLen, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const,
    PolyExpr.eval_var]

/-- The syntactic block length at answer width `ℓ`:
`histBlockLenOut ℓ = 4 · var + 2 · ℓ + 6`. -/
def histBlockLenOut (ℓ : PolyExpr) : PolyExpr :=
  .add (.add (.mul (.const 4) .var) (.mul (.const 2) ℓ)) (.const 6)

/-- `histBlockLenOut ℓ = 4 · var + 2 · ℓ + 6` (the defining equation). -/
theorem histBlockLenOut_eq (ℓ : PolyExpr) :
    histBlockLenOut ℓ = .add (.add (.mul (.const 4) .var) (.mul (.const 2) ℓ)) (.const 6) :=
  rfl

/-- `(histBlockLenOut ℓ).eval n = 4n + 2ℓ(n) + 6`. -/
theorem eval_histBlockLenOut (ℓ : PolyExpr) (n : ℕ) :
    (histBlockLenOut ℓ).eval n = 4 * n + 2 * ℓ.eval n + 6 := by
  simp only [histBlockLenOut, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const,
    PolyExpr.eval_var]

/-- The length of a concatenation of chunks of a common length `b`. -/
theorem length_flatMap_of_length {α : Type*} (f : α → List Bool) (b : ℕ) :
    ∀ L : List α, (∀ x ∈ L, (f x).length = b) → (L.flatMap f).length = L.length * b
  | [], _ => by simp
  | x :: L, h => by
    rw [List.flatMap_cons, List.length_append,
      length_flatMap_of_length f b L (fun y hy => h y (by simp [hy])), h x (by simp),
      List.length_cons]
    ring

/-- **The block map on a concatenation of equal-length chunks**: reading the string
`f x₀ ++ ⋯ ++ f x_{k−1}` (chunks of length `b > 0`) in blocks of length `b` and applying `g` to
each block gives `g (f x₀) ++ ⋯ ++ g (f x_{k−1})` (the function of
`Complexity.polyTimeComputable_blockMap`).

**Proof sketch.** Induction on the list: the string has `k + 1` blocks
(`length_flatMap_of_length`), `List.range_succ_eq_map` splits off block `0`, which is `f x`
(`List.take_left'`), and block `i + 1` of `f x ++ rest` is block `i` of `rest`
(`List.drop_append`). -/
theorem flatMap_range_blocks {α : Type*} (f : α → List Bool) (g : List Bool → List Bool) {b : ℕ}
    (hb : 0 < b) : ∀ L : List α, (∀ x ∈ L, (f x).length = b) →
      (List.range ((L.flatMap f).length / b)).flatMap
          (fun i => g (((L.flatMap f).drop (i * b)).take b)) =
        L.flatMap fun x => g (f x)
  | [], _ => by simp
  | x :: L, h => by
    have hx : (f x).length = b := h x (by simp)
    have hL : ∀ y ∈ L, (f y).length = b := fun y hy => h y (by simp [hy])
    have hlen : ((x :: L).flatMap f).length = (L.length + 1) * b := by
      rw [length_flatMap_of_length f b _ h, List.length_cons]
    rw [hlen, Nat.mul_div_cancel _ hb, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
      List.flatMap_cons]
    congr 1
    · show g (((f x ++ L.flatMap f).drop (0 * b)).take b) = g (f x)
      rw [Nat.zero_mul, List.drop_zero, List.take_left' hx]
    · show (List.range L.length).flatMap
          (fun i => g (((f x ++ L.flatMap f).drop (i.succ * b)).take b)) = L.flatMap fun y => g (f y)
      rw [← flatMap_range_blocks f g hb L hL, length_flatMap_of_length f b L hL,
        Nat.mul_div_cancel _ hb]
      congr 1
      funext i
      rw [List.drop_append,
        List.drop_of_length_le (by rw [hx]; exact Nat.le_mul_of_pos_left b (Nat.succ_pos i)),
        List.nil_append, show i.succ * b - (f x).length = i * b by
          rw [hx, Nat.succ_mul, Nat.add_sub_cancel]]

/-- A constant block map outputs the unary count of the blocks. -/
theorem flatMap_const_singleton {α : Type*} : ∀ L : List α,
    (L.flatMap fun _ => [true]) = List.replicate L.length true
  | [] => rfl
  | _ :: L => by
    rw [List.flatMap_cons, flatMap_const_singleton L, List.length_cons, List.replicate_succ]
    rfl

/-- A block map outputting `1^n` per block outputs `1^{k·n}` on `k` blocks. -/
theorem flatMap_const_replicate {α : Type*} (n : ℕ) : ∀ L : List α,
    (L.flatMap fun _ => List.replicate n true) = List.replicate (L.length * n) true
  | [] => by simp
  | _ :: L => by
    rw [List.flatMap_cons, flatMap_const_replicate n L, List.length_cons, Nat.succ_mul, add_comm,
      List.replicate_add]

/-- The query component of a history block at answer width `l`:
`pairFstD (pairFstD (histBlockOut p)) = ⟦p.1⟧`. -/
theorem pairFstD_pairFstD_histBlockOut {n l : ℕ} (p : (Fin n → Bool) × (Fin l → Bool)) :
    pairFstD (pairFstD (histBlockOut p)) = List.ofFn p.1 := by
  simp [histBlockOut]

/-- The query component of a history block: `pairFstD (pairFstD (histBlock p))` is the query
`p.1`. -/
theorem pairFstD_pairFstD_histBlock {n : ℕ} (p : (Fin n → Bool) × (Fin n → Bool)) :
    pairFstD (pairFstD (histBlock p)) = List.ofFn p.1 := by
  rw [histBlock_eq_histBlockOut, pairFstD_pairFstD_histBlockOut]

/-- **The mask block at answer width `l`** for `n`-bit queries: zeros under the (doubled) query
and the separators, `w` doubled under the (doubled) answer:
`maskBlockOut n w = 0^{4n+4} ++ dbl ⟦w⟧ ++ [0, 0]`. -/
def maskBlockOut {l : ℕ} (n : ℕ) (w : Fin l → Bool) : List Bool :=
  List.replicate (4 * n + 4) false ++ dbl (List.ofFn w) ++ [false, false]

/-- `maskBlockOut n w = 0^{4n+4} ++ dbl ⟦w⟧ ++ [0, 0]`. -/
theorem maskBlockOut_eq {l : ℕ} (n : ℕ) (w : Fin l → Bool) :
    maskBlockOut n w = List.replicate (4 * n + 4) false ++ dbl (List.ofFn w) ++ [false, false] :=
  rfl

/-- A mask block at answer width `l` has the length of a history block:
`|maskBlockOut n w| = 4n + 2l + 6`. -/
theorem length_maskBlockOut {l : ℕ} (n : ℕ) (w : Fin l → Bool) :
    (maskBlockOut n w).length = 4 * n + 2 * l + 6 := by
  simp only [maskBlockOut, List.length_append, List.length_replicate, length_dbl, List.length_ofFn,
    List.length_cons, List.length_nil]
  omega

/-- The mask block of the message `w`: zeros under the (doubled) query and the separators,
`w` doubled under the (doubled) answer, so that `histBlock (x, y) ⊕ maskBlock w` is the
history block of `(x, w ⊕ y)`. -/
def maskBlock {n : ℕ} (w : Fin n → Bool) : List Bool :=
  List.replicate (4 * n + 4) false ++ dbl (List.ofFn w) ++ [false, false]

/-- The `n`-bit mask block is the case `l = n` of `maskBlockOut`:
`maskBlock w = maskBlockOut n w` (`rfl`). -/
theorem maskBlock_eq_maskBlockOut {n : ℕ} (w : Fin n → Bool) : maskBlock w = maskBlockOut n w :=
  rfl

/-- A mask block has the length `6n + 6` of a history block. -/
theorem length_maskBlock {n : ℕ} (w : Fin n → Bool) : (maskBlock w).length = 6 * n + 6 := by
  rw [maskBlock_eq_maskBlockOut, length_maskBlockOut]
  omega

/-- Doubling distributes over concatenation. -/
theorem dbl_append (a b : List Bool) : dbl (a ++ b) = dbl a ++ dbl b := by
  induction a with
  | nil => rw [List.nil_append, dbl_nil, List.nil_append]
  | cons x a ih => rw [List.cons_append, dbl_cons, dbl_cons, ih, List.cons_append, List.cons_append]

/-- Masking with zeros is the identity. -/
theorem zipWith_xor_replicate_false : ∀ l : List Bool,
    List.zipWith xor l (List.replicate l.length false) = l
  | [] => rfl
  | a :: l => by
    rw [List.length_cons, List.replicate_succ, List.zipWith_cons_cons, zipWith_xor_replicate_false l,
      Bool.xor_false]

/-- Exclusive-or commutes with doubling. -/
theorem zipWith_xor_dbl : ∀ a b : List Bool,
    List.zipWith xor (dbl a) (dbl b) = dbl (List.zipWith xor a b)
  | [], _ => by rw [dbl_nil, List.zipWith_nil_left, List.zipWith_nil_left, dbl_nil]
  | _ :: _, [] => by rw [dbl_nil, List.zipWith_nil_right, List.zipWith_nil_right, dbl_nil]
  | x :: a, y :: b => by
    simp only [dbl_cons, List.zipWith_cons_cons, zipWith_xor_dbl a b]

/-- **Masking a history block at answer width `l`**: for an `n`-bit query `x` and `l`-bit
strings `y`, `w`, `histBlockOut (x, y) ⊕ maskBlockOut n w = ⟨⟨⟦x⟧, ⟦w + y⟧⟩, []⟩`.

**Proof sketch.** `⟨⟨x, y⟩, []⟩ = dbl (dbl x) ++ 0011 ++ dbl y ++ 01`; the mask is
`0^{4n+4} ++ dbl w ++ 00`; `List.zipWith_append` splits the exclusive-or along these segments,
zeros are neutral (`zipWith_xor_replicate_false`) and `dbl y ⊕ dbl w = dbl (y ⊕ w)`
(`zipWith_xor_dbl`). -/
theorem zipWith_xor_histBlockOut_maskBlockOut {n l : ℕ} (x : Fin n → Bool) (y w : Fin l → Bool) :
    List.zipWith xor (histBlockOut (x, y)) (maskBlockOut n w) =
      pairEncode (pairEncode (List.ofFn x) (List.ofFn (w + y))) [] := by
  have hyw : List.zipWith xor (List.ofFn y) (List.ofFn w) = List.ofFn (w + y) := by
    rw [zipWith_xor_ofFn_add, add_comm]
  have h1 : histBlockOut (x, y) =
      (dbl (dbl (List.ofFn x)) ++ [false, false, true, true]) ++
        (dbl (List.ofFn y) ++ [false, true]) := by
    simp only [histBlockOut, pairEncode_eq_dbl, dbl_append, List.append_nil, List.append_assoc,
      dbl_cons, List.cons_append, List.nil_append]
  have h2 : maskBlockOut n w =
      List.replicate (dbl (dbl (List.ofFn x)) ++ [false, false, true, true]).length false ++
        (dbl (List.ofFn w) ++ [false, false]) := by
    simp only [maskBlockOut, List.length_append, length_dbl, List.length_ofFn, List.length_cons,
      List.length_nil, List.append_assoc]
    congr 2
    omega
  rw [h1, h2, List.zipWith_append (List.length_replicate ..).symm, zipWith_xor_replicate_false,
    List.zipWith_append (by simp only [length_dbl, List.length_ofFn]), zipWith_xor_dbl, hyw]
  simp only [pairEncode_eq_dbl, dbl_append, List.append_nil, List.append_assoc, dbl_cons,
    List.cons_append, List.nil_append]
  rfl

/-- **Masking a history block**: the exclusive-or of the history block of `(x, y)` with the
mask block of `w` is the history block of `(x, w ⊕ y)` (strings `x, y, w` of the same length).

**Proof sketch.** The case `l = n` of `zipWith_xor_histBlockOut_maskBlockOut`
(`histBlock_eq_histBlockOut`, `maskBlock_eq_maskBlockOut`). -/
theorem zipWith_xor_histBlock_maskBlock {n : ℕ} (x y w : Fin n → Bool) :
    List.zipWith xor (histBlock (x, y)) (maskBlock w) =
      pairEncode (pairEncode (List.ofFn x) (List.ofFn (w + y))) [] := by
  rw [histBlock_eq_histBlockOut, maskBlock_eq_maskBlockOut]
  exact zipWith_xor_histBlockOut_maskBlockOut x y w

/-- The exclusive-or of two concatenations of `k` chunks of pairwise equal lengths is the
concatenation of the chunkwise exclusive-ors. -/
theorem zipWith_xor_flatten_ofFn : ∀ {k : ℕ} (F G : Fin k → List Bool),
    (∀ j, (F j).length = (G j).length) →
      List.zipWith xor (List.ofFn F).flatten (List.ofFn G).flatten =
        (List.ofFn fun j => List.zipWith xor (F j) (G j)).flatten
  | 0, _, _, _ => rfl
  | k + 1, F, G, h => by
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.flatten_cons, List.flatten_cons,
      List.flatten_cons, List.zipWith_append (h 0),
      zipWith_xor_flatten_ofFn (fun j => F j.succ) (fun j => G j.succ) fun j => h j.succ]

/-- A string of `q·s` bits read as `q` chunks of `s` bits: chunk `i` is block `i` of
`FunFamily.blocks` (the block window `FunFamily.ofFn_blocks`, read backwards). -/
theorem take_drop_ofFn_blocks {q s : ℕ} (w : Fin (q * s) → Bool) (i : ℕ) (hi : i < q) :
    ((List.ofFn w).drop (i * s)).take s = List.ofFn (FunFamily.blocks q s w ⟨i, hi⟩) :=
  (FunFamily.ofFn_blocks q s w ⟨i, hi⟩).symm

/-! ### The next-query machine of Thm-99.2.1 -/

/-- The function of `Complexity.polyTimeComputable_blockMap`: on `⟨u, s⟩`, apply `g` to the
consecutive blocks of `s` of length `b(|u|)` and concatenate. -/
def blockMapFun (b : PolyExpr) (g : List Bool → List Bool) (z : List Bool) : List Bool :=
  (List.range ((pairSndD z).length / b.eval (pairFstD z).length)).flatMap fun i =>
    g (((pairSndD z).drop (i * b.eval (pairFstD z).length)).take (b.eval (pairFstD z).length))

/-- The block map is polynomial-time (`Complexity.polyTimeComputable_blockMap`). -/
theorem polyTimeComputable_blockMapFun (b : PolyExpr) {g : List Bool → List Bool}
    (hg : PolyTimeComputable g) : PolyTimeComputable (blockMapFun b g) :=
  polyTimeComputable_blockMap b hg

/-- The typed head cut `⟨u, s⟩ ↦ s.take (p(|u|))` (`Complexity.polyTimeComputable_pairTakePoly`). -/
def takePolyFun (p : PolyExpr) (z : List Bool) : List Bool :=
  (pairSndD z).take (p.eval (pairFstD z).length)

/-- The typed tail cut `⟨u, s⟩ ↦ s.drop (p(|u|))` (`Complexity.polyTimeComputable_pairDropPoly`). -/
def dropPolyFun (p : PolyExpr) (z : List Bool) : List Bool :=
  (pairSndD z).drop (p.eval (pairFstD z).length)

/-- **The pre-processing of the next-query machine**: on `⟨⟨H, ρ⟩, ⟨M, u⟩⟩` output `H ⊕ M`,
the encoded history masked by the hard-wired mask of the messages (which turns the recorded
answers `ans_j` into `m_j ⊕ ans_j`, `zipWith_xor_histBlock_maskBlock`). -/
def preFun (y : List Bool) : List Bool :=
  List.zipWith xor (pairFstD (pairFstD y)) (pairFstD (pairSndD y))

/-- `preFun` is polynomial-time (`Complexity.polyTimeComputable_pairXor` on two projections). -/
theorem polyTimeComputable_preFun : PolyTimeComputable preFun := by
  have h := polyTimeComputable_pairXor.comp
    ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD).pairEncode
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD))
  convert h using 1
  funext y
  simp [preFun, Function.comp_apply]

/-- The history slot of the post-processor's argument `⟨⟨⟨H, ρ⟩, ⟨M, u⟩⟩, a⟩`. -/
def postHist (z : List Bool) : List Bool := pairFstD (pairFstD (pairFstD (NUPPT.inArg z)))

/-- The points slot `ρ` of the post-processor's argument. -/
def postPoints (z : List Bool) : List Bool := pairSndD (pairFstD (pairFstD (NUPPT.inArg z)))

/-- The budget slot `u = 1^{q+1}` of the post-processor's argument. -/
def postBudget (z : List Bool) : List Bool := pairSndD (pairSndD (pairFstD (NUPPT.inArg z)))

/-- The slot `a` of the post-processor's argument holding the distinguisher's output. -/
def postAns (z : List Bool) : List Bool := pairSndD (NUPPT.inArg z)

/-- The unary count `1^k` of the history blocks (block map with the constant `[true]`). -/
def postCount (z : List Bool) : List Bool :=
  blockMapFun histBlockLen (fun _ => [true]) (pairEncode (NUPPT.inParam z) (postHist z))

/-- The unary offset `1^{k·n}` of the next point in the coin string (block map emitting
`1^{|x|}` for the query `x` of each block). -/
def postOffset (z : List Bool) : List Bool :=
  blockMapFun histBlockLen (fun blk => List.replicate (pairFstD (pairFstD blk)).length true)
    (pairEncode (NUPPT.inParam z) (postHist z))

/-- The query move `⟨[false], ρ_k⟩`: the `n`-bit block of the points after the first `k·n`. -/
def postQuery (z : List Bool) : List Bool :=
  pairEncode [false] (takePolyFun .var
    (pairEncode (NUPPT.inParam z) (dropPolyFun .var (pairEncode (postOffset z) (postPoints z)))))

/-- The verdict move `[true, b]` with `b` the distinguisher's acceptance `a = [true]`. -/
def postVerdict (z : List Bool) : List Bool :=
  [true] ++ [decide (pairFstD (pairEncode (postAns z) [true]) = pairSndD (pairEncode (postAns z) [true]))]

/-- The unary count `1^k` of the history blocks at answer width `ℓ(n)` (block length
`histBlockLenOut ℓ`): `postCountOut ℓ z = blockMapFun (histBlockLenOut ℓ) (fun _ => [true])
⟨inParam z, postHist z⟩`. -/
def postCountOut (ℓ : PolyExpr) (z : List Bool) : List Bool :=
  blockMapFun (histBlockLenOut ℓ) (fun _ => [true]) (pairEncode (NUPPT.inParam z) (postHist z))

/-- `postCountOut ℓ z = blockMapFun (histBlockLenOut ℓ) (fun _ => [true]) ⟨inParam z, postHist z⟩`.
-/
theorem postCountOut_eq (ℓ : PolyExpr) (z : List Bool) :
    postCountOut ℓ z = blockMapFun (histBlockLenOut ℓ) (fun _ => [true])
      (pairEncode (NUPPT.inParam z) (postHist z)) :=
  rfl

/-- The unary offset `1^{k·n}` of the next point at answer width `ℓ(n)`: the block map emitting
`1^{|x|}` for the query `x` of each block of length `histBlockLenOut ℓ`,
`postOffsetOut ℓ z = blockMapFun (histBlockLenOut ℓ) (fun blk => 1^{|fst (fst blk)|})
⟨inParam z, postHist z⟩`. -/
def postOffsetOut (ℓ : PolyExpr) (z : List Bool) : List Bool :=
  blockMapFun (histBlockLenOut ℓ) (fun blk => List.replicate (pairFstD (pairFstD blk)).length true)
    (pairEncode (NUPPT.inParam z) (postHist z))

/-- `postOffsetOut ℓ z = blockMapFun (histBlockLenOut ℓ) (fun blk => 1^{|fst (fst blk)|})
⟨inParam z, postHist z⟩`. -/
theorem postOffsetOut_eq (ℓ : PolyExpr) (z : List Bool) :
    postOffsetOut ℓ z = blockMapFun (histBlockLenOut ℓ)
      (fun blk => List.replicate (pairFstD (pairFstD blk)).length true)
      (pairEncode (NUPPT.inParam z) (postHist z)) :=
  rfl

/-- The query move `⟨[false], ρ_k⟩` at answer width `ℓ(n)`: the `n`-bit block of the points
after the first `k·n` (`postOffsetOut ℓ`), `postQueryOut ℓ z = ⟨[false], takePolyFun var
⟨inParam z, dropPolyFun var ⟨postOffsetOut ℓ z, postPoints z⟩⟩⟩`. -/
def postQueryOut (ℓ : PolyExpr) (z : List Bool) : List Bool :=
  pairEncode [false] (takePolyFun .var
    (pairEncode (NUPPT.inParam z)
      (dropPolyFun .var (pairEncode (postOffsetOut ℓ z) (postPoints z)))))

/-- `postQueryOut ℓ z = ⟨[false], takePolyFun var ⟨inParam z, dropPolyFun var ⟨postOffsetOut ℓ z,
postPoints z⟩⟩⟩`. -/
theorem postQueryOut_eq (ℓ : PolyExpr) (z : List Bool) :
    postQueryOut ℓ z = pairEncode [false] (takePolyFun .var
      (pairEncode (NUPPT.inParam z)
        (dropPolyFun .var (pairEncode (postOffsetOut ℓ z) (postPoints z))))) :=
  rfl

/-- **The post-processing of the next-query machine at answer width `ℓ(n)`**: the verdict
`[true, [a = [true]]]` once the history has `|u|` blocks (of length `histBlockLenOut ℓ`), the
query `⟨[false], ρ_k⟩` before: `postFunOut ℓ z = if |postBudget z| ≤ |postCountOut ℓ z| then
postVerdict z else postQueryOut ℓ z`. -/
def postFunOut (ℓ : PolyExpr) (z : List Bool) : List Bool :=
  if decide ((postBudget z).length ≤ (postCountOut ℓ z).length) = true then postVerdict z
  else postQueryOut ℓ z

/-- `postFunOut ℓ z = if |postBudget z| ≤ |postCountOut ℓ z| then postVerdict z
else postQueryOut ℓ z`. -/
theorem postFunOut_eq (ℓ : PolyExpr) (z : List Bool) :
    postFunOut ℓ z =
      if decide ((postBudget z).length ≤ (postCountOut ℓ z).length) = true then postVerdict z
      else postQueryOut ℓ z :=
  rfl

/-- `postFunOut ℓ` is polynomial-time: `PolyTimeComputable (postFunOut ℓ)`.

**Proof sketch.** As `polyTimeComputable_postFun`, with the block length `histBlockLenOut ℓ`:
projections of the layout, two block maps (`polyTimeComputable_blockMapFun`), the typed cuts, a
length test (`StateLoop.lenLe_comp`), an equality test and one branch. -/
theorem polyTimeComputable_postFunOut (ℓ : PolyExpr) : PolyTimeComputable (postFunOut ℓ) := by
  have hArg := NUPPT.polyTimeComputable_inArg
  have hParam := NUPPT.polyTimeComputable_inParam
  have hHist : PolyTimeComputable postHist :=
    polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp
      (polyTimeComputable_pairFstD.comp hArg))
  have hPoints : PolyTimeComputable postPoints :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp
      (polyTimeComputable_pairFstD.comp hArg))
  have hBudget : PolyTimeComputable postBudget :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp
      (polyTimeComputable_pairFstD.comp hArg))
  have hAns : PolyTimeComputable postAns := polyTimeComputable_pairSndD.comp hArg
  have hCount : PolyTimeComputable (postCountOut ℓ) :=
    (polyTimeComputable_blockMapFun (histBlockLenOut ℓ) (polyTimeComputable_const [true])).comp
      (hParam.pairEncode hHist)
  have hOffset : PolyTimeComputable (postOffsetOut ℓ) :=
    (polyTimeComputable_blockMapFun (histBlockLenOut ℓ)
      (polyTimeComputable_unary.comp
        (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD))).comp
      (hParam.pairEncode hHist)
  have hQuery : PolyTimeComputable (postQueryOut ℓ) :=
    (polyTimeComputable_const [false]).pairEncode ((polyTimeComputable_pairTakePoly .var).comp
      (hParam.pairEncode ((polyTimeComputable_pairDropPoly .var).comp
        (hOffset.pairEncode hPoints))))
  have hVerdict : PolyTimeComputable postVerdict :=
    (polyTimeComputable_prepend [true]).comp
      (polyTimeComputable_pairEq.comp (hAns.pairEncode (polyTimeComputable_const [true])))
  exact polyTimeComputable_ite (StateLoop.lenLe_comp hCount hBudget) hVerdict hQuery

/-- **The post-processing of the next-query machine** on the raw layout
`⟨⟨⟨1^n, ⟨⟨⟨H, ρ⟩, ⟨M, u⟩⟩, a⟩⟩, []⟩, r⟩`: if the history already has `|u|` blocks, the
verdict `[true, [a = [true]]]`; otherwise the query `⟨[false], ρ_k⟩` at the `k`-th point,
`k` the number of history blocks. -/
def postFun (z : List Bool) : List Bool :=
  if decide ((postBudget z).length ≤ (postCount z).length) = true then postVerdict z
  else postQuery z

/-- The `n`-bit block count is the case `ℓ = var` of `postCountOut`:
`postCount z = postCountOut var z` (equal block lengths `6n + 6 = 4n + 2n + 6`). -/
theorem postCount_eq_postCountOut (z : List Bool) : postCount z = postCountOut .var z := by
  simp only [postCount, postCountOut, blockMapFun, eval_histBlockLen, eval_histBlockLenOut,
    PolyExpr.eval_var, show ∀ m : ℕ, 4 * m + 2 * m + 6 = 6 * m + 6 from fun m => by omega]

/-- The `n`-bit offset is the case `ℓ = var` of `postOffsetOut`:
`postOffset z = postOffsetOut var z`. -/
theorem postOffset_eq_postOffsetOut (z : List Bool) : postOffset z = postOffsetOut .var z := by
  simp only [postOffset, postOffsetOut, blockMapFun, eval_histBlockLen, eval_histBlockLenOut,
    PolyExpr.eval_var, show ∀ m : ℕ, 4 * m + 2 * m + 6 = 6 * m + 6 from fun m => by omega]

/-- The `n`-bit query move is the case `ℓ = var` of `postQueryOut`:
`postQuery z = postQueryOut var z`. -/
theorem postQuery_eq_postQueryOut (z : List Bool) : postQuery z = postQueryOut .var z := by
  rw [postQuery, postQueryOut, postOffset_eq_postOffsetOut]

/-- The `n`-bit post-processor is the case `ℓ = var` of `postFunOut`:
`postFun z = postFunOut var z`. -/
theorem postFun_eq_postFunOut (z : List Bool) : postFun z = postFunOut .var z := by
  rw [postFun, postFunOut, postCount_eq_postCountOut, postQuery_eq_postQueryOut]

/-- `postFun` is polynomial-time.

**Proof sketch.** The case `ℓ = var` of `polyTimeComputable_postFunOut`
(`postFun_eq_postFunOut`). -/
theorem polyTimeComputable_postFun : PolyTimeComputable postFun :=
  (polyTimeComputable_postFunOut .var).congr fun z => (postFun_eq_postFunOut z).symm

/-- **The mask of a message vector at answer width `l`** (for `n`-bit queries): the concatenation
of the mask blocks of its entries,
`maskOfOut n v = (List.ofFn fun j => maskBlockOut n (v j)).flatten`. -/
def maskOfOut {l k : ℕ} (n : ℕ) (v : Fin k → Fin l → Bool) : List Bool :=
  (List.ofFn fun j => maskBlockOut n (v j)).flatten

/-- `maskOfOut n v = (List.ofFn fun j => maskBlockOut n (v j)).flatten`. -/
theorem maskOfOut_eq {l k : ℕ} (n : ℕ) (v : Fin k → Fin l → Bool) :
    maskOfOut n v = (List.ofFn fun j => maskBlockOut n (v j)).flatten :=
  rfl

/-- The mask of a message vector: the concatenation of the mask blocks of its entries. -/
def maskOf {n k : ℕ} (v : Fin k → Fin n → Bool) : List Bool :=
  (List.ofFn fun j => maskBlock (v j)).flatten

/-- The `n`-bit mask is the case `l = n` of `maskOfOut`: `maskOf v = maskOfOut n v` (`rfl`). -/
theorem maskOf_eq_maskOfOut {n k : ℕ} (v : Fin k → Fin n → Bool) : maskOf v = maskOfOut n v :=
  rfl

/-- The length of a concatenation of strings of a common length `b`. -/
theorem length_flatten_of_length (b : ℕ) : ∀ L : List (List Bool),
    (∀ x ∈ L, x.length = b) → L.flatten.length = L.length * b
  | [], _ => by simp
  | x :: L, h => by
    rw [List.flatten_cons, List.length_append,
      length_flatten_of_length b L (fun y hy => h y (by simp [hy])), h x (by simp),
      List.length_cons]
    ring

/-- The mask of `k` messages of `l` bits for `n`-bit queries has `k (4n + 2l + 6)` bits:
`|maskOfOut n v| = k · (4n + 2l + 6)`. -/
theorem length_maskOfOut {l k : ℕ} (n : ℕ) (v : Fin k → Fin l → Bool) :
    (maskOfOut n v).length = k * (4 * n + 2 * l + 6) := by
  unfold maskOfOut
  rw [length_flatten_of_length (4 * n + 2 * l + 6), List.length_ofFn]
  intro x hx
  obtain ⟨j, -, rfl⟩ := List.mem_ofFn.1 hx
  exact length_maskBlockOut _ _

/-- The length of the mask of `k` messages of `n` bits is `k (6n + 6)`. -/
theorem length_maskOf {n k : ℕ} (v : Fin k → Fin n → Bool) :
    (maskOf v).length = k * (6 * n + 6) := by
  rw [maskOf_eq_maskOfOut, length_maskOfOut]
  congr 1
  omega

/-- The advice bound of the next-query machine: `|⟨mask, 1^{q+1}⟩|`. -/
def adviceBound (q : PolyExpr) : PolyExpr :=
  .add (.add (.mul (.const 2) (.mul (.add q (.const 1)) histBlockLen)) (.const 2)) (.add q (.const 1))

/-- The advice bound of the next-query machine at answer width `ℓ`: `|⟨mask, 1^{q+1}⟩|`,
`adviceBoundOut q ℓ = 2 · ((q + 1) · histBlockLenOut ℓ) + 2 + (q + 1)`. -/
def adviceBoundOut (q ℓ : PolyExpr) : PolyExpr :=
  .add (.add (.mul (.const 2) (.mul (.add q (.const 1)) (histBlockLenOut ℓ))) (.const 2))
    (.add q (.const 1))

/-- `adviceBoundOut q ℓ = 2 · ((q + 1) · histBlockLenOut ℓ) + 2 + (q + 1)` (the defining
equation). -/
theorem adviceBoundOut_eq (q ℓ : PolyExpr) :
    adviceBoundOut q ℓ =
      .add (.add (.mul (.const 2) (.mul (.add q (.const 1)) (histBlockLenOut ℓ))) (.const 2))
        (.add q (.const 1)) :=
  rfl

/-- `(adviceBoundOut q ℓ).eval n = 2 ((q(n) + 1)(4n + 2ℓ(n) + 6)) + 2 + (q(n) + 1)`. -/
theorem eval_adviceBoundOut (q ℓ : PolyExpr) (n : ℕ) :
    (adviceBoundOut q ℓ).eval n =
      2 * ((q.eval n + 1) * (4 * n + 2 * ℓ.eval n + 6)) + 2 + (q.eval n + 1) := by
  simp only [adviceBoundOut, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const,
    eval_histBlockLenOut]

/-- Decoding the well-formed query move `⟨[false], x⟩`. -/
theorem decodeOracleMove_query (ℓ : ℕ) (x : Fin ℓ → Bool) :
    decodeOracleMove ℓ (pairEncode [false] (List.ofFn x)) = .query x := by
  rw [decodeOracleMove_pairEncode_false, decodeFin_ofFn]

/-- Decoding the verdict move `[true, b]`. -/
theorem decodeOracleMove_ret (ℓ : ℕ) (b : Bool) : decodeOracleMove ℓ [true, b] = .ret b :=
  decodeOracleMove_true_two ℓ b

/-- **The post-processor at answer width `ℓ(n)` on the layout of the composite machine**: for a
history of `k` pairs of an `n`-bit query and an `ℓ(n)`-bit answer, the points string `P`, a mask
`M`, the budget string `u` and the distinguisher's output `a`, the move is the verdict
`[true, [a = [true]]]` when `|u| ≤ k` and the query `⟨[false], P[k n, (k+1) n)⟩` otherwise.

**Proof sketch.** The projections of the layout read the slots; the two block maps on
`⟨1^n, encodeHist hist⟩` output `1^k` and `1^{k n}` (`encodeHist_eq_flatMapOut`,
`flatMap_range_blocks` with blocks of length `4n + 2ℓ(n) + 6 > 0`, `flatMap_const_singleton`,
`flatMap_const_replicate`); the typed cuts then select the block. -/
theorem postFunOut_layout {n : ℕ} (ℓ : PolyExpr)
    (hist : List ((Fin n → Bool) × (Fin (ℓ.eval n) → Bool))) (P M u a : List Bool) :
    postFunOut ℓ (NUPPT.layout (List.replicate n true)
        (pairEncode (pairEncode (pairEncode (encodeHist hist) P) (pairEncode M u)) a) [] []) =
      if u.length ≤ hist.length then [true, decide (a = [true])]
      else pairEncode [false] ((P.drop (hist.length * n)).take n) := by
  set z := NUPPT.layout (List.replicate n true)
    (pairEncode (pairEncode (pairEncode (encodeHist hist) P) (pairEncode M u)) a) [] [] with hz
  have harg : NUPPT.inArg z =
      pairEncode (pairEncode (pairEncode (encodeHist hist) P) (pairEncode M u)) a :=
    NUPPT.inArg_layout _ _ _ _
  have hpar : NUPPT.inParam z = List.replicate n true := NUPPT.inParam_layout _ _ _ _
  have hblocks : ∀ x ∈ hist, (histBlockOut x).length = 4 * n + 2 * ℓ.eval n + 6 :=
    fun x _ => length_histBlockOut x
  have hpos : 0 < 4 * n + 2 * ℓ.eval n + 6 := by omega
  have hcount : postCountOut ℓ z = List.replicate hist.length true := by
    simp only [postCountOut, postHist, harg, hpar, pairFstD_pairEncode, pairSndD_pairEncode,
      blockMapFun, List.length_replicate, eval_histBlockLenOut, encodeHist_eq_flatMapOut]
    exact (flatMap_range_blocks histBlockOut (fun _ => [true]) hpos hist hblocks).trans
      (flatMap_const_singleton hist)
  have hoffset : postOffsetOut ℓ z = List.replicate (hist.length * n) true := by
    simp only [postOffsetOut, postHist, harg, hpar, pairFstD_pairEncode, pairSndD_pairEncode,
      blockMapFun, List.length_replicate, eval_histBlockLenOut, encodeHist_eq_flatMapOut]
    refine (flatMap_range_blocks histBlockOut
      (fun blk => List.replicate (pairFstD (pairFstD blk)).length true) hpos hist
        hblocks).trans ?_
    show hist.flatMap
      (fun x => List.replicate (pairFstD (pairFstD (histBlockOut x))).length true) = _
    simp only [pairFstD_pairFstD_histBlockOut, List.length_ofFn]
    exact flatMap_const_replicate n hist
  have hbudget : postBudget z = u := by
    simp only [postBudget, harg, pairFstD_pairEncode, pairSndD_pairEncode]
  have hans : postAns z = a := by
    simp only [postAns, harg, pairSndD_pairEncode]
  have hpoints : postPoints z = P := by
    simp only [postPoints, harg, pairFstD_pairEncode, pairSndD_pairEncode]
  simp only [postFunOut, hbudget, hcount, List.length_replicate]
  by_cases h : u.length ≤ hist.length
  · rw [if_pos (by simpa using h), if_pos h]
    simp only [postVerdict, hans, pairFstD_pairEncode, pairSndD_pairEncode]
    rfl
  · rw [if_neg (by simpa using h), if_neg h]
    simp only [postQueryOut, takePolyFun, dropPolyFun, hoffset, hpoints, hpar,
      pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate, PolyExpr.eval_var]

/-- **The post-processor on the layout of the composite machine**: for a history of `k` pairs
of `n`-bit strings, the points string `P`, a mask `M`, the budget string `u` and the
distinguisher's output `a`, the move is the verdict `[true, [a = [true]]]` when `|u| ≤ k` and
the query `⟨[false], P[k n, (k+1) n)⟩` otherwise.

**Proof sketch.** The case `ℓ = var` of `postFunOut_layout` (`postFun_eq_postFunOut`). -/
theorem postFun_layout {n : ℕ} (hist : List ((Fin n → Bool) × (Fin n → Bool)))
    (P M u a : List Bool) :
    postFun (NUPPT.layout (List.replicate n true)
        (pairEncode (pairEncode (pairEncode (encodeHist hist) P) (pairEncode M u)) a) [] []) =
      if u.length ≤ hist.length then [true, decide (a = [true])]
      else pairEncode [false] ((P.drop (hist.length * n)).take n) := by
  rw [postFun_eq_postFunOut]
  exact postFunOut_layout .var hist P M u a

/-- Concatenating the chunks `f (F i)` of a tuple: `flatMap` over `ofFn`. -/
theorem flatMap_ofFn {α : Type*} {k : ℕ} (F : Fin k → α) (f : α → List Bool) :
    (List.ofFn F).flatMap f = (List.ofFn fun i => f (F i)).flatten := by
  rw [List.flatMap_def, List.map_ofFn]
  rfl

/-- **Masking the canonical history at answer width `l`**: the pre-processor on the encoded
history `((ρ_j, g ρ_j))_j` with the mask `maskOfOut n v` outputs the encoded tuple
`(ρ_j, v_j ⊕ g(ρ_j))_j`: `preFun ⟨⟨encodeHist …, P⟩, ⟨maskOfOut n v, u⟩⟩ =
(List.ofFn fun j => ⟨⟨⟦ρ j⟧, ⟦v j + g (ρ j)⟧⟩, []⟩).flatten` (`zipWith_xor_flatten_ofFn`,
`zipWith_xor_histBlockOut_maskBlockOut`). -/
theorem preFun_encodeHistOut {n l k : ℕ} (ρ : Fin k → Fin n → Bool) (v : Fin k → Fin l → Bool)
    (g : (Fin n → Bool) → (Fin l → Bool)) (P u : List Bool) :
    preFun (pairEncode (pairEncode (encodeHist (List.ofFn fun i => (ρ i, g (ρ i)))) P)
        (pairEncode (maskOfOut n v) u)) =
      (List.ofFn fun j =>
        pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v j + g (ρ j)))) []).flatten := by
  simp only [preFun, pairFstD_pairEncode, pairSndD_pairEncode, encodeHist_eq_flatMapOut,
    maskOfOut, flatMap_ofFn]
  rw [zipWith_xor_flatten_ofFn _ _ fun j => by rw [length_histBlockOut, length_maskBlockOut]]
  exact congrArg List.flatten (congrArg List.ofFn (funext fun j =>
    zipWith_xor_histBlockOut_maskBlockOut (ρ j) (g (ρ j)) (v j)))

/-- **Masking the canonical history**: the pre-processor on the encoded history
`((ρ_j, g ρ_j))_j` with the mask of `v` outputs the encoded ciphertext tuple
`(ρ_j, v_j ⊕ g(ρ_j))_j` (`zipWith_xor_flatten_ofFn`, `zipWith_xor_histBlock_maskBlock`). -/
theorem preFun_encodeHist {n k : ℕ} (ρ v : Fin k → Fin n → Bool)
    (g : (Fin n → Bool) → (Fin n → Bool)) (P u : List Bool) :
    preFun (pairEncode (pairEncode (encodeHist (List.ofFn fun i => (ρ i, g (ρ i)))) P)
        (pairEncode (maskOf v) u)) =
      (List.ofFn fun j =>
        pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v j + g (ρ j)))) []).flatten := by
  rw [maskOf_eq_maskOfOut]
  exact preFun_encodeHistOut ρ v g P u

/-- **The next-query machine of Thm-99.2.1 at answer width `ℓ(n)`** ([PS10, Theorem 99.2, proof,
with `ℓ`-bit outputs]): for a non-uniform PPT `D`, a budget polynomial `q` and masks
`v n ∈ ({0,1}^{ℓ(n)})^{q(n)+1}`, there is a non-uniform PPT `B` whose coins at `n` are, up to a
bijection `φ`, the `q(n) + 1` points `ρ` and the coins `c` of `D`, such that for every oracle
`g : {0,1}^n → {0,1}^{ℓ(n)}`,
`(B.toOracleAdversary n n ℓ(n) (q(n) + 1) (φ (ρ, c))).eval g =
decide (D.runAt n ⟦(⟨⟨ρ_j, v_j ⊕ g(ρ_j)⟩, []⟩)_j⟧ c = [true])`.

**Proof sketch.** As `exists_queryChain_nuppt`, with the string layer at answer width `ℓ(n)`:
`B` is `exists_split` (the first `(q(n)+1) n` coins are the points) of `exists_withAdvice` (advice
`⟨maskOfOut n (v n), 1^{q(n)+1}⟩`, bound `adviceBoundOut q ℓ`) of `exists_seq` of `D ∘ preFun`
and the uniform machine of `postFunOut ℓ`. On the encoded history of `k` blocks of
`4n + 2ℓ(n) + 6` bits the post-processor asks `ρ_k` while `k ≤ q(n)`, and then outputs `D`'s
verdict on the masked history (`postFunOut_layout`, `take_drop_ofFn_blocks`,
`preFun_encodeHistOut`); `buildTree` is evaluated by induction on the remaining budget along the
canonical history `((ρ_i, g ρ_i))_i`. -/
theorem exists_queryChainOut_nuppt (D : NUPPT) (q ℓ : PolyExpr)
    (v : ∀ n, Fin (q.eval n + 1) → Fin (ℓ.eval n) → Bool) :
    ∃ B : NUPPT, ∀ n, ∃ φ : (Fin (q.eval n + 1) → Fin n → Bool) × D.Coins n ≃ B.Coins n,
      ∀ (g : (Fin n → Bool) → (Fin (ℓ.eval n) → Bool))
        (ρ : Fin (q.eval n + 1) → Fin n → Bool) (c : D.Coins n),
        (B.toOracleAdversary n n (ℓ.eval n) (q.eval n + 1) (φ (ρ, c))).eval g =
          decide (D.runAt n (List.ofFn fun j =>
            pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v n j + g (ρ j)))) []).flatten c =
              [true]) := by
  classical
  have hβ : ∀ n, (pairEncode (maskOfOut n (v n)) (List.replicate (q.eval n + 1) true)).length ≤
      (adviceBoundOut q ℓ).eval n := by
    intro n
    rw [length_pairEncode, length_maskOfOut, List.length_replicate, eval_adviceBoundOut]
  obtain ⟨D₁, hD₁c, -, -, hD₁⟩ := D.exists_comp polyTimeComputable_preFun polyTimeComputable_id
  obtain ⟨C, hCc, -, hC⟩ :=
    D₁.exists_seq (NUPPT.ofPolyTimeUniform (polyTimeComputable_postFunOut ℓ) (.const 0))
  obtain ⟨C₂, hC₂c, hC₂⟩ := C.exists_withAdvice
    (fun n => pairEncode (maskOfOut n (v n)) (List.replicate (q.eval n + 1) true))
    (adviceBoundOut q ℓ) hβ
  obtain ⟨B, hBc, -, hB⟩ := C₂.exists_split (.mul (.add q (.const 1)) .var)
  refine ⟨B, fun n => ?_⟩
  have hlen : B.coinLen n = (q.eval n + 1) * n + D.coinLen n := by
    simp only [NUPPT.coinLen_eq, hBc, hC₂c, hCc, hD₁c, NUPPT.coins_ofPolyTimeUniform,
      PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var, Nat.add_zero]
  let φ : (Fin (q.eval n + 1) → Fin n → Bool) × D.Coins n ≃ B.Coins n :=
    ((FunFamily.blocks (q.eval n + 1) n).symm.prodCongr (Equiv.refl (D.Coins n))).trans
      ((Fin.appendEquiv _ _).trans (Equiv.arrowCongr (finCongr hlen.symm) (Equiv.refl Bool)))
  refine ⟨φ, fun g ρ c => ?_⟩
  set Pstr : List Bool := List.ofFn ((FunFamily.blocks (q.eval n + 1) n).symm ρ) with hPstr
  have hφ : φ (ρ, c) =
      fun i => Fin.append ((FunFamily.blocks (q.eval n + 1) n).symm ρ) c (Fin.cast hlen i) := by
    funext i
    rfl
  have hcoins : List.ofFn (φ (ρ, c)) = Pstr ++ List.ofFn c := by
    rw [hφ, hPstr, ← List.ofFn_fin_append]
    exact (List.ofFn_congr hlen.symm _).symm
  -- the activation of `B` on an encoded history
  have hD₁len : D₁.coinLen n = D.coinLen n := by simp only [NUPPT.coinLen_eq, hD₁c]
  have hrun : ∀ hist : List ((Fin n → Bool) × (Fin (ℓ.eval n) → Bool)),
      B.runAt n (encodeHist hist) (φ (ρ, c)) =
        postFunOut ℓ (NUPPT.layout (List.replicate n true)
          (pairEncode (pairEncode (pairEncode (encodeHist hist) Pstr)
              (pairEncode (maskOfOut n (v n)) (List.replicate (q.eval n + 1) true)))
            (D.runAt n (preFun (pairEncode (pairEncode (encodeHist hist) Pstr)
              (pairEncode (maskOfOut n (v n)) (List.replicate (q.eval n + 1) true)))) c))
          [] []) := by
    intro hist
    have hp : (PolyExpr.mul (.add q (.const 1)) .var).eval n = (q.eval n + 1) * n := by
      simp only [PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const, PolyExpr.eval_var]
    have hPlen : Pstr.length = (q.eval n + 1) * n := by simp [hPstr]
    have hclen : (List.ofFn c).length = D.coinLen n := by simp
    rw [NUPPT.runAt_eq, hcoins, hB, hp, List.take_left' hPlen, List.drop_left' hPlen]
    have hC₂' := hC₂ n (pairEncode (encodeHist hist) Pstr) (List.ofFn c)
    simp only at hC₂'
    rw [hC₂', hC, hD₁len, List.take_of_length_le hclen.le, List.drop_of_length_le hclen.le, hD₁,
      NUPPT.runAtL_ofPolyTimeUniform]
    simp only [NUPPT.layout_eq, NUPPT.advInput_eq, NUPPT.runAt_eq, id_eq]
  -- the canonical history along the points `ρ` against the oracle `g`
  let ρ' : ℕ → Fin n → Bool := fun i => if h : i < q.eval n + 1 then ρ ⟨i, h⟩ else fun _ => false
  let hist : ℕ → List ((Fin n → Bool) × (Fin (ℓ.eval n) → Bool)) :=
    fun k => List.ofFn fun i : Fin k => (ρ' i, g (ρ' i))
  have hρ' : ∀ (i : ℕ) (hi : i < q.eval n + 1), ρ' i = ρ ⟨i, hi⟩ := fun i hi => dif_pos hi
  have hist_len : ∀ k, (hist k).length = k := fun k => List.length_ofFn
  have hist_succ : ∀ k, hist (k + 1) = hist k ++ [(ρ' k, g (ρ' k))] := by
    intro k
    simp only [hist]
    rw [List.ofFn_succ', List.concat_eq_append]
    simp only [Fin.coe_castSucc, Fin.val_last]
  have hist_top :
      hist (q.eval n + 1) = List.ofFn fun i : Fin (q.eval n + 1) => (ρ i, g (ρ i)) := by
    simp only [hist]
    congr 1
    funext i
    rw [hρ' i i.isLt]
  -- the next-query function of `B`
  set next : List ((Fin n → Bool) × (Fin (ℓ.eval n) → Bool)) → OracleMove n :=
    fun h => decodeOracleMove n (B.runAt n (encodeHist h) (φ (ρ, c))) with hnext
  have hquery : ∀ k (hk : k < q.eval n + 1), next (hist k) = .query (ρ ⟨k, hk⟩) := by
    intro k hk
    simp only [hnext]
    rw [hrun, postFunOut_layout, hist_len, if_neg (by simp; omega), hPstr,
      take_drop_ofFn_blocks _ k hk, Equiv.apply_symm_apply, decodeOracleMove_query]
  have hret : next (hist (q.eval n + 1)) =
      .ret (decide (D.runAt n (List.ofFn fun j =>
        pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v n j + g (ρ j)))) []).flatten c =
          [true])) := by
    simp only [hnext]
    rw [hrun, postFunOut_layout, hist_len, if_pos (by simp), hist_top, preFun_encodeHistOut,
      decodeOracleMove_ret]
  -- evaluation of the tree by induction on the remaining budget
  have main : ∀ j, j ≤ q.eval n + 1 →
      (buildTree next j (hist (q.eval n + 1 - j))).eval g =
        decide (D.runAt n (List.ofFn fun j =>
          pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v n j + g (ρ j)))) []).flatten c =
            [true]) := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [Nat.sub_zero, buildTree_zero_of_ret hret, QueryTree.eval_ret]
    | succ j ih =>
      intro hj
      have hk : q.eval n + 1 - (j + 1) < q.eval n + 1 := by omega
      rw [buildTree_succ_of_query (hquery _ hk), QueryTree.eval_query, ← hρ' _ hk, ← hist_succ,
        show q.eval n + 1 - (j + 1) + 1 = q.eval n + 1 - j by omega]
      exact ih (by omega)
  have h0 : hist 0 = [] := rfl
  have := main (q.eval n + 1) le_rfl
  rw [Nat.sub_self, h0] at this
  rw [NUPPT.toOracleAdversary_eq]
  exact this

/-- **The one-query next-query machine at answer width `ℓ(n)`** ([PS10, Definition 96.2,
clause (2), with `ℓ`-bit outputs]): for a non-uniform PPT `D` there is a non-uniform PPT `B`
whose coins at `n` are, up to a bijection `φ`, a point `r ∈ {0,1}^n` and the coins `c` of `D`,
such that for every oracle `g : {0,1}^n → {0,1}^{ℓ(n)}`, with the budget `1`,
`(B.toOracleAdversary n n ℓ(n) 1 (φ (r, c))).eval g = decide (D.runAt n ⟨⟦r⟧, ⟦g r⟧⟩ c = [true])`.

**Proof sketch.** `exists_queryChainOut_nuppt` with `q = 0`, the zero mask, and `D` precomposed
with `pairFstD` (`NUPPT.exists_comp`): the encoded one-entry tuple is `⟨⟨⟦r⟧, ⟦g r⟧⟩, []⟩`, whose
first component is `⟨⟦r⟧, ⟦g r⟧⟩`. The coins are `r` read as the one-point tuple
(`Equiv.funUnique`, `finCongr`) and `D`'s coins carried to the composite (`NUPPT.coinsCongr`);
the budget `(const 0)(n) + 1` is `1` (`PolyExpr.eval_const`). -/
theorem exists_oneQuery_nuppt (D : NUPPT) (ℓ : PolyExpr) :
    ∃ B : NUPPT, ∀ n, ∃ φ : (Fin n → Bool) × D.Coins n ≃ B.Coins n,
      ∀ (g : (Fin n → Bool) → (Fin (ℓ.eval n) → Bool)) (r : Fin n → Bool) (c : D.Coins n),
        (B.toOracleAdversary n n (ℓ.eval n) 1 (φ (r, c))).eval g =
          decide (D.runAt n (pairEncode (List.ofFn r) (List.ofFn (g r))) c = [true]) := by
  obtain ⟨D₁, hD₁c, -, -, hD₁⟩ :=
    D.exists_comp polyTimeComputable_pairFstD polyTimeComputable_id
  obtain ⟨B, hB⟩ := exists_queryChainOut_nuppt D₁ (.const 0) ℓ fun _ _ => 0
  refine ⟨B, fun n => ?_⟩
  obtain ⟨φ, hφ⟩ := hB n
  have h1 : 1 = (PolyExpr.const 0).eval n + 1 := by rw [PolyExpr.eval_const]
  let e : (Fin n → Bool) ≃ (Fin ((PolyExpr.const 0).eval n + 1) → Fin n → Bool) :=
    (Equiv.funUnique (Fin 1) (Fin n → Bool)).symm.trans
      (Equiv.arrowCongr (finCongr h1) (Equiv.refl _))
  have he : ∀ (r : Fin n → Bool) j, e r j = r := fun r j => rfl
  refine ⟨(e.prodCongr (NUPPT.coinsCongr hD₁c.symm n)).trans φ, fun g r c => ?_⟩
  -- the budget `1` is `(const 0)(n) + 1`
  have hbud : ∀ (m : ℕ), m = (PolyExpr.const 0).eval n + 1 → ∀ x : B.Coins n,
      (B.toOracleAdversary n n (ℓ.eval n) m x).eval g =
        (B.toOracleAdversary n n (ℓ.eval n) ((PolyExpr.const 0).eval n + 1) x).eval g := by
    rintro m rfl x
    rfl
  rw [hbud 1 h1, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply, hφ]
  congr 2
  -- the one-entry tuple, read by `pairFstD`
  rw [NUPPT.runAt_coinsCongr, hD₁, id_eq, ← NUPPT.runAt_eq]
  congr 1
  have hnil : ∀ (f : Fin ((PolyExpr.const 0).eval n) → List Bool), List.ofFn f = [] :=
    fun f => List.eq_nil_of_length_eq_zero (by rw [List.length_ofFn, PolyExpr.eval_const])
  rw [List.ofFn_succ, hnil, List.flatten_cons, List.flatten_nil, List.append_nil,
    pairFstD_pairEncode, he, zero_add]

/-- **The next-query machine of Thm-99.2.1** ([PS10, Theorem 99.2, proof, "`H¹` and `H²` …
by closure under efficient operations we contradict the pseudorandomness property"]): for a
non-uniform PPT `D` (a distinguisher of encoded ciphertext tuples), a budget polynomial `q` and
message vectors `v n ∈ ({0,1}^n)^{q(n)+1}`, there is a non-uniform PPT `B` whose coins at `n`
are, up to a bijection `φ`, the `q(n) + 1` points `ρ` and the coins `c` of `D`, and whose
query tree with budget `q(n) + 1`, evaluated against any oracle `g`, gives `D`'s verdict on the
encoded tuple `(ρ_j, v_j ⊕ g(ρ_j))_j` with coins `c` (an equality of outputs; the sequence of
queries is not part of the statement).

**Proof sketch.** The case `ℓ = var` of `exists_queryChainOut_nuppt`. -/
theorem exists_queryChain_nuppt (D : NUPPT) (q : PolyExpr)
    (v : ∀ n, Fin (q.eval n + 1) → Fin n → Bool) :
    ∃ B : NUPPT, ∀ n, ∃ φ : (Fin (q.eval n + 1) → Fin n → Bool) × D.Coins n ≃ B.Coins n,
      ∀ (g : (Fin n → Bool) → (Fin n → Bool)) (ρ : Fin (q.eval n + 1) → Fin n → Bool)
        (c : D.Coins n),
        (B.toOracleAdversary n n n (q.eval n + 1) (φ (ρ, c))).eval g =
          decide (D.runAt n (List.ofFn fun j =>
            pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v n j + g (ρ j)))) []).flatten c =
              [true]) :=
  exists_queryChainOut_nuppt D q .var v

end TCSlib.Cryptography.MultiMsg
