/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.PRF
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Proof infrastructure for the multi-message encryption theorem

The lemmas behind the proofs of `TCSlib/Cryptography/Asymptotic/MultiMessage.lean`
([PS10, Theorem 99.2]), kept in a sibling file so that the statements file stays short:

* **Probability.** The coupling bound `abs_uexp_sub_le_uprob` ("two `[0,1]`-valued
  functions that agree outside an event `E` have averages within `Pr[E]`"), the count of
  pairs `i < j` in `Fin k × Fin k` (`card_filter_lt_pairs`, the `C(k, 2)` of the birthday
  bound), the probability `1 / |α|` that two independent uniform elements coincide
  (`uprob_eq_pair`), and the negligibility of the collision term `C(q(n)+1, 2) · 2^{−n}`
  (`negligible_choose_div_two_pow`).
* **Strings.** The encoded history `encodeHist` is a concatenation of self-delimited
  chunks (`encodeHist_eq_flatMap`);
  the history of a next-query machine with `n`-bit queries and answers consists of blocks of
  the fixed length `6n + 6` (`histBlock`, `length_histBlock`), which the block map of
  `Complexity.polyTimeComputable_blockMap` reads off (`flatMap_range_blocks`); masking a
  history block with the mask block of a message replaces the recorded answer `y` by
  `m ⊕ y` (`zipWith_xor_histBlock_maskBlock`).
* **Machines.** The next-query machine of Thm-99.2.1 (`exists_queryChain_nuppt`): a
  non-uniform PPT whose query tree with budget `q(n) + 1` asks the `q(n) + 1` points read
  from its coins and outputs the verdict of the given distinguisher `D` on the ciphertext
  tuple `(r_j, m_j ⊕ ans_j)_j`, the messages `m` hard-wired as advice. Its raw functions
  `preFun` (the mask) and `postFun` (the move) are built from the FP calculus and the closure
  catalogue of `TCSlib/Complexity/Randomized/Closure.lean`.
* **Oracle adversaries.** Relabelling the coins of an oracle adversary by a bijection
  preserves its PRF advantage (`prfAdv_congr_equiv`).

## Main definitions

* `TCSlib.Cryptography.MultiMsg.histBlock`, `TCSlib.Cryptography.MultiMsg.maskBlock` — the
  block of a history entry and the mask block of a message.
* `TCSlib.Cryptography.MultiMsg.preFun`, `TCSlib.Cryptography.MultiMsg.postFun` — the raw
  string functions of the next-query machine of Thm-99.2.1.

## Main results

* `TCSlib.Cryptography.MultiMsg.abs_uexp_sub_le_uprob` — the coupling bound.
* `TCSlib.Cryptography.MultiMsg.card_filter_lt_pairs` — `#{(i, j) | i < j} = C(k, 2)`.
* `TCSlib.Cryptography.MultiMsg.negligible_choose_div_two_pow` — the collision term is
  negligible.
* `TCSlib.Cryptography.MultiMsg.flatMap_range_blocks` — the block map on a concatenation of
  equal-length chunks.
* `TCSlib.Cryptography.MultiMsg.zipWith_xor_histBlock_maskBlock` — masking a history block.
* `TCSlib.Cryptography.MultiMsg.exists_queryChain_nuppt` — the next-query machine of
  Thm-99.2.1 and its query tree.
* `TCSlib.Cryptography.MultiMsg.prfAdv_congr_equiv` — coin relabelling preserves `prfAdv`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.9: Algorithm 99.1, Theorem 99.2.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4 (oracle adversaries, `prfAdv`).
-/

namespace TCSlib.Cryptography.MultiMsg

open Complexity Turing Finset

/-! ### Probability: coupling, pair counting, the collision term -/

/-- The absolute value of an average is at most the average of the absolute values. -/
theorem abs_uexp_le_uexp_abs {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) :
    |uexp f| ≤ uexp fun ω => |f ω| := by
  unfold uexp
  rw [abs_div, Nat.abs_cast]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)

/-- **The coupling bound**: two `[0,1]`-valued functions on a finite sample space that agree
outside the event `E` have averages at most `Pr[E]` apart (the "two experiments that agree
on an event `E` have advantage `≤ Pr[¬E]`" step of [PS10, Theorem 99.2, proof, `H²` vs `H³`]).

**Proof sketch.** `|E a − E b| = |E (a − b)| ≤ E |a − b|` (`abs_uexp_le_uexp_abs`), and
pointwise `|a − b| ≤ [E]` since the difference vanishes off `E` and is at most `1` on it. -/
theorem abs_uexp_sub_le_uprob {Ω : Type*} [Fintype Ω] (a b : Ω → ℝ) (E : Ω → Prop)
    [DecidablePred E] (ha : ∀ ω, 0 ≤ a ω ∧ a ω ≤ 1) (hb : ∀ ω, 0 ≤ b ω ∧ b ω ≤ 1)
    (heq : ∀ ω, ¬ E ω → a ω = b ω) :
    |uexp a - uexp b| ≤ uprob E := by
  rw [← HardcoreBit.uexp_sub, uprob_eq_uexp]
  refine (abs_uexp_le_uexp_abs _).trans (HardcoreBit.uexp_mono fun ω => ?_)
  by_cases hE : E ω
  · rw [if_pos hE]
    obtain ⟨h1, h2⟩ := ha ω
    obtain ⟨h3, h4⟩ := hb ω
    exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  · rw [if_neg hE, heq ω hE, sub_self, abs_zero]

/-- **Counting the pairs `i < j`**: there are `C(k, 2)` pairs `(i, j)` with `i < j` in
`Fin k × Fin k` (the `C(q(n)+1, 2)` of the birthday bound of [PS10, Theorem 99.2]).

**Proof sketch.** The pairs `i < j` and their swaps partition the off-diagonal of
`Fin k × Fin k`, which has `k² − k` elements (`Finset.offDiag_card`); the swap is injective,
so `2 · #{i < j} = k(k − 1)` and `Nat.choose_two_right` finishes. -/
theorem card_filter_lt_pairs (k : ℕ) :
    ((univ : Finset (Fin k × Fin k)).filter fun p => p.1 < p.2).card = k.choose 2 := by
  set S := (univ : Finset (Fin k × Fin k)).filter fun p => p.1 < p.2 with hS
  have hunion : S ∪ S.image Prod.swap = (univ : Finset (Fin k)).offDiag := by
    ext ⟨i, j⟩
    simp only [S, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, Finset.mem_offDiag, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq]
    constructor
    · rintro (h | ⟨a, b, hab, rfl, rfl⟩)
      · exact ne_of_lt h
      · exact ne_of_gt hab
    · intro hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl h
      · exact Or.inr ⟨j, i, h, rfl, rfl⟩
  have hdisj : Disjoint S (S.image Prod.swap) := by
    rw [Finset.disjoint_left]
    rintro ⟨i, j⟩ hij hji
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hij
    simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Prod.exists,
      Prod.swap_prod_mk, Prod.mk.injEq] at hji
    obtain ⟨a, b, hab, rfl, rfl⟩ := hji
    exact absurd hij (not_lt.2 hab.le)
  have hcard := congrArg Finset.card hunion
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ Prod.swap_injective,
    Finset.offDiag_card, Finset.card_univ, Fintype.card_fin] at hcard
  rw [Nat.choose_two_right, Nat.mul_sub_one]
  omega

/-- Two independent uniform elements of a nonempty finite type coincide with probability
`1 / |α|` (Fubini and `OneWay.uprob_eq_one_div_card`). -/
theorem uprob_eq_pair {α : Type*} [Fintype α] [Nonempty α] :
    uprob (fun z : α × α => z.1 = z.2) = 1 / Fintype.card α := by
  rw [uprob_prod]
  have h : ∀ a : α, uprob (fun b : α => a = b) = 1 / Fintype.card α := by
    intro a
    rw [← OneWay.uprob_eq_one_div_card a]
    exact uprob_congr fun b => eq_comm
  simp_rw [h]
  exact HardcoreBit.uexp_const _

/-- **The collision term is negligible**: `n ↦ C(q(n)+1, 2) / 2^n` is negligible for every
syntactic polynomial `q` ([PS10, Theorem 99.2, proof: the collision probability is
negligible]).

**Proof sketch.** `C(k, 2) ≤ k²` (`Nat.choose_le_pow`) and `q(n) + 1 ≤ (C+1)(n+1)^c ≤
(C+1) 2^c n^c` for `n ≥ 1` (`PolyExpr.eval_le`), so the term is at most a constant times
`n^{2c} · 2^{−n}`, negligible by `negligible_two_pow_neg`, `Negligible.mul_pow` and
`Negligible.const_mul`; conclude with `Negligible.mono`. -/
theorem negligible_choose_div_two_pow (q : PolyExpr) :
    Negligible fun n => (Nat.choose (q.eval n + 1) 2 : ℝ) / 2 ^ n := by
  obtain ⟨C, c, hC⟩ := q.eval_le
  have hν : Negligible fun n =>
      ((((C + 1) * 2 ^ c) ^ 2 : ℕ) : ℝ) * ((n : ℝ) ^ (2 * c) * (2 : ℝ)⁻¹ ^ n) :=
    (negligible_two_pow_neg.mul_pow (2 * c)).const_mul _
  refine hν.mono ⟨1, fun n hn => ?_⟩
  have hnat : Nat.choose (q.eval n + 1) 2 ≤ ((C + 1) * 2 ^ c) ^ 2 * n ^ (2 * c) := by
    have h1 : q.eval n + 1 ≤ (C + 1) * (n + 1) ^ c := by
      have := hC n
      have hp : 1 ≤ (n + 1) ^ c := Nat.one_le_pow _ _ (Nat.succ_pos n)
      nlinarith
    have h2 : (n + 1) ^ c ≤ (2 * n) ^ c := Nat.pow_le_pow_left (by omega) c
    calc Nat.choose (q.eval n + 1) 2 ≤ (q.eval n + 1) ^ 2 := Nat.choose_le_pow _ _
      _ ≤ ((C + 1) * (2 * n) ^ c) ^ 2 :=
          Nat.pow_le_pow_left (h1.trans (Nat.mul_le_mul_left _ h2)) 2
      _ = ((C + 1) * 2 ^ c) ^ 2 * n ^ (2 * c) := by ring
  have hR : (Nat.choose (q.eval n + 1) 2 : ℝ) ≤
      ((((C + 1) * 2 ^ c) ^ 2 : ℕ) : ℝ) * (n : ℝ) ^ (2 * c) := by
    exact_mod_cast hnat
  have hinv : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ n := by positivity
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity), div_eq_mul_inv, ← inv_pow]
  calc (Nat.choose (q.eval n + 1) 2 : ℝ) * (2 : ℝ)⁻¹ ^ n
      ≤ ((((C + 1) * 2 ^ c) ^ 2 : ℕ) : ℝ) * (n : ℝ) ^ (2 * c) * (2 : ℝ)⁻¹ ^ n :=
        mul_le_mul_of_nonneg_right hR hinv
    _ = _ := by ring

/-! ### Oracle adversaries: coin relabelling -/

/-- Relabelling the coins of an oracle adversary by a bijection preserves its acceptance
probability against every oracle sampler, provided the two trees agree on every oracle. -/
theorem acceptProb_oracleDist_congr_equiv {σ I O ρ ρ' : Type*} [Fintype σ] [Fintype ρ]
    [Fintype ρ'] (X : σ → I → O) (A : OracleAdversary ρ I O) (A' : OracleAdversary ρ' I O)
    (φ : ρ' ≃ ρ) (h : ∀ (g : I → O) (w : ρ'), (A (φ w)).eval g = (A' w).eval g) :
    acceptProb X (oracleDist A) = acceptProb X (oracleDist A') := by
  unfold acceptProb oracleDist
  rw [← uprob_comp_equiv ((Equiv.refl σ).prodCongr φ)]
  congr 1
  funext z
  simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.refl_apply, h]

/-- **Coin relabelling preserves the PRF advantage**: oracle adversaries whose trees agree on
every oracle after a bijective relabelling of the coins have the same `prfAdv`. -/
theorem prfAdv_congr_equiv {K I O ρ ρ' : Type*} [Fintype K] [Fintype I] [DecidableEq I]
    [Fintype O] [Fintype ρ] [Fintype ρ'] (F : K → I → O) (A : OracleAdversary ρ I O)
    (A' : OracleAdversary ρ' I O) (φ : ρ' ≃ ρ)
    (h : ∀ (g : I → O) (w : ρ'), (A (φ w)).eval g = (A' w).eval g) :
    prfAdv F A = prfAdv F A' := by
  unfold prfAdv distAdv
  rw [acceptProb_oracleDist_congr_equiv F A A' φ h,
    acceptProb_oracleDist_congr_equiv (randomFunction I O) A A' φ h]

/-! ### Strings: chunked encodings, history blocks, mask blocks -/

/-- The block contributed to an encoded history by one (query, answer) pair of `n`-bit
strings: the self-delimited chunk `⟨⟨x, y⟩, []⟩`. -/
def histBlock {n : ℕ} (p : (Fin n → Bool) × (Fin n → Bool)) : List Bool :=
  pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) []

/-- A history block of `n`-bit strings has length `6n + 6`. -/
theorem length_histBlock {n : ℕ} (p : (Fin n → Bool) × (Fin n → Bool)) :
    (histBlock p).length = 6 * n + 6 := by
  simp only [histBlock, length_pairEncode, List.length_ofFn, List.length_nil]
  omega

/-- The encoded history is the concatenation of its blocks. -/
theorem encodeHist_eq_flatMap {n : ℕ} : ∀ h : List ((Fin n → Bool) × (Fin n → Bool)),
    encodeHist h = h.flatMap histBlock
  | [] => rfl
  | p :: h => by
    show pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) (encodeHist h) = _
    rw [encodeHist_eq_flatMap h, List.flatMap_cons]
    simp [histBlock, pairEncode]

/-- The syntactic block length `6n + 6` of a history block. -/
def histBlockLen : PolyExpr := .add (.mul (.const 6) .var) (.const 6)

/-- Evaluating the block length. -/
theorem eval_histBlockLen (n : ℕ) : histBlockLen.eval n = 6 * n + 6 := rfl

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

/-- The two components of a history block: the query and the answer. -/
theorem pairFstD_pairFstD_histBlock {n : ℕ} (p : (Fin n → Bool) × (Fin n → Bool)) :
    pairFstD (pairFstD (histBlock p)) = List.ofFn p.1 := by
  simp [histBlock]

/-- The mask block of the message `w`: zeros under the (doubled) query and the separators,
`w` doubled under the (doubled) answer, so that `histBlock (x, y) ⊕ maskBlock w` is the
history block of `(x, w ⊕ y)`. -/
def maskBlock {n : ℕ} (w : Fin n → Bool) : List Bool :=
  List.replicate (4 * n + 4) false ++ dbl (List.ofFn w) ++ [false, false]

/-- A mask block has the length `6n + 6` of a history block. -/
theorem length_maskBlock {n : ℕ} (w : Fin n → Bool) : (maskBlock w).length = 6 * n + 6 := by
  simp only [maskBlock, List.length_append, List.length_replicate, length_dbl, List.length_ofFn,
    List.length_cons, List.length_nil]
  omega

/-- Doubling distributes over concatenation. -/
theorem dbl_append (a b : List Bool) : dbl (a ++ b) = dbl a ++ dbl b :=
  List.flatMap_append

/-- Masking with zeros is the identity. -/
theorem zipWith_xor_replicate_false : ∀ l : List Bool,
    List.zipWith xor l (List.replicate l.length false) = l
  | [] => rfl
  | a :: l => by
    rw [List.length_cons, List.replicate_succ, List.zipWith_cons_cons, zipWith_xor_replicate_false l,
      Bool.xor_false]

/-- The string exclusive-or of two `n`-bit strings is the encoding of their sum in the Boolean
group `Fin n → Bool` (`+` on `Bool` is `xor`). -/
theorem zipWith_xor_ofFn_eq_add {n : ℕ} (a b : Fin n → Bool) :
    List.zipWith xor (List.ofFn a) (List.ofFn b) = List.ofFn (a + b) := by
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp only [List.getElem_zipWith, List.getElem_ofFn, Pi.add_apply]
  cases a ⟨i, by simpa using h₂⟩ <;> cases b ⟨i, by simpa using h₂⟩ <;> rfl

/-- Exclusive-or commutes with doubling. -/
theorem zipWith_xor_dbl : ∀ a b : List Bool,
    List.zipWith xor (dbl a) (dbl b) = dbl (List.zipWith xor a b)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | x :: a, y :: b => by
    simp only [dbl_cons, List.zipWith_cons_cons, zipWith_xor_dbl a b]

/-- **Masking a history block**: the exclusive-or of the history block of `(x, y)` with the
mask block of `w` is the history block of `(x, w ⊕ y)` (strings `x, y, w` of the same length).

**Proof sketch.** `⟨⟨x, y⟩, []⟩ = dbl (dbl x) ++ 0011 ++ dbl y ++ 01`; the mask is
`0^{4n+4} ++ dbl w ++ 00`; `List.zipWith_append` splits the exclusive-or along these
segments, zeros are neutral (`zipWith_xor_replicate_false`) and `dbl y ⊕ dbl w = dbl (y ⊕ w)`
(`zipWith_xor_dbl`). -/
theorem zipWith_xor_histBlock_maskBlock {n : ℕ} (x y w : Fin n → Bool) :
    List.zipWith xor (histBlock (x, y)) (maskBlock w) =
      pairEncode (pairEncode (List.ofFn x) (List.ofFn (w + y))) [] := by
  have hyw : List.zipWith xor (List.ofFn y) (List.ofFn w) = List.ofFn (w + y) := by
    rw [zipWith_xor_ofFn_eq_add, add_comm]
  have h1 : histBlock (x, y) =
      (dbl (dbl (List.ofFn x)) ++ [false, false, true, true]) ++
        (dbl (List.ofFn y) ++ [false, true]) := by
    simp only [histBlock, pairEncode_eq_dbl, dbl_append, List.append_nil, List.append_assoc]
    rfl
  have h2 : maskBlock w =
      List.replicate (dbl (dbl (List.ofFn x)) ++ [false, false, true, true]).length false ++
        (dbl (List.ofFn w) ++ [false, false]) := by
    simp only [maskBlock, List.length_append, length_dbl, List.length_ofFn, List.length_cons,
      List.length_nil, List.append_assoc]
    congr 2
    omega
  rw [h1, h2, List.zipWith_append (List.length_replicate ..).symm, zipWith_xor_replicate_false,
    List.zipWith_append (by simp only [length_dbl, List.length_ofFn]), zipWith_xor_dbl, hyw]
  simp only [pairEncode_eq_dbl, dbl_append, List.append_nil, List.append_assoc]
  rfl

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
`FunFamily.blocks` (private copy of the lemma of `Asymptotic/EnsemblesLemmas.lean`). -/
theorem take_drop_ofFn_blocks {q s : ℕ} (w : Fin (q * s) → Bool) (i : ℕ) (hi : i < q) :
    ((List.ofFn w).drop (i * s)).take s = List.ofFn (FunFamily.blocks q s w ⟨i, hi⟩) := by
  have hle : i * s + s ≤ q * s := by
    rw [← Nat.succ_mul]
    exact Nat.mul_le_mul_right s hi
  refine List.ext_getElem ?_ fun j h₁ h₂ => ?_
  · simp only [List.length_take, List.length_drop, List.length_ofFn]
    omega
  · simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    show w _ = w (finProdFinEquiv (⟨i, hi⟩, _))
    congr 1
    ext
    simp [finProdFinEquiv]
    ring

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
  simp [preFun, Function.comp]

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

/-- **The post-processing of the next-query machine** on the raw layout
`⟨⟨⟨1^n, ⟨⟨⟨H, ρ⟩, ⟨M, u⟩⟩, a⟩⟩, []⟩, r⟩`: if the history already has `|u|` blocks, the
verdict `[true, [a = [true]]]`; otherwise the query `⟨[false], ρ_k⟩` at the `k`-th point,
`k` the number of history blocks. -/
def postFun (z : List Bool) : List Bool :=
  if decide ((postBudget z).length ≤ (postCount z).length) = true then postVerdict z
  else postQuery z

/-- `postFun` is polynomial-time.

**Proof sketch.** Projections of the layout (`NUPPT.polyTimeComputable_inArg`,
`polyTimeComputable_pairFstD`/`pairSndD`), two block maps
(`Complexity.polyTimeComputable_blockMap`), the typed cuts
(`polyTimeComputable_pairTakePoly`/`pairDropPoly`), a length test
(`Complexity.StateLoop.lenLe_comp`), an equality test (`Complexity.polyTimeComputable_pairEq`)
and one branch (`Complexity.polyTimeComputable_ite`). -/
theorem polyTimeComputable_postFun : PolyTimeComputable postFun := by
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
  have hCount : PolyTimeComputable postCount :=
    (polyTimeComputable_blockMapFun histBlockLen (polyTimeComputable_const [true])).comp
      (hParam.pairEncode hHist)
  have hOffset : PolyTimeComputable postOffset :=
    (polyTimeComputable_blockMapFun histBlockLen
      (polyTimeComputable_unary.comp
        (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD))).comp
      (hParam.pairEncode hHist)
  have hQuery : PolyTimeComputable postQuery :=
    (polyTimeComputable_const [false]).pairEncode ((polyTimeComputable_pairTakePoly .var).comp
      (hParam.pairEncode ((polyTimeComputable_pairDropPoly .var).comp
        (hOffset.pairEncode hPoints))))
  have hVerdict : PolyTimeComputable postVerdict :=
    (polyTimeComputable_prepend [true]).comp
      (polyTimeComputable_pairEq.comp (hAns.pairEncode (polyTimeComputable_const [true])))
  exact polyTimeComputable_ite (StateLoop.lenLe_comp hCount hBudget) hVerdict hQuery

/-- The mask of a message vector: the concatenation of the mask blocks of its entries. -/
def maskOf {n k : ℕ} (v : Fin k → Fin n → Bool) : List Bool :=
  (List.ofFn fun j => maskBlock (v j)).flatten

/-- The length of a concatenation of strings of a common length `b`. -/
theorem length_flatten_of_length (b : ℕ) : ∀ L : List (List Bool),
    (∀ x ∈ L, x.length = b) → L.flatten.length = L.length * b
  | [], _ => by simp
  | x :: L, h => by
    rw [List.flatten_cons, List.length_append,
      length_flatten_of_length b L (fun y hy => h y (by simp [hy])), h x (by simp),
      List.length_cons]
    ring

/-- The length of the mask of `k` messages of `n` bits is `k (6n + 6)`. -/
theorem length_maskOf {n k : ℕ} (v : Fin k → Fin n → Bool) :
    (maskOf v).length = k * (6 * n + 6) := by
  unfold maskOf
  rw [length_flatten_of_length (6 * n + 6), List.length_ofFn]
  intro x hx
  obtain ⟨j, -, rfl⟩ := List.mem_ofFn.1 hx
  exact length_maskBlock _

/-- The advice bound of the next-query machine: `|⟨mask, 1^{q+1}⟩|`. -/
def adviceBound (q : PolyExpr) : PolyExpr :=
  .add (.add (.mul (.const 2) (.mul (.add q (.const 1)) histBlockLen)) (.const 2)) (.add q (.const 1))

/-- Decoding the well-formed query move `⟨[false], x⟩`. -/
theorem decodeOracleMove_query (ℓ : ℕ) (x : Fin ℓ → Bool) :
    decodeOracleMove ℓ (pairEncode [false] (List.ofFn x)) = .query x := by
  simp [decodeOracleMove, pairDecode_pairEncode, decodeFin_ofFn]

/-- Decoding the verdict move `[true, b]`. -/
theorem decodeOracleMove_ret (ℓ : ℕ) (b : Bool) : decodeOracleMove ℓ [true, b] = .ret b := by
  cases b <;> rfl

/-- **The post-processor on the layout of the composite machine**: for a history of `k` pairs
of `n`-bit strings, the points string `P`, a mask `M`, the budget string `u` and the
distinguisher's output `a`, the move is the verdict `[true, [a = [true]]]` when `|u| ≤ k` and
the query `⟨[false], P[k n, (k+1) n)⟩` otherwise.

**Proof sketch.** The projections of the layout read the slots; the two block maps on
`⟨1^n, encodeHist hist⟩` output `1^k` and `1^{k n}` (`encodeHist_eq_flatMap`,
`flatMap_range_blocks` with blocks of length `6n + 6`, `flatMap_const_singleton`,
`flatMap_const_replicate`); the typed cuts then select the block. -/
theorem postFun_layout {n : ℕ} (hist : List ((Fin n → Bool) × (Fin n → Bool)))
    (P M u a : List Bool) :
    postFun (NUPPT.layout (List.replicate n true)
        (pairEncode (pairEncode (pairEncode (encodeHist hist) P) (pairEncode M u)) a) [] []) =
      if u.length ≤ hist.length then [true, decide (a = [true])]
      else pairEncode [false] ((P.drop (hist.length * n)).take n) := by
  set z := NUPPT.layout (List.replicate n true)
    (pairEncode (pairEncode (pairEncode (encodeHist hist) P) (pairEncode M u)) a) [] [] with hz
  have harg : NUPPT.inArg z = pairEncode (pairEncode (pairEncode (encodeHist hist) P) (pairEncode M u)) a :=
    NUPPT.inArg_layout _ _ _ _
  have hpar : NUPPT.inParam z = List.replicate n true := NUPPT.inParam_layout _ _ _ _
  have hblocks : ∀ x ∈ hist, (histBlock x).length = 6 * n + 6 := fun x _ => length_histBlock x
  have hpos : 0 < 6 * n + 6 := by omega
  have hcount : postCount z = List.replicate hist.length true := by
    simp only [postCount, postHist, harg, hpar, pairFstD_pairEncode, pairSndD_pairEncode,
      blockMapFun, List.length_replicate, eval_histBlockLen, encodeHist_eq_flatMap]
    exact (flatMap_range_blocks histBlock (fun _ => [true]) hpos hist hblocks).trans
      (flatMap_const_singleton hist)
  have hoffset : postOffset z = List.replicate (hist.length * n) true := by
    simp only [postOffset, postHist, harg, hpar, pairFstD_pairEncode, pairSndD_pairEncode,
      blockMapFun, List.length_replicate, eval_histBlockLen, encodeHist_eq_flatMap]
    refine (flatMap_range_blocks histBlock
      (fun blk => List.replicate (pairFstD (pairFstD blk)).length true) hpos hist hblocks).trans ?_
    show hist.flatMap (fun x => List.replicate (pairFstD (pairFstD (histBlock x))).length true) = _
    simp only [pairFstD_pairFstD_histBlock, List.length_ofFn]
    exact flatMap_const_replicate n hist
  have hbudget : postBudget z = u := by
    simp only [postBudget, harg, pairFstD_pairEncode, pairSndD_pairEncode]
  have hans : postAns z = a := by
    simp only [postAns, harg, pairSndD_pairEncode]
  have hpoints : postPoints z = P := by
    simp only [postPoints, harg, pairFstD_pairEncode, pairSndD_pairEncode]
  simp only [postFun, hbudget, hcount, List.length_replicate]
  by_cases h : u.length ≤ hist.length
  · rw [if_pos (by simpa using h), if_pos h]
    simp only [postVerdict, hans, pairFstD_pairEncode, pairSndD_pairEncode]
    rfl
  · rw [if_neg (by simpa using h), if_neg h]
    simp only [postQuery, takePolyFun, dropPolyFun, hoffset, hpoints, hpar, pairFstD_pairEncode,
      pairSndD_pairEncode, List.length_replicate, PolyExpr.eval_var]

/-- Concatenating the chunks `f (F i)` of a tuple: `flatMap` over `ofFn`. -/
theorem flatMap_ofFn {α : Type*} {k : ℕ} (F : Fin k → α) (f : α → List Bool) :
    (List.ofFn F).flatMap f = (List.ofFn fun i => f (F i)).flatten := by
  rw [List.flatMap_def, List.map_ofFn]
  rfl

/-- **Masking the canonical history**: the pre-processor on the encoded history
`((ρ_j, g ρ_j))_j` with the mask of `v` outputs the encoded ciphertext tuple
`(ρ_j, v_j ⊕ g(ρ_j))_j` (`zipWith_xor_flatten_ofFn`, `zipWith_xor_histBlock_maskBlock`). -/
theorem preFun_encodeHist {n k : ℕ} (ρ v : Fin k → Fin n → Bool)
    (g : (Fin n → Bool) → (Fin n → Bool)) (P u : List Bool) :
    preFun (pairEncode (pairEncode (encodeHist (List.ofFn fun i => (ρ i, g (ρ i)))) P)
        (pairEncode (maskOf v) u)) =
      (List.ofFn fun j =>
        pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v j + g (ρ j)))) []).flatten := by
  simp only [preFun, pairFstD_pairEncode, pairSndD_pairEncode, encodeHist_eq_flatMap, maskOf,
    flatMap_ofFn]
  rw [zipWith_xor_flatten_ofFn _ _ fun j => by rw [length_histBlock, length_maskBlock]]
  exact congrArg List.flatten (congrArg List.ofFn (funext fun j =>
    zipWith_xor_histBlock_maskBlock (ρ j) (g (ρ j)) (v j)))

/-- **The next-query machine of Thm-99.2.1** ([PS10, Theorem 99.2, proof, "`H¹` and `H²` …
by closure under efficient operations we contradict the pseudorandomness property"]): for a
non-uniform PPT `D` (a distinguisher of encoded ciphertext tuples), a budget polynomial `q` and
message vectors `v n ∈ ({0,1}^n)^{q(n)+1}`, there is a non-uniform PPT `B` whose coins at `n`
are, up to a bijection `φ`, the `q(n) + 1` points `ρ` and the coins `c` of `D`, and whose
query tree with budget `q(n) + 1` run against any oracle `g` asks `ρ₀, …, ρ_{q(n)}` and
outputs `D`'s verdict on the encoded tuple `(ρ_j, v_j ⊕ g(ρ_j))_j` with coins `c`.

**Proof sketch.** `B` is `exists_split` (the first `(q(n)+1) n` coins are the points) of
`exists_withAdvice` (advice `⟨maskOf (v n), 1^{q(n)+1}⟩`) of `exists_seq` of `D ∘ preFun`
(`exists_comp`) and the uniform machine of `postFun`. On the encoded history `H` of `k`
blocks the post-processor asks `ρ_k` while `k ≤ q(n)` and otherwise outputs `[true, b]` with
`b` the verdict of `D` on `H ⊕ maskOf (v n)` (`postFun_layout`, `take_drop_ofFn_blocks`,
`preFun_encodeHist`). The tree `buildTree` from the empty history is evaluated by induction on
the remaining budget `j` along the canonical history `((ρ_i, g ρ_i))_{i < q(n)+1-j}`. -/
theorem exists_queryChain_nuppt (D : NUPPT) (q : PolyExpr)
    (v : ∀ n, Fin (q.eval n + 1) → Fin n → Bool) :
    ∃ B : NUPPT, ∀ n, ∃ φ : (Fin (q.eval n + 1) → Fin n → Bool) × D.Coins n ≃ B.Coins n,
      ∀ (g : (Fin n → Bool) → (Fin n → Bool)) (ρ : Fin (q.eval n + 1) → Fin n → Bool)
        (c : D.Coins n),
        (B.toOracleAdversary n n n (q.eval n + 1) (φ (ρ, c))).eval g =
          decide (D.runAt n (List.ofFn fun j =>
            pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v n j + g (ρ j)))) []).flatten c =
              [true]) := by
  classical
  have hβ : ∀ n, (pairEncode (maskOf (v n)) (List.replicate (q.eval n + 1) true)).length ≤
      (adviceBound q).eval n := by
    intro n
    simp only [length_pairEncode, length_maskOf, List.length_replicate, adviceBound,
      PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, eval_histBlockLen, le_refl]
  obtain ⟨D₁, hD₁c, -, -, hD₁⟩ := D.exists_comp polyTimeComputable_preFun polyTimeComputable_id
  obtain ⟨C, hCc, -, hC⟩ :=
    D₁.exists_seq (NUPPT.ofPolyTimeUniform polyTimeComputable_postFun (.const 0))
  obtain ⟨C₂, hC₂c, hC₂⟩ := C.exists_withAdvice
    (fun n => pairEncode (maskOf (v n)) (List.replicate (q.eval n + 1) true)) (adviceBound q) hβ
  obtain ⟨B, hBc, -, hB⟩ := C₂.exists_split (.mul (.add q (.const 1)) .var)
  refine ⟨B, fun n => ?_⟩
  have hlen : B.coinLen n = (q.eval n + 1) * n + D.coinLen n := by
    simp only [NUPPT.coinLen, hBc, hC₂c, hCc, hD₁c, NUPPT.coins_ofPolyTimeUniform,
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
  have hD₁len : D₁.coinLen n = D.coinLen n := by simp only [NUPPT.coinLen, hD₁c]
  have hrun : ∀ hist : List ((Fin n → Bool) × (Fin n → Bool)),
      B.runAt n (encodeHist hist) (φ (ρ, c)) =
        postFun (NUPPT.layout (List.replicate n true)
          (pairEncode (pairEncode (pairEncode (encodeHist hist) Pstr)
              (pairEncode (maskOf (v n)) (List.replicate (q.eval n + 1) true)))
            (D.runAt n (preFun (pairEncode (pairEncode (encodeHist hist) Pstr)
              (pairEncode (maskOf (v n)) (List.replicate (q.eval n + 1) true)))) c)) [] []) := by
    intro hist
    have hp : (PolyExpr.mul (.add q (.const 1)) .var).eval n = (q.eval n + 1) * n := rfl
    have hPlen : Pstr.length = (q.eval n + 1) * n := by simp [hPstr]
    have hclen : (List.ofFn c).length = D.coinLen n := by simp
    rw [NUPPT.runAt_eq, hcoins, hB, hp, List.take_left' hPlen, List.drop_left' hPlen]
    have hC₂' := hC₂ n (pairEncode (encodeHist hist) Pstr) (List.ofFn c)
    simp only at hC₂'
    rw [hC₂', hC, hD₁len, List.take_of_length_le hclen.le, List.drop_of_length_le hclen.le, hD₁,
      NUPPT.runAtL_ofPolyTimeUniform]
    rfl
  -- the canonical history along the points `ρ` against the oracle `g`
  let ρ' : ℕ → Fin n → Bool := fun i => if h : i < q.eval n + 1 then ρ ⟨i, h⟩ else fun _ => false
  let hist : ℕ → List ((Fin n → Bool) × (Fin n → Bool)) :=
    fun k => List.ofFn fun i : Fin k => (ρ' i, g (ρ' i))
  have hρ' : ∀ (i : ℕ) (hi : i < q.eval n + 1), ρ' i = ρ ⟨i, hi⟩ := fun i hi => dif_pos hi
  have hist_len : ∀ k, (hist k).length = k := fun k => List.length_ofFn
  have hist_succ : ∀ k, hist (k + 1) = hist k ++ [(ρ' k, g (ρ' k))] := by
    intro k
    simp only [hist]
    rw [List.ofFn_succ', List.concat_eq_append]
    simp only [Fin.coe_castSucc, Fin.val_last]
  have hist_top : hist (q.eval n + 1) = List.ofFn fun i : Fin (q.eval n + 1) => (ρ i, g (ρ i)) := by
    simp only [hist]
    congr 1
    funext i
    rw [hρ' i i.isLt]
  -- the next-query function of `B`
  set next : List ((Fin n → Bool) × (Fin n → Bool)) → OracleMove n :=
    fun h => decodeOracleMove n (B.runAt n (encodeHist h) (φ (ρ, c))) with hnext
  have hquery : ∀ k (hk : k < q.eval n + 1), next (hist k) = .query (ρ ⟨k, hk⟩) := by
    intro k hk
    simp only [hnext]
    rw [hrun, postFun_layout, hist_len, if_neg (by simp; omega), hPstr,
      take_drop_ofFn_blocks _ k hk, Equiv.apply_symm_apply, decodeOracleMove_query]
  have hret : next (hist (q.eval n + 1)) =
      .ret (decide (D.runAt n (List.ofFn fun j =>
        pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v n j + g (ρ j)))) []).flatten c =
          [true])) := by
    simp only [hnext]
    rw [hrun, postFun_layout, hist_len, if_pos (by simp), hist_top, preFun_encodeHist,
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
      rw [Nat.sub_zero, buildTree, hret]
      rfl
    | succ j ih =>
      intro hj
      have hk : q.eval n + 1 - (j + 1) < q.eval n + 1 := by omega
      rw [buildTree, hquery _ hk, QueryTree.eval_query, ← hρ' _ hk, ← hist_succ,
        show q.eval n + 1 - (j + 1) + 1 = q.eval n + 1 - j by omega]
      exact ih (by omega)
  have h0 : hist 0 = [] := rfl
  have := main (q.eval n + 1) le_rfl
  rw [Nat.sub_self, h0] at this
  exact this

end TCSlib.Cryptography.MultiMsg
