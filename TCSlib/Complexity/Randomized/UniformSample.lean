/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.RandomBits
import TCSlib.Complexity.Randomized.PolyTimeModel
import TCSlib.Complexity.ClassP.BinaryArith.Loops
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Nat.Log

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A uniform number in `[N]` from fair coins

[AB09, Exercise 7.1]: rejection sampling. Read `k` blocks of `L = ⌈log₂ N⌉` fair coins; output
the first block value below `N`, or `?` if there is none. Every value in `[N]` has the same
probability, so conditioned on not outputting `?` the output is uniform, and
`Pr[?] ≤ 2^{-k}`; with `k = ⌈log₂(1/δ)⌉` this is at most `δ`, using `k·L` coins. The procedure is
a polynomial-time word function of `⟨⟨N, 1^k⟩, coins⟩`.

## Main definitions

* `Randomized.uniformSample` — the procedure on `N`, `k` and a coin word (`none` is `?`).
* `Randomized.sampleCoins` — its coin count `k · ⌈log₂ N⌉`.
* `Randomized.uniformSampleAlg` — its word-level implementation on `⟨⟨N, 1^k⟩, r⟩`.

## Main results

* `Randomized.randProb_uniformSample_eq` — all values in `[N]` are equally likely.
* `Randomized.randProb_uniformSample_some_mul` — `Pr[i] · N = Pr[not ?]` (uniform given not `?`).
* `Randomized.randProb_uniformSample_none_le` — `Pr[?] ≤ 2^{-k}`.
* `Randomized.polyTimeComputable_uniformSampleAlg`, `Randomized.uniformSampleAlg_pairEncode`.
* `Randomized.uniformSample_spec` — [AB09, Exercise 7.1].

## Divergences

* Values are `0, …, N-1` (the book's `1, …, N` shifted by one) and `?` is `none`.
* "Running time `poly(log N · log(1/δ))`" is rendered as `PolyTimeComputable` of the procedure
  as a deterministic function of the input `⟨N in binary, 1^k⟩` and the `k·⌈log₂ N⌉` coins, the
  certificate view of [AB09, Def 7.3]; that input has length `O(log N + log(1/δ))`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open Finset Complexity Turing
open Complexity.LogProg (bitsVal bitsVal_bits)

/-! ### The procedure -/

/-- Rejection sampling with `k` tries of `L` coins each: the first block of `r` whose value is
below `N`, or `none`. -/
def sampleTries (N L : ℕ) : ℕ → List Bool → Option ℕ
  | 0, _ => none
  | k + 1, r => if bitsVal (r.take L) < N then some (bitsVal (r.take L))
      else sampleTries N L k (r.drop L)

/-- [AB09, Exercise 7.1]: a number in `[0, N)` from `k` blocks of `⌈log₂ N⌉ = size (N - 1)`
fair coins, or `none` (the book's `?`). -/
def uniformSample (N k : ℕ) (r : List Bool) : Option ℕ := sampleTries N (Nat.size (N - 1)) k r

/-- The number of coins `uniformSample N k` reads: `k · ⌈log₂ N⌉`. -/
def sampleCoins (N k : ℕ) : ℕ := k * Nat.size (N - 1)

/-- The tries read the blocks in order: `sampleTries` is the first block value below `N`. -/
theorem sampleTries_eq_find (N L k : ℕ) (r : List Bool) :
    sampleTries N L k r = (List.ofFn fun j : Fin k => blockVal L r j).find? (· < N) := by
  induction k generalizing r with
  | zero => rfl
  | succ k ih =>
    have h0 : blockVal L r 0 = bitsVal (r.take L) := by simp [blockVal]
    have hs : ∀ j : ℕ, blockVal L r (j + 1) = blockVal L (r.drop L) j := fun j => by
      simp only [blockVal, List.drop_drop, Nat.succ_mul]; rw [Nat.add_comm]
    rw [sampleTries, List.ofFn_succ, List.find?_cons, ih]
    simp only [Fin.val_zero, h0, Fin.val_succ, hs]
    split_ifs with h <;> simp [h]

/-- A sampled value is below `N`. -/
theorem lt_of_uniformSample_eq_some {N k : ℕ} {r : List Bool} {i : ℕ}
    (h : uniformSample N k r = some i) : i < N := by
  rw [uniformSample, sampleTries_eq_find] at h
  simpa using List.find?_some h

/-- `2^{⌈log₂ N⌉}` is at least `N` and below `2N`. -/
theorem le_two_pow_size_pred {N : ℕ} (hN : 1 ≤ N) :
    N ≤ 2 ^ Nat.size (N - 1) ∧ 2 ^ Nat.size (N - 1) < 2 * N := by
  refine ⟨by have := Nat.lt_size_self (N - 1); omega, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.size (N - 1)) with h | h
  · rw [h]; omega
  · have h2 : 2 ^ (Nat.size (N - 1) - 1) ≤ N - 1 := Nat.lt_size.mp (by omega)
    have : 2 ^ Nat.size (N - 1) = 2 * 2 ^ (Nat.size (N - 1) - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega

/-! ### The output distribution -/

/-- The events of `uniformSample` as events of the `k` block values. -/
theorem randProb_uniformSample (N k : ℕ) (P : Option ℕ → Prop) [DecidablePred P] :
    randProb (sampleCoins N k) (fun r => P (uniformSample N k r)) =
      (#{f ∈ Fintype.piFinset fun _ : Fin k => range (2 ^ Nat.size (N - 1)) |
        P ((List.ofFn f).find? (· < N))} : ℚ) / 2 ^ sampleCoins N k := by
  rw [sampleCoins, ← randProb_blocks_piFinset k (Nat.size (N - 1))
    (fun f => P ((List.ofFn f).find? (· < N)))]
  exact randProb_congr fun r => by rw [uniformSample, sampleTries_eq_find]

/-- **Uniformity** [AB09, Exercise 7.1 (1)]: any two values `i, j < N` are output with the
same probability.

**Proof sketch.** Swapping the values `i` and `j` in every block is a bijection of the block
tuples (both are below `N ≤ 2^L`) which preserves the test `· < N`, so it carries the tuples
whose first value below `N` is `j` onto those where it is `i`. -/
theorem randProb_uniformSample_eq {N k i j : ℕ} (hi : i < N) (hj : j < N) :
    randProb (sampleCoins N k) (fun r => uniformSample N k r = some i) =
      randProb (sampleCoins N k) (fun r => uniformSample N k r = some j) := by
  have hN : 1 ≤ N := by omega
  have hL := (le_two_pow_size_pred hN).1
  rw [randProb_uniformSample N k (fun o => o = some i),
    randProb_uniformSample N k (fun o => o = some j)]
  congr 2
  set σ := Equiv.swap i j
  have hlt : ∀ v, σ v < N ↔ v < N := fun v => by
    simp only [σ, Equiv.swap_apply_def]; split_ifs <;> simp_all
  have hrange : ∀ v, σ v < 2 ^ Nat.size (N - 1) ↔ v < 2 ^ Nat.size (N - 1) := fun v => by
    simp only [σ, Equiv.swap_apply_def]; split_ifs <;> subst_vars <;> omega
  have hp : ((fun x => decide (x < N)) ∘ σ) = fun x => decide (x < N) :=
    funext fun v => by simp [hlt]
  have hfind : ∀ f : Fin k → ℕ, (List.ofFn (σ ∘ f)).find? (fun x => decide (x < N)) =
      ((List.ofFn f).find? (fun x => decide (x < N))).map σ := fun f => by
    rw [← List.map_ofFn, List.find?_map, hp]
  refine Finset.card_equiv ((Equiv.refl (Fin k)).arrowCongr σ) fun f => ?_
  have he : ((Equiv.refl (Fin k)).arrowCongr σ) f = σ ∘ f := rfl
  simp only [mem_filter, Fintype.mem_piFinset, mem_range, he, hfind, Function.comp_apply, hrange]
  refine and_congr Iff.rfl ?_
  cases (List.ofFn f).find? (fun x => decide (x < N)) with
  | none => simp
  | some v =>
    simp only [Option.map_some, Option.some.injEq]
    constructor
    · rintro rfl; simp [σ]
    · intro h; simpa [σ] using congrArg σ h

/-- The probability of `?`: every block is at least `N`, i.e. `((2^L - N)/2^L)^k`. -/
theorem randProb_uniformSample_none (N k : ℕ) :
    randProb (sampleCoins N k) (fun r => uniformSample N k r = none) =
      (((2 ^ Nat.size (N - 1) - N : ℕ) : ℚ) / 2 ^ Nat.size (N - 1)) ^ k := by
  have h := randProb_forall_blocks k (Nat.size (N - 1)) (fun v => ¬ v < N)
  rw [randProb_bitsVal (Nat.size (N - 1)) (fun v => ¬ v < N)] at h
  rw [sampleCoins, randProb_congr (B := fun s => ∀ j : Fin k,
    ¬ blockVal (Nat.size (N - 1)) s j < N) fun r => ?_, h]
  · congr 3
    rw [show ({v ∈ range (2 ^ Nat.size (N - 1)) | ¬ v < N} : Finset ℕ) =
      Ico N (2 ^ Nat.size (N - 1)) by ext v; simp; omega, Nat.card_Ico]
  · rw [uniformSample, sampleTries_eq_find, List.find?_eq_none]
    simp

/-- **Failure probability** [AB09, Exercise 7.1 (2)]: `Pr[?] ≤ 2^{-k}` for `N ≥ 1`. -/
theorem randProb_uniformSample_none_le {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    randProb (sampleCoins N k) (fun r => uniformSample N k r = none) ≤ (1 / 2) ^ k := by
  rw [randProb_uniformSample_none]
  obtain ⟨h1, h2⟩ := le_two_pow_size_pred hN
  have hpos : (0 : ℚ) < 2 ^ Nat.size (N - 1) := by positivity
  refine pow_le_pow_left₀ (by positivity) ?_ k
  rw [div_le_iff₀ hpos, Nat.cast_sub h1]
  push_cast
  have : (2 : ℚ) ^ Nat.size (N - 1) < 2 * N := by exact_mod_cast h2
  linarith

/-- **Uniform given not `?`** [AB09, Exercise 7.1 (1)]: every value `i < N` has
probability `Pr[not ?] / N`.

**Proof sketch.** Reading `?` as the value `N`, the output is always in `[0, N]`, so the
probabilities of the `N + 1` values sum to `1` (`randProb_mem_eq_sum`); the `N` values below
`N` are equally likely (`randProb_uniformSample_eq`). -/
theorem randProb_uniformSample_some_mul {N : ℕ} (k : ℕ) {i : ℕ} (hi : i < N) :
    randProb (sampleCoins N k) (fun r => uniformSample N k r = some i) * N =
      1 - randProb (sampleCoins N k) (fun r => uniformSample N k r = none) := by
  set m := sampleCoins N k
  let g : List Bool → ℕ := fun r => (uniformSample N k r).getD N
  have hg : ∀ r, g r < N + 1 := fun r => by
    cases h : uniformSample N k r with
    | none => simp [g, h]
    | some v => have := lt_of_uniformSample_eq_some h; simp [g, h]; omega
  have hsum := randProb_mem_eq_sum (m := m) g (range (N + 1))
  rw [randProb_congr (B := fun _ => True) fun r => by simp [hg], randProb_true,
    sum_range_succ] at hsum
  have hsome : ∀ j < N, randProb m (fun l => g l = j) =
      randProb m (fun r => uniformSample N k r = some i) := fun j hj => by
    rw [randProb_uniformSample_eq (k := k) hi hj]
    refine randProb_congr fun r => ?_
    cases h : uniformSample N k (List.ofFn r) with
    | none => simp [g, h]; omega
    | some v => simp [g, h]
  have hnone : randProb m (fun l => g l = N) =
      randProb m (fun r => uniformSample N k r = none) := randProb_congr fun r => by
    cases h : uniformSample N k (List.ofFn r) with
    | none => simp [g, h]
    | some v => have := lt_of_uniformSample_eq_some h; simp [g, h]; omega
  rw [sum_congr rfl fun j hj => hsome j (mem_range.mp hj), sum_const, card_range, nsmul_eq_mul,
    hnone] at hsum
  linarith

/-! ### The word-level implementation -/

/-- The encoding of an output: `[]` for `?`, and `1 :: bits v` for the value `v`. -/
def encSample : Option ℕ → List Bool
  | none => []
  | some v => true :: Nat.bits v

/-- One try on the state `⟨⟨N, ℓ⟩, ⟨r, out⟩⟩`: cut the next `|ℓ|` coins off `r`, and if nothing
has been output yet and their value is below `N`, output it. -/
def sampleStep (d : List Bool) : List Bool :=
  pairEncode (pairFstD d)
    (pairEncode (dropPrefixByLen (pairEncode (pairSndD (pairFstD d)) (pairFstD (pairSndD d))))
      (if isNilB (pairSndD (pairSndD d)) && BinArith.lt (pairEncode
          (takePrefixByLen (pairEncode (pairSndD (pairFstD d)) (pairFstD (pairSndD d))))
          (pairFstD (pairFstD d)))
        then true :: Nat.bits (bitsVal
          (takePrefixByLen (pairEncode (pairSndD (pairFstD d)) (pairFstD (pairSndD d)))))
        else pairSndD (pairSndD d)))

/-- [AB09, Exercise 7.1] as a word function: on `⟨⟨N, 1^k⟩, r⟩` (`N` in binary), run `k` tries of
`sampleStep` from `⟨⟨N, bits (N - 1)⟩, ⟨r, []⟩⟩` and return the output slot. -/
def uniformSampleAlg (z : List Bool) : List Bool :=
  pairSndD (pairSndD (pairSndD (BinArith.forLoop sampleStep
    (pairEncode (pairSndD (pairFstD z))
      (pairEncode (pairEncode (pairFstD (pairFstD z))
          (BinArith.sub (pairEncode (pairFstD (pairFstD z)) [true])))
        (pairEncode (pairSndD z) []))))))

/-- The tries of the implementation: after `j` tries the coins have advanced by `j` blocks and
the output slot holds the result of `sampleTries`, unless it was already set. -/
theorem iterate_sampleStep (Nw Lw : List Bool) (j : ℕ) (r out : List Bool) :
    sampleStep^[j] (pairEncode (pairEncode Nw Lw) (pairEncode r out)) =
      pairEncode (pairEncode Nw Lw) (pairEncode (r.drop (j * Lw.length))
        (if out = [] then encSample (sampleTries (bitsVal Nw) Lw.length j r) else out)) := by
  induction j generalizing r out with
  | zero => by_cases h : out = [] <;> simp [h, sampleTries, encSample]
  | succ j ih =>
    rw [Function.iterate_succ_apply]
    simp only [sampleStep, pairFstD_pairEncode, pairSndD_pairEncode, takePrefixByLen,
      dropPrefixByLen, BinArith.lt, isNilB]
    rw [ih, List.drop_drop, show Lw.length + j * Lw.length = (j + 1) * Lw.length by ring]
    congr 2
    by_cases h : out = []
    · by_cases hb : bitsVal (r.take Lw.length) < bitsVal Nw
      · simp [h, hb, sampleTries, encSample]
      · simp [h, hb, sampleTries]
    · simp [h]

/-- **The implementation computes the procedure**: on `⟨⟨bits-word of N, 1^k⟩, r⟩` it outputs
the encoding of `uniformSample N k r`. -/
theorem uniformSampleAlg_pairEncode (w r : List Bool) (k : ℕ) :
    uniformSampleAlg (pairEncode (pairEncode w (List.replicate k true)) r) =
      encSample (uniformSample (bitsVal w) k r) := by
  have hL : (BinArith.sub (pairEncode w [true])).length = Nat.size (bitsVal w - 1) := by
    simp [BinArith.sub, bitsVal, Nat.size_eq_bits_len]
  simp only [uniformSampleAlg, pairFstD_pairEncode, pairSndD_pairEncode,
    BinArith.forLoop_pairEncode, List.length_replicate, iterate_sampleStep, hL, if_true,
    uniformSample]

/-- A try is polynomial-time.

**Proof sketch.** It is assembled from the pair projections, `takePrefixByLen`,
`dropPrefixByLen`, the comparison `BinArith.lt`, `BinArith.polyTimeComputable_normBits` and
`polyTimeComputable_ite`. -/
theorem polyTimeComputable_sampleStep : PolyTimeComputable sampleStep := by
  have hq : PolyTimeComputable pairFstD := polyTimeComputable_pairFstD
  have hL : PolyTimeComputable (fun d => pairSndD (pairFstD d)) :=
    polyTimeComputable_pairSndD.comp hq
  have hN : PolyTimeComputable (fun d => pairFstD (pairFstD d)) :=
    polyTimeComputable_pairFstD.comp hq
  have hLr : PolyTimeComputable
      (fun d => pairEncode (pairSndD (pairFstD d)) (pairFstD (pairSndD d))) :=
    hL.pairEncode BinArith.polyTimeComputable_slot2
  have hblk := polyTimeComputable_takePrefixByLen.comp hLr
  have htest : PolyTimeComputable (fun d => [isNilB (pairSndD (pairSndD d)) &&
      BinArith.lt (pairEncode (takePrefixByLen (pairEncode (pairSndD (pairFstD d))
        (pairFstD (pairSndD d)))) (pairFstD (pairFstD d)))]) :=
    polyTimeComputable_and (polyTimeComputable_isNil.comp BinArith.polyTimeComputable_slot3)
      (BinArith.polyTimeComputable_lt.comp (hblk.pairEncode hN))
  have hset : PolyTimeComputable (fun d => true :: Nat.bits (bitsVal
      (takePrefixByLen (pairEncode (pairSndD (pairFstD d)) (pairFstD (pairSndD d)))))) :=
    (polyTimeComputable_const [true]).append (BinArith.polyTimeComputable_normBits.comp hblk)
  exact hq.pairEncode ((polyTimeComputable_dropPrefixByLen.comp hLr).pairEncode
    (polyTimeComputable_ite htest hset BinArith.polyTimeComputable_slot3))

/-- **The implementation is polynomial-time** [AB09, Exercise 7.1]: `k` tries on the input
`⟨⟨N, 1^k⟩, r⟩` take time polynomial in its length.

**Proof sketch.** `sampleStep` is polynomial-time and keeps the context `⟨N, ℓ⟩`; each try adds
at most `|ℓ| + 5` letters (the output slot is set once, to a word no longer than `ℓ`), so the
counted loop `BinArith.forLoop` stays in a polynomial envelope (`forLoop_bound_of_ctx`). -/
theorem polyTimeComputable_uniformSampleAlg : PolyTimeComputable uniformSampleAlg := by
  have hloop := BinArith.polyTimeComputable_forLoop polyTimeComputable_sampleStep _ _
    (BinArith.forLoop_bound_of_ctx 5 (fun d => by simp [sampleStep]) fun d => by
      have h1 := length_pair_components_le d
      have h2 := length_pair_components_le (pairSndD d)
      have h3 := length_pairSndD_le (pairFstD d)
      have h4 : (takePrefixByLen (pairEncode (pairSndD (pairFstD d))
          (pairFstD (pairSndD d)))).length ≤ (pairFstD d).length := by
        simp only [takePrefixByLen, pairFstD_pairEncode, pairSndD_pairEncode,
          List.length_take]
        omega
      have h5 := BinArith.length_bits_bitsVal_le (takePrefixByLen (pairEncode
        (pairSndD (pairFstD d)) (pairFstD (pairSndD d))))
      have h6 : (dropPrefixByLen (pairEncode (pairSndD (pairFstD d))
          (pairFstD (pairSndD d)))).length ≤ (pairFstD (pairSndD d)).length := by
        simp [dropPrefixByLen]
      simp only [sampleStep, length_pairEncode]
      split_ifs
      · simp only [List.length_cons]; omega
      · omega)
  have hinit : PolyTimeComputable (fun z => pairEncode (pairSndD (pairFstD z))
      (pairEncode (pairEncode (pairFstD (pairFstD z))
          (BinArith.sub (pairEncode (pairFstD (pairFstD z)) [true])))
        (pairEncode (pairSndD z) []))) :=
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD).pairEncode
      (((polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD).pairEncode
        (BinArith.polyTimeComputable_sub.comp
          ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD).pairEncode
            (polyTimeComputable_const [true])))).pairEncode
        (polyTimeComputable_pairSndD.pairEncode (polyTimeComputable_const [])))
  exact BinArith.polyTimeComputable_slot4.comp (hloop.comp hinit)

/-! ### Exercise 7.1 -/

/-- **[AB09, Exercise 7.1]**: for `N ≥ 1` and `δ > 0`, with `k = ⌈log₂ ⌈1/δ⌉⌉` tries the
procedure reads `k · ⌈log₂ N⌉` coins, is a polynomial-time function of `⟨⟨N, 1^k⟩, coins⟩`,
outputs only values below `N`, outputs every `i < N` with probability `Pr[not ?] / N`
(uniform conditioned on not `?`), and outputs `?` with probability at most `δ`. -/
theorem uniformSample_spec {N : ℕ} (hN : 1 ≤ N) {δ : ℝ} (hδ : 0 < δ) :
    PolyTimeComputable uniformSampleAlg ∧
    (∀ r : List Bool, uniformSampleAlg (pairEncode (pairEncode (Nat.bits N)
        (List.replicate (Nat.clog 2 ⌈δ⁻¹⌉₊) true)) r) =
      encSample (uniformSample N (Nat.clog 2 ⌈δ⁻¹⌉₊) r)) ∧
    (∀ (r : List Bool) (i : ℕ),
      uniformSample N (Nat.clog 2 ⌈δ⁻¹⌉₊) r = some i → i < N) ∧
    (∀ i < N, randProb (sampleCoins N (Nat.clog 2 ⌈δ⁻¹⌉₊))
        (fun r => uniformSample N (Nat.clog 2 ⌈δ⁻¹⌉₊) r = some i) * N =
      1 - randProb (sampleCoins N (Nat.clog 2 ⌈δ⁻¹⌉₊))
        (fun r => uniformSample N (Nat.clog 2 ⌈δ⁻¹⌉₊) r = none)) ∧
    (randProb (sampleCoins N (Nat.clog 2 ⌈δ⁻¹⌉₊))
        (fun r => uniformSample N (Nat.clog 2 ⌈δ⁻¹⌉₊) r = none) : ℝ) ≤ δ := by
  set k := Nat.clog 2 ⌈δ⁻¹⌉₊
  refine ⟨polyTimeComputable_uniformSampleAlg, fun r => ?_,
    fun r i h => lt_of_uniformSample_eq_some h,
    fun i hi => randProb_uniformSample_some_mul k hi, ?_⟩
  · rw [uniformSampleAlg_pairEncode, bitsVal_bits]
  · have h1 := (Rat.cast_le (K := ℝ)).mpr (randProb_uniformSample_none_le hN k)
    push_cast at h1
    refine h1.trans ?_
    have h2 : δ⁻¹ ≤ (2 : ℝ) ^ k :=
      calc δ⁻¹ ≤ (⌈δ⁻¹⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast Nat.le_pow_clog (by norm_num) _
        _ = (2 : ℝ) ^ k := by push_cast; rfl
    rw [one_div_pow, one_div]
    calc ((2 : ℝ) ^ k)⁻¹ ≤ (δ⁻¹)⁻¹ := inv_anti₀ (inv_pos.mpr hδ) h2
      _ = δ := inv_inv δ

end Randomized
