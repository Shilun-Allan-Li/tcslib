/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import Mathlib.Data.Nat.Size
import TCSlib.Complexity.ClassP.BinaryArith.PrimeFind
import TCSlib.Complexity.ClassNP.Transducer
import TCSlib.Complexity.TimeHierarchy.Diagonal

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# P is a proper subset of DTIME(n^{log n})

[AB09, §7.5, p.135]: "(by the Time Hierarchy Theorem) `BPP` [`= P`] is a proper subset of,
say, `DTIME(n^{log n})`." We prove `P ⊊ DTIME(n^{log n})` with `log = Nat.log 2`, by the
time hierarchy theorem — its two halves `diagLang_mem_DTIME` and `diagLang_not_mem_DTIME`
of `Complexity.time_hierarchy` — at the time-constructible budget
`2^{(log n)² + 1} ≤ 2 n^{log n}`.

## Main definitions

* `Randomized.quasiPolyBudget` — `n ↦ 2^{(log n)² + 1}`.

## Main results

* `Randomized.timeConstructible_quasiPolyBudget` — it is time constructible.
* `Randomized.P_ssubset_DTIME_pow_log` — `P ⊊ DTIME(n^{log n})`.

## Divergences

* The book says "say, `DTIME(n^{log n})`"; we fix `log = Nat.log 2` (so `0^{log 0} = 1`).
* The repository's hierarchy theorem needs `(f + n + 1)² = o(g)` and a constructible `g`,
  so the separating budget is `2^{(log n)² + 1}`, not `n^{log n}` itself; its diagonal
  language lies in `DTIME(n^{log n})` by monotonicity.
* Constructibility goes through `PolyTimeComputable`: the budget word `0^{(log n)²+1} 1` is
  emitted by `Complexity.polyTimeComputable_emitIter`, and a polynomial bound is within a
  constant of the superpolynomial budget.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open Turing Complexity Complexity.TimeHierarchy

/-- The separating budget `n ↦ 2^{(log n)² + 1}`. -/
def quasiPolyBudget (n : ℕ) : ℕ := 2 ^ (Nat.log 2 n ^ 2 + 1)

/-! ### Arithmetic of the budget -/

/-- `n` has `log n + 1` binary digits (none for `n = 0`). -/
private theorem length_bits_eq (n : ℕ) : n.bits.length = if n = 0 then 0 else Nat.log 2 n + 1 := by
  rw [Nat.size_eq_bits_len]
  split_ifs with hn
  · subst hn; simp
  · refine le_antisymm (Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by norm_num) n)) ?_
    exact Nat.succ_le_of_lt (Nat.lt_size.mpr (Nat.pow_log_le_self 2 hn))

/-- `n ≤ 2^{(log n)² + 1}`. -/
theorem le_quasiPolyBudget (n : ℕ) : n ≤ quasiPolyBudget n := by
  have h1 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
  have h2 : Nat.log 2 n ≤ Nat.log 2 n ^ 2 := by nlinarith
  exact h1.le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- `1 ≤ n^{log n}` for every `n` (`0^{log 0} = 1`). -/
private theorem one_le_pow_log (n : ℕ) : 1 ≤ n ^ Nat.log 2 n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact Nat.one_le_pow _ _ hn

/-- `2^{(log n)²} ≤ n^{log n}`. -/
theorem two_pow_log_sq_le (n : ℕ) : 2 ^ (Nat.log 2 n ^ 2) ≤ n ^ Nat.log 2 n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [sq, pow_mul]
    exact Nat.pow_le_pow_left (Nat.pow_log_le_self 2 hn.ne') _

/-- `2^{(log n)² + 1} + 1 ≤ 3 n^{log n}`. -/
theorem quasiPolyBudget_add_one_le (n : ℕ) :
    quasiPolyBudget n + 1 ≤ 3 * n ^ Nat.log 2 n := by
  have := two_pow_log_sq_le n
  have := one_le_pow_log n
  unfold quasiPolyBudget
  rw [pow_succ]
  omega

/-- A polynomial is within a constant of the budget: `(n+1)^c ≤ 2^{c(c+1)} 2^{(log n)²}`.

**Proof sketch.** `n + 1 ≤ 2^{m+1}` with `m = log n`, and `(m+1)c ≤ c(c+1) + m²` (split on
`m ≤ c`). -/
theorem succ_pow_le_quasiPoly (n c : ℕ) :
    (n + 1) ^ c ≤ 2 ^ (c * (c + 1)) * 2 ^ (Nat.log 2 n ^ 2) := by
  set m := Nat.log 2 n
  have h1 : n + 1 ≤ 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hexp : (m + 1) * c ≤ c * (c + 1) + m ^ 2 := by
    rcases le_or_gt m c with h | h
    · nlinarith
    · nlinarith
  calc (n + 1) ^ c ≤ (2 ^ (m + 1)) ^ c := Nat.pow_le_pow_left h1 c
    _ = 2 ^ ((m + 1) * c) := (pow_mul _ _ _).symm
    _ ≤ 2 ^ (c * (c + 1) + m ^ 2) := Nat.pow_le_pow_right (by norm_num) hexp
    _ = 2 ^ (c * (c + 1)) * 2 ^ (m ^ 2) := pow_add _ _ _

/-- On `n = 2^m` the budget beats `A (nᵏ + 1 + n + 1)²` once `m ≥ A + 2k + 6`.

**Proof sketch.** `nᵏ + n + 2 ≤ 2^{m(k+1)+2}` and `A < 2^A`, so the left side is below
`2^{A + 2m(k+1) + 4} ≤ 2^{m²}`. -/
theorem poly_sq_le_quasiPolyBudget (k A m : ℕ) (hm : A + 2 * k + 6 ≤ m) :
    A * ((2 ^ m) ^ k + 1 + 2 ^ m + 1) ^ 2 ≤ quasiPolyBudget (2 ^ m) := by
  unfold quasiPolyBudget
  rw [Nat.log_pow (by norm_num)]
  have hA : A < 2 ^ A := Nat.lt_two_pow_self
  have hk : (2 ^ m) ^ k ≤ 2 ^ (m * (k + 1)) := by
    rw [← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hm1 : 2 ^ m ≤ 2 ^ (m * (k + 1)) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hone : 1 ≤ 2 ^ (m * (k + 1)) := Nat.one_le_two_pow
  have hsum : (2 ^ m) ^ k + 1 + 2 ^ m + 1 ≤ 2 ^ (m * (k + 1) + 2) := by
    rw [pow_add]; omega
  have hexp : A + (m * (k + 1) + 2) * 2 ≤ m ^ 2 + 1 := by nlinarith
  calc A * ((2 ^ m) ^ k + 1 + 2 ^ m + 1) ^ 2
      ≤ 2 ^ A * (2 ^ (m * (k + 1) + 2)) ^ 2 :=
        Nat.mul_le_mul hA.le (Nat.pow_le_pow_left hsum 2)
    _ = 2 ^ (A + (m * (k + 1) + 2) * 2) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ (m ^ 2 + 1) := Nat.pow_le_pow_right (by norm_num) hexp

/-! ### Constructing the budget -/

/-- Rewrite every symbol as `1` (a one-state transducer). -/
private def allTrue : List Bool → List Bool :=
  transduce (fun (_ : Unit) _ => ()) (fun _ _ => some true) ()

/-- Output one `0` per symbol after the first `0` (state: a `0` has been seen). -/
private def zerosAfterZero : List Bool → List Bool :=
  transduce (fun q b => q || !b) (fun q _ => if q then some false else none) false

/-- `allTrue l = 1^{|l|}`. -/
private theorem allTrue_eq (l : List Bool) : allTrue l = List.replicate l.length true := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [allTrue] at ih ⊢
    simp [transduce, ih, List.replicate_succ]

/-- After a `0` has been seen, every symbol emits `0`. -/
private theorem transduce_seen (l : List Bool) :
    transduce (fun q b => q || !b) (fun q _ => if q then some false else none) true l =
      List.replicate l.length false := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [transduce, ih, List.replicate_succ]

/-- `zerosAfterZero (1^j 0 l) = 0^{|l|}`. -/
private theorem zerosAfterZero_ones_zero (j : ℕ) (l : List Bool) :
    zerosAfterZero (List.replicate j true ++ false :: l) = List.replicate l.length false := by
  induction j with
  | zero => simp [zerosAfterZero, transduce, transduce_seen]
  | succ j ih => simpa [zerosAfterZero, transduce, List.replicate_succ] using ih

/-- `zerosAfterZero (1^j) = []`. -/
private theorem zerosAfterZero_ones (j : ℕ) : zerosAfterZero (List.replicate j true) = [] := by
  induction j with
  | zero => rfl
  | succ j ih => simpa [zerosAfterZero, transduce, List.replicate_succ] using ih

/-- On `w = 1^{m-1} 0 1^m`, the chunk of round `i` is `0^m` for `i < m` and empty after. -/
private theorem zerosAfterZero_drop (m i : ℕ) :
    zerosAfterZero ((List.replicate (m - 1) true ++ false :: List.replicate m true).drop i) =
      if i < m then List.replicate m false else [] := by
  split_ifs with hi
  · rw [List.drop_append_of_le_length (by simp; omega), List.drop_replicate,
      zerosAfterZero_ones_zero, List.length_replicate]
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · rcases i with _ | i
      · rfl
      · simp [zerosAfterZero, transduce]
    · have hlen : (List.replicate (m - 1) true ++ [false]).length = m := by simp; omega
      rw [show List.replicate (m - 1) true ++ false :: List.replicate m true =
          (List.replicate (m - 1) true ++ [false]) ++ List.replicate m true by simp,
        List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append, hlen,
        List.drop_replicate, zerosAfterZero_ones]

/-- Rounds `0, …, R-1` of chunks `0^m` (for `i < m`) emit `0^{min(R,m)·m}`. -/
private theorem flatMap_range_ite (m R : ℕ) :
    (List.range R).flatMap (fun i => if i < m then List.replicate m false else []) =
      List.replicate (min R m * m) false := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [List.range_succ, List.flatMap_append, ih, List.flatMap_singleton]
    by_cases h : R < m
    · rw [if_pos h, ← List.replicate_add, Nat.min_eq_left h.le,
        Nat.min_eq_left (Nat.succ_le_of_lt h), Nat.succ_mul]
    · rw [if_neg h, List.append_nil, Nat.min_eq_right (not_lt.mp h),
        Nat.min_eq_right (by omega : m ≤ R + 1)]

/-- The loop's start word `1^{m-1} 0 1^m` with `m = log |x|`, built from `bits |x|`. -/
private def budgetSeed (x : List Bool) : List Bool :=
  allTrue ((x.length.bits).drop 2) ++ false :: allTrue ((x.length.bits).drop 1)

/-- `budgetSeed x = 1^{m-1} 0 1^m` for `m = log |x|`. -/
private theorem budgetSeed_eq (x : List Bool) : budgetSeed x =
    List.replicate (Nat.log 2 x.length - 1) true ++ false ::
      List.replicate (Nat.log 2 x.length) true := by
  have h := length_bits_eq x.length
  unfold budgetSeed
  rw [allTrue_eq, allTrue_eq, List.length_drop, List.length_drop, h]
  split_ifs with h0
  · simp [h0]
  · congr 2

/-- The budget word is the seed's emission loop followed by `01`. -/
private theorem bits_quasiPolyBudget (x : List Bool) :
    (quasiPolyBudget x.length).bits =
      (List.range (1 * ((budgetSeed x).length + 1) ^ 1 + 1)).flatMap
        (fun i => zerosAfterZero ((fun w : List Bool => w.drop 1)^[i] (budgetSeed x))) ++
        [false, true] := by
  set m := Nat.log 2 x.length
  have hR : m ≤ 1 * ((budgetSeed x).length + 1) ^ 1 + 1 := by
    rw [budgetSeed_eq]; simp; omega
  simp only [BinArith.iterate_drop_one, budgetSeed_eq]
  rw [List.flatMap_congr (fun i _ => zerosAfterZero_drop m i), ← budgetSeed_eq,
    flatMap_range_ite, Nat.min_eq_right hR, quasiPolyBudget, bits_two_pow_eq_replicate]
  simp [m, List.replicate_succ', sq]

/-- The budget word `x ↦ ⌞2^{(log |x|)² + 1}⌟` is polynomial-time computable.

**Proof sketch.** Build the seed `1^{m-1} 0 1^m` (`m = log |x|`) from `bits |x|` by tails and
a one-state transducer; the emit loop over its tails prints `0^m` in each of the first `m`
rounds, i.e. `0^{m²}`; append `01`. -/
theorem polyTimeComputable_bits_quasiPolyBudget :
    PolyTimeComputable (fun x => (quasiPolyBudget x.length).bits) := by
  have hbits : PolyTimeComputable (fun x : List Bool => x.length.bits) := by
    convert polyTimeComputable_pairFstD.comp BinArith.polyTimeComputable_countLoop using 1
    funext x
    simp [BinArith.countLoop_eq]
  have hT : PolyTimeComputable allTrue := polyTimeComputable_transduce _ _ _
  have hseed : PolyTimeComputable budgetSeed := by
    convert (hT.comp (polyTimeComputable_tail.comp (polyTimeComputable_tail.comp hbits))).append
      ((polyTimeComputable_const [false]).append (hT.comp (polyTimeComputable_tail.comp hbits)))
      using 1
    funext x
    simp only [budgetSeed, Function.comp_apply, List.drop_drop, List.singleton_append]
  have hloop := polyTimeComputable_emitIter polyTimeComputable_tail
    (polyTimeComputable_transduce _ _ _ : PolyTimeComputable zerosAfterZero) 1 1 1 1
    (fun w i => by rw [BinArith.iterate_drop_one]; simp; omega)
  convert (hloop.comp hseed).append (polyTimeComputable_const [false, true]) using 1
  funext x
  rw [bits_quasiPolyBudget]
  rfl

/-- **`2^{(log n)² + 1}` is time constructible.**

**Proof sketch.** A machine computes the budget word within `C(n+1)^c` steps
(`polyTimeComputable_bits_quasiPolyBudget`), and `C(n+1)^c ≤ C 2^{c(c+1)} 2^{(log n)²}`
(`succ_pow_le_quasiPoly`); the budget is at least `n` (`le_quasiPolyBudget`). -/
theorem timeConstructible_quasiPolyBudget : TimeConstructible quasiPolyBudget := by
  obtain ⟨M, C, c, hM⟩ := polyTimeComputable_bits_quasiPolyBudget
  refine ⟨le_quasiPolyBudget, C * 2 ^ (c * (c + 1)) + 1, by omega, M, fun x => (hM x).mono ?_⟩
  have h := Nat.mul_le_mul_left C (succ_pow_le_quasiPoly x.length c)
  have hq : 2 ^ (Nat.log 2 x.length ^ 2) ≤ quasiPolyBudget x.length + 1 := by
    have := Nat.pow_le_pow_right (n := 2) (by norm_num) (Nat.le_succ (Nat.log 2 x.length ^ 2))
    unfold quasiPolyBudget
    omega
  calc C * (x.length + 1) ^ c ≤ C * 2 ^ (c * (c + 1)) * 2 ^ (Nat.log 2 x.length ^ 2) := by
        rw [Nat.mul_assoc]; exact h
    _ ≤ (C * 2 ^ (c * (c + 1)) + 1) * (quasiPolyBudget x.length + 1) :=
        Nat.mul_le_mul (Nat.le_succ _) hq

/-! ### The separation -/

/-- A constant factor in the time bound does not change `DTIME`. -/
theorem DTIME_const_mul_subset (C : ℕ) (T : ℕ → ℕ) : DTIME (fun n => C * T n) ⊆ DTIME T := by
  rintro L ⟨c, M, hM⟩
  exact ⟨c * C, M, fun x => (hM x).mono (le_of_eq (Nat.mul_assoc _ _ _).symm)⟩

/-- `nᵏ + 1 ≤ (2^{k²} + 2) n^{log n}`. -/
theorem pow_add_one_le_pow_log (k n : ℕ) :
    n ^ k + 1 ≤ (2 ^ (k * k) + 2) * n ^ Nat.log 2 n := by
  have h1 := one_le_pow_log n
  have hk : n ^ k ≤ 2 ^ (k * k) + n ^ Nat.log 2 n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rcases k with _ | k <;> simp
    by_cases hkl : k ≤ Nat.log 2 n
    · exact (Nat.pow_le_pow_right hn hkl).trans (Nat.le_add_left _ _)
    · have hlt : n < 2 ^ k :=
        (Nat.lt_pow_succ_log_self (by norm_num) n).trans_le
          (Nat.pow_le_pow_right (by norm_num) (by omega))
      calc n ^ k ≤ (2 ^ k) ^ k := Nat.pow_le_pow_left hlt.le k
        _ = 2 ^ (k * k) := (pow_mul _ _ _).symm
        _ ≤ _ := Nat.le_add_right _ _
  have h2 : 2 ^ (k * k) * 1 ≤ 2 ^ (k * k) * n ^ Nat.log 2 n := Nat.mul_le_mul_left _ h1
  rw [add_mul]
  omega

/-- **`P ⊊ DTIME(n^{log n})`** [AB09, §7.5, p.135, by Theorem 3.1].

**Proof sketch.** `P ⊆`: `nᵏ + 1 ≤ (2^{k²} + 2) n^{log n}`. Properness: the diagonal language
of the constructible budget `g = 2^{(log n)²+1}` lies in `DTIME(g + 1) ⊆ DTIME(n^{log n})`
(`g + 1 ≤ 3 n^{log n}`), but in no `DTIME(nᵏ + 1)`: at `n = 2^m` with `m` large,
`A (nᵏ + 1 + n + 1)² ≤ g(n)` (`poly_sq_le_quasiPolyBudget`, `diagLang_not_mem_DTIME`). -/
theorem P_ssubset_DTIME_pow_log : P ⊂ DTIME (fun n => n ^ Nat.log 2 n) := by
  refine ⟨fun L hL => ?_, fun h => ?_⟩
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hL
    exact DTIME_const_mul_subset (2 ^ (k * k) + 2) _
      (DTIME.mono (pow_add_one_le_pow_log k) hk)
  · have hmem : diagLang quasiPolyBudget ∈ DTIME (fun n => n ^ Nat.log 2 n) :=
      DTIME_const_mul_subset 3 _ (DTIME.mono quasiPolyBudget_add_one_le
        (diagLang_mem_DTIME timeConstructible_quasiPolyBudget))
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (h hmem)
    refine diagLang_not_mem_DTIME (T := fun n => n ^ k + 1) (fun A N => ?_) hk
    refine ⟨2 ^ max N (A + 2 * k + 6), ?_, poly_sq_le_quasiPolyBudget k A _ (le_max_right _ _)⟩
    exact (le_max_left _ _).trans Nat.lt_two_pow_self.le

/-- `P ≠ DTIME(n^{log n})`. -/
theorem P_ne_DTIME_pow_log : P ≠ DTIME (fun n => n ^ Nat.log 2 n) :=
  P_ssubset_DTIME_pow_log.ne

end Randomized
