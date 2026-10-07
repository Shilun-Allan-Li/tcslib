/-
Copyright (c) 2026 Hydroxyi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.ClassNP.EXP
import TCSlib.Complexity.TimeHierarchy.Diagonal

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# P ⊊ EXP

[AB09, §3.1, after Theorem 3.1]: the time hierarchy theorem separates polynomial from
exponential time. We instantiate `Complexity.time_hierarchy` (more precisely, its two
halves `diagLang_mem_DTIME` and `diagLang_not_mem_DTIME`) with the budget `g(n) = 2ⁿ`:
the single diagonal language `diagLang (2^·)` lies in `DTIME(2ⁿ + 1) ⊆ EXP` and in no
`DTIME(nᵏ + 1)`, hence not in `P`.

## Main results

* `Complexity.timeConstructible_two_pow` — `n ↦ 2ⁿ` is time constructible
  [AB09, §1.3, example `2ⁿ`].
* `Complexity.eventually_poly_le_two_pow` — polynomials are eventually dominated by
  `2ⁿ`, with an arbitrary constant factor.
* `Complexity.dtime_poly_ssubset_dtime_two_pow` — `DTIME(nᵏ + 1) ⊊ DTIME(2ⁿ)` for
  every `k` (the hierarchy theorem at the polynomial/exponential gap).
* `Complexity.P_ssubset_EXP` — `P ⊊ EXP` [AB09, §3.1; cf. Claim 2.4 for `P ⊆ EXP`].
* `Complexity.P_ne_EXP` — `P ≠ EXP`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.3; §2.6, Claim 2.4; §3.1, Theorem 3.1.)
-/

namespace Complexity

open Turing Turing.FinTM TimeHierarchy

/-- The machine `x ↦ 0^|x| 1`, the binary representation of `2^|x|` (low bit first):
emit `false` for every input symbol, then `true`, and halt. -/
private def twoPowTM : FinTM Bool where
  k := 0
  State := Unit
  tm :=
    { q₀ := ()
      tr := fun _ inp _ =>
        match inp with
        | some _ => ⟨.pos, fun _ => (none, 0), some false, some ()⟩
        | none => ⟨0, fun _ => (none, 0), some true, none⟩ }

/-- The run invariant of `twoPowTM`: after `i ≤ |x|` steps it is live at input
position `i + 1` with `0^i` emitted. -/
private lemma twoPowTM_run (x : List Bool) : ∀ i, i ≤ x.length →
    (twoPowTM.tm.runFrom (twoPowTM.tm.initCfg x) i).state = some () ∧
    ((twoPowTM.tm.runFrom (twoPowTM.tm.initCfg x) i).inputPos : ℕ) = i + 1 ∧
    (twoPowTM.tm.runFrom (twoPowTM.tm.initCfg x) i).output = List.replicate i false := by
  intro i
  induction i with
  | zero => intro _; exact ⟨rfl, rfl, rfl⟩
  | succ i ih =>
    intro hi
    obtain ⟨hs, hp, ho⟩ := ih (by omega)
    rw [MultiTapeTM.runFrom_succ_eq_step']
    generalize twoPowTM.tm.runFrom (twoPowTM.tm.initCfg x) i = c at hs hp ho
    have hin : c.inputSymbol = some (x[i]'(by omega)) := inputSymbolInner i (by omega) (by omega)
    unfold MultiTapeTM.step
    rw [hs]
    simp only [twoPowTM, hin, Action.apply]
    refine ⟨trivial, ?_, ?_⟩
    · rw [moveInputPos_pos_of_ne_right _ (by omega)]; simp [hp]
    · simp [ho, List.replicate_succ']

/-- The binary representation of `2ⁿ`, low bit first. -/
private lemma bits_two_pow (n : ℕ) : (2 ^ n).bits = List.replicate n false ++ [true] := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : 2 ^ (n + 1) = Nat.bit false (2 ^ n) := by
      simp [Nat.bit_val, Nat.pow_succ]; ring
    rw [h, Nat.bits_append_bit _ _ (fun h0 => absurd h0 (by positivity)), ih]
    simp [List.replicate_succ]

/-- **`2ⁿ` is time constructible** [AB09, §1.3: "`n`, `n log n`, `n²`, `2ⁿ` are time
constructible"]: `n ≤ 2ⁿ`, and `twoPowTM` writes `bits (2^|x|) = 0^|x| 1` in
`|x| + 1 ≤ 2^|x| + 1` steps. -/
theorem timeConstructible_two_pow : TimeConstructible (fun n => 2 ^ n) := by
  refine ⟨fun n => Nat.lt_two_pow_self.le, 1, Nat.one_pos, twoPowTM, fun x => ?_⟩
  obtain ⟨hs, hp, ho⟩ := twoPowTM_run x x.length (le_refl _)
  have hhalt : twoPowTM.ComputesInTime x (2 ^ x.length).bits (x.length + 1) := by
    rw [computesInTime_iff, MultiTapeTM.runFrom_succ_eq_step']
    generalize twoPowTM.tm.runFrom (twoPowTM.tm.initCfg x) x.length = c at hs hp ho
    have hin : c.inputSymbol = none := by
      have hpos : c.inputPos = ⟨x.length + 1, by omega⟩ := Fin.ext hp
      simp [Cfg.inputSymbol, hpos]
    unfold MultiTapeTM.step
    rw [hs]
    simp only [twoPowTM, hin, Action.apply]
    exact ⟨trivial, by simp [ho, bits_two_pow]⟩
  exact hhalt.mono (by have := @Nat.lt_two_pow_self x.length; simp only; omega)

/-- **Polynomials are eventually below `2ⁿ`**: for all constants `A` and `K` there is
`N` with `A · (n + 1)^K ≤ 2ⁿ` for all `n ≥ N`.

**Proof sketch.** Let `d = K + 1` and `m = ⌊n / d⌋`, so `n + 1 ≤ d (m + 1)` and
`d m ≤ n`. Then `A (n+1)^K ≤ A d^K (m+1)^K ≤ m · (2^m)^K < (2^m)^(K+1) ≤ 2ⁿ` as soon as
`m ≥ A d^K`, i.e. for `n ≥ d · A d^K`. -/
theorem eventually_poly_le_two_pow (A K : ℕ) :
    ∃ N, ∀ n ≥ N, A * (n + 1) ^ K ≤ 2 ^ n := by
  refine ⟨(K + 1) * (A * (K + 1) ^ K), fun n hn => ?_⟩
  set d := K + 1 with hd
  have hd0 : 0 < d := by omega
  set m := n / d with hm
  have hmA : A * d ^ K ≤ m := by
    rw [hm, Nat.le_div_iff_mul_le hd0]; rw [Nat.mul_comm]; exact hn
  have hn1 : n + 1 ≤ d * (m + 1) := Nat.lt_mul_div_succ n hd0
  have hdm : d * m ≤ n := Nat.mul_div_le n d
  have hm2 : m + 1 ≤ 2 ^ m := Nat.lt_two_pow_self
  calc A * (n + 1) ^ K ≤ A * (d * (m + 1)) ^ K :=
        Nat.mul_le_mul_left A (Nat.pow_le_pow_left hn1 K)
    _ = (A * d ^ K) * (m + 1) ^ K := by rw [mul_pow]; ring
    _ ≤ 2 ^ m * (2 ^ m) ^ K :=
        Nat.mul_le_mul (hmA.trans (Nat.le_of_lt (Nat.lt_two_pow_self)))
          (Nat.pow_le_pow_left hm2 K)
    _ = 2 ^ (d * m) := by rw [← pow_mul, ← pow_add, hd]; ring_nf
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hdm

/-- The hierarchy hypothesis for polynomial `f = nᵏ + 1` against `g = 2ⁿ`: for every
`A`, eventually `A · (nᵏ + 1 + n + 1)² ≤ 2ⁿ`. -/
theorem eventually_poly_sq_le_two_pow (k A : ℕ) :
    ∃ N, ∀ n ≥ N, A * (n ^ k + 1 + n + 1) ^ 2 ≤ 2 ^ n := by
  obtain ⟨N, hN⟩ := eventually_poly_le_two_pow (9 * A) (2 * k + 2)
  refine ⟨N, fun n hn => le_trans ?_ (hN n hn)⟩
  have h1 : n ^ k ≤ (n + 1) ^ (k + 1) :=
    (Nat.pow_le_pow_left (Nat.le_succ n) k).trans
      (Nat.pow_le_pow_right (Nat.succ_pos n) (Nat.le_succ k))
  have h2 : n + 1 ≤ (n + 1) ^ (k + 1) := by
    calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
      _ ≤ (n + 1) ^ (k + 1) := Nat.pow_le_pow_right (Nat.succ_pos n) (by omega)
  have h3 : n ^ k + 1 + n + 1 ≤ 3 * (n + 1) ^ (k + 1) := by omega
  have h4 : (n ^ k + 1 + n + 1) ^ 2 ≤ 9 * (n + 1) ^ (2 * k + 2) := by
    calc (n ^ k + 1 + n + 1) ^ 2 ≤ (3 * (n + 1) ^ (k + 1)) ^ 2 := Nat.pow_le_pow_left h3 2
      _ = 9 * (n + 1) ^ (2 * k + 2) := by ring
  calc A * (n ^ k + 1 + n + 1) ^ 2 ≤ A * (9 * (n + 1) ^ (2 * k + 2)) :=
        Nat.mul_le_mul_left A h4
    _ = 9 * A * (n + 1) ^ (2 * k + 2) := by ring

/-- **The polynomial/exponential gap of the hierarchy theorem** [AB09, Theorem 3.1
instantiated]: `DTIME(nᵏ + 1) ⊊ DTIME(2ⁿ)` for every `k` (the `+ 1` normalization
is that of `Complexity.P`). -/
theorem dtime_poly_ssubset_dtime_two_pow (k : ℕ) :
    DTIME (fun n => n ^ k + 1) ⊂ DTIME (fun n => 2 ^ n) :=
  time_hierarchy_of_pos timeConstructible_two_pow (fun n => by positivity)
    (eventually_poly_sq_le_two_pow k)

/-- **`P ⊊ EXP`** [AB09, §3.1, consequence of the Time Hierarchy Theorem 3.1; the
inclusion is Claim 2.4]. The witness is the diagonal language `diagLang (2^·)`.

**Proof sketch.** Inclusion is `Complexity.P_subset_EXP`. The diagonal language with
budget `2ⁿ` lies in `DTIME(2ⁿ + 1) ⊆ DTIME(2^(n¹))` up to the constant `2`, hence in
`EXP`; and for every `k` it is not in `DTIME(nᵏ + 1)` (`diagLang_not_mem_DTIME`, whose
hypothesis `A (nᵏ + 1 + n + 1)² ≤ 2ⁿ` holds eventually by
`eventually_poly_sq_le_two_pow`), hence not in `P = ⋃ₖ DTIME(nᵏ + 1)`. -/
theorem P_ssubset_EXP : P ⊂ EXP := by
  refine ⟨P_subset_EXP, fun h => ?_⟩
  have hmem : diagLang (fun n => 2 ^ n) ∈ EXP := by
    obtain ⟨c, M, hM⟩ := diagLang_mem_DTIME timeConstructible_two_pow
    refine Set.mem_iUnion.mpr ⟨1, 2 * c, M, fun x => (hM x).mono ?_⟩
    have : 1 ≤ 2 ^ x.length := Nat.one_le_two_pow
    simp only [pow_one]
    nlinarith
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (h hmem)
  refine diagLang_not_mem_DTIME (T := fun n => n ^ k + 1) (fun A N₀ => ?_) hk
  obtain ⟨N, hN⟩ := eventually_poly_sq_le_two_pow k A
  exact ⟨max N N₀, le_max_right _ _, hN _ (le_max_left _ _)⟩

/-- **`P ≠ EXP`** [AB09, §3.1]. -/
theorem P_ne_EXP : P ≠ EXP := P_ssubset_EXP.ne

end Complexity
