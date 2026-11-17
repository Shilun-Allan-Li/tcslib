/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassNP.Reductions
import TCSlib.Complexity.ClassNP.PClosure
import TCSlib.Complexity.CookLevin.Hardness
import TCSlib.Complexity.Diagonalization.EXPCOM
import TCSlib.Complexity.ClassP.ModelInvariance
import TCSlib.Complexity.ClassP.BinaryArith.Loops
import Mathlib.Data.Nat.Log

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Delayed diagonalization and intermediate languages

## Main definitions

* `Complexity.padSAT` is SAT padded by a variable exponent after a final separator.
* `Complexity.ladnerMachine` is the uniformly timed enumeration used in the delayed diagonal.
* `Complexity.ladnerH` is the least currently successful index, capped by a double logarithm.
* `Complexity.SAT_H` is the language padded by that index function.

## Main results

* `Complexity.ladnerH_polyTime` states that the delayed index is polynomial-time computable.
* `Complexity.SAT_H_intermediate` gives an intermediate language when P differs from NP.
* `Complexity.ladner` states the existence of an NP-intermediate language.

## Conventions

The bounded test uses acceptance equivalence at the indexed deadline, rather than
requiring a Boolean output within that deadline. At the empty input the deadline
is zero, so acceptance and padded-language membership are both false. The enumeration
uses the existing uniform binary code scheme. The inherited SAT decoder is total and
maps malformed words to a satisfiable formula. The general padding theorem below uses
the weaker NP-hardness premise, strengthening the NP-complete version.

## References

* [AB09] S. Arora, B. Barak, Computational Complexity: A Modern Approach,
  Cambridge University Press, 2009. Theorem 3.3 and its proof.
-/

namespace Complexity

open Turing
open scoped Classical

/-- `padSAT h` consists of a satisfiable word followed by a false separator and
`|ψ| ^ h |ψ|` true bits. [AB09, Theorem 3.3 and its proof] -/
def padSAT (h : ℕ → ℕ) : Language Bool :=
  {y | ∃ ψ ∈ SAT, y = ψ ++ false :: List.replicate (ψ.length ^ h ψ.length) true}

/-- A word belongs to `padSAT h` exactly when it has the indicated satisfiable prefix
and the prescribed separator and unary suffix. -/
theorem mem_padSAT_iff {h : ℕ → ℕ} {y : List Bool} :
    y ∈ padSAT h ↔
      ∃ ψ ∈ SAT, y = ψ ++ false :: List.replicate (ψ.length ^ h ψ.length) true :=
  Iff.rfl

/-- Padding-language membership at a word depends only on exponent values at shorter
prefix lengths.

**Proof sketch.** A padding witness is shorter than the whole word because the separator
contributes one position. Substitute equality of the exponent functions at that length. -/
theorem padSAT_congr {h g : ℕ → ℕ} {y : List Bool}
    (hfg : ∀ m < y.length, h m = g m) :
    y ∈ padSAT h ↔ y ∈ padSAT g := by
  constructor
  · intro hy
    obtain ⟨ψ, hψ, he⟩ := mem_padSAT_iff.mp hy
    have hshort : ψ.length < y.length := by
      rw [he, List.length_append, List.length_cons, List.length_replicate]
      omega
    apply mem_padSAT_iff.mpr
    refine ⟨ψ, hψ, ?_⟩
    rw [← hfg ψ.length hshort]
    exact he
  · intro hy
    obtain ⟨ψ, hψ, he⟩ := mem_padSAT_iff.mp hy
    have hshort : ψ.length < y.length := by
      rw [he, List.length_append, List.length_cons, List.length_replicate]
      omega
    apply mem_padSAT_iff.mpr
    refine ⟨ψ, hψ, ?_⟩
    rw [hfg ψ.length hshort]
    exact he

/-- The index `i` denotes the machine obtained by decoding its binary digits in the
uniformly timed code scheme. [AB09, Theorem 3.3 and its proof] -/
noncomputable def ladnerMachine (i : ℕ) : FinTM Bool :=
  (expCode.decode (Nat.bits i)).toFinTM

/-- The enumeration uses `expCode` on the binary digits of its index. -/
theorem ladnerMachine_eq (i : ℕ) :
    ladnerMachine i = (expCode.decode (Nat.bits i)).toFinTM :=
  rfl

/-- The delayed index at `n` is the least index below the double logarithm that correctly
recognizes the padded language on words of length at most the logarithm, within its indexed
polynomial deadline. If no such index exists, it is the double logarithm. Values used in a
short padded word depend only on smaller arguments, so strong recursion defines the index.
[AB09, Theorem 3.3 and its proof] -/
noncomputable def ladnerH (n : ℕ) : ℕ :=
  Nat.strongRecOn (motive := fun _ => ℕ) n fun n prev =>
    let h : ℕ → ℕ := fun m => if hm : m < n then prev m hm else 0
    let good : ℕ → Prop := fun i => ∀ x : List Bool, x.length ≤ Nat.log 2 n →
      ((ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔ x ∈ padSAT h)
    if hex : ∃ i, i < Nat.log 2 (Nat.log 2 n) ∧ good i then Nat.find hex
    else Nat.log 2 (Nat.log 2 n)

/-- The delayed index satisfies its minimum-index equation, with the global padded
language in the bounded acceptance test.

**Proof sketch.** Read the strong-recursion equation and use `padSAT_congr` to identify
local and global exponents on every queried word. Handle zero before using logarithmic decrease. -/
theorem ladnerH_eq (n : ℕ) :
    ladnerH n =
      if hex : ∃ i, i < Nat.log 2 (Nat.log 2 n) ∧
          ∀ x : List Bool, x.length ≤ Nat.log 2 n →
            ((ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
              x ∈ padSAT ladnerH) then
        Nat.find hex
      else Nat.log 2 (Nat.log 2 n) := by
  conv_lhs => rw [ladnerH]
  change (Nat.lt_wfRel.wf.fix (C := fun _ : ℕ => ℕ) _ n) = _
  rw [WellFounded.fix_eq]
  dsimp only
  let previous : ℕ → ℕ := fun m => if hm : m < n then ladnerH m else 0
  let localTest : ℕ → Prop := fun i => i < Nat.log 2 (Nat.log 2 n) ∧
    ∀ x : List Bool, x.length ≤ Nat.log 2 n →
      ((ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
        x ∈ padSAT previous)
  let globalTest : ℕ → Prop := fun i => i < Nat.log 2 (Nat.log 2 n) ∧
    ∀ x : List Bool, x.length ≤ Nat.log 2 n →
      ((ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
        x ∈ padSAT ladnerH)
  have hpad (hn : n ≠ 0) (x : List Bool) (hx : x.length ≤ Nat.log 2 n) :
      x ∈ padSAT previous ↔ x ∈ padSAT ladnerH := by
    apply padSAT_congr
    intro m hm
    have hmn : m < n := (hm.trans_le hx).trans (Nat.log_lt_self 2 hn)
    exact dif_pos hmn
  have hnonzero (i : ℕ) (hi : i < Nat.log 2 (Nat.log 2 n)) : n ≠ 0 := by
    intro hz
    subst n
    simp at hi
  have htests : localTest = globalTest := by
    funext i
    apply propext
    constructor
    · rintro ⟨hi, hgood⟩
      refine ⟨hi, fun x hx => ?_⟩
      exact (hgood x hx).trans (hpad (hnonzero i hi) x hx)
    · rintro ⟨hi, hgood⟩
      refine ⟨hi, fun x hx => ?_⟩
      exact (hgood x hx).trans (hpad (hnonzero i hi) x hx).symm
  have hexists : (∃ i, localTest i) ↔ ∃ i, globalTest i :=
    exists_congr fun i => Iff.of_eq (congrFun htests i)
  split_ifs with hlocal hglobal
  · exact Nat.find_congr' fun {i} => Iff.of_eq (congrFun htests i)
  · exact False.elim (hglobal (hexists.mp hlocal))
  · rename_i hglobal
    exact False.elim (hlocal (hexists.mpr hglobal))
  · rfl

/-- The delayed index never exceeds its double-logarithmic cap.

**Proof sketch.** In the successful case, read the strict index bound of the least witness;
in the fallback case, the index equals the cap. -/
theorem ladnerH_le (n : ℕ) : ladnerH n ≤ Nat.log 2 (Nat.log 2 n) := by
  rw [ladnerH_eq]
  split_ifs with h
  · exact (Nat.find_spec h).1.le
  · exact le_rfl

/-- `SAT_H` is the language obtained by padding SAT with the delayed index function.
[AB09, Theorem 3.3 and its proof] -/
noncomputable def SAT_H : Language Bool := padSAT ladnerH

/-- The witness language is `padSAT ladnerH`. -/
theorem SAT_H_eq : SAT_H = padSAT ladnerH :=
  rfl

/-- The empty word is outside every padded language because a separator contributes
one symbol. [AB09, Theorem 3.3 and its proof] -/
private theorem ladner_pad_nil (h : ℕ → ℕ) : ([] : List Bool) ∉ padSAT h := by
  intro hx
  obtain ⟨ψ, _, he⟩ := mem_padSAT_iff.mp hx
  have hlen := congrArg List.length he
  simp only [List.length_nil, List.length_append, List.length_cons,
    List.length_replicate] at hlen
  omega

/-- Prepending a word to the binary word of a positive number gives the binary word of a
number at least as large. [AB09, Theorem 3.3 and its proof] -/
private theorem ladner_bits_prepend (u : List Bool) (j : ℕ) (hj : 0 < j) :
    ∃ i, j ≤ i ∧ i.bits = u ++ j.bits := by
  induction u with
  | nil => exact ⟨j, le_rfl, rfl⟩
  | cons b u ih =>
    obtain ⟨i, hi, hbits⟩ := ih
    refine ⟨Nat.bit b i, ?_, ?_⟩
    · rw [Nat.bit_val]
      omega
    · rw [Nat.bits_append_bit i b (fun hz => by omega), hbits, List.cons_append]

/-- Every coded machine occurs at arbitrarily large canonical binary indices.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Construct a positive all-true binary suffix whose value exceeds
the requested bound. Prepending each bit of the machine's encoding preserves
canonicality and cannot decrease the value. The decoding padding law then
identifies the indexed machine. -/
private theorem ladner_padded_index (M : CodeTM) (B : ℕ) :
    ∃ i, B < i ∧ ladnerMachine i = M.toFinTM := by
  have ones : ∀ b : ℕ, ∃ j, b + 1 ≤ j ∧ j.bits = List.replicate (b + 1) true := by
    intro b
    induction b with
    | zero => exact ⟨1, le_rfl, Nat.one_bits⟩
    | succ b ih =>
      obtain ⟨j, hj, hbits⟩ := ih
      refine ⟨Nat.bit true j, ?_, ?_⟩
      · rw [Nat.bit_val]
        omega
      · rw [Nat.bits_append_bit j true (fun _ => rfl), hbits,
          List.replicate_succ (n := b + 1)]
  obtain ⟨j, hj, hbits⟩ := ones B
  obtain ⟨i, hi, hi_bits⟩ := ladner_bits_prepend (expCode.encode M) j (by omega)
  refine ⟨i, by omega, ?_⟩
  rw [ladnerMachine_eq, hi_bits, hbits, expCode.toMachineCode.decode_encode_pad]

/-- An indexed deadline dominates a polynomial on nonempty inputs when its index
bounds both the degree and the scaled coefficient. [AB09, Theorem 3.3 and its proof] -/
private theorem ladner_indexed_deadline (a d i m : ℕ)
    (hd : d ≤ i) (ha : a * 2 ^ d ≤ i) (hm : 1 ≤ m) :
    a * (m + 1) ^ d ≤ i * m ^ i := calc
  a * (m + 1) ^ d ≤ a * (2 * m) ^ d :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  _ = (a * 2 ^ d) * m ^ d := by rw [mul_pow, mul_assoc]
  _ ≤ i * m ^ i := Nat.mul_le_mul ha (Nat.pow_le_pow_right hm hd)

/-- A polynomial decider supplies one index that passes every bounded-acceptance
test. The empty word is handled by the zero-deadline convention.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Replace the decider by a one-work-tape machine and then its coded
normal form. Choose a padded index above the degree and scaled coefficient.
On a positive input length, the indexed clock contains the decider's clock.
Acceptance gives membership by uniqueness of completed outputs; membership gives
acceptance by monotonicity. At the empty input both sides are false. -/
private theorem ladner_correct_index (hP : SAT_H ∈ P) :
    ∃ i, ∀ x : List Bool,
      (ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
        x ∈ padSAT ladnerH := by
  classical
  obtain ⟨M, a, d, hk, hM⟩ := mem_P_iff_one_work_tape.mp hP
  have hdec := (FinTM.computesFunInTime_iff M _ _).mp
    ((FinTM.decidesInTime_iff M SAT_H _).mp hM)
  obtain ⟨i, hi, hcode⟩ := ladner_padded_index (M.toCodeTM hk) (max d (a * 2 ^ d))
  have hd : d ≤ i := (le_max_left d (a * 2 ^ d)).trans hi.le
  have ha : a * 2 ^ d ≤ i := (le_max_right d (a * 2 ^ d)).trans hi.le
  refine ⟨i, fun x => ?_⟩
  by_cases hx : x = []
  · subst x
    have hzero : i * ([] : List Bool).length ^ i = 0 := by
      have hipos : i ≠ 0 := by omega
      simp only [List.length_nil, zero_pow hipos, Nat.mul_zero]
    rw [hzero]
    exact iff_of_false (FinTM.not_computesInTime_zero _ _ _) (ladner_pad_nil ladnerH)
  · have hlen : 1 ≤ x.length := by
      cases x with
      | nil => exact False.elim (hx rfl)
      | cons b xs => exact Nat.succ_le_succ (Nat.zero_le _)
    have hclock := ladner_indexed_deadline a d i x.length hd ha hlen
    have hrun : (ladnerMachine i).ComputesInTime x
        [MultiTapeTM.indicator (SAT_H : Set (List Bool)) x] (a * (x.length + 1) ^ d) := by
      rw [hcode, FinTM.toCodeTM_computesInTime_iff]
      exact hdec x
    constructor
    · intro hacc
      by_contra hnot
      have hnot' : x ∉ SAT_H := by rw [SAT_H_eq]; exact hnot
      have hfalse := hrun
      rw [MultiTapeTM.indicator_of_not_mem hnot'] at hfalse
      have he := hacc.output_unique hfalse
      simp only [List.cons.injEq, Bool.true_eq_false, false_and] at he
    · intro hmem
      have hmem' : x ∈ SAT_H := by rw [SAT_H_eq]; exact hmem
      rw [MultiTapeTM.indicator_of_mem hmem'] at hrun
      exact hrun.mono hclock

/-- A globally correct index bounds the delayed selector at every stage.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_selector_bound (i : ℕ)
    (good : ∀ x : List Bool,
      (ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
        x ∈ padSAT ladnerH) :
    ∀ n, ladnerH n ≤ i := by
  classical
  intro n
  rw [ladnerH_eq]
  split_ifs with h
  · by_cases hcap : i < Nat.log 2 (Nat.log 2 n)
    · exact Nat.find_min' h ⟨hcap, fun x _ => good x⟩
    · exact (Nat.find_spec h).1.le.trans (Nat.le_of_not_gt hcap)
  · apply Nat.le_of_not_gt
    intro hcap
    exact h ⟨i, hcap, fun x _ => good x⟩

/-- A polynomial-time decider for the padded language forces its delayed index to be
bounded. [AB09, Theorem 3.3 and its proof]

**Proof sketch.** Choose a padded code of the decider whose enumeration index dominates
its polynomial time degree. That index eventually passes every short acceptance test;
absorb the finitely many earlier index values into one bound. -/
theorem ladnerH_bounded_of_mem_P :
    SAT_H ∈ P → ∃ C, ∀ n, ladnerH n ≤ C := by
  intro hP
  obtain ⟨i, hi⟩ := ladner_correct_index hP
  exact ⟨i, ladner_selector_bound i hi⟩

/-- A fixed polynomial clock can be prepared in the uniform simulator's paired
input format in polynomial time. [AB09, Theorem 3.3 and its proof]

**Proof sketch.** On a nonempty word, evaluating the successor-length polynomial
on its tail gives the required polynomial of the original length. Handle the
empty word by a fixed equality test and constant output, then pair the clock
with the fixed machine code and the original word. -/
private theorem ladner_fixed_clock_preparation (code : List Bool) (a d : ℕ) :
    PolyTimeComputable (fun x : List Bool =>
      pairEncode (pairEncode (Nat.bits (a * x.length ^ d)) code) x) := by
  classical
  obtain ⟨M, c, hM⟩ := FinTM.computesFunInTime_polyBits a d
  have hpoly : PolyTimeComputable (fun x : List Bool => Nat.bits (a * (x.length + 1) ^ d)) :=
    (polyTimeComputable_iff _).mpr ⟨M, c, d + 1, hM⟩
  have htail : PolyTimeComputable
      (fun x : List Bool => Nat.bits (a * ((x.drop 1).length + 1) ^ d)) :=
    hpoly.comp polyTimeComputable_tail
  have hnil : PolyTimeComputable (fun x : List Bool => [decide (x = [])]) :=
    polyTimeComputable_of_linear (FinTM.computesFunInTime_decideEq [])
  have hbranch := polyTimeComputable_ite hnil
    (polyTimeComputable_const (Nat.bits (a * 0 ^ d))) htail
  have heq : (fun x : List Bool => if decide (x = []) then
      Nat.bits (a * 0 ^ d) else Nat.bits (a * ((x.drop 1).length + 1) ^ d)) =
      (fun x : List Bool => Nat.bits (a * x.length ^ d)) := by
    funext x
    cases x with
    | nil => simp only [decide_true, if_true, List.length_nil]
    | cons b xs =>
      simp only [List.cons_ne_nil, decide_false, Bool.false_eq_true, if_false,
        List.drop_succ_cons, List.drop_zero, List.length_cons]
  rw [heq] at hbranch
  exact (hbranch.pairEncode (polyTimeComputable_const code)).pairEncode polyTimeComputable_id

/-- The simulator's polynomial in the numerical deadline has a polynomial envelope
when the simulated code and clock are fixed. [AB09, Theorem 3.3 and its proof]

**Proof sketch.** Each input-length term is bounded by a coefficient times the
successor length raised to the larger of one and the clock degree. Add these
bounds, raise to the simulator degree, and collect the constant factors. -/
private theorem ladner_fixed_clock_budget (D u a d n : ℕ) :
    D * (u + n + a * n ^ d + 1) ^ D ≤
      (D * (u + a + 2) ^ D) * (n + 1) ^ (max 1 d * D) := by
  let q := (n + 1) ^ max 1 d
  have hq : 1 ≤ q := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hn : n ≤ q := calc
    n ≤ n + 1 := Nat.le_succ _
    _ = (n + 1) ^ 1 := (pow_one _).symm
    _ ≤ q := Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left 1 d)
  have hnd : n ^ d ≤ q :=
    (Nat.pow_le_pow_left (Nat.le_succ n) d).trans
      (Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_right 1 d))
  have hu : u ≤ u * q := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left u hq
  have ha := Nat.mul_le_mul_left a hnd
  have hbase : u + n + a * n ^ d + 1 ≤ (u + a + 2) * q := calc
    _ ≤ u * q + q + a * q + q := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hu hn) ha) hq
    _ = _ := by ring
  calc
    D * (u + n + a * n ^ d + 1) ^ D ≤ D * ((u + a + 2) * q) ^ D :=
      Nat.mul_le_mul_left D (Nat.pow_le_pow_left hbase D)
    _ = (D * (u + a + 2) ^ D) * (n + 1) ^ (max 1 d * D) := by
      rw [mul_pow, mul_assoc, ← pow_mul]

/-- The bounded-acceptance test for a fixed code and polynomial clock is a total
polynomial-time Boolean function. [AB09, Theorem 3.3 and its proof]

**Proof sketch.** Prepare the exact simulator input with a polynomial-time machine.
The uniform simulator returns the bounded-acceptance bit on this image, including
when the simulated machine diverges. Bound its numerical clock by a fixed
polynomial, compose on the preparation machine's image, and absorb setup and
composition costs into one successor-length polynomial. -/
private theorem ladner_fixed_clock_FP (code : List Bool) (a d : ℕ) :
    PolyTimeComputable (fun x : List Bool =>
      [decide ((expCode.decode code).toFinTM.ComputesInTime
        x [true] (a * x.length ^ d))]) := by
  classical
  obtain ⟨M, C, e, hM⟩ := (polyTimeComputable_iff _).mp
    (ladner_fixed_clock_preparation code a d)
  let A := expCode.simDegree * (code.length + a + 2) ^ expCode.simDegree
  let k := max 1 d * expCode.simDegree
  have hU (x : List Bool) : expCode.simulator.ComputesInTime
      (pairEncode (pairEncode (Nat.bits (a * x.length ^ d)) code) x)
      [decide ((expCode.decode code).toFinTM.ComputesInTime x [true] (a * x.length ^ d))]
      (A * (x.length + 1) ^ k) := by
    have hb := ladner_fixed_clock_budget expCode.simDegree code.length a d x.length
    by_cases hacc : (expCode.decode code).toFinTM.ComputesInTime x [true] (a * x.length ^ d)
    · simpa only [hacc, decide_true] using
        (expCode.simulator_accepts code x (a * x.length ^ d) hacc).mono hb
    · simpa only [hacc, decide_false] using
        (expCode.simulator_rejects code x (a * x.length ^ d) hacc).mono hb
  obtain ⟨N, hN⟩ := FinTM.exists_comp_on_image M expCode.simulator _ _
    (fun n => C * (n + 1) ^ e) (fun n => A * (n + 1) ^ k) hM hU
  apply (polyTimeComputable_iff _).mpr
  refine ⟨N, 2 * C + A + 2, max e k, (FinTM.computesFunInTime_iff N _ _).mpr ?_⟩
  intro x
  apply (((FinTM.computesFunInTime_iff N _ _).mp hN) x).mono
  have he := Nat.pow_le_pow_right (Nat.succ_pos x.length) (le_max_left e k)
  have hk := Nat.pow_le_pow_right (Nat.succ_pos x.length) (le_max_right e k)
  have hone := Nat.one_le_pow (max e k) (x.length + 1) (Nat.succ_pos _)
  calc
    2 * (C * (x.length + 1) ^ e) + A * (x.length + 1) ^ k + 2 ≤
        2 * (C * (x.length + 1) ^ max e k) + A * (x.length + 1) ^ max e k +
          2 * (x.length + 1) ^ max e k :=
      Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left C he))
        (Nat.mul_le_mul_left A hk)) (by omega)
    _ = (2 * C + A + 2) * (x.length + 1) ^ max e k := by ring

/-- If one indexed test agrees everywhere with the padded language, its total
bounded simulator decides that language in polynomial time.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_all_tests_imply_P (i : ℕ)
    (good : ∀ x : List Bool,
      (ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
        x ∈ padSAT ladnerH) : SAT_H ∈ P := by
  classical
  have htest := mem_P_of_test (ladner_fixed_clock_FP (Nat.bits i) i i)
  have heq : {x : List Bool | decide ((expCode.decode (Nat.bits i)).toFinTM.ComputesInTime
      x [true] (i * x.length ^ i)) = true} = SAT_H := by
    ext x
    change (decide ((expCode.decode (Nat.bits i)).toFinTM.ComputesInTime
      x [true] (i * x.length ^ i)) = true) ↔ x ∈ SAT_H
    rw [decide_eq_true_eq, ← ladnerMachine_eq, SAT_H_eq]
    exact good x
  rw [heq] at htest
  exact htest

/-- Finitely many failing words are all visible at every sufficiently large stage,
so the delayed selector eventually exceeds any prescribed bound.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Choose a failing word for every index. For a given bound, take
the maximum length of witnesses below it. Choose an exponential stage whose query
window contains that maximum and whose double-log cap exceeds the bound. The
least successful index cannot be below the bound; neither can the fallback. -/
private theorem ladner_selector_threshold
    (bad : ∀ i : ℕ, ∃ x : List Bool,
      ¬ ((ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
        x ∈ padSAT ladnerH)) :
    ∀ C, ∃ N, ∀ n ≥ N, C ≤ ladnerH n := by
  classical
  choose witness counterexample using bad
  intro C
  let B := (Finset.range C).sup fun i => (witness i).length
  let M := max B (2 ^ C)
  refine ⟨2 ^ M, ?_⟩
  intro n hn
  have hlog : M ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by decide) hn
  have hcap : C ≤ Nat.log 2 (Nat.log 2 n) :=
    Nat.le_log_of_pow_le (by decide) ((le_max_right B (2 ^ C)).trans hlog)
  rw [ladnerH_eq]
  split_ifs with h
  · by_contra! hi
    have hlen : (witness (Nat.find h)).length ≤ B :=
      Finset.le_sup (f := fun i => (witness i).length) (Finset.mem_range.mpr hi)
    exact counterexample (Nat.find h)
      ((Nat.find_spec h).2 _ (hlen.trans ((le_max_left B (2 ^ C)).trans hlog)))
  · exact hcap

/-- If the padded language is outside P, the delayed index eventually exceeds every
constant. [AB09, Theorem 3.3 and its proof]

**Proof sketch.** Each fixed machine has a failing finite test, since a machine that passed
all its indexed polynomial tests would decide the language in polynomial time. Once all
failing tests below a fixed cap are visible, none of those indices is selected. -/
theorem ladnerH_unbounded_of_not_mem_P :
    SAT_H ∉ P → ∀ C, ∃ N, ∀ n ≥ N, C ≤ ladnerH n := by
  classical
  intro hP
  apply ladner_selector_threshold
  intro i
  by_contra! hgood
  exact hP (ladner_all_tests_imply_P i hgood)

/-! ### Padding syntax and fixed finite tables -/

/-- Parse the final false separator and its true suffix.
This is the mathematical padding parser of [AB09, Theorem 3.3 and its proof]. -/
private def ladner_parse : List Bool → Option (List Bool × ℕ)
  | [] => none
  | b :: bs => match ladner_parse bs with
    | some (p, t) => some (b :: p, t)
    | none => if b then none else some ([], bs.length)

/-- Padding syntax requires the suffix length to be the prescribed power.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_padSyntax (h : ℕ → ℕ) (y : List Bool) : Bool :=
  match ladner_parse y with
  | none => false
  | some (p, t) => decide (t = p.length ^ h p.length)

/-- Serialize a successful parse with a nonempty marker; failure is the empty word.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_parseWord (y : List Bool) : List Bool :=
  match ladner_parse y with
  | none => []
  | some (p, t) => pairEncode [true] (pairEncode p (Nat.bits t))

/-- The parser fails exactly on words with no false separator.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_parse_none (y : List Bool) :
    ladner_parse y = none ↔ ∀ b ∈ y, b = true := by
  induction y with
  | nil => simp only [ladner_parse, List.not_mem_nil, false_implies, implies_true]
  | cons b bs ih =>
    rw [List.forall_mem_cons, ← ih]
    cases hs : ladner_parse bs with
    | none => cases b <;> simp only [ladner_parse, hs, Bool.false_eq_true,
        if_false, if_true, Option.some_ne_none, and_true]
    | some pt =>
      obtain ⟨p, t⟩ := pt
      simp only [ladner_parse, hs, Option.some_ne_none, and_false]

/-- A successful parse reconstructs the input around the final separator.

**Proof sketch.** Induct on the input. A successful recursive parse extends the prefix.
When the recursive parse fails, the tail is all true and the current false bit is the
final separator. [AB09, Theorem 3.3 and its proof] -/
private theorem ladner_parse_sound {y p : List Bool} {t : ℕ}
    (hp : ladner_parse y = some (p, t)) : y = p ++ false :: List.replicate t true := by
  induction y generalizing p t with
  | nil => cases hp
  | cons b bs ih =>
    cases hs : ladner_parse bs with
    | none =>
      cases b with
      | false =>
        simp only [ladner_parse, hs, Bool.false_eq_true, if_false,
          Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        have he : bs = List.replicate bs.length true :=
          List.eq_replicate_iff.mpr ⟨rfl, (ladner_parse_none bs).mp hs⟩
        simpa only [List.nil_append] using congrArg (List.cons false) he
      | true =>
        simp only [ladner_parse, hs, if_true] at hp
        cases hp
    | some pt =>
      obtain ⟨q, u⟩ := pt
      simp only [ladner_parse, hs, Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      simpa only [List.cons_append] using congrArg (List.cons b) (ih hs)

/-- The parser reads any prefix followed by a false separator and a true suffix.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_parse_pad (p : List Bool) (t : ℕ) :
    ladner_parse (p ++ false :: List.replicate t true) = some (p, t) := by
  have hn : ladner_parse (List.replicate t true) = none :=
    (ladner_parse_none _).mpr (by simp only [List.mem_replicate]; aesop)
  induction p with
  | nil => simp only [List.nil_append, ladner_parse, hn, Bool.false_eq_true,
      if_false, List.length_replicate]
  | cons b p ih => simp only [List.cons_append, ladner_parse, ih]

/-- Parsing succeeds exactly on the indicated padded word.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_parse_some (y p : List Bool) (t : ℕ) :
    ladner_parse y = some (p, t) ↔ y = p ++ false :: List.replicate t true :=
  ⟨ladner_parse_sound, fun he => he ▸ ladner_parse_pad p t⟩

/-- A parsed prefix is shorter than the input, whose length includes the separator.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_parsed_length {y p : List Bool} {t : ℕ}
    (hp : ladner_parse y = some (p, t)) :
    y.length = p.length + 1 + t ∧ p.length < y.length := by
  rw [(ladner_parse_some y p t).mp hp]
  simp only [List.length_append, List.length_cons, List.length_replicate]
  omega

/-- The public false-bit test is false exactly on all-true words. -/
private theorem ladner_hasFalse_false (y : List Bool) :
    BinArith.hasFalse y = false ↔ ∀ b ∈ y, b = true := by
  induction y with
  | nil => simp only [BinArith.hasFalse_nil, List.not_mem_nil, false_implies, implies_true]
  | cons b bs ih => cases b <;> simp only [BinArith.hasFalse_cons, Bool.not_false,
      Bool.not_true, Bool.true_or, Bool.false_or, Bool.true_eq_false,
      List.forall_mem_cons, Bool.false_eq_true, false_and, true_and, ih]

/-- The public false-bit test distributes over append. -/
private theorem ladner_hasFalse_append (u v : List Bool) :
    BinArith.hasFalse (u ++ v) = (BinArith.hasFalse u || BinArith.hasFalse v) := by
  induction u with
  | nil => simp only [List.nil_append, BinArith.hasFalse_nil, Bool.false_or]
  | cons b u ih => simp only [List.cons_append, BinArith.hasFalse_cons, ih, Bool.or_assoc]

/-- Reverse and the public unary-rest reader recover a successful parse's prefix.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_parse_prefix {y p : List Bool} {t : ℕ}
    (hp : ladner_parse y = some (p, t)) : (BinArith.uRest y.reverse).reverse = p := by
  have hr (n : ℕ) (w : List Bool) :
      BinArith.uRest (List.replicate n true ++ false :: w) = w := by
    have h := BinArith.uRest_encodeNat n w
    rwa [BoolCircuit.encodeNat_eq, List.append_assoc, List.singleton_append] at h
  rw [(ladner_parse_some y p t).mp hp]
  simp only [List.reverse_append, List.reverse_cons, List.reverse_replicate,
    List.append_assoc, List.singleton_append, hr, List.reverse_reverse]

/-- The binary length of a word is polynomial-time (`FinTM.computesFunInTime_lengthBits`).
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_lengthBits_FP : PolyTimeComputable (fun y : List Bool => Nat.bits y.length) :=
  polyTimeComputable_of_linear FinTM.computesFunInTime_lengthBits

/-- The mathematical padding parser has a polynomial-time serialization.

**Proof sketch.** Reverse the input, skip its true suffix and separator with the existing
unary-rest reader, and reverse the remainder. Subtract the prefix length and one from
the input length to get the suffix length. The public false-bit test distinguishes a
missing separator from an empty prefix. [AB09, Theorem 3.3 and its proof] -/
private theorem ladner_parse_FP : PolyTimeComputable ladner_parseWord := by
  have hl := ladner_lengthBits_FP
  have hpre := BinArith.polyTimeComputable_reverse.comp
    (BinArith.polyTimeComputable_uRest.comp BinArith.polyTimeComputable_reverse)
  have ht := BinArith.polyTimeComputable_sub.comp
    ((BinArith.polyTimeComputable_sub.comp (hl.pairEncode (hl.comp hpre))).pairEncode
      (polyTimeComputable_const (Nat.bits 1)))
  have hout := polyTimeComputable_ite BinArith.polyTimeComputable_hasFalse
    ((polyTimeComputable_const [true]).pairEncode (hpre.pairEncode ht))
    (polyTimeComputable_const [])
  convert hout using 1
  funext y
  cases hp : ladner_parse y with
  | none =>
    have hf := (ladner_hasFalse_false y).mpr ((ladner_parse_none y).mp hp)
    simp only [ladner_parseWord, hp, Function.comp_apply, hf, Bool.false_eq_true, if_false]
  | some pt =>
    obtain ⟨p, t⟩ := pt
    have hpre' := ladner_parse_prefix hp
    have hlen := (ladner_parsed_length hp).1
    have hf : BinArith.hasFalse y = true := by
      rw [(ladner_parse_some y p t).mp hp, ladner_hasFalse_append,
        BinArith.hasFalse_cons]
      simp only [Bool.not_false, Bool.true_or, Bool.or_true]
    have ht' : y.length - p.length - 1 = t := by omega
    simp only [ladner_parseWord, hp, Function.comp_apply, hf, if_true, hpre',
      BinArith.sub_pairEncode, ht']

/-- The padding syntax test, for an exponent function that may depend on the input word, is
polynomial-time when the exponent at the parsed prefix length is.

**Proof sketch.** Parse the word and compute the prefix length and exponent in binary.
Use the saturated power with cap parameter equal to the suffix length. Its result equals
the suffix length exactly when the full power does; this avoids allocating an enormous
power. [AB09, Theorem 3.3 and its proof] -/
private theorem ladner_padSyntax_FP {g : List Bool → List Bool} {h : List Bool → ℕ → ℕ}
    (hg : PolyTimeComputable g)
    (hh : PolyTimeComputable (fun z : List Bool =>
      Nat.bits (h (pairSndD z) (pairFstD z).length))) :
    PolyTimeComputable (fun S => [ladner_padSyntax (h S) (g S)]) := by
  have hl := ladner_lengthBits_FP
  have hp := ladner_parse_FP.comp hg
  have hpre := BinArith.polyTimeComputable_slot2.comp hp
  have ht := BinArith.polyTimeComputable_slot3.comp hp
  have he := hh.comp (hpre.pairEncode polyTimeComputable_id)
  have hpow := BinArith.polyTimeComputable_powCap.comp
    ((hl.comp hpre).pairEncode (he.pairEncode ht))
  have heq := BinArith.polyTimeComputable_beq.comp (ht.pairEncode hpow)
  have hout := polyTimeComputable_ite (polyTimeComputable_isNil.comp hp)
    (polyTimeComputable_const [false]) heq
  convert hout using 1
  funext S
  cases hy : ladner_parse (g S) with
  | none => simp only [ladner_padSyntax, ladner_parseWord, hy, Function.comp_apply,
      decide_true, if_true]
  | some pt =>
    obtain ⟨p, t⟩ := pt
    have hne : pairEncode [true] (pairEncode p (Nat.bits t)) ≠ [] := by
      intro he
      have he' := congrArg List.length he
      rw [length_pairEncode] at he'
      simp only [List.length_cons, List.length_nil] at he'
      omega
    simp only [ladner_padSyntax, ladner_parseWord, hy, Function.comp_apply, id_eq,
      hne, decide_false, Bool.false_eq_true, if_false, pairFstD_pairEncode,
      pairSndD_pairEncode, BinArith.powCap_pairEncode, BinArith.beq_pairEncode]
    have heq' : (t = min (p.length ^ h S p.length) (t + 1)) ↔
        t = p.length ^ h S p.length := by omega
    simp only [heq']

/-- The padding syntax test is polynomial-time when its exponent function is: the
instance of `ladner_padSyntax_FP` with a fixed exponent function.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_syntax_FP {h : ℕ → ℕ}
    (hp : PolyTimeComputable (fun x : List Bool => Nat.bits (h x.length))) :
    PolyTimeComputable (fun y => [ladner_padSyntax h y]) :=
  ladner_padSyntax_FP (h := fun _ => h) polyTimeComputable_id
    (hp.comp polyTimeComputable_pairFstD)

/-- Padding membership is successful parsing, the prescribed suffix length, and SAT
membership of the prefix. [AB09, Theorem 3.3 and its proof] -/
private theorem ladner_pad_membership {h : ℕ → ℕ} {y : List Bool} :
    y ∈ padSAT h ↔ ∃ p t, ladner_parse y = some (p, t) ∧
      t = p.length ^ h p.length ∧ p ∈ SAT := by
  rw [mem_padSAT_iff]
  constructor
  · rintro ⟨p, hp, he⟩
    exact ⟨p, p.length ^ h p.length, (ladner_parse_some _ _ _).mpr he, rfl, hp⟩
  · rintro ⟨p, t, hparse, rfl, hp⟩
    exact ⟨p, hp, (ladner_parse_some _ _ _).mp hparse⟩

/-- Every fixed finite table of words has a polynomial-time membership test.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_finite_lookup_FP (S : Finset (List Bool)) :
    PolyTimeComputable (fun x : List Bool => [decide (x ∈ S)]) := by
  induction S using Finset.induction_on with
  | empty => exact polyTimeComputable_const [false]
  | @insert w S hw ih =>
    have heq := polyTimeComputable_of_linear (FinTM.computesFunInTime_decideEq w)
    convert polyTimeComputable_or heq ih using 1
    funext x
    simp only [Finset.mem_insert, Bool.decide_or]

/-- SAT on words shorter than a fixed bound is represented by a finite table.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Enumerate Boolean functions on each `Fin n` for `n < B`, turn them
into lists, and filter this finite universe by SAT. No SAT computation is performed at
runtime; the table is fixed once the bound is chosen. -/
private theorem ladner_small_SAT_table (B : ℕ) :
    ∃ S : Finset (List Bool), ∀ x : List Bool,
      x ∈ S ↔ x.length < B ∧ x ∈ SAT := by
  classical
  let U : Finset (List Bool) := (Finset.range B).biUnion (fun n =>
    (Finset.univ : Finset (Fin n → Bool)).image List.ofFn)
  have hu (x : List Bool) : x ∈ U ↔ x.length < B := by
    simp only [U, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨n, hn, f, rfl⟩
      simpa only [List.length_ofFn] using hn
    · intro hx
      exact ⟨x.length, hx, x.get, List.ofFn_get x⟩
  exact ⟨U.filter (fun x => x ∈ SAT), fun x => by rw [Finset.mem_filter, hu]⟩


/-! ### Shrinking a reduction into the padded language -/

/-- The fixed finite SAT table below a length threshold.
[AB09, Theorem 3.3 and its proof] -/
private noncomputable def ladner_smallSAT (B : ℕ) (x : List Bool) : Bool :=
  decide (x.length < B ∧ x ∈ SAT)

/-- One shrinking round: finish small inputs, reject invalid padding, tabulate short
prefixes, and otherwise keep just the parsed prefix. A nonempty answer flag is fixed.
[AB09, Theorem 3.3 and its proof] -/
private noncomputable def ladner_shrinkStep (h : ℕ → ℕ) (f : List Bool → List Bool) (B K : ℕ)
    (S : List Bool) : List Bool :=
  let x := pairSndD S
  if pairFstD S ≠ [] then S
  else if x.length < K then pairEncode [ladner_smallSAT K x] []
  else match ladner_parse (f x) with
    | none => pairEncode [false] []
    | some (p, t) =>
      if t ≠ p.length ^ h p.length then pairEncode [false] []
      else if p.length < B then pairEncode [ladner_smallSAT B p] []
      else pairEncode [] p

/-- A live state holds a word no longer than the original input with the same SAT answer;
a terminal state holds that answer as one bit. In particular `[false]` is terminal.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_ShrinkInv (x S : List Bool) : Prop :=
  (∃ y, S = pairEncode [] y ∧ y.length ≤ x.length ∧ (y ∈ SAT ↔ x ∈ SAT)) ∨
  (∃ b : Bool, S = pairEncode [b] [] ∧ (b = true ↔ x ∈ SAT))

/-- The live-word length plus one is the shrinking measure; terminal states have measure zero.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_shrinkMeasure (S : List Bool) : ℕ :=
  if pairFstD S = [] then (pairSndD S).length + 1 else 0

/-- NP-hardness supplies a polynomial reduction from SAT through the published
`NPHard_iff` and `polyTimeReducible_iff` readers. -/
private theorem ladner_reduction_from_hardness {h : ℕ → ℕ} (hH : NPHard (padSAT h)) :
    ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
      ∀ x, x ∈ SAT ↔ f x ∈ padSAT h := by
  exact (polyTimeReducible_iff _ _).mp ((NPHard_iff _).mp hH SAT SAT_mem_NP)

/-- A sufficiently large exponent forces every polynomially bounded padded prefix
below the square root of the original input length.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** If `m² > n`, then `(n+1)^(d+1) ≤ (m²)^(d+1) ≤ m^(h m)`.
The output bound would give `(n+1)^(d+1) ≤ A(n+1)^d`, contradicting `A ≤ n`.
Treat the zero prefix separately; no monotonicity of `h` is needed. -/
private theorem ladner_prefix_square_bound {h : ℕ → ℕ} (A d B n m : ℕ)
    (hh : ∀ r ≥ B, 2 * (d + 1) ≤ h r)
    (hn : A * 2 ^ d + 2 ≤ n) (hm : B ≤ m)
    (hsize : m ^ h m ≤ A * (n + 1) ^ d) : m ^ 2 ≤ n := by
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), Nat.zero_le]
  · by_contra hbad
    have hmn : n + 1 ≤ m ^ 2 := by omega
    have hlarge : (n + 1) ^ (d + 1) ≤ m ^ h m := calc
      _ ≤ (m ^ 2) ^ (d + 1) := Nat.pow_le_pow_left hmn _
      _ = m ^ (2 * (d + 1)) := (pow_mul _ _ _).symm
      _ ≤ m ^ h m := Nat.pow_le_pow_right hmpos (hh m hm)
    have hpos : 0 < (n + 1) ^ d := Nat.pow_pos (by omega)
    have hpoly : (n + 1) ^ d * (n + 1) ≤ A * (n + 1) ^ d := by
      rw [← pow_succ]
      exact hlarge.trans hsize
    have hAn : A ≤ n := calc
      A ≤ A * 2 ^ d := Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide))
      _ ≤ n := by omega
    have hmul := Nat.mul_le_mul_right ((n + 1) ^ d) hAn
    nlinarith

/-- Every syntactically valid reduction output with a sufficiently long prefix shrinks
that prefix below both the square root and the length of the current input.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Extract the reduction's polynomial output-length bound. Divergence
supplies a threshold where the padding exponent dominates twice its degree plus two.
The parsed suffix fits inside the output, so the square bound applies on yes- and
no-instances alike. The input threshold is at least two, making the square bound strict. -/
private theorem ladner_reduction_shrinks {h : ℕ → ℕ} {f : List Bool → List Bool}
    (hf : PolyTimeComputable f)
    (hu : ∀ C, ∃ N, ∀ n ≥ N, C ≤ h n) :
    ∃ B K, 2 ≤ K ∧ ∀ x p t,
      K ≤ x.length → ladner_parse (f x) = some (p, t) →
      t = p.length ^ h p.length → B ≤ p.length →
        p.length ^ 2 ≤ x.length ∧ p.length < x.length := by
  obtain ⟨A, d, hsize⟩ := hf.output_length_le
  obtain ⟨B, hB⟩ := hu (2 * (d + 1))
  refine ⟨B, A * 2 ^ d + 2, by omega, ?_⟩
  intro x p t hK hparse ht hpB
  have hlen := (ladner_parsed_length hparse).1
  have hpower : p.length ^ h p.length ≤ A * (x.length + 1) ^ d := by
    rw [← ht]
    have hfsize := hsize x
    omega
  have hsquare := ladner_prefix_square_bound A d B x.length p.length hB hK hpB hpower
  refine ⟨hsquare, ?_⟩
  have hx2 : 2 ≤ x.length := by omega
  by_contra hnot
  have hnp : x.length ≤ p.length := by omega
  have hsq := Nat.pow_le_pow_left hnp 2
  nlinarith

/-- A fixed short-input SAT test is polynomial-time by the existing finite-table leaves.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_smallSAT_FP (B : ℕ) :
    PolyTimeComputable (fun x => [ladner_smallSAT B x]) := by
  obtain ⟨S, hS⟩ := ladner_small_SAT_table B
  convert ladner_finite_lookup_FP S using 1
  funext x
  simp only [ladner_smallSAT, hS]

/-- A shrinking round is FP independently of hardness or divergence of the padding.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Compose the reduction with the existing parser and capped syntax test.
Use separate fixed SAT tables for small current inputs and small parsed prefixes.
Only valid syntax reaches a prefix branch; all remaining operations are FP length tests,
projections, pairing, and conditional composition. Large exponent values are never expanded. -/
private theorem ladner_shrinkStep_FP {h : ℕ → ℕ} {f : List Bool → List Bool}
    (hp : PolyTimeComputable (fun x : List Bool => Nat.bits (h x.length)))
    (hf : PolyTimeComputable f) (B K : ℕ) :
    PolyTimeComputable (ladner_shrinkStep h f B K) := by
  have hfx := hf.comp polyTimeComputable_pairSndD
  have hpre := BinArith.polyTimeComputable_slot2.comp (ladner_parse_FP.comp hfx)
  have hsyntax := (ladner_syntax_FP hp).comp hfx
  have hxsmall := BinArith.polyTimeComputable_lt.comp
    ((ladner_lengthBits_FP.comp polyTimeComputable_pairSndD).pairEncode
      (polyTimeComputable_const (Nat.bits K)))
  have hpsmall := BinArith.polyTimeComputable_lt.comp
    ((ladner_lengthBits_FP.comp hpre).pairEncode (polyTimeComputable_const (Nat.bits B)))
  have hprefix := polyTimeComputable_ite hpsmall
    (((ladner_smallSAT_FP B).comp hpre).pairEncode (polyTimeComputable_const []))
    ((polyTimeComputable_const []).pairEncode hpre)
  have hlarge := polyTimeComputable_ite hsyntax hprefix
    (polyTimeComputable_const (pairEncode [false] []))
  have hlive := polyTimeComputable_ite hxsmall
    (((ladner_smallSAT_FP K).comp polyTimeComputable_pairSndD).pairEncode
      (polyTimeComputable_const [])) hlarge
  have hout := polyTimeComputable_ite
    (polyTimeComputable_isNil.comp polyTimeComputable_pairFstD) hlive polyTimeComputable_id
  convert hout using 1
  funext S
  by_cases hflag : pairFstD S = []
  · by_cases hx : (pairSndD S).length < K
    · simp only [ladner_shrinkStep, ne_eq, Function.comp_apply, hflag, not_true_eq_false,
        if_false, decide_true, if_true, BinArith.lt_pairEncode, hx]
    · cases hparse : ladner_parse (f (pairSndD S)) with
      | none =>
        simp only [ladner_shrinkStep, ne_eq, Function.comp_apply, hflag, not_true_eq_false,
          if_false, hx, BinArith.lt_pairEncode, decide_false, Bool.false_eq_true,
          decide_true, if_true, hparse, ladner_padSyntax]
      | some pt =>
        obtain ⟨p, t⟩ := pt
        by_cases ht : t = p.length ^ h p.length <;>
          simp only [ladner_shrinkStep, ne_eq, Function.comp_apply, hflag, not_true_eq_false,
            if_false, hx, BinArith.lt_pairEncode, decide_false, Bool.false_eq_true,
            decide_true, if_true, hparse, ladner_padSyntax, ladner_parseWord,
            pairFstD_pairEncode, pairSndD_pairEncode, ht, not_false_eq_true,
            decide_eq_true_eq]
  · simp only [ladner_shrinkStep, ne_eq, Function.comp_apply, hflag, not_false_eq_true,
      if_true, decide_false, Bool.false_eq_true, if_false, id_eq]

/-- A correct one-bit terminal answer preserves the invariant and strictly lowers the
measure of any live state. This common ledger covers both answers and both finite tables.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_shrink_terminal_result (x y : List Bool) (b : Bool)
    (hb : b = true ↔ x ∈ SAT) :
    ladner_ShrinkInv x (pairEncode [b] []) ∧
      (0 < ladner_shrinkMeasure (pairEncode [] y) →
        ladner_shrinkMeasure (pairEncode [b] []) < ladner_shrinkMeasure (pairEncode [] y)) ∧
      (ladner_shrinkMeasure (pairEncode [] y) = 0 → pairEncode [b] [] = pairEncode [] y) := by
  have hne : ([b] : List Bool) ≠ [] := by intro h; cases h
  have hlive : ladner_shrinkMeasure (pairEncode [] y) = y.length + 1 := by
    rw [ladner_shrinkMeasure, pairFstD_pairEncode, if_pos rfl, pairSndD_pairEncode]
  have hdone : ladner_shrinkMeasure (pairEncode [b] []) = 0 := by
    rw [ladner_shrinkMeasure, pairFstD_pairEncode, if_neg hne]
  refine ⟨Or.inr ⟨b, rfl, hb⟩, ?_, ?_⟩
  · intro _
    rw [hdone, hlive]
    omega
  · intro hz
    rw [hlive] at hz
    omega

/-- A shrinking round preserves the SAT answer, lowers every positive live measure,
and fixes terminal states, including the false terminal bit.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Terminal flags are fixed. A short current input is answered by its
fixed table. For a large input, failed parsing or a wrong padding length contradicts
SAT membership through the reduction. Valid padding preserves the SAT answer at its
unique prefix. A short prefix is tabulated; every remaining prefix is strictly shorter
by hypothesis and becomes the sole next live word. -/
private theorem ladner_shrink_progress {h : ℕ → ℕ} {f : List Bool → List Bool} {B K : ℕ}
    (hK : 2 ≤ K)
    (hred : ∀ x, x ∈ SAT ↔ f x ∈ padSAT h)
    (hshrink : ∀ x p t, K ≤ x.length → ladner_parse (f x) = some (p, t) →
      t = p.length ^ h p.length → B ≤ p.length → p.length < x.length)
    (x S : List Bool) (hI : ladner_ShrinkInv x S) :
    ladner_ShrinkInv x (ladner_shrinkStep h f B K S) ∧
      (0 < ladner_shrinkMeasure S →
        ladner_shrinkMeasure (ladner_shrinkStep h f B K S) < ladner_shrinkMeasure S) ∧
      (ladner_shrinkMeasure S = 0 → ladner_shrinkStep h f B K S = S) := by
  rcases hI with ⟨y, rfl, hylen, hySAT⟩ | ⟨b, rfl, hb⟩
  · have hmeasure : ladner_shrinkMeasure (pairEncode [] y) = y.length + 1 := by
      rw [ladner_shrinkMeasure, pairFstD_pairEncode, if_pos rfl, pairSndD_pairEncode]
    by_cases hsmall : y.length < K
    · have hstep : ladner_shrinkStep h f B K (pairEncode [] y) =
          pairEncode [ladner_smallSAT K y] [] := by
        simp only [ladner_shrinkStep, ne_eq, pairFstD_pairEncode, pairSndD_pairEncode,
          not_true_eq_false, if_false, hsmall, if_true]
      rw [hstep]
      apply ladner_shrink_terminal_result
      simpa only [ladner_smallSAT, decide_eq_true_eq, hsmall, true_and] using hySAT
    · have hlarge : K ≤ y.length := by omega
      cases hparse : ladner_parse (f y) with
      | none =>
        have hstep : ladner_shrinkStep h f B K (pairEncode [] y) = pairEncode [false] [] := by
          simp only [ladner_shrinkStep, ne_eq, pairFstD_pairEncode, pairSndD_pairEncode,
            not_true_eq_false, if_false, hsmall, hparse]
        have hnot : x ∉ SAT := by
          intro hx
          obtain ⟨p, t, hp, -, -⟩ := ladner_pad_membership.mp ((hred y).mp (hySAT.mpr hx))
          rw [hparse] at hp
          cases hp
        rw [hstep]
        exact ladner_shrink_terminal_result x y false (iff_of_false (by decide) hnot)
      | some pt =>
        obtain ⟨p, t⟩ := pt
        have hpad : f y ∈ padSAT h ↔ t = p.length ^ h p.length ∧ p ∈ SAT := by
          simp only [ladner_pad_membership, hparse, Option.some.injEq, Prod.mk.injEq,
            and_assoc, exists_and_left, exists_eq_left']
        by_cases ht : t = p.length ^ h p.length
        · have hprefix : p ∈ SAT ↔ x ∈ SAT := by
            have hparsed : f y ∈ padSAT h ↔ p ∈ SAT := by
              simpa only [ht, true_and] using hpad
            exact hparsed.symm.trans ((hred y).symm.trans hySAT)
          by_cases hpB : p.length < B
          · have hstep : ladner_shrinkStep h f B K (pairEncode [] y) =
                pairEncode [ladner_smallSAT B p] [] := by
              simp only [ladner_shrinkStep, ne_eq, pairFstD_pairEncode, pairSndD_pairEncode,
                not_true_eq_false, if_false, hsmall, hparse, ht, hpB, if_true]
            rw [hstep]
            apply ladner_shrink_terminal_result
            simpa only [ladner_smallSAT, decide_eq_true_eq, hpB, true_and] using hprefix
          · have hshort := hshrink y p t hlarge hparse ht (by omega)
            have hy2 := hK.trans hlarge
            have hstep : ladner_shrinkStep h f B K (pairEncode [] y) = pairEncode [] p := by
              simp only [ladner_shrinkStep, ne_eq, pairFstD_pairEncode, pairSndD_pairEncode,
                not_true_eq_false, if_false, hsmall, hparse, ht, hpB]
            have hnext : ladner_shrinkMeasure (pairEncode [] p) = p.length + 1 := by
              rw [ladner_shrinkMeasure, pairFstD_pairEncode, if_pos rfl, pairSndD_pairEncode]
            rw [hstep]
            refine ⟨Or.inl ⟨p, rfl, hshort.le.trans hylen, hprefix⟩, ?_, ?_⟩
            · intro _
              rw [hnext, hmeasure]
              omega
            · intro hz
              rw [hmeasure] at hz
              omega
        · have hstep : ladner_shrinkStep h f B K (pairEncode [] y) = pairEncode [false] [] := by
            simp only [ladner_shrinkStep, ne_eq, pairFstD_pairEncode, pairSndD_pairEncode,
              not_true_eq_false, if_false, hsmall, hparse, ht, not_false_eq_true, if_true]
          have hnot : x ∉ SAT := fun hx => ht (hpad.mp ((hred y).mp (hySAT.mpr hx))).1
          rw [hstep]
          exact ladner_shrink_terminal_result x y false (iff_of_false (by decide) hnot)
  · have hne : ([b] : List Bool) ≠ [] := by intro he; cases he
    have hstep : ladner_shrinkStep h f B K (pairEncode [b] []) = pairEncode [b] [] := by
      simp only [ladner_shrinkStep, pairFstD_pairEncode, if_pos hne]
    have hz : ladner_shrinkMeasure (pairEncode [b] []) = 0 := by
      rw [ladner_shrinkMeasure, pairFstD_pairEncode, if_neg hne]
    rw [hstep]
    refine ⟨Or.inr ⟨b, rfl, hb⟩, ?_, fun _ => rfl⟩
    simp only [hz, Nat.lt_irrefl, false_implies]

/-- The shrinking iterator starts live with the original input and its unchanged SAT answer.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_shrink_initial (x : List Bool) :
    ladner_ShrinkInv x (pairEncode [] x) :=
  Or.inl ⟨x, rfl, le_rfl, Iff.rfl⟩

/-- Every state in the initialized shrinking orbit has a linear serialized length bound.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_shrink_orbit_size {h : ℕ → ℕ} {f : List Bool → List Bool} {B K : ℕ}
    (hinv : ∀ x S, ladner_ShrinkInv x S → ladner_ShrinkInv x (ladner_shrinkStep h f B K S))
    (x : List Bool) (j : ℕ) :
    ((ladner_shrinkStep h f B K)^[j] (pairEncode [] x)).length ≤ 4 * (x.length + 1) ^ 1 := by
  have hI := BinArith.iterate_invariant (ladner_ShrinkInv x) (hinv x) j (ladner_shrink_initial x)
  rcases hI with ⟨y, hy, hlen, -⟩ | ⟨b, hb, -⟩
  · rw [hy, length_pairEncode]
    simp only [List.length_nil, pow_one]
    omega
  · rw [hb, length_pairEncode]
    simp only [List.length_cons, List.length_nil, pow_one]
    omega

/-- The bounded shrinking orbit finishes with exactly the original SAT decision bit.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** The initial measure is `|x|+1`. Apply the public decreasing-measure
iterator theorem for that many rounds and retain the invariant along the whole orbit.
A live state cannot have measure zero, so the invariant's terminal alternative supplies
the unique correct answer bit. -/
private theorem ladner_shrink_final_readout {h : ℕ → ℕ} {f : List Bool → List Bool} {B K : ℕ}
    (hprogress : ∀ x S, ladner_ShrinkInv x S →
      ladner_ShrinkInv x (ladner_shrinkStep h f B K S) ∧
        (0 < ladner_shrinkMeasure S →
          ladner_shrinkMeasure (ladner_shrinkStep h f B K S) < ladner_shrinkMeasure S) ∧
        (ladner_shrinkMeasure S = 0 → ladner_shrinkStep h f B K S = S)) (x : List Bool) :
    pairFstD ((ladner_shrinkStep h f B K)^[1 * (x.length + 1) ^ 1] (pairEncode [] x)) =
      [decide (x ∈ SAT)] := by
  have hI := BinArith.iterate_invariant (g := ladner_shrinkStep h f B K) (ladner_ShrinkInv x)
    (fun S hS => (hprogress x S hS).1) (1 * (x.length + 1) ^ 1) (ladner_shrink_initial x)
  have hz := BinArith.iterate_measure_eq_zero (g := ladner_shrinkStep h f B K)
    (ladner_ShrinkInv x) ladner_shrinkMeasure
    (fun S hS => (hprogress x S hS).1)
    (fun S hS hpos => (hprogress x S hS).2.1 hpos)
    (fun S hS hzero => (hprogress x S hS).2.2 hzero)
    (1 * (x.length + 1) ^ 1) (pairEncode [] x) (ladner_shrink_initial x)
    (by simpa only [ladner_shrinkMeasure, pairFstD_pairEncode, if_pos rfl,
        pairSndD_pairEncode, pow_one, one_mul] using Nat.le_refl (x.length + 1))
  rcases hI with ⟨y, hy, -, -⟩ | ⟨b, hb, hans⟩
  · rw [hy, ladner_shrinkMeasure, pairFstD_pairEncode, if_pos rfl,
      pairSndD_pairEncode] at hz
    omega
  · rw [hb, pairFstD_pairEncode]
    apply congrArg (fun b : Bool => [b])
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using hans

/-- The public polynomial iterator and a correct shrinking readout put SAT in P.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Initialize a live pair, run the supplied FP step for `|x|+1` rounds
under its linear all-orbit bound, and project the answer flag. The readout identifies
this FP bit with SAT; `mem_P_of_test` supplies the language-class conclusion. -/
private theorem ladner_shrinking_transfer {h : ℕ → ℕ} {f : List Bool → List Bool} (B K : ℕ)
    (hstep : PolyTimeComputable (ladner_shrinkStep h f B K))
    (hsize : ∀ x j, j ≤ 1 * (x.length + 1) ^ 1 →
      ((ladner_shrinkStep h f B K)^[j] (pairEncode [] x)).length ≤ 4 * (x.length + 1) ^ 1)
    (hout : ∀ x, pairFstD ((ladner_shrinkStep h f B K)^[1 * (x.length + 1) ^ 1]
      (pairEncode [] x)) = [decide (x ∈ SAT)]) : SAT ∈ P := by
  have hinit : PolyTimeComputable (fun x : List Bool => pairEncode [] x) :=
    (polyTimeComputable_const []).pairEncode polyTimeComputable_id
  have hloop := BinArith.polyTimeComputable_iterate hstep hinit 1 1 4 1 hsize
  have htest : PolyTimeComputable (fun x : List Bool => [decide (x ∈ SAT)]) := by
    convert polyTimeComputable_pairFstD.comp hloop using 1
    funext x
    exact (hout x).symm
  convert mem_P_of_test htest using 1
  ext x
  simp only [decide_eq_true_eq]
  rfl


/-! ### Polynomial-time preparation for the bounded candidate test -/

/-- Read the numeric memo entries through `BinArith.decWords`.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_values (T : List Bool) : List ℕ :=
  (BinArith.decWords T).map LogProg.bitsVal

/-- Enumerate every short word by deleting the high sentinel bit of a positive rank.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_shortWords (a : ℕ) : List (List Bool) :=
  (List.range (2 ^ (a + 1) - 1)).map (fun r => (Nat.bits (r + 1)).dropLast)

/-- Select the least successful index against the supplied memo values, or the cap.
[AB09, Theorem 3.3 and its proof] -/
private noncomputable def ladner_stage (vs : List ℕ) : ℕ :=
  let n := vs.length
  if hex : ∃ i, i < Nat.log 2 (Nat.log 2 n) ∧
      ∀ x : List Bool, x.length ≤ Nat.log 2 n →
        ((ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
          x ∈ padSAT (fun m => vs.getD m 0)) then Nat.find hex
  else Nat.log 2 (Nat.log 2 n)

/-- The candidate predicate checks context consistency and every short input.
[AB09, Theorem 3.3 and its proof] -/
private noncomputable def ladner_candidate (S : List Bool) : Bool :=
  let n := (pairFstD S).length
  let i := LogProg.bitsVal (pairFstD (pairSndD S))
  let vs := ladner_values (pairSndD (pairSndD S))
  decide (n = vs.length ∧ i < Nat.log 2 (Nat.log 2 n) ∧
    ∀ x : List Bool, x.length ≤ Nat.log 2 n →
      ((ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
        x ∈ padSAT (fun m => vs.getD m 0)))

/-- A simulator query contains an index below the double logarithm and a short input.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_validQuery (S : List Bool) : Prop :=
  LogProg.bitsVal (pairFstD (pairSndD S)) <
      Nat.log 2 (Nat.log 2 (pairFstD S).length) ∧
    (pairSndD (pairSndD S)).length ≤ Nat.log 2 (pairFstD S).length

/-- Invalid queries use the empty code; valid ones use the canonical index bits.
[AB09, Theorem 3.3 and its proof] -/
private noncomputable def ladner_queryCode (S : List Bool) : List Bool :=
  if ladner_validQuery S then Nat.bits (LogProg.bitsVal (pairFstD (pairSndD S))) else []

/-- Invalid queries use the empty simulator input.
[AB09, Theorem 3.3 and its proof] -/
private noncomputable def ladner_queryInput (S : List Bool) : List Bool :=
  if ladner_validQuery S then pairSndD (pairSndD S) else []

/-- Invalid queries use deadline zero; valid ones use the indexed deadline.
[AB09, Theorem 3.3 and its proof] -/
private noncomputable def ladner_queryDeadline (S : List Bool) : ℕ :=
  if ladner_validQuery S then
    LogProg.bitsVal (pairFstD (pairSndD S)) *
      (pairSndD (pairSndD S)).length ^ LogProg.bitsVal (pairFstD (pairSndD S))
  else 0

/-- Serialize the guarded query in the uniform simulator's input format.
[AB09, Theorem 3.3 and its proof] -/
private noncomputable def ladner_queryPrep (S : List Bool) : List Bool :=
  pairEncode (pairEncode (Nat.bits (ladner_queryDeadline S)) (ladner_queryCode S))
    (ladner_queryInput S)

/-- Check the candidate context before using its numeric index.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_ctxGuard (C : List Bool) : Prop :=
  (pairFstD C).length = (ladner_values (pairSndD (pairSndD C))).length ∧
    LogProg.bitsVal (pairFstD (pairSndD C)) <
      Nat.log 2 (Nat.log 2 (pairFstD C).length)

/-- A single rank's verdict includes every guard and the acceptance equivalence.
[AB09, Theorem 3.3 and its proof] -/
private noncomputable def ladner_wordVerdict (C : List Bool) (r : ℕ) : Bool :=
  let x := (Nat.bits (r + 1)).dropLast
  let i := LogProg.bitsVal (pairFstD (pairSndD C))
  decide (ladner_ctxGuard C ∧ x.length ≤ Nat.log 2 (pairFstD C).length ∧
    ((ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
      x ∈ padSAT (fun m => (ladner_values (pairSndD (pairSndD C))).getD m 0)))

/-- The number of words in the bounded short-input scan.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_queryCount (C : List Bool) : ℕ :=
  2 ^ (Nat.log 2 (pairFstD C).length + 1) - 1

/-- Initialize the remaining count, completed rank, and conjunction flag.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_testInit (C : List Bool) : List Bool :=
  pairEncode C (pairEncode (List.replicate (ladner_queryCount C) true) (pairEncode [] [true]))

/-- One transition of the candidate scan, intended for `BinArith.polyTimeComputable_iterate`.
[AB09, Theorem 3.3 and its proof] -/
private noncomputable def ladner_testStep (S : List Bool) : List Bool :=
  let C := pairFstD S
  let rem := pairFstD (pairSndD S)
  let rank := pairFstD (pairSndD (pairSndD S))
  let flag := pairSndD (pairSndD (pairSndD S))
  if rem = [] then S else
    pairEncode C (pairEncode (rem.drop 1)
      (pairEncode (rank ++ [true]) [flag.headD false && ladner_wordVerdict C rank.length]))

/-- Read the conjunction flag of the candidate scan.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_testOut (S : List Bool) : List Bool :=
  pairSndD (pairSndD (pairSndD S))

/-- The sentinel enumeration contains exactly the words of length at most its bound.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** The upper rank bound limits the binary word to `a + 1` bits.
Conversely prepend the bits of any word to the positive sentinel `1`; the resulting
canonical number has that word as its binary expansion with its last bit removed. -/
private theorem ladner_shortWords_complete (a : ℕ) (x : List Bool) :
    x ∈ ladner_shortWords a ↔ x.length ≤ a := by
  constructor
  · intro hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    have hr' := List.mem_range.mp hr
    have hl := LogProg.length_bits_le (show r + 1 < 2 ^ (a + 1) by omega)
    rw [List.length_dropLast]
    omega
  · intro hx
    obtain ⟨n, hn, he⟩ := ladner_bits_prepend x 1 Nat.one_pos
    rw [Nat.one_bits] at he
    have hlt := LogProg.lt_two_pow_bits n
    rw [he, List.length_append, List.length_cons, List.length_nil] at hlt
    have hna : n < 2 ^ (a + 1) := hlt.trans_le
      (Nat.pow_le_pow_right (by decide) (by omega))
    apply List.mem_map.mpr
    refine ⟨n - 1, List.mem_range.mpr (by omega), ?_⟩
    rw [Nat.sub_add_cancel hn, he, List.dropLast_concat]

/-- The short-input scan has at most twice the stage length plus two queries.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_shortWords_count (n : ℕ) :
    (ladner_shortWords (Nat.log 2 n)).length ≤ 2 * (n + 1) := by
  rw [ladner_shortWords, List.length_map, List.length_range, pow_succ']
  have h := Nat.pow_log_le_add_one 2 n
  omega

/-- A uniform elementary bound used to charge the double logarithm.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_square_le_power (k : ℕ) : k ^ 2 ≤ 2 ^ (k + 1) := by
  induction k with
  | zero => decide
  | succ k ih =>
    by_cases hk : k < 3
    · have hk0 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases hk0 with rfl | rfl | rfl <;> norm_num
    · have hk' : 3 ≤ k := by omega
      calc (k + 1) ^ 2 ≤ 2 * k ^ 2 := by nlinarith
           _ ≤ 2 * 2 ^ (k + 1) := Nat.mul_le_mul_left _ ih
           _ = 2 ^ (k + 1 + 1) := by simp only [pow_succ']

/-- Short indexed simulations have a deadline bounded by the cube of the stage length.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Put `L = log₂ n` and `k = log₂ L`. The index is below `k`,
so `(k + 1)i ≤ k² ≤ 2^(k+1) ≤ 2L`. Thus `m^i ≤ 2^(2L) ≤ n²`,
while `i ≤ n`. No monotonicity of the delayed index is used. -/
private theorem ladner_short_deadline (n i m : ℕ)
    (hi : i < Nat.log 2 (Nat.log 2 n)) (hm : m ≤ Nat.log 2 n) :
    i * m ^ i ≤ n ^ 3 := by
  have hL : Nat.log 2 n ≠ 0 := by
    intro h
    rw [h, Nat.log_zero_right] at hi
    omega
  have hn : n ≠ 0 := by
    intro h
    subst n
    rw [Nat.log_zero_right] at hL
    exact hL rfl
  have hi' : (Nat.log 2 (Nat.log 2 n) + 1) * i ≤
      (Nat.log 2 (Nat.log 2 n)) ^ 2 := by
    have h := Nat.mul_le_mul_left (Nat.log 2 (Nat.log 2 n) + 1)
      (Nat.succ_le_of_lt hi)
    nlinarith
  have hexp : (Nat.log 2 (Nat.log 2 n) + 1) * i ≤ 2 * Nat.log 2 n := calc
    _ ≤ (Nat.log 2 (Nat.log 2 n)) ^ 2 := hi'
    _ ≤ 2 ^ (Nat.log 2 (Nat.log 2 n) + 1) := ladner_square_le_power _
    _ = 2 * 2 ^ Nat.log 2 (Nat.log 2 n) := by rw [pow_succ']
    _ ≤ 2 * Nat.log 2 n := Nat.mul_le_mul_left _ (Nat.pow_log_le_self 2 hL)
  have hpow : m ^ i ≤ n ^ 2 := calc
    _ ≤ (2 ^ (Nat.log 2 (Nat.log 2 n) + 1)) ^ i := Nat.pow_le_pow_left
      (hm.trans (Nat.lt_pow_succ_log_self (by decide) (Nat.log 2 n)).le) _
    _ = 2 ^ ((Nat.log 2 (Nat.log 2 n) + 1) * i) := (pow_mul _ _ _).symm
    _ ≤ 2 ^ (2 * Nat.log 2 n) := Nat.pow_le_pow_right (by decide) hexp
    _ = (2 ^ Nat.log 2 n) ^ 2 := by rw [Nat.mul_comm 2, pow_mul]
    _ ≤ n ^ 2 := Nat.pow_le_pow_left (Nat.pow_log_le_self 2 hn) _
  have hin : i ≤ n := hi.le.trans ((Nat.log_le_self 2 _).trans (Nat.log_le_self 2 n))
  calc i * m ^ i ≤ n * n ^ 2 := Nat.mul_le_mul hin hpow
       _ = n ^ 3 := by ring

/-- The uniform simulator's numeric deadline cost has a polynomial stage envelope.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Bound each of the code length, short-input length, deadline, and
constant by `(n + 1)^3`, then raise the sum bound to the simulator degree. -/
private theorem ladner_numeric_envelope (D n i : ℕ) (x : List Bool)
    (hi : i < Nat.log 2 (Nat.log 2 n)) (hx : x.length ≤ Nat.log 2 n) :
    D * ((Nat.bits i).length + x.length + i * x.length ^ i + 1) ^ D ≤
      (D * 4 ^ D) * (n + 1) ^ (3 * D) := by
  have hin : i ≤ n := hi.le.trans ((Nat.log_le_self 2 _).trans (Nat.log_le_self 2 n))
  have hb := (length_bits_le_self i).trans hin
  have hx' := hx.trans (Nat.log_le_self 2 n)
  have ht := ladner_short_deadline n i x.length hi hx
  have hcube : n ^ 3 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_left (Nat.le_succ _) _
  have hlin : n + 1 ≤ (n + 1) ^ 3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ n + 1) (by decide : 1 ≤ 3)
  calc _ ≤ D * (4 * (n + 1) ^ 3) ^ D :=
         Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
       _ = (D * 4 ^ D) * (n + 1) ^ (3 * D) := by rw [mul_pow, ← pow_mul]; ring

/-- Polynomial preparation and an image budget absorb the exact composition overhead.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_composition_clock (C q A e n : ℕ) :
    2 * (C * (n + 1) ^ q) + A * (n + 1) ^ e + 2 ≤
      (2 * C + A + 2) * (n + 1) ^ max q e := by
  have hq := Nat.pow_le_pow_right (by omega : 1 ≤ n + 1) (le_max_left q e)
  have he := Nat.pow_le_pow_right (by omega : 1 ≤ n + 1) (le_max_right q e)
  have hp : 1 ≤ (n + 1) ^ max q e := Nat.one_le_pow _ _ (by omega)
  nlinarith

/-- The floor binary logarithm is the canonical binary length minus one.
`Complexity.LogProg.length_bits_eq_log` supplies the nonzero case. -/
private theorem ladner_log_eq_bits_length (n : ℕ) :
    Nat.log 2 n = (Nat.bits n).length - 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.log_zero_right, Nat.zero_bits, List.length_nil, Nat.zero_sub]
  · rw [LogProg.length_bits_eq_log (by omega)]
    omega

/-- The binary floor logarithm is polynomial-time, including noncanonical inputs.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_binary_log_FP : PolyTimeComputable
    (fun w : List Bool => Nat.bits (Nat.log 2 (LogProg.bitsVal w))) := by
  have hl := ladner_lengthBits_FP
  have h := BinArith.polyTimeComputable_sub.comp
    ((hl.comp BinArith.polyTimeComputable_normBits).pairEncode
      (polyTimeComputable_const (Nat.bits 1)))
  convert h using 1
  funext w
  simp only [Function.comp_apply, BinArith.sub_pairEncode, ladner_log_eq_bits_length]

/-- A linear SAT verifier yields the exact exponential short-SAT search clock.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Apply `Complexity.exists_proj_decider` at certificate width `m + 1`.
The verifier sees `2m + 1` symbols, and its clock therefore has base `2m + 2`.
Identify the projected language using the supplied verifier equivalence. -/
private theorem ladner_short_SAT_machine
    (linear : ∃ V : Language Bool, V ∈ P ∧ ∀ x : List Bool, x ∈ SAT ↔
      ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ V) :
    ∃ (a d b : ℕ) (E : FinTM Bool), E.DecidesInTime SAT
      (fun m => b * 2 ^ (m + 1) *
        (a * (2 * m + 2) ^ d + (2 * m + 2) ^ 2)) := by
  obtain ⟨V, hV, hv⟩ := linear
  obtain ⟨a, d, M, hM⟩ := mem_P_iff.mp hV
  obtain ⟨b, E, hE⟩ := exists_proj_decider 1 1 V (fun n => a * (n + 1) ^ d) M hM
  have hlang : {x : List Bool | ∃ u, u.length = 1 * (x.length + 1) ^ 1 ∧ x ++ u ∈ V} =
      SAT := by
    ext x
    simpa only [Set.mem_setOf_eq, one_mul, pow_one] using (hv x).symm
  rw [hlang] at hE
  refine ⟨a, d, b, E, ?_⟩
  convert hE using 1
  funext m
  congr 2 <;> simp only [one_mul, pow_one] <;> ring

/-- The short-SAT search clock is polynomial when the queried word is logarithmic.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** `2^m ≤ n + 1` and `2m + 2 ≤ 2(n + 1)`. Raise the latter
bound to each degree, enlarge both degrees to `d + 2`, and charge the outer
factor `2(n + 1)` to obtain degree `d + 3`. -/
private theorem ladner_short_SAT_envelope (a b d n m : ℕ) (hm : m ≤ Nat.log 2 n) :
    b * 2 ^ (m + 1) * (a * (2 * m + 2) ^ d + (2 * m + 2) ^ 2) ≤
      (2 * b * (a * 2 ^ d + 4)) * (n + 1) ^ (d + 3) := by
  have hm' := hm.trans (Nat.log_le_self 2 n)
  have hexp : 2 ^ (m + 1) ≤ 2 * (n + 1) := by
    rw [pow_succ']
    exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_right (by decide) hm).trans
      (Nat.pow_log_le_add_one 2 n))
  have hd : (2 * m + 2) ^ d ≤ 2 ^ d * (n + 1) ^ (d + 2) := calc
    _ ≤ (2 * (n + 1)) ^ d := Nat.pow_le_pow_left (by omega) _
    _ = 2 ^ d * (n + 1) ^ d := mul_pow _ _ _
    _ ≤ 2 ^ d * (n + 1) ^ (d + 2) := Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right (by omega) (by omega))
  have htwo : (2 * m + 2) ^ 2 ≤ 4 * (n + 1) ^ (d + 2) := calc
    _ ≤ (2 * (n + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) _
    _ = 4 * (n + 1) ^ 2 := by ring
    _ ≤ 4 * (n + 1) ^ (d + 2) := Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right (by omega) (by omega))
  calc _ ≤ b * (2 * (n + 1)) *
          ((a * 2 ^ d + 4) * (n + 1) ^ (d + 2)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hexp) (by nlinarith)
       _ = (2 * b * (a * 2 ^ d + 4)) * (n + 1) ^ (d + 3) := by
        rw [show d + 3 = (d + 2) + 1 by omega, pow_succ]
        ring

/-- Polynomial query preparation and a polynomial numeric budget suffice for simulation.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Extract the preparation machine through `polyTimeComputable_iff`.
The simulator's accepting and rejecting contracts compute the indicated bit on its image.
Use `FinTM.exists_comp_on_image`, then absorb its exact setup overhead with
`ladner_composition_clock`. The simulator clock is charged in the numeric deadline. -/
private theorem ladner_simulation_on_image (code input : List Bool → List Bool)
    (deadline : List Bool → ℕ)
    (hprep : PolyTimeComputable (fun z =>
      pairEncode (pairEncode (Nat.bits (deadline z)) (code z)) (input z)))
    (hbudget : ∃ A e, ∀ z, expCode.simDegree *
      ((code z).length + (input z).length + deadline z + 1) ^ expCode.simDegree ≤
        A * (z.length + 1) ^ e) :
    PolyTimeComputable (fun z => [decide
      ((expCode.decode (code z)).toFinTM.ComputesInTime
        (input z) [true] (deadline z))]) := by
  obtain ⟨M, C, q, hM⟩ := (polyTimeComputable_iff _).mp hprep
  obtain ⟨A, e, hA⟩ := hbudget
  have hU (z : List Bool) : expCode.simulator.ComputesInTime
      (pairEncode (pairEncode (Nat.bits (deadline z)) (code z)) (input z))
      [decide ((expCode.decode (code z)).toFinTM.ComputesInTime
        (input z) [true] (deadline z))] (A * (z.length + 1) ^ e) := by
    by_cases h : (expCode.decode (code z)).toFinTM.ComputesInTime
        (input z) [true] (deadline z)
    · simpa only [h, decide_true] using
        (expCode.simulator_accepts (code z) (input z) (deadline z) h).mono (hA z)
    · simpa only [h, decide_false] using
        (expCode.simulator_rejects (code z) (input z) (deadline z) h).mono (hA z)
  obtain ⟨N, hN⟩ := FinTM.exists_comp_on_image M expCode.simulator _ _
    (fun n => C * (n + 1) ^ q) (fun n => A * (n + 1) ^ e) hM hU
  apply (polyTimeComputable_iff _).mpr
  refine ⟨N, 2 * C + A + 2, max q e, ?_⟩
  apply (FinTM.computesFunInTime_iff _ _ _).mpr
  intro z
  exact ((FinTM.computesFunInTime_iff _ _ _).mp hN z).mono
    (ladner_composition_clock C q A e z.length)

/-- Short SAT evaluation on an FP-prepared image has polynomial total cost.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Use the linear verifier's exponential projection decider only on the
logarithmically short image. `ladner_short_SAT_envelope` bounds that phase in the
original input length; image composition explicitly includes the FP preparation clock. -/
private theorem ladner_short_SAT_on_image (f : List Bool → List Bool)
    (hf : PolyTimeComputable f)
    (hshort : ∀ z, (f z).length ≤ Nat.log 2 z.length)
    (linear : ∃ V : Language Bool, V ∈ P ∧ ∀ x : List Bool, x ∈ SAT ↔
      ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ V) :
    PolyTimeComputable (fun z => [decide (f z ∈ SAT)]) := by
  obtain ⟨M, C, q, hM⟩ := (polyTimeComputable_iff _).mp hf
  obtain ⟨a, d, b, E, hE⟩ := ladner_short_SAT_machine linear
  have he := (FinTM.computesFunInTime_iff _ _ _).mp
    ((FinTM.decidesInTime_iff _ _ _).mp hE)
  have hU (z : List Bool) : E.ComputesInTime (f z) [decide (f z ∈ SAT)]
      ((2 * b * (a * 2 ^ d + 4)) * (z.length + 1) ^ (d + 3)) := by
    have h := (he (f z)).mono (ladner_short_SAT_envelope a b d z.length (f z).length (hshort z))
    by_cases hz : f z ∈ SAT
    · simpa only [MultiTapeTM.indicator_of_mem hz, hz, decide_true] using h
    · simpa only [MultiTapeTM.indicator_of_not_mem hz, hz, decide_false] using h
  obtain ⟨N, hN⟩ := FinTM.exists_comp_on_image M E f _
    (fun n => C * (n + 1) ^ q)
    (fun n => (2 * b * (a * 2 ^ d + 4)) * (n + 1) ^ (d + 3)) hM hU
  apply (polyTimeComputable_iff _).mpr
  refine ⟨N, 2 * C + (2 * b * (a * 2 ^ d + 4)) + 2, max q (d + 3), ?_⟩
  apply (FinTM.computesFunInTime_iff _ _ _).mpr
  intro z
  exact ((FinTM.computesFunInTime_iff _ _ _).mp hN z).mono
    (ladner_composition_clock C q _ (d + 3) z.length)

/-- A canonical index below the double logarithm of a word's length is an FP test.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_index_lt_loglog_FP {f g : List Bool → List Bool}
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun S => [decide
      (LogProg.bitsVal (f S) < Nat.log 2 (Nat.log 2 (g S).length))]) := by
  have hl := ladner_lengthBits_FP
  have hi := BinArith.polyTimeComputable_normBits.comp hf
  have hcap := ladner_binary_log_FP.comp (ladner_binary_log_FP.comp (hl.comp hg))
  convert BinArith.polyTimeComputable_lt.comp (hi.pairEncode hcap) using 1
  funext S
  simp only [Function.comp_apply, LogProg.bitsVal_bits, BinArith.lt_pairEncode]

/-- The query guard is an FP test of canonical binary lengths and indices.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_validQuery_FP :
    PolyTimeComputable (fun S => [decide (ladner_validQuery S)]) := by
  have hl := ladner_lengthBits_FP
  have hx := hl.comp BinArith.polyTimeComputable_slot3
  have hlog := ladner_binary_log_FP.comp (hl.comp polyTimeComputable_pairFstD)
  convert polyTimeComputable_and
    (ladner_index_lt_loglog_FP BinArith.polyTimeComputable_slot2 polyTimeComputable_pairFstD)
    (BinArith.polyTimeComputable_le.comp (hx.pairEncode hlog)) using 1
  funext S
  simp only [Function.comp_apply, LogProg.bitsVal_bits, BinArith.le_pairEncode,
    Bool.decide_and, ladner_validQuery]

/-- The guarded simulator query has a polynomial preparation machine and clock.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Normalize the index, compute the input and context lengths, and test
`ladner_validQuery` in binary. Compute the power with `BinArith.powCap` capped at
`n³ + 1`; the short deadline bound makes saturation inert on valid queries. All
operations remain FP on malformed inputs. Mask all three fields on invalid queries,
then pair them and expose the preparation witness through `polyTimeComputable_iff`. -/
private theorem ladner_query_preparation :
    ∃ (M : FinTM Bool) (C q : ℕ),
      M.ComputesFunInTime ladner_queryPrep (fun n => C * (n + 1) ^ q) := by
  have hl := ladner_lengthBits_FP
  have hn := hl.comp polyTimeComputable_pairFstD
  have hi := BinArith.polyTimeComputable_normBits.comp BinArith.polyTimeComputable_slot2
  have hx := hl.comp BinArith.polyTimeComputable_slot3
  have hc : PolyTimeComputable (fun S : List Bool => Nat.bits ((pairFstD S).length ^ 3)) := by
    convert BinArith.polyTimeComputable_mul.comp
      ((BinArith.polyTimeComputable_mul.comp (hn.pairEncode hn)).pairEncode hn) using 1
    funext S
    simp only [Function.comp_apply, BinArith.mul_pairEncode]
    congr 1
    ring
  have hpower := BinArith.polyTimeComputable_powCap.comp (hx.pairEncode (hi.pairEncode hc))
  have hraw := BinArith.polyTimeComputable_mul.comp (hi.pairEncode hpower)
  have hd : PolyTimeComputable (fun S => Nat.bits (ladner_queryDeadline S)) := by
    convert polyTimeComputable_ite ladner_validQuery_FP hraw (polyTimeComputable_const []) using 1
    funext S
    by_cases hv : ladner_validQuery S
    · have ht := ladner_short_deadline (pairFstD S).length
        (LogProg.bitsVal (pairFstD (pairSndD S))) (pairSndD (pairSndD S)).length hv.1 hv.2
      have hcap : (pairSndD (pairSndD S)).length ^
          LogProg.bitsVal (pairFstD (pairSndD S)) ≤ (pairFstD S).length ^ 3 + 1 := by
        by_cases hi0 : LogProg.bitsVal (pairFstD (pairSndD S)) = 0
        · simp only [hi0, pow_zero]
          omega
        · have hi1 : 1 ≤ LogProg.bitsVal (pairFstD (pairSndD S)) := by omega
          have hm := Nat.mul_le_mul_right
            ((pairSndD (pairSndD S)).length ^ LogProg.bitsVal (pairFstD (pairSndD S))) hi1
          rw [one_mul] at hm
          omega
      simp only [Function.comp_apply, ladner_queryDeadline, hv, decide_true, if_true,
        BinArith.powCap_pairEncode, BinArith.mul_pairEncode, min_eq_left hcap]
    · simp only [Function.comp_apply, ladner_queryDeadline, hv, decide_false, Bool.false_eq_true, if_false,
        Nat.zero_bits]
  have hcode : PolyTimeComputable ladner_queryCode := by
    convert polyTimeComputable_ite ladner_validQuery_FP hi (polyTimeComputable_const []) using 1
    funext S
    simp only [Function.comp_apply, ladner_queryCode, decide_eq_true_eq]
  have hin : PolyTimeComputable ladner_queryInput := by
    convert polyTimeComputable_ite ladner_validQuery_FP BinArith.polyTimeComputable_slot3
      (polyTimeComputable_const []) using 1
    funext S
    simp only [ladner_queryInput, decide_eq_true_eq]
  exact (polyTimeComputable_iff _).mp ((hd.pairEncode hcode).pairEncode hin)

/-- The simulator's guarded numeric clock is polynomial in the serialized query length.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** For valid queries use `ladner_numeric_envelope` and the public
projection length bound. Invalid queries have empty code and input and deadline zero,
so their simulator budget reduces to its degree. -/
private theorem ladner_query_budget (S : List Bool) :
    expCode.simDegree *
      ((ladner_queryCode S).length + (ladner_queryInput S).length + ladner_queryDeadline S + 1) ^
        expCode.simDegree ≤
      (expCode.simDegree * 4 ^ expCode.simDegree) *
        (S.length + 1) ^ (3 * expCode.simDegree) := by
  by_cases hv : ladner_validQuery S
  · simp only [ladner_queryCode, ladner_queryInput, ladner_queryDeadline, hv, if_true]
    exact (ladner_numeric_envelope expCode.simDegree (pairFstD S).length
      (LogProg.bitsVal (pairFstD (pairSndD S))) (pairSndD (pairSndD S)) hv.1 hv.2).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
        (Nat.add_le_add_right (length_pairFstD_le S) 1) _))
  · simp only [ladner_queryCode, ladner_queryInput, ladner_queryDeadline, hv, if_false,
      List.length_nil, Nat.zero_add, one_pow, mul_one]
    calc expCode.simDegree ≤ expCode.simDegree * 4 ^ expCode.simDegree :=
          Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide))
         _ ≤ _ * (S.length + 1) ^ (3 * expCode.simDegree) :=
          Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))

/-- Canonicalize all memo entries using the public encoded-list map.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_table_FP : PolyTimeComputable
    (fun T => BinArith.encWords ((ladner_values T).map Nat.bits)) := by
  have hg := BinArith.polyTimeComputable_normBits.comp polyTimeComputable_pairSndD
  have h := (BinArith.polyTimeComputable_mapW hg).comp
    ((polyTimeComputable_const []).pairEncode polyTimeComputable_id)
  convert h using 1
  funext T
  simp only [Function.comp_apply, BinArith.mapW_pairEncode, pairSndD_pairEncode,
    ladner_values, List.map_map, id_eq]
  rfl

/-- The number of numeric memo entries is available in binary in polynomial time.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_values_length_FP :
    PolyTimeComputable (fun T => Nat.bits (ladner_values T).length) := by
  have hl := ladner_lengthBits_FP
  convert hl.comp BinArith.polyTimeComputable_countW using 1
  funext T
  simp only [Function.comp_apply, BinArith.countW_eq, List.length_replicate,
    ladner_values, List.length_map]

/-- Numeric memo entries are no more numerous than their serialized input bits.
`Complexity.BinArith.length_decWords_le` supplies the bound. -/
private theorem ladner_values_length_le (T : List Bool) : (ladner_values T).length ≤ T.length := by
  simpa only [ladner_values, List.length_map] using BinArith.length_decWords_le T

/-- Lookup of a memo exponent is FP after canonicalizing the table through `mapW`.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_get_value_FP : PolyTimeComputable (fun S : List Bool =>
    Nat.bits ((ladner_values (pairSndD S)).getD (pairFstD S).length 0)) := by
  have h := BinArith.polyTimeComputable_getW.comp (polyTimeComputable_pairFstD.pairEncode
    (ladner_table_FP.comp polyTimeComputable_pairSndD))
  convert h using 1
  funext S
  simp only [Function.comp_apply, BinArith.getW_pairEncode_bits]

/-- Check the padding syntax against an exponent read from the supplied table.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_tableSyntax (S : List Bool) : Bool :=
  match ladner_parse (pairFstD S) with
  | none => false
  | some (p, t) => decide (t = p.length ^ (ladner_values (pairSndD S)).getD p.length 0)

/-- Table-dependent padding syntax is FP, even for enormous malformed exponents: the
instance of `ladner_padSyntax_FP` whose exponent is read from the supplied table.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_tableSyntax_FP : PolyTimeComputable (fun S => [ladner_tableSyntax S]) := by
  have hh : PolyTimeComputable (fun z : List Bool => Nat.bits
      ((ladner_values (pairSndD (pairSndD z))).getD (pairFstD z).length 0)) := by
    convert ladner_get_value_FP.comp
      (polyTimeComputable_pairFstD.pairEncode BinArith.polyTimeComputable_slot3) using 1
    funext z
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  exact ladner_padSyntax_FP (h := fun S m => (ladner_values (pairSndD S)).getD m 0)
    polyTimeComputable_pairFstD hh

/-- The short-word guard relative to the memo entry count is an FP predicate.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_pad_guard_FP : PolyTimeComputable (fun S : List Bool =>
    [decide ((pairFstD S).length ≤ Nat.log 2 (ladner_values (pairSndD S)).length)]) := by
  have hl := ladner_lengthBits_FP
  have h := BinArith.polyTimeComputable_le.comp ((hl.comp polyTimeComputable_pairFstD).pairEncode
    (ladner_binary_log_FP.comp (ladner_values_length_FP.comp polyTimeComputable_pairSndD)))
  convert h using 1
  funext S
  simp only [Function.comp_apply, LogProg.bitsVal_bits, BinArith.le_pairEncode]

/-- Table-dependent padding membership of short words is polynomial-time.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Test the short-word guard and table-dependent syntax with the public
parser, list map, lookup, and saturated-power routines. Feed the parsed prefix to the
short-SAT machine only on guarded inputs, using the empty word as a default. The final
bit is masked by both syntax and guard, so no SAT fact about the default is assumed. -/
private theorem ladner_short_pad_FP
    (linear : ∃ V : Language Bool, V ∈ P ∧ ∀ x : List Bool, x ∈ SAT ↔
      ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ V) :
    PolyTimeComputable (fun S : List Bool => [decide
      ((pairFstD S).length ≤ Nat.log 2 (ladner_values (pairSndD S)).length ∧
        pairFstD S ∈ padSAT (fun m => (ladner_values (pairSndD S)).getD m 0))]) := by
  let f : List Bool → List Bool := fun S =>
    if (pairFstD S).length ≤ Nat.log 2 (ladner_values (pairSndD S)).length then
      pairFstD (pairSndD (ladner_parseWord (pairFstD S))) else []
  have hf : PolyTimeComputable f := by
    convert polyTimeComputable_ite ladner_pad_guard_FP
      (BinArith.polyTimeComputable_slot2.comp (ladner_parse_FP.comp polyTimeComputable_pairFstD))
      (polyTimeComputable_const []) using 1
    funext S
    simp only [f, Function.comp_apply, decide_eq_true_eq]
  have hfst0 : pairFstD [] = [] := pairFstD_nil
  have hsnd0 : pairSndD [] = [] := by
    simpa only [Function.iterate_one] using BinArith.iterate_pairSndD_nil 1
  have hshort (S : List Bool) : (f S).length ≤ Nat.log 2 S.length := by
    by_cases hg : (pairFstD S).length ≤ Nat.log 2 (ladner_values (pairSndD S)).length
    · dsimp only [f]
      rw [if_pos hg]
      cases hp : ladner_parse (pairFstD S) with
      | none => simp only [ladner_parseWord, hp, hsnd0, hfst0, List.length_nil, Nat.zero_le]
      | some pt =>
        obtain ⟨p, t⟩ := pt
        simp only [ladner_parseWord, hp, pairFstD_pairEncode, pairSndD_pairEncode]
        exact ((ladner_parsed_length hp).2.le.trans hg).trans
          (Nat.log_mono_right ((ladner_values_length_le _).trans (length_pairSndD_le S)))
    · simp only [f, hg, if_false, List.length_nil, Nat.zero_le]
  have hsat := ladner_short_SAT_on_image f hf hshort linear
  have hout := polyTimeComputable_and ladner_pad_guard_FP
    (polyTimeComputable_and ladner_tableSyntax_FP hsat)
  convert hout using 1
  funext S
  by_cases hg : (pairFstD S).length ≤ Nat.log 2 (ladner_values (pairSndD S)).length
  · cases hp : ladner_parse (pairFstD S) with
    | none =>
      have hn : pairFstD S ∉ padSAT (fun m => (ladner_values (pairSndD S)).getD m 0) := by
        rintro h
        obtain ⟨p, t, ht, -, -⟩ := ladner_pad_membership.mp h
        rw [hp] at ht
        cases ht
      simp only [hg, hn, and_false, decide_false, ladner_tableSyntax, hp, Bool.false_and,
        Bool.true_and, decide_true]
    | some pt =>
      obtain ⟨p, t⟩ := pt
      have hm : (pairFstD S ∈ padSAT (fun m => (ladner_values (pairSndD S)).getD m 0)) ↔
          t = p.length ^ (ladner_values (pairSndD S)).getD p.length 0 ∧ p ∈ SAT := by
        rw [ladner_pad_membership]
        constructor
        · rintro ⟨p', t', hp', ht, hsat⟩
          rw [hp, Option.some.injEq, Prod.mk.injEq] at hp'
          obtain ⟨rfl, rfl⟩ := hp'
          exact ⟨ht, hsat⟩
        · rintro ⟨ht, hsat⟩
          exact ⟨p, t, hp, ht, hsat⟩
      simp only [hg, true_and, decide_true, Bool.true_and, hm, Bool.decide_and,
        ladner_tableSyntax, hp, f, if_true, ladner_parseWord, pairFstD_pairEncode,
        pairSndD_pairEncode]
  · simp only [hg, false_and, decide_false, Bool.false_and]

/-- The candidate context guard is an FP test of lengths and canonical indices.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_ctxGuard_FP : PolyTimeComputable (fun C => [decide (ladner_ctxGuard C)]) := by
  have hl := ladner_lengthBits_FP
  have hcount := ladner_values_length_FP.comp BinArith.polyTimeComputable_slot3
  convert polyTimeComputable_and
    (BinArith.polyTimeComputable_beq.comp ((hl.comp polyTimeComputable_pairFstD).pairEncode hcount))
    (ladner_index_lt_loglog_FP BinArith.polyTimeComputable_slot2 polyTimeComputable_pairFstD) using 1
  funext C
  simp only [Function.comp_apply, BinArith.beq_pairEncode, ladner_ctxGuard, Bool.decide_and]

/-- Deleting the high sentinel bit is FP through reversal and the public tail routine.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_dropLast_FP : PolyTimeComputable (fun w : List Bool => w.dropLast) := by
  convert BinArith.polyTimeComputable_reverse.comp
    (polyTimeComputable_tail.comp BinArith.polyTimeComputable_reverse) using 1
  funext w
  simp only [Function.comp_apply, List.drop_one, List.tail_reverse, List.reverse_reverse]

/-- The guarded single-word acceptance equivalence has a polynomial-time test.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Decode the unary rank with a high sentinel, test the context and
short-input guards, and build a guarded uniform-simulator query. Compare its verdict
with short padded-SAT membership. The outer guards mask every invalid state; the
SAT and simulator implementations retain their explicit preparation clocks. -/
private theorem ladner_wordVerdict_FP
    (linear : ∃ V : Language Bool, V ∈ P ∧ ∀ x : List Bool, x ∈ SAT ↔
      ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ V) :
    PolyTimeComputable (fun S : List Bool =>
      [ladner_wordVerdict (pairFstD S) (pairSndD S).length]) := by
  have hl := ladner_lengthBits_FP
  let x : List Bool → List Bool := fun S => (Nat.bits ((pairSndD S).length + 1)).dropLast
  have hx : PolyTimeComputable x := by
    convert ladner_dropLast_FP.comp (BinArith.polyTimeComputable_add.comp
      ((hl.comp polyTimeComputable_pairSndD).pairEncode
        (polyTimeComputable_const (Nat.bits 1)))) using 1
    funext S
    simp only [x, Function.comp_apply, BinArith.add_pairEncode]
  let Q : List Bool → List Bool := fun S =>
    pairEncode (pairFstD (pairFstD S)) (pairEncode (pairFstD (pairSndD (pairFstD S))) (x S))
  have hQ : PolyTimeComputable Q :=
    (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD).pairEncode
      ((BinArith.polyTimeComputable_slot2.comp polyTimeComputable_pairFstD).pairEncode hx)
  have hprep : PolyTimeComputable ladner_queryPrep :=
    (polyTimeComputable_iff _).mpr ladner_query_preparation
  have hsim := (ladner_simulation_on_image ladner_queryCode ladner_queryInput
    ladner_queryDeadline hprep ⟨_, _, ladner_query_budget⟩).comp hQ
  have hpad := (ladner_short_pad_FP linear).comp
    (hx.pairEncode (BinArith.polyTimeComputable_slot3.comp polyTimeComputable_pairFstD))
  have hshort := BinArith.polyTimeComputable_le.comp ((hl.comp hx).pairEncode
    (ladner_binary_log_FP.comp (hl.comp (polyTimeComputable_pairFstD.comp
      polyTimeComputable_pairFstD))))
  have hout := polyTimeComputable_and (ladner_ctxGuard_FP.comp polyTimeComputable_pairFstD)
    (polyTimeComputable_and hshort
      (polyTimeComputable_not (BinArith.polyTimeComputable_xor hsim hpad)))
  convert hout using 1
  funext S
  have hxS : (Nat.bits ((pairSndD S).length + 1)).dropLast = x S := rfl
  by_cases hc : ladner_ctxGuard (pairFstD S)
  · by_cases hs : (x S).length ≤ Nat.log 2 (pairFstD (pairFstD S)).length
    · have hvalid : ladner_validQuery (Q S) := by
        simp only [ladner_validQuery, Q, pairFstD_pairEncode, pairSndD_pairEncode]
        exact ⟨hc.2, hs⟩
      have htable : (x S).length ≤
          Nat.log 2 (ladner_values (pairSndD (pairSndD (pairFstD S)))).length := by
        rw [← hc.1]
        exact hs
      by_cases hrun : (ladnerMachine (LogProg.bitsVal (pairFstD (pairSndD (pairFstD S))))).ComputesInTime (x S) [true]
          (LogProg.bitsVal (pairFstD (pairSndD (pairFstD S))) *
            (x S).length ^ LogProg.bitsVal (pairFstD (pairSndD (pairFstD S)))) <;>
        by_cases hsat : x S ∈ padSAT
          (fun m => (ladner_values (pairSndD (pairSndD (pairFstD S)))).getD m 0) <;>
        simp only [Function.comp_apply, ladner_wordVerdict, hxS, hc, hs, true_and,
          decide_true, Bool.true_and, BinArith.le_pairEncode, LogProg.bitsVal_bits,
          ladner_queryCode, ladner_queryInput, ladner_queryDeadline, hvalid, if_true,
          Q, pairFstD_pairEncode, pairSndD_pairEncode, ← ladnerMachine_eq,
          htable, hrun, hsat, iff_self, iff_true, iff_false, not_true_eq_false,
          decide_false, Bool.false_xor, Bool.true_xor,
          Bool.not_false, Bool.not_true]
    · simp only [Function.comp_apply, ladner_wordVerdict, hxS, hc, hs, true_and,
        false_and, decide_false, decide_true, BinArith.le_pairEncode, LogProg.bitsVal_bits,
        Bool.false_and, Bool.and_false]
  · simp only [Function.comp_apply, ladner_wordVerdict, hc, false_and, decide_false,
      Bool.false_and]

/-- A candidate-scan transition is FP once its single-word verdict is FP.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_testStep_FP
    (hw : PolyTimeComputable (fun S : List Bool =>
      [ladner_wordVerdict (pairFstD S) (pairSndD S).length])) :
    PolyTimeComputable ladner_testStep := by
  have hr := polyTimeComputable_pairFstD.comp BinArith.polyTimeComputable_slot3
  have hf := polyTimeComputable_headD.comp BinArith.polyTimeComputable_slot4
  have hword := hw.comp (polyTimeComputable_pairFstD.pairEncode hr)
  have hstep := polyTimeComputable_pairFstD.pairEncode
    ((polyTimeComputable_tail.comp BinArith.polyTimeComputable_slot2).pairEncode
      ((hr.append (polyTimeComputable_const [true])).pairEncode
        (polyTimeComputable_and hf hword)))
  convert polyTimeComputable_ite
    (polyTimeComputable_isNil.comp BinArith.polyTimeComputable_slot2)
    polyTimeComputable_id hstep using 1
  funext S
  simp only [Function.comp_apply, ladner_testStep, decide_eq_true_eq,
    pairFstD_pairEncode, pairSndD_pairEncode, id_eq]

/-- The short-word count needs one doubling per bit of the positive stage length.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_queryFuel (C : List Bool) : List Bool :=
  if pairFstD C = [] then [true] else Nat.bits (pairFstD C).length

/-- The count-generation counter has exactly `log₂ n + 1` symbols, including at zero.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_queryFuel_length (C : List Bool) :
    (ladner_queryFuel C).length = Nat.log 2 (pairFstD C).length + 1 := by
  by_cases hn : pairFstD C = []
  · simp only [ladner_queryFuel, hn, if_true, List.length_cons, List.length_nil,
      Nat.log_zero_right]
  · have hlen : (pairFstD C).length ≠ 0 := by
      intro h
      exact hn (List.eq_nil_of_length_eq_zero h)
    simp only [ladner_queryFuel, hn, if_false, LogProg.length_bits_eq_log hlen]

/-- The doubling loop's final unary count is linearly bounded by the context length.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_queryFuel_power_le (C : List Bool) :
    2 ^ (ladner_queryFuel C).length ≤ 2 * (C.length + 1) := by
  rw [ladner_queryFuel_length, pow_succ']
  exact Nat.mul_le_mul_left _ ((Nat.pow_log_le_add_one 2 _).trans
    (Nat.add_le_add_right (length_pairFstD_le C) 1))

/-- Initialize the bounded query-count generation through the existing iterator.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_countInit (C : List Bool) : List Bool :=
  pairEncode C (pairEncode (ladner_queryFuel C) [])

/-- A bounded doubling transition for query-count initialization; malformed states
cannot grow beyond the explicit guard. It is consumed by `BinArith.polyTimeComputable_iterate`.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_countStep (S : List Bool) : List Bool :=
  let C := pairFstD S
  let rem := pairFstD (pairSndD S)
  let acc := pairSndD (pairSndD S)
  let next := acc ++ acc ++ [true]
  if rem = [] then S else pairEncode C (pairEncode (rem.drop 1)
    (if next.length ≤ 2 * (C.length + 1) then next else acc))

/-- Query-count initialization is an FP serialization.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_countInit_FP : PolyTimeComputable ladner_countInit := by
  have hl := ladner_lengthBits_FP
  have hf : PolyTimeComputable ladner_queryFuel := by
    convert polyTimeComputable_ite (polyTimeComputable_isNil.comp polyTimeComputable_pairFstD)
      (polyTimeComputable_const [true]) (hl.comp polyTimeComputable_pairFstD) using 1
    funext C
    simp only [Function.comp_apply, ladner_queryFuel, decide_eq_true_eq]
  exact polyTimeComputable_id.pairEncode (hf.pairEncode (polyTimeComputable_const []))

/-- One guarded query-count doubling transition is polynomial-time.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_countStep_FP : PolyTimeComputable ladner_countStep := by
  have ha := BinArith.polyTimeComputable_slot3
  have hn := (ha.append ha).append (polyTimeComputable_const [true])
  have hb := (polyTimeComputable_polyUnary 2 1).comp polyTimeComputable_pairFstD
  have hg : PolyTimeComputable (fun S : List Bool =>
      [decide ((pairSndD (pairSndD S) ++ pairSndD (pairSndD S) ++ [true]).length ≤
        2 * ((pairFstD S).length + 1))]) := by
    convert polyTimeComputable_lenLe.comp (hb.pairEncode hn) using 1
    funext S
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
      List.length_replicate, pow_one]
  have hs := polyTimeComputable_pairFstD.pairEncode
    ((polyTimeComputable_tail.comp BinArith.polyTimeComputable_slot2).pairEncode
      (polyTimeComputable_ite hg hn ha))
  convert polyTimeComputable_ite (polyTimeComputable_isNil.comp BinArith.polyTimeComputable_slot2)
    polyTimeComputable_id hs using 1
  funext S
  simp only [Function.comp_apply, ladner_countStep, decide_eq_true_eq, id_eq]

/-- Every round of bounded query-count generation has the exact doubling value.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Before fuel exhaustion, `2^j - 1` becomes `2^(j+1) - 1` by
doubling and appending one. The full-fuel power bound makes the cap guard inert.
After exhaustion the transition is fixed, and the `min` in the exponent records this. -/
private theorem ladner_count_orbit (C : List Bool) (j : ℕ) :
    ladner_countStep^[j] (ladner_countInit C) =
      pairEncode C (pairEncode ((ladner_queryFuel C).drop j)
        (List.replicate (2 ^ min j (ladner_queryFuel C).length - 1) true)) := by
  induction j with
  | zero => simp only [Function.iterate_zero_apply, ladner_countInit, List.drop_zero,
      Nat.zero_min, pow_zero, Nat.sub_self, List.replicate_zero]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    by_cases hj : j < (ladner_queryFuel C).length
    · have hm : min j (ladner_queryFuel C).length = j := min_eq_left hj.le
      have hm' : min (j + 1) (ladner_queryFuel C).length = j + 1 := min_eq_left (by omega)
      have hp : 0 < 2 ^ j := Nat.pow_pos (by decide)
      have he : 2 * (2 ^ j - 1) + 1 = 2 ^ (j + 1) - 1 := by
        rw [pow_succ']
        omega
      have hn : List.replicate (2 ^ j - 1) true ++ List.replicate (2 ^ j - 1) true ++ [true] =
          List.replicate (2 ^ (j + 1) - 1) true := by
        rw [← List.replicate_add, ← List.replicate_succ']
        congr 1
        omega
      have hg : (List.replicate (2 ^ j - 1) true ++
          List.replicate (2 ^ j - 1) true ++ [true]).length ≤ 2 * (C.length + 1) := by
        rw [hn, List.length_replicate]
        have hp' := (Nat.pow_le_pow_right (by decide : 1 ≤ 2)
          (by omega : j + 1 ≤ (ladner_queryFuel C).length)).trans (ladner_queryFuel_power_le C)
        omega
      have hne : (ladner_queryFuel C).drop j ≠ [] := by
        intro h
        have hlen := congrArg List.length h
        rw [List.length_drop, List.length_nil] at hlen
        omega
      have hg' : (List.replicate (2 ^ (j + 1) - 1) true).length ≤ 2 * (C.length + 1) := by
        rw [← hn]
        exact hg
      simp only [ladner_countStep, pairFstD_pairEncode, pairSndD_pairEncode, hm,
        hm', hne, if_false, hn, hg', if_true, List.drop_drop]
    · have hm : min j (ladner_queryFuel C).length = (ladner_queryFuel C).length :=
        min_eq_right (by omega)
      have hm' : min (j + 1) (ladner_queryFuel C).length = (ladner_queryFuel C).length :=
        min_eq_right (by omega)
      simp only [ladner_countStep, pairFstD_pairEncode, pairSndD_pairEncode,
        List.drop_eq_nil_of_le (by omega : (ladner_queryFuel C).length ≤ j),
        List.drop_eq_nil_of_le (by omega : (ladner_queryFuel C).length ≤ j + 1),
        hm, hm', if_true]

/-- All initialized query-count generation states have a linear serialized envelope.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_count_size (C : List Bool) (j : ℕ) :
    (ladner_countStep^[j] (ladner_countInit C)).length ≤ 8 * (C.length + 1) ^ 1 := by
  rw [ladner_count_orbit]
  simp only [length_pairEncode, List.length_drop, List.length_replicate, pow_one]
  have hfuel : (ladner_queryFuel C).length ≤ C.length + 1 := by
    rw [ladner_queryFuel_length]
    exact Nat.add_le_add_right ((Nat.log_le_self 2 _).trans (length_pairFstD_le C)) 1
  have hpow := (Nat.pow_le_pow_right (by decide : 1 ≤ 2)
    (min_le_right j (ladner_queryFuel C).length)).trans (ladner_queryFuel_power_le C)
  omega

/-- The candidate scan's unary budget is constructed in polynomial time with a capped
application of the public iterator.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Generate `2^(log₂ n+1)-1` true bits by bounded doubling for one
round per binary length bit. Every intermediate state has the linear envelope
`ladner_count_size`; the guard protects malformed states. Compose the resulting
budget with the fixed initial rank and conjunction flag. -/
private theorem ladner_testInit_FP : PolyTimeComputable ladner_testInit := by
  have hloop := BinArith.polyTimeComputable_iterate ladner_countStep_FP ladner_countInit_FP
    1 1 8 1 (fun C j _ => ladner_count_size C j)
  have hu : PolyTimeComputable (fun C => List.replicate (ladner_queryCount C) true) := by
    convert BinArith.polyTimeComputable_slot3.comp hloop using 1
    funext C
    have hfuel : (ladner_queryFuel C).length ≤ 1 * (C.length + 1) ^ 1 := by
      rw [ladner_queryFuel_length, pow_one, one_mul]
      exact Nat.add_le_add_right ((Nat.log_le_self 2 _).trans (length_pairFstD_le C)) 1
    simp only [Function.comp_apply, ladner_count_orbit, pairSndD_pairEncode, min_eq_right hfuel]
    rw [ladner_queryFuel_length]
    rfl
  exact polyTimeComputable_id.pairEncode
    (hu.pairEncode ((polyTimeComputable_const []).pairEncode (polyTimeComputable_const [true])))

/-- Every initialized scan state has the exact remaining count, completed rank, and flag.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Induct on the iteration count. Before exhaustion the unary counter
loses one symbol and the conjunction gains exactly the next verdict. After exhaustion
the transition fixes the state, so both counters and the flag remain constant. -/
private theorem ladner_test_orbit (C : List Bool) (j : ℕ) :
    ladner_testStep^[j] (ladner_testInit C) =
      pairEncode C (pairEncode (List.replicate (ladner_queryCount C - j) true)
        (pairEncode (List.replicate (min j (ladner_queryCount C)) true)
          [decide (∀ r < min j (ladner_queryCount C), ladner_wordVerdict C r = true)])) := by
  induction j with
  | zero => simp only [Function.iterate_zero_apply, ladner_testInit, Nat.sub_zero,
      Nat.zero_min, List.replicate_zero, Nat.not_lt_zero, false_implies, implies_true,
      decide_true]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    by_cases hj : j < ladner_queryCount C
    · have hmin : min j (ladner_queryCount C) = j := min_eq_left hj.le
      have hmin' : min (j + 1) (ladner_queryCount C) = j + 1 := min_eq_left (by omega)
      have hne : List.replicate (ladner_queryCount C - j) true ≠ [] := by
        intro h
        have hlen := congrArg List.length h
        rw [List.length_replicate, List.length_nil] at hlen
        omega
      have hrem : ladner_queryCount C - j - 1 = ladner_queryCount C - (j + 1) := by omega
      have hrank : List.replicate j true ++ [true] = List.replicate (j + 1) true :=
        List.replicate_succ'.symm
      have hflag : (decide (∀ r < j, ladner_wordVerdict C r = true) && ladner_wordVerdict C j) =
          decide (∀ r < j + 1, ladner_wordVerdict C r = true) := by
        cases hv : ladner_wordVerdict C j <;>
          simp only [Nat.forall_lt_succ_right, Bool.decide_and, hv, Bool.false_eq_true,
            decide_false, decide_true, Bool.and_false, Bool.and_true]
      simp only [ladner_testStep, pairFstD_pairEncode, pairSndD_pairEncode, hne,
        if_false, hmin, hmin', List.drop_replicate, List.length_replicate,
        List.headD_cons, hrem, hrank, hflag]
    · have hmin : min j (ladner_queryCount C) = ladner_queryCount C := min_eq_right (by omega)
      have hmin' : min (j + 1) (ladner_queryCount C) = ladner_queryCount C :=
        min_eq_right (by omega)
      have hsub : ladner_queryCount C - j = 0 := by omega
      have hsub' : ladner_queryCount C - (j + 1) = 0 := by omega
      simp only [ladner_testStep, pairFstD_pairEncode, pairSndD_pairEncode, hmin,
        hmin', hsub, hsub', List.replicate_zero, if_true]

/-- The number of scan queries is bounded by twice the serialized context length plus two.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_queryCount_le (C : List Bool) :
    ladner_queryCount C ≤ 2 * (C.length + 1) := by
  have h := ladner_shortWords_count (pairFstD C).length
  simp only [ladner_shortWords, List.length_map, List.length_range] at h
  exact h.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right (length_pairFstD_le C) 1))

/-- Every state reached by an initialized candidate scan has linear serialized length.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_test_size (C : List Bool) (j : ℕ) :
    (ladner_testStep^[j] (ladner_testInit C)).length ≤ 12 * (C.length + 1) ^ 1 := by
  rw [ladner_test_orbit]
  simp only [length_pairEncode, List.length_replicate, List.length_cons, List.length_nil,
    pow_one]
  have h := ladner_queryCount_le C
  have hsum : ladner_queryCount C - j + min j (ladner_queryCount C) = ladner_queryCount C :=
    by omega
  omega

/-- After the bounded word scan, its masked flag is exactly the candidate predicate.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** The query-count bound ensures the scan is exhausted. Sentinel
completeness changes the conjunction over ranks into the universal short-word test.
The context guard supplies the table-length and index conditions, and masks all
inconsistent inputs. -/
private theorem ladner_candidate_readout (C : List Bool) :
    [ladner_candidate C] = if ladner_ctxGuard C then
      ladner_testOut (ladner_testStep^[2 * (C.length + 1) ^ 1] (ladner_testInit C))
      else [false] := by
  have hq : ladner_queryCount C ≤ 2 * (C.length + 1) ^ 1 := by
    simpa only [pow_one] using ladner_queryCount_le C
  by_cases hc : ladner_ctxGuard C
  · rw [if_pos hc, ladner_test_orbit]
    simp only [ladner_testOut, pairSndD_pairEncode, min_eq_right hq]
    have hequiv :
        (∀ x : List Bool, x.length ≤ Nat.log 2 (pairFstD C).length →
          ((ladnerMachine (LogProg.bitsVal (pairFstD (pairSndD C)))).ComputesInTime x [true]
            (LogProg.bitsVal (pairFstD (pairSndD C)) *
              x.length ^ LogProg.bitsVal (pairFstD (pairSndD C))) ↔
            x ∈ padSAT (fun m => (ladner_values (pairSndD (pairSndD C))).getD m 0))) ↔
        ∀ r < ladner_queryCount C, ladner_wordVerdict C r = true := by
      constructor
      · intro h r hr
        have hx : (Nat.bits (r + 1)).dropLast ∈
            ladner_shortWords (Nat.log 2 (pairFstD C).length) :=
          List.mem_map.mpr ⟨r, List.mem_range.mpr hr, rfl⟩
        have hlen := (ladner_shortWords_complete _ _).mp hx
        simp only [ladner_wordVerdict, hc, hlen, true_and, decide_eq_true_eq]
        exact h _ hlen
      · intro h x hx
        obtain ⟨r, hr, he⟩ := List.mem_map.mp ((ladner_shortWords_complete _ _).mpr hx)
        have htest := h r (List.mem_range.mp hr)
        simp only [ladner_wordVerdict, decide_eq_true_eq] at htest
        simpa only [he] using htest.2.2
    have hlen : decide ((pairFstD C).length =
        (ladner_values (pairSndD (pairSndD C))).length) = true := decide_eq_true hc.1
    have hindex : decide (LogProg.bitsVal (pairFstD (pairSndD C)) <
        Nat.log 2 (Nat.log 2 (pairFstD C).length)) = true := decide_eq_true hc.2
    simp only [ladner_candidate, Bool.decide_and, hlen, hindex, Bool.true_and, hequiv]
  · rw [if_neg hc]
    have hn : ¬ ((pairFstD C).length = (ladner_values (pairSndD (pairSndD C))).length ∧
        LogProg.bitsVal (pairFstD (pairSndD C)) < Nat.log 2 (Nat.log 2 (pairFstD C).length) ∧
        ∀ x : List Bool, x.length ≤ Nat.log 2 (pairFstD C).length →
          ((ladnerMachine (LogProg.bitsVal (pairFstD (pairSndD C)))).ComputesInTime x [true]
            (LogProg.bitsVal (pairFstD (pairSndD C)) *
              x.length ^ LogProg.bitsVal (pairFstD (pairSndD C))) ↔
            x ∈ padSAT (fun m => (ladner_values (pairSndD (pairSndD C))).getD m 0))) := by
      rintro ⟨hn, hi, -⟩
      exact hc ⟨hn, hi⟩
    simp only [ladner_candidate, hn, decide_false]

/-- The polynomial-time candidate test is the guarded readout of the existing bounded
iterator; no Ladner target is used or proved here.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Use the single-word FP verdict in the scan transition, the FP unary
initialization, and the linear bound on every scan state. Run `2(|C|+1)` rounds through
`BinArith.polyTimeComputable_iterate`, then read and mask its flag by the context guard. -/
private theorem ladner_candidate_FP
    (linear : ∃ V : Language Bool, V ∈ P ∧ ∀ x : List Bool, x ∈ SAT ↔
      ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ V) :
    PolyTimeComputable (fun S => [ladner_candidate S]) := by
  have hstep := ladner_testStep_FP (ladner_wordVerdict_FP linear)
  have hloop := BinArith.polyTimeComputable_iterate hstep ladner_testInit_FP 2 1 12 1
    (fun C j _ => ladner_test_size C j)
  have hflag := BinArith.polyTimeComputable_slot4.comp hloop
  convert polyTimeComputable_ite ladner_ctxGuard_FP hflag (polyTimeComputable_const [false]) using 1
  funext C
  simpa only [Function.comp_apply, ladner_testOut, decide_eq_true_eq] using ladner_candidate_readout C

/-! ### Polynomial-time selection and memo-table evaluation -/

/-- Prepare a candidate context using the number of decoded memo entries.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_selectCtx (T : List Bool) (i : ℕ) : List Bool :=
  pairEncode (List.replicate (ladner_values T).length true) (pairEncode (Nat.bits i) T)

/-- Initialize the candidate rank and the absorbing completion flag.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_selectInit (T : List Bool) : List Bool :=
  pairEncode T (pairEncode [] (pairEncode [] []))

/-- Test the next candidate, recording the first success or the exact cap.
[AB09, Theorem 3.3 and its proof] -/
private noncomputable def ladner_selectStep (S : List Bool) : List Bool :=
  let T := pairFstD S
  let rank := pairFstD (pairSndD S)
  let flag := pairFstD (pairSndD (pairSndD S))
  let cap := Nat.log 2 (Nat.log 2 (ladner_values T).length)
  if flag ≠ [] then S else
    if rank.length < cap then
      if ladner_candidate (ladner_selectCtx T rank.length) then
        pairEncode T (pairEncode rank (pairEncode [true] (Nat.bits rank.length)))
      else pairEncode T (pairEncode (rank ++ [true]) (pairEncode [] []))
    else pairEncode T (pairEncode rank (pairEncode [true] (Nat.bits cap)))

/-- Read the selected index from a completed selection state.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_selectOut (S : List Bool) : List Bool :=
  pairSndD (pairSndD (pairSndD S))

/-- In a prepared context the candidate predicate is precisely the bounded stage test.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_candidate_selectCtx (T : List Bool) (i : ℕ) :
    ladner_candidate (ladner_selectCtx T i) = decide
      (i < Nat.log 2 (Nat.log 2 (ladner_values T).length) ∧
        ∀ x : List Bool, x.length ≤ Nat.log 2 (ladner_values T).length →
          ((ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
            x ∈ padSAT (fun m => (ladner_values T).getD m 0))) := by
  simp only [ladner_candidate, ladner_selectCtx, pairFstD_pairEncode,
    pairSndD_pairEncode, List.length_replicate, LogProg.bitsVal_bits, true_and]

/-- The stage is at most its cap, every earlier candidate fails, and a stage below
the cap succeeds. [AB09, Theorem 3.3 and its proof]

**Proof sketch.** Apply `Nat.find_spec` and `Nat.find_min` when a bounded candidate
exists. Otherwise every bounded candidate fails and the stage is exactly the cap. -/
private theorem ladner_stage_spec (T : List Bool) :
    ladner_stage (ladner_values T) ≤ Nat.log 2 (Nat.log 2 (ladner_values T).length) ∧
      (∀ i < ladner_stage (ladner_values T),
        ladner_candidate (ladner_selectCtx T i) = false) ∧
      (ladner_stage (ladner_values T) < Nat.log 2 (Nat.log 2 (ladner_values T).length) →
        ladner_candidate (ladner_selectCtx T (ladner_stage (ladner_values T))) = true) := by
  simp only [ladner_stage]
  split_ifs with h
  · refine ⟨(Nat.find_spec h).1.le, ?_, ?_⟩
    · intro i hi
      rw [ladner_candidate_selectCtx]
      exact decide_eq_false (Nat.find_min h hi)
    · intro _
      rw [ladner_candidate_selectCtx]
      exact decide_eq_true (Nat.find_spec h)
  · refine ⟨le_rfl, ?_, ?_⟩
    · intro i _
      rw [ladner_candidate_selectCtx]
      exact decide_eq_false (fun hi => h ⟨i, hi⟩)
    · intro hi
      exact False.elim (Nat.lt_irrefl _ hi)

/-- Selection initialization uses only pairing with fixed empty words.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_selectInit_FP : PolyTimeComputable ladner_selectInit := by
  exact polyTimeComputable_id.pairEncode ((polyTimeComputable_const []).pairEncode
    ((polyTimeComputable_const []).pairEncode (polyTimeComputable_const [])))

/-- The selection transition is polynomial-time whenever the candidate test is.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Count entries through `countW`, encode the unary rank's length,
and compute the cap with two binary logarithms. Compose the candidate test on this
prepared context, then use FP conditionals for success, exhaustion and completion. -/
private theorem ladner_selectStep_FP
    (hc : PolyTimeComputable (fun C => [ladner_candidate C])) :
    PolyTimeComputable ladner_selectStep := by
  have hcount : PolyTimeComputable
      (fun T => List.replicate (ladner_values T).length true) := by
    convert BinArith.polyTimeComputable_countW using 1
    funext T
    simp only [BinArith.countW_eq, ladner_values, List.length_map]
  have hT := polyTimeComputable_pairFstD
  have hr := BinArith.polyTimeComputable_slot2
  have hi := ladner_lengthBits_FP.comp hr
  have hcap := ladner_binary_log_FP.comp
    (ladner_binary_log_FP.comp (ladner_values_length_FP.comp hT))
  have hctx := (hcount.comp hT).pairEncode (hi.pairEncode hT)
  have htest := hc.comp hctx
  have hlt : PolyTimeComputable (fun S => [decide
      ((pairFstD (pairSndD S)).length <
        Nat.log 2 (Nat.log 2 (ladner_values (pairFstD S)).length))]) := by
    convert ladner_index_lt_loglog_FP hi (hcount.comp hT) using 1
    funext S
    simp only [Function.comp_apply, LogProg.bitsVal_bits, List.length_replicate]
  have hsuccess := hT.pairEncode
    (hr.pairEncode ((polyTimeComputable_const [true]).pairEncode hi))
  have hnext := hT.pairEncode ((hr.append (polyTimeComputable_const [true])).pairEncode
    ((polyTimeComputable_const []).pairEncode (polyTimeComputable_const [])))
  have hfinish := hT.pairEncode
    (hr.pairEncode ((polyTimeComputable_const [true]).pairEncode hcap))
  convert polyTimeComputable_ite
    (polyTimeComputable_isNil.comp
      (polyTimeComputable_pairFstD.comp BinArith.polyTimeComputable_slot3))
    (polyTimeComputable_ite hlt (polyTimeComputable_ite htest hsuccess hnext) hfinish)
    polyTimeComputable_id using 1
  funext S
  simp only [Function.comp_apply, ladner_selectStep, ladner_selectCtx,
    LogProg.bitsVal_bits, decide_eq_true_eq, id_eq]
  by_cases hf : pairFstD (pairSndD (pairSndD S)) = [] <;>
    simp only [hf, ne_eq, not_true_eq_false, not_false_eq_true, if_true, if_false]

/-- The exact selection orbit: before selection the rank is the iteration count;
after selection the completed state is fixed. [AB09, Theorem 3.3 and its proof]

**Proof sketch.** Every index strictly below the stage fails by `ladner_stage_spec`.
At the stage either its candidate succeeds or the cap is reached. Both cases record
the same value and set the completion flag, which makes all later steps fixed. -/
private theorem ladner_select_orbit (T : List Bool) (j : ℕ) :
    ladner_selectStep^[j] (ladner_selectInit T) =
      if j ≤ ladner_stage (ladner_values T) then
        pairEncode T (pairEncode (List.replicate j true) (pairEncode [] []))
      else pairEncode T (pairEncode (List.replicate (ladner_stage (ladner_values T)) true)
        (pairEncode [true] (Nat.bits (ladner_stage (ladner_values T))))) := by
  obtain ⟨hcap, hprev, hsuccess⟩ := ladner_stage_spec T
  induction j with
  | zero => simp only [Function.iterate_zero_apply, ladner_selectInit, Nat.zero_le,
      if_true, List.replicate_zero]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    by_cases hj : j < ladner_stage (ladner_values T)
    · have hj' : j + 1 ≤ ladner_stage (ladner_values T) := by omega
      have hr : j < Nat.log 2 (Nat.log 2 (ladner_values T).length) := hj.trans_le hcap
      simp only [if_pos hj.le, if_pos hj', ladner_selectStep, pairFstD_pairEncode,
        pairSndD_pairEncode, List.length_replicate, ne_eq, not_true_eq_false,
        if_false, if_pos hr, hprev j hj, Bool.false_eq_true, ← List.replicate_succ']
    · by_cases he : j = ladner_stage (ladner_values T)
      · subst j
        have hn : ¬ ladner_stage (ladner_values T) + 1 ≤ ladner_stage (ladner_values T) :=
          by omega
        simp only [if_pos le_rfl, if_neg hn, ladner_selectStep, pairFstD_pairEncode,
          pairSndD_pairEncode, List.length_replicate, ne_eq, not_true_eq_false, if_false]
        by_cases hs : ladner_stage (ladner_values T) <
            Nat.log 2 (Nat.log 2 (ladner_values T).length)
        · simp only [if_pos hs, hsuccess hs, if_true]
        · have heq : ladner_stage (ladner_values T) =
              Nat.log 2 (Nat.log 2 (ladner_values T).length) := by omega
          rw [if_neg hs, ← heq]
      · have hn : ¬ j ≤ ladner_stage (ladner_values T) := by omega
        have hn' : ¬ j + 1 ≤ ladner_stage (ladner_values T) := by omega
        simp only [if_neg hn, if_neg hn', ladner_selectStep, pairFstD_pairEncode,
          pairSndD_pairEncode, List.cons_ne_nil, ne_eq, not_false_eq_true, if_true]

/-- The selected stage is bounded by the serialized table length.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_stage_length_le (T : List Bool) :
    ladner_stage (ladner_values T) ≤ T.length := by
  exact (ladner_stage_spec T).1.trans ((Nat.log_le_self 2 _).trans
    ((Nat.log_le_self 2 _).trans (ladner_values_length_le T)))

/-- Every selection state, including every fixed state after completion, has linear
serialized length. [AB09, Theorem 3.3 and its proof] -/
private theorem ladner_select_size (T : List Bool) (j : ℕ) :
    (ladner_selectStep^[j] (ladner_selectInit T)).length ≤ 12 * (T.length + 1) ^ 1 := by
  have hstage := ladner_stage_length_le T
  have hbits := (length_bits_le_self (ladner_stage (ladner_values T))).trans hstage
  rw [ladner_select_orbit]
  split_ifs with hj <;>
    simp only [length_pairEncode, List.length_replicate, List.length_nil,
      List.length_cons, pow_one] <;> omega

/-- After `|T|+1` rounds the selected word is exactly the stage's binary digits.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_select_readout (T : List Bool) :
    ladner_selectOut (ladner_selectStep^[1 * (T.length + 1) ^ 1] (ladner_selectInit T)) =
      Nat.bits (ladner_stage (ladner_values T)) := by
  have hstage := ladner_stage_length_le T
  have hn : ¬ 1 * (T.length + 1) ^ 1 ≤ ladner_stage (ladner_values T) := by
    simp only [pow_one, one_mul]
    omega
  simp only [ladner_select_orbit, if_neg hn, ladner_selectOut, pairSndD_pairEncode]

/-- The stage is computed by the public bounded iterator followed by its fourth-slot
readout. [AB09, Theorem 3.3 and its proof] -/
private theorem ladner_stage_FP
    (hcheck : PolyTimeComputable (fun S => [ladner_candidate S])) :
    PolyTimeComputable (fun T => Nat.bits (ladner_stage (ladner_values T))) := by
  have hloop := BinArith.polyTimeComputable_iterate (ladner_selectStep_FP hcheck)
    ladner_selectInit_FP 1 1 12 1 (fun T j _ => ladner_select_size T j)
  convert BinArith.polyTimeComputable_slot4.comp hloop using 1
  funext T
  exact (ladner_select_readout T).symm

/-- A table of all earlier correct values computes the global delayed index at its
length. [AB09, Theorem 3.3 and its proof]

**Proof sketch.** Every padding exponent queried by a word of length at most `log₂ n`
has index strictly below that word's length, hence below `n`. Apply `padSAT_congr`
with the table hypothesis, then identify the two minimum-index equations. -/
private theorem ladner_stage_correct (vs : List ℕ)
    (hvs : ∀ m < vs.length, vs.getD m 0 = ladnerH m) :
    ladner_stage vs = ladnerH vs.length := by
  have htests (i : ℕ) :
      (∀ x : List Bool, x.length ≤ Nat.log 2 vs.length →
        ((ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
          x ∈ padSAT (fun m => vs.getD m 0))) ↔
      ∀ x : List Bool, x.length ≤ Nat.log 2 vs.length →
        ((ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
          x ∈ padSAT ladnerH) := by
    apply forall_congr'
    intro x
    apply imp_congr_right
    intro hx
    exact iff_congr Iff.rfl (padSAT_congr (fun m hm =>
      hvs m (hm.trans_le (hx.trans (Nat.log_le_self 2 vs.length)))))
  rw [ladner_stage, ladnerH_eq]
  simp_rw [htests]

/-- The memo driver starts with the immutable unary input length and an empty table.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_memoInit (z : List Bool) : List Bool :=
  pairEncode (List.replicate z.length true) []

/-- Append the next stage value to the memo table, preserving the requested index.
[AB09, Theorem 3.3 and its proof] -/
private noncomputable def ladner_memoStep (S : List Bool) : List Bool :=
  pairEncode (pairFstD S)
    (pairSndD S ++ pairEncode (Nat.bits (ladner_stage (ladner_values (pairSndD S)))) [])

/-- One memo step composes the stage computation, append and pairing.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_memoStep_FP
    (hstage : PolyTimeComputable (fun T => Nat.bits (ladner_stage (ladner_values T)))) :
    PolyTimeComputable ladner_memoStep := by
  exact polyTimeComputable_pairFstD.pairEncode (polyTimeComputable_pairSndD.append
    ((hstage.comp polyTimeComputable_pairSndD).pairEncode (polyTimeComputable_const [])))

/-- The unary input-length marker and empty initial table are polynomial-time.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_memoInit_FP : PolyTimeComputable ladner_memoInit := by
  exact polyTimeComputable_unary.pairEncode (polyTimeComputable_const [])

/-- Every memo orbit consists exactly of the first `j` delayed-index values.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Decode the canonical encoded table with `decWords_encWords` and
`bitsVal_bits`. Its in-range entries satisfy the hypothesis of `ladner_stage_correct`.
That theorem supplies the next value, and `encWords_append_singleton` identifies the
serialized append with the longer history. -/
private theorem ladner_memo_orbit (z : List Bool) (j : ℕ) :
    ladner_memoStep^[j] (ladner_memoInit z) =
      pairEncode (List.replicate z.length true)
        (BinArith.encWords ((List.range j).map (fun m => Nat.bits (ladnerH m)))) := by
  induction j with
  | zero => simp only [Function.iterate_zero_apply, ladner_memoInit, List.range_zero,
      List.map_nil, BinArith.encWords_nil]
  | succ j ih =>
    have hv : ladner_values (BinArith.encWords
        ((List.range j).map (fun m => Nat.bits (ladnerH m)))) =
        (List.range j).map ladnerH := by
      rw [ladner_values, BinArith.decWords_encWords, List.map_map]
      congr 1
      funext m
      show LogProg.bitsVal (Nat.bits (ladnerH m)) = ladnerH m
      exact LogProg.bitsVal_bits _
    have hcorrect : ladner_stage (ladner_values (BinArith.encWords
        ((List.range j).map (fun m => Nat.bits (ladnerH m))))) = ladnerH j := by
      rw [hv]
      have h := ladner_stage_correct ((List.range j).map ladnerH) (fun m hm => by
        have hm' : m < j := by simpa only [List.length_map, List.length_range] using hm
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range hm', Option.map_some, Option.getD_some])
      simpa only [List.length_map, List.length_range] using h
    rw [Function.iterate_succ_apply', ih]
    simp only [ladner_memoStep, pairFstD_pairEncode, pairSndD_pairEncode, hcorrect,
      List.range_succ, List.map_append, List.map_singleton, BinArith.encWords_append_singleton]

/-- Every memo state through the requested final round has quadratic serialized length.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_memo_size (z : List Bool) (j : ℕ) (hj : j ≤ z.length + 1) :
    (ladner_memoStep^[j] (ladner_memoInit z)).length ≤ 4 * (z.length + 1) ^ 2 := by
  have hwords : ∀ w ∈ (List.range j).map (fun m => Nat.bits (ladnerH m)),
      w.length ≤ z.length := by
    intro w hw
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hw
    have hm' := List.mem_range.mp hm
    exact (length_bits_le_self _).trans ((ladnerH_le m).trans
      ((Nat.log_le_self 2 _).trans ((Nat.log_le_self 2 m).trans (by omega))))
  have htable := BinArith.length_encWords_le _ z.length hwords
  simp only [List.length_map, List.length_range] at htable
  have hbound := htable.trans (Nat.mul_le_mul_right (2 * z.length + 2) hj)
  rw [ladner_memo_orbit]
  simp only [length_pairEncode, List.length_replicate]
  nlinarith

/-- The existing word-table lookup reads the delayed index at the requested input length.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_memo_readout (z : List Bool) :
    BinArith.getW (ladner_memoStep^[1 * (z.length + 1) ^ 1] (ladner_memoInit z)) =
      Nat.bits (ladnerH z.length) := by
  simp only [pow_one, one_mul, ladner_memo_orbit]
  show BinArith.getW (pairEncode (List.replicate z.length true)
    (BinArith.encWords ((List.range (z.length + 1)).map (Nat.bits ∘ ladnerH)))) =
      Nat.bits (ladnerH z.length)
  rw [← List.map_map (g := Nat.bits) (f := ladnerH),
    BinArith.getW_pairEncode_bits, List.length_replicate]
  congr 1
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; omega),
    List.getElem_map, List.getElem_range]


/-! ### NP membership of the padded language -/

/-- The padded-language verifier checks the final separator, prescribed suffix and
an exact-length SAT certificate for the parsed prefix.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_verifier (h : ℕ → ℕ) (V : Language Bool) : Language Bool :=
  {S | match ladner_parse (pairFstD S) with
    | none => False
    | some (p, t) => t = p.length ^ h p.length ∧
      (pairSndD S).length = p.length + 1 ∧ p ++ pairSndD S ∈ V}

/-- The padded verifier is in P when the exponent function is polynomial-time and
the prefix verifier is in P. [AB09, Theorem 3.3 and its proof]

**Proof sketch.** Use the existing parser serialization to recover the prefix.
Intersect the capped padding-syntax test, a certificate-length comparison and the
polynomial preimage of `V` under prefix/certificate concatenation. The syntax test
rejects a missing separator before any default prefix can cause acceptance. -/
private theorem ladner_verifier_P {h : ℕ → ℕ} {V : Language Bool}
    (hp : PolyTimeComputable (fun x : List Bool => Nat.bits (h x.length)))
    (hV : V ∈ P) : ladner_verifier h V ∈ P := by
  let pre (S : List Bool) : List Bool :=
    pairFstD (pairSndD (ladner_parseWord (pairFstD S)))
  have hprefix : PolyTimeComputable pre :=
    BinArith.polyTimeComputable_slot2.comp (ladner_parse_FP.comp polyTimeComputable_pairFstD)
  have hsyntax := mem_P_of_test ((ladner_syntax_FP hp).comp polyTimeComputable_pairFstD)
  have hlength := lenEq_preimage_mem_P polyTimeComputable_pairSndD
    (hprefix.append (polyTimeComputable_const [true]))
  have hverify := preimage_mem_P hV (hprefix.append polyTimeComputable_pairSndD)
  let W : Language Bool := {S | ladner_padSyntax h (pairFstD S) = true ∧
    (pairSndD S).length = (pre S ++ [true]).length ∧ pre S ++ pairSndD S ∈ V}
  have hW : W ∈ P :=
    show W ∈ P from inter_mem_P hsyntax (inter_mem_P hlength hverify)
  have heq : ladner_verifier h V = W := by
    funext S
    apply propext
    show (match ladner_parse (pairFstD S) with
      | none => False
      | some (p, t) => t = p.length ^ h p.length ∧
        (pairSndD S).length = p.length + 1 ∧ p ++ pairSndD S ∈ V) ↔
      ladner_padSyntax h (pairFstD S) = true ∧
        (pairSndD S).length = (pre S ++ [true]).length ∧ pre S ++ pairSndD S ∈ V
    cases hs : ladner_parse (pairFstD S) with
    | none => simp only [ladner_padSyntax, hs, Bool.false_eq_true, false_and]
    | some pt =>
      obtain ⟨p, t⟩ := pt
      simp only [pre, ladner_padSyntax, ladner_parseWord, hs, decide_eq_true_eq,
        pairSndD_pairEncode, pairFstD_pairEncode, List.length_append,
        List.length_cons, List.length_nil, Nat.zero_add]
  rw [heq]
  exact hW

/-- Padding membership is equivalent to a paired verifier certificate of length
at most the padded input's length plus one. [AB09, Theorem 3.3 and its proof]

**Proof sketch.** Successful padding supplies the parser's unique prefix and a
linear SAT certificate, whose length is bounded by the strict parsed-prefix bound.
Conversely the verifier supplies the suffix equation and a SAT certificate for
that prefix; `ladner_pad_membership` reconstructs membership without guessing a split. -/
private theorem ladner_verifier_equiv {h : ℕ → ℕ} {V : Language Bool}
    (hcert : ∀ x : List Bool, x ∈ SAT ↔
      ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ V) (y : List Bool) :
    y ∈ padSAT h ↔ ∃ u : List Bool,
      u.length ≤ y.length + 1 ∧ pairEncode y u ∈ ladner_verifier h V := by
  have hread (u : List Bool) : pairEncode y u ∈ ladner_verifier h V ↔
      match ladner_parse y with
      | none => False
      | some (p, t) => t = p.length ^ h p.length ∧
        u.length = p.length + 1 ∧ p ++ u ∈ V := by
    show (match ladner_parse (pairFstD (pairEncode y u)) with
      | none => False
      | some (p, t) => t = p.length ^ h p.length ∧
        (pairSndD (pairEncode y u)).length = p.length + 1 ∧
          p ++ pairSndD (pairEncode y u) ∈ V) ↔ _
    simp only [pairFstD_pairEncode, pairSndD_pairEncode]
  rw [ladner_pad_membership]
  constructor
  · rintro ⟨p, t, hparse, hpower, hp⟩
    obtain ⟨u, hlen, hVu⟩ := (hcert p).mp hp
    refine ⟨u, ?_, (hread u).mpr ?_⟩
    · have hshort := (ladner_parsed_length hparse).2
      omega
    · rw [hparse]
      exact ⟨hpower, hlen, hVu⟩
  · rintro ⟨u, _, hu⟩
    have hv := (hread u).mp hu
    cases hparse : ladner_parse y with
    | none =>
      rw [hparse] at hv
      exact hv.elim
    | some pt =>
      obtain ⟨p, t⟩ := pt
      rw [hparse] at hv
      exact ⟨p, t, rfl, hv.1, (hcert p).mpr ⟨u, hv.2.1, hv.2.2⟩⟩

/-- Polynomial-time padding exponents preserve SAT's NP membership through its
linear verifier. [AB09, Theorem 3.3 and its proof] -/
private theorem ladner_padded_NP {h : ℕ → ℕ}
    (hp : PolyTimeComputable (fun x : List Bool => Nat.bits (h x.length)))
    (linear : ∃ V : Language Bool, V ∈ P ∧ ∀ x : List Bool, x ∈ SAT ↔
      ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ V) :
    padSAT h ∈ NP := by
  obtain ⟨V, hV, hcert⟩ := linear
  refine mem_NP_iff_exists_length_le.mpr ⟨1, 1, ladner_verifier h V, ladner_verifier_P hp hV,
    fun y => ?_⟩
  simpa only [one_mul, pow_one] using ladner_verifier_equiv (h := h) hcert y


/-! ### Bounded padding and the intermediate language -/

/-- The literal padded word keeps its input before a final false separator.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_padWord (h : ℕ → ℕ) (x : List Bool) : List Bool :=
  x ++ false :: List.replicate (x.length ^ h x.length) true

/-- A value bound on the exponent gives a polynomial bound on the literal padded word.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_bounded_pad_length {h : ℕ → ℕ} {C : ℕ} (hb : ∀ n, h n ≤ C)
    (x : List Bool) : (ladner_padWord h x).length ≤ 2 * (x.length + 1) ^ (C + 1) := by
  have hpower : x.length ^ h x.length ≤ (x.length + 1) ^ C :=
    (Nat.pow_le_pow_left (Nat.le_succ _) _).trans
      (Nat.pow_le_pow_right (Nat.succ_pos _) (hb _))
  have hprefix : x.length + 1 ≤ (x.length + 1) ^ (C + 1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (Nat.succ_pos x.length)
      (show 1 ≤ C + 1 by omega)
  have hdegree : (x.length + 1) ^ C ≤ (x.length + 1) ^ (C + 1) :=
    Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_succ _)
  simp only [ladner_padWord, List.length_append, List.length_cons, List.length_replicate]
  omega

/-- A fixed finite set of exponent values has an FP unary-power selector.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Each fixed power is a finite composition of the public unary
multiplication row, followed by the unary length map. Starting with the constant
zeroth power, add one canonical binary equality test and one fixed-power branch
for each possible exponent. Induction constructs finite compositions of FP closures
whose number of branches depends only on the fixed bound. -/
private theorem ladner_power_cases_FP {h : ℕ → ℕ}
    (hp : PolyTimeComputable (fun x : List Bool => Nat.bits (h x.length))) (C : ℕ) :
    ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
      ∀ x, h x.length ≤ C → f x = List.replicate (x.length ^ h x.length) true := by
  have hpower (k : ℕ) :
      PolyTimeComputable (fun x : List Bool => List.replicate (x.length ^ k) true) := by
    induction k with
    | zero =>
      simpa only [pow_zero, List.replicate_one] using polyTimeComputable_const [true]
    | succ k ih =>
      have hmul := polyTimeComputable_unary.comp
        (BinArith.polyTimeComputable_mulU.comp (ih.pairEncode polyTimeComputable_unary))
      convert hmul using 1
      funext x
      simp only [Function.comp_apply, BinArith.length_mulU, List.length_replicate, pow_succ]
  induction C with
  | zero =>
    refine ⟨fun _ => [true], polyTimeComputable_const [true], ?_⟩
    intro x hx
    have hz : h x.length = 0 := by omega
    simp only [hz, pow_zero, List.replicate_one]
  | succ C ih =>
    obtain ⟨f, hf, hcorrect⟩ := ih
    let test (x : List Bool) : Bool :=
      BinArith.beq (pairEncode (Nat.bits (h x.length)) (Nat.bits (C + 1)))
    have htest := BinArith.polyTimeComputable_beq.comp
      (hp.pairEncode (polyTimeComputable_const (Nat.bits (C + 1))))
    refine ⟨fun x => if test x then List.replicate (x.length ^ (C + 1)) true else f x,
      polyTimeComputable_ite htest (hpower (C + 1)) hf, ?_⟩
    intro x hx
    by_cases he : h x.length = C + 1
    · simp only [test, BinArith.beq_pairEncode, he, decide_true, if_true]
    · have hsmall : h x.length ≤ C := by omega
      simp only [test, BinArith.beq_pairEncode, he, decide_false, Bool.false_eq_true, if_false,
        hcorrect x hsmall]

/-- Polynomial-time exponents with bounded values give a polynomial-time literal
padding map, through the finite unary-power selector.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_bounded_pad_FP {h : ℕ → ℕ} {C : ℕ}
    (hp : PolyTimeComputable (fun x : List Bool => Nat.bits (h x.length)))
    (hb : ∀ n, h n ≤ C) : PolyTimeComputable (ladner_padWord h) := by
  obtain ⟨f, hf, hcorrect⟩ := ladner_power_cases_FP hp C
  have hpad := polyTimeComputable_id.append ((polyTimeComputable_const [false]).append hf)
  convert hpad using 1
  funext x
  simp only [ladner_padWord, id_eq, List.singleton_append, hcorrect x (hb _)]

/-- The final-separator parser recovers the original prefix of its literal padded
word, so padding preserves its SAT membership.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_padWord_membership (h : ℕ → ℕ) (x : List Bool) :
    ladner_padWord h x ∈ padSAT h ↔ x ∈ SAT := by
  simp only [ladner_pad_membership, ladner_padWord, ladner_parse_pad,
    Option.some.injEq, Prod.mk.injEq, and_assoc, exists_and_left, exists_eq_left', true_and]

/-- Bounded polynomial-time padding reduces SAT to its padded language.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_bounded_pad_reduction {h : ℕ → ℕ} {C : ℕ}
    (hp : PolyTimeComputable (fun x : List Bool => Nat.bits (h x.length)))
    (hb : ∀ n, h n ≤ C) : PolyTimeReducible SAT (padSAT h) :=
  (polyTimeReducible_iff _ _).mpr ⟨ladner_padWord h, ladner_bounded_pad_FP hp hb,
    fun x => (ladner_padWord_membership h x).symm⟩

/-- A P decider for the padded witness would bound its exponent and hence put SAT
in P, contradicting P ≠ NP. [AB09, Theorem 3.3 and its proof] -/
private theorem ladner_outside_P (hne : P ≠ NP)
    (hp : PolyTimeComputable (fun x : List Bool => Nat.bits (ladnerH x.length)))
    (hbounded : SAT_H ∈ P → ∃ C, ∀ n, ladnerH n ≤ C) : SAT_H ∉ P := by
  intro hP
  obtain ⟨C, hC⟩ := hbounded hP
  rw [SAT_H_eq] at hP
  exact hne (P_eq_NP_of_NPHard_mem_P SAT_NPHard
    (mem_P_of_polyTimeReducible (ladner_bounded_pad_reduction hp hC) hP))

/-- NP-completeness of the padded witness would combine divergent padding with
the shrinking argument to put SAT in P. [AB09, Theorem 3.3 and its proof] -/
private theorem ladner_not_complete (hne : P ≠ NP)
    (hp : PolyTimeComputable (fun x : List Bool => Nat.bits (ladnerH x.length)))
    (hout : SAT_H ∉ P)
    (hdiv : SAT_H ∉ P → ∀ C, ∃ N, ∀ n ≥ N, C ≤ ladnerH n)
    (hpadding : ∀ h : ℕ → ℕ,
      PolyTimeComputable (fun x : List Bool => Nat.bits (h x.length)) →
      (∀ C, ∃ N, ∀ n ≥ N, C ≤ h n) → NPHard (padSAT h) → SAT ∈ P) :
    ¬ NPComplete SAT_H := by
  intro hc
  obtain ⟨-, hH⟩ := (NPComplete_iff _).mp hc
  rw [SAT_H_eq] at hH
  exact hne (P_eq_NP_of_NPHard_mem_P SAT_NPHard (hpadding ladnerH hp (hdiv hout) hH))

/-! ### The theorem and its remaining targets -/

/-- The binary digits of the delayed index at an input's length are polynomial-time
computable. [AB09, Theorem 3.3 and its proof]

**Proof sketch.** Maintain previously computed index values, simulate only the short
inputs through the uniformly timed acceptance simulator, and test SAT on short words.
Polynomially bounded iteration supplies the memo-table driver; the short-SAT search,
poly-bounded simulator invocation and state-size ledger are separate route obligations. -/
theorem ladnerH_polyTime :
    PolyTimeComputable (fun x => Nat.bits (ladnerH x.length)) := by
  have hloop := BinArith.polyTimeComputable_iterate
    (ladner_memoStep_FP (ladner_stage_FP (ladner_candidate_FP SAT_exists_linear_verifier)))
    ladner_memoInit_FP 1 1 4 2 (fun z j hj => ladner_memo_size z j (by simpa using hj))
  convert BinArith.polyTimeComputable_getW.comp hloop using 1
  funext z
  exact (ladner_memo_readout z).symm

/-- The padded SAT witness is in NP. [AB09, Theorem 3.3 and its proof]

**Proof sketch.** Parse the final false separator to recover the prefix and guess its
SAT certificate. Compute the index at the prefix length and check the prescribed unary suffix. -/
theorem SAT_H_mem_NP : SAT_H ∈ NP := by
  rw [SAT_H_eq]
  exact ladner_padded_NP ladnerH_polyTime SAT_exists_linear_verifier

/-- Polynomial-time computable, diverging padding cannot be NP-hard unless SAT belongs
to P. The hypothesis uses NP-hardness, rather than NP-completeness.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** A polynomial reduction into the padded language eventually maps an
instance to a satisfiable-prefix candidate at most the square root of its length.
Repeatedly shrink, with the finite small cases tabulated, to obtain a polynomial SAT decider. -/
theorem SAT_mem_P_of_padSAT_NPHard {h : ℕ → ℕ}
    (hp : PolyTimeComputable (fun x => Nat.bits (h x.length)))
    (hu : ∀ C, ∃ N, ∀ n ≥ N, C ≤ h n) (hH : NPHard (padSAT h)) : SAT ∈ P := by
  obtain ⟨f, hf, hred⟩ := ladner_reduction_from_hardness hH
  obtain ⟨B, K, hK, hshr⟩ := ladner_reduction_shrinks hf hu
  have hprog := fun x S hI => ladner_shrink_progress (B := B) hK hred
    (fun x p t a b c d => (hshr x p t a b c d).2) x S hI
  exact ladner_shrinking_transfer B K (ladner_shrinkStep_FP hp hf B K)
    (fun x j _ => ladner_shrink_orbit_size (fun x S hI => (hprog x S hI).1) x j)
    (ladner_shrink_final_readout hprog)

/-- If P differs from NP, the explicit padded SAT language is in NP, outside P and
not NP-complete. [AB09, Theorem 3.3]

**Proof sketch.** A P decider would bound the delayed index and make bounded padding a
polynomial reduction from SAT. NP-hardness would instead combine divergence of the
index with the shrinking reduction. Each case would put SAT in P and collapse P and NP. -/
theorem SAT_H_intermediate (h : P ≠ NP) :
    SAT_H ∈ NP ∧ SAT_H ∉ P ∧ ¬ NPComplete SAT_H := by
  have hout := ladner_outside_P h ladnerH_polyTime ladnerH_bounded_of_mem_P
  exact ⟨SAT_H_mem_NP, hout, ladner_not_complete h ladnerH_polyTime hout
    ladnerH_unbounded_of_not_mem_P (fun _ hp hu hH => SAT_mem_P_of_padSAT_NPHard hp hu hH)⟩

/-- If P differs from NP, an NP-intermediate language exists. [AB09, Theorem 3.3] -/
theorem ladner (h : P ≠ NP) : ∃ L ∈ NP, L ∉ P ∧ ¬ NPComplete L :=
  ⟨SAT_H, SAT_H_intermediate h⟩

end Complexity
