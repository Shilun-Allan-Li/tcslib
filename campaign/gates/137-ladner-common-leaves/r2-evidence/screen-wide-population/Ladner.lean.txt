/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
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

/-- The binary digits of the delayed index at an input's length are polynomial-time
computable. [AB09, Theorem 3.3 and its proof]

**Proof sketch.** Maintain previously computed index values, simulate only the short
inputs through the uniformly timed acceptance simulator, and test SAT on short words.
Polynomially bounded iteration supplies the memo-table driver; the short-SAT search,
poly-bounded simulator invocation and state-size ledger are separate route obligations. -/
theorem ladnerH_polyTime :
    PolyTimeComputable (fun x => Nat.bits (ladnerH x.length)) :=
  sorry

/-- The padded SAT witness is in NP. [AB09, Theorem 3.3 and its proof]

**Proof sketch.** Guess the satisfiable prefix and its SAT certificate. Compute the
index at that prefix length and check the separator and exactly prescribed unary suffix. -/
theorem SAT_H_mem_NP : SAT_H ∈ NP :=
  sorry

/-- The empty word is outside every padded language because a separator contributes
one symbol. [AB09, Theorem 3.3 and its proof] -/
private theorem ladner_pad_nil (h : ℕ → ℕ) : ([] : List Bool) ∉ padSAT h := by
  intro hx
  obtain ⟨ψ, _, he⟩ := mem_padSAT_iff.mp hx
  have hlen := congrArg List.length he
  simp only [List.length_nil, List.length_append, List.length_cons,
    List.length_replicate] at hlen
  omega

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
  have prepend (u : List Bool) (j : ℕ) (hj : 0 < j) :
      ∃ i, j ≤ i ∧ i.bits = u ++ j.bits := by
    induction u with
    | nil => exact ⟨j, le_rfl, rfl⟩
    | cons b u ih =>
      obtain ⟨i, hi, hbits⟩ := ih
      refine ⟨Nat.bit b i, ?_, ?_⟩
      · rw [Nat.bit_val]
        omega
      · rw [Nat.bits_append_bit i b (fun hz => by omega), hbits, List.cons_append]
  obtain ⟨j, hj, hbits⟩ := ones B
  obtain ⟨i, hi, hi_bits⟩ := prepend (expCode.encode M) j (by omega)
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

/-- Polynomial-time computable, diverging padding cannot be NP-hard unless SAT belongs
to P. The hypothesis uses NP-hardness, rather than NP-completeness.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** A polynomial reduction into the padded language eventually maps an
instance to a satisfiable-prefix candidate at most the square root of its length.
Repeatedly shrink, with the finite small cases tabulated, to obtain a polynomial SAT decider. -/
theorem SAT_mem_P_of_padSAT_NPHard {h : ℕ → ℕ}
    (hp : PolyTimeComputable (fun x => Nat.bits (h x.length)))
    (hu : ∀ C, ∃ N, ∀ n ≥ N, C ≤ h n) (hH : NPHard (padSAT h)) : SAT ∈ P :=
  sorry

/-- If P differs from NP, the explicit padded SAT language is in NP, outside P and
not NP-complete. [AB09, Theorem 3.3]

**Proof sketch.** A P decider would bound the delayed index and make bounded padding a
polynomial reduction from SAT. NP-hardness would instead combine divergence of the
index with the shrinking reduction. Each case would put SAT in P and collapse P and NP. -/
theorem SAT_H_intermediate (h : P ≠ NP) :
    SAT_H ∈ NP ∧ SAT_H ∉ P ∧ ¬ NPComplete SAT_H :=
  sorry

/-- If P differs from NP, an NP-intermediate language exists. [AB09, Theorem 3.3] -/
theorem ladner (h : P ≠ NP) : ∃ L ∈ NP, L ∉ P ∧ ¬ NPComplete L :=
  ⟨SAT_H, SAT_H_intermediate h⟩

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

/-- The mathematical padding parser has a polynomial-time serialization.

**Proof sketch.** Reverse the input, skip its true suffix and separator with the existing
unary-rest reader, and reverse the remainder. Subtract the prefix length and one from
the input length to get the suffix length. The public false-bit test distinguishes a
missing separator from an empty prefix. [AB09, Theorem 3.3 and its proof] -/
private theorem ladner_parse_FP : PolyTimeComputable ladner_parseWord := by
  have hl : PolyTimeComputable (fun y : List Bool => Nat.bits y.length) :=
    polyTimeComputable_of_linear FinTM.computesFunInTime_lengthBits
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

/-- The padding syntax test is polynomial-time when its exponent function is.

**Proof sketch.** Parse the word and compute the prefix length and exponent in binary.
Use the saturated power with cap parameter equal to the suffix length. Its result equals
the suffix length exactly when the full power does; this avoids allocating an enormous
power. [AB09, Theorem 3.3 and its proof] -/
private theorem ladner_syntax_FP {h : ℕ → ℕ}
    (hp : PolyTimeComputable (fun x : List Bool => Nat.bits (h x.length))) :
    PolyTimeComputable (fun y => [ladner_padSyntax h y]) := by
  have hl : PolyTimeComputable (fun y : List Bool => Nat.bits y.length) :=
    polyTimeComputable_of_linear FinTM.computesFunInTime_lengthBits
  have hpre := BinArith.polyTimeComputable_slot2.comp ladner_parse_FP
  have ht := BinArith.polyTimeComputable_slot3.comp ladner_parse_FP
  have hpow := BinArith.polyTimeComputable_powCap.comp
    ((hl.comp hpre).pairEncode ((hp.comp hpre).pairEncode ht))
  have heq := BinArith.polyTimeComputable_beq.comp (ht.pairEncode hpow)
  have hout := polyTimeComputable_ite (polyTimeComputable_isNil.comp ladner_parse_FP)
    (polyTimeComputable_const [false]) heq
  convert hout using 1
  funext y
  cases hy : ladner_parse y with
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
    simp only [ladner_padSyntax, ladner_parseWord, hy, Function.comp_apply,
      hne, decide_false, Bool.false_eq_true, if_false, pairFstD_pairEncode,
      pairSndD_pairEncode, BinArith.powCap_pairEncode, BinArith.beq_pairEncode]
    have heq' : (t = min (p.length ^ h p.length) (t + 1)) ↔
        t = p.length ^ h p.length := by omega
    simp only [heq']

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


end Complexity
