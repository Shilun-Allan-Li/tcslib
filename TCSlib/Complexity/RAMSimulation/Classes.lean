/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Simulation
import TCSlib.Complexity.ClassP.P
import TCSlib.Complexity.SpaceComplexity.SpaceClasses
import TCSlib.Complexity.ClassNP.PolyTime
import TCSlib.Programs.WordRAM.Output

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Complexity classes from word-RAM programs

The corollaries of stage 2 (`WordRAM.exists_simulation`, `WordRAM.exists_ndSimulation`) that put
a language into a class of `Complexity` from a word-RAM program that decides it: `DTIME` and `P`
(the time grade), `SPACE`, `LOGSPACE` and `SPACE (S · S)` (the space grades, the last in the
shape that Savitch's program needs), log-space transducers, and `NSPACE` and `NL` (the
nondeterministic space grades, with read-once coins).

## Main results

* `WordRAM.mem_DTIME_of_decides`, `WordRAM.mem_P_of_decides`, `WordRAM.mem_P_of_decides_logWord`.
* `WordRAM.polyTimeComputable_of_computes`, `WordRAM.polyTimeComputable_progOut`: polynomial-time
  functions from programs (function mode).
* `WordRAM.mem_SPACE_of_decides`, `WordRAM.mem_LOGSPACE_of_decides`,
  `WordRAM.computesInSpace_of_computes`, `WordRAM.mem_SPACE_mul_of_decides`.
* `WordRAM.mem_NSPACE_of_accepts`, `WordRAM.mem_NL_of_accepts`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Definitions 1.12, 1.13; Definitions 4.1, 4.5; Definition
  4.16 and Exercise 4.8; Theorem 4.14; §4.3.1, Definition 4.19.)
-/

namespace WordRAM

/-! ## Private bound arithmetic -/

/-- Absorb the start-up cost and the simulation constant into one multiplicative constant. -/
private lemma simulation_constant_bound (A u v : ℕ) :
    u + A * v ≤ (A + 1) * (u + v) := by
  nlinarith

/-- A bound for the space expression without its simulation constant bounds `simSpace`. -/
private lemma simulation_space_bound (A : ℕ) (SW W F s : ℕ → ℕ) (a n : ℕ)
    (hs : SW n + F n * (W n + 1) + W n + Complexity.logSpace n + 1 ≤ a * s n) :
    simSpace A SW n (W n) (F n) ≤ ((A + 1) * a) * s n := by
  rw [simSpace_eq]
  calc
    _ ≤ (A + 1) * (SW n + (F n * (W n + 1) + W n + Complexity.logSpace n + 1)) :=
      simulation_constant_bound _ _ _
    _ ≤ (A + 1) * (a * s n) :=
      Nat.mul_le_mul_left _ (by simpa only [Nat.add_assoc] using hs)
    _ = _ := by ring

/-- Constantly many logarithmic words and the start-up space occupy logarithmic space. -/
private lemma logarithmic_space_bound (a c F n : ℕ) :
    a * Complexity.logSpace n + F * (c * Complexity.logSpace n + 1) +
      c * Complexity.logSpace n + Complexity.logSpace n + 1 ≤
        (a + F * (c + 1) + c + 2) * Complexity.logSpace n := by
  have hlog : 1 ≤ Complexity.logSpace n := by rw [Complexity.logSpace_eq]; omega
  nlinarith [Nat.mul_le_mul_left F hlog]

/-- The time overhead is cubic in a common bound for steps and word size, times the input
length allowance.

**Proof sketch.** Bound `w + 1` by `(C + 1) b` and the per-step cost by
`(4 C² + 3 C + 1) b² z`. Multiply by the step bound, and use `b ≤ b³ z` for the
start-up cost. The power comparisons are `Nat.le_self_pow`; all factors are natural numbers. -/
private lemma polynomial_time_bound (C b z tw w : ℕ) (hb : 1 ≤ b) (hz : 1 ≤ z)
    (h : tw + w ≤ C * b) :
    tw + (C * b + 1) * (3 * C * b * (w + 1) + w ^ 2 + z) ≤
      (C + (C + 1) * (4 * C ^ 2 + 3 * C + 1)) * (b ^ 3 * z) := by
  have htw : tw ≤ C * b := by omega
  have hw : w ≤ C * b := by omega
  have hwone : w + 1 ≤ (C + 1) * b := by nlinarith
  have htone : C * b + 1 ≤ (C + 1) * b := by nlinarith
  have hb2 : b ^ 2 ≤ b ^ 2 * z := Nat.le_mul_of_pos_right _ (by omega)
  have hz2 : z ≤ b ^ 2 * z := Nat.le_mul_of_pos_left _ (by nlinarith)
  have hcost : 3 * C * b * (w + 1) + w ^ 2 + z ≤
      (4 * C ^ 2 + 3 * C + 1) * b ^ 2 * z := by
    calc
      _ ≤ (4 * C ^ 2 + 3 * C) * b ^ 2 + z := by
        nlinarith [Nat.mul_le_mul_left (3 * C * b) hwone, Nat.pow_le_pow_left hw 2]
      _ ≤ (4 * C ^ 2 + 3 * C) * (b ^ 2 * z) + b ^ 2 * z :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hb2) hz2
      _ = _ := by ring
  have hb3 : b ≤ b ^ 3 * z :=
    (Nat.le_self_pow (by decide) b).trans (Nat.le_mul_of_pos_right _ (by omega))
  calc
    _ ≤ C * (b ^ 3 * z) + ((C + 1) * b) *
        ((4 * C ^ 2 + 3 * C + 1) * b ^ 2 * z) :=
      Nat.add_le_add (htw.trans (Nat.mul_le_mul_left C hb3))
        (Nat.mul_le_mul htone hcost)
    _ = _ := by ring

/-! ## The time grade -/

/-- **Deciding in time.** If the program `P` decides `L` (verdict `[x ∈ L]`) with a computable
word size `W`, within `T |x|` steps and `F |x|` cells, then `L ∈ DTIME T'` for every `T'` that
dominates the stage-2 time bound up to a constant `a`. [AB09, Definition 1.12]

**Proof sketch.** `exists_simulation` in verdict mode gives a machine and a constant `A`.
Read its output with `outputOf_false` and its deadline with `simTime_eq`.
`simulation_constant_bound` and the assumed domination bound that deadline by
`(A + 1)·a·T' n`. `Turing.FinTM.ComputesInTime.mono` enlarges the deadline, and
`Complexity.mem_DTIME_iff`, `Turing.FinTM.decidesInTime_iff` and
`Turing.FinTM.computesFunInTime_iff` package the resulting decider. -/
theorem mem_DTIME_of_decides (P : XProgram) (L : Language Bool) {W TW SW T F : ℕ → ℕ}
    (hW : WordSizeComputable W TW SW)
    (hdec : ∀ x : List Bool, ∃ o : List Bool,
      HaltsWithin P x [] (W x.length) (T x.length)
        (Turing.MultiTapeTM.indicator (L : Set (List Bool)) x) o (F x.length))
    (T' : ℕ → ℕ) (a : ℕ)
    (hT : ∀ n, TW n + (T n + 1) * (F n * (W n + 1) + W n ^ 2 + n + 1) ≤ a * T' n) :
    L ∈ Complexity.DTIME T' := by
  obtain ⟨M, A, hM⟩ := exists_simulation P false hW
  apply Complexity.mem_DTIME_iff.mpr
  refine ⟨(A + 1) * a, M, (Turing.FinTM.decidesInTime_iff _ _ _).mpr ?_⟩
  apply (Turing.FinTM.computesFunInTime_iff _ _ _).mpr
  intro x
  obtain ⟨o, ho⟩ := hdec x
  have hm := (hM x (T x.length) (F x.length) _ o ho).1
  rw [outputOf_false] at hm
  apply hm.mono
  rw [simTime_eq, mul_assoc]
  calc
    _ ≤ (A + 1) * (TW x.length + (T x.length + 1) *
        (F x.length * (W x.length + 1) + W x.length ^ 2 + x.length + 1)) :=
      simulation_constant_bound _ _ _
    _ ≤ (A + 1) * (a * T' x.length) := Nat.mul_le_mul_left _ (hT x.length)
    _ = _ := by ring

/-- **The P grade.** If `P` decides `L` within polynomially many steps, with a word size of
polynomial value computable in polynomial time, then `L ∈ P`. No bound on the cells is needed:
a run of `t` steps touches at most `3 t` cells (`HaltsWithin.touches_le`). [AB09, Definition
1.13]

**Proof sketch.** `HaltsWithin.touches_le` and `HaltsWithin.mono` give uniform bounds
`C·(n + 1)^d` steps and `3·C·(n + 1)^d` cells. `polynomial_time_bound`, with
`b = (n + 1)^d` and `z = n + 1`, bounds the time expression without its simulation
constant by `a·(n + 1)^(3d + 1)`, where
`a = C + (C + 1)·(4C² + 3C + 1)`. Apply `mem_DTIME_of_decides`, then read its witness
through `Complexity.mem_DTIME_iff` and package it with `Complexity.mem_P_iff`. -/
theorem mem_P_of_decides (P : XProgram) (L : Language Bool) {W TW SW : ℕ → ℕ}
    (hW : WordSizeComputable W TW SW) (C d : ℕ)
    (hWpoly : ∀ n, TW n + W n ≤ C * (n + 1) ^ d)
    (hdec : ∀ x : List Bool, ∃ (t f : ℕ) (o : List Bool), t ≤ C * (x.length + 1) ^ d ∧
      HaltsWithin P x [] (W x.length) t
        (Turing.MultiTapeTM.indicator (L : Set (List Bool)) x) o f) :
    L ∈ Complexity.P := by
  let a := C + (C + 1) * (4 * C ^ 2 + 3 * C + 1)
  have hdt : L ∈ Complexity.DTIME (fun n => (n + 1) ^ (3 * d + 1)) := by
    refine mem_DTIME_of_decides P L (T := fun n => C * (n + 1) ^ d)
      (F := fun n => 3 * C * (n + 1) ^ d) hW ?_ _ a ?_
    · intro x
      obtain ⟨t, f, o, ht, ho⟩ := hdec x
      refine ⟨o, ho.touches_le.mono ht ?_⟩
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 3 ht
    · intro n
      have hb : 1 ≤ (n + 1) ^ d := Nat.one_le_pow d _ (by omega)
      have hp : ((n + 1) ^ d) ^ 3 * (n + 1) = (n + 1) ^ (3 * d + 1) := by
        rw [← pow_mul, Nat.mul_comm d 3, pow_succ]
      have h := polynomial_time_bound C ((n + 1) ^ d) (n + 1) (TW n) (W n)
        hb (by omega) (hWpoly n)
      rw [hp] at h
      simpa only [Nat.add_assoc] using h
  obtain ⟨A, M, hM⟩ := Complexity.mem_DTIME_iff.mp hdt
  exact Complexity.mem_P_iff.mpr ⟨A, 3 * d + 1, M, hM⟩

/-- **The P grade with logarithmic words**, the form that the curriculum and `NL ⊆ P` use: word
size `c · (⌊log₂ n⌋ + 1)` and polynomially many steps. [AB09, Definition 1.13]

**Proof sketch.** `wordSizeComputable_logSpace c` gives the word-size computation with
linear-time coefficient `a`. `Complexity.logSpace_le_succ` bounds its time plus its
value by `(a + c)·(n + 1)`. Enlarge both this bound and the program's step bound to
`(a + c + C)·(n + 1)^(d + 1)` using `Nat.le_self_pow` and `Nat.pow_le_pow_right`, then
apply `mem_P_of_decides`. -/
theorem mem_P_of_decides_logWord (P : XProgram) (L : Language Bool) (c C d : ℕ)
    (hdec : ∀ x : List Bool, ∃ (t f : ℕ) (o : List Bool), t ≤ C * (x.length + 1) ^ d ∧
      HaltsWithin P x [] (c * Complexity.logSpace x.length) t
        (Turing.MultiTapeTM.indicator (L : Set (List Bool)) x) o f) :
    L ∈ Complexity.P := by
  obtain ⟨a, hW⟩ := wordSizeComputable_logSpace c
  apply mem_P_of_decides P L hW (a + c + C) (d + 1)
  · intro n
    calc
      _ ≤ (a + c) * (n + 1) := by
        nlinarith [Nat.mul_le_mul_left c (Complexity.logSpace_le_succ n)]
      _ ≤ (a + c + C) * (n + 1) ^ (d + 1) :=
        Nat.mul_le_mul (by omega) (Nat.le_self_pow (by omega) _)
  · intro x
    obtain ⟨t, f, o, ht, ho⟩ := hdec x
    refine ⟨t, f, o, ht.trans ?_, ho⟩
    exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))

/-- **Polynomial-time functions from programs.** If `P`, with a word size of polynomial value
computable in polynomial time, emits `g x` on every input `x` within polynomially many steps, then
`g` is computable in polynomial time. [AB09, Definition 1.13, Exercise 1.9]

**Proof sketch.** As `mem_P_of_decides`, in function mode. `exists_simulation P true hW` gives a
machine and a constant `A`; `outputOf_true` reads its output as `g x`. `HaltsWithin.touches_le`
and `HaltsWithin.mono` give the bounds `C·(n + 1)^d` steps and `3·C·(n + 1)^d` cells, and
`polynomial_time_bound` bounds the simulation's deadline by `(A + 1)·a·(n + 1)^(3d + 1)`.
`simulation_constant_bound` absorbs the simulation constant into that coefficient.
`Turing.FinTM.ComputesInTime.mono` enlarges each run's deadline to it, and
`Turing.FinTM.computesFunInTime_iff` and `Complexity.polyTimeComputable_iff` package the machine. -/
theorem polyTimeComputable_of_computes (P : XProgram) (g : List Bool → List Bool)
    {W TW SW : ℕ → ℕ} (hW : WordSizeComputable W TW SW) (C d : ℕ)
    (hWpoly : ∀ n, TW n + W n ≤ C * (n + 1) ^ d)
    (hcomp : ∀ x : List Bool, ∃ (t f : ℕ) (v : Bool), t ≤ C * (x.length + 1) ^ d ∧
      HaltsWithin P x [] (W x.length) t v (g x) f) :
    Complexity.PolyTimeComputable g := by
  obtain ⟨M, A, hM⟩ := exists_simulation P true hW
  let a := C + (C + 1) * (4 * C ^ 2 + 3 * C + 1)
  apply (Complexity.polyTimeComputable_iff g).mpr
  refine ⟨M, (A + 1) * a, 3 * d + 1,
    (Turing.FinTM.computesFunInTime_iff _ _ _).mpr ?_⟩
  intro x
  obtain ⟨t, f, v, ht, ho⟩ := hcomp x
  have hrun : HaltsWithin P x [] (W x.length) (C * (x.length + 1) ^ d) v (g x)
      (3 * C * (x.length + 1) ^ d) :=
    ho.touches_le.mono ht (by
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 3 ht)
  have hm := (hM x _ _ v (g x) hrun).1
  rw [outputOf_true] at hm
  apply hm.mono
  rw [simTime_eq, Nat.mul_assoc]
  calc
    _ ≤ (A + 1) * (TW x.length + (C * (x.length + 1) ^ d + 1) *
        (3 * C * (x.length + 1) ^ d * (W x.length + 1) +
          W x.length ^ 2 + x.length + 1)) :=
      simulation_constant_bound _ _ _
    _ ≤ (A + 1) * (a * (x.length + 1) ^ (3 * d + 1)) := by
      apply Nat.mul_le_mul_left
      have h := polynomial_time_bound C ((x.length + 1) ^ d) (x.length + 1)
        (TW x.length) (W x.length) (Nat.one_le_pow _ _ (by omega)) (by omega) (hWpoly _)
      simpa only [a, ← pow_mul, Nat.mul_comm d 3, ← pow_succ, Nat.add_assoc] using h
    _ = _ := by ring

/-- **The output of a program halting in polynomial time is computable in polynomial time.** If
`P` halts on every input within polynomially many steps, with a word size of polynomial value
computable in polynomial time, then its output function `progOut P W` is computable in polynomial
time. A consumer then proves halting on every input, and correctness, `progOut P W x = g x`, only
where it needs it. [AB09, Definition 1.13, Exercise 1.9]

**Proof sketch.** `polyTimeComputable_of_computes` with `g := progOut P W`, where `progOut_eq`
identifies each halting run's output with `progOut P W x`. -/
theorem polyTimeComputable_progOut (P : XProgram) {W TW SW : ℕ → ℕ}
    (hW : WordSizeComputable W TW SW) (C d : ℕ) (hWpoly : ∀ n, TW n + W n ≤ C * (n + 1) ^ d)
    (hhalt : ∀ x : List Bool, ∃ (t f : ℕ) (v : Bool) (o : List Bool),
      t ≤ C * (x.length + 1) ^ d ∧ HaltsWithin P x [] (W x.length) t v o f) :
    Complexity.PolyTimeComputable (progOut P W) := by
  apply polyTimeComputable_of_computes P (progOut P W) hW C d hWpoly
  intro x
  obtain ⟨t, f, v, o, ht, ho⟩ := hhalt x
  refine ⟨t, f, v, ht, ?_⟩
  rw [progOut_eq ho]
  exact ho

/-! ## The space grades: L, log-space transducers, Savitch's shape -/

/-- **Deciding in space.** If `P` decides `L` with a computable word size `W`, touching at most
`F |x|` cells, in any number of steps, then `L ∈ SPACE s` for every `s` that dominates
`SW + F·(W + 1) + W + logSpace + 1` up to a constant `a`. [AB09, Definition 4.1]

**Proof sketch.** `exists_simulation` in verdict mode gives a halting computation on
each input. `outputOf_false` identifies its one-bit answer, and
`simulation_space_bound` bounds its visited work cells by `(A + 1)·a·s n`.
`Turing.FinTM.computesInSpace_iff`, `Turing.FinTM.decidesInSpace_iff` and
`Complexity.mem_SPACE_iff` package the same times and space bounds. -/
theorem mem_SPACE_of_decides (P : XProgram) (L : Language Bool) {W TW SW F : ℕ → ℕ}
    (hW : WordSizeComputable W TW SW)
    (hdec : ∀ x : List Bool, ∃ (t : ℕ) (o : List Bool),
      HaltsWithin P x [] (W x.length) t (Turing.MultiTapeTM.indicator (L : Set (List Bool)) x) o
        (F x.length))
    (s : ℕ → ℕ) (a : ℕ)
    (hs : ∀ n, SW n + F n * (W n + 1) + W n + Complexity.logSpace n + 1 ≤ a * s n) :
    L ∈ Complexity.SPACE s := by
  obtain ⟨M, A, hM⟩ := exists_simulation P false hW
  apply Complexity.mem_SPACE_iff.mpr
  refine ⟨(A + 1) * a, M, (Turing.FinTM.decidesInSpace_iff _ _ _).mpr ?_⟩
  apply (Turing.FinTM.computesInSpace_iff _ _ _).mpr
  intro x
  obtain ⟨t, o, ho⟩ := hdec x
  obtain ⟨hm, hspace⟩ := hM x t (F x.length) _ o ho
  rw [outputOf_false] at hm
  exact ⟨_, hm, hspace.trans (simulation_space_bound A SW W F s a _ (hs _))⟩

/-- **The logspace grade** (design §15a, §16b item 4): a program that decides `L` touching `O(1)`
cells, with word size `c · (⌊log₂ n⌋ + 1)`, puts `L` in `L`. The input is read in place (`rdIn`),
so it occupies no cell. [AB09, Definition 4.5]

**Proof sketch.** Obtain the word-size witness from `wordSizeComputable_logSpace c`.
`logarithmic_space_bound` bounds the space expression by
`(a + F₀·(c + 1) + c + 2)·logSpace n`, using `Complexity.logSpace_eq` for positivity.
Apply `mem_SPACE_of_decides` and identify the class with `Complexity.LOGSPACE_eq`. -/
theorem mem_LOGSPACE_of_decides (P : XProgram) (L : Language Bool) (c F₀ : ℕ)
    (hdec : ∀ x : List Bool, ∃ (t : ℕ) (o : List Bool),
      HaltsWithin P x [] (c * Complexity.logSpace x.length) t
        (Turing.MultiTapeTM.indicator (L : Set (List Bool)) x) o F₀) :
    L ∈ Complexity.LOGSPACE := by
  obtain ⟨a, hW⟩ := wordSizeComputable_logSpace c
  rw [Complexity.LOGSPACE_eq]
  exact mem_SPACE_of_decides P L hW hdec Complexity.logSpace
    (a + F₀ * (c + 1) + c + 2) (logarithmic_space_bound a c F₀)

/-- **Log-space transducers**: a program that, on every `x`, emits `g x` touching `O(1)` cells,
with word size `c · (⌊log₂ n⌋ + 1)`, gives a machine that computes `g` in logarithmic space; the
output tape is append-only and not counted. [AB09, §4.3: Definition 4.16, with the write-once
output tape of Exercise 4.8]

Deviation: `Turing.FinTM.ComputesInSpace` asks for no polynomial bound on `|g x|`, which
[AB09, Definition 4.16] includes in "implicitly logspace computable"; a halting program bounds it
by its running time.

**Proof sketch.** Use `wordSizeComputable_logSpace c` and `exists_simulation` in
function mode. `outputOf_true` identifies the emitted word with `g x`.
`logarithmic_space_bound` and `simulation_space_bound` bound the visited work cells by
`(A + 1)·(a + F₀·(c + 1) + c + 2)·logSpace n`; retain the simulation's halting time and
apply `Turing.FinTM.computesInSpace_iff`. -/
theorem computesInSpace_of_computes (P : XProgram) (g : List Bool → List Bool) (c F₀ : ℕ)
    (hcomp : ∀ x : List Bool, ∃ (t : ℕ) (v : Bool),
      HaltsWithin P x [] (c * Complexity.logSpace x.length) t v (g x) F₀) :
    ∃ (M : Turing.FinTM Bool) (a : ℕ),
      M.ComputesInSpace g fun n => a * Complexity.logSpace n := by
  obtain ⟨a, hW⟩ := wordSizeComputable_logSpace c
  obtain ⟨M, A, hM⟩ := exists_simulation P true hW
  refine ⟨M, (A + 1) * (a + F₀ * (c + 1) + c + 2),
    (Turing.FinTM.computesInSpace_iff _ _ _).mpr ?_⟩
  intro x
  obtain ⟨t, v, hv⟩ := hcomp x
  obtain ⟨hm, hspace⟩ := hM x t F₀ v (g x) hv
  rw [outputOf_true] at hm
  exact ⟨_, hm, hspace.trans (simulation_space_bound A (fun n => a * Complexity.logSpace n)
    (fun n => c * Complexity.logSpace n) (fun _ => F₀)
    Complexity.logSpace _ _ (logarithmic_space_bound a c F₀ _))⟩

/-- **Savitch's shape** (design §16b item 1): with a space-constructible `S`, word size `c · S(n)`
and at most `c · S(n)` cells touched (depth `O(S)` of frames of `O(1)` words, a configuration of
the simulated machine in one word), `L ∈ SPACE (S²)`. [AB09, Theorem 4.14, its space count]

**Proof sketch.** Obtain the word-size witness from
`wordSizeComputable_of_spaceConstructible hS c`, and apply `mem_SPACE_of_decides`.
`Complexity.spaceConstructible_iff` gives `logSpace ≤ S`; `Complexity.logSpace_eq`
therefore gives `1 ≤ S`, hence `S ≤ S²`. Bound the remaining linear terms by
`(a + 2c + 2)·S²` and retain the quadratic table term `c²·S²`, giving total coefficient
`a + c² + 2c + 2`. -/
theorem mem_SPACE_mul_of_decides (P : XProgram) (L : Language Bool) {S : ℕ → ℕ}
    (hS : Complexity.SpaceConstructible S) (c : ℕ)
    (hdec : ∀ x : List Bool, ∃ (t : ℕ) (o : List Bool),
      HaltsWithin P x [] (c * S x.length) t
        (Turing.MultiTapeTM.indicator (L : Set (List Bool)) x) o (c * S x.length)) :
    L ∈ Complexity.SPACE fun n => S n * S n := by
  obtain ⟨a, TW, hW⟩ := wordSizeComputable_of_spaceConstructible hS c
  apply mem_SPACE_of_decides P L (F := fun n => c * S n) hW hdec
    (fun n => S n * S n) (a + c ^ 2 + 2 * c + 2)
  intro n
  have hlog := ((Complexity.spaceConstructible_iff S).mp hS).1 n
  have hone : 1 ≤ S n := by
    have h := hlog
    rw [Complexity.logSpace_eq] at h
    omega
  have hsquare : S n ≤ S n * S n := by nlinarith
  have hlinear : a * S n + c * S n + c * S n + S n + 1 ≤
      (a + 2 * c + 2) * (S n * S n) := by
    nlinarith [Nat.mul_le_mul_left (a + 2 * c + 2) hsquare]
  nlinarith

/-! ## The nondeterministic space grades -/

/-- **Accepting in nondeterministic space.** If, on every `x`, every coin stream lets `P` halt
within one time `t` (depending on `x`) touching at most `F |x|` cells with a computable word
size `W`, and `x ∈ L` exactly when some stream makes `P` accept, then `L ∈ NSPACE s` for every
`s` that dominates the stage-2 space bound up to a constant `a`. [AB09, Definition 4.1,
nondeterministic clause]

**Proof sketch.** `exists_ndSimulation` supplies a common deadline on each input,
halting of every branch, its space bound, and the acceptance equivalence.
`simulation_space_bound` bounds every branch's space by `(A + 1)·a·s n`.
Compose the supplied acceptance equivalence with the hypothesis, and package the
deadline through `Turing.FinNDTM.decidesInSpace_iff` and `Complexity.mem_NSPACE_iff`. -/
theorem mem_NSPACE_of_accepts (P : XProgram) (L : Language Bool) {W TW SW F : ℕ → ℕ}
    (hW : WordSizeComputable W TW SW)
    (hrun : ∀ x : List Bool, ∃ t : ℕ,
      (∀ ρ : List Bool, ∃ (v : Bool) (o : List Bool),
        HaltsWithin P x ρ (W x.length) t v o (F x.length)) ∧
      (x ∈ L ↔ ∃ (ρ o : List Bool), HaltsWithin P x ρ (W x.length) t true o (F x.length)))
    (s : ℕ → ℕ) (a : ℕ)
    (hs : ∀ n, SW n + F n * (W n + 1) + W n + Complexity.logSpace n + 1 ≤ a * s n) :
    L ∈ Complexity.NSPACE s := by
  obtain ⟨N, A, hN⟩ := exists_ndSimulation P hW
  apply Complexity.mem_NSPACE_iff.mpr
  refine ⟨(A + 1) * a, N, (Turing.FinNDTM.decidesInSpace_iff _ _ _).mpr ?_⟩
  intro x
  obtain ⟨t, hhalt, hacc⟩ := hrun x
  obtain ⟨hn, hspace, haccept⟩ := hN x t (F x.length) hhalt
  refine ⟨_, hn, fun w hw => ?_, hacc.trans haccept.symm⟩
  exact (hspace w hw).trans (simulation_space_bound A SW W F s a _ (hs _))

/-- **The NL grade** (design §16b item 4, C2): a program with read-once coins that, on every `x`,
halts under every coin stream within one time touching `O(1)` cells, with word size
`c · (⌊log₂ n⌋ + 1)`, and accepts under some stream exactly when `x ∈ L`, puts `L` in `NL`.
[AB09, Definition 4.5 (NL); §4.3.1, Definition 4.19: read-once certificates]

**Proof sketch.** Obtain the word-size witness from `wordSizeComputable_logSpace c`.
`logarithmic_space_bound` supplies the same logarithmic space estimate as in
`mem_LOGSPACE_of_decides`. Apply `mem_NSPACE_of_accepts` with the unchanged uniform
halting and acceptance hypotheses, and identify the class with `Complexity.NL_eq`. -/
theorem mem_NL_of_accepts (P : XProgram) (L : Language Bool) (c F₀ : ℕ)
    (hrun : ∀ x : List Bool, ∃ t : ℕ,
      (∀ ρ : List Bool, ∃ (v : Bool) (o : List Bool),
        HaltsWithin P x ρ (c * Complexity.logSpace x.length) t v o F₀) ∧
      (x ∈ L ↔ ∃ (ρ o : List Bool),
        HaltsWithin P x ρ (c * Complexity.logSpace x.length) t true o F₀)) :
    L ∈ Complexity.NL := by
  obtain ⟨a, hW⟩ := wordSizeComputable_logSpace c
  rw [Complexity.NL_eq]
  exact mem_NSPACE_of_accepts P L hW hrun Complexity.logSpace
    (a + F₀ * (c + 1) + c + 2) (logarithmic_space_bound a c F₀)

end WordRAM
