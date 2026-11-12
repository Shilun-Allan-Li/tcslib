/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Simulation
import TCSlib.Complexity.ClassP.P
import TCSlib.Complexity.SpaceComplexity.SpaceClasses

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

## Main results (statements gated 2026-10-14, `audits/stage2-statements-findings.md`; proofs pending)

* `WordRAM.mem_DTIME_of_decides`, `WordRAM.mem_P_of_decides`, `WordRAM.mem_P_of_decides_logWord`.
* `WordRAM.mem_SPACE_of_decides`, `WordRAM.mem_LOGSPACE_of_decides`,
  `WordRAM.computesInSpace_of_computes`, `WordRAM.mem_SPACE_mul_of_decides`.
* `WordRAM.mem_NSPACE_of_accepts`, `WordRAM.mem_NL_of_accepts`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Definitions 1.12, 1.13; Definitions 4.1, 4.5; Definition
  4.16 and Exercise 4.8; Theorem 4.14; §4.3.1, Definition 4.19.)
-/

namespace WordRAM

/-! ## The time grade -/

/-- **Deciding in time.** If the program `P` decides `L` (verdict `[x ∈ L]`) with a computable
word size `W`, within `T |x|` steps and `F |x|` cells, then `L ∈ DTIME T'` for every `T'` that
dominates the stage-2 time bound up to a constant `a`. [AB09, Definition 1.12]

**Proof sketch.** `exists_simulation` in verdict mode gives a machine `M` and a constant `A`;
`simTime A TW n (W n) (T n) (F n) ≤ (A + 1)·(TW n + (T n + 1)·(…)) ≤ (A + 1)·a·T' n`, and
`Turing.FinTM.ComputesInTime.mono` moves each input's halting time there. -/
theorem mem_DTIME_of_decides (P : XProgram) (L : Language Bool) {W TW SW T F : ℕ → ℕ}
    (hW : WordSizeComputable W TW SW)
    (hdec : ∀ x : List Bool, ∃ o : List Bool,
      HaltsWithin P x [] (W x.length) (T x.length)
        (Turing.MultiTapeTM.indicator (L : Set (List Bool)) x) o (F x.length))
    (T' : ℕ → ℕ) (a : ℕ)
    (hT : ∀ n, TW n + (T n + 1) * (F n * (W n + 1) + W n ^ 2 + n + 1) ≤ a * T' n) :
    L ∈ Complexity.DTIME T' := by
  sorry

/-- **The P grade.** If `P` decides `L` within polynomially many steps, with a word size of
polynomial value computable in polynomial time, then `L ∈ P`. No bound on the cells is needed:
a run of `t` steps touches at most `3 t` cells (`HaltsWithin.touches_le`). [AB09, Definition
1.13]

**Proof sketch.** `HaltsWithin.touches_le` and `HaltsWithin.mono` turn each input's run into one
within `C·(n + 1)^d` steps and `3·C·(n + 1)^d` cells; `mem_DTIME_of_decides` with
`T' n = (n + 1)^(3d + 1)` (the bound `(t + 1)·(f·(W + 1) + W² + n + 1)` is a polynomial of
polynomials), then `Complexity.mem_P_iff`. -/
theorem mem_P_of_decides (P : XProgram) (L : Language Bool) {W TW SW : ℕ → ℕ}
    (hW : WordSizeComputable W TW SW) (C d : ℕ)
    (hWpoly : ∀ n, TW n + W n ≤ C * (n + 1) ^ d)
    (hdec : ∀ x : List Bool, ∃ (t f : ℕ) (o : List Bool), t ≤ C * (x.length + 1) ^ d ∧
      HaltsWithin P x [] (W x.length) t
        (Turing.MultiTapeTM.indicator (L : Set (List Bool)) x) o f) :
    L ∈ Complexity.P := by
  sorry

/-- **The P grade with logarithmic words**, the form that the curriculum and `NL ⊆ P` use: word
size `c · (⌊log₂ n⌋ + 1)` and polynomially many steps. [AB09, Definition 1.13]

**Proof sketch.** `mem_P_of_decides` with `wordSizeComputable_logSpace c`; then
`TW n + W n = a·(n + 1) + c·logSpace n ≤ (a + c)·(n + 1)`, since `logSpace n ≤ n + 1`. -/
theorem mem_P_of_decides_logWord (P : XProgram) (L : Language Bool) (c C d : ℕ)
    (hdec : ∀ x : List Bool, ∃ (t f : ℕ) (o : List Bool), t ≤ C * (x.length + 1) ^ d ∧
      HaltsWithin P x [] (c * Complexity.logSpace x.length) t
        (Turing.MultiTapeTM.indicator (L : Set (List Bool)) x) o f) :
    L ∈ Complexity.P := by
  sorry

/-! ## The space grades: L, log-space transducers, Savitch's shape -/

/-- **Deciding in space.** If `P` decides `L` with a computable word size `W`, touching at most
`F |x|` cells, in any number of steps, then `L ∈ SPACE s` for every `s` that dominates
`SW + F·(W + 1) + W + logSpace + 1` up to a constant `a`. [AB09, Definition 4.1]

**Proof sketch.** `exists_simulation` in verdict mode gives, on each input, a halting time and
the space bound `simSpace A SW n (W n) (F n) ≤ (A + 1)·(…) ≤ (A + 1)·a·s n`, which is
`Turing.FinTM.DecidesInSpace` at the constant `(A + 1)·a`. -/
theorem mem_SPACE_of_decides (P : XProgram) (L : Language Bool) {W TW SW F : ℕ → ℕ}
    (hW : WordSizeComputable W TW SW)
    (hdec : ∀ x : List Bool, ∃ (t : ℕ) (o : List Bool),
      HaltsWithin P x [] (W x.length) t (Turing.MultiTapeTM.indicator (L : Set (List Bool)) x) o
        (F x.length))
    (s : ℕ → ℕ) (a : ℕ)
    (hs : ∀ n, SW n + F n * (W n + 1) + W n + Complexity.logSpace n + 1 ≤ a * s n) :
    L ∈ Complexity.SPACE s := by
  sorry

/-- **The logspace grade** (design §15a, §16b item 4): a program that decides `L` touching `O(1)`
cells, with word size `c · (⌊log₂ n⌋ + 1)`, puts `L` in `L`. The input is read in place (`rdIn`),
so it occupies no cell. [AB09, Definition 4.5]

**Proof sketch.** `mem_SPACE_of_decides` with `wordSizeComputable_logSpace c`, `F = F₀` and
`s = logSpace`: `a·logSpace n + F₀·(c·logSpace n + 1) + c·logSpace n + logSpace n + 1` is at
most `(a + F₀·(c + 1) + c + 2)·logSpace n`, since `logSpace n ≥ 1`. -/
theorem mem_LOGSPACE_of_decides (P : XProgram) (L : Language Bool) (c F₀ : ℕ)
    (hdec : ∀ x : List Bool, ∃ (t : ℕ) (o : List Bool),
      HaltsWithin P x [] (c * Complexity.logSpace x.length) t
        (Turing.MultiTapeTM.indicator (L : Set (List Bool)) x) o F₀) :
    L ∈ Complexity.LOGSPACE := by
  sorry

/-- **Log-space transducers**: a program that, on every `x`, emits `g x` touching `O(1)` cells,
with word size `c · (⌊log₂ n⌋ + 1)`, gives a machine that computes `g` in logarithmic space; the
output tape is append-only and not counted. [AB09, §4.3: Definition 4.16, with the write-once
output tape of Exercise 4.8]

Deviation: `Turing.FinTM.ComputesInSpace` asks for no polynomial bound on `|g x|`, which
[AB09, Definition 4.16] includes in "implicitly logspace computable"; a halting program bounds it
by its running time.

**Proof sketch.** `exists_simulation` in function mode, with the bounds of
`mem_LOGSPACE_of_decides`. -/
theorem computesInSpace_of_computes (P : XProgram) (g : List Bool → List Bool) (c F₀ : ℕ)
    (hcomp : ∀ x : List Bool, ∃ (t : ℕ) (v : Bool),
      HaltsWithin P x [] (c * Complexity.logSpace x.length) t v (g x) F₀) :
    ∃ (M : Turing.FinTM Bool) (a : ℕ),
      M.ComputesInSpace g fun n => a * Complexity.logSpace n := by
  sorry

/-- **Savitch's shape** (design §16b item 1): with a space-constructible `S`, word size `c · S(n)`
and at most `c · S(n)` cells touched (depth `O(S)` of frames of `O(1)` words, a configuration of
the simulated machine in one word), `L ∈ SPACE (S²)`. [AB09, Theorem 4.14, its space count]

**Proof sketch.** `mem_SPACE_of_decides` with `wordSizeComputable_of_spaceConstructible hS c`:
`a·S + c·S·(c·S + 1) + c·S + logSpace + 1 ≤ (a + c² + 2c + 2)·S²`, since `logSpace ≤ S` (a
conjunct of `Complexity.SpaceConstructible`) and so `S ≥ 1`. -/
theorem mem_SPACE_mul_of_decides (P : XProgram) (L : Language Bool) {S : ℕ → ℕ}
    (hS : Complexity.SpaceConstructible S) (c : ℕ)
    (hdec : ∀ x : List Bool, ∃ (t : ℕ) (o : List Bool),
      HaltsWithin P x [] (c * S x.length) t
        (Turing.MultiTapeTM.indicator (L : Set (List Bool)) x) o (c * S x.length)) :
    L ∈ Complexity.SPACE fun n => S n * S n := by
  sorry

/-! ## The nondeterministic space grades -/

/-- **Accepting in nondeterministic space.** If, on every `x`, every coin stream lets `P` halt
within one time `t` (depending on `x`) touching at most `F |x|` cells with a computable word
size `W`, and `x ∈ L` exactly when some stream makes `P` accept, then `L ∈ NSPACE s` for every
`s` that dominates the stage-2 space bound up to a constant `a`. [AB09, Definition 4.1,
nondeterministic clause]

**Proof sketch.** `exists_ndSimulation`; the per-input budget of `Turing.FinNDTM.DecidesInSpace`
is `simTime A TW n (W n) t (F n)`, all branches of that length halt and stay within
`simSpace … ≤ (A + 1)·a·s n`, and acceptance is the stated equivalence. -/
theorem mem_NSPACE_of_accepts (P : XProgram) (L : Language Bool) {W TW SW F : ℕ → ℕ}
    (hW : WordSizeComputable W TW SW)
    (hrun : ∀ x : List Bool, ∃ t : ℕ,
      (∀ ρ : List Bool, ∃ (v : Bool) (o : List Bool),
        HaltsWithin P x ρ (W x.length) t v o (F x.length)) ∧
      (x ∈ L ↔ ∃ (ρ o : List Bool), HaltsWithin P x ρ (W x.length) t true o (F x.length)))
    (s : ℕ → ℕ) (a : ℕ)
    (hs : ∀ n, SW n + F n * (W n + 1) + W n + Complexity.logSpace n + 1 ≤ a * s n) :
    L ∈ Complexity.NSPACE s := by
  sorry

/-- **The NL grade** (design §16b item 4, C2): a program with read-once coins that, on every `x`,
halts under every coin stream within one time touching `O(1)` cells, with word size
`c · (⌊log₂ n⌋ + 1)`, and accepts under some stream exactly when `x ∈ L`, puts `L` in `NL`.
[AB09, Definition 4.5 (NL); §4.3.1, Definition 4.19: read-once certificates]

**Proof sketch.** `mem_NSPACE_of_accepts` with `wordSizeComputable_logSpace c`, `F = F₀` and
`s = logSpace`, the arithmetic of `mem_LOGSPACE_of_decides`. -/
theorem mem_NL_of_accepts (P : XProgram) (L : Language Bool) (c F₀ : ℕ)
    (hrun : ∀ x : List Bool, ∃ t : ℕ,
      (∀ ρ : List Bool, ∃ (v : Bool) (o : List Bool),
        HaltsWithin P x ρ (c * Complexity.logSpace x.length) t v o F₀) ∧
      (x ∈ L ↔ ∃ (ρ o : List Bool),
        HaltsWithin P x ρ (c * Complexity.logSpace x.length) t true o F₀)) :
    L ∈ Complexity.NL := by
  sorry

end WordRAM
