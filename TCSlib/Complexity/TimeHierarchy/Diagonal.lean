/-
Copyright (c) 2026 Hydroxyi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import TCSlib.Complexity.ClassP.DTIME
import TCSlib.Complexity.ClassP.TimeConstructible
import TCSlib.Complexity.TimeHierarchy.ClockLoop
import TCSlib.Complexity.TimeHierarchy.CodePrefix
import TCSlib.Complexity.TuringMachine.Composition
import TCSlib.Complexity.TuringMachine.MathlibBridge
import TCSlib.Complexity.TuringMachine.Universal

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Time Hierarchy Theorem

[AB09, Theorem 3.1]: if `f, g` are time-constructible functions with
`f(n) log f(n) = o(g(n))`, then `DTIME(f) ⊊ DTIME(g)`. This file proves the theorem
in the form supported by this development's universal machine:

  if `g` is time constructible and `(f(n) + n + 1)² = o(g(n))`, then
  `DTIME(f) ⊊ DTIME(g + 1)`.

## The diagonal language

Fix the effective representation scheme `code` and the universal machine `univTM`
(`Turing.universal`). The simulator `diagSim` composes the prefix-duplication machine
`preTM` with `univTM`; on an input `x = pairEncode α w` it runs the machine coded by
`α` on `x` itself. The diagonal language is

  `diagLang g = {x | diagSim does not halt on x with output [true] within g(|x|) steps}`,

decided within `O(g(n))` by the clocked runner `clockTM K diagSim`, where `K` is the
time-constructibility witness of `g` (`diagLang_mem_DTIME`). If a machine `M`
decided `diagLang g` within `c·T(n)`, take a code `α` of its one-work-tape normal form
and the inputs `x = pairEncode α 1^m`: the simulation of `M` on `x` finishes within
`A·(T(n) + n + 1)²` steps for a constant `A` depending only on `M`, which is at most
`g(n)` for suitable `n` — and then `diagSim`'s verdict on `x` contradicts `M`'s
(`diagLang_not_mem_DTIME`).

## Divergences from [AB09, Theorem 3.1]

* **Overhead `f²` instead of `f log f`.** The book's universal machine has
  `O(T log T)` overhead ([AB09, Theorem 1.9 / §1.7]); this development's universal
  machine is linear on coded machines but coded machines are one-work-tape binary
  machines, and an arbitrary binary machine is normal-formed with quadratic slowdown
  (`Turing.FinTM.one_work_tape_binary`, [AB09, Claims 1.5–1.6]). The hypothesis is
  therefore `(f(n) + n + 1)² = o(g(n))`, written out as
  `∀ A, ∃ N, ∀ n ≥ N, A · (f n + n + 1)² ≤ g n`. The `+ n + 1` absorbs the linear
  cost of reading the input and the `+ 1` normalization of `DTIME` bounds. The
  sharper `f log f` form is out of reach until the `O(T log T)` simulation (phase-5
  stretch goal of the Chapter 1 plan) exists.
  Because of the `+ n + 1` term the hypothesis forces `g(n) = ω(n²)`, so finer
  separations below the quadratic threshold — e.g. the book's illustration
  `DTIME(n) ⊊ DTIME(n^1.5)` — are **not** derivable from this theorem; the best
  linear-time separation it yields is roughly `DTIME(n) ⊊ DTIME(n^(2+ε))`.
* **No time-constructibility hypothesis on `f`** — none is needed (the book assumes
  it only for symmetry).
* **`DTIME(g + 1)` instead of `DTIME(g)`.** `TimeConstructible g` permits `g 0 = 0`,
  and `DTIME` of a bound vanishing anywhere is empty
  (`Complexity.DTIME_eq_empty_of_exists_zero`); the `+ 1` repairs this degenerate
  case only (for `n ≥ 1`, `g n ≥ n ≥ 1`).
* **Padding the input, not the code.** The book uses that every machine has
  infinitely many codes. Here the universal machine's constant depends on the code
  string (`Turing.universal` — the canonizer time of the representation scheme is an
  opaque bound), so the diagonal argument fixes one code `α` and pads the *input*
  `pairEncode α 1^m`; the code is recovered from the input by `preTM`.
* **The clock counts the diagonal machine's own simulation steps**, via the clocked
  runner `Complexity.TimeHierarchy.clockTM`.
* The separation is proved in the stronger *infinitely-often* form:
  `diagLang_not_mem_DTIME` needs `A · (T n + n + 1)² ≤ g n` only for infinitely many
  `n`, for each `A`.

## Main definitions

* `Complexity.TimeHierarchy.code`, `univTM`, `diagSim` — the fixed scheme, universal
  machine, and simulator.
* `Complexity.TimeHierarchy.diagLang` — the diagonal language.

## Main results

* `Complexity.TimeHierarchy.diagLang_mem_DTIME` — `diagLang g ∈ DTIME (g + 1)`.
* `Complexity.TimeHierarchy.diagLang_not_mem_DTIME` — `diagLang g ∉ DTIME T` whenever
  `A · (T n + n + 1)² ≤ g n` infinitely often for every `A`.
* `Complexity.time_hierarchy` — [AB09, Theorem 3.1], in the form above.
* `Complexity.time_hierarchy_of_pos` — the same with `DTIME g` when `g` never vanishes.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.1, Theorem 3.1, pp. 69–70; §1.4.)
-/

namespace Complexity.TimeHierarchy

open Turing Turing.FinTM

/-- The fixed effective representation scheme of the hierarchy construction (any
scheme works; `Turing.exists_effectiveMachineCode` provides one). -/
noncomputable def code : EffectiveMachineCode := Classical.choice exists_effectiveMachineCode

/-- The universal machine for `code`, from `Turing.universal`. -/
noncomputable def univTM : FinTM Bool := Classical.choose (universal code)

/-- The universal machine's specification (`Turing.universal`). -/
lemma univTM_spec : ∀ α : List Bool, ∃ C : ℕ, ∀ x : List Bool,
    (∀ (output : List Bool) (t : ℕ),
      (code.decode α).toFinTM.ComputesInTime x output t →
      univTM.ComputesInTime (pairEncode α x) output (C * (t + 1))) ∧
    (∀ output : List Bool,
      (∃ t, univTM.ComputesInTime (pairEncode α x) output t) →
      ∃ t, (code.decode α).toFinTM.ComputesInTime x output t) :=
  Classical.choose_spec (universal code)

/-- The diagonal simulator: duplicate the code prefix (`preTM`), then run the
universal machine. On `x = pairEncode α w` it runs the machine coded by `α` on `x`. -/
noncomputable def diagSim : FinTM Bool := bufferedCompTM preTM univTM

/-- **The diagonal language** of the hierarchy theorem [AB09, Theorem 3.1, proof]:
the strings `x` on which the diagonal simulator does **not** halt with output `[true]`
within `g(|x|)` steps. -/
def diagLang (g : ℕ → ℕ) : Language Bool :=
  {x | ¬diagSim.ComputesInTime x [true] (g x.length)}

/-- **The diagonal language is decidable in time `O(g)`** [AB09, Theorem 3.1, proof:
"`D` runs in time `O(g(n))`"]: for time-constructible `g`,
`diagLang g ∈ DTIME (g + 1)`.

**Proof sketch.** Run the clocked runner `clockTM K diagSim`, with `K` the
time-constructibility witness of `g`: its budget word is `bits (g n)` of value `g n`,
so by `clockTM_spec` it outputs `[x ∈ diagLang g]` within
`c_K (g n + 1) + 4|bits (g n)| + n + 4 g n + 6 ≤ (c_K + 15)(g n + 1)` steps, using
`|bits m| ≤ m` and `n ≤ g n`. -/
theorem diagLang_mem_DTIME {g : ℕ → ℕ} (hg : TimeConstructible g) :
    diagLang g ∈ DTIME (fun n => g n + 1) := by
  classical
  obtain ⟨hgn, cK, _, K, hK⟩ := hg
  refine ⟨cK + 15, clockTM K diagSim, fun x => ?_⟩
  have h := clockTM_spec K diagSim x (g x.length).bits _ (hK x)
  rw [ctrVal_bits] at h
  have hout : [!(decide (diagSim.ComputesInTime x [true] (g x.length)))] =
      [MultiTapeTM.indicator (diagLang g : Set (List Bool)) x] := by
    by_cases hx : diagSim.ComputesInTime x [true] (g x.length)
    · have : x ∉ (diagLang g : Set (List Bool)) := fun h' => h' hx
      simp [MultiTapeTM.indicator, hx, this]
    · have : x ∈ (diagLang g : Set (List Bool)) := hx
      simp [MultiTapeTM.indicator, hx, this]
  rw [hout] at h
  apply h.mono
  have h1 := length_bits_le_self (g x.length)
  have h2 := hgn x.length
  nlinarith

/-- The polynomial bookkeeping of the diagonal argument: with `X = T + n + 1`, the
simulation cost `5n + 7 + C · (c₁ (c₀ T + 1)² + 1)` is at most
`(8 + C (c₁ (c₀ + 1)² + 1)) · X²`. -/
lemma diag_cost_le (n T c₀ c₁ C : ℕ) :
    5 * n + 7 + C * (c₁ * (c₀ * T + 1) ^ 2 + 1) ≤
      (8 + C * (c₁ * (c₀ + 1) ^ 2 + 1)) * (T + n + 1) ^ 2 := by
  have hX : 1 ≤ T + n + 1 := by omega
  have hX2 : T + n + 1 ≤ (T + n + 1) ^ 2 := by nlinarith
  have hlin : c₀ * T + 1 ≤ (c₀ + 1) * (T + n + 1) := by nlinarith
  have hsq : (c₀ * T + 1) ^ 2 ≤ (c₀ + 1) ^ 2 * (T + n + 1) ^ 2 := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left hlin 2
  have hone : 1 ≤ (T + n + 1) ^ 2 := by nlinarith
  have hinner : c₁ * (c₀ * T + 1) ^ 2 + 1 ≤ (c₁ * (c₀ + 1) ^ 2 + 1) * (T + n + 1) ^ 2 := by
    have := Nat.mul_le_mul_left c₁ hsq
    nlinarith
  have hC := Nat.mul_le_mul_left C hinner
  nlinarith

/-- **The diagonal language is not in `DTIME T`** [AB09, Theorem 3.1, proof: "`D`
differs from every machine running in time `f`"], provided `g` dominates
`A · (T n + n + 1)²` for infinitely many `n`, for every constant `A`.

**Proof sketch.** Suppose `M` decides `diagLang g` within `c₀ T(n)`. Normal-form `M`
to a one-work-tape binary machine (time `c₁ (c₀ T + 1)²`,
`Turing.FinTM.one_work_tape_binary`), relabel it to a coded machine `N`
(`Turing.exists_codeTM`), and let `α = ⌞N⌟`; let `C` be the universal machine's
constant for `α`. With `A = 8 + C (c₁ (c₀ + 1)² + 1)` pick `n ≥ 2|α| + 2` with
`A (T n + n + 1)² ≤ g n` and put `x = pairEncode α 1^(n - 2|α| - 2)`, so `|x| = n`.
Then `preTM` maps `x` to `pairEncode α x` (`scanPre_pairEncode_append`), on which
`univTM` simulates `N` on `x`, producing `M`'s verdict `[χ(x)]`; altogether `diagSim`
halts on `x` with `[χ(x)]` within `5n + 7 + C(c₁(c₀T + 1)² + 1) ≤ g n` steps
(`bufferedCompTM_computesInTime`, `diag_cost_le`). If `χ(x) = true` then
`x ∈ diagLang g`, i.e. `diagSim` does *not* output `[true]` within `g n` — a
contradiction; if `χ(x) = false` then `x ∉ diagLang g`, so `diagSim` outputs `[true]`
within `g n`, contradicting determinism of its output `[false]`. -/
theorem diagLang_not_mem_DTIME {g T : ℕ → ℕ}
    (hT : ∀ A N : ℕ, ∃ n ≥ N, A * (T n + n + 1) ^ 2 ≤ g n) :
    diagLang g ∉ DTIME T := by
  classical
  rintro ⟨c₀, M, hM⟩
  let χ := MultiTapeTM.indicator (diagLang g : Set (List Bool))
  obtain ⟨M₁, c₁, hk, h₁⟩ :=
    one_work_tape_binary M (fun x => [χ x]) (fun n => c₀ * T n) hM
  obtain ⟨N, hN⟩ := exists_codeTM M₁ hk
  let α := code.encode N
  have hdec : code.decode α = N := code.toMachineCode.decode_encode N
  obtain ⟨C, hC⟩ := univTM_spec α
  obtain ⟨n, hn, hgn⟩ := hT (8 + C * (c₁ * (c₀ + 1) ^ 2 + 1)) (2 * α.length + 2)
  let w := List.replicate (n - (2 * α.length + 2)) true
  let x := pairEncode α w
  have hx : x.length = n := by
    simp only [x, w, length_pairEncode, List.length_replicate]; omega
  -- the simulated decider
  have hNx : (code.decode α).toFinTM.ComputesInTime x [χ x]
      (c₁ * (c₀ * T n + 1) ^ 2) := by
    rw [hdec, hN]
    have := h₁ x
    rw [hx] at this
    exact this
  have hU := (hC x).1 [χ x] _ hNx
  have hP := preTM_computes x
  rw [show scanPre x ++ x = pairEncode α x from scanPre_pairEncode_append α w] at hP
  have hD := bufferedCompTM_computesInTime preTM univTM hP hU
  have hlen : (pairEncode α x).length ≤ 2 * n := by
    rw [length_pairEncode, hx]; omega
  have hD' : diagSim.ComputesInTime x [χ x] (g x.length) := by
    apply hD.mono
    rw [hx]
    have := diag_cost_le n (T n) c₀ c₁ C
    calc 3 * n + 5 + (pairEncode α x).length + 2 + C * (c₁ * (c₀ * T n + 1) ^ 2 + 1)
        ≤ 5 * n + 7 + C * (c₁ * (c₀ * T n + 1) ^ 2 + 1) := by omega
      _ ≤ _ := this
      _ ≤ g n := hgn
  by_cases hmem : x ∈ (diagLang g : Set (List Bool))
  · have hχ : χ x = true := by simp [χ, MultiTapeTM.indicator, hmem]
    rw [hχ] at hD'
    exact hmem hD'
  · have hχ : χ x = false := by simp [χ, MultiTapeTM.indicator, hmem]
    rw [hχ] at hD'
    have htrue : diagSim.ComputesInTime x [true] (g x.length) := by
      by_contra hc
      exact hmem hc
    have := htrue.output_unique hD'
    simp at this

end Complexity.TimeHierarchy

namespace Complexity

open TimeHierarchy

/-- **The Time Hierarchy Theorem** [AB09, Theorem 3.1], in the form supported by this
development: if `g` is time constructible and `(f(n) + n + 1)² = o(g(n))` — i.e. for
every constant `A`, eventually `A · (f n + n + 1)² ≤ g n` — then
`DTIME(f) ⊊ DTIME(g + 1)`.

Deviations from the book (see the module docstring): the overhead is quadratic
(`(f + n + 1)²` in place of `f log f`), owing to the one-work-tape normal form of
coded machines; `f` need not be time constructible; and the larger class is
`DTIME (g + 1)`, which differs from `DTIME g` only in the degenerate case `g 0 = 0`.

**Proof sketch.** *Inclusion:* the hypothesis with `A = 1` gives `f n ≤ g n` for
`n ≥ N`; the finitely many smaller lengths are absorbed into the constant, so
`f n ≤ c (g n + 1)` for all `n`, and `DTIME` absorbs `c`. *Strictness:* the diagonal
language `diagLang g` lies in `DTIME (g + 1)` (`diagLang_mem_DTIME`) but not in
`DTIME f` (`diagLang_not_mem_DTIME`, whose infinitely-often hypothesis follows from the
eventual one). -/
theorem time_hierarchy {f g : ℕ → ℕ} (hg : TimeConstructible g)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f n + n + 1) ^ 2 ≤ g n) :
    DTIME f ⊂ DTIME (fun n => g n + 1) := by
  refine ⟨?_, fun hsub => diagLang_not_mem_DTIME (g := g) (T := f) ?_
    (hsub (diagLang_mem_DTIME hg))⟩
  · -- inclusion
    obtain ⟨N, hN⟩ := hfg 1
    let F := ∑ i ∈ Finset.range N, f i
    have hle : ∀ n, f n ≤ (F + 1) * (g n + 1) := by
      intro n
      by_cases hn : n < N
      · have : f n ≤ F := Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.mpr hn)
        nlinarith
      · have h := hN n (by omega)
        have : f n ≤ g n := by nlinarith
        nlinarith
    rintro L ⟨c, M, hM⟩
    exact ⟨c * (F + 1), M, fun x => (hM x).mono (by
      simp only [Nat.mul_assoc]; exact Nat.mul_le_mul_left c (hle x.length))⟩
  · intro A N₀
    obtain ⟨N, hN⟩ := hfg A
    exact ⟨max N N₀, le_max_right _ _, hN _ (le_max_left _ _)⟩

/-- **The Time Hierarchy Theorem for a positive bound** [AB09, Theorem 3.1]: as
`Complexity.time_hierarchy`, with the larger class exactly `DTIME g` when `g` never
vanishes (then `DTIME (g + 1) = DTIME g`, the constant `2` being absorbed).

**Proof sketch.** `c (g n + 1) ≤ 2c · g n` when `g n ≥ 1`, so `DTIME (g + 1) ⊆ DTIME g`;
the reverse inclusion is `Complexity.DTIME.mono`; conclude from
`Complexity.time_hierarchy`. -/
theorem time_hierarchy_of_pos {f g : ℕ → ℕ} (hg : TimeConstructible g) (hpos : ∀ n, 0 < g n)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f n + n + 1) ^ 2 ≤ g n) :
    DTIME f ⊂ DTIME g := by
  have heq : DTIME (fun n => g n + 1) = DTIME g := by
    apply Set.Subset.antisymm
    · rintro L ⟨c, M, hM⟩
      refine ⟨2 * c, M, fun x => (hM x).mono ?_⟩
      have := hpos x.length
      dsimp only
      nlinarith
    · exact DTIME.mono (fun n => Nat.le_succ _)
  rw [← heq]
  exact time_hierarchy hg hfg

end Complexity
