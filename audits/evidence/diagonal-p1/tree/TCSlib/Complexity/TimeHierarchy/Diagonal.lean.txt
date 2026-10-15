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

## The parameterized argument

The argument is stated once, over the simulator and its overhead; the received theorem is its
instance at `diagSim` (user authorization, 2026-10-14; design note
`audits/evidence/u2/U2-design.md` §3).

* `diagLangOf W g` is the diagonal language of an arbitrary machine `W`. It lies in
  `DTIME (g + 1)` for every `W` (`diagLangOf_mem_DTIME`), because the clocked runner counts
  `W`'s own steps.
* A `DiagSimulator Φ` is a machine that reproduces, on some input of every large length `n`,
  the verdict of every `DTIME T` language within `A · Φ (T n) n` steps, `A` depending on the
  language. Its diagonal language escapes `DTIME T` whenever `A · Φ (T n) n ≤ g n` infinitely
  often for every `A` (`DiagSimulator.diagLang_not_mem_DTIME`); hence the hierarchy theorem
  with overhead `Φ` (`DiagSimulator.time_hierarchy`, `DiagSimulator.time_hierarchy_of_pos`).
* A `SelfSimulator Ψ` is the universal-machine form of that hypothesis: a machine that runs
  each code on its own input at a cost linear per code, and a normal form of overhead `Ψ` for
  `DTIME` deciders. Padding the input makes it a `DiagSimulator` with overhead `Ψ t + n + 1`
  (`SelfSimulator.toDiagSimulator`).
* The received instance is `diagSim` with the one-work-tape normal form, `Ψ t = (t + 1)²`
  (`oneTapeSelfSimulator`), weakened to the overhead `(t + n + 1)²` (`sqDiagSimulator`).
  `diagLang_mem_DTIME`, `diagLang_not_mem_DTIME`, `time_hierarchy` and
  `time_hierarchy_of_pos` are its corollaries, with their statements unchanged.

## Divergences from [AB09, Theorem 3.1]

* **Overhead `f²` instead of `f log f`.** The book's universal machine has
  `O(T log T)` overhead ([AB09, Theorem 1.9 / §1.7]); this development's universal
  machine is linear on coded machines but coded machines are one-work-tape binary
  machines, and an arbitrary binary machine is normal-formed with quadratic slowdown
  (`Turing.FinTM.one_work_tape_binary`, [AB09, Claims 1.5–1.6]). The hypothesis is
  therefore `(f(n) + n + 1)² = o(g(n))`, written out as
  `∀ A, ∃ N, ∀ n ≥ N, A · (f n + n + 1)² ≤ g n`. The `+ n + 1` absorbs the linear
  cost of reading the input and the `+ 1` normalization of `DTIME` bounds. The
  sharper `f log f` form is planned as another instance of the parameterized argument
  (above): a two-work-tape universal machine with the Hennie–Stearns `O(T log T)` normal
  form ([AB09, §1.7]; `AroraBarakChapters3-4Plan.md` §2.1). It is not available until those
  exist.
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
* `Complexity.TimeHierarchy.diagLangOf` — the diagonal language of an arbitrary simulator.
* `Complexity.TimeHierarchy.DiagSimulator`, `SelfSimulator` — the hypothesis on a simulator,
  at the level of padded simulation and at the level of a universal machine with a normal
  form; `DiagSimulator.mono`, `SelfSimulator.toDiagSimulator` — weakening and input padding.
* `Complexity.TimeHierarchy.oneTapeSelfSimulator`, `sqDiagSimulator` — the received instance.

## Main results

* `Complexity.TimeHierarchy.diagLang_mem_DTIME` — `diagLang g ∈ DTIME (g + 1)`.
* `Complexity.TimeHierarchy.diagLang_not_mem_DTIME` — `diagLang g ∉ DTIME T` whenever
  `A · (T n + n + 1)² ≤ g n` infinitely often for every `A`.
* `Complexity.time_hierarchy` — [AB09, Theorem 3.1], in the form above.
* `Complexity.time_hierarchy_of_pos` — the same with `DTIME g` when `g` never vanishes.
* `Complexity.TimeHierarchy.diagLangOf_mem_DTIME`, `DiagSimulator.diagLang_not_mem_DTIME`,
  `DiagSimulator.time_hierarchy`, `DiagSimulator.time_hierarchy_of_pos` — the parameterized
  argument, of which the four results above are the instance at `sqDiagSimulator`.

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

/-! ### The parameterized argument -/

/-- **The diagonal language of a simulator `W`** [AB09, Theorem 3.1, proof]: the strings `x`
on which `W` does **not** halt with output `[true]` within `g(|x|)` steps. The received
`diagLang g` is the case `W = diagSim` (`diagLang_eq_diagLangOf`). -/
def diagLangOf (W : FinTM Bool) (g : ℕ → ℕ) : Language Bool :=
  {x | ¬W.ComputesInTime x [true] (g x.length)}

/-- The received diagonal language is the diagonal language of `diagSim`, by definition. -/
theorem diagLang_eq_diagLangOf (g : ℕ → ℕ) : diagLang g = diagLangOf diagSim g := rfl

/-- **The diagonal language of any simulator is decidable in time `O(g)`** [AB09, Theorem 3.1,
proof]: for time-constructible `g` and every machine `W`, `diagLangOf W g ∈ DTIME (g + 1)`.
Nothing is assumed of `W`: the clocked runner counts `W`'s own steps.

**Proof sketch.** Run the clocked runner `clockTM K W`, with `K` the time-constructibility
witness of `g`: its budget word is `bits (g n)` of value `g n`, so by `clockTM_spec` it outputs
`[x ∈ diagLangOf W g]` within `c_K (g n + 1) + 4|bits (g n)| + n + 4 g n + 6 ≤
(c_K + 15)(g n + 1)` steps, using `|bits m| ≤ m` and `n ≤ g n`. -/
theorem diagLangOf_mem_DTIME (W : FinTM Bool) {g : ℕ → ℕ} (hg : TimeConstructible g) :
    diagLangOf W g ∈ DTIME (fun n => g n + 1) := by
  classical
  obtain ⟨hgn, cK, _, K, hK⟩ := hg
  refine ⟨cK + 15, clockTM K W, fun x => ?_⟩
  have h := clockTM_spec K W x (g x.length).bits _ (hK x)
  rw [ctrVal_bits] at h
  have hout : [!(decide (W.ComputesInTime x [true] (g x.length)))] =
      [MultiTapeTM.indicator (diagLangOf W g : Set (List Bool)) x] := by
    by_cases hx : W.ComputesInTime x [true] (g x.length)
    · have : x ∉ (diagLangOf W g : Set (List Bool)) := fun h' => h' hx
      simp [MultiTapeTM.indicator, hx, this]
    · have : x ∈ (diagLangOf W g : Set (List Bool)) := hx
      simp [MultiTapeTM.indicator, hx, this]
  rw [hout] at h
  apply h.mono
  have h1 := length_bits_le_self (g x.length)
  have h2 := hgn x.length
  nlinarith

/-- **A diagonal simulator with overhead `Φ`** (the hypothesis of the diagonal argument
[AB09, Theorem 3.1, proof]; design note `audits/evidence/u2/U2-design.md` §3): a machine `W`
such that for every time bound `T` and every language `L ∈ DTIME T` there are constants `A`
and `N₀` with: for every length `n ≥ N₀` some input `x` of length `n` makes `W` halt with the
verdict `[x ∈ L]` within `A · Φ (T n) n` steps. No clock is part of it: the clocked runner
supplies one for every `W` (`diagLangOf_mem_DTIME`). Deviation: the book simulates a code of
the machine at hand, which has infinitely many codes; here the simulator is only required to
succeed on one input of each large length, which is what the diagonal argument uses. -/
structure DiagSimulator (Φ : ℕ → ℕ → ℕ) where
  /-- the simulating machine -/
  W : FinTM Bool
  /-- padded simulation of every `DTIME T` language within `A · Φ (T n) n` steps -/
  simulates : ∀ (T : ℕ → ℕ) (L : Language Bool), L ∈ DTIME T →
    ∃ A N₀ : ℕ, ∀ n ≥ N₀, ∃ x : List Bool, x.length = n ∧
      W.ComputesInTime x [MultiTapeTM.indicator (L : Set (List Bool)) x] (A * Φ (T n) n)

namespace DiagSimulator

variable {Φ : ℕ → ℕ → ℕ}

/-- **Weakening the overhead** up to a constant factor: a diagonal simulator with overhead `Φ`
is one, with the same machine, with overhead `Φ'` whenever `Φ ≤ K · Φ'` pointwise. -/
def mono (S : DiagSimulator Φ) {Φ' : ℕ → ℕ → ℕ} (K : ℕ) (h : ∀ t n, Φ t n ≤ K * Φ' t n) :
    DiagSimulator Φ' where
  W := S.W
  simulates T L hL := by
    obtain ⟨A, N₀, hA⟩ := S.simulates T L hL
    refine ⟨A * K, N₀, fun n hn => ?_⟩
    obtain ⟨x, hx, hW⟩ := hA n hn
    exact ⟨x, hx, hW.mono (by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left A (h _ _))⟩

/-- **The diagonal language is not in `DTIME T`** [AB09, Theorem 3.1, proof], for a diagonal
simulator with overhead `Φ`, provided `A · Φ (T n) n ≤ g n` for infinitely many `n`, for every
constant `A` (the infinitely-often form).

**Proof sketch.** Suppose `diagLangOf W g ∈ DTIME T`. The simulation clause gives `A` and
`N₀`; pick `n ≥ N₀` with `A · Φ (T n) n ≤ g n`, and an input `x` of length `n` on which `W`
halts with `[χ(x)]` within `A · Φ (T n) n ≤ g n` steps, `χ` the indicator of the diagonal
language. If `χ(x) = true` then `x ∈ diagLangOf W g`, so `W` does not output `[true]` within
`g n`, a contradiction; if `χ(x) = false` then `x ∉ diagLangOf W g`, so `W` outputs `[true]`
within `g n`, against the uniqueness of its output `[false]`. -/
theorem diagLang_not_mem_DTIME (S : DiagSimulator Φ) {g T : ℕ → ℕ}
    (hT : ∀ A N : ℕ, ∃ n ≥ N, A * Φ (T n) n ≤ g n) :
    diagLangOf S.W g ∉ DTIME T := by
  classical
  intro hL
  obtain ⟨A, N₀, hA⟩ := S.simulates T _ hL
  obtain ⟨n, hn, hgn⟩ := hT A N₀
  obtain ⟨x, hx, hW⟩ := hA n hn
  let χ := MultiTapeTM.indicator (diagLangOf S.W g : Set (List Bool))
  have hD : S.W.ComputesInTime x [χ x] (g x.length) := hW.mono (by rw [hx]; exact hgn)
  by_cases hmem : x ∈ (diagLangOf S.W g : Set (List Bool))
  · have hχ : χ x = true := by simp [χ, MultiTapeTM.indicator, hmem]
    rw [hχ] at hD
    exact hmem hD
  · have hχ : χ x = false := by simp [χ, MultiTapeTM.indicator, hmem]
    rw [hχ] at hD
    have htrue : S.W.ComputesInTime x [true] (g x.length) := by
      by_contra hc
      exact hmem hc
    have := htrue.output_unique hD
    simp at this

/-- **The Time Hierarchy Theorem with overhead `Φ`** [AB09, Theorem 3.1], for a diagonal
simulator: if `g` is time constructible, `t ≤ Φ t n` for all `t` and `n`, and for every
constant `A` eventually `A · Φ (f n) n ≤ g n`, then `DTIME(f) ⊊ DTIME(g + 1)`. The deviations
of `Complexity.time_hierarchy` apply (`f` need not be time constructible; `DTIME (g + 1)`).

**Proof sketch.** *Inclusion:* the hypothesis at `A = 1` and `t ≤ Φ t n` give `f n ≤ g n`
for `n ≥ N`; the finitely many smaller lengths are absorbed into the constant, so
`f n ≤ c (g n + 1)` for all `n`, and `DTIME` absorbs `c`. *Strictness:* `diagLangOf W g` lies
in `DTIME (g + 1)` (`diagLangOf_mem_DTIME`) but not in `DTIME f`
(`DiagSimulator.diagLang_not_mem_DTIME`, whose infinitely-often hypothesis follows from the
eventual one). -/
theorem time_hierarchy (S : DiagSimulator Φ) (hΦ : ∀ t n, t ≤ Φ t n)
    {f g : ℕ → ℕ} (hg : TimeConstructible g)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * Φ (f n) n ≤ g n) :
    DTIME f ⊂ DTIME (fun n => g n + 1) := by
  refine ⟨?_, fun hsub => S.diagLang_not_mem_DTIME (g := g) (T := f) ?_
    (hsub (diagLangOf_mem_DTIME S.W hg))⟩
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
        have h' := hΦ (f n) n
        have : f n ≤ g n := by omega
        nlinarith
    rintro L ⟨c, M, hM⟩
    exact ⟨c * (F + 1), M, fun x => (hM x).mono (by
      simp only [Nat.mul_assoc]; exact Nat.mul_le_mul_left c (hle x.length))⟩
  · intro A N₀
    obtain ⟨N, hN⟩ := hfg A
    exact ⟨max N N₀, le_max_right _ _, hN _ (le_max_left _ _)⟩

/-- **The Time Hierarchy Theorem with overhead `Φ`, for a positive bound** [AB09,
Theorem 3.1]: as `DiagSimulator.time_hierarchy`, with the larger class exactly `DTIME g` when
`g` never vanishes.

**Proof sketch.** `c (g n + 1) ≤ 2c · g n` when `g n ≥ 1`, so `DTIME (g + 1) ⊆ DTIME g`; the
reverse inclusion is `Complexity.DTIME.mono`; conclude from `DiagSimulator.time_hierarchy`. -/
theorem time_hierarchy_of_pos (S : DiagSimulator Φ) (hΦ : ∀ t n, t ≤ Φ t n)
    {f g : ℕ → ℕ} (hg : TimeConstructible g) (hpos : ∀ n, 0 < g n)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * Φ (f n) n ≤ g n) :
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
  exact S.time_hierarchy hΦ hg hfg

end DiagSimulator

/-- **A self-simulator with normal-form overhead `Ψ`** (the universal-machine form of the
hypothesis [AB09, §1.4 and Theorem 3.1, proof]; design note `audits/evidence/u2/U2-design.md`
§3): a machine `W` and machines `decode α` indexed by codes `α`, such that
* for every code `α` there is a constant `C`, depending on `α` only, with: whenever
  `decode α` halts on `pairEncode α w` with a one-bit output `[b]` within `t` steps, `W` halts
  on the same input with `[b]` within `C · (t + |pairEncode α w| + 1)` steps (self-application:
  the coded machine runs on the very input that carries its code);
* every `DTIME T` language has a code `α` whose machine decides it within
  `c · (Ψ (T n) + 1)` steps, for a constant `c` (the normal form).

No clock, no uniformity in the code and no output beyond the one-bit verdict is required.
Deviation: the book uses that every machine has infinitely many codes; here one code is fixed
and the input is padded (`SelfSimulator.toDiagSimulator`), as in the received proof, because
the constant `C` depends on the code string. -/
structure SelfSimulator (Ψ : ℕ → ℕ) where
  /-- the self-application simulator -/
  W : FinTM Bool
  /-- the machine each code denotes -/
  decode : List Bool → FinTM Bool
  /-- per-code linear self-simulation of one-bit verdicts -/
  simulates : ∀ α : List Bool, ∃ C : ℕ, ∀ (w : List Bool) (b : Bool) (t : ℕ),
    (decode α).ComputesInTime (pairEncode α w) [b] t →
    W.ComputesInTime (pairEncode α w) [b] (C * (t + (pairEncode α w).length + 1))
  /-- the normal form: every `DTIME T` language has a coded decider within `c · (Ψ T + 1)` -/
  normalForm : ∀ (T : ℕ → ℕ) (L : Language Bool), L ∈ DTIME T →
    ∃ (α : List Bool) (c : ℕ), ∀ x : List Bool,
      (decode α).ComputesInTime x [MultiTapeTM.indicator (L : Set (List Bool)) x]
        (c * (Ψ (T x.length) + 1))

/-- **Input padding** [AB09, Theorem 3.1, proof]: a self-simulator with normal-form overhead
`Ψ` is a diagonal simulator, with the same machine, with overhead `Ψ t + n + 1`.

**Proof sketch.** For `L ∈ DTIME T` take the normal form's code `α` and constant `c`, and the
simulation constant `C` of `α`. For `n ≥ 2|α| + 2` the input
`x = pairEncode α 1^(n - 2|α| - 2)` has length `n`; `decode α` decides `L` on it within
`c (Ψ (T n) + 1)` steps, so `W` reproduces the verdict within
`C (c (Ψ (T n) + 1) + n + 1) ≤ C (c + 1) (Ψ (T n) + n + 1)` steps. -/
def SelfSimulator.toDiagSimulator {Ψ : ℕ → ℕ} (S : SelfSimulator Ψ) :
    DiagSimulator (fun t n => Ψ t + n + 1) where
  W := S.W
  simulates T L hL := by
    obtain ⟨α, c, hc⟩ := S.normalForm T L hL
    obtain ⟨C, hC⟩ := S.simulates α
    refine ⟨C * (c + 1), 2 * α.length + 2, fun n hn => ?_⟩
    have hx : (pairEncode α (List.replicate (n - (2 * α.length + 2)) true)).length = n := by
      simp only [length_pairEncode, List.length_replicate]; omega
    refine ⟨pairEncode α (List.replicate (n - (2 * α.length + 2)) true), hx, ?_⟩
    have h := hC _ _ _ (hc (pairEncode α (List.replicate (n - (2 * α.length + 2)) true)))
    rw [hx] at h
    apply h.mono
    have hle : c * (Ψ (T n) + 1) + n + 1 ≤ (c + 1) * (Ψ (T n) + n + 1) := by nlinarith
    calc C * (c * (Ψ (T n) + 1) + n + 1) ≤ C * ((c + 1) * (Ψ (T n) + n + 1)) :=
          Nat.mul_le_mul_left C hle
      _ = C * (c + 1) * (Ψ (T n) + n + 1) := by ring

/-- **The diagonal language is decidable in time `O(g)`** [AB09, Theorem 3.1, proof:
"`D` runs in time `O(g(n))`"]: for time-constructible `g`,
`diagLang g ∈ DTIME (g + 1)`.

**Proof sketch.** The case `W = diagSim` of `diagLangOf_mem_DTIME`, since `diagLang g` is
`diagLangOf diagSim g` by definition (`diagLang_eq_diagLangOf`): the clocked runner
`clockTM K diagSim`, with `K` the time-constructibility witness of `g`, decides it within
`(c_K + 15)(g n + 1)` steps. -/
theorem diagLang_mem_DTIME {g : ℕ → ℕ} (hg : TimeConstructible g) :
    diagLang g ∈ DTIME (fun n => g n + 1) :=
  diagLangOf_mem_DTIME diagSim hg

/-- The polynomial bookkeeping of the received diagonal argument: with `X = T + n + 1`, the
simulation cost `5n + 7 + C · (c₁ (c₀ T + 1)² + 1)` is at most
`(8 + C (c₁ (c₀ + 1)² + 1)) · X²`. Kept with its statement; the parameterized argument does its
bookkeeping in `oneTapeSelfSimulator`, `SelfSimulator.toDiagSimulator` and `sqDiagSimulator`,
and no declaration of this file uses this lemma. -/
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

/-! ### The received instance -/

/-- **The received self-simulator** [AB09, Theorem 3.1, proof; Claims 1.5–1.6]: `diagSim` is a
self-simulator for the codes of `code` (`decode α` the machine `code.decode α`), with the
one-work-tape normal form, whose overhead is the square `Ψ t = (t + 1)²`.

**Proof sketch.** *Simulation:* on `x = pairEncode α w`, `preTM` writes `pairEncode α x`
within `3|x| + 5` steps (`preTM_computes`, `scanPre_pairEncode_append`), and `univTM` simulates
the coded machine on `x` within `C (t + 1)` steps (`univTM_spec`); buffered composition adds
the intermediate length plus two, `|pairEncode α x| + 2 ≤ 2|x| + 2`
(`bufferedCompTM_computesInTime`): in all at most `(C + 7)(t + |x| + 1)` steps. *Normal form:*
a decider within `c₀ T` becomes a one-work-tape binary machine within `c₁ (c₀ T + 1)²`
(`Turing.FinTM.one_work_tape_binary`), then a coded machine `N` with the same runs
(`Turing.exists_codeTM`), whose code `code.encode N` decodes back to `N`; and
`c₁ (c₀ T + 1)² ≤ c₁ (c₀ + 1)² ((T + 1)² + 1)`. -/
noncomputable def oneTapeSelfSimulator : SelfSimulator (fun t => (t + 1) ^ 2) where
  W := diagSim
  decode α := (code.decode α).toFinTM
  simulates α := by
    obtain ⟨C, hC⟩ := univTM_spec α
    refine ⟨C + 7, fun w b t h => ?_⟩
    have hU := (hC (pairEncode α w)).1 [b] t h
    have hP := preTM_computes (pairEncode α w)
    rw [scanPre_pairEncode_append α w] at hP
    have hD := bufferedCompTM_computesInTime preTM univTM hP hU
    apply hD.mono
    have h1 : (pairEncode α (pairEncode α w)).length ≤ 2 * (pairEncode α w).length := by
      simp only [length_pairEncode]; omega
    nlinarith
  normalForm T L := by
    rintro ⟨c₀, M, hM⟩
    obtain ⟨M₁, c₁, hk, h₁⟩ := one_work_tape_binary M
      (fun x => [MultiTapeTM.indicator (L : Set (List Bool)) x]) (fun n => c₀ * T n) hM
    obtain ⟨N, hN⟩ := exists_codeTM M₁ hk
    refine ⟨code.encode N, c₁ * (c₀ + 1) ^ 2, fun x => ?_⟩
    rw [show code.decode (code.encode N) = N from code.toMachineCode.decode_encode N]
    apply ((hN x _ _).2 (h₁ x)).mono
    have hlin : c₀ * T x.length + 1 ≤ (c₀ + 1) * (T x.length + 1) := by nlinarith
    have hsq : (c₀ * T x.length + 1) ^ 2 ≤ (c₀ + 1) ^ 2 * (T x.length + 1) ^ 2 := by
      rw [← mul_pow]; exact Nat.pow_le_pow_left hlin 2
    have := Nat.mul_le_mul_left c₁ hsq
    nlinarith

/-- The received overhead dominates the time: `t ≤ (t + n + 1)²` for all `t` and `n`. -/
theorem le_sq_overhead (t n : ℕ) : t ≤ (t + n + 1) ^ 2 := by
  have h : t + n + 1 ≤ (t + n + 1) ^ 2 := by rw [pow_two]; exact Nat.le_mul_self _
  omega

/-- **The received diagonal simulator**: `diagSim` with the overhead `(t + n + 1)²` of the
received theorem, from `oneTapeSelfSimulator` by input padding
(`SelfSimulator.toDiagSimulator`) and `(t + 1)² + n + 1 ≤ 2 (t + n + 1)²`. -/
noncomputable def sqDiagSimulator : DiagSimulator (fun t n => (t + n + 1) ^ 2) :=
  oneTapeSelfSimulator.toDiagSimulator.mono 2 (fun t n => by
    show (t + 1) ^ 2 + n + 1 ≤ 2 * (t + n + 1) ^ 2
    have h1 : (t + 1) ^ 2 ≤ (t + n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : t + n + 1 ≤ (t + n + 1) ^ 2 := by rw [pow_two]; exact Nat.le_mul_self _
    omega)

/-- The received diagonal simulator's machine is `diagSim`, by definition. -/
theorem sqDiagSimulator_W : sqDiagSimulator.W = diagSim := rfl

/-- **The diagonal language is not in `DTIME T`** [AB09, Theorem 3.1, proof: "`D`
differs from every machine running in time `f`"], provided `g` dominates
`A · (T n + n + 1)²` for infinitely many `n`, for every constant `A`.

**Proof sketch.** The case `sqDiagSimulator` of `DiagSimulator.diagLang_not_mem_DTIME`,
whose machine is `diagSim` (`sqDiagSimulator_W`). Its simulation clause is
`oneTapeSelfSimulator`'s, padded by `SelfSimulator.toDiagSimulator`: a decider `M` of
`diagLang g` within `c₀ T(n)` becomes a one-work-tape binary machine within `c₁ (c₀ T + 1)²`
(`Turing.FinTM.one_work_tape_binary`) and then a coded machine `N` with the same runs
(`Turing.exists_codeTM`), with code `α = ⌞N⌟`. On `x = pairEncode α 1^(n - 2|α| - 2)`, of
length `n`, `preTM` and `univTM` reproduce `M`'s verdict `[χ(x)]` within `A (T n + n + 1)²`
steps, `A` depending on `M` only. At an `n` with `A (T n + n + 1)² ≤ g n` that verdict
contradicts the definition of `diagLang g`: if `χ(x) = true`, `diagSim` does not output
`[true]` within `g n`; if `χ(x) = false`, it does, against the uniqueness of its output
`[false]`. -/
theorem diagLang_not_mem_DTIME {g T : ℕ → ℕ}
    (hT : ∀ A N : ℕ, ∃ n ≥ N, A * (T n + n + 1) ^ 2 ≤ g n) :
    diagLang g ∉ DTIME T :=
  sqDiagSimulator.diagLang_not_mem_DTIME hT

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

**Proof sketch.** The case `Φ t n = (t + n + 1)²` of `DiagSimulator.time_hierarchy` at
`sqDiagSimulator`, with `t ≤ (t + n + 1)²` (`le_sq_overhead`). *Inclusion:* the hypothesis
with `A = 1` gives `f n ≤ g n` for `n ≥ N`; the finitely many smaller lengths are absorbed
into the constant, so `f n ≤ c (g n + 1)` for all `n`, and `DTIME` absorbs `c`.
*Strictness:* the diagonal language `diagLang g` lies in `DTIME (g + 1)`
(`diagLangOf_mem_DTIME`) but not in `DTIME f` (`DiagSimulator.diagLang_not_mem_DTIME`, whose
infinitely-often hypothesis follows from the eventual one). -/
theorem time_hierarchy {f g : ℕ → ℕ} (hg : TimeConstructible g)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f n + n + 1) ^ 2 ≤ g n) :
    DTIME f ⊂ DTIME (fun n => g n + 1) :=
  sqDiagSimulator.time_hierarchy le_sq_overhead hg hfg

/-- **The Time Hierarchy Theorem for a positive bound** [AB09, Theorem 3.1]: as
`Complexity.time_hierarchy`, with the larger class exactly `DTIME g` when `g` never
vanishes (then `DTIME (g + 1) = DTIME g`, the constant `2` being absorbed).

**Proof sketch.** The case `Φ t n = (t + n + 1)²` of
`DiagSimulator.time_hierarchy_of_pos` at `sqDiagSimulator`: `c (g n + 1) ≤ 2c · g n` when
`g n ≥ 1`, so `DTIME (g + 1) ⊆ DTIME g`; the reverse inclusion is `Complexity.DTIME.mono`;
conclude from `DiagSimulator.time_hierarchy`. -/
theorem time_hierarchy_of_pos {f g : ℕ → ℕ} (hg : TimeConstructible g) (hpos : ∀ n, 0 < g n)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f n + n + 1) ^ 2 ≤ g n) :
    DTIME f ⊂ DTIME g :=
  sqDiagSimulator.time_hierarchy_of_pos le_sq_overhead hg hpos hfg

end Complexity
