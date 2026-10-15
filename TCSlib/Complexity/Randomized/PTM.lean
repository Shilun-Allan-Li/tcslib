/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.ClassNP.NTIME
import TCSlib.Complexity.Randomized.RandomBits

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Probabilistic Turing machines and the classes BPTIME, BPP, RTIME, RP, coRP

The machine-level randomized classes of [AB09, §7.1 and §7.3].  A probabilistic Turing
machine is a binary-choice machine `Turing.FinNDTM Bool` read probabilistically: its coin
tosses are the choice word of `Turing.NDTM.runWith`, and `Pr[M(x) = v]` over `t` coins is
the fraction of length-`t` choice words whose run ends with output `v` (`Randomized.randProb`).

## Main definitions

* `Turing.FinNDTM.RunsInTime` — [AB09, Def 7.1]: halts within `T(|x|)` steps on every branch.
* `Turing.FinNDTM.outputWith`, `Turing.FinNDTM.outputProb` — the output under a coin word and
  the probability of an output over `t` coins.
* `Turing.FinNDTM.BPDecidesInTime`, `Randomized.BPTIME`, `Randomized.BPP_PTM` — [AB09, Def 7.2].
* `Turing.FinNDTM.RDecidesInTime`, `Randomized.RTIME`, `Randomized.RP_PTM` — [AB09, Def 7.6];
  `Randomized.coRP_PTM` — [AB09, §7.3].
* `Turing.NDTM.flipOutput` — negate every emitted output bit.

## Main results

* `Turing.FinNDTM.outputProb_eq_of_haltsWithin` — the acceptance probability does not change
  once every branch has halted.
* `Randomized.BPTIME.mono`, `Randomized.BPTIME_const_mul_subset`, and the `RTIME` analogues.
* `Randomized.compl_mem_BPTIME`, `Randomized.compl_mem_BPP_PTM` — closure under complement.

## Divergences

* Output convention: [AB09] says the machine "only outputs 1 or 0".  `BPDecidesInTime` counts a
  branch as correct iff its output is exactly `[L(x)]` (as `FinNDTM.AcceptsWithin` reads
  `[true]`), so any other output counts as an error.  For `RTIME` the clause
  "`x ∉ L ⇒ Pr[M(x) = 1] = 0`" is stated as "every branch outputs `[false]`", which is the
  book's clause under its 0/1-output convention and makes `RP ⊆ BPP` hold as in the book.
  So `BPDecidesInTime` admits machines with other outputs (counted as errors), and the `RTIME`
  soundness clause is stricter than the literal `Pr[M(x) = 1] = 0` for such machines; that
  the classes coincide with the book's is secured by the equivalence with [AB09, Def 7.3]
  (unit U2).
* As for `Complexity.NTIME`, the constant `c` in `c · T` ranges over `ℕ`; `c = 0` (or
  `T n = 0`) gives the unsatisfiable budget `0`, since no machine is halted at time `0`, and
  contributes nothing.  `BPP`/`RP` use the bounds `n^c + 1` of `Complexity.P`, the `+ 1`
  keeping the budget positive at `n = 0`.
* `Turing.NDTM.flipOutput` is a transition relabelling, defined directly; the general output
  map `Turing.NDTM.mapOutput` (`TCSlib.Complexity.TuringMachine.Build.NDCombinators`) is not
  imported here.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Turing

namespace NDTM

variable {k : ℕ} {State : Type*} {input : List Bool}

/-- The machine `tm` with every emitted output bit negated: the transitions of `tm`, with the
output symbol of each action replaced by its negation. -/
def flipOutput (tm : NDTM k Bool State) : NDTM k Bool State :=
  ⟨tm.q₀, fun b q i w => { tm.tr b q i w with output := (tm.tr b q i w).output.map not }⟩

/-- A configuration with its output tape negated bitwise. -/
def flipCfg (cfg : Cfg k Bool State input) : Cfg k Bool State input :=
  { cfg with output := cfg.output.map not }

/-- One step of `flipOutput` on a negated configuration is the negation of one step. -/
theorem flipOutput_stepWith (tm : NDTM k Bool State) (b : Bool) (cfg : Cfg k Bool State input) :
    tm.flipOutput.stepWith b (flipCfg cfg) = flipCfg (tm.stepWith b cfg) := by
  cases h : cfg.state with
  | none =>
    rw [stepWith_of_halt h, stepWith_of_halt (by simpa [flipCfg] using h)]
  | some q =>
    have h' : (flipCfg cfg).state = some q := by simpa [flipCfg] using h
    simp only [stepWith, h, flipOutput, flipCfg, Action.apply, List.map_append,
      Option.toList_map]
    rfl

/-- Running `flipOutput` from a negated configuration gives the negated run. -/
theorem flipOutput_runWith (tm : NDTM k Bool State) (w : List Bool)
    (cfg : Cfg k Bool State input) :
    tm.flipOutput.runWith w (flipCfg cfg) = flipCfg (tm.runWith w cfg) := by
  induction w generalizing cfg with
  | nil => rfl
  | cons b w ih => rw [runWith_cons, runWith_cons, flipOutput_stepWith, ih]

/-- `flipOutput` starts in the negation of the original initial configuration. -/
theorem flipOutput_initCfg (tm : NDTM k Bool State) (x : List Bool) :
    tm.flipOutput.initCfg x = flipCfg (tm.initCfg x) := rfl

end NDTM

namespace FinNDTM

/-- `flipOutput` on the bundled layer: the same tapes and states, output bits negated. -/
def flipOutput (N : FinNDTM Bool) : FinNDTM Bool :=
  ⟨N.k, N.State, N.tm.flipOutput⟩

/-- The PTM `N` *runs in time* `T`: on every input `x` it halts within `T(|x|)` steps whatever
its coin tosses. [AB09, Def 7.1] -/
def RunsInTime (N : FinNDTM Bool) (T : ℕ → ℕ) : Prop :=
  ∀ x : List Bool, N.tm.HaltsWithin x (T x.length)

/-- The output of `N` on `x` under the coin word `w` (one coin per step). -/
def outputWith (N : FinNDTM Bool) (x w : List Bool) : List Bool :=
  (N.tm.runWith w (N.tm.initCfg x)).output

/-- `Pr[M(x) = v]` over `t` fair coins: the fraction of coin words of length `t` whose run on
`x` ends with output `v`. [AB09, §7.1: "the fraction of branches"] -/
def outputProb (N : FinNDTM Bool) (x : List Bool) (t : ℕ) (v : List Bool) : ℚ :=
  Randomized.randProb t fun w => N.outputWith x w = v

/-- The PTM `N` *decides* `L` in time `T` with bounded error: on every input `x` it halts
within `T(|x|)` steps on every branch, and `Pr[M(x) = L(x)] ≥ 2/3`. [AB09, Def 7.2] -/
def BPDecidesInTime (N : FinNDTM Bool) (L : Language Bool) (T : ℕ → ℕ) : Prop :=
  ∀ x : List Bool, N.tm.HaltsWithin x (T x.length) ∧
    2/3 ≤ N.outputProb x (T x.length) [MultiTapeTM.indicator (L : Set (List Bool)) x]

/-- The PTM `N` decides `L` in time `T` with one-sided error: every branch halts within
`T(|x|)` steps, members are accepted with probability at least `2/3`, and on non-members every
branch outputs `0`. [AB09, Def 7.6] -/
def RDecidesInTime (N : FinNDTM Bool) (L : Language Bool) (T : ℕ → ℕ) : Prop :=
  ∀ x : List Bool, N.tm.HaltsWithin x (T x.length) ∧
    (x ∈ L → 2/3 ≤ N.outputProb x (T x.length) [true]) ∧
    (x ∉ L → ∀ w : List Bool, w.length = T x.length → N.outputWith x w = [false])

/-- `BPDecidesInTime` bundles `RunsInTime`. -/
theorem BPDecidesInTime.runsInTime {N : FinNDTM Bool} {L : Language Bool} {T : ℕ → ℕ}
    (h : N.BPDecidesInTime L T) : N.RunsInTime T := fun x => (h x).1

/-- `RDecidesInTime` bundles `RunsInTime`. -/
theorem RDecidesInTime.runsInTime {N : FinNDTM Bool} {L : Language Bool} {T : ℕ → ℕ}
    (h : N.RDecidesInTime L T) : N.RunsInTime T := fun x => (h x).1

/-- Once every branch has halted by time `t`, the run under a longer coin word is the run
under its length-`t` prefix. -/
theorem runWith_eq_runWith_take {N : FinNDTM Bool} {x : List Bool} {t : ℕ}
    (h : N.tm.HaltsWithin x t) {w : List Bool} (hw : t ≤ w.length) :
    N.tm.runWith w (N.tm.initCfg x) = N.tm.runWith (w.take t) (N.tm.initCfg x) := by
  have hhalt := h (w.take t) (List.length_take_of_le hw)
  have hrun := NDTM.runWith_append (tm := N.tm) (w.take t) (w.drop t) (N.tm.initCfg x)
  rw [List.take_append_drop, NDTM.runWith_of_halt _ hhalt] at hrun
  exact hrun

/-- **Coins past the halting time are ignored**: if every branch halts within `t` steps, the
output distribution over `t' ≥ t` coins equals the one over `t` coins. -/
theorem outputProb_eq_of_haltsWithin {N : FinNDTM Bool} {x : List Bool} {t t' : ℕ}
    (h : N.tm.HaltsWithin x t) (hle : t ≤ t') (v : List Bool) :
    N.outputProb x t' v = N.outputProb x t v := by
  unfold outputProb
  rw [← Randomized.randProb_take hle (fun w => N.outputWith x w = v)]
  refine Randomized.randProb_congr fun r => ?_
  have hlen : t ≤ (List.ofFn r).length := by rw [List.length_ofFn]; exact hle
  simp only [outputWith, runWith_eq_runWith_take h hlen]

/-- If every branch of length `t` outputs `v`, then `Pr[M(x) = v] = 1`. -/
theorem outputProb_eq_one {N : FinNDTM Bool} {x : List Bool} {t : ℕ} {v : List Bool}
    (h : ∀ w : List Bool, w.length = t → N.outputWith x w = v) : N.outputProb x t v = 1 := by
  unfold outputProb
  rw [Randomized.randProb_congr (B := fun _ => True) fun r => by
    simp only [h _ (List.length_ofFn)]]
  exact Randomized.randProb_true

/-- An output of positive probability is produced by some branch. -/
theorem exists_outputWith_of_outputProb_pos {N : FinNDTM Bool} {x : List Bool} {t : ℕ}
    {v : List Bool} (h : 0 < N.outputProb x t v) :
    ∃ w : List Bool, w.length = t ∧ N.outputWith x w = v := by
  obtain ⟨r, hr⟩ := Randomized.exists_ofFn_of_randProb_pos h
  exact ⟨List.ofFn r, List.length_ofFn, hr⟩

/-- Bounded-error deciding is monotone in the time bound. -/
theorem BPDecidesInTime.mono {N : FinNDTM Bool} {L : Language Bool} {T₁ T₂ : ℕ → ℕ}
    (h : N.BPDecidesInTime L T₁) (hT : ∀ n, T₁ n ≤ T₂ n) : N.BPDecidesInTime L T₂ := by
  intro x
  obtain ⟨hhalt, hprob⟩ := h x
  refine ⟨hhalt.mono (hT _), ?_⟩
  rw [outputProb_eq_of_haltsWithin hhalt (hT _)]
  exact hprob

/-- One-sided-error deciding is monotone in the time bound. -/
theorem RDecidesInTime.mono {N : FinNDTM Bool} {L : Language Bool} {T₁ T₂ : ℕ → ℕ}
    (h : N.RDecidesInTime L T₁) (hT : ∀ n, T₁ n ≤ T₂ n) : N.RDecidesInTime L T₂ := by
  intro x
  obtain ⟨hhalt, hin, hout⟩ := h x
  refine ⟨hhalt.mono (hT _), fun hx => ?_, fun hx w hw => ?_⟩
  · rw [outputProb_eq_of_haltsWithin hhalt (hT _)]
    exact hin hx
  · have hle : T₁ x.length ≤ w.length := hw ▸ hT _
    unfold outputWith
    rw [runWith_eq_runWith_take hhalt hle]
    exact hout hx _ (List.length_take_of_le hle)

/-- A one-sided-error decider is a bounded-error decider. [AB09, §7.3: `RP ⊆ BPP`] -/
theorem RDecidesInTime.bpDecidesInTime {N : FinNDTM Bool} {L : Language Bool} {T : ℕ → ℕ}
    (h : N.RDecidesInTime L T) : N.BPDecidesInTime L T := by
  classical
  intro x
  obtain ⟨hhalt, hin, hout⟩ := h x
  refine ⟨hhalt, ?_⟩
  by_cases hx : x ∈ L
  · simpa only [MultiTapeTM.indicator, hx, if_true] using hin hx
  · have hone : N.outputProb x (T x.length) [false] = 1 := outputProb_eq_one (hout hx)
    simp only [MultiTapeTM.indicator, hx, if_false, hone]
    norm_num

/-- The negated machine has the same halting behaviour. -/
theorem flipOutput_haltsWithin_iff (N : FinNDTM Bool) (x : List Bool) (t : ℕ) :
    N.flipOutput.tm.HaltsWithin x t ↔ N.tm.HaltsWithin x t := by
  show (∀ w : List Bool, w.length = t →
      (N.tm.flipOutput.runWith w (N.tm.flipOutput.initCfg x)).state = none) ↔ _
  simp only [NDTM.flipOutput_initCfg, NDTM.flipOutput_runWith]
  rfl

/-- The negated machine's output is the bitwise negation of the original output. -/
theorem flipOutput_outputWith (N : FinNDTM Bool) (x w : List Bool) :
    N.flipOutput.outputWith x w = (N.outputWith x w).map not := by
  show (N.tm.flipOutput.runWith w (N.tm.flipOutput.initCfg x)).output = _
  rw [NDTM.flipOutput_initCfg, NDTM.flipOutput_runWith]
  rfl

/-- Negating the output turns a bounded-error decider for `L` into one for `Lᶜ`.
[AB09, p. 136: "`BPP = coBPP`"]

**Proof sketch.** Halting is unchanged, and the negated output equals `[Lᶜ(x)]` exactly when
the original equals `[L(x)]` (bitwise negation is injective), so the two events coincide. -/
theorem BPDecidesInTime.flipOutput {N : FinNDTM Bool} {L : Language Bool} {T : ℕ → ℕ}
    (h : N.BPDecidesInTime L T) : N.flipOutput.BPDecidesInTime Lᶜ T := by
  classical
  intro x
  obtain ⟨hhalt, hprob⟩ := h x
  refine ⟨(N.flipOutput_haltsWithin_iff x _).mpr hhalt, ?_⟩
  have hind : [MultiTapeTM.indicator ((Lᶜ : Language Bool) : Set (List Bool)) x] =
      [MultiTapeTM.indicator (L : Set (List Bool)) x].map not := by
    by_cases hx : x ∈ L
    · have hxc : x ∉ (Lᶜ : Language Bool) := fun h => h hx
      simp [MultiTapeTM.indicator, hx, hxc]
    · have hxc : x ∈ (Lᶜ : Language Bool) := hx
      simp [MultiTapeTM.indicator, hx, hxc]
  unfold outputProb at hprob ⊢
  rw [Randomized.randProb_congr (B := fun w =>
    N.outputWith x w = [MultiTapeTM.indicator (L : Set (List Bool)) x]) fun r => by
      rw [flipOutput_outputWith, hind]
      exact (List.map_injective_iff.mpr fun a b hab => by
        cases a <;> cases b <;> simp_all).eq_iff]
  exact hprob

end FinNDTM

end Turing

namespace Randomized

open Turing

/-- `BPTIME(T)`: the languages decided with bounded error by some PTM in time `c · T` for a
constant `c`. [AB09, Def 7.2] -/
def BPTIME (T : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (N : FinNDTM Bool), N.BPDecidesInTime L fun n => c * T n}

/-- `BPP = ⋃_c BPTIME(n^c + 1)`, the PTM form of bounded-error probabilistic polynomial time.
[AB09, Def 7.2] -/
def BPP_PTM : Set (Language Bool) := ⋃ c : ℕ, BPTIME fun n => n ^ c + 1

/-- `RTIME(T)`: the languages decided with one-sided error by some PTM in time `c · T` for a
constant `c`. [AB09, Def 7.6] -/
def RTIME (T : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (N : FinNDTM Bool), N.RDecidesInTime L fun n => c * T n}

/-- `RP = ⋃_c RTIME(n^c + 1)`. [AB09, Def 7.6] -/
def RP_PTM : Set (Language Bool) := ⋃ c : ℕ, RTIME fun n => n ^ c + 1

/-- `coRP = {L | Lᶜ ∈ RP}`. [AB09, §7.3] -/
def coRP_PTM : Set (Language Bool) := {L | Lᶜ ∈ RP_PTM}

/-- `BPTIME` is monotone in the time bound. -/
theorem BPTIME.mono {T₁ T₂ : ℕ → ℕ} (h : ∀ n, T₁ n ≤ T₂ n) : BPTIME T₁ ⊆ BPTIME T₂ := by
  rintro L ⟨c, N, hN⟩
  exact ⟨c, N, hN.mono fun n => Nat.mul_le_mul_left c (h n)⟩

/-- `RTIME` is monotone in the time bound. -/
theorem RTIME.mono {T₁ T₂ : ℕ → ℕ} (h : ∀ n, T₁ n ≤ T₂ n) : RTIME T₁ ⊆ RTIME T₂ := by
  rintro L ⟨c, N, hN⟩
  exact ⟨c, N, hN.mono fun n => Nat.mul_le_mul_left c (h n)⟩

/-- Constant factors are absorbed: `BPTIME(a · T) ⊆ BPTIME(T)`. -/
theorem BPTIME_const_mul_subset (a : ℕ) (T : ℕ → ℕ) :
    BPTIME (fun n => a * T n) ⊆ BPTIME T := by
  rintro L ⟨c, N, hN⟩
  exact ⟨c * a, N, by simpa only [Nat.mul_assoc] using hN⟩

/-- Constant factors are absorbed: `RTIME(a · T) ⊆ RTIME(T)`. -/
theorem RTIME_const_mul_subset (a : ℕ) (T : ℕ → ℕ) :
    RTIME (fun n => a * T n) ⊆ RTIME T := by
  rintro L ⟨c, N, hN⟩
  exact ⟨c * a, N, by simpa only [Nat.mul_assoc] using hN⟩

/-- `RTIME(T) ⊆ BPTIME(T)`. [AB09, §7.3] -/
theorem RTIME_subset_BPTIME (T : ℕ → ℕ) : RTIME T ⊆ BPTIME T := by
  rintro L ⟨c, N, hN⟩
  exact ⟨c, N, hN.bpDecidesInTime⟩

/-- `BPTIME(T)` is closed under complement. -/
theorem compl_mem_BPTIME {T : ℕ → ℕ} {L : Language Bool} (h : L ∈ BPTIME T) :
    Lᶜ ∈ BPTIME T := by
  obtain ⟨c, N, hN⟩ := h
  exact ⟨c, N.flipOutput, hN.flipOutput⟩

/-- `BPP` (PTM form) is closed under complement. [AB09, p. 136] -/
theorem compl_mem_BPP_PTM {L : Language Bool} (h : L ∈ BPP_PTM) : Lᶜ ∈ BPP_PTM := by
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp h
  exact Set.mem_iUnion.mpr ⟨c, compl_mem_BPTIME hc⟩

end Randomized
