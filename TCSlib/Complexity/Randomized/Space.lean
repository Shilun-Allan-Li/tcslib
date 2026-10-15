/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.SpaceAmplifyRun
import Mathlib.Algebra.Order.Archimedean.Basic
import TCSlib.Complexity.SpaceComplexity.ExpTime

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Randomized space-bounded computation: BPL and RL

[AB09, §7.7]: a probabilistic Turing machine uses space `S(n)` if on every branch of its
computation on a length-`n` input it uses `O(S(n))` work-tape cells; `BPL` and `RL` are the
two-sided and one-sided error classes of logarithmic space. The PTM is a
`Turing.FinNDTM Bool` as in `TCSlib.Complexity.Randomized.PTM`; its coins are the choice word,
one coin per step, never written on a tape. The coins are therefore *read-once* in the sense
of [AB09, §7.7]: re-reading a coin requires storing it on a work tape, which is charged.

## Main definitions

* `Turing.FinNDTM.UsesSpace` — every branch uses at most `s(|x|)` work cells. [AB09, §7.7]
* `Turing.FinNDTM.BPDecidesInSpace`, `Randomized.BPSPACE`, `Randomized.BPL` — [AB09, Def 7.18].
* `Turing.FinNDTM.RDecidesInSpace`, `Randomized.RSPACE`, `Randomized.RL` — [AB09, Def 7.18].

## Main results

* `Turing.FinNDTM.usesSpace_of_haltsWithin` — the exact-length space bound of
  `Turing.FinNDTM.DecidesInSpace` (and of `Complexity.LogProg.narm_space_randProb`) bounds
  every branch.
* `Randomized.RL_subset_BPL`, `Randomized.RL_subset_NL`, `Randomized.RL_subset_P`,
  `Randomized.LOGSPACE_subset_RL`, `Randomized.LOGSPACE_subset_BPL` — [AB09, p. 139].
* `Randomized.compl_mem_BPL` — `BPL` is closed under complement.
* `Randomized.exists_rDecides_of_pos`, `Randomized.exists_bpDecides_of_advantage`,
  `Randomized.mem_RSPACE_of_pos`, `Randomized.mem_BPSPACE_of_advantage` — error reduction
  with constant space overhead: the constant `2/3` of [AB09, Def 7.18] may be any `δ > 0`
  (one-sided) or `1/2 + δ` (two-sided), and the error made any constant `ε > 0`
  [AB09, p. 139], by repetition and majority (`Randomized.Amplify.amp`).

## Divergences

* [AB09, Def 7.18] does not state a running time. The probability `Pr[M(x) = L(x)]` is over
  the coins of a PTM that halts on every branch ([AB09, Def 7.1]); we require, as for
  `Complexity.NSPACE` (convention CH34-Q7), that for every input `x` some `T` exists by which
  every branch has halted, and the probability is taken over coin words of length `T` (by
  `Turing.FinNDTM.outputProb_eq_of_haltsWithin` any larger `T` gives the same value). With
  logarithmic space this forces polynomial time (a halting branch repeats no configuration):
  `Randomized.BPLInP.haltsWithin_of_codes` (`TCSlib.Complexity.Randomized.BPLInPCount`).
* Space counts *visited* work cells, as for `Complexity.NSPACE`; [AB09, §7.7] says "nonblank".
* Output and one-sided conventions are those of `Turing.FinNDTM.BPDecidesInTime` and
  `Turing.FinNDTM.RDecidesInTime`; constants are absorbed as `c · s n`; `logSpace` is
  `⌊log₂ n⌋ + 1`.
* Error reduction here is for a constant number of repetitions, which is what the book's
  conclusion ("the choice of the precise constant is not significant") needs. Repeating
  polynomially often, for error `2^{-n^d}`, is `Randomized.BPL_error_reduction` and
  `Randomized.RL_error_reduction` (`TCSlib.Complexity.Randomized.SpaceAmplifyPoly`);
  [AB09, Exercise 7.9] (`BPL ⊆ P`) is `Randomized.BPL_subset_P`
  (`TCSlib.Complexity.Randomized.BPLInP`).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Turing

namespace NDTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- Extending a choice word only adds visited cells. -/
theorem spaceUsedWith_le_append (tm : NDTM k Symbol State) (w w' : List Bool)
    (cfg : Cfg k Symbol State input) :
    tm.spaceUsedWith w cfg ≤ tm.spaceUsedWith (w ++ w') cfg := by
  refine Finset.sum_le_sum fun i _ => Finset.card_le_card fun p hp => ?_
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
  have hjle : j ≤ w.length := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  refine Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr ?_, ?_⟩
  · simp only [List.length_append]
    omega
  · rw [List.take_append_of_le_length hjle]

/-- `flipOutput` moves the heads exactly as the original machine. -/
theorem flipOutput_spaceUsedWith {x : List Bool} (tm : NDTM k Bool State) (w : List Bool)
    (cfg : Cfg k Bool State x) :
    tm.flipOutput.spaceUsedWith w (flipCfg cfg) = tm.spaceUsedWith w cfg := by
  unfold spaceUsedWith visitedWith
  simp only [flipOutput_runWith]
  rfl

end NDTM

namespace FinNDTM

/-- The PTM `N` *uses space* `s`: on every input `x`, every branch (a coin word of any
length) visits at most `s(|x|)` work-tape cells. [AB09, §7.7] -/
def UsesSpace (N : FinNDTM Bool) (s : ℕ → ℕ) : Prop :=
  ∀ x w : List Bool, N.tm.spaceUsedWith w (N.tm.initCfg x) ≤ s x.length

/-- The PTM `N` decides `L` in space `s` with bounded error: it uses space `s`, and on every
input `x` there is a `T` by which every branch has halted with `Pr[M(x) = L(x)] ≥ 2/3` over
`T` coins. [AB09, Def 7.18] -/
def BPDecidesInSpace (N : FinNDTM Bool) (L : Language Bool) (s : ℕ → ℕ) : Prop :=
  N.UsesSpace s ∧ ∀ x : List Bool, ∃ T : ℕ, N.tm.HaltsWithin x T ∧
    2/3 ≤ N.outputProb x T [MultiTapeTM.indicator (L : Set (List Bool)) x]

/-- The PTM `N` decides `L` in space `s` with one-sided error: it uses space `s`, and on every
input `x` there is a `T` by which every branch has halted, members are accepted with
probability at least `2/3`, and on non-members every branch outputs `0`. [AB09, Def 7.18] -/
def RDecidesInSpace (N : FinNDTM Bool) (L : Language Bool) (s : ℕ → ℕ) : Prop :=
  N.UsesSpace s ∧ ∀ x : List Bool, ∃ T : ℕ, N.tm.HaltsWithin x T ∧
    (x ∈ L → 2/3 ≤ N.outputProb x T [true]) ∧
    (x ∉ L → ∀ w : List Bool, w.length = T → N.outputWith x w = [false])

/-- A space bound can be weakened. -/
theorem UsesSpace.mono {N : FinNDTM Bool} {s s' : ℕ → ℕ} (h : N.UsesSpace s)
    (hs : ∀ n, s n ≤ s' n) : N.UsesSpace s' :=
  fun x w => (h x w).trans (hs _)

/-- **Bounding the branches of one length bounds every branch**: if every branch of length
`T` has halted on `x` and visited at most `S` cells, then every branch visits at most `S`
cells.

**Proof sketch.** A shorter word extends to length `T` (`NDTM.spaceUsedWith_le_append`); a longer
word is its length-`T` prefix followed by bits read after halting
(`NDTM.spaceUsedWith_append_of_halt`). -/
theorem spaceUsedWith_le_of_haltsWithin {N : FinNDTM Bool} {x : List Bool} {T S : ℕ}
    (hT : N.tm.HaltsWithin x T)
    (hS : ∀ w : List Bool, w.length = T → N.tm.spaceUsedWith w (N.tm.initCfg x) ≤ S)
    (w : List Bool) : N.tm.spaceUsedWith w (N.tm.initCfg x) ≤ S := by
  by_cases hw : w.length ≤ T
  · refine (N.tm.spaceUsedWith_le_append w (List.replicate (T - w.length) false) _).trans ?_
    exact hS _ (by simp only [List.length_append, List.length_replicate]; omega)
  · have hlen : (w.take T).length = T := List.length_take_of_le (by omega)
    rw [← List.take_append_drop T w,
      NDTM.spaceUsedWith_append_of_halt _ (hT _ hlen) (w.drop T)]
    exact hS _ hlen

/-- The exact-length space clause of `DecidesInSpace` and of the compiled register machines
gives `UsesSpace`. -/
theorem usesSpace_of_haltsWithin {N : FinNDTM Bool} {s : ℕ → ℕ}
    (h : ∀ x : List Bool, ∃ T, N.tm.HaltsWithin x T ∧
      ∀ w : List Bool, w.length = T → N.tm.spaceUsedWith w (N.tm.initCfg x) ≤ s x.length) :
    N.UsesSpace s := by
  intro x w
  obtain ⟨T, hT, hS⟩ := h x
  exact spaceUsedWith_le_of_haltsWithin hT hS w

/-- Bounded-error space deciding is monotone in the space bound. -/
theorem BPDecidesInSpace.mono {N : FinNDTM Bool} {L : Language Bool} {s s' : ℕ → ℕ}
    (h : N.BPDecidesInSpace L s) (hs : ∀ n, s n ≤ s' n) : N.BPDecidesInSpace L s' :=
  ⟨h.1.mono hs, h.2⟩

/-- One-sided-error space deciding is monotone in the space bound. -/
theorem RDecidesInSpace.mono {N : FinNDTM Bool} {L : Language Bool} {s s' : ℕ → ℕ}
    (h : N.RDecidesInSpace L s) (hs : ∀ n, s n ≤ s' n) : N.RDecidesInSpace L s' :=
  ⟨h.1.mono hs, h.2⟩

/-- A one-sided-error space decider is a bounded-error one. [AB09, p. 139] -/
theorem RDecidesInSpace.bpDecidesInSpace {N : FinNDTM Bool} {L : Language Bool} {s : ℕ → ℕ}
    (h : N.RDecidesInSpace L s) : N.BPDecidesInSpace L s := by
  classical
  refine ⟨h.1, fun x => ?_⟩
  obtain ⟨T, hT, hin, hout⟩ := h.2 x
  refine ⟨T, hT, ?_⟩
  by_cases hx : x ∈ L
  · simpa only [MultiTapeTM.indicator, hx, if_true] using hin hx
  · have hone : N.outputProb x T [false] = 1 := outputProb_eq_one (hout hx)
    simp only [MultiTapeTM.indicator, hx, if_false, hone]
    norm_num

/-- A one-sided-error space decider is a nondeterministic space decider: a positive
acceptance probability gives an accepting branch. [AB09, p. 139: "`RL ⊆ NL`"] -/
theorem RDecidesInSpace.decidesInSpace {N : FinNDTM Bool} {L : Language Bool} {s : ℕ → ℕ}
    (h : N.RDecidesInSpace L s) : N.DecidesInSpace L s := by
  intro x
  obtain ⟨T, hT, hin, hout⟩ := h.2 x
  refine ⟨T, hT, fun w _ => h.1 x w, fun hx => ?_, fun ⟨w, hw, _, hacc⟩ => ?_⟩
  · obtain ⟨w, hw, hwout⟩ :=
      exists_outputWith_of_outputProb_pos (lt_of_lt_of_le (by norm_num) (hin hx))
    exact ⟨w, hw, hT w hw, hwout⟩
  · by_contra hx
    have hf : N.outputWith x w = [false] := hout hx w hw
    exact absurd (hf.symm.trans hacc) (by decide)

/-- Negating the output turns a bounded-error space decider for `L` into one for `Lᶜ`.

**Proof sketch.** Negation does not move the heads (`NDTM.flipOutput_spaceUsedWith`) nor change
halting (`flipOutput_haltsWithin_iff`); a branch outputs `[L(x)]` iff the negated branch outputs the
negated word, which is `[Lᶜ(x)]` (`flipOutput_outputWith`, injectivity of `map not`). -/
theorem BPDecidesInSpace.flipOutput {N : FinNDTM Bool} {L : Language Bool} {s : ℕ → ℕ}
    (h : N.BPDecidesInSpace L s) : N.flipOutput.BPDecidesInSpace Lᶜ s := by
  refine ⟨fun x w => ?_, fun x => ?_⟩
  · show N.tm.flipOutput.spaceUsedWith w (N.tm.flipOutput.initCfg x) ≤ _
    rw [NDTM.flipOutput_initCfg, NDTM.flipOutput_spaceUsedWith]
    exact h.1 x w
  · classical
    obtain ⟨T, hT, hp⟩ := h.2 x
    refine ⟨T, (N.flipOutput_haltsWithin_iff x _).mpr hT, ?_⟩
    have hind : [MultiTapeTM.indicator ((Lᶜ : Language Bool) : Set (List Bool)) x] =
        [MultiTapeTM.indicator (L : Set (List Bool)) x].map not := by
      by_cases hx : x ∈ L
      · have hxc : x ∉ (Lᶜ : Language Bool) := fun h => h hx
        simp [MultiTapeTM.indicator, hx, hxc]
      · have hxc : x ∈ (Lᶜ : Language Bool) := hx
        simp [MultiTapeTM.indicator, hx, hxc]
    unfold outputProb at hp ⊢
    rw [Randomized.randProb_congr (B := fun w =>
      N.outputWith x w = [MultiTapeTM.indicator (L : Set (List Bool)) x]) fun r => by
        rw [flipOutput_outputWith, hind]
        exact (List.map_injective_iff.mpr fun a b hab => by
          cases a <;> cases b <;> simp_all).eq_iff]
    exact hp

end FinNDTM

end Turing

namespace Randomized

open Complexity Turing

/-- `BPSPACE(s)`: the languages decided with bounded error by some PTM in space `c · s` for a
constant `c`. [AB09, Def 7.18, for general `S`] -/
def BPSPACE (s : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (N : FinNDTM Bool), N.BPDecidesInSpace L fun n => c * s n}

/-- `BPL = BPSPACE(log n)`. [AB09, Def 7.18] -/
def BPL : Set (Language Bool) := BPSPACE logSpace

/-- `RSPACE(s)`: the languages decided with one-sided error by some PTM in space `c · s` for a
constant `c`. [AB09, Def 7.18, for general `S`] -/
def RSPACE (s : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (N : FinNDTM Bool), N.RDecidesInSpace L fun n => c * s n}

/-- `RL = RSPACE(log n)`. [AB09, Def 7.18] -/
def RL : Set (Language Bool) := RSPACE logSpace

/-- `BPSPACE` is monotone in the space bound. -/
theorem BPSPACE.mono {s₁ s₂ : ℕ → ℕ} (h : ∀ n, s₁ n ≤ s₂ n) : BPSPACE s₁ ⊆ BPSPACE s₂ := by
  rintro L ⟨c, N, hN⟩
  exact ⟨c, N, hN.mono fun n => Nat.mul_le_mul_left c (h n)⟩

/-- `RSPACE` is monotone in the space bound. -/
theorem RSPACE.mono {s₁ s₂ : ℕ → ℕ} (h : ∀ n, s₁ n ≤ s₂ n) : RSPACE s₁ ⊆ RSPACE s₂ := by
  rintro L ⟨c, N, hN⟩
  exact ⟨c, N, hN.mono fun n => Nat.mul_le_mul_left c (h n)⟩

/-- `RSPACE(s) ⊆ BPSPACE(s)`. -/
theorem RSPACE_subset_BPSPACE (s : ℕ → ℕ) : RSPACE s ⊆ BPSPACE s := by
  rintro L ⟨c, N, hN⟩
  exact ⟨c, N, hN.bpDecidesInSpace⟩

/-- `RL ⊆ BPL`. [AB09, §7.7] -/
theorem RL_subset_BPL : RL ⊆ BPL := RSPACE_subset_BPSPACE logSpace

/-- `RSPACE(s) ⊆ NSPACE(s)`. -/
theorem RSPACE_subset_NSPACE (s : ℕ → ℕ) : RSPACE s ⊆ NSPACE s := by
  rintro L ⟨c, N, hN⟩
  exact ⟨c, N, hN.decidesInSpace⟩

/-- **`RL ⊆ NL`**. [AB09, p. 139] -/
theorem RL_subset_NL : RL ⊆ NL := RSPACE_subset_NSPACE logSpace

/-- **`RL ⊆ P`**, through `NL ⊆ P`. [AB09, p. 139] -/
theorem RL_subset_P : RL ⊆ P := RL_subset_NL.trans NL_subset_P

/-- `SPACE(s) ⊆ RSPACE(s)`: a deterministic machine is a PTM whose two transition functions
coincide, and its unique outcome is correct with probability `1`.

**Proof sketch.** Embed the deterministic decider as `M.toFinNDTM`: every branch is the
deterministic run (`MultiTapeTM.toNDTM_runWith`), so it halts at the deterministic halting time,
uses the deterministic space (`MultiTapeTM.toNDTM_spaceUsedWith`, then `usesSpace_of_haltsWithin`),
and outputs `[x ∈ L]` on every branch; hence members are accepted with probability `1`
(`outputProb_eq_one`). -/
theorem SPACE_subset_RSPACE (s : ℕ → ℕ) : SPACE s ⊆ RSPACE s := by
  classical
  rintro L ⟨c, M, hM⟩
  have hrun : ∀ (x w : List Bool), M.toFinNDTM.tm.runWith w (M.toFinNDTM.tm.initCfg x) =
      M.tm.runFrom (M.tm.initCfg x) w.length := fun x w =>
    M.tm.toNDTM_runWith w (M.tm.initCfg x)
  refine ⟨c, M.toFinNDTM, FinNDTM.usesSpace_of_haltsWithin fun x => ?_, fun x => ?_⟩
  · obtain ⟨t, hcomp, hsp⟩ := hM x
    obtain ⟨hhalt, -⟩ := (M.computesInTime_iff _ _ _).mp hcomp
    refine ⟨t, fun w hw => by rw [hrun, hw]; exact hhalt, fun w hw => ?_⟩
    change M.tm.toNDTM.spaceUsedWith w (M.tm.initCfg x) ≤ c * s x.length
    rw [M.tm.toNDTM_spaceUsedWith, hw]
    exact hsp
  · obtain ⟨t, hcomp, -⟩ := hM x
    obtain ⟨hhalt, hout⟩ := (M.computesInTime_iff _ _ _).mp hcomp
    have hw : ∀ w : List Bool, w.length = t →
        M.toFinNDTM.outputWith x w = [MultiTapeTM.indicator (L : Set (List Bool)) x] :=
      fun w hw => by rw [FinNDTM.outputWith, hrun, hw]; exact hout
    refine ⟨t, fun w hw => by rw [hrun, hw]; exact hhalt, fun hx => ?_, fun hx w hlen => ?_⟩
    · rw [FinNDTM.outputProb_eq_one (v := [true]) fun w hlen => by
        rw [hw w hlen]; simp [MultiTapeTM.indicator, hx]]
      norm_num
    · rw [hw w hlen]; simp [MultiTapeTM.indicator, hx]

/-- **`L ⊆ RL`**. [AB09, §7.7] -/
theorem LOGSPACE_subset_RL : LOGSPACE ⊆ RL := SPACE_subset_RSPACE logSpace

/-- **`L ⊆ BPL`**. [AB09, §7.7] -/
theorem LOGSPACE_subset_BPL : LOGSPACE ⊆ BPL := LOGSPACE_subset_RL.trans RL_subset_BPL

/-- `BPSPACE(s)` is closed under complement. -/
theorem compl_mem_BPSPACE {s : ℕ → ℕ} {L : Language Bool} (h : L ∈ BPSPACE s) :
    Lᶜ ∈ BPSPACE s := by
  obtain ⟨c, N, hN⟩ := h
  exact ⟨c, N.flipOutput, hN.flipOutput⟩

/-- `BPL` is closed under complement. -/
theorem compl_mem_BPL {L : Language Bool} (h : L ∈ BPL) : Lᶜ ∈ BPL := compl_mem_BPSPACE h

/-! ### Error reduction -/

/-- An event of probability `1` holds of every random string. -/
theorem forall_of_randProb_eq_one {m : ℕ} {A : List Bool → Prop} [DecidablePred A]
    (h : randProb m A = 1) (r : Fin m → Bool) : A (List.ofFn r) := by
  by_contra hr
  have h0 : randProb m (fun l => ¬ A l) = 0 := by rw [randProb_not, h]; ring
  unfold randProb at h0
  rcases div_eq_zero_iff.mp h0 with h0 | h0
  · have hmem : r ∈ Finset.univ.filter (fun r : Fin m → Bool => ¬ A (List.ofFn r)) := by
      simp [hr]
    rw [Nat.cast_eq_zero, Finset.card_eq_zero] at h0
    rw [h0] at hmem
    simp at hmem
  · exact absurd h0 (by positivity)

/-- A machine using space `s` has at most `s n` work tapes: the empty branch visits one cell
on each. -/
theorem _root_.Turing.FinNDTM.UsesSpace.k_le {N : FinNDTM Bool} {s : ℕ → ℕ} (h : N.UsesSpace s)
    (n : ℕ) : N.k ≤ s n := by
  have := h (List.replicate n false) []
  simpa [NDTM.spaceUsedWith] using this

/-- The repeated machine uses space `3 (r + 1) k · s`. -/
theorem amp_usesSpace_mul {N : FinNDTM Bool} {s : ℕ → ℕ} (hN : N.UsesSpace s) (r : ℕ)
    (dec : ℕ → Bool) : (Amplify.amp N r dec).UsesSpace fun n => 3 * (r + 1) * N.k * s n := by
  refine FinNDTM.UsesSpace.mono (s := fun n => (r + 1) * N.k * (2 * s n + 1))
    (fun x w => Amplify.amp_usesSpace hN x w) fun n => ?_
  have hk := hN.k_le n
  rcases Nat.eq_zero_or_pos N.k with h0 | hpos
  · simp [h0]
  · have : 2 * s n + 1 ≤ 3 * s n := by omega
    calc (r + 1) * N.k * (2 * s n + 1) ≤ (r + 1) * N.k * (3 * s n) :=
          Nat.mul_le_mul_left _ this
      _ = 3 * (r + 1) * N.k * s n := by ring

/-- **Error reduction for one-sided error in space** [AB09, p. 139]: a space-`s` PTM that
accepts members with probability at least `δ > 0` and never accepts non-members is repeated
into a space-`O(s)` PTM that accepts members with probability at least `1 - ε`.

**Proof sketch.** Run `N` `n + 1` times (`Amplify.amp`) and accept iff some run accepted. The
runs are independent blocks (`Amplify.amp_outputProb`), so a member is rejected with
probability `(1 - p)^{n+1} ≤ (1 - δ)^{n+1} < ε` for `n` large (`randProb_blockCount`); a
non-member has acceptance probability `0` in every run, so every branch rejects. -/
theorem exists_rDecides_of_pos {N : FinNDTM Bool} {L : Language Bool} {s : ℕ → ℕ} {δ ε : ℚ}
    (hδ : 0 < δ) (hε : 0 < ε) (hN : N.UsesSpace s)
    (h : ∀ x : List Bool, ∃ T, N.tm.HaltsWithin x T ∧ (x ∈ L → δ ≤ N.outputProb x T [true]) ∧
      (x ∉ L → ∀ w : List Bool, w.length = T → N.outputWith x w = [false])) :
    ∃ (a : ℕ) (N' : FinNDTM Bool), N'.UsesSpace (fun n => a * s n) ∧
      ∀ x : List Bool, ∃ T, N'.tm.HaltsWithin x T ∧
        (x ∈ L → 1 - ε ≤ N'.outputProb x T [true]) ∧
        (x ∉ L → ∀ w : List Bool, w.length = T → N'.outputWith x w = [false]) := by
  set d := min δ 1 with hd
  have hd0 : 0 < d := lt_min hδ one_pos
  have hd1 : d ≤ 1 := min_le_right _ _
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (show 1 - d < 1 by linarith)
  refine ⟨3 * (n + 1) * N.k, Amplify.amp N n (fun m => decide (1 ≤ m)), amp_usesSpace_mul hN n _,
    fun x => ?_⟩
  obtain ⟨T, hT, hin, hout⟩ := h x
  have hp : randProb T (fun l => Amplify.acc N x l = true) = N.outputProb x T [true] :=
    randProb_congr fun r => by simp [Amplify.acc, FinNDTM.outputWith]
  have hzero := randProb_blockCount T (Amplify.acc N x) (n + 1) 0 (Nat.zero_le _)
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, Nat.sub_zero] at hzero
  have hev : ∀ v : Bool, randProb ((n + 1) * T)
      (fun l => decide (1 ≤ blockCount T (n + 1) (Amplify.acc N x) l) = v) =
      if v then 1 - randProb ((n + 1) * T) (fun l => blockCount T (n + 1) (Amplify.acc N x) l = 0)
      else randProb ((n + 1) * T) (fun l => blockCount T (n + 1) (Amplify.acc N x) l = 0) := by
    intro v
    cases v
    · rw [if_neg (by simp)]
      exact randProb_congr fun r => by simp
    · rw [if_pos rfl, ← randProb_not]
      exact randProb_congr fun r => by simp; omega
  refine ⟨_, Amplify.amp_haltsWithin hT, fun hx => ?_, fun hx w hw => ?_⟩
  · rw [Amplify.amp_outputProb hT, hev, if_pos rfl, hzero, hp]
    have hle : N.outputProb x T [true] ≤ 1 := randProb_le_one
    have h1 : (1 - N.outputProb x T [true]) ^ (n + 1) ≤ (1 - d) ^ (n + 1) :=
      pow_le_pow_left₀ (by linarith) (by linarith [hin hx, min_le_left δ 1]) _
    have h2 : (1 - d) ^ (n + 1) ≤ (1 - d) ^ n :=
      pow_le_pow_of_le_one (by linarith) (by linarith) (Nat.le_succ n)
    linarith
  · have hp0 : randProb T (fun l => Amplify.acc N x l = true) = 0 := by
      rw [← randProb_false (m := T)]
      refine randProb_congr fun r => ?_
      simp [Amplify.acc, hout hx _ (List.length_ofFn)]
    have h1 := Amplify.amp_outputProb (r := n) (dec := fun m => decide (1 ≤ m)) hT false
    rw [hev, if_neg (by simp), hzero, hp0] at h1
    simp only [sub_zero, one_pow] at h1
    obtain ⟨r, rfl⟩ := exists_ofFn_eq hw
    exact forall_of_randProb_eq_one h1 r

/-- **Error reduction for bounded error in space** [AB09, p. 139]: a space-`s` PTM that is
correct with probability at least `1/2 + δ` is repeated into a space-`O(s)` PTM that is correct
with probability at least `1 - ε`.

**Proof sketch.** Run `N` `2n + 1` times (`Amplify.amp`) and accept iff more than half of the
runs accepted. The runs are independent blocks (`Amplify.amp_outputProb`). The majority is
wrong only if at least half of the blocks err, and each block errs with probability at most
`1/2 - δ` (for a non-member, accepting and outputting `[false]` are disjoint), so the
Chernoff-type bound `randProb_tail_le` gives error at most `2 (1 - 4δ²)^n < ε` for `n` large;
the failing blocks are counted by `blockCount_add_not`. -/
theorem exists_bpDecides_of_advantage {N : FinNDTM Bool} {L : Language Bool} {s : ℕ → ℕ}
    {δ ε : ℚ} (hδ : 0 < δ) (hε : 0 < ε) (hN : N.UsesSpace s)
    (h : ∀ x : List Bool, ∃ T, N.tm.HaltsWithin x T ∧
      1/2 + δ ≤ N.outputProb x T [MultiTapeTM.indicator (L : Set (List Bool)) x]) :
    ∃ (a : ℕ) (N' : FinNDTM Bool), N'.UsesSpace (fun n => a * s n) ∧
      ∀ x : List Bool, ∃ T, N'.tm.HaltsWithin x T ∧
        1 - ε ≤ N'.outputProb x T [MultiTapeTM.indicator (L : Set (List Bool)) x] := by
  classical
  set d := min δ (1/4) with hd
  have hd0 : 0 < d := lt_min hδ (by norm_num)
  have hd4 : d ≤ 1/4 := min_le_right _ _
  have hdδ : d ≤ δ := min_le_left _ _
  have hq1 : 1 - 4 * d ^ 2 < 1 := by nlinarith
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (half_pos hε) hq1
  set dec : ℕ → Bool := fun m => decide (2 * n + 1 < 2 * m) with hdec
  refine ⟨3 * (2 * n + 1) * N.k, Amplify.amp N (2 * n) dec, amp_usesSpace_mul hN (2 * n) dec,
    fun x => ?_⟩
  obtain ⟨T, hT, hp⟩ := h x
  refine ⟨_, Amplify.amp_haltsWithin hT, ?_⟩
  rw [Amplify.amp_outputProb hT]
  have tail : ∀ B : List Bool → Bool, randProb T (fun l => B l = true) ≤ 1/2 - d →
      randProb ((2 * n + 1) * T) (fun l => 2 * n + 1 ≤ 2 * blockCount T (2 * n + 1) B l) < ε := by
    intro B hB
    have := randProb_tail_le T (2 * n + 1) B hd0.le hB
    rw [show (2 * n + 1) / 2 = n by omega] at this
    linarith
  have hpt : randProb T (fun l => Amplify.acc N x l = true) = N.outputProb x T [true] :=
    randProb_congr fun r => by simp [Amplify.acc, FinNDTM.outputWith]
  by_cases hx : x ∈ L
  · simp only [MultiTapeTM.indicator, hx, if_true] at hp ⊢
    have hB : randProb T (fun l => (fun l => !Amplify.acc N x l) l = true) ≤ 1/2 - d := by
      have e : randProb T (fun l => (fun l => !Amplify.acc N x l) l = true) =
          randProb T (fun l => Amplify.acc N x l = false) := randProb_congr fun r => by simp
      rw [e, randProb_bool_false, hpt]
      linarith
    have hmono : randProb ((2 * n + 1) * T)
        (fun l => ¬ dec (blockCount T (2 * n + 1) (Amplify.acc N x) l) = true) ≤
        randProb ((2 * n + 1) * T) (fun l => 2 * n + 1 ≤
          2 * blockCount T (2 * n + 1) (fun l => !Amplify.acc N x l) l) :=
      randProb_mono fun r hr => by
        have := blockCount_add_not T (2 * n + 1) (Amplify.acc N x) (List.ofFn r)
        simp only [hdec, decide_eq_true_eq, not_lt] at hr
        omega
    have hnot := randProb_not (m := (2 * n + 1) * T)
      (fun l => dec (blockCount T (2 * n + 1) (Amplify.acc N x) l) = true)
    linarith [tail _ hB]
  · simp only [MultiTapeTM.indicator, hx, if_false] at hp ⊢
    have hsum : N.outputProb x T [true] + N.outputProb x T [false] ≤ 1 := by
      unfold FinNDTM.outputProb
      rw [← randProb_or_disjoint _ _ fun r h => by
        have := h.1.symm.trans h.2
        simp at this]
      exact randProb_le_one
    have hB : randProb T (fun l => Amplify.acc N x l = true) ≤ 1/2 - d := by
      rw [hpt]
      linarith
    have hmono : randProb ((2 * n + 1) * T)
        (fun l => ¬ dec (blockCount T (2 * n + 1) (Amplify.acc N x) l) = false) ≤
        randProb ((2 * n + 1) * T)
          (fun l => 2 * n + 1 ≤ 2 * blockCount T (2 * n + 1) (Amplify.acc N x) l) :=
      randProb_mono fun r hr => by
        simp only [hdec, decide_eq_false_iff_not, not_not] at hr
        omega
    have hnot := randProb_not (m := (2 * n + 1) * T)
      (fun l => dec (blockCount T (2 * n + 1) (Amplify.acc N x) l) = false)
    linarith [tail _ hB]

/-- The constant `2/3` in `RSPACE` may be any `δ > 0`. [AB09, p. 139] -/
theorem mem_RSPACE_of_pos {N : FinNDTM Bool} {L : Language Bool} {s : ℕ → ℕ} {c : ℕ} {δ : ℚ}
    (hδ : 0 < δ) (hN : N.UsesSpace fun n => c * s n)
    (h : ∀ x : List Bool, ∃ T, N.tm.HaltsWithin x T ∧ (x ∈ L → δ ≤ N.outputProb x T [true]) ∧
      (x ∉ L → ∀ w : List Bool, w.length = T → N.outputWith x w = [false])) :
    L ∈ RSPACE s := by
  obtain ⟨a, N', hs, h'⟩ := exists_rDecides_of_pos hδ (show (0 : ℚ) < 1/3 by norm_num) hN h
  refine ⟨a * c, N', hs.mono fun n => (Nat.mul_assoc a c (s n)).ge, fun x => ?_⟩
  obtain ⟨T, hT, hin, hout⟩ := h' x
  exact ⟨T, hT, fun hx => by linarith [hin hx], hout⟩

/-- The constant `2/3` in `BPSPACE` may be any `1/2 + δ` with `δ > 0`. [AB09, p. 139] -/
theorem mem_BPSPACE_of_advantage {N : FinNDTM Bool} {L : Language Bool} {s : ℕ → ℕ} {c : ℕ}
    {δ : ℚ} (hδ : 0 < δ) (hN : N.UsesSpace fun n => c * s n)
    (h : ∀ x : List Bool, ∃ T, N.tm.HaltsWithin x T ∧
      1/2 + δ ≤ N.outputProb x T [MultiTapeTM.indicator (L : Set (List Bool)) x]) :
    L ∈ BPSPACE s := by
  obtain ⟨a, N', hs, h'⟩ :=
    exists_bpDecides_of_advantage hδ (show (0 : ℚ) < 1/3 by norm_num) hN h
  refine ⟨a * c, N', ⟨hs.mono fun n => (Nat.mul_assoc a c (s n)).ge, fun x => ?_⟩⟩
  obtain ⟨T, hT, hp⟩ := h' x
  exact ⟨T, hT, by linarith⟩

end Randomized
