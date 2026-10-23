/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.SpaceComplexity.Machines.NARMPSem
import TCSlib.Complexity.Randomized.Space

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Probabilistic register machines as logspace PTMs, and `RL`

A nondeterministic abstract register machine (`Complexity.LogProg.NARM`) with polynomially
bounded registers, whose `choose` bits are fair coins and whose oracle calls go to logspace
deciders, compiles to a probabilistic Turing machine in logarithmic space [AB09, §7.7] with
the output probabilities `Complexity.LogProg.ansProb` of its probabilistic semantics
(`TCSlib.Complexity.SpaceComplexity.Machines.NARMPSem`). The one-sided corollary places the
language such a machine decides in `RL` [AB09, Def 7.18].

This is infrastructure for [AB09, Theorem 7.19] (`TCSlib.Complexity.Randomized.UPathRL`) and
for polynomial error reduction in `BPL`/`RL` (`TCSlib.Complexity.Randomized.SpaceAmplifyPoly`),
not itself a result of the book.

## Main results

* `Complexity.LogProg.narm_logspace_ptm` — the compiled logspace PTM has the abstract output
  probabilities.
* `Complexity.LogProg.narm_mem_RL` — the bridge to `RL`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.7.)
-/

namespace Complexity.LogProg

open Turing Randomized

variable {m d : ℕ} {Λ : Type}

/-- **A probabilistic register machine with polynomially bounded registers is a PTM in
logarithmic space** with the same output distribution: the compiled machine uses space
`O(log n)` on every branch and, whenever the abstract machine halts within `N` choices
through the guard, outputs `[b]` with the abstract probability of the answer `b`.
`Complexity.LogProg.narm_mem_RL` is its one-sided corollary.

**Proof sketch.** As `narm_mem_RL`: collect the deciders in a clean bank, take decider head
range `B = C · logSpace |x| + 1` and register width `K · logSpace |x|` (`log_poly_bound`), so
that the preconditions `NGuard` hold (`npre_of_npreS`); `narm_space_randProb` gives a `T`
within which every compiled branch halts in `O(logSpace)` cells with the abstract output
probabilities, and `FinNDTM.usesSpace_of_haltsWithin` bounds every branch. -/
theorem narm_logspace_ptm [Fintype Λ] [DecidableEq Λ] (A : NARM m d Λ) (l₀ : Λ)
    (As : Fin d → Language Bool) (hAs : ∀ j, As j ∈ LOGSPACE) (C₀ c₀ : ℕ)
    (hcorr : ∀ x, ∃ N, NHalts A (fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V) x
      (fun a => NPreS A x a ∧ ∀ r, a.2.1 r ≤ C₀ * (x.length + 1) ^ c₀)
      (some l₀, fun _ => 0, none) N) :
    ∃ (c : ℕ) (M : FinNDTM Bool), M.UsesSpace (fun n => c * logSpace n) ∧
      ∀ x N, NHalts A (fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V) x
        (fun a => NPreS A x a ∧ ∀ r, a.2.1 r ≤ C₀ * (x.length + 1) ^ c₀)
        (some l₀, fun _ => 0, none) N →
        ∃ T, M.tm.HaltsWithin x T ∧ ∀ b : Bool, M.outputProb x T [b] =
          ansProb A (fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V) x
            (some l₀, fun _ => 0, none) N b := by
  classical
  have hc : ∀ j, ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInSpace (As j) fun n => c * logSpace n :=
    fun j => hAs j
  choose c Ms hMs using hc
  set cs := ∑ j, c j with hcs
  have hcj : ∀ j, c j ≤ cs := fun j =>
    Finset.single_le_sum (f := c) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  obtain ⟨K, hK⟩ := log_poly_bound C₀ c₀ 1
  set Q := 4 + 2 * m + 2 * m * K with hQ
  obtain ⟨K2, hK2⟩ := log_poly_bound Q 1 0
  set C := K + cs * K2 with hC
  set kD := bankK Ms + bankK Ms with hkD
  set oracle : Fin d → List Bool → Bool :=
    fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V with horacle
  set M := ncompileFinNDTM A l₀ (bankTM Ms) (bankStart Ms) with hM
  have key : ∀ (x : List Bool) (N : ℕ), NHalts A oracle x
      (fun a => NPreS A x a ∧ ∀ r, a.2.1 r ≤ C₀ * (x.length + 1) ^ c₀)
      (some l₀, fun _ => 0, none) N → ∃ T, M.tm.HaltsWithin x T ∧
      (∀ w : List Bool, w.length = T →
        M.tm.spaceUsedWith w (M.tm.initCfg x) ≤
          (m * C + 2 * m + kD * (2 * C + 3)) * logSpace x.length) ∧
      ∀ b : Bool, M.outputProb x T [b] = ansProb A oracle x (some l₀, fun _ => 0, none) N b := by
    intro x N hN
    set n := x.length with hn
    have hS1 : 1 ≤ logSpace n := by simp [logSpace]
    set W := K * logSpace n with hW
    set B := C * logSpace n + 1 with hB
    have hLn : logSpace n ≤ n + 1 := by
      have := Nat.log_le_self 2 n
      simp only [logSpace]; omega
    have hsp : ∀ j v, v ≤ 2 * n + 2 + m * (2 * W + 2) → c j * logSpace v ≤ B := by
      intro j v hv
      rw [hW] at hv
      have hVQ : v ≤ Q * (n + 1) ^ 1 + 0 := by
        have hW' : K * logSpace n ≤ K * (n + 1) := Nat.mul_le_mul_left K hLn
        have e : Q * (n + 1) ^ 1 + 0 = (4 + 2 * m) * (n + 1) + 2 * m * (K * (n + 1)) := by
          simp only [hQ]; ring
        rw [e]
        have h5 : m * (2 * (K * logSpace n) + 2) ≤ 2 * m * (K * (n + 1)) + 2 * m := by
          have := Nat.mul_le_mul_left (2 * m) hW'
          calc m * (2 * (K * logSpace n) + 2) = 2 * m * (K * logSpace n) + 2 * m := by ring
            _ ≤ 2 * m * (K * (n + 1)) + 2 * m := by omega
        have h6 : 2 * m ≤ 2 * m * (n + 1) := Nat.le_mul_of_pos_right _ (by omega)
        have h7 : (4 + 2 * m) * (n + 1) = 4 * (n + 1) + 2 * m * (n + 1) := by ring
        omega
      have hlog : logSpace v ≤ K2 * logSpace n := by
        have h := hK2 n
        have hm' := Nat.log_mono_right (b := 2) hVQ
        simp only [logSpace] at h hm' ⊢
        omega
      calc c j * logSpace v ≤ cs * (K2 * logSpace n) := Nat.mul_le_mul (hcj j) hlog
        _ ≤ C * logSpace n := by rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (by omega)
        _ ≤ B := by omega
    have hwid : ∀ a : AConf m Λ, (∀ r, a.2.1 r ≤ C₀ * (n + 1) ^ c₀) →
        ∀ r, (Nat.bits (a.2.1 r + 1)).length ≤ W := by
      intro a h2 r
      have e1 := length_bits_le_log (a.2.1 r + 1)
      have e2 : Nat.log 2 (a.2.1 r + 1) ≤ Nat.log 2 (C₀ * (n + 1) ^ c₀ + 1) :=
        Nat.log_mono_right (by have := h2 r; omega)
      have e3 := hK n
      simp only [hW, logSpace]
      omega
    have hG : NHalts A oracle x (NGuard A oracle (bankTM Ms) (bankStart Ms) B W x)
        (some l₀, fun _ => 0, none) N :=
      hN.mono fun a ⟨hps, hbd⟩ =>
        ⟨npre_of_npreS A Ms As (fun j n => c j * logSpace n) hMs B W (by omega)
          (fun j v hv => hsp j v hv) a hps (hwid a hbd),
         fun r => by exact_mod_cast hwid a hbd r⟩
    obtain ⟨T, hhalt, hspace, -, hprob⟩ :=
      narm_space_randProb A l₀ oracle (bankTM Ms) (bankStart Ms) B W N hG
    refine ⟨T, hhalt, fun w hw => (hspace w hw).trans ?_, fun b => ?_⟩
    · have f0 : m * W ≤ m * (C * logSpace n) :=
        Nat.mul_le_mul_left m (Nat.mul_le_mul_right _ (by omega))
      have e1 : m * (W + 2) = m * W + 2 * m := by ring
      have e2 : kD * (2 * B + 1) = 2 * kD * C * logSpace n + 3 * kD := by simp only [hB]; ring
      have e3 : (m * C + 2 * m + kD * (2 * C + 3)) * logSpace n =
          m * (C * logSpace n) + 2 * m * logSpace n + 2 * kD * C * logSpace n +
            3 * kD * logSpace n := by ring
      rw [e1, e2, e3]
      have f1 : 2 * m ≤ 2 * m * logSpace n := Nat.le_mul_of_pos_right _ (by omega)
      have f2 : 3 * kD ≤ 3 * kD * logSpace n := Nat.le_mul_of_pos_right _ (by omega)
      omega
    · unfold FinNDTM.outputProb FinNDTM.outputWith ansProb
      exact hprob b
  refine ⟨m * C + 2 * m + kD * (2 * C + 3), M,
    FinNDTM.usesSpace_of_haltsWithin fun x => ?_, fun x N hN => ?_⟩
  · obtain ⟨N, hN⟩ := hcorr x
    obtain ⟨T, hT, hs, -⟩ := key x N hN
    exact ⟨T, hT, hs⟩
  · obtain ⟨T, hT, -, hp⟩ := key x N hN
    exact ⟨T, hT, hp⟩

/-! ## The bridge to `RL` -/

/-- **Probabilistic register machines with polynomially bounded registers decide languages in
`RL`**: if, on every input `x`, for some `N` every choice word of length `N` halts the machine
`A` (calling deciders for languages in `L`) through configurations meeting the syntactic
preconditions with register values at most `C₀ (|x| + 1)^{c₀}`, members answer `true` with
probability at least `δ > 0` and non-members answer `false` with probability `1`, then
`L ∈ RL`. Infrastructure for [AB09, Def 7.18]; the probabilistic form of
`Complexity.LogProg.narm_decides_poly`.

**Proof sketch.** `narm_logspace_ptm` compiles the machine into a logspace PTM with the
abstract output probabilities. Members are accepted with probability `≥ δ`; for non-members
every compiled branch outputs `[false]` (`forall_of_randProb_eq_one`), and `mem_RSPACE_of_pos`
amplifies `δ` to `2/3`. -/
theorem narm_mem_RL {L : Language Bool} [Fintype Λ] [DecidableEq Λ] (A : NARM m d Λ)
    (l₀ : Λ) (As : Fin d → Language Bool) (hAs : ∀ j, As j ∈ LOGSPACE) (C₀ c₀ : ℕ) {δ : ℚ}
    (hδ : 0 < δ)
    (hcorr : ∀ x, ∃ N,
      NHalts A (fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V) x
        (fun a => NPreS A x a ∧ ∀ r, a.2.1 r ≤ C₀ * (x.length + 1) ^ c₀)
        (some l₀, fun _ => 0, none) N ∧
      (x ∈ L → δ ≤ ansProb A (fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V) x
        (some l₀, fun _ => 0, none) N true) ∧
      (x ∉ L → ansProb A (fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V) x
        (some l₀, fun _ => 0, none) N false = 1)) :
    L ∈ RL := by
  classical
  obtain ⟨c, M, hU, hM⟩ := narm_logspace_ptm A l₀ As hAs C₀ c₀ fun x => by
    obtain ⟨N, hN, -⟩ := hcorr x
    exact ⟨N, hN⟩
  refine mem_RSPACE_of_pos (c := c) (N := M) hδ hU fun x => ?_
  obtain ⟨N, hN, hin, hout⟩ := hcorr x
  obtain ⟨T, hT, hp⟩ := hM x N hN
  refine ⟨T, hT, fun hx => by rw [hp]; exact hin hx, fun hx w hw => ?_⟩
  obtain ⟨r, rfl⟩ := exists_ofFn_eq hw
  exact forall_of_randProb_eq_one ((hp false).trans (hout hx)) r

end Complexity.LogProg
