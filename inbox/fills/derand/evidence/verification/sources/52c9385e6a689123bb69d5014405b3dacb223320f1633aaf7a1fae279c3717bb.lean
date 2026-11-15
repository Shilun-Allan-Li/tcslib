/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.SpaceAmplifyPolyRun
import TCSlib.Complexity.SpaceComplexity.Machines.NARMLogspace

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Error reduction for BPL and RL with logarithmic space overhead

[AB09, §7.7, p. 139]: "The reader can verify that the error reduction procedure described in
Chapter 7 can be implemented with only logarithmic space overhead." For `L ∈ BPL` and every
`d`, a logarithmic-space PTM decides `L` with error at most `2^{-(|x|+1)^d} ≤ 2^{-|x|^d}` —
the space form of [AB09, Theorem 7.10] — and likewise for `RL` with one-sided error. The machine
(`Randomized.PolyAmp.ampA`) repeats the given PTM `K + 1 = 2^{F ℓ} + 1` times, polynomially
often, keeping a run counter, a count of accepting runs and the current configuration's code
in `O(log n)`-bit registers, and answers by majority (or by "some run accepted"); the
Chernoff bound `Randomized.randProb_tail_le` bounds the error. The setup phase measures `n`,
computes `ℓ`, the radius `c_S ℓ` and `K`, and enters the loop over the runs; the compiled
machine is then a logspace PTM with the register machine's output distribution
(`Complexity.LogProg.narm_logspace_ptm`).

## Main definitions

* `Randomized.PolyAmp.ell`, `Randomized.PolyAmp.bigK` — `ℓ` and `K` as functions of `n`.

## Main results

* `Randomized.PolyAmp.ps_start` — the semantics of the machine from the start.
* `Randomized.BPL_error_reduction` — [AB09, p. 139] for `BPL`.
* `Randomized.RL_error_reduction` — [AB09, p. 139] for `RL`.

## Divergences

* The hypothesis is membership in `BPL` (success `2/3`, [AB09, Def 7.18]), not Theorem 7.10's
  `1/2 + |x|^{-c}`. A constant advantage `1/2 + δ` reaches `2/3` first by
  `Randomized.mem_BPSPACE_of_advantage` (`Randomized.exists_bpDecides_of_advantage`); the
  error bound `2^{-(|x|+1)^d}` is slightly stronger than the book's `2^{-|x|^d}`.
* The book repeats `8 |x|^{2c+d}` times (Theorem 7.10); we repeat `2^{F ℓ} + 1` times with
  `ℓ = |bits |x|| + 1`, a power of two that the register machine computes by doublings.
* A run does not simulate the PTM on its work tapes: it walks the code of its configuration
  through the step pairs of `Complexity.Codec.stepLang`, the coin choosing the least or the
  greatest partner. This picks each successor with probability `1/2`, as a coin of the PTM
  does, though not by the same coin; only the distribution of the run matters.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized.PolyAmp

open Complexity Complexity.LogProg Complexity.Codec Turing

/-! ### The setup -/

section Setup

variable {cS F : ℕ} {N : FinNDTM Bool} {os : Bool} {x : List Bool} {B : ℕ}

/-- `ℓ = |bits n| + 1`. -/
def ell (n : ℕ) : ℕ := (Nat.bits n).length + 1

/-- `K = 2^{F ℓ}`. -/
def bigK (F n : ℕ) : ℕ := 2 ^ (F * ell n)

/-- A register file of the setup: `n`, `ℓ`, `s`, `e`, `K`, `R`, `t`, `a`; the others `0`. -/
def sreg (n l s e K R t a : ℕ) : Reg := ⟨n, l, s, e, K, R, 0, 0, 0, 0, 0, 0, t, a, 0⟩

/-- The register file at the start. -/
def reg0 : Reg := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- A configuration given by a register function equal to that of a register file. -/
lemma PS.of_v {l : Lab cS F} {σ' : Reg} {p : ℚ} {f : Fin 15 → ℕ} (h : f = σ'.v)
    (hp : PS N os x B l σ' p) :
    PSem (ampA cS F os) (ampOr N) x (RegLe 15 (Lab cS F) B) (some l, f, none) p := by
  rw [h]; exact hp

/-- Close an equation between register functions by evaluating every register. -/
local macro "reg_eq" : tactic =>
  `(tactic| (funext r; fin_cases r <;>
    simp [Reg.v, Function.update_apply, cpDst, cpSrc, reg0, sreg] <;> rfl))

/-- **The machine from the start** [AB09, §7.7, p. 139]: the setup computes `n`, `ℓ`, `S`
and `K` and the loop over the `K + 1` runs answers `true` with probability `runVal (K + 1) 0`.

**Proof sketch.** The setup is a chain of deterministic loops (`inputLength_loop`,
`copy_run`, `halvCount_loop`, `registerScale_loop`, `shl_run`), transported to the
probabilistic semantics by `PSem.of_reach`; then `ps_runs`. -/
theorem ps_start {sp : ℕ → ℕ} (hN : N.UsesSpace sp) (hs : sp x.length ≤ cS * ell x.length)
    (hK : codeBound N x.length (cS * ell x.length) ≤ bigK F x.length)
    (hB : x.length + ell x.length + (cS + F) * ell x.length + 2 * bigK F x.length + 2 ≤ B) :
    PS N os x B (.len : Lab cS F) reg0
      (runVal N x os (bigK F x.length) (bigK F x.length + 1) 0) := by
  set n := x.length with hn
  set ℓ := ell n with hℓ
  set K := bigK F n with hK'
  have hℓ1 : 1 ≤ ℓ := by simp [hℓ, ell]
  have hbits : (Nat.bits n).length + 1 = ℓ := rfl
  have hKpos : 1 ≤ K := Nat.one_le_two_pow
  have e : (cS + F) * ℓ = cS * ℓ + F * ℓ := by ring
  have hKdef : 2 ^ (F * ℓ) = K := rfl
  have hlb : (Nat.bits n).length ≤ B := by omega
  set A := (ampA cS F os).detPart false with hA
  -- the input length
  have r1 := inputLength_loop A (ampOr N) x 0 0 .len .lenI (.cp0 .nt) rfl rfl
    (fun m _ => by
      simp only [ampOr, ampAs, Matrix.cons_val_zero, inputLenLang]
      rw [indicator_indexLang_pairEncode]
      exact decide_eq_decide.mpr Iff.rfl)
    B (by omega) reg0.v (Reg.le_v (by simp only [Reg.Le, reg0]; omega)) (Nat.zero_le _)
  refine PSem.of_reach (AReach.mono r1 fun _ h => h.2) ?_
  refine PS.of_v (σ' := sreg n 0 0 0 0 0 0 0) (by reg_eq) ?_
  -- `t := n`, then `ℓ := |bits n| + 1`
  refine ps_cp .nt (σ' := sreg n 0 0 0 0 0 n 0) (by simp only [Reg.Le, sreg]; omega) rfl
    (by simp [cpDst, cpSrc, sreg]; omega) (by reg_eq) ?_
  have r2 := halvCount_loop A (ampOr N) x 12 1 (by decide) .hT .hH .hB .lI rfl rfl rfl B
    (sreg n 0 0 0 0 0 n 0).v
    (Reg.le_v (by simp only [Reg.Le, sreg]; omega)) (by simp [sreg]; omega)
  refine PSem.of_reach (AReach.mono r2 fun _ h => h.2) ?_
  refine PS.of_v (σ' := (sreg n ((Nat.bits n).length) 0 0 0 0 0 0)) (by reg_eq) ?_
  refine PSem.inc (A := ampA cS F os) rfl (Reg.le_v (by simp only [Reg.Le, sreg]; omega)) ?_
  refine PS.of_v (σ' := sreg n ℓ 0 0 0 0 0 0) (by reg_eq) ?_
  -- `S := c_S ℓ`
  refine ps_cp .la1 (σ' := sreg n ℓ 0 0 0 0 0 ℓ) (by simp only [Reg.Le, sreg]; omega) rfl
    (by simp [cpDst, cpSrc, sreg]; omega) (by reg_eq) ?_
  have r3 := registerScale_loop A (ampOr N) x 13 2 (by decide) .sT0 .sD0 (.cp0 .la2) sL0 cS
    rfl rfl (fun i hi => by simp [hA, sL0, hi, NARM.detPart, ampA]) (by simp [sL0]) B
    (sreg n ℓ 0 0 0 0 0 ℓ).v
    (Reg.le_v (by simp only [Reg.Le, sreg]; omega)) (by simp [sreg]; omega)
  refine PSem.of_reach (AReach.mono r3 fun _ h => h.2) ?_
  refine PS.of_v (σ' := sreg n ℓ (cS * ℓ) 0 0 0 0 0) (by reg_eq) ?_
  -- `e := F ℓ`
  refine ps_cp .la2 (σ' := sreg n ℓ (cS * ℓ) 0 0 0 0 ℓ) (by simp only [Reg.Le, sreg]; omega) rfl
    (by simp [cpDst, cpSrc, sreg]; omega) (by reg_eq) ?_
  have r4 := registerScale_loop A (ampOr N) x 13 3 (by decide) .sT1 .sD1 .kI sL1 F
    rfl rfl (fun i hi => by simp [hA, sL1, hi, NARM.detPart, ampA]) (by simp [sL1]) B
    (sreg n ℓ (cS * ℓ) 0 0 0 0 ℓ).v
    (Reg.le_v (by simp only [Reg.Le, sreg]; omega)) (by simp [sreg]; omega)
  refine PSem.of_reach (AReach.mono r4 fun _ h => h.2) ?_
  refine PS.of_v (σ' := sreg n ℓ (cS * ℓ) (F * ℓ) 0 0 0 0) (by reg_eq) ?_
  -- `K := 2^{F ℓ}`
  refine PSem.inc (A := ampA cS F os) rfl (Reg.le_v (by simp only [Reg.Le, sreg]; omega)) ?_
  have r5 := shl_run (A := A) (oracle := ampOr N) (x := x) (B := B) (l := .sh0) (l1 := .sh1)
    (l2 := .sh2) (l3 := .sh3) (l4 := .sh4) (l5 := .sh5) (l6 := .sh6) (l7 := .sh7) (l8 := .sh8)
    (lx := .cp0 .kR) (c := 3) (r := 4) (z := 11) (by decide) (by decide) (by decide)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl _ (sreg n ℓ (cS * ℓ) (F * ℓ) 1 0 0 0).v rfl rfl
    (Reg.le_v (by simp only [Reg.Le, sreg]; omega))
    (by show 1 * 2 ^ (F * ℓ) ≤ B; rw [hKdef]; omega)
  refine PS.of_v (σ' := sreg n ℓ (cS * ℓ) (F * ℓ) 1 0 0 0) (by reg_eq) ?_
  refine PSem.of_reach (AReach.mono r5 fun _ h => h.2) ?_
  refine PS.of_v (σ' := sreg n ℓ (cS * ℓ) 0 K 0 0 0)
      (by funext r; fin_cases r <;> simp [Reg.v, sreg, hKdef]) ?_
  -- `R := K + 1`, `i := K + 1`
  refine ps_cp .kR (σ' := sreg n ℓ (cS * ℓ) 0 K K 0 0) (by simp only [Reg.Le, sreg]; omega) rfl
    (by simp [cpDst, cpSrc, sreg]; omega) (by reg_eq) ?_
  refine PSem.inc (A := ampA cS F os) rfl (Reg.le_v (by simp only [Reg.Le, sreg]; omega)) ?_
  refine PS.of_v (σ' := sreg n ℓ (cS * ℓ) 0 K (K + 1) 0 0) (by reg_eq) ?_
  refine ps_cp .ri (σ' := mk n ℓ (cS * ℓ) K (K + 1) 0 0 0 0) (by simp only [Reg.Le, sreg]; omega)
    rfl (by simp [cpDst, cpSrc, sreg]; omega) (by simp only [mk]; reg_eq) ?_
  exact ps_runs hN hs hK (by omega) (K + 1) 0 0 0 (by omega) (by omega) (by omega)

end Setup

variable {N : FinNDTM Bool} {x : List Bool}

/-! ### Chernoff bounds for the runs -/

/-- **Majority of the runs, accepting case**: if a run accepts with probability `≥ 2/3`, the
majority of `K + 1` runs errs with probability at most `2 (8/9)^{(K+1)/2}`. -/
theorem runVal_two_ge {K : ℕ} (h : 2/3 ≤ randProb K (fun l => accBit N x l = true)) :
    1 - 2 * (8/9 : ℚ) ^ ((K + 1) / 2) ≤ runVal N x false K (K + 1) 0 := by
  classical
  have hB : randProb K (fun l => (fun l => !accBit N x l) l = true) ≤ 1/2 - 1/6 := by
    rw [randProb_congr (B := fun l => accBit N x l = false) fun r => by simp, randProb_bool_false]
    linarith
  have ht := randProb_tail_le K (K + 1) (fun l => !accBit N x l) (by norm_num) hB
  have hmono : randProb ((K + 1) * K)
      (fun w => ¬ decRule false K (0 + blockCount K (K + 1) (accBit N x) w) = true) ≤
      randProb ((K + 1) * K)
        (fun w => K + 1 ≤ 2 * blockCount K (K + 1) (fun l => !accBit N x l) w) :=
    randProb_mono fun r hr => by
      have := blockCount_add_not K (K + 1) (accBit N x) (List.ofFn r)
      simp only [decRule, Bool.false_eq_true, if_false, decide_eq_true_eq, not_lt,
        Nat.zero_add] at hr
      omega
  have hnot := randProb_not (m := (K + 1) * K)
    (fun w => decRule false K (0 + blockCount K (K + 1) (accBit N x) w) = true)
  unfold runVal
  have e : (1 - 4 * (1/6 : ℚ) ^ 2) = 8/9 := by norm_num
  rw [e] at ht
  linarith

/-- **Majority of the runs, rejecting case**: if a run accepts with probability `≤ 1/3`, the
majority of `K + 1` runs accepts with probability at most `2 (8/9)^{(K+1)/2}`. -/
theorem runVal_two_le {K : ℕ} (h : randProb K (fun l => accBit N x l = true) ≤ 1/3) :
    runVal N x false K (K + 1) 0 ≤ 2 * (8/9 : ℚ) ^ ((K + 1) / 2) := by
  classical
  have ht := randProb_tail_le K (K + 1) (accBit N x) (ε := 1/6) (by norm_num) (by linarith)
  have hmono : runVal N x false K (K + 1) 0 ≤
      randProb ((K + 1) * K) (fun w => K + 1 ≤ 2 * blockCount K (K + 1) (accBit N x) w) :=
    randProb_mono fun r hr => by
      simp only [decRule, Bool.false_eq_true, if_false, decide_eq_true_eq, Nat.zero_add] at hr
      omega
  have e : (1 - 4 * (1/6 : ℚ) ^ 2) = 8/9 := by norm_num
  rw [e] at ht
  linarith

/-- **Some run accepts**: the probability is `1 - (1 - p)^{K+1}`. -/
theorem runVal_one (K : ℕ) :
    runVal N x true K (K + 1) 0 = 1 - (1 - randProb K (fun l => accBit N x l = true)) ^ (K + 1)
        := by
  classical
  have hzero := randProb_blockCount K (accBit N x) (K + 1) 0 (Nat.zero_le _)
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, Nat.sub_zero] at hzero
  rw [← hzero, ← randProb_not]
  refine randProb_congr fun r => ?_
  simp [decRule]
  omega

/-- The error bound: `2 (8/9)^{(K+1)/2} ≤ 2^{-(n+1)^d}` once `K ≥ 32 (n + 1)^d`. -/
theorem two_mul_pow_le {K n d : ℕ} (hK : 32 * (n + 1) ^ d ≤ K) :
    2 * (8/9 : ℚ) ^ ((K + 1) / 2) ≤ (1/2) ^ ((n + 1) ^ d) := by
  have h2 : 1 ≤ (n + 1) ^ d := Nat.one_le_pow _ _ (Nat.succ_pos n)
  have ht : 6 * ((n + 1) ^ d + 1) ≤ (K + 1) / 2 := by omega
  have h89 : (8/9 : ℚ) ^ 6 ≤ 1/2 := by norm_num
  calc 2 * (8/9 : ℚ) ^ ((K + 1) / 2) ≤ 2 * (8/9 : ℚ) ^ (6 * ((n + 1) ^ d + 1)) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) ht)
          (by norm_num)
    _ = 2 * ((8/9 : ℚ) ^ 6) ^ ((n + 1) ^ d + 1) := by rw [pow_mul]
    _ ≤ 2 * (1/2 : ℚ) ^ ((n + 1) ^ d + 1) := by gcongr
    _ = (1/2) ^ ((n + 1) ^ d) := by rw [pow_succ]; ring

/-! ### Sizes -/

/-- `2^{|bits n|} ≤ 2n + 1`. -/
theorem two_pow_bits_le (n : ℕ) : 2 ^ (Nat.bits n).length ≤ 2 * n + 1 := by
  rw [Nat.size_eq_bits_len]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hs : 0 < n.size := Nat.size_pos.mpr hn
    have := Nat.lt_size.mp (show n.size - 1 < n.size by omega)
    have e : 2 ^ n.size = 2 * 2 ^ (n.size - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega

/-- `n < 2^{|bits n|}`. -/
theorem lt_two_pow_bits (n : ℕ) : n < 2 ^ (Nat.bits n).length := by
  rw [Nat.size_eq_bits_len]; exact Nat.lt_size_self n

/-- `logSpace n ≤ ℓ`. -/
theorem logSpace_le_ell (n : ℕ) : logSpace n ≤ ell n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [logSpace, ell]
  · have := Nat.log_lt_of_lt_pow (b := 2) (by omega) (lt_two_pow_bits n)
    simp only [logSpace, ell]; omega

/-- `K ≥ 32 (n + 1)^d` when `F ≥ d + 5`. -/
theorem bigK_ge {F n d : ℕ} (hF : d + 5 ≤ F) : 32 * (n + 1) ^ d ≤ bigK F n := by
  have h2 : n + 1 ≤ 2 ^ ell n := by
    have := lt_two_pow_bits n; simp only [ell, pow_succ]; omega
  have h1 : 2 ≤ 2 ^ ell n := by
    simp only [ell, pow_succ]; have := Nat.one_le_two_pow (n := (Nat.bits n).length); omega
  calc 32 * (n + 1) ^ d ≤ (2 ^ ell n) ^ 5 * (2 ^ ell n) ^ d := by
        gcongr
        calc 32 = 2 ^ 5 := by norm_num
          _ ≤ (2 ^ ell n) ^ 5 := Nat.pow_le_pow_left h1 5
    _ = 2 ^ ((d + 5) * ell n) := by rw [← pow_add, ← pow_mul]; ring_nf
    _ ≤ bigK F n := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ hF)

/-- `K ≤ 4^F (n + 1)^F`. -/
theorem bigK_le (F n : ℕ) : bigK F n ≤ 4 ^ F * (n + 1) ^ F := by
  have h : 2 ^ ell n ≤ 4 * (n + 1) := by
    have := two_pow_bits_le n; simp only [ell, pow_succ]; omega
  calc bigK F n = (2 ^ ell n) ^ F := by rw [bigK, ← pow_mul, Nat.mul_comm]
    _ ≤ (4 * (n + 1)) ^ F := Nat.pow_le_pow_left h F
    _ = 4 ^ F * (n + 1) ^ F := mul_pow _ _ _

/-- `ℓ ≤ n + 1`. -/
theorem ell_le (n : ℕ) : ell n ≤ n + 1 := by
  have := lt_two_pow_bits n
  have h : (Nat.bits n).length ≤ n := by
    rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr (Nat.lt_two_pow_self)
  simp only [ell]; omega

/-- The register bound is polynomial. -/
theorem regBound_le (cS F n : ℕ) :
    n + ell n + (cS + F) * ell n + 2 * bigK F n + 2 ≤
      (cS + F + 6 + 2 * 4 ^ F) * (n + 1) ^ (F + 1) := by
  have hK := bigK_le F n
  have hl := ell_le n
  have p1 : n + 1 ≤ (n + 1) ^ (F + 1) := Nat.le_self_pow (by omega) _
  have p0 : 1 ≤ n + 1 := by omega
  have pF : (n + 1) ^ F ≤ (n + 1) ^ (F + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have e : (cS + F + 6 + 2 * 4 ^ F) * (n + 1) ^ (F + 1) =
      (cS + F) * (n + 1) ^ (F + 1) + 6 * (n + 1) ^ (F + 1) +
        2 * (4 ^ F * (n + 1) ^ (F + 1)) := by ring
  have h1 : (cS + F) * ell n ≤ (cS + F) * (n + 1) ^ (F + 1) :=
    Nat.mul_le_mul_left _ (hl.trans p1)
  have h2 : 4 ^ F * (n + 1) ^ F ≤ 4 ^ F * (n + 1) ^ (F + 1) := Nat.mul_le_mul_left _ pF
  omega

end Randomized.PolyAmp

namespace Randomized

open Complexity Complexity.LogProg Complexity.Codec Turing PolyAmp

/-- The setting of the repetition machine for a PTM `N` deciding in space `c · logSpace`:
on every input it halts within `bigK F |x|` (for `F ≥ codeK N · (c + 2)`), its acceptance
probability is that of the blocks of `bigK F |x|` coins, and the machine's semantics from the
start is `runVal`.

**Proof sketch.** The codes at radius `c · ℓ ≥ c · logSpace |x|` are below `codeBound ≤ bigK`;
halting moves to `bigK` by `haltsWithin_codeBound` and output probabilities by
`outputProb_eq_of_haltsWithin`; the block probability is `accP_init`; `ps_start` gives the
semantics, and `PSem.decides` a halting length with the answer probabilities. -/
theorem polyAmp_setting {N : FinNDTM Bool} {c F : ℕ} (os : Bool)
    (hN : N.UsesSpace fun n => c * logSpace n) (hF : codeK N * (c + 2) ≤ F) (x : List Bool)
    {T₀ : ℕ} (hT₀ : N.tm.HaltsWithin x T₀) :
    N.tm.HaltsWithin x (bigK F x.length) ∧
      (∀ v, N.outputProb x (bigK F x.length) v = N.outputProb x T₀ v) ∧
      randProb (bigK F x.length) (fun l => accBit N x l = true) =
        N.outputProb x (bigK F x.length) [true] ∧
      ∃ Nc, NHalts (ampA c F os) (ampOr N) x
        (fun a => NPreS (ampA c F os) x a ∧
          ∀ r, a.2.1 r ≤ (c + F + 6 + 2 * 4 ^ F) * (x.length + 1) ^ (F + 1))
        (some .len, fun _ => 0, none) Nc ∧
        ansProb (ampA c F os) (ampOr N) x (some .len, fun _ => 0, none) Nc true =
          runVal N x os (bigK F x.length) (bigK F x.length + 1) 0 ∧
        ansProb (ampA c F os) (ampOr N) x (some .len, fun _ => 0, none) Nc false =
          1 - runVal N x os (bigK F x.length) (bigK F x.length + 1) 0 := by
  set n := x.length
  have hs : (fun n => c * logSpace n) x.length ≤ c * ell n :=
    Nat.mul_le_mul_left c (logSpace_le_ell n)
  have hK : codeBound N n (c * ell n) ≤ bigK F n := by
    unfold codeBound bigK
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have h1 := logSpace_le_ell n
    have h2 : 1 ≤ ell n := by simp [ell]
    have e : (c + 2) * ell n = c * ell n + 2 * ell n := by ring
    calc codeK N * (c * ell n + logSpace n + 1) ≤ codeK N * ((c + 2) * ell n) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = codeK N * (c + 2) * ell n := by ring
      _ ≤ F * ell n := Nat.mul_le_mul_right _ hF
  have hhalt : N.tm.HaltsWithin x (bigK F n) :=
    (haltsWithin_codeBound hN hs hT₀).mono hK
  refine ⟨hhalt, fun v => ?_, ?_, ?_⟩
  · rw [FinNDTM.outputProb_eq_of_haltsWithin (haltsWithin_codeBound hN hs hT₀) hK]
    rcases le_total (codeBound N n (c * ell n)) T₀ with h | h
    · exact (FinNDTM.outputProb_eq_of_haltsWithin (haltsWithin_codeBound hN hs hT₀) h v).symm
    · exact FinNDTM.outputProb_eq_of_haltsWithin hT₀ h v
  · rw [← accP_init hhalt]
    exact randProb_congr fun r => by simp [accBit]
  · have hp := ps_start (cS := c) (F := F) (os := os) (B := n + ell n + (c + F) * ell n +
      2 * bigK F n + 2) hN hs hK le_rfl
    obtain ⟨Nc, hNc, h1, h0⟩ := hp.decides
    have e : reg0.v = fun _ => 0 := by funext r; fin_cases r <;> rfl
    rw [e] at hNc h1 h0
    exact ⟨Nc, hNc.mono fun a ha => ⟨ampA_npreS os x a, fun r =>
      (ha r).trans (regBound_le c F n)⟩, h1, h0⟩

/-- **Error reduction for `BPL` with logarithmic space overhead** [AB09, §7.7, p. 139]: for
`L ∈ BPL` and every `d`, some PTM using space `O(log n)` decides `L` with error at most
`2^{-(|x|+1)^d}`.

**Proof sketch.** Repeat the `BPL` machine `K + 1` times by `ampA` with `F = codeK N (c + 2) +
d + 5` (`polyAmp_setting`), compile it (`narm_logspace_ptm`); a run accepts with the
machine's acceptance probability, at least `2/3` on members and at most `1/3` on non-members,
so the majority errs with probability at most `2 (8/9)^{(K+1)/2} ≤ 2^{-(|x|+1)^d}`
(`runVal_two_ge`, `runVal_two_le`, `two_mul_pow_le`, `bigK_ge`). -/
theorem BPL_error_reduction {L : Language Bool} (hL : L ∈ BPL) (d : ℕ) :
    ∃ (c : ℕ) (M : FinNDTM Bool), M.UsesSpace (fun n => c * logSpace n) ∧
      ∀ x : List Bool, ∃ T, M.tm.HaltsWithin x T ∧
        1 - (1/2 : ℚ) ^ ((x.length + 1) ^ d) ≤
          M.outputProb x T [MultiTapeTM.indicator (L : Set (List Bool)) x] := by
  classical
  obtain ⟨c, N, hNs, hN⟩ := hL
  set F := codeK N * (c + 2) + d + 5 with hF
  obtain ⟨c', M, hU, hM⟩ := narm_logspace_ptm (ampA c F false) .len (ampAs N) (ampAs_mem N)
    (c + F + 6 + 2 * 4 ^ F) (F + 1) fun x => by
      obtain ⟨T₀, hT₀, -⟩ := hN x
      obtain ⟨-, -, -, Nc, hNc, -⟩ := polyAmp_setting (F := F) false hNs (by omega) x hT₀
      exact ⟨Nc, hNc⟩
  refine ⟨c', M, hU, fun x => ?_⟩
  obtain ⟨T₀, hT₀, hp⟩ := hN x
  obtain ⟨-, hout, hacc, Nc, hNc, h1, h0⟩ := polyAmp_setting (F := F) false hNs (by omega) x hT₀
  obtain ⟨T, hT, hMp⟩ := hM x Nc hNc
  refine ⟨T, hT, ?_⟩
  have herr := two_mul_pow_le (bigK_ge (n := x.length) (d := d) (by omega : d + 5 ≤ F))
  by_cases hx : x ∈ L
  · simp only [MultiTapeTM.indicator, hx, if_true] at hp ⊢
    rw [hMp, h1]
    have : 2/3 ≤ randProb (bigK F x.length) (fun l => accBit N x l = true) := by
      rw [hacc, hout]; exact hp
    linarith [runVal_two_ge this]
  · simp only [MultiTapeTM.indicator, hx, if_false] at hp ⊢
    rw [hMp, h0]
    have hsum : N.outputProb x T₀ [true] + N.outputProb x T₀ [false] ≤ 1 := by
      unfold FinNDTM.outputProb
      rw [← randProb_or_disjoint _ _ fun r h => by
        have := h.1.symm.trans h.2
        simp at this]
      exact randProb_le_one
    have : randProb (bigK F x.length) (fun l => accBit N x l = true) ≤ 1/3 := by
      rw [hacc, hout]; linarith
    linarith [runVal_two_le this]

/-- **Error reduction for `RL` with logarithmic space overhead** [AB09, §7.7, p. 139]: for
`L ∈ RL` and every `d`, some PTM using space `O(log n)` accepts members with probability at
least `1 - 2^{-(|x|+1)^d}` and rejects non-members on every branch.

**Proof sketch.** As `BPL_error_reduction` with the one-sided rule: members are rejected only
if all `K + 1` runs reject, with probability `(1 - p)^{K+1} ≤ 3^{-(K+1)}` (`runVal_one`); on
non-members no run accepts, so the answer is `false` with probability `1`, hence on every
branch (`forall_of_randProb_eq_one`). -/
theorem RL_error_reduction {L : Language Bool} (hL : L ∈ RL) (d : ℕ) :
    ∃ (c : ℕ) (M : FinNDTM Bool), M.UsesSpace (fun n => c * logSpace n) ∧
      ∀ x : List Bool, ∃ T, M.tm.HaltsWithin x T ∧
        (x ∈ L → 1 - (1/2 : ℚ) ^ ((x.length + 1) ^ d) ≤ M.outputProb x T [true]) ∧
        (x ∉ L → ∀ w : List Bool, w.length = T → M.outputWith x w = [false]) := by
  classical
  obtain ⟨c, N, hNs, hN⟩ := hL
  set F := codeK N * (c + 2) + d + 5 with hF
  obtain ⟨c', M, hU, hM⟩ := narm_logspace_ptm (ampA c F true) .len (ampAs N) (ampAs_mem N)
    (c + F + 6 + 2 * 4 ^ F) (F + 1) fun x => by
      obtain ⟨T₀, hT₀, -⟩ := hN x
      obtain ⟨-, -, -, Nc, hNc, -⟩ := polyAmp_setting (F := F) true hNs (by omega) x hT₀
      exact ⟨Nc, hNc⟩
  refine ⟨c', M, hU, fun x => ?_⟩
  obtain ⟨T₀, hT₀, hin, hrej⟩ := hN x
  obtain ⟨hhalt, hout, hacc, Nc, hNc, h1, h0⟩ := polyAmp_setting (F := F) true hNs (by omega) x hT₀
  obtain ⟨T, hT, hMp⟩ := hM x Nc hNc
  set K := bigK F x.length
  have hK := bigK_ge (n := x.length) (d := d) (by omega : d + 5 ≤ F)
  refine ⟨T, hT, fun hx => ?_, fun hx w hw => ?_⟩
  · rw [hMp, h1, runVal_one]
    have hp : 2/3 ≤ randProb K (fun l => accBit N x l = true) := by
      rw [hacc, hout]; exact hin hx
    have hp1 := randProb_le_one (m := K) (A := fun l => accBit N x l = true)
    have h3 : (1 - randProb K (fun l => accBit N x l = true)) ^ (K + 1) ≤ (1/2 : ℚ) ^ (K + 1) :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    have h4 : (1/2 : ℚ) ^ (K + 1) ≤ (1/2) ^ ((x.length + 1) ^ d) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith
  · -- no run accepts
    have hp0 : randProb K (fun l => accBit N x l = true) = 0 := by
      rw [← randProb_false (m := K)]
      refine randProb_congr fun r => ?_
      simp only [accBit, Accepting, decide_eq_true_eq, iff_false, not_and]
      intro _ hacc'
      have hlen : (List.ofFn r).length = K := List.length_ofFn
      have hfalse : N.outputWith x (List.ofFn r) = [false] := by
        rcases le_total T₀ K with h | h
        · rw [FinNDTM.outputWith, FinNDTM.runWith_eq_runWith_take hT₀ (by rw [hlen]; exact h)]
          exact hrej hx _ (List.length_take_of_le (by rw [hlen]; exact h))
        · have hw' := hrej hx (List.ofFn r ++ List.replicate (T₀ - K) false)
            (by simp only [List.length_append, List.length_replicate, hlen]; omega)
          rw [FinNDTM.outputWith, NDTM.runWith_append,
            NDTM.runWith_of_halt _ (hhalt _ hlen)] at hw'
          exact hw'
      rw [FinNDTM.outputWith] at hfalse
      rw [hfalse] at hacc'
      exact absurd hacc' (by decide)
    have hone : M.outputProb x T [false] = 1 := by
      rw [hMp, h0, runVal_one, hp0]; ring
    obtain ⟨r, rfl⟩ := exists_ofFn_eq hw
    exact forall_of_randProb_eq_one hone r

end Randomized
