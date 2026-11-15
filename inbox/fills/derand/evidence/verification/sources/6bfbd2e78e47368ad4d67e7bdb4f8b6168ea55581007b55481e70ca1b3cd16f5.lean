/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.ZPPHosts

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# ZPP: expected time, abort form, certificates, and RP ∩ coRP

The converse inclusions for the zero-error classes, at machine level, through the clocked
restart host (`Randomized.clockHost_zDecides`, `Randomized.clockHost_abortDecides`), and the
resulting equalities with the easy directions of `TCSlib.Complexity.Randomized.ZPPEquiv`.

* **§7.4.2** — a zero-error PTM with expected time `T`, run for `m ≥ 2T` steps with abort on
  timeout, is an abort-form decider.
* **Ex 7.6(a), ⇐** — a polynomial-time zero-error verifier gives a PTM attempt: one coin
  `b` selects the PTM of the Boolean verifier "`M` answers `b`"
  (`Randomized.exists_FinNDTM_of_eff`), whose `1` becomes the answer `b` and whose `0` becomes
  no answer. An attempt answers with probability at least `1/4`, always correctly; the restart
  host reruns it until it answers.

## Main definitions

* `Randomized.zppAttempt`, `Randomized.keepAs` — the one-coin attempt built from two PTMs.

## Main results

* `Turing.FinNDTM.ZDecidesInTime.exists_abortDecidesInTime` — [AB09, §7.4.2] at machine
  level.
* `Randomized.ZPP_PTM_subset_ZPPAbort_PTM`, `Randomized.inZPP_subset_ZPP_PTM`,
  `Randomized.inZPP_subset_ZPPAbort_PTM`, `Randomized.mem_ZPP_PTM_iff`.
* `Randomized.ZPP_PTM_eq_setOf_inZPP`, `Randomized.ZPPAbort_PTM_eq_ZPP_PTM` —
  [AB09, Def 7.7 and Exercise 7.6(a)].
* `Randomized.ZPP_PTM_eq_RP_PTM_inter_coRP_PTM` — [AB09, Theorem 7.8] for Def 7.7's `ZPP`.

## Divergences

* Ex 7.6(a)'s "repeat until an answer" reruns an attempt that answers with probability at
  least `1/4` (one coin chooses which answer to look for), not the abort-form machine itself;
  the expected time is `16(m + 1)` steps after a polynomial startup.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open Turing Complexity

/-- `(n + 1)^p ≤ 2^p (n^p + 1)`. -/
theorem succ_pow_le_two_pow_mul (n p : ℕ) : (n + 1) ^ p ≤ 2 ^ p * (n ^ p + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [zero_add, one_pow]
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  · calc (n + 1) ^ p ≤ (2 * n) ^ p := Nat.pow_le_pow_left (by omega) p
      _ = 2 ^ p * n ^ p := mul_pow 2 n p
      _ ≤ 2 ^ p * (n ^ p + 1) := Nat.mul_le_mul_left _ (by omega)

/-- A sum of terms in `(n+1)^(p+1)`, `(n+1)^p` and constants, in the `c(n^e + 1)` normal form. -/
theorem add_mul_succ_pow_le (A B C n p : ℕ) :
    A * (n + 1) ^ (p + 1) + B * (n + 1) ^ p + C ≤
      (A + B + C) * 2 ^ (p + 1) * (n ^ (p + 1) + 1) := by
  have h1 : (n + 1) ^ p ≤ (n + 1) ^ (p + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : 1 ≤ (n + 1) ^ (p + 1) := Nat.one_le_pow _ _ (by omega)
  calc A * (n + 1) ^ (p + 1) + B * (n + 1) ^ p + C
      ≤ (A + B + C) * (n + 1) ^ (p + 1) := by
        rw [Nat.add_mul, Nat.add_mul]
        have := Nat.mul_le_mul_left B h1
        have := Nat.mul_le_mul_left C h2
        omega
    _ ≤ (A + B + C) * (2 ^ (p + 1) * (n ^ (p + 1) + 1)) :=
        Nat.mul_le_mul_left _ (succ_pow_le_two_pow_mul n (p + 1))
    _ = (A + B + C) * 2 ^ (p + 1) * (n ^ (p + 1) + 1) := by ring

/-! ### §7.4.2: the clocked runner -/

/-- **Markov truncation at machine level** [AB09, §7.4.2]: a PTM deciding `L` with zero error
in expected time `c(n^e + 1)` yields a PTM deciding `L` in the abort form of
[AB09, Exercise 7.6(a)] in polynomial time.

**Proof sketch.** Run it in the one-shot clocked host for `m = (4c + 1)(n + 1)^{e+1} ≥ 2c(n^e+1)`
steps (`clockHost_abortDecides`). Its answers are correct by zero error; by Markov
(`ZDecidesInTime.truncate`) it has halted, with output `L(x)`, with probability
`≥ 1 - c(n^e+1)/m ≥ 1/2`. -/
theorem _root_.Turing.FinNDTM.ZDecidesInTime.exists_abortDecidesInTime {N : FinNDTM Bool}
    {L : Language Bool} {c e : ℕ} (h : N.ZDecidesInTime L fun n => c * (n ^ e + 1)) :
    ∃ (K E : ℕ) (N' : FinNDTM Bool), N'.AbortDecidesInTime L fun n => K * (n ^ E + 1) := by
  classical
  obtain ⟨S, cS, hS⟩ := FinTM.computesFunInTime_polyUnary (4 * c + 1) (e + 1)
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ → ℕ, m = fun n => (4 * c + 1) * (n + 1) ^ (e + 1) := ⟨_, rfl⟩
  have hS' : S.ComputesFunInTime (fun x => List.replicate (m x.length) true)
      (fun n => cS * (n + 1) ^ (e + 1 + 1)) := by rw [hmdef]; exact hS
  have hpow : ∀ n, n + 1 ≤ (n + 1) ^ (e + 1) := fun n => by
    have := Nat.pow_le_pow_right (show 0 < n + 1 by omega) (show 1 ≤ e + 1 by omega)
    simpa using this
  have hm : ∀ n, n ≤ m n := fun n => by
    have h1 := hpow n
    have h2 : (n + 1) ^ (e + 1) ≤ (4 * c + 1) * (n + 1) ^ (e + 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    simp only [hmdef]
    omega
  have h2B : ∀ n, 2 * (c * (n ^ e + 1)) ≤ m n := fun n => by
    have h1 : n ^ e ≤ (n + 1) ^ (e + 1) :=
      (Nat.pow_le_pow_left (by omega) e).trans (Nat.pow_le_pow_right (by omega) (by omega))
    have h2 : 1 ≤ (n + 1) ^ (e + 1) := Nat.one_le_pow _ _ (by omega)
    have h3 : c * (n ^ e + 1) ≤ c * (2 * (n + 1) ^ (e + 1)) := Nat.mul_le_mul_left _ (by omega)
    simp only [hmdef]
    calc 2 * (c * (n ^ e + 1)) ≤ 2 * (c * (2 * (n + 1) ^ (e + 1))) := Nat.mul_le_mul_left _ h3
      _ = 4 * c * (n + 1) ^ (e + 1) := by ring
      _ ≤ (4 * c + 1) * (n + 1) ^ (e + 1) := Nat.mul_le_mul_right _ (by omega)
  have hab := clockHost_abortDecides S N L m (fun n => cS * (n + 1) ^ (e + 1 + 1)) hS' hm
    (fun x u v _ hv => by
      obtain ⟨h1, h2⟩ := attemptBit_eq_some.mp hv
      have := (h x).2 u h1
      rw [FinNDTM.outputWith, h2] at this
      simpa using this)
    (fun x => by
      have hB1 : (1 : ℚ) ≤ ((c * (x.length ^ e + 1) : ℕ) : ℚ) := (h x).1.one_le
      have hB1' : 1 ≤ c * (x.length ^ e + 1) := by exact_mod_cast hB1
      have hmpos : 0 < m x.length := by have := h2B x.length; omega
      obtain ⟨-, hprob⟩ := h.truncate x hmpos
      have hhalf : ((c * (x.length ^ e + 1) : ℕ) : ℚ) / (m x.length : ℕ) ≤ 1 / 2 := by
        rw [div_le_iff₀ (by exact_mod_cast hmpos)]
        have : ((2 * (c * (x.length ^ e + 1)) : ℕ) : ℚ) ≤ (m x.length : ℕ) := by
          exact_mod_cast h2B x.length
        push_cast at this ⊢
        linarith
      calc (1 : ℚ) / 2 ≤ 1 - ((c * (x.length ^ e + 1) : ℕ) : ℚ) / (m x.length : ℕ) := by
            linarith
        _ ≤ _ := hprob
        _ = _ := randProb_congr fun r => by
            rw [attemptBit_eq_some, FinNDTM.haltRun_eq_some_iff, FinNDTM.outputWith])
  refine ⟨(cS + 2 * (4 * c + 1) + 3) * 2 ^ (e + 1 + 1), e + 1 + 1, _, hab.mono fun n => ?_⟩
  calc cS * (n + 1) ^ (e + 1 + 1) + m n + 2 + (m n + 1)
      = cS * (n + 1) ^ (e + 1 + 1) + 2 * (4 * c + 1) * (n + 1) ^ (e + 1) + 3 := by
        simp only [hmdef]; ring
    _ ≤ _ := add_mul_succ_pow_le _ _ _ n (e + 1)

/-- **`ZPP ⊆ ZPP` (abort form)** [AB09, §7.4.2 and Exercise 7.6(a)], at machine level. -/
theorem ZPP_PTM_subset_ZPPAbort_PTM : ZPP_PTM ⊆ ZPPAbort_PTM := by
  intro L h
  obtain ⟨e, c, N, hN⟩ := Set.mem_iUnion.mp h
  obtain ⟨K, E, N', hN'⟩ := hN.exists_abortDecidesInTime
  exact Set.mem_iUnion.mpr ⟨E, K, N', hN'⟩

/-! ### Exercise 7.6(a), ⇐: restarting a zero-error verifier -/

/-- Keep an output bit `β` as the answer `b` if `β = 1`, drop it otherwise. -/
def keepAs (b : Bool) : Bool → Option Bool := fun β => if β then some b else none

/-- The attempt built from two PTMs: one coin `b` selects `N b`, whose output `1` is read as
the answer `b` and `0` as no answer. -/
def zppAttempt (N : Bool → FinNDTM Bool) : FinNDTM Bool :=
  FinNDTM.coinBranch ((N false).mapOutput (keepAs false)) ((N true).mapOutput (keepAs true))

/-- The attempt has halted under `b :: u` exactly when `N b` has halted under `u`. -/
theorem zppAttempt_halted (N : Bool → FinNDTM Bool) (x : List Bool) (b : Bool)
    (u : List Bool) :
    ((zppAttempt N).tm.runWith (b :: u) ((zppAttempt N).tm.initCfg x)).state = none ↔
      ((N b).tm.runWith u ((N b).tm.initCfg x)).state = none := by
  rw [zppAttempt, FinNDTM.coinBranch_runWith]
  cases b
  · change (FinNDTM.coinBranchCfg₀ _ _ (((N false).tm.mapOutput (keepAs false)).runWith u
      (((N false).tm.mapOutput (keepAs false)).initCfg x))).state = none ↔ _
    rw [NDTM.mapOutput_initCfg, NDTM.mapOutput_runWith]
    simp [FinNDTM.coinBranchCfg₀, NDTM.mapOutputCfg]
  · change (FinNDTM.coinBranchCfg₁ _ _ (((N true).tm.mapOutput (keepAs true)).runWith u
      (((N true).tm.mapOutput (keepAs true)).initCfg x))).state = none ↔ _
    rw [NDTM.mapOutput_initCfg, NDTM.mapOutput_runWith]
    simp [FinNDTM.coinBranchCfg₁, NDTM.mapOutputCfg]

/-- The output of the attempt under `b :: u` is `N b`'s output, filtered by `keepAs b`. -/
theorem zppAttempt_output (N : Bool → FinNDTM Bool) (x : List Bool) (b : Bool)
    (u : List Bool) :
    ((zppAttempt N).tm.runWith (b :: u) ((zppAttempt N).tm.initCfg x)).output =
      ((N b).tm.runWith u ((N b).tm.initCfg x)).output.filterMap (keepAs b) := by
  rw [zppAttempt, FinNDTM.coinBranch_runWith]
  cases b
  · change (FinNDTM.coinBranchCfg₀ _ _ (((N false).tm.mapOutput (keepAs false)).runWith u
      (((N false).tm.mapOutput (keepAs false)).initCfg x))).output = _
    rw [NDTM.mapOutput_initCfg, NDTM.mapOutput_runWith]
    rfl
  · change (FinNDTM.coinBranchCfg₁ _ _ (((N true).tm.mapOutput (keepAs true)).runWith u
      (((N true).tm.mapOutput (keepAs true)).initCfg x))).output = _
    rw [NDTM.mapOutput_initCfg, NDTM.mapOutput_runWith]
    rfl

/-- **Ex 7.6(a), ⇐** [AB09, Exercise 7.6(a) and Def 7.7]: a polynomial-time zero-error
verifier gives a PTM deciding with zero error in expected polynomial time.

**Proof sketch.** For each `b`, `exists_FinNDTM_of_eff` turns the Boolean verifier
"`M(x, r) = some b`" into a PTM `N b` with the same output distribution, every branch outputting
one bit. In the attempt `zppAttempt N` a coin `b` selects `N b`, whose `1` is the answer `b`;
since `M` never answers wrongly, every answer is `L(x)`. With `ℓ = L(x)`, the attempt answers
when the coin is `ℓ` and `M` answers, so with probability at least `1/2 · 1/2`
(`randProb_append_ge`). The restart host with yardstick `m(n) ≥ 1 + max_b T_b(n)` reruns it
(`clockHost_zDecides`). -/
theorem inZPP_subset_ZPP_PTM : {L | InZPP polyTimeModel L} ⊆ ZPP_PTM := by
  classical
  intro L hL
  obtain ⟨M, a, k, hEff, hM⟩ := hL
  have hE : ∀ b : Bool, ∃ (K e : ℕ) (N : FinNDTM Bool), ∀ x : List Bool,
      N.tm.HaltsWithin x (K * (x.length ^ e + 1)) ∧
      (∀ β : Bool, N.outputProb x (K * (x.length ^ e + 1)) [β] =
        randProb (polyLen a k x.length) fun u => decide (M x u = some b) = β) ∧
      ∀ w : List Bool, w.length = K * (x.length ^ e + 1) →
        ∃ r : Fin (polyLen a k x.length) → Bool,
          N.outputWith x w = [decide (M x (List.ofFn r) = some b)] := fun b =>
    exists_FinNDTM_of_eff (polyTimeModel_closedUnderAnswerIs M b hEff)
  choose K e N hN using hE
  obtain ⟨E, hEdef⟩ : ∃ E, E = e false + e true + 1 := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = 2 * (K false + K true) + 2 := ⟨_, rfl⟩
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ → ℕ, m = fun n => C * (n + 1) ^ E := ⟨_, rfl⟩
  have hpowE : ∀ n, n + 1 ≤ (n + 1) ^ E := fun n => by
    have := Nat.pow_le_pow_right (show 0 < n + 1 by omega) (show 1 ≤ E by omega)
    simpa using this
  have hm : ∀ n, n ≤ m n := fun n => by
    have h1 := hpowE n
    have h2 : (n + 1) ^ E ≤ C * (n + 1) ^ E := Nat.le_mul_of_pos_left _ (by omega)
    simp only [hmdef]
    omega
  have hT : ∀ b n, K b * (n ^ e b + 1) + 1 ≤ m n := fun b n => by
    have h1 : n ^ e b ≤ (n + 1) ^ E := (Nat.pow_le_pow_left (by omega) _).trans
      (Nat.pow_le_pow_right (by omega) (by cases b <;> omega))
    have h2 : 1 ≤ (n + 1) ^ E := Nat.one_le_pow _ _ (by omega)
    have hK : K b ≤ K false + K true := by cases b <;> omega
    have h3 : K b * (n ^ e b + 1) ≤ (K false + K true) * (2 * (n + 1) ^ E) :=
      Nat.mul_le_mul hK (by omega)
    have h4 : (K false + K true) * (2 * (n + 1) ^ E) + 1 ≤ C * (n + 1) ^ E := by
      rw [hC]
      calc (K false + K true) * (2 * (n + 1) ^ E) + 1
          = 2 * (K false + K true) * (n + 1) ^ E + 1 := by ring
        _ ≤ 2 * (K false + K true) * (n + 1) ^ E + 2 * (n + 1) ^ E := by omega
        _ = (2 * (K false + K true) + 2) * (n + 1) ^ E := by ring
    simp only [hmdef]
    omega
  -- the attempt on `b :: u` with `|u| ≥ T_b`: `N b` has halted with one bit
  have hcase : ∀ (x : List Bool) (b : Bool) (u : List Bool),
      K b * (x.length ^ e b + 1) ≤ u.length → ∃ r : Fin (polyLen a k x.length) → Bool,
        ((N b).tm.runWith u ((N b).tm.initCfg x)).state = none ∧
        ((N b).tm.runWith u ((N b).tm.initCfg x)).output =
          [decide (M x (List.ofFn r) = some b)] := by
    intro x b u hu
    obtain ⟨hhalt, -, hout⟩ := hN b x
    obtain ⟨r, hr⟩ := hout (u.take _) (List.length_take_of_le hu)
    refine ⟨r, ?_, ?_⟩
    · rw [FinNDTM.runWith_eq_runWith_take hhalt hu]
      exact hhalt _ (List.length_take_of_le hu)
    · rw [FinNDTM.runWith_eq_runWith_take hhalt hu]
      exact hr
  have hbit : ∀ (x : List Bool) (b : Bool) (u : List Bool),
      K b * (x.length ^ e b + 1) ≤ u.length → ∀ v, attemptBit (zppAttempt N) x (b :: u) = some v →
        ∃ r : Fin (polyLen a k x.length) → Bool, M x (List.ofFn r) = some b ∧ v = b := by
    intro x b u hu v hv
    obtain ⟨r, h1, h2⟩ := hcase x b u hu
    rw [attemptBit_eq_some, zppAttempt_output, h2] at hv
    refine ⟨r, ?_⟩
    by_cases hr : M x (List.ofFn r) = some b
    · simp only [hr, decide_true, List.filterMap_cons, keepAs, if_true, List.filterMap_nil,
        List.cons.injEq, and_true] at hv
      exact ⟨hr, hv.2.symm⟩
    · simp [hr, keepAs] at hv
  have hcorr : ∀ x u v, u.length = m x.length → attemptBit (zppAttempt N) x u = some v →
      v = MultiTapeTM.indicator (L : Set (List Bool)) x := by
    intro x u v hu hv
    rcases u with _ | ⟨b, u⟩
    · have := hm x.length; have := hT true x.length; simp at hu; omega
    · obtain ⟨r, hr, hvb⟩ := hbit x b u (by have := hT b x.length; simp at hu; omega) v hv
      subst hvb
      by_cases hx : x ∈ L
      · have := (hM x).1 hx r
        cases v
        · exact absurd hr this
        · simp [MultiTapeTM.indicator, hx]
      · have := (hM x).2.1 hx r
        cases v
        · simp [MultiTapeTM.indicator, hx]
        · exact absurd hr this
  have hprob : ∀ x : List Bool,
      randProb (m x.length) (fun u => attemptBit (zppAttempt N) x u = none) ≤ 3 / 4 := by
    intro x
    obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ, ℓ = MultiTapeTM.indicator (L : Set (List Bool)) x := ⟨_, rfl⟩
    have hm1 : m x.length = 1 + (m x.length - 1) := by have := hT true x.length; omega
    -- `M` answers `ℓ` with probability at least `1/2`
    have hans : 1 / 2 ≤
        randProb (polyLen a k x.length) fun u => decide (M x u = some ℓ) = true := by
      have hle : randProb (polyLen a k x.length) (fun u => ¬ (decide (M x u = some ℓ) = true)) ≤
          randProb (polyLen a k x.length) (fun u => M x u = none) := randProb_mono fun r hr => by
        by_cases hx : x ∈ L
        · have h1 := (hM x).1 hx r
          have hℓ : ℓ = true := by rw [hℓdef]; simp [MultiTapeTM.indicator, hx]
          rw [hℓ] at hr
          cases hMr : M x (List.ofFn r) with
          | none => rfl
          | some β => cases β <;> simp_all
        · have h1 := (hM x).2.1 hx r
          have hℓ : ℓ = false := by rw [hℓdef]; simp [MultiTapeTM.indicator, hx]
          rw [hℓ] at hr
          cases hMr : M x (List.ofFn r) with
          | none => rfl
          | some β => cases β <;> simp_all
      rw [randProb_not] at hle
      linarith [(hM x).2.2]
    -- conditioned on the first coin being `ℓ`, the attempt answers with probability `≥ 1/2`
    have hcond : ∀ u : Fin 1 → Bool, List.ofFn u = [ℓ] → 1 / 2 ≤
        randProb (m x.length - 1)
          (fun v => attemptBit (zppAttempt N) x (List.ofFn u ++ v) ≠ none) := by
      intro u hu
      rw [hu]
      obtain ⟨hhalt, hdist, -⟩ := hN ℓ x
      have hTℓ : K ℓ * (x.length ^ e ℓ + 1) ≤ m x.length - 1 := by have := hT ℓ x.length; omega
      calc (1 : ℚ) / 2 ≤ _ := hans
        _ = (N ℓ).outputProb x (K ℓ * (x.length ^ e ℓ + 1)) [true] := (hdist true).symm
        _ = (N ℓ).outputProb x (m x.length - 1) [true] :=
            (FinNDTM.outputProb_eq_of_haltsWithin hhalt hTℓ _).symm
        _ ≤ _ := randProb_mono fun r hr => by
            obtain ⟨r', h1, h2⟩ := hcase x ℓ (List.ofFn r) (by simpa using hTℓ)
            have h2' := hr
            rw [FinNDTM.outputWith, h2, List.singleton_inj, decide_eq_true_iff] at h2'
            intro hnone
            have hsome : attemptBit (zppAttempt N) x (ℓ :: List.ofFn r) = some ℓ := by
              rw [attemptBit_eq_some, zppAttempt_output, h2]
              refine ⟨(zppAttempt_halted N x ℓ _).mpr h1, ?_⟩
              simp [h2', keepAs]
            rw [List.singleton_append, hsome] at hnone
            exact absurd hnone (by simp)
    have hlow := randProb_append_ge 1 (m x.length - 1) (fun p => p = [ℓ])
      (fun p v => attemptBit (zppAttempt N) x (p ++ v) ≠ none) hcond
    rw [randProb_one_eq, ← hm1] at hlow
    have heq : randProb (m x.length)
          (fun r => attemptBit (zppAttempt N) x (r.take 1 ++ r.drop 1) ≠ none) =
        randProb (m x.length) (fun u => ¬ attemptBit (zppAttempt N) x u = none) :=
      randProb_congr fun r => by rw [List.take_append_drop]
    rw [heq, randProb_not] at hlow
    linarith
  obtain ⟨S, cS, hS⟩ := FinTM.computesFunInTime_polyUnary C E
  have hS' : S.ComputesFunInTime (fun x => List.replicate (m x.length) true)
      (fun n => cS * (n + 1) ^ (E + 1)) := by rw [hmdef]; exact hS
  have hz := clockHost_zDecides S (zppAttempt N) L m (fun n => cS * (n + 1) ^ (E + 1)) hS' hm
    hcorr hprob
  refine Set.mem_iUnion.mpr ⟨E + 1, (cS + 17 * C + 18) * 2 ^ (E + 1), _, hz.mono fun n => ?_⟩
  calc cS * (n + 1) ^ (E + 1) + m n + 2 + 16 * (m n + 1)
      = cS * (n + 1) ^ (E + 1) + 17 * C * (n + 1) ^ E + 18 := by simp only [hmdef]; ring
    _ ≤ _ := add_mul_succ_pow_le _ _ _ n E

/-! ### The equalities -/

/-- **[AB09, Def 7.7 and Exercise 7.6(a)]**: the expected-time class `ZPP` is the
certificate class of polynomial-time zero-error verifiers. -/
theorem ZPP_PTM_eq_setOf_inZPP : ZPP_PTM = {L | InZPP polyTimeModel L} :=
  Set.Subset.antisymm (fun _ h => inZPP_of_mem_ZPP_PTM h) inZPP_subset_ZPP_PTM

/-- `L ∈ ZPP` (Def 7.7) iff `L` has a polynomial-time zero-error verifier. -/
theorem mem_ZPP_PTM_iff (L : Language Bool) : L ∈ ZPP_PTM ↔ InZPP polyTimeModel L := by
  rw [ZPP_PTM_eq_setOf_inZPP]; rfl

/-- **[AB09, Exercise 7.6(a)]** at machine level: the abort-form class equals `ZPP`. -/
theorem ZPPAbort_PTM_eq_ZPP_PTM : ZPPAbort_PTM = ZPP_PTM :=
  Set.Subset.antisymm (fun _ h => inZPP_subset_ZPP_PTM (inZPP_of_mem_ZPPAbort_PTM h))
    ZPP_PTM_subset_ZPPAbort_PTM

/-- A polynomial-time zero-error verifier gives an abort-form PTM. [AB09, Exercise 7.6(a)] -/
theorem inZPP_subset_ZPPAbort_PTM : {L | InZPP polyTimeModel L} ⊆ ZPPAbort_PTM :=
  fun _ h => ZPP_PTM_subset_ZPPAbort_PTM (inZPP_subset_ZPP_PTM h)

/-- **`ZPP = RP ∩ coRP`** [AB09, Theorem 7.8; Exercise 7.6(b)], for the expected-time `ZPP` of
Def 7.7. -/
theorem ZPP_PTM_eq_RP_PTM_inter_coRP_PTM : ZPP_PTM = RP_PTM ∩ coRP_PTM :=
  Set.Subset.antisymm ZPP_PTM_subset_RP_PTM_inter_coRP_PTM fun L ⟨h1, h2⟩ =>
    inZPP_subset_ZPP_PTM ((zpp_eq_rp_inter_corp_polyTime L).mpr
      ⟨(mem_RP_PTM_iff L).mp h1, (mem_coRP_PTM_iff L).mp h2⟩)

end Randomized
