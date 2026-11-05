/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.PTM
import TCSlib.Complexity.ClassP.P
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Archimedean.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Expected running time, ZTIME and ZPP

The running-time random variable `T_{M,x}` of [AB09, §7.3], the zero-error classes of
[AB09, Def 7.7], the Markov truncation of [AB09, §7.4.2], and the two halves of
[AB09, Exercise 7.6(a)] at the level of coin-driven runs.

A *coin run* `r : List Bool → Option α` reports the result after reading a finite coin word
(`none`: still running); it is *prefix-stable* when a result, once produced, survives further
coins. For a PTM, `Turing.FinNDTM.haltRun` is the run on a fixed input. `Pr[T > t]` is
`notHaltedProb r t`, the fraction of `t`-coin words with no result: by prefix stability the
event "not halted after `t` coins" of an infinite fair coin sequence depends on its first `t`
coins only, so this is its exact probability, and `E[T] = ∑_{t ≥ 0} Pr[T > t]`. Hence
"`E[T] ≤ B`" is `ExpTimeLe r B`: every finite tail sum `∑_{t<K} Pr[T > t]` is at most `B`.

## Main definitions

* `Randomized.notHaltedProb`, `Randomized.ExpTimeLe` — `Pr[T > t]` and `E[T] ≤ B`.
* `Turing.FinNDTM.haltRun`, `Turing.FinNDTM.ExpTimeLe` — the same for a PTM on input `x`.
* `Turing.FinNDTM.ZDecidesInTime`, `Randomized.ZTIME`, `Randomized.ZPP_PTM` — [AB09, Def 7.7].
* `Turing.FinNDTM.AbortDecidesInTime`, `Randomized.ZPPAbort_PTM` — the right-hand side of
  [AB09, Exercise 7.6(a)]: polynomial time, outputs in `{0, 1, ?}`, never wrong, `Pr[?] ≤ 1/2`.
* `Randomized.repeatRun` — rerun a fixed-length procedure on fresh coins until it answers.

## Main results

* `Randomized.expTimeLe_repeatRun` — restarting a procedure that answers with probability
  `≥ 1/2` on `t` coins takes at most `2t` coins in expectation.
* `Randomized.notHaltedProb_le_of_le`, `Randomized.notHaltedProb_le_div` (Markov),
  `Randomized.exists_notHaltedProb_le` (halting with probability one).
* `Turing.FinNDTM.expTimeLe_of_haltsWithin` — worst-case time `t₀` gives `E[T] ≤ t₀`.
* `Turing.FinNDTM.haltProb_mono`, `Turing.FinNDTM.haltProb_le_truncate` — [AB09, §7.4.2]:
  cutting the run at `100 B` steps changes the probability of every output by at most `1/100`.
* `Turing.FinNDTM.ZDecidesInTime.flipOutput` — zero error is closed under complement.
* `Turing.FinNDTM.ZDecidesInTime.truncate` — the zero-error form of the same truncation.
* `Turing.FinNDTM.ZDecidesInTime.abort` and `Turing.FinNDTM.AbortDecidesInTime.restart` —
  the two directions of [AB09, Exercise 7.6(a)]; `Randomized.InZPP.restart` for `InZPP`.
* `Randomized.P_subset_ZPP_PTM`.

## Divergences

* The book's `O(T(n))` is `c · T` with `c : ℕ`, and `ZPP` uses the bounds `n^c + 1`, as for
  `Randomized.BPTIME`. Output `?` is any output other than `[0]`/`[1]` (cf. `PTM.lean`).
* This file states the coin-level behaviour of the machines of §7.4.2 and Exercise 7.6(a):
  the run cut at `t` steps (`haltRun` on `t` coins), and `repeatRun` of the abort-form
  output. The machines themselves are the clocked restart host
  `Turing.FinNDTM.clockHost` (`TCSlib.Complexity.TuringMachine.Build.NDClockHost`); the
  machine-level equalities, e.g. `Randomized.ZPPAbort_PTM_eq_ZPP_PTM`, are in
  `TCSlib.Complexity.Randomized.ZPPHostsClasses`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open Finset

variable {α : Type*}

/-! ### Coin runs -/

/-- A result, once produced, survives any further coins. -/
def IsPrefixStable (r : List Bool → Option α) : Prop :=
  ∀ (w v : List Bool) (a : α), r w = some a → r (w ++ v) = some a

variable {r : List Bool → Option α} {q : List Bool → Option α} {t : ℕ}

/-- A result on a prefix is the result on the whole word. -/
theorem IsPrefixStable.of_take (h : IsPrefixStable r) {w : List Bool} {t : ℕ} {a : α}
    (ha : r (w.take t) = some a) : r w = some a := by
  simpa only [List.take_append_drop] using h (w.take t) (w.drop t) a ha

/-- No result on a word means no result on any prefix. -/
theorem IsPrefixStable.take_eq_none (h : IsPrefixStable r) {w : List Bool} (t : ℕ)
    (hw : r w = none) : r (w.take t) = none := by
  cases ha : r (w.take t) with
  | none => rfl
  | some a => rw [h.of_take ha] at hw; exact absurd hw (by simp)

/-! ### Restarting a fixed-length procedure -/

/-- Read the coins in blocks of `t`, run `q` on each block, and return the first answer.
[AB09, Exercise 7.6(a)] -/
def repeatRun (q : List Bool → Option α) (t : ℕ) (w : List Bool) : Option α :=
  if 0 < t ∧ t ≤ w.length then (q (w.take t)).or (repeatRun q t (w.drop t)) else none
termination_by w.length
decreasing_by simp only [List.length_drop]; omega

/-- With a full block available, `repeatRun` tries `q` on it, then reruns on the rest. -/
theorem repeatRun_of_le (ht : 0 < t) {w : List Bool} (hw : t ≤ w.length) :
    repeatRun q t w = (q (w.take t)).or (repeatRun q t (w.drop t)) := by
  rw [repeatRun, if_pos ⟨ht, hw⟩]

/-- Without a full block, `repeatRun` has no result. -/
theorem repeatRun_of_lt {w : List Bool} (hw : w.length < t) : repeatRun q t w = none := by
  rw [repeatRun, if_neg (by omega)]

/-- `repeatRun` is a prefix-stable run. -/
theorem repeatRun_isPrefixStable (q : List Bool → Option α) (t : ℕ) :
    IsPrefixStable (repeatRun q t) := by
  intro w
  induction hn : w.length using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    intro v a ha
    by_cases hw : 0 < t ∧ t ≤ w.length
    · have hwv : t ≤ (w ++ v).length := by simp; omega
      rw [repeatRun_of_le hw.1 hw.2] at ha
      rw [repeatRun_of_le hw.1 hwv, List.take_append_of_le_length hw.2,
        List.drop_append_of_le_length hw.2]
      cases hq : q (w.take t) with
      | some b => rw [hq] at ha; exact ha
      | none =>
        rw [hq, Option.none_or] at ha
        rw [Option.none_or]
        exact ih _ (by simp; omega) _ rfl v a ha
    · rw [repeatRun, if_neg hw] at ha; exact absurd ha (by simp)

/-- Every answer of `repeatRun` is an answer of `q` on some block of length `t`. -/
theorem exists_of_repeatRun_eq_some {w : List Bool} {a : α} (h : repeatRun q t w = some a) :
    ∃ u : List Bool, u.length = t ∧ q u = some a := by
  induction hn : w.length using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    by_cases hw : 0 < t ∧ t ≤ w.length
    · rw [repeatRun_of_le hw.1 hw.2] at h
      cases hq : q (w.take t) with
      | some b =>
        rw [hq, Option.some_or] at h
        exact ⟨w.take t, List.length_take_of_le hw.2, hq.trans h⟩
      | none =>
        rw [hq, Option.none_or] at h
        exact ih _ (by simp; omega) h rfl
    · rw [repeatRun, if_neg hw] at h; exact absurd h (by simp)

/-! ### Tail sums -/

section TailSums

variable [DecidableEq α]

/-- `Pr[T > t]`: the probability over `t` fair coins that the run has produced no result.
[AB09, §7.3: the random variable `T_{M,x}`] -/
def notHaltedProb (r : List Bool → Option α) (t : ℕ) : ℚ :=
  randProb t fun w => r w = none

/-- `E[T] ≤ B`: every tail sum `∑_{t<K} Pr[T > t]` is at most `B`. [AB09, §7.3] -/
def ExpTimeLe (r : List Bool → Option α) (B : ℚ) : Prop :=
  ∀ K : ℕ, ∑ t ∈ range K, notHaltedProb r t ≤ B

/-- `Pr[T > t] ≥ 0`. -/
theorem notHaltedProb_nonneg (t : ℕ) : 0 ≤ notHaltedProb r t := randProb_nonneg

/-- `Pr[T > t] ≤ 1`. -/
theorem notHaltedProb_le_one (t : ℕ) : notHaltedProb r t ≤ 1 := randProb_le_one

/-- `Pr[T > t]` is antitone in `t`. -/
theorem notHaltedProb_le_of_le (h : IsPrefixStable r) {s t : ℕ} (hst : s ≤ t) :
    notHaltedProb r t ≤ notHaltedProb r s := by
  unfold notHaltedProb
  rw [← randProb_take hst (fun w => r w = none)]
  exact randProb_mono fun w hw => h.take_eq_none s hw

/-- The bound in `ExpTimeLe` is nonnegative. -/
theorem ExpTimeLe.nonneg {B : ℚ} (hB : ExpTimeLe r B) : 0 ≤ B := by
  simpa using hB 0

/-- `t · Pr[T > t] ≤ E[T]`, the form of Markov's inequality used in [AB09, §7.4.2]. -/
theorem mul_notHaltedProb_le (h : IsPrefixStable r) {B : ℚ} (hB : ExpTimeLe r B) (t : ℕ) :
    (t : ℚ) * notHaltedProb r t ≤ B :=
  calc (t : ℚ) * notHaltedProb r t = ∑ _s ∈ range t, notHaltedProb r t := by simp
    _ ≤ ∑ s ∈ range t, notHaltedProb r s :=
        sum_le_sum fun s hs => notHaltedProb_le_of_le h (mem_range.1 hs).le
    _ ≤ B := hB t

/-- **Markov's inequality** [AB09, Lemma A.7]: `Pr[T > t] ≤ E[T] / t`. -/
theorem notHaltedProb_le_div (h : IsPrefixStable r) {B : ℚ} (hB : ExpTimeLe r B) {t : ℕ}
    (ht : 0 < t) : notHaltedProb r t ≤ B / t := by
  rw [le_div_iff₀ (by exact_mod_cast ht), mul_comm]
  exact mul_notHaltedProb_le h hB t

/-- Finite expected time forces halting with probability one: `Pr[T > t] → 0`. -/
theorem exists_notHaltedProb_le (h : IsPrefixStable r) {B : ℚ} (hB : ExpTimeLe r B)
    {ε : ℚ} (hε : 0 < ε) : ∃ t : ℕ, notHaltedProb r t ≤ ε := by
  obtain ⟨n, ht⟩ := exists_nat_gt (B / ε)
  have hn : 0 < n := by
    exact_mod_cast (div_nonneg hB.nonneg hε.le).trans_lt ht
  refine ⟨n, (notHaltedProb_le_div h hB hn).trans ?_⟩
  rw [div_le_iff₀ (by positivity)]
  rw [div_lt_iff₀ hε] at ht
  linarith

/-- `Pr[result v within t coins]` is monotone in `t`. -/
theorem randProb_eq_some_mono (h : IsPrefixStable r) (v : α) {t t' : ℕ}
    (ht : t ≤ t') :
    randProb t (fun w => r w = some v) ≤ randProb t' (fun w => r w = some v) := by
  rw [← randProb_take ht (fun w => r w = some v)]
  exact randProb_mono fun w hw => h.of_take hw

/-- **Truncation** [AB09, §7.4.2]: the probability of a result `v` after any number `t'` of
coins exceeds that after `t` coins by at most `Pr[T > t]`.

**Proof sketch.** For `t' ≤ t` a result at `t'` coins persists to `t`. For `t' > t`, a run
that yields `v` at `t'` coins either has yielded `v` after its first `t` coins or has
yielded nothing then; prefix stability excludes a different early result. -/
theorem randProb_eq_some_le (h : IsPrefixStable r) (v : α) (t t' : ℕ) :
    randProb t' (fun w => r w = some v) ≤
      randProb t (fun w => r w = some v) + notHaltedProb r t := by
  have h0 : 0 ≤ notHaltedProb r t := notHaltedProb_nonneg t
  rcases le_total t' t with ht | ht
  · exact le_add_of_le_of_nonneg (randProb_eq_some_mono h v ht) h0
  · unfold notHaltedProb
    rw [← randProb_take ht (fun w => r w = some v), ← randProb_take ht (fun w => r w = none),
      ← randProb_or_disjoint _ _ fun w ⟨h1, h2⟩ => by rw [h1] at h2; exact absurd h2 (by simp)]
    refine randProb_mono fun w hw => ?_
    cases hc : r ((List.ofFn w).take t) with
    | none => exact Or.inr rfl
    | some a => rw [h.of_take hc] at hw; exact Or.inl hw

/-- A run that has a result on every `t₀`-coin word has `E[T] ≤ t₀`.

**Proof sketch.** `Pr[T > s] = 0` for `s ≥ t₀` by prefix stability and `≤ 1` otherwise, so
by induction `∑_{s<K} Pr[T > s] ≤ min K t₀`. -/
theorem expTimeLe_of_forall_ne_none (h : IsPrefixStable r) {t₀ : ℕ}
    (hhalt : ∀ w : List Bool, w.length = t₀ → r w ≠ none) : ExpTimeLe r t₀ := by
  have hzero : ∀ s, t₀ ≤ s → notHaltedProb r s = 0 := fun s hs => by
    unfold notHaltedProb
    rw [randProb_congr (B := fun _ => False) fun w => ?_, randProb_false]
    refine iff_false_intro fun hw => hhalt _ ?_ (h.take_eq_none t₀ hw)
    rw [List.length_take, List.length_ofFn, Nat.min_eq_left hs]
  have hsum : ∀ K, ∑ s ∈ range K, notHaltedProb r s ≤ (min K t₀ : ℕ) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [sum_range_succ]
      rcases lt_or_ge K t₀ with hK | hK
      · rw [Nat.min_eq_left (by omega : K + 1 ≤ t₀)] at *
        rw [Nat.min_eq_left hK.le] at ih
        push_cast
        linarith [notHaltedProb_le_one (r := r) K]
      · rw [hzero K hK, add_zero, Nat.min_eq_right (by omega : t₀ ≤ K + 1)]
        rwa [Nat.min_eq_right hK] at ih
  exact fun K => (hsum K).trans (by exact_mod_cast Nat.min_le_right K t₀)

/-- `Pr[T > m t + s] = a^m` for `s < t`, where `a` is the probability that `q` answers
nothing: the first `m` blocks must all fail. -/
theorem notHaltedProb_repeatRun (ht : 0 < t) (m : ℕ) {s : ℕ} (hs : s < t) :
    notHaltedProb (repeatRun q t) (m * t + s) = (randProb t fun u => q u = none) ^ m := by
  induction m with
  | zero =>
    unfold notHaltedProb
    rw [pow_zero, zero_mul, zero_add,
      randProb_congr (B := fun _ => True) fun w => by
        simp [repeatRun_of_lt (q := q) (show (List.ofFn w).length < t by simpa using hs)]]
    exact randProb_true
  | succ m ih =>
    unfold notHaltedProb at ih ⊢
    rw [show (m + 1) * t + s = t + (m * t + s) by ring, pow_succ', ← ih,
      ← randProb_split t (m * t + s) (fun u => q u = none) (fun u => repeatRun q t u = none)]
    refine randProb_congr fun w => ?_
    rw [repeatRun_of_le ht (by simp), Option.or_eq_none_iff]

/-- **Restarting** [AB09, Exercise 7.6(a)]: if `q` answers nothing with probability at most
`1/2` on `t > 0` coins, then rerunning it until it answers takes at most `2t` coins in
expectation.

**Proof sketch.** With `a ≤ 1/2` the failure probability of one block,
`Pr[T > K] = a^⌊K/t⌋`. Summing over the first `n` blocks gives `t · ∑_{j<n} a^j ≤ t/(1-a)`,
and every tail sum is dominated by such a block sum since all terms are nonnegative. -/
theorem expTimeLe_repeatRun (ht : 0 < t) (ha : (randProb t fun u => q u = none) ≤ 1 / 2) :
    ExpTimeLe (repeatRun q t) (2 * t) := by
  set a := randProb t fun u => q u = none
  have ha0 : 0 ≤ a := randProb_nonneg
  have hblock : ∀ n, ∑ K ∈ range (n * t), notHaltedProb (repeatRun q t) K =
      t * ∑ j ∈ range n, a ^ j := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ, mul_add]
      congr 1
      rw [sum_congr rfl fun s hs => notHaltedProb_repeatRun ht n (mem_range.1 hs), sum_const,
        card_range, nsmul_eq_mul]
  intro K
  have hgeom : ∑ j ∈ range K, a ^ j ≤ 2 := by
    have := geom_sum_Ico_le_of_lt_one ha0 (by linarith : a < 1) (m := 0) (n := K)
    rw [← range_eq_Ico, pow_zero] at this
    exact this.trans (by rw [div_le_iff₀ (by linarith)]; linarith)
  calc ∑ s ∈ range K, notHaltedProb (repeatRun q t) s
      ≤ ∑ s ∈ range (K * t), notHaltedProb (repeatRun q t) s :=
        sum_le_sum_of_subset_of_nonneg (range_mono (Nat.le_mul_of_pos_right K ht))
          fun _ _ _ => notHaltedProb_nonneg _
    _ = t * ∑ j ∈ range K, a ^ j := hblock K
    _ ≤ t * 2 := by gcongr
    _ = 2 * t := mul_comm _ _

end TailSums

end Randomized

namespace Turing.FinNDTM

open Randomized

/-! ### The running time of a PTM -/

/-- The run of the PTM `N` on `x` as a coin run: its output once halted within `|w|` steps
under the coins `w`, and `none` otherwise. -/
def haltRun (N : FinNDTM Bool) (x w : List Bool) : Option (List Bool) :=
  if (N.tm.runWith w (N.tm.initCfg x)).state = none then some (N.outputWith x w) else none

/-- `E[T_{N,x}] ≤ B`. [AB09, §7.3] -/
def ExpTimeLe (N : FinNDTM Bool) (x : List Bool) (B : ℚ) : Prop :=
  Randomized.ExpTimeLe (N.haltRun x) B

variable {N : FinNDTM Bool} {x : List Bool}

/-- `haltRun` is the halted output. -/
theorem haltRun_eq_some_iff {w o : List Bool} :
    N.haltRun x w = some o ↔
      (N.tm.runWith w (N.tm.initCfg x)).state = none ∧ N.outputWith x w = o := by
  unfold haltRun
  by_cases h : (N.tm.runWith w (N.tm.initCfg x)).state = none
  · rw [if_pos h, Option.some.injEq]; exact ⟨fun e => ⟨h, e⟩, fun e => e.2⟩
  · rw [if_neg h]; exact ⟨fun e => absurd e (by simp), fun e => absurd e.1 h⟩

/-- `haltRun` is `none` exactly while the run is live. -/
theorem haltRun_eq_none_iff {w : List Bool} :
    N.haltRun x w = none ↔ (N.tm.runWith w (N.tm.initCfg x)).state ≠ none := by
  unfold haltRun
  by_cases h : (N.tm.runWith w (N.tm.initCfg x)).state = none
  · rw [if_pos h]; exact ⟨fun e => absurd e (by simp), fun e => absurd h e⟩
  · rw [if_neg h]; exact ⟨fun _ => h, fun _ => rfl⟩

/-- Further coins do not change a halted run. -/
theorem haltRun_isPrefixStable (N : FinNDTM Bool) (x : List Bool) :
    IsPrefixStable (N.haltRun x) := by
  intro w v o hw
  rw [haltRun_eq_some_iff] at hw ⊢
  have hrun : N.tm.runWith (w ++ v) (N.tm.initCfg x) = N.tm.runWith w (N.tm.initCfg x) := by
    rw [NDTM.runWith_append, NDTM.runWith_of_halt _ hw.1]
  exact ⟨hrun ▸ hw.1, by rw [outputWith, hrun]; exact hw.2⟩

/-- A PTM has not halted before its first step: `Pr[T > 0] = 1`. -/
theorem notHaltedProb_haltRun_zero : notHaltedProb (N.haltRun x) 0 = 1 := by
  unfold notHaltedProb
  rw [randProb_congr (B := fun _ => True) fun w => by
    simp [List.ofFn_zero, haltRun_eq_none_iff, NDTM.initCfg, Cfg.init]]
  exact randProb_true

/-- Every run takes at least one step: `E[T] ≤ B` forces `1 ≤ B`. -/
theorem ExpTimeLe.one_le {B : ℚ} (h : N.ExpTimeLe x B) : 1 ≤ B := by
  simpa [notHaltedProb_haltRun_zero] using h 1

/-- A PTM halting within `t₀` steps on every branch has `E[T] ≤ t₀`. [AB09, §7.3] -/
theorem expTimeLe_of_haltsWithin {t₀ : ℕ} (h : N.tm.HaltsWithin x t₀) : N.ExpTimeLe x t₀ :=
  expTimeLe_of_forall_ne_none (N.haltRun_isPrefixStable x) fun w hw => by
    rw [Ne, haltRun_eq_none_iff, not_not]; exact h w hw

/-- `Pr[T > t]` for a PTM is antitone in `t`. -/
theorem notHaltedProb_haltRun_antitone (N : FinNDTM Bool) (x : List Bool) :
    Antitone (notHaltedProb (N.haltRun x)) :=
  fun _ _ hst => notHaltedProb_le_of_le (N.haltRun_isPrefixStable x) hst

/-- `Pr[N halts on x with output v within t steps]` is monotone in `t`. -/
theorem haltProb_mono (v : List Bool) {t t' : ℕ} (ht : t ≤ t') :
    randProb t (fun w => N.haltRun x w = some v) ≤
      randProb t' (fun w => N.haltRun x w = some v) :=
  randProb_eq_some_mono (N.haltRun_isPrefixStable x) v ht

/-- **Markov truncation** [AB09, §7.4.2]: if `E[T_{N,x}] ≤ B`, then for every `t'`,
`Pr_{t'}[halted with v] ≤ Pr_{100B}[halted with v] + 1/100`; together with
`haltProb_mono` (`≥` for `t' ≥ 100 B`), cutting the run at `100 B` steps changes the
probability of halting with output `v` by at most `1/100`. -/
theorem haltProb_le_truncate {B : ℕ} (hB : N.ExpTimeLe x B) (v : List Bool) (t' : ℕ) :
    randProb t' (fun w => N.haltRun x w = some v) ≤
      randProb (100 * B) (fun w => N.haltRun x w = some v) + 1 / 100 := by
  have hB1 : (1 : ℚ) ≤ B := hB.one_le
  have hpos : 0 < 100 * B := by
    have : 1 ≤ B := by exact_mod_cast hB1
    omega
  refine (randProb_eq_some_le (N.haltRun_isPrefixStable x) v (100 * B) t').trans ?_
  have hm := notHaltedProb_le_div (N.haltRun_isPrefixStable x) hB hpos
  rw [Nat.cast_mul, Nat.cast_ofNat, div_mul_eq_div_div_swap, div_self (by positivity)] at hm
  linarith

/-! ### Zero error: ZTIME and ZPP -/

/-- `N` decides `L` with zero error in expected time `T`: `E[T_{N,x}] ≤ T(|x|)`, and every
halted branch outputs `[L(x)]`. [AB09, Def 7.7] -/
def ZDecidesInTime (N : FinNDTM Bool) (L : Language Bool) (T : ℕ → ℕ) : Prop :=
  ∀ x : List Bool, N.ExpTimeLe x (T x.length) ∧
    ∀ w : List Bool, (N.tm.runWith w (N.tm.initCfg x)).state = none →
      N.outputWith x w = [MultiTapeTM.indicator (L : Set (List Bool)) x]

/-- `N` decides `L` in time `T` with abort: every branch halts within `T(|x|)` steps, never
outputs the wrong bit, and outputs `[L(x)]` with probability at least `1/2`.
[AB09, Exercise 7.6(a)] -/
def AbortDecidesInTime (N : FinNDTM Bool) (L : Language Bool) (T : ℕ → ℕ) : Prop :=
  ∀ x : List Bool, N.tm.HaltsWithin x (T x.length) ∧
    (∀ w : List Bool, w.length = T x.length →
      N.outputWith x w ≠ [!MultiTapeTM.indicator (L : Set (List Bool)) x]) ∧
    1 / 2 ≤ N.outputProb x (T x.length) [MultiTapeTM.indicator (L : Set (List Bool)) x]

variable {L : Language Bool} {T : ℕ → ℕ}

/-- A zero-error run that is cut at `t > 0` steps outputs `[L(x)]` with probability at least
`1 - T(|x|)/t`, and never outputs anything else. [AB09, §7.4.2]

**Proof sketch.** Every halted output is `[L(x)]` by zero error, so "halted with `[L(x)]`" is
"halted". By Markov (`notHaltedProb_le_div`) the run is still going after `t` steps with
probability at most `T(|x|)/t`. -/
theorem ZDecidesInTime.truncate (h : N.ZDecidesInTime L T) (x : List Bool) {t : ℕ}
    (ht : 0 < t) :
    (∀ w o, N.haltRun x w = some o →
      o = [MultiTapeTM.indicator (L : Set (List Bool)) x]) ∧
    1 - (T x.length : ℚ) / t ≤
      randProb t (fun w =>
        N.haltRun x w = some [MultiTapeTM.indicator (L : Set (List Bool)) x]) := by
  obtain ⟨hexp, hcorr⟩ := h x
  refine ⟨fun w o hw => ?_, ?_⟩
  · rw [haltRun_eq_some_iff] at hw
    exact hw.2.symm.trans (hcorr w hw.1)
  · have hm := notHaltedProb_le_div (N.haltRun_isPrefixStable x) hexp ht
    have hc : randProb t (fun w => N.haltRun x w =
        some [MultiTapeTM.indicator (L : Set (List Bool)) x]) =
        1 - notHaltedProb (N.haltRun x) t := by
      unfold notHaltedProb
      rw [← randProb_not]
      refine randProb_congr fun w => ?_
      rw [haltRun_eq_some_iff, haltRun_eq_none_iff, not_not]
      exact ⟨fun h => h.1, fun h => ⟨h, hcorr _ h⟩⟩
    rw [hc]
    linarith

/-- **Ex 7.6(a), ⇒** [AB09, Exercise 7.6(a)]: a zero-error machine cut at `2T(|x|)` steps,
with `?` on timeout, is never wrong and answers with probability at least `1/2`. -/
theorem ZDecidesInTime.abort (h : N.ZDecidesInTime L T) (x : List Bool) :
    (∀ w o, N.haltRun x w = some o →
      o = [MultiTapeTM.indicator (L : Set (List Bool)) x]) ∧
    1 / 2 ≤ randProb (2 * T x.length)
      (fun w => N.haltRun x w = some [MultiTapeTM.indicator (L : Set (List Bool)) x]) := by
  have hT : (1 : ℚ) ≤ T x.length := (h x).1.one_le
  have hT' : 0 < T x.length := by exact_mod_cast (zero_lt_one.trans_le hT)
  obtain ⟨h1, h2⟩ := h.truncate x (t := 2 * T x.length) (by omega)
  refine ⟨h1, le_trans (le_of_eq ?_) h2⟩
  push_cast
  field_simp
  norm_num

/-- `flipOutput` halts exactly when `N` does, with the negated output. -/
theorem haltRun_flipOutput (w : List Bool) :
    N.flipOutput.haltRun x w = (N.haltRun x w).map (List.map not) := by
  have hst : (N.flipOutput.tm.runWith w (N.flipOutput.tm.initCfg x)).state =
      (N.tm.runWith w (N.tm.initCfg x)).state := by
    show (N.tm.flipOutput.runWith w (N.tm.flipOutput.initCfg x)).state = _
    rw [NDTM.flipOutput_initCfg, NDTM.flipOutput_runWith]; rfl
  unfold haltRun
  rw [hst, flipOutput_outputWith]
  split_ifs <;> rfl

/-- Negating the output turns a zero-error decider for `L` into one for `Lᶜ`. -/
theorem ZDecidesInTime.flipOutput (h : N.ZDecidesInTime L T) :
    N.flipOutput.ZDecidesInTime Lᶜ T := by
  classical
  intro x
  obtain ⟨hexp, hcorr⟩ := h x
  refine ⟨fun K => le_of_eq_of_le (Finset.sum_congr rfl fun t _ => ?_) (hexp K), fun w hw => ?_⟩
  · unfold notHaltedProb
    exact randProb_congr fun r => by rw [haltRun_flipOutput, Option.map_eq_none_iff]
  · have h1 : N.flipOutput.haltRun x w = some (N.flipOutput.outputWith x w) := by
      unfold haltRun; rw [if_pos hw]
    rw [haltRun_flipOutput, Option.map_eq_some_iff] at h1
    obtain ⟨o, ho, heq⟩ := h1
    rw [haltRun_eq_some_iff] at ho
    rw [← heq, ← ho.2, hcorr w ho.1]
    by_cases hx : x ∈ L
    · have hxc : x ∉ (Lᶜ : Language Bool) := fun h => h hx
      simp [MultiTapeTM.indicator, hx, hxc]
    · have hxc : x ∈ (Lᶜ : Language Bool) := hx
      simp [MultiTapeTM.indicator, hx, hxc]

/-- The answer `q` reads off an abort-form output: `[b]` gives `b`, anything else `?`. -/
def bitOfOutput : List Bool → Option Bool
  | [b] => some b
  | _ => none

/-- **Ex 7.6(a), ⇐** [AB09, Exercise 7.6(a)]: rerunning an abort-form machine on fresh coins
until it answers is never wrong and uses at most `2T(|x|)` coins in expectation.

**Proof sketch.** `T(|x|) > 0`, since the initial configuration is live. One block answers
nothing only if its output is not `[L(x)]`, which has probability at most `1/2`, so
`expTimeLe_repeatRun` bounds the expectation by `2T(|x|)`. Every answer `b` of the restarted
run is read off some block whose output is `[b]`; the output is never `[¬L(x)]`, so
`b = L(x)`. -/
theorem AbortDecidesInTime.restart (h : N.AbortDecidesInTime L T) (x : List Bool) :
    Randomized.ExpTimeLe (repeatRun (fun u => bitOfOutput (N.outputWith x u)) (T x.length))
      (2 * T x.length) ∧
    ∀ w b, repeatRun (fun u => bitOfOutput (N.outputWith x u)) (T x.length) w = some b →
      b = MultiTapeTM.indicator (L : Set (List Bool)) x := by
  obtain ⟨hhalt, hwrong, hprob⟩ := h x
  unfold outputProb at hprob
  set ℓ := MultiTapeTM.indicator (L : Set (List Bool)) x
  have hT : 0 < T x.length := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    have := hhalt [] (by simp [h0])
    simp [NDTM.initCfg, Cfg.init] at this
  refine ⟨expTimeLe_repeatRun hT ?_, fun w b hw => ?_⟩
  · show (randProb (T x.length) fun u => bitOfOutput (N.outputWith x u) = none) ≤ 1 / 2
    have hle : (randProb (T x.length) fun u => bitOfOutput (N.outputWith x u) = none) ≤
        randProb (T x.length) fun u => ¬ N.outputWith x u = [ℓ] :=
      randProb_mono fun u hu heq => by rw [heq] at hu; exact absurd hu (by simp [bitOfOutput])
    rw [randProb_not] at hle
    linarith
  · obtain ⟨u, hu, hb⟩ := exists_of_repeatRun_eq_some hw
    have hout : N.outputWith x u = [b] := by
      revert hb; unfold bitOfOutput; split <;> simp_all
    have := hwrong u hu
    rw [hout] at this
    cases b <;> cases hℓ : ℓ <;> simp_all

end Turing.FinNDTM

namespace Randomized

open Turing Complexity

/-- `ZTIME(T)`: languages decided with zero error by a PTM in expected time `c · T`.
[AB09, Def 7.7] -/
def ZTIME (T : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (N : FinNDTM Bool), N.ZDecidesInTime L fun n => c * T n}

/-- `ZPP = ⋃_c ZTIME(n^c + 1)`. [AB09, Def 7.7] -/
def ZPP_PTM : Set (Language Bool) := ⋃ c : ℕ, ZTIME fun n => n ^ c + 1

/-- The abort-form class of [AB09, Exercise 7.6(a)]: polynomial-time PTMs with outputs in
`{0, 1, ?}`, never wrong, with `Pr[?] ≤ 1/2`. -/
def ZPPAbort_PTM : Set (Language Bool) :=
  ⋃ c : ℕ, {L | ∃ (a : ℕ) (N : FinNDTM Bool), N.AbortDecidesInTime L fun n => a * (n ^ c + 1)}

/-- `ZTIME` is monotone in the time bound. -/
theorem ZTIME.mono {T₁ T₂ : ℕ → ℕ} (h : ∀ n, T₁ n ≤ T₂ n) : ZTIME T₁ ⊆ ZTIME T₂ := by
  rintro L ⟨c, N, hN⟩
  refine ⟨c, N, fun x => ⟨fun K => ((hN x).1 K).trans ?_, (hN x).2⟩⟩
  exact_mod_cast Nat.mul_le_mul_left c (h _)

/-- `DTIME(T) ⊆ ZTIME(T)`: a deterministic machine never errs and halts within its bound.
[AB09, §7.3] -/
theorem DTIME_subset_ZTIME (T : ℕ → ℕ) : DTIME T ⊆ ZTIME T := by
  classical
  rintro L ⟨c, M, hM⟩
  refine ⟨c, M.toFinNDTM, fun x => ?_⟩
  obtain ⟨hhalt, hout⟩ := (M.computesInTime_iff _ _ _).mp (hM x)
  have hrun : ∀ w : List Bool, M.toFinNDTM.tm.runWith w (M.toFinNDTM.tm.initCfg x) =
      M.tm.runFrom (M.tm.initCfg x) w.length := fun w =>
    M.tm.toNDTM_runWith w (M.tm.initCfg x)
  refine ⟨FinNDTM.expTimeLe_of_haltsWithin fun w hw => by rw [hrun, hw]; exact hhalt,
    fun w hw => ?_⟩
  rw [FinNDTM.outputWith, hrun]
  rw [hrun] at hw
  rcases le_total w.length (c * T x.length) with hle | hle
  · rw [← M.tm.runFrom_output_eq_of_halt _ hle hw]; exact hout
  · rw [M.tm.runFrom_output_eq_of_halt _ hle hhalt]; exact hout

/-- `ZTIME(T)` is closed under complement. -/
theorem compl_mem_ZTIME {T : ℕ → ℕ} {L : Language Bool} (h : L ∈ ZTIME T) : Lᶜ ∈ ZTIME T := by
  obtain ⟨c, N, hN⟩ := h
  exact ⟨c, N.flipOutput, hN.flipOutput⟩

/-- **`P ⊆ ZPP`** (PTM form). [AB09, §7.3] -/
theorem P_subset_ZPP_PTM : P ⊆ ZPP_PTM :=
  Set.iUnion_mono fun _ => DTIME_subset_ZTIME _

/-- **Restarting an `InZPP` verifier** [AB09, Exercise 7.6(a)]: for `L ∈ InZPP E`, rerunning
the verifier on fresh blocks of `p(|x|) + 1` coins until it answers is never wrong and uses at
most `2(p(|x|) + 1)` coins in expectation.

**Proof sketch.** Each block answers `none` with probability at most `1/2` (only its first
`p(|x|)` coins are read, `randProb_take`), so `expTimeLe_repeatRun` bounds the expected number
of coins; an answer comes from some block (`exists_of_repeatRun_eq_some`), and the verifier
is never wrong on any block. -/
theorem InZPP.restart {E : VerifierModel} {L : Language Bool} (h : InZPP E L) :
    ∃ (M : List Bool → List Bool → Option Bool) (a k : ℕ), E.Eff M ∧ ∀ x : List Bool,
      ExpTimeLe (repeatRun (fun u => M x (u.take (polyLen a k x.length)))
        (polyLen a k x.length + 1)) (2 * (polyLen a k x.length + 1)) ∧
      ∀ w b, repeatRun (fun u => M x (u.take (polyLen a k x.length)))
        (polyLen a k x.length + 1) w = some b → (b = true ↔ x ∈ L) := by
  obtain ⟨M, a, k, hEff, hM⟩ := h
  refine ⟨M, a, k, hEff, fun x => ⟨?_, fun w b hw => ?_⟩⟩
  · have := expTimeLe_repeatRun (q := fun u => M x (u.take (polyLen a k x.length)))
      (t := polyLen a k x.length + 1) (Nat.succ_pos _)
      (by show (randProb (polyLen a k x.length + 1) fun u =>
            M x (u.take (polyLen a k x.length)) = none) ≤ 1 / 2
          rw [randProb_take (Nat.le_succ _) (fun u => M x u = none)]; exact (hM x).2.2)
    exact_mod_cast this
  · obtain ⟨u, hu, hb⟩ := exists_of_repeatRun_eq_some hw
    obtain ⟨r, hr⟩ := exists_ofFn_eq (l := u.take (polyLen a k x.length))
      (m := polyLen a k x.length) (by simp [hu])
    rw [hr] at hb
    by_cases hx : x ∈ L
    · have := (hM x).1 hx r
      cases b <;> simp_all
    · have := (hM x).2.1 hx r
      cases b <;> simp_all

end Randomized
