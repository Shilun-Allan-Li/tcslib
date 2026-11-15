/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.TuringMachine.Build.NDClockHostRun
import TCSlib.Complexity.Randomized.ZPPEquiv

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Zero-error machines from the clocked restart host

The probabilistic contracts of the clocked restart host `Turing.FinNDTM.clockHost`
(`TCSlib.Complexity.TuringMachine.Build.NDClockHostRun`) on a PTM `A`: run `A` against a clock
of `m` coins and accept only a one-bit answer.

* With restarts, if every answer is correct and an attempt fails with probability at most
  `3/4`, the host decides with zero error in expected time `s₀ + 16(m + 1)`
  [AB09, Def 7.7 and Exercise 7.6(a)].
* Without restarts, if `A` answers correctly with probability at least `1/2` within `m` coins,
  the host is an abort-form decider [AB09, §7.4.2 and Exercise 7.6(a)].

The expected-time bound is a renewal argument on finite coin words: a round of fixed length
`R` either halts or returns to a ready configuration, so `Pr[T > s₀ + jR] ≤ a^j`.

## Main definitions

* `Randomized.attemptBit` — the one-bit answer of a PTM after a number of coins.

## Main results

* `Randomized.randProb_rounds_le`, `Randomized.halted_rounds` — the renewal bounds.
* `Turing.FinNDTM.expTimeLe_of_rounds` — `E[T] ≤ s₀ + R / (1 - a)`.
* `Randomized.clockHost_zDecides`, `Randomized.clockHost_abortDecides` — the two hosts.
* `Turing.FinNDTM.ZDecidesInTime.mono`, `Turing.FinNDTM.AbortDecidesInTime.mono`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open Finset Turing

/-! ### Renewal over rounds of fixed length -/

variable {k : ℕ} {St : Type} [DecidableEq St] {x : List Bool}

/-- **Renewal, halting**: if every round of `R` coins from a ready configuration either halts
or ends ready, and fails to halt with probability at most `a`, then `j` rounds fail to halt
with probability at most `a^j`.

**Proof sketch.** Induction on `j`, conditioning on the first round
(`randProb_append_le`): a halted round stays halted, and a ready one contributes `a^j`. -/
theorem randProb_rounds_le (tm : NDTM k Bool St) (Ready : Cfg k Bool St x → Prop) (R : ℕ)
    {a : ℚ} (ha : 0 ≤ a)
    (hstep : ∀ c, Ready c → ∀ p : List Bool, p.length = R →
      (tm.runWith p c).state = none ∨ Ready (tm.runWith p c))
    (hprob : ∀ c, Ready c → randProb R (fun p => (tm.runWith p c).state ≠ none) ≤ a)
    (j : ℕ) (c : Cfg k Bool St x) (hc : Ready c) :
    randProb (R * j) (fun w => (tm.runWith w c).state ≠ none) ≤ a ^ j := by
  induction j generalizing c with
  | zero => simpa using (randProb_le_one : randProb 0 (fun w => (tm.runWith w c).state ≠ none) ≤ 1)
  | succ j ih =>
    rw [show R * (j + 1) = R + R * j by ring, pow_succ, mul_comm (a ^ j) a]
    rw [randProb_congr (B := fun r => (tm.runWith (r.drop R) (tm.runWith (r.take R) c)).state ≠
      none) fun r => by
        show _ ↔ (tm.runWith ((List.ofFn r).drop R) (tm.runWith ((List.ofFn r).take R) c)).state ≠
          none
        rw [← NDTM.runWith_append, List.take_append_drop]]
    refine (randProb_append_le R (R * j) (fun p => (tm.runWith p c).state ≠ none)
      (fun p v => (tm.runWith v (tm.runWith p c)).state ≠ none) ?_ ?_).trans
      (mul_le_mul_of_nonneg_right (hprob c hc) (pow_nonneg ha j))
    · intro p v hv hp
      exact hv (by rw [NDTM.runWith_of_halt _ hp]; exact hp)
    · intro u hu
      rcases hstep c hc _ List.length_ofFn with h | h
      · exact absurd h hu
      · exact ih _ h

omit [DecidableEq St] in
/-- **Renewal, answers**: if every round from a ready configuration either halts in a
configuration satisfying `P` or ends ready, and ready configurations are live, then every run
of whole rounds that has halted satisfies `P`.

**Proof sketch.** Induction on the number of rounds: split off the first round; if it halted,
later coins change nothing, otherwise it ended ready. -/
theorem halted_rounds (tm : NDTM k Bool St) (Ready P : Cfg k Bool St x → Prop) (R : ℕ)
    (hstep : ∀ c, Ready c → ∀ p : List Bool, p.length = R →
      ((tm.runWith p c).state = none ∧ P (tm.runWith p c)) ∨ Ready (tm.runWith p c))
    (hlive : ∀ c, Ready c → c.state ≠ none) (j : ℕ) (c : Cfg k Bool St x) (hc : Ready c)
    (w : List Bool) (hw : w.length = R * j) (hh : (tm.runWith w c).state = none) :
    P (tm.runWith w c) := by
  induction j generalizing c w with
  | zero =>
    rw [Nat.mul_zero, List.length_eq_zero_iff] at hw
    subst hw
    exact absurd hh (hlive c hc)
  | succ j ih =>
    have ht : (w.take R).length = R :=
      List.length_take_of_le (by rw [hw]; exact Nat.le_mul_of_pos_right R (Nat.succ_pos j))
    rw [← List.take_append_drop R w, NDTM.runWith_append] at hh ⊢
    rcases hstep c hc _ ht with ⟨h1, h2⟩ | h
    · rw [NDTM.runWith_of_halt _ h1]; exact h2
    · exact ih _ h _ (by rw [List.length_drop, hw, Nat.mul_succ, Nat.add_sub_cancel]) hh

end Randomized

namespace Turing.FinNDTM

open Finset Randomized

/-- **Expected time from rounds**: if a startup of `s₀` steps always reaches `c₀`, and `j`
rounds of `R > 0` coins from `c₀` fail to halt with probability at most `a^j` (`a < 1`), then
`E[T_{N,x}] ≤ s₀ + R/(1 - a)`. [AB09, Exercise 7.6(a)]

**Proof sketch.** `Pr[T > s₀ + jR] ≤ a^j`, since the startup ignores its coins
(`randProb_split`). Bound `Pr[T > t]` by `1` for `t < s₀`, and by antitonicity by `a^j` on the
`j`-th block of `R` steps after `s₀`; sum the geometric series. -/
theorem expTimeLe_of_rounds (N : FinNDTM Bool) (x : List Bool) (s₀ R : ℕ) (hR : 0 < R)
    (c₀ : Cfg N.k Bool N.State x)
    (hstart : ∀ w : List Bool, w.length = s₀ → N.tm.runWith w (N.tm.initCfg x) = c₀)
    {a : ℚ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hround : ∀ j, randProb (R * j) (fun w => (N.tm.runWith w c₀).state ≠ none) ≤ a ^ j) :
    N.ExpTimeLe x (s₀ + R / (1 - a)) := by
  set f := notHaltedProb (N.haltRun x)
  have hf1 : ∀ t, f t ≤ 1 := fun t => notHaltedProb_le_one t
  have hf0 : ∀ t, 0 ≤ f t := fun t => notHaltedProb_nonneg t
  have hblock : ∀ j, f (s₀ + R * j) ≤ a ^ j := by
    intro j
    have : f (s₀ + R * j) = randProb (s₀ + R * j) (fun r => True ∧
        (N.tm.runWith (r.drop s₀) c₀).state ≠ none) := by
      refine randProb_congr fun r => ?_
      have hl : ((List.ofFn r).take s₀).length = s₀ :=
        List.length_take_of_le (by simp)
      have hrun : N.tm.runWith (List.ofFn r) (N.tm.initCfg x) =
          N.tm.runWith ((List.ofFn r).drop s₀) c₀ := by
        conv_lhs => rw [← List.take_append_drop s₀ (List.ofFn r)]
        rw [NDTM.runWith_append, hstart _ hl]
      rw [haltRun_eq_none_iff, hrun]
      simp
    rw [this, randProb_split s₀ (R * j) (fun _ => True)
      (fun v => (N.tm.runWith v c₀).state ≠ none), randProb_true, one_mul]
    exact hround j
  have hanti : Antitone f := notHaltedProb_haltRun_antitone N x
  have hsum : ∀ n, ∑ t ∈ range (R * n), f (s₀ + t) ≤ R * ∑ j ∈ range n, a ^ j := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show R * (n + 1) = R * n + R by ring, sum_range_add, sum_range_succ, mul_add]
      refine add_le_add ih ?_
      calc ∑ r ∈ range R, f (s₀ + (R * n + r))
          ≤ ∑ _r ∈ range R, a ^ n := sum_le_sum fun r _ =>
            (hanti (Nat.add_le_add_left (Nat.le_add_right _ _) _ :
              s₀ + R * n ≤ s₀ + (R * n + r))).trans (hblock n)
        _ = R * a ^ n := by simp
  have hgeom : ∀ K, ∑ j ∈ range K, a ^ j ≤ 1 / (1 - a) := by
    intro K
    have := geom_sum_Ico_le_of_lt_one ha0 ha1 (m := 0) (n := K)
    rwa [← range_eq_Ico, pow_zero] at this
  intro K
  calc ∑ t ∈ range K, f t
      ≤ ∑ t ∈ range (s₀ + R * K), f t :=
        sum_le_sum_of_subset_of_nonneg
          (range_mono (le_trans (Nat.le_mul_of_pos_left K hR) (Nat.le_add_left _ _)))
          fun _ _ _ => hf0 _
    _ = ∑ t ∈ range s₀, f t + ∑ t ∈ range (R * K), f (s₀ + t) := sum_range_add _ _ _
    _ ≤ s₀ + R * (1 / (1 - a)) := by
        refine add_le_add ?_ ((hsum K).trans ?_)
        · calc ∑ t ∈ range s₀, f t ≤ ∑ _t ∈ range s₀, (1 : ℚ) := sum_le_sum fun t _ => hf1 t
            _ = s₀ := by simp
        · exact mul_le_mul_of_nonneg_left (hgeom K) (by positivity)
    _ = s₀ + R / (1 - a) := by ring

variable {N : FinNDTM Bool} {L : Language Bool}

/-- Zero-error deciding is monotone in the time bound. -/
theorem ZDecidesInTime.mono {T₁ T₂ : ℕ → ℕ} (h : N.ZDecidesInTime L T₁)
    (hT : ∀ n, T₁ n ≤ T₂ n) : N.ZDecidesInTime L T₂ :=
  fun x => ⟨fun K => ((h x).1 K).trans (by exact_mod_cast hT _), (h x).2⟩

/-- Abort-form deciding is monotone in the time bound. -/
theorem AbortDecidesInTime.mono {T₁ T₂ : ℕ → ℕ} (h : N.AbortDecidesInTime L T₁)
    (hT : ∀ n, T₁ n ≤ T₂ n) : N.AbortDecidesInTime L T₂ := by
  intro x
  obtain ⟨hhalt, hwrong, hprob⟩ := h x
  refine ⟨hhalt.mono (hT _), fun w hw => ?_, ?_⟩
  · have hle : T₁ x.length ≤ w.length := hw ▸ hT _
    unfold outputWith
    rw [runWith_eq_runWith_take hhalt hle]
    exact hwrong _ (List.length_take_of_le hle)
  · rw [outputProb_eq_of_haltsWithin hhalt (hT _)]
    exact hprob

end Turing.FinNDTM

namespace Randomized

open Turing Turing.ClockHost

/-- The one-bit answer of the PTM `A` on `x` after the coins `u`: `some v` if it has halted
with output `[v]`, else `none`. -/
def attemptBit (A : FinNDTM Bool) (x u : List Bool) : Option Bool :=
  (A.haltRun x u).bind FinNDTM.bitOfOutput

/-- `attemptBit` reads a halted one-bit output. -/
theorem attemptBit_eq_some {A : FinNDTM Bool} {x u : List Bool} {v : Bool} :
    attemptBit A x u = some v ↔ (A.tm.runWith u (A.tm.initCfg x)).state = none ∧
      (A.tm.runWith u (A.tm.initCfg x)).output = [v] := by
  unfold attemptBit
  cases h : A.haltRun x u with
  | none =>
    rw [FinNDTM.haltRun_eq_none_iff] at h
    simp only [Option.bind_none]
    exact ⟨fun h' => absurd h' (by simp), fun h' => absurd h'.1 h⟩
  | some o =>
    rw [FinNDTM.haltRun_eq_some_iff] at h
    obtain ⟨h1, h2⟩ := h
    simp only [Option.bind_some, h1, true_and, FinNDTM.outputWith] at h2 ⊢
    rw [h2]
    rcases o with _ | ⟨b, _ | ⟨b', o⟩⟩ <;> simp [FinNDTM.bitOfOutput]

/-- **The restart host decides with zero error** [AB09, Def 7.7 and Exercise 7.6(a)]: let `S`
compute `1^{m(n)}` in time `T_S(n)` with `n ≤ m(n)`, and let every one-bit answer of `A` within
`m` coins be `L(x)`, with no answer with probability at most `3/4`. Then the restart host
decides `L` with zero error in expected time `T_S(n) + m(n) + 2 + 16(m(n) + 1)`.

**Proof sketch.** After the startup (`startup`), the host performs rounds of `4(m + 1)` coins
(`round`): each halts with `A`'s answer on its first `m` coins, which is `L(x)`, or ends ready.
A round fails to halt only if `A` gives no answer, with probability at most `3/4`
(`randProb_take`). Renewal (`randProb_rounds_le`, `expTimeLe_of_rounds`) bounds the expected
time; `halted_rounds`, after padding a halted run to whole rounds, gives correctness. -/
theorem clockHost_zDecides (S : FinTM Bool) (A : FinNDTM Bool) (L : Language Bool)
    (m TS : ℕ → ℕ)
    (hS : S.ComputesFunInTime (fun x => List.replicate (m x.length) true) TS)
    (hm : ∀ n, n ≤ m n)
    (hcorr : ∀ x u v, u.length = m x.length → attemptBit A x u = some v →
      v = MultiTapeTM.indicator (L : Set (List Bool)) x)
    (hprob : ∀ x : List Bool, randProb (m x.length) (fun u => attemptBit A x u = none) ≤ 3 / 4) :
    (FinNDTM.clockHost S A true).ZDecidesInTime L
      fun n => TS n + m n + 2 + 16 * (m n + 1) := by
  classical
  intro x
  set mm := m x.length with hmm
  set ℓ := MultiTapeTM.indicator (L : Set (List Bool)) x
  obtain ⟨s₀, hs₀, sT, sP, hstart⟩ :=
    startup (A := A) (loop := true) mm (hS x) (hm _)
  set c₀ := runCfg (S := S) mm (A.tm.initCfg x) 0 sT sP
  have hc₀ : ClockReady mm c₀ := ⟨_, _, _, readyAt_initCfg mm, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = 4 * (mm + 1) := ⟨_, rfl⟩
  have hsucc : ∀ p : List Bool, p.length = R → ∀ v, attemptBit A x (p.take mm) = some v →
      ∀ (c : Cfg (S.k + A.k + 1) Bool (ClockPhase S.State A.State) x), ClockReady mm c →
        ((hostTM S A true).runWith p c).state = none ∧
        ((hostTM S A true).runWith p c).output = [ℓ] := by
    intro p hp v hv c hc
    obtain ⟨h1, h2⟩ := attemptBit_eq_some.mp hv
    have hvℓ : v = ℓ := hcorr x _ v (List.length_take_of_le (by omega)) hv
    rw [hvℓ] at h2
    exact (round mm hc (hm _) p (hp.trans hR)).1 ℓ h1 h2
  have hfail : ∀ p : List Bool, p.length = R → attemptBit A x (p.take mm) = none →
      ∀ (c : Cfg (S.k + A.k + 1) Bool (ClockPhase S.State A.State) x), ClockReady mm c →
        ClockReady mm ((hostTM S A true).runWith p c) := by
    intro p hp hn c hc
    refine (round mm hc (hm _) p (hp.trans hR)).2 fun ⟨h1, v, h2⟩ => ?_
    rw [attemptBit_eq_some.mpr ⟨h1, h2⟩] at hn
    exact absurd hn (by simp)
  have hstep : ∀ (c : Cfg (S.k + A.k + 1) Bool (ClockPhase S.State A.State) x),
      ClockReady mm c → ∀ p : List Bool, p.length = R →
      (((hostTM S A true).runWith p c).state = none ∧
        ((hostTM S A true).runWith p c).output = [ℓ]) ∨
      ClockReady mm ((hostTM S A true).runWith p c) := by
    intro c hc p hp
    cases hb : attemptBit A x (p.take mm) with
    | none => exact Or.inr (hfail p hp hb c hc)
    | some v => exact Or.inl (hsucc p hp v hb c hc)
  have hprobR : ∀ (c : Cfg (S.k + A.k + 1) Bool (ClockPhase S.State A.State) x), ClockReady mm c →
      randProb R (fun p => ((hostTM S A true).runWith p c).state ≠ none) ≤ 3 / 4 := by
    intro c hc
    calc randProb R (fun p => ((hostTM S A true).runWith p c).state ≠ none)
        ≤ randProb R (fun p => attemptBit A x (p.take mm) = none) := randProb_mono fun r hr => by
          cases hb : attemptBit A x ((List.ofFn r).take mm) with
          | none => rfl
          | some v => exact absurd (hsucc _ List.length_ofFn v hb c hc).1 hr
      _ = randProb mm (fun u => attemptBit A x u = none) :=
          randProb_take (by omega) (fun u => attemptBit A x u = none)
      _ ≤ 3 / 4 := hprob x
  refine ⟨?_, fun w hw => ?_⟩
  · have hexp := FinNDTM.expTimeLe_of_rounds (FinNDTM.clockHost S A true) x s₀ R (by omega) c₀
      hstart (a := 3 / 4) (by norm_num) (by norm_num) fun j =>
        randProb_rounds_le (hostTM S A true) (ClockReady mm) R (by norm_num)
          (fun c hc p hp => (hstep c hc p hp).imp_left And.left) hprobR j c₀ hc₀
    intro K
    refine (hexp K).trans ?_
    have h4 : ((R : ℕ) : ℚ) / (1 - 3 / 4) = 16 * ((mm : ℚ) + 1) := by
      rw [hR]; push_cast; ring
    have hs : (s₀ : ℚ) ≤ TS x.length + mm + 2 := by exact_mod_cast hs₀
    rw [h4]
    push_cast
    linarith
  · -- pad the halted run to whole rounds after the startup
    have hle : w.length ≤ s₀ + R * w.length :=
      le_trans (Nat.le_mul_of_pos_left _ (by omega)) (Nat.le_add_left _ _)
    set w' := w ++ List.replicate (s₀ + R * w.length - w.length) false with hw'
    have hlen : w'.length = s₀ + R * w.length := by
      rw [hw', List.length_append, List.length_replicate, Nat.add_sub_cancel' hle]
    have hrun : (hostTM S A true).runWith w' ((hostTM S A true).initCfg x) =
        (hostTM S A true).runWith w ((hostTM S A true).initCfg x) := by
      rw [hw', NDTM.runWith_append]
      exact NDTM.runWith_of_halt _ hw
    have hsplit : (hostTM S A true).runWith w' ((hostTM S A true).initCfg x) =
        (hostTM S A true).runWith (w'.drop s₀) c₀ := by
      rw [← List.take_append_drop s₀ w', NDTM.runWith_append,
        hstart (w'.take s₀) (List.length_take_of_le (by rw [hlen]; exact Nat.le_add_right _ _)),
        List.take_append_drop]
    have hh : ((hostTM S A true).runWith (w'.drop s₀) c₀).state = none := by
      rw [← hsplit, hrun]; exact hw
    have := halted_rounds (hostTM S A true) (ClockReady mm) (fun c => c.output = [ℓ]) R hstep
      (fun c hc => hc.state_ne_none mm) w.length c₀ hc₀ (w'.drop s₀)
      (by rw [List.length_drop, hlen, Nat.add_sub_cancel_left]) hh
    show ((hostTM S A true).runWith w ((hostTM S A true).initCfg x)).output = [ℓ]
    rw [← hrun, hsplit]
    exact this

/-- **The clocked runner is an abort-form decider** [AB09, §7.4.2 and Exercise 7.6(a)]: let `S`
compute `1^{m(n)}` in time `T_S(n)` with `n ≤ m(n)`, let every one-bit answer of `A` within
`m` coins be `L(x)`, and let `A` answer `L(x)` with probability at least `1/2`. Then the
one-shot host halts within `T_S(n) + m(n) + 2 + (m(n) + 1)` steps on every branch, never
outputs `[¬L(x)]`, and outputs `[L(x)]` with probability at least `1/2`.

**Proof sketch.** After the startup (`startup`), `m + 1` more steps halt the host (`oneShot`),
with output `[v]` exactly when `A` answered `v` on the first `m` coins after the startup. Since
the startup ignores its coins, the output distribution is `A`'s (`randProb_split`,
`randProb_take`). -/
theorem clockHost_abortDecides (S : FinTM Bool) (A : FinNDTM Bool) (L : Language Bool)
    (m TS : ℕ → ℕ)
    (hS : S.ComputesFunInTime (fun x => List.replicate (m x.length) true) TS)
    (hm : ∀ n, n ≤ m n)
    (hcorr : ∀ x u v, u.length = m x.length → attemptBit A x u = some v →
      v = MultiTapeTM.indicator (L : Set (List Bool)) x)
    (hprob : ∀ x : List Bool, 1 / 2 ≤ randProb (m x.length)
      (fun u => attemptBit A x u = some (MultiTapeTM.indicator (L : Set (List Bool)) x))) :
    (FinNDTM.clockHost S A false).AbortDecidesInTime L
      fun n => TS n + m n + 2 + (m n + 1) := by
  classical
  intro x
  set mm := m x.length with hmm
  set ℓ := MultiTapeTM.indicator (L : Set (List Bool)) x
  obtain ⟨s₀, hs₀, sT, sP, hstart⟩ :=
    startup (A := A) (loop := false) mm (hS x) (hm _)
  have hrun : ∀ w : List Bool, w.length = s₀ + (mm + 1) →
      (hostTM S A false).runWith w ((hostTM S A false).initCfg x) =
        (hostTM S A false).runWith (w.drop s₀) (runCfg mm (A.tm.initCfg x) 0 sT sP) := by
    intro w hw
    rw [← List.take_append_drop s₀ w, NDTM.runWith_append,
      hstart (w.take s₀) (List.length_take_of_le (by omega)), List.take_append_drop]
  have hdrop : ∀ w : List Bool, w.length = s₀ + (mm + 1) → (w.drop s₀).length = mm + 1 :=
    fun w hw => by rw [List.length_drop, hw]; omega
  have hhalt : (FinNDTM.clockHost S A false).tm.HaltsWithin x (s₀ + (mm + 1)) := fun w hw => by
    show ((hostTM S A false).runWith w ((hostTM S A false).initCfg x)).state = none
    rw [hrun w hw]
    exact (oneShot mm sT sP _ (hdrop w hw)).1
  have hout : ∀ w : List Bool, w.length = s₀ + (mm + 1) → ∀ v,
      (FinNDTM.clockHost S A false).outputWith x w = [v] ↔
        attemptBit A x ((w.drop s₀).take mm) = some v := by
    intro w hw v
    show ((hostTM S A false).runWith w ((hostTM S A false).initCfg x)).output = [v] ↔ _
    rw [hrun w hw, (oneShot mm sT sP _ (hdrop w hw)).2, attemptBit_eq_some]
  have hT' : s₀ + (mm + 1) ≤ TS x.length + mm + 2 + (mm + 1) := by omega
  refine ⟨hhalt.mono hT', fun w hw => ?_, ?_⟩
  · have hle : s₀ + (mm + 1) ≤ w.length := by rw [hw]; exact hT'
    intro heq
    have h1 : (FinNDTM.clockHost S A false).outputWith x (w.take (s₀ + (mm + 1))) = [!ℓ] := by
      unfold FinNDTM.outputWith
      rw [← FinNDTM.runWith_eq_runWith_take hhalt hle]
      exact heq
    rw [hout _ (List.length_take_of_le hle)] at h1
    have hl1 : mm ≤ (List.drop s₀ (List.take (s₀ + (mm + 1)) w)).length := by
      rw [List.length_drop, List.length_take_of_le hle]
      omega
    have hbad : (!ℓ) = ℓ := hcorr x _ _ (List.length_take_of_le hl1) h1
    revert hbad
    generalize ℓ = b
    cases b <;> decide
  · rw [FinNDTM.outputProb_eq_of_haltsWithin hhalt hT']
    unfold FinNDTM.outputProb
    rw [randProb_congr (B := fun r => True ∧ attemptBit A x ((r.drop s₀).take mm) = some ℓ)
        fun r => by rw [hout _ List.length_ofFn]; simp,
      randProb_split s₀ (mm + 1) (fun _ => True) (fun u => attemptBit A x (u.take mm) = some ℓ),
      randProb_true, one_mul, randProb_take (by omega) (fun u => attemptBit A x u = some ℓ)]
    exact hprob x

end Randomized
