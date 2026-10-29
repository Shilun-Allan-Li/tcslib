/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.TuringMachine.Build.NDClockHost

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The clocked restart host: startup and round contracts

The whole-run contracts of the clocked restart host `Turing.FinNDTM.clockHost`
(`TCSlib.Complexity.TuringMachine.Build.NDClockHost`), with yardstick length `m`:

* **startup** — within `T + m + 2` steps (`T` the yardstick machine's time) the host reaches
  the first attempt, with `A` in its initial configuration;
* **one-shot** (`loop = false`) — `m + 1` further steps later the host has halted, with output
  `[v]` exactly when `A`, run on the first `m` of those coins, has halted with output `[v]`;
* **round** (`loop = true`) — from a *ready* attempt configuration, `4(m + 1)` steps later the
  host has either halted with `A`'s one-bit output on the first `m` coins of the round, or is
  ready again. A ready configuration has `A`'s bank blank from `m` cells left of each head on,
  so by locality (`Turing.NDTM.AgreeShift`) an attempt behaves exactly as from `A`'s start.

## Main definitions

* `Turing.ClockHost.ReadyAt`, `Turing.ClockHost.ClockReady` — ready attempt configurations.

## Main results

* `Turing.ClockHost.reset_run` — the three reset sweeps.
* `Turing.ClockHost.nextAttempt_workTapePos` — the head envelope of a round.
* `Turing.ClockHost.startup` — the startup contract.
* `Turing.ClockHost.oneShot` — the clocked runner of [AB09, §7.4.2].
* `Turing.ClockHost.round` — the restart round of [AB09, Exercise 7.6(a)].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Turing.ClockHost

variable {S : FinTM Bool} {A : FinNDTM Bool} {loop : Bool} {x : List Bool} (m : ℕ)

/-- Split a word of length `m + 1 + r` at its `m`-th letter. -/
theorem exists_split_block {w : List Bool} {r : ℕ} (hw : w.length = m + 1 + r) :
    ∃ u b v, w = u ++ b :: v ∧ u.length = m ∧ v.length = r := by
  rcases hd : w.drop m with _ | ⟨b, v⟩
  · have := congrArg List.length hd; simp at this; omega
  · refine ⟨w.take m, b, v, by rw [← hd, List.take_append_drop],
      List.length_take_of_le (by omega), ?_⟩
    have := congrArg List.length hd; simp at this; omega

/-- One more left move, taken last. -/
theorem inLeft_succ {n : ℕ} (ip : Fin (n + 2)) (j : ℕ) :
    inLeft ip (j + 1) = moveInputPos (inLeft ip j) (-1) := by
  induction j generalizing ip with
  | zero => rfl
  | succ j ih => exact ih (moveInputPos ip (-1))

/-! ### The reset sweeps -/

/-- A step of a reset sweep over a mark. -/
theorem p0_mark (b : Bool) (ip : Fin (x.length + 2)) (sT : Fin S.k → ℤ → Option Bool)
    (sP : Fin S.k → ℤ) (aT : Fin A.k → ℤ → Option Bool) (aP : Fin A.k → ℤ) (z : ℤ)
    (hz : yard m z = some true) :
    (hostTM S A loop).stepWith b (hostCfg (some .p0) ip sT sP aT aP (yard m) z []) =
      hostCfg (some .p0) (moveInputPos ip (-1)) sT sP aT (fun i => aP i + 1) (yard m) (z - 1)
        [] := by
  rw [stepWith_hostCfg]
  simp only [clockTr, hostCfg_symbols_yI, hz]
  rw [apply_hostCfg]
  host_congr

/-- The turnaround of the first sweep. -/
theorem p0_turn (b : Bool) (ip : Fin (x.length + 2)) (sT : Fin S.k → ℤ → Option Bool)
    (sP : Fin S.k → ℤ) (aT : Fin A.k → ℤ → Option Bool) (aP : Fin A.k → ℤ) :
    (hostTM S A loop).stepWith b (hostCfg (some .p0) ip sT sP aT aP (yard m) (-1) []) =
      hostCfg (some .p1) (moveInputPos ip (-1)) sT sP aT (fun i => aP i + 1) (yard m) 0 [] := by
  rw [stepWith_hostCfg]
  simp only [clockTr, hostCfg_symbols_yI, yard_neg_one]
  rw [apply_hostCfg]
  host_congr

/-- A step of the second sweep over a mark. -/
theorem p1_mark (b : Bool) (ip : Fin (x.length + 2)) (sT : Fin S.k → ℤ → Option Bool)
    (sP : Fin S.k → ℤ) (aT : Fin A.k → ℤ → Option Bool) (aP : Fin A.k → ℤ) (z : ℤ)
    (hz : yard m z = some true) :
    (hostTM S A loop).stepWith b (hostCfg (some .p1) ip sT sP aT aP (yard m) z []) =
      hostCfg (some .p1) ip sT sP aT (fun i => aP i + 1) (yard m) (z + 1) [] := by
  rw [stepWith_hostCfg]
  simp only [clockTr, hostCfg_symbols_yI, hz]
  rw [apply_hostCfg]
  host_congr

/-- The turnaround of the second sweep. -/
theorem p1_turn (b : Bool) (ip : Fin (x.length + 2)) (sT : Fin S.k → ℤ → Option Bool)
    (sP : Fin S.k → ℤ) (aT : Fin A.k → ℤ → Option Bool) (aP : Fin A.k → ℤ) :
    (hostTM S A loop).stepWith b (hostCfg (some .p1) ip sT sP aT aP (yard m) m []) =
      hostCfg (some .p2) ip sT sP aT (fun i => aP i + 1) (yard m) ((m : ℤ) - 1) [] := by
  rw [stepWith_hostCfg]
  simp only [clockTr, hostCfg_symbols_yI, yard_len]
  rw [apply_hostCfg]
  host_congr

/-- A step of the third sweep over a mark. -/
theorem p2_mark (b : Bool) (ip : Fin (x.length + 2)) (sT : Fin S.k → ℤ → Option Bool)
    (sP : Fin S.k → ℤ) (aT : Fin A.k → ℤ → Option Bool) (aP : Fin A.k → ℤ) (z : ℤ)
    (hz : yard m z = some true) :
    (hostTM S A loop).stepWith b (hostCfg (some .p2) ip sT sP aT aP (yard m) z []) =
      hostCfg (some .p2) ip sT sP aT (fun i => aP i + 1) (yard m) (z - 1) [] := by
  rw [stepWith_hostCfg]
  simp only [clockTr, hostCfg_symbols_yI, hz]
  rw [apply_hostCfg]
  host_congr

/-- The turnaround of the third sweep starts a new attempt. -/
theorem p2_turn (b : Bool) (ip : Fin (x.length + 2)) (sT : Fin S.k → ℤ → Option Bool)
    (sP : Fin S.k → ℤ) (aT : Fin A.k → ℤ → Option Bool) (aP : Fin A.k → ℤ) :
    (hostTM S A loop).stepWith b (hostCfg (some .p2) ip sT sP aT aP (yard m) (-1) []) =
      hostCfg (some (.run (some A.tm.q₀) none)) (moveInputPos ip 1) sT sP aT
        (fun i => aP i + 1) (yard m) 0 [] := by
  rw [stepWith_hostCfg]
  simp only [clockTr, hostCfg_symbols_yI, yard_neg_one]
  rw [apply_hostCfg]
  host_congr

/-- The first sweep over `j ≤ m` marks.

**Proof sketch.** Induction on the word, one `p0_mark` step at a time; `p1_marks` and `p2_marks`
are the same. -/
theorem p0_marks (ip : Fin (x.length + 2)) (sT : Fin S.k → ℤ → Option Bool)
    (sP : Fin S.k → ℤ) (aT : Fin A.k → ℤ → Option Bool) (aP : Fin A.k → ℤ) (w : List Bool)
    (hj : w.length ≤ m) (z : ℤ) (hz : z = (w.length : ℤ) - 1) :
    (hostTM S A loop).runWith w (hostCfg (some .p0) ip sT sP aT aP (yard m) z []) =
      hostCfg (some .p0) (inLeft ip w.length) sT sP aT (fun i => aP i + w.length) (yard m) (-1)
        [] := by
  subst hz
  induction w generalizing ip aP with
  | nil => simp [inLeft]
  | cons b w ih =>
    simp only [List.length_cons] at hj ⊢
    rw [NDTM.runWith_cons, p0_mark m b ip sT sP aT aP (((w.length + 1 : ℕ) : ℤ) - 1)
      (yard_of_lt (by omega) (by push_cast; omega))]
    have h : ((w.length + 1 : ℕ) : ℤ) - 1 - 1 = (w.length : ℤ) - 1 := by push_cast; omega
    rw [h, ih]
    · congr 1
      funext i
      push_cast
      omega
    · omega

/-- The second sweep over `j ≤ m` marks. -/
theorem p1_marks (ip : Fin (x.length + 2)) (sT : Fin S.k → ℤ → Option Bool)
    (sP : Fin S.k → ℤ) (aT : Fin A.k → ℤ → Option Bool) (aP : Fin A.k → ℤ) (w : List Bool)
    (hj : w.length ≤ m) (z : ℤ) (hz : z = (m : ℤ) - w.length) :
    (hostTM S A loop).runWith w (hostCfg (some .p1) ip sT sP aT aP (yard m) z []) =
      hostCfg (some .p1) ip sT sP aT (fun i => aP i + w.length) (yard m) m [] := by
  subst hz
  induction w generalizing aP with
  | nil => simp
  | cons b w ih =>
    simp only [List.length_cons] at hj ⊢
    rw [NDTM.runWith_cons, p1_mark m b ip sT sP aT aP ((m : ℤ) - ((w.length + 1 : ℕ) : ℤ))
      (yard_of_lt (by push_cast; omega) (by push_cast; omega))]
    have h : (m : ℤ) - ((w.length + 1 : ℕ) : ℤ) + 1 = (m : ℤ) - w.length := by push_cast; omega
    rw [h, ih]
    · congr 1
      funext i
      push_cast
      omega
    · omega

/-- The third sweep over `j ≤ m` marks. -/
theorem p2_marks (ip : Fin (x.length + 2)) (sT : Fin S.k → ℤ → Option Bool)
    (sP : Fin S.k → ℤ) (aT : Fin A.k → ℤ → Option Bool) (aP : Fin A.k → ℤ) (w : List Bool)
    (hj : w.length ≤ m) (z : ℤ) (hz : z = (w.length : ℤ) - 1) :
    (hostTM S A loop).runWith w (hostCfg (some .p2) ip sT sP aT aP (yard m) z []) =
      hostCfg (some .p2) ip sT sP aT (fun i => aP i + w.length) (yard m) (-1) [] := by
  subst hz
  induction w generalizing aP with
  | nil => simp
  | cons b w ih =>
    simp only [List.length_cons] at hj ⊢
    rw [NDTM.runWith_cons, p2_mark m b ip sT sP aT aP (((w.length + 1 : ℕ) : ℤ) - 1)
      (yard_of_lt (by omega) (by push_cast; omega))]
    have h : ((w.length + 1 : ℕ) : ℤ) - 1 - 1 = (w.length : ℤ) - 1 := by push_cast; omega
    rw [h, ih]
    · congr 1
      funext i
      push_cast
      omega
    · omega

/-- **Reset run**: from the timeout, three sweeps of `m + 1` steps each move every head of
`A`'s bank `3(m + 1)` cells right, bring the input head `m + 1` cells left and one right, and
start a new attempt.

**Proof sketch.** Split the coins into three blocks of `m` and three turnaround steps; apply the
sweep lemmas and the turnarounds in order, and add up the head moves. -/
theorem reset_run (ip : Fin (x.length + 2)) (sT : Fin S.k → ℤ → Option Bool)
    (sP : Fin S.k → ℤ) (aT : Fin A.k → ℤ → Option Bool) (aP : Fin A.k → ℤ) (w : List Bool)
    (hw : w.length = 3 * (m + 1)) :
    (hostTM S A loop).runWith w (hostCfg (some .p0) ip sT sP aT aP (yard m) ((m : ℤ) - 1) []) =
      hostCfg (some (.run (some A.tm.q₀) none)) (moveInputPos (inLeft ip (m + 1)) 1) sT sP aT
        (fun i => aP i + (3 * (m + 1) : ℕ)) (yard m) 0 [] := by
  obtain ⟨u₁, b₁, r₁, rfl, h₁, hr₁⟩ :=
    exists_split_block m (w := w) (r := 2 * (m + 1)) (by omega)
  obtain ⟨u₂, b₂, r₂, rfl, h₂, hr₂⟩ := exists_split_block m (w := r₁) (r := m + 1) (by omega)
  obtain ⟨u₃, b₃, r₃, rfl, h₃, hr₃⟩ := exists_split_block m (w := r₂) (r := 0) (by omega)
  rw [List.length_eq_zero_iff] at hr₃
  subst hr₃
  rw [NDTM.runWith_append, p0_marks m _ _ _ _ _ u₁ h₁.le ((m : ℤ) - 1) (by rw [h₁]),
    NDTM.runWith_cons, p0_turn, NDTM.runWith_append,
    p1_marks m _ _ _ _ _ u₂ h₂.le 0 (by rw [h₂]; simp),
    NDTM.runWith_cons, p1_turn, NDTM.runWith_append,
    p2_marks m _ _ _ _ _ u₃ h₃.le ((m : ℤ) - 1) (by rw [h₃]),
    NDTM.runWith_cons, p2_turn, NDTM.runWith_nil, h₁, ← inLeft_succ]
  congr 1
  funext i
  simp only [h₂, h₃]
  push_cast
  omega

/-! ### Ready configurations -/

/-- An attempt configuration of `A` is *ready* when it is at `A`'s start state, input head and
empty output, with every tape blank from `m` cells left of its head on. -/
def ReadyAt (a : Cfg A.k Bool A.State x) : Prop :=
  a.state = some A.tm.q₀ ∧ a.inputPos = 1 ∧ a.output = [] ∧
    ∀ i z, a.workTapePos i - m ≤ z → a.workTapes i z = none

/-- `A`'s initial configuration is ready. -/
theorem readyAt_initCfg : ReadyAt m (A.tm.initCfg x) :=
  ⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩

/-- **Locality**: from a ready configuration, a run of at most `m` steps has the state and the
output of the run from `A`'s start. -/
theorem ReadyAt.runWith_eq {a : Cfg A.k Bool A.State x} (ha : ReadyAt m a) (u : List Bool)
    (hu : u.length ≤ m) :
    (A.tm.runWith u a).state = (A.tm.runWith u (A.tm.initCfg x)).state ∧
      (A.tm.runWith u a).output = (A.tm.runWith u (A.tm.initCfg x)).output := by
  have h : NDTM.AgreeShift (0 + u.length) a.workTapePos (A.tm.initCfg x) a := by
    refine ⟨ha.1, ha.2.1, ha.2.2.1, fun i => by simp [Cfg.init], fun i z hz => ?_⟩
    simp only [NDTM.initCfg, Cfg.init, zero_add, zero_sub] at hz ⊢
    exact ha.2.2.2 i _ (by omega)
  obtain ⟨h1, -, h3, -⟩ := NDTM.AgreeShift.runWith A.tm u h
  exact ⟨h1, h3⟩

/-- The configuration of `A` a reset makes from the end `a` of an attempt. -/
def nextAttempt (a : Cfg A.k Bool A.State x) : Cfg A.k Bool A.State x :=
  ⟨some A.tm.q₀, moveInputPos (inLeft a.inputPos (m + 1)) 1, a.workTapes,
    fun i => a.workTapePos i + (3 * (m + 1) : ℕ), []⟩

/-- After an attempt of `m` steps from a ready configuration, the reset leaves a ready
configuration: the heads move past every cell the attempt can have written. -/
theorem ReadyAt.next {a : Cfg A.k Bool A.State x} (ha : ReadyAt m a) (hm : x.length ≤ m)
    (u : List Bool) (hu : u.length = m) : ReadyAt m (nextAttempt m (A.tm.runWith u a)) := by
  refine ⟨rfl, moveInputPos_inLeft _ (by have := (A.tm.runWith u a).inputPos.isLt; omega), rfl,
    fun i z hz => ?_⟩
  have hpos := NDTM.abs_runWith_workTapePos_sub_le A.tm u a i
  rw [abs_le, hu] at hpos
  simp only [nextAttempt] at hz ⊢
  push_cast at hz
  rw [NDTM.runWith_workTapes_of_le A.tm u a i z (by rw [hu]; omega)]
  exact ha.2.2.2 i z (by omega)

/-- **Head envelope of a round**: after an attempt of `m` steps and the reset, each head of
`A`'s bank lies between `2m + 3` and `4m + 3` cells right of where the attempt started. -/
theorem nextAttempt_workTapePos (a : Cfg A.k Bool A.State x) (u : List Bool)
    (hu : u.length = m) (i : Fin A.k) :
    a.workTapePos i + ((2 * m + 3 : ℕ) : ℤ) ≤ (nextAttempt m (A.tm.runWith u a)).workTapePos i ∧
      (nextAttempt m (A.tm.runWith u a)).workTapePos i ≤
        a.workTapePos i + ((4 * m + 3 : ℕ) : ℤ) := by
  have h := NDTM.abs_runWith_workTapePos_sub_le A.tm u a i
  rw [abs_le, hu] at h
  simp only [nextAttempt]
  push_cast
  constructor <;> omega

/-- A host configuration at the start of an attempt from a ready configuration. -/
def ClockReady (c : Cfg (S.k + A.k + 1) Bool (ClockPhase S.State A.State) x) : Prop :=
  ∃ (a : Cfg A.k Bool A.State x) (sT : Fin S.k → ℤ → Option Bool) (sP : Fin S.k → ℤ),
    ReadyAt m a ∧ c = runCfg m a 0 sT sP

/-- A ready host configuration is live. -/
theorem ClockReady.state_ne_none {c : Cfg (S.k + A.k + 1) Bool (ClockPhase S.State A.State) x}
    (hc : ClockReady m c) : c.state ≠ none := by
  obtain ⟨a, sT, sP, -, rfl⟩ := hc
  simp [runCfg, hostCfg]

/-! ### Whole-run contracts -/

/-- **Startup** [AB09, §7.4.2]: if the yardstick machine `S` computes `1^m` on `x` within `T`
steps and `|x| ≤ m`, then for some `s₀ ≤ T + m + 2`, every coin word of length `s₀` leads the
host to the first attempt, with `A` at its initial configuration.

**Proof sketch.** Run `S` to its first halt `t_S ≤ T` (boot), where the yardstick tape holds
its output `1^m` with the head at `m`; then rewind in `m + 2` steps. -/
theorem startup {T : ℕ} (hS : S.ComputesInTime x (List.replicate m true) T)
    (hm : x.length ≤ m) :
    ∃ s₀ ≤ T + m + 2, ∃ (sT : Fin S.k → ℤ → Option Bool) (sP : Fin S.k → ℤ),
      ∀ w : List Bool, w.length = s₀ →
        (hostTM S A loop).runWith w ((hostTM S A loop).initCfg x) =
          runCfg m (A.tm.initCfg x) 0 sT sP := by
  classical
  have hex : ∃ t, (S.tm.runFrom (S.tm.initCfg x) t).state = none :=
    ⟨T, ((FinTM.computesInTime_iff _ _ _ _).mp hS).1⟩
  have htS : Nat.find hex ≤ T := Nat.find_min' hex ((FinTM.computesInTime_iff _ _ _ _).mp hS).1
  obtain ⟨cS, hcSdef⟩ : ∃ c, c = S.tm.runFrom (S.tm.initCfg x) (Nat.find hex) := ⟨_, rfl⟩
  have hcS : cS.state = none := hcSdef ▸ Nat.find_spec hex
  have hout : cS.output = List.replicate m true := by
    rw [hcSdef]
    exact ((FinTM.computesInTime_iff _ _ _ _).mpr ⟨Nat.find_spec hex, rfl⟩).output_unique hS
  refine ⟨Nat.find hex + (m + 2), by omega, cS.workTapes, cS.workTapePos, fun w hw => ?_⟩
  have ht : (w.take (Nat.find hex)).length = Nat.find hex := List.length_take_of_le (by omega)
  have hboot := boot_run (A := A) (loop := loop) (S.tm.initCfg x) (w.take (Nat.find hex))
    (fun t h => Nat.find_min hex (by omega))
  rw [ht, ← hcSdef] at hboot
  rw [initCfg_eq_bootCfg, ← List.take_append_drop (Nat.find hex) w, NDTM.runWith_append, hboot]
  have hb : bootCfg (A := A) cS = hostCfg (some .rew) cS.inputPos cS.workTapes cS.workTapePos
      (fun _ _ => none) (fun _ => 0) (yard m) m [] := by
    simp [bootCfg, hcS, hout]
  rw [hb, rewind_run m _ _ _ _ _ (w.drop (Nat.find hex)) (by simp; omega),
    moveInputPos_inLeft cS.inputPos (by have := cS.inputPos.isLt; omega)]
  rfl

/-- **One-shot run** (`loop = false`), the clocked runner of [AB09, §7.4.2]: `m + 1` steps
from the first attempt, the host has halted, and its output is `[v]` exactly when `A`, run from
its start on the first `m` coins, has halted with output `[v]`.

**Proof sketch.** Run `A` for `m` steps (`run_run_zero`), then take the timeout step
(`timeout_success` or `timeout_fail`). -/
theorem oneShot (sT : Fin S.k → ℤ → Option Bool) (sP : Fin S.k → ℤ) (w : List Bool)
    (hw : w.length = m + 1) :
    ((hostTM S A false).runWith w (runCfg m (A.tm.initCfg x) 0 sT sP)).state = none ∧
      ∀ v, ((hostTM S A false).runWith w (runCfg m (A.tm.initCfg x) 0 sT sP)).output = [v] ↔
        (A.tm.runWith (w.take m) (A.tm.initCfg x)).state = none ∧
          (A.tm.runWith (w.take m) (A.tm.initCfg x)).output = [v] := by
  obtain ⟨u, b, r, rfl, hu, hr⟩ := exists_split_block m (w := w) (r := 0) (by omega)
  rw [List.length_eq_zero_iff] at hr
  subst hr
  have htake : (u ++ [b]).take m = u := List.take_left' hu
  rw [htake, NDTM.runWith_append, run_run_zero m _ sT sP u (by omega), NDTM.runWith_cons,
    NDTM.runWith_nil, hu]
  set a' := A.tm.runWith u (A.tm.initCfg x)
  by_cases hs : a'.state = none ∧ ∃ v, a'.output = [v]
  · obtain ⟨hs, v, hv⟩ := hs
    rw [timeout_success m b a' sT sP hs hv]
    refine ⟨rfl, fun v' => ?_⟩
    simp [hostCfg, hs, hv]
  · rw [timeout_fail m b a' sT sP hs, if_neg (by decide)]
    refine ⟨rfl, fun v' => ⟨fun h => absurd h (by simp [hostCfg]), fun h => ?_⟩⟩
    exact absurd ⟨h.1, v', h.2⟩ hs

/-- **Restart round** (`loop = true`), [AB09, Exercise 7.6(a)]: from a ready attempt, after
`4(m + 1)` coins the host has halted with output `[v]` if `A`, run from its start on the first
`m` coins of the round, halted with output `[v]`; otherwise it is ready again.

**Proof sketch.** The attempt runs `A` in lockstep (`run_run`), and by locality its state and
output are those of the run from `A`'s start. On success the timeout emits `v` and the host
stays halted. Otherwise the timeout starts the reset (`reset_run`), which ends at the next
attempt, ready by `ReadyAt.next`. -/
theorem round {c : Cfg (S.k + A.k + 1) Bool (ClockPhase S.State A.State) x}
    (hc : ClockReady m c) (hm : x.length ≤ m) (w : List Bool) (hw : w.length = 4 * (m + 1)) :
    (∀ v, (A.tm.runWith (w.take m) (A.tm.initCfg x)).state = none →
      (A.tm.runWith (w.take m) (A.tm.initCfg x)).output = [v] →
        ((hostTM S A true).runWith w c).state = none ∧
          ((hostTM S A true).runWith w c).output = [v]) ∧
    (¬ ((A.tm.runWith (w.take m) (A.tm.initCfg x)).state = none ∧
        ∃ v, (A.tm.runWith (w.take m) (A.tm.initCfg x)).output = [v]) →
      ClockReady m ((hostTM S A true).runWith w c)) := by
  obtain ⟨a, sT, sP, ha, rfl⟩ := hc
  obtain ⟨u, b, r, rfl, hu, hr⟩ := exists_split_block m (w := w) (r := 3 * (m + 1)) (by omega)
  have htake : (u ++ b :: r).take m = u := List.take_left' hu
  rw [htake]
  obtain ⟨hst, hout⟩ := ha.runWith_eq m u hu.le
  rw [NDTM.runWith_append, run_run_zero m _ sT sP u (by omega), NDTM.runWith_cons, hu]
  set a' := A.tm.runWith u a
  refine ⟨fun v hs hv => ?_, fun hfail => ?_⟩
  · rw [timeout_success m b a' sT sP (hst.trans hs) (hout.trans hv), NDTM.runWith_of_halt]
    · exact ⟨rfl, rfl⟩
    · rfl
  · have hfail' : ¬ (a'.state = none ∧ ∃ v, a'.output = [v]) := by
      rw [hst, hout]; exact hfail
    rw [timeout_fail m b a' sT sP hfail', if_pos rfl, reset_run m _ _ _ _ _ r hr]
    exact ⟨nextAttempt m a', sT, sP, ha.next m hm u hu, rfl⟩

end Turing.ClockHost
