/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.TuringMachine.Build.NDCombinators
import TCSlib.Complexity.TuringMachine.Simulation
import Mathlib.Tactic.DeriveFintype

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The clocked restart host for binary-choice machines

A host that runs a binary-choice machine `A` against a clock, and optionally restarts it: the
clocked runner of [AB09, §7.4.2] and the restart loop of [AB09, Exercise 7.6(a)]. Its tapes are
a bank for a deterministic *yardstick* machine `S`, a bank for `A`, and a yardstick tape `Y`.

* **Startup.** `S` runs on its bank with its emissions written on `Y` (it is meant to emit
  `1^m`); then `Y`'s head and the input head are rewound.
* **Attempt.** `A` runs in lockstep with `Y`'s head, one coin per step, its emissions captured
  in the control state (`Turing.capOf`); after `m` steps `Y` reads a blank (the timeout).
* **Timeout.** If `A` has halted with output exactly `[v]`, the host emits `v` and halts.
  Otherwise it halts silently (`loop = false`) or resets (`loop = true`).
* **Reset.** Three sweeps over `Y` move every head of `A`'s bank `3(m+1)` cells to the right,
  onto blank tape, and bring the input head back to its start; then a new attempt begins.

Each phase is a hand-built transition table: the construction layer has no rows for
nondeterministic machines, and the deterministic clocked runner
(`Complexity.TimeHierarchy.clockTM`) does not host a coin-reading machine. The boot, rewind and
attempt contracts are proved here; the reset sweeps and the startup and round contracts are in
`TCSlib.Complexity.TuringMachine.Build.NDClockHostRun`.

## Main definitions

* `Turing.capOf` — the captured summary of an output word: empty, one bit, or longer.
* `Turing.ClockPhase`, `Turing.ClockHost.hostTM`, `Turing.FinNDTM.clockHost` — the host.

## Main results

* `Turing.ClockHost.boot_run`, `Turing.ClockHost.rewind_run`, `Turing.ClockHost.run_run`,
  `Turing.ClockHost.timeout_success`, `Turing.ClockHost.timeout_fail` — the phase contracts.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Turing

open FinTM (bufferTape)

/-! ### Captured output -/

/-- Append one optional emission to a captured summary. -/
def capPush : Option (Option Bool) → Option Bool → Option (Option Bool)
  | c, none => c
  | none, some e => some (some e)
  | some _, some _ => some none

/-- The captured summary of an output word: `none` if empty, `some (some b)` for `[b]`, and
`some none` for two or more bits. -/
def capOf : List Bool → Option (Option Bool)
  | [] => none
  | [b] => some (some b)
  | _ :: _ :: _ => some none

/-- The summary is updated emission by emission. -/
theorem capOf_append (o : List Bool) (e : Option Bool) :
    capOf (o ++ e.toList) = capPush (capOf o) e := by
  rcases e with _ | e
  · simp [capPush]
  · rcases o with _ | ⟨a, _ | ⟨b, o⟩⟩ <;> rfl

/-- The summary records a single bit exactly for one-bit words. -/
theorem capOf_eq_some_some {o : List Bool} {v : Bool} :
    capOf o = some (some v) ↔ o = [v] := by
  rcases o with _ | ⟨a, _ | ⟨b, o⟩⟩ <;> simp [capOf]

/-- The control phases of the clocked restart host. -/
inductive ClockPhase (SS AS : Type) where
  /-- running the yardstick machine in state `q` -/
  | boot (q : SS)
  /-- first rewind step -/
  | rew
  /-- rewinding the yardstick -/
  | rew2
  /-- the clocked attempt: the attempt's state and its captured output -/
  | run (q : Option AS) (cap : Option (Option Bool))
  /-- first reset sweep (leftward) -/
  | p0
  /-- second reset sweep (rightward) -/
  | p1
  /-- third reset sweep (leftward) -/
  | p2
  deriving DecidableEq, Fintype

namespace ClockHost

/-! ### Tape layout: yardstick bank, attempt bank, yardstick tape -/

section Slots

variable {α : Type*} {s a : ℕ}

/-- Assemble a per-tape family from the yardstick bank, the attempt bank and the tape `Y`. -/
def slots (f : Fin s → α) (g : Fin a → α) (y : α) : Fin (s + a + 1) → α :=
  Fin.append (Fin.append f g) fun _ => y

/-- The yardstick-bank tape `i`. -/
def sI (i : Fin s) : Fin (s + a + 1) := Fin.castAdd 1 (Fin.castAdd a i)

/-- The attempt-bank tape `i`. -/
def aI (i : Fin a) : Fin (s + a + 1) := Fin.castAdd 1 (Fin.natAdd s i)

/-- The yardstick tape. -/
def yI : Fin (s + a + 1) := Fin.natAdd (s + a) 0

/-- A yardstick-bank slot. -/
@[simp] theorem slots_sI (f : Fin s → α) (g : Fin a → α) (y : α) (i : Fin s) :
    slots f g y (sI i) = f i := by simp [slots, sI]

/-- An attempt-bank slot. -/
@[simp] theorem slots_aI (f : Fin s → α) (g : Fin a → α) (y : α) (i : Fin a) :
    slots f g y (aI i) = g i := by simp [slots, aI]

/-- The yardstick-tape slot. -/
@[simp] theorem slots_yI (f : Fin s → α) (g : Fin a → α) (y : α) :
    slots f g y (yI : Fin (s + a + 1)) = y := by simp [slots, yI]

/-- Every tape index is a yardstick-bank, attempt-bank or yardstick index. -/
theorem slots_cases {P : Fin (s + a + 1) → Prop} (hs : ∀ i, P (sI i)) (ha : ∀ i, P (aI i))
    (hy : P yI) (j : Fin (s + a + 1)) : P j := by
  refine Fin.addCases (fun j => Fin.addCases (fun i => hs i) (fun i => ha i) j) (fun i => ?_) j
  have : i = 0 := Subsingleton.elim _ _
  subst this
  exact hy

end Slots

/-- A work tape after an action: written at the head if the action writes, as computed by
`Turing.Action.apply` (to which it unfolds). -/
def tapeAfter (act : Option (Option Bool) × SignType) (t : ℤ → Option Bool) (p : ℤ) :
    ℤ → Option Bool :=
  (Action.apply (⟨0, fun _ => act, none, none⟩ : Action 1 Bool Unit)
    (⟨none, 0, fun _ => t, fun _ => p, []⟩ : Cfg 1 Bool Unit [])).workTapes 0

/-- A host configuration from its parts. -/
def hostCfg {SS AS : Type} {s a : ℕ} {x : List Bool} (q : Option (ClockPhase SS AS))
    (ip : Fin (x.length + 2)) (sT : Fin s → ℤ → Option Bool) (sP : Fin s → ℤ)
    (aT : Fin a → ℤ → Option Bool) (aP : Fin a → ℤ) (yT : ℤ → Option Bool) (yP : ℤ)
    (out : List Bool) : Cfg (s + a + 1) Bool (ClockPhase SS AS) x :=
  ⟨q, ip, slots sT aT yT, slots sP aP yP, out⟩

/-- Applying a slot-assembled action to a host configuration acts slot by slot. -/
theorem apply_hostCfg {SS AS : Type} {s a : ℕ} {x : List Bool} (im : SignType)
    (sa : Fin s → Option (Option Bool) × SignType) (aa : Fin a → Option (Option Bool) × SignType)
    (ya : Option (Option Bool) × SignType) (o : Option Bool) (q' q : Option (ClockPhase SS AS))
    (ip : Fin (x.length + 2)) (sT : Fin s → ℤ → Option Bool) (sP : Fin s → ℤ)
    (aT : Fin a → ℤ → Option Bool) (aP : Fin a → ℤ) (yT : ℤ → Option Bool) (yP : ℤ)
    (out : List Bool) :
    (⟨im, slots sa aa ya, o, q'⟩ : Action (s + a + 1) Bool (ClockPhase SS AS)).apply
        (hostCfg q ip sT sP aT aP yT yP out) =
      hostCfg q' (moveInputPos ip im) (fun i => tapeAfter (sa i) (sT i) (sP i))
        (fun i => sP i + (sa i).2) (fun i => tapeAfter (aa i) (aT i) (aP i))
        (fun i => aP i + (aa i).2) (tapeAfter ya yT yP) (yP + ya.2) (out ++ o.toList) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext j
    revert j
    refine slots_cases (fun i => ?_) (fun i => ?_) ?_ <;>
      simp only [Action.apply, hostCfg, slots_sI, slots_aI, slots_yI, tapeAfter]
  · funext j
    revert j
    refine slots_cases (fun i => ?_) (fun i => ?_) ?_ <;>
      simp only [Action.apply, hostCfg, slots_sI, slots_aI, slots_yI]

/-- The symbol read on a yardstick-bank tape. -/
@[simp] theorem hostCfg_symbols_sI {SS AS : Type} {s a : ℕ} {x : List Bool}
    (q : Option (ClockPhase SS AS)) (ip : Fin (x.length + 2)) (sT : Fin s → ℤ → Option Bool)
    (sP : Fin s → ℤ) (aT : Fin a → ℤ → Option Bool) (aP : Fin a → ℤ) (yT : ℤ → Option Bool)
    (yP : ℤ) (out : List Bool) (i : Fin s) :
    (hostCfg q ip sT sP aT aP yT yP out).workTapeSymbols (sI i) = sT i (sP i) := by
  simp [hostCfg, Cfg.workTapeSymbols]

/-- The symbol read on an attempt-bank tape. -/
@[simp] theorem hostCfg_symbols_aI {SS AS : Type} {s a : ℕ} {x : List Bool}
    (q : Option (ClockPhase SS AS)) (ip : Fin (x.length + 2)) (sT : Fin s → ℤ → Option Bool)
    (sP : Fin s → ℤ) (aT : Fin a → ℤ → Option Bool) (aP : Fin a → ℤ) (yT : ℤ → Option Bool)
    (yP : ℤ) (out : List Bool) (i : Fin a) :
    (hostCfg q ip sT sP aT aP yT yP out).workTapeSymbols (aI i) = aT i (aP i) := by
  simp [hostCfg, Cfg.workTapeSymbols]

/-- The symbol read on the yardstick tape. -/
@[simp] theorem hostCfg_symbols_yI {SS AS : Type} {s a : ℕ} {x : List Bool}
    (q : Option (ClockPhase SS AS)) (ip : Fin (x.length + 2)) (sT : Fin s → ℤ → Option Bool)
    (sP : Fin s → ℤ) (aT : Fin a → ℤ → Option Bool) (aP : Fin a → ℤ) (yT : ℤ → Option Bool)
    (yP : ℤ) (out : List Bool) :
    (hostCfg q ip sT sP aT aP yT yP out).workTapeSymbols yI = yT yP := by
  simp [hostCfg, Cfg.workTapeSymbols]

/-! ### The machine -/

variable (S : FinTM Bool) (A : FinNDTM Bool) (loop : Bool)

/-- No write, no move. -/
abbrev idle : Option (Option Bool) × SignType := (none, 0)

/-- Heads under the idle action stay put. -/
theorem heads_idle {n : ℕ} (P : Fin n → ℤ) : (fun i => P i + ((idle.2 : SignType) : ℤ)) = P :=
  funext fun i => by show P i + ((0 : SignType) : ℤ) = P i; simp

/-- Write an emission on the yardstick tape and advance, or do nothing. -/
def emitTo : Option Bool → Option (Option Bool) × SignType
  | some e => (some (some e), 1)
  | none => (none, 0)

/-- The transition table of the clocked restart host. -/
def clockTr (b : Bool) (q : ClockPhase S.State A.State) (inp : Option Bool)
    (w : Fin (S.k + A.k + 1) → Option Bool) :
    Action (S.k + A.k + 1) Bool (ClockPhase S.State A.State) :=
  match q with
  | .boot q =>
    let act := S.tm.tr q inp fun i => w (sI i)
    ⟨act.inputTape, slots act.workTapes (fun _ => idle) (emitTo act.output), none,
      some ((act.state.map ClockPhase.boot).getD ClockPhase.rew)⟩
  | .rew => ⟨-1, slots (fun _ => idle) (fun _ => idle) (none, -1), none, some .rew2⟩
  | .rew2 => match w yI with
    | some _ => ⟨-1, slots (fun _ => idle) (fun _ => idle) (none, -1), none, some .rew2⟩
    | none => ⟨1, slots (fun _ => idle) (fun _ => idle) (none, 1), none,
        some (.run (some A.tm.q₀) none)⟩
  | .run q c => match w yI with
    | some _ => match q with
      | some qa =>
        let act := A.tm.tr b qa inp fun i => w (aI i)
        ⟨act.inputTape, slots (fun _ => idle) act.workTapes (none, 1), none,
          some (.run act.state (capPush c act.output))⟩
      | none => ⟨0, slots (fun _ => idle) (fun _ => idle) (none, 1), none, some (.run none c)⟩
    | none => match q, c with
      | none, some (some v) => ⟨0, slots (fun _ => idle) (fun _ => idle) idle, some v, none⟩
      | _, _ =>
        if loop then ⟨0, slots (fun _ => idle) (fun _ => idle) (none, -1), none, some .p0⟩
        else ⟨0, slots (fun _ => idle) (fun _ => idle) idle, none, none⟩
  | .p0 => match w yI with
    | some _ => ⟨-1, slots (fun _ => idle) (fun _ => (none, 1)) (none, -1), none, some .p0⟩
    | none => ⟨-1, slots (fun _ => idle) (fun _ => (none, 1)) (none, 1), none, some .p1⟩
  | .p1 => match w yI with
    | some _ => ⟨0, slots (fun _ => idle) (fun _ => (none, 1)) (none, 1), none, some .p1⟩
    | none => ⟨0, slots (fun _ => idle) (fun _ => (none, 1)) (none, -1), none, some .p2⟩
  | .p2 => match w yI with
    | some _ => ⟨0, slots (fun _ => idle) (fun _ => (none, 1)) (none, -1), none, some .p2⟩
    | none => ⟨1, slots (fun _ => idle) (fun _ => (none, 1)) (none, 1), none,
        some (.run (some A.tm.q₀) none)⟩

/-- The host as a raw binary-choice machine. -/
def hostTM : NDTM (S.k + A.k + 1) Bool (ClockPhase S.State A.State) :=
  ⟨.boot S.tm.q₀, clockTr S A loop⟩

end ClockHost

/-- **The clocked restart host** [AB09, §7.4.2 and Exercise 7.6(a)]: run the yardstick machine
`S` (meant to emit `1^m`), then run `A` for `m` coins; emit `A`'s one-bit output if it has
halted with one, else halt silently (`loop = false`) or reset and retry (`loop = true`). -/
def FinNDTM.clockHost (S : FinTM Bool) (A : FinNDTM Bool) (loop : Bool) : FinNDTM Bool :=
  @FinNDTM.mk Bool (S.k + A.k + 1) (ClockPhase S.State A.State) inferInstance inferInstance
    (ClockHost.hostTM S A loop)

namespace ClockHost

variable {S : FinTM Bool} {A : FinNDTM Bool} {loop : Bool} {x : List Bool}

/-- Close the slot-by-slot equations left by `apply_hostCfg`. -/
scoped macro "host_congr" : tactic =>
  `(tactic| (congr 1 <;> (try rfl) <;> (try exact Turing.moveInputPos_zero _)
    <;> (try exact Turing.ClockHost.heads_idle _)
    <;> (try (funext i; (simp [Turing.ClockHost.tapeAfter, Turing.ClockHost.idle]); done))
    <;> (try ((simp [Turing.ClockHost.tapeAfter, Turing.capOf_append]); done))
    <;> (try ((simp [Turing.ClockHost.tapeAfter]); omega))))

/-- A host step from a live host configuration applies `clockTr`. -/
theorem stepWith_hostCfg (b : Bool) (q : ClockPhase S.State A.State) (ip : Fin (x.length + 2))
    (sT : Fin S.k → ℤ → Option Bool) (sP : Fin S.k → ℤ) (aT : Fin A.k → ℤ → Option Bool)
    (aP : Fin A.k → ℤ) (yT : ℤ → Option Bool) (yP : ℤ) (out : List Bool) :
    (hostTM S A loop).stepWith b (hostCfg (some q) ip sT sP aT aP yT yP out) =
      (clockTr S A loop b q (hostCfg (some q) ip sT sP aT aP yT yP out).inputSymbol
        (hostCfg (some q) ip sT sP aT aP yT yP out).workTapeSymbols).apply
        (hostCfg (some q) ip sT sP aT aP yT yP out) :=
  NDTM.stepWith_of_state _ b rfl

/-- The yardstick tape `1^m`. -/
abbrev yard (m : ℕ) : ℤ → Option Bool := bufferTape (List.replicate m true)

/-- The yardstick reads a mark on `[0, m)`. -/
theorem yard_of_lt {m : ℕ} {z : ℤ} (h0 : 0 ≤ z) (h : z < m) : yard m z = some true := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  simp only [yard, FinTM.bufferTape_nat, List.getElem?_replicate]
  rw [if_pos (by omega)]

/-- The yardstick reads a blank at `-1`. -/
theorem yard_neg_one (m : ℕ) : yard m (-1) = none := FinTM.bufferTape_left _

/-- The yardstick reads a blank at `m`. -/
theorem yard_len (m : ℕ) : yard m m = none := by
  simp only [yard, FinTM.bufferTape_nat, List.getElem?_replicate, lt_irrefl, if_false]

/-! ### Boot phase -/

/-- The boot-phase configuration: `S` on its bank, its output on the yardstick tape. -/
def bootCfg (c : Cfg S.k Bool S.State x) :
    Cfg (S.k + A.k + 1) Bool (ClockPhase S.State A.State) x :=
  hostCfg (some ((c.state.map ClockPhase.boot).getD ClockPhase.rew)) c.inputPos c.workTapes
    c.workTapePos (fun _ _ => none) (fun _ => 0) (bufferTape c.output) c.output.length []

/-- A boot step is a step of `S`, its emission appended to the yardstick tape.

**Proof sketch.** The boot action is `S`'s action on its bank with its emission written on `Y`
(`apply_hostCfg`); the appended cell is `FinTM.bufferTape_append`. -/
theorem boot_step (b : Bool) (c : Cfg S.k Bool S.State x) {q : S.State}
    (hq : c.state = some q) :
    (hostTM S A loop).stepWith b (bootCfg (A := A) c) = bootCfg (S.tm.step c) := by
  have hst : (bootCfg (A := A) c).state = some (.boot q) := by simp [bootCfg, hostCfg, hq]
  rw [NDTM.stepWith_of_state _ b hst]
  have hsym : ∀ i, (bootCfg (A := A) c).workTapeSymbols (sI i) = c.workTapeSymbols i :=
    fun i => by simp [bootCfg, hostCfg, Cfg.workTapeSymbols]
  have hin : (bootCfg (A := A) c).inputSymbol = c.inputSymbol := rfl
  simp only [hostTM, clockTr, hsym, hin]
  have hS : S.tm.step c = (S.tm.tr q c.inputSymbol c.workTapeSymbols).apply c := by
    simp [MultiTapeTM.step, hq]
  rw [hS]
  unfold bootCfg
  rw [apply_hostCfg]
  rcases ho : (S.tm.tr q c.inputSymbol c.workTapeSymbols).output with _ | e
  · congr 1 <;> first
      | rfl
      | (funext i; simp; done)
      | simp [tapeAfter, emitTo, Action.apply, ho]
  · congr 1 <;> first
      | rfl
      | (funext i; simp; done)
      | simp [tapeAfter, emitTo, Action.apply, ho, FinTM.bufferTape_append]

/-- **Boot run**: while `S` is live, the host simulates it step for step. -/
theorem boot_run (c : Cfg S.k Bool S.State x) (w : List Bool)
    (hlive : ∀ t < w.length, (S.tm.runFrom c t).state ≠ none) :
    (hostTM S A loop).runWith w (bootCfg (A := A) c) = bootCfg (S.tm.runFrom c w.length) := by
  induction w generalizing c with
  | nil => rfl
  | cons b w ih =>
    have h0 := hlive 0 (by simp)
    rw [MultiTapeTM.runFrom_zero] at h0
    obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp h0
    rw [NDTM.runWith_cons, boot_step b c hq, ih, List.length_cons,
      MultiTapeTM.runFrom_succ_eq_step]
    intro t ht
    rw [← MultiTapeTM.runFrom_succ_eq_step]
    exact hlive (t + 1) (by simp; omega)

/-- The host starts in the boot configuration of `S`'s start. -/
theorem initCfg_eq_bootCfg :
    (hostTM S A loop).initCfg x = bootCfg (A := A) (S.tm.initCfg x) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext j z
    revert j
    refine slots_cases (fun i => ?_) (fun i => ?_) ?_ <;> simp [bootCfg, hostCfg, Cfg.init]
  · funext j
    revert j
    refine slots_cases (fun i => ?_) (fun i => ?_) ?_ <;> simp [bootCfg, hostCfg, Cfg.init]

/-! ### Rewinding -/

/-- The input position after `j` left moves (clamped at `0`). -/
def inLeft {n : ℕ} : Fin (n + 2) → ℕ → Fin (n + 2)
  | ip, 0 => ip
  | ip, j + 1 => inLeft (moveInputPos ip (-1)) j

/-- `j` left moves subtract `j`, clamped at `0`. -/
theorem inLeft_val {n : ℕ} (ip : Fin (n + 2)) (j : ℕ) : (inLeft ip j).val = ip.val - j := by
  induction j generalizing ip with
  | zero => rfl
  | succ j ih =>
    rw [inLeft, ih]
    by_cases h : ip = 0
    · subst h; simp
    · have hv : ip.val ≠ 0 := fun h' => h (Fin.ext h')
      rw [show (-1 : SignType) = .neg from rfl, moveInputPos_neg_of_ne_left ip h]
      simp only
      omega

/-- After at least `ip` left moves, one right move puts the input head on its start cell. -/
theorem moveInputPos_inLeft {n : ℕ} (ip : Fin (n + 2)) {j : ℕ} (hj : ip.val ≤ j) :
    moveInputPos (inLeft ip j) 1 = 1 := by
  have h0 : inLeft ip j = 0 := Fin.ext (by rw [inLeft_val, Fin.val_zero]; omega)
  rw [h0, show (1 : SignType) = .pos from rfl, moveInputPos_pos_of_ne_right _ (by simp)]
  exact Fin.ext (by simp)

variable (m : ℕ)

/-- One rewind step over a mark. -/
theorem rew2_step (b : Bool) (ip : Fin (x.length + 2)) (sT : Fin S.k → ℤ → Option Bool)
    (sP : Fin S.k → ℤ) (aT : Fin A.k → ℤ → Option Bool) (aP : Fin A.k → ℤ) (z : ℤ)
    (hz : yard m z = some true) :
    (hostTM S A loop).stepWith b (hostCfg (some .rew2) ip sT sP aT aP (yard m) z []) =
      hostCfg (some .rew2) (moveInputPos ip (-1)) sT sP aT aP (yard m) (z - 1) [] := by
  rw [stepWith_hostCfg]
  simp only [clockTr, hostCfg_symbols_yI, hz]
  rw [apply_hostCfg]
  host_congr

/-- The first rewind step moves the yardstick and input heads left. -/
theorem rew_step (b : Bool) (ip : Fin (x.length + 2)) (sT : Fin S.k → ℤ → Option Bool)
    (sP : Fin S.k → ℤ) (aT : Fin A.k → ℤ → Option Bool) (aP : Fin A.k → ℤ) (z : ℤ) :
    (hostTM S A loop).stepWith b (hostCfg (some .rew) ip sT sP aT aP (yard m) z []) =
      hostCfg (some .rew2) (moveInputPos ip (-1)) sT sP aT aP (yard m) (z - 1) [] := by
  rw [stepWith_hostCfg]
  simp only [clockTr]
  rw [apply_hostCfg]
  host_congr

/-- The rewind's turnaround: at the left blank, step right and start the attempt. -/
theorem rew2_turn (b : Bool) (ip : Fin (x.length + 2)) (sT : Fin S.k → ℤ → Option Bool)
    (sP : Fin S.k → ℤ) (aT : Fin A.k → ℤ → Option Bool) (aP : Fin A.k → ℤ) :
    (hostTM S A loop).stepWith b (hostCfg (some .rew2) ip sT sP aT aP (yard m) (-1) []) =
      hostCfg (some (.run (some A.tm.q₀) none)) (moveInputPos ip 1) sT sP aT aP (yard m) 0
        [] := by
  rw [stepWith_hostCfg]
  simp only [clockTr, hostCfg_symbols_yI, yard_neg_one]
  rw [apply_hostCfg]
  host_congr

/-- Rewinding over `j` marks. -/
theorem rew2_marks (ip : Fin (x.length + 2)) (sT : Fin S.k → ℤ → Option Bool)
    (sP : Fin S.k → ℤ) (aT : Fin A.k → ℤ → Option Bool) (aP : Fin A.k → ℤ) (w : List Bool)
    (hj : w.length ≤ m) :
    (hostTM S A loop).runWith w
        (hostCfg (some .rew2) ip sT sP aT aP (yard m) ((w.length : ℤ) - 1) []) =
      hostCfg (some .rew2) (inLeft ip w.length) sT sP aT aP (yard m) (-1) [] := by
  induction w generalizing ip with
  | nil => simp [inLeft]
  | cons b w ih =>
    simp only [List.length_cons] at hj ⊢
    rw [NDTM.runWith_cons, rew2_step m b ip sT sP aT aP (((w.length + 1 : ℕ) : ℤ) - 1)
      (yard_of_lt (by omega) (by push_cast; omega))]
    have h : ((w.length + 1 : ℕ) : ℤ) - 1 - 1 = (w.length : ℤ) - 1 := by push_cast; omega
    rw [h, ih _ (by omega)]
    rfl

/-- **Rewind run**: from the end of the yardstick, `m + 2` steps bring the yardstick head to
its first mark, move the input head `m + 1` cells left and one right, and start the attempt.

**Proof sketch.** One step left, `m` steps over the marks (`rew2_marks`), and the turnaround
(`rew2_turn`). -/
theorem rewind_run (ip : Fin (x.length + 2)) (sT : Fin S.k → ℤ → Option Bool)
    (sP : Fin S.k → ℤ) (aT : Fin A.k → ℤ → Option Bool) (aP : Fin A.k → ℤ) (w : List Bool)
    (hw : w.length = m + 2) :
    (hostTM S A loop).runWith w (hostCfg (some .rew) ip sT sP aT aP (yard m) m []) =
      hostCfg (some (.run (some A.tm.q₀) none)) (moveInputPos (inLeft ip (m + 1)) 1) sT sP aT aP
        (yard m) 0 [] := by
  rcases w with _ | ⟨b, w⟩
  · simp at hw
  rw [NDTM.runWith_cons, rew_step, ← List.take_append_drop m w, NDTM.runWith_append]
  have ht : (w.take m).length = m := List.length_take_of_le (by simp at hw; omega)
  have hrw := rew2_marks (S := S) (A := A) (loop := loop) m (moveInputPos ip (-1)) sT sP aT aP
    (w.take m) (by omega)
  rw [ht] at hrw
  rw [hrw]
  have hd : (w.drop m).length = 1 := by simp at hw ⊢; omega
  rcases hdw : w.drop m with _ | ⟨b', _ | ⟨b'', r⟩⟩
  · simp [hdw] at hd
  · rw [NDTM.runWith_cons, rew2_turn, NDTM.runWith_nil]
    rfl
  · simp [hdw] at hd

/-! ### The clocked attempt -/

/-- The attempt-phase configuration: `A`'s configuration on its bank, its output captured, and
the yardstick head at `j`. -/
def runCfg (a : Cfg A.k Bool A.State x) (j : ℤ) (sT : Fin S.k → ℤ → Option Bool)
    (sP : Fin S.k → ℤ) : Cfg (S.k + A.k + 1) Bool (ClockPhase S.State A.State) x :=
  hostCfg (some (.run a.state (capOf a.output))) a.inputPos sT sP a.workTapes a.workTapePos
    (yard m) j []

/-- Before the timeout, a host step is a step of `A` under the same coin.

**Proof sketch.** `Y` reads a mark. If `A` has halted, only `Y` moves; otherwise the host applies
`A`'s action on its bank, and the captured summary follows `capOf_append`. -/
theorem run_step (b : Bool) (a : Cfg A.k Bool A.State x) (j : ℕ) (hj : j < m)
    (sT : Fin S.k → ℤ → Option Bool) (sP : Fin S.k → ℤ) :
    (hostTM S A loop).stepWith b (runCfg m a j sT sP) =
      runCfg m (A.tm.stepWith b a) ((j + 1 : ℕ) : ℤ) sT sP := by
  have hY : (runCfg (S := S) (A := A) m a j sT sP).workTapeSymbols yI = some true := by
    simp only [runCfg, hostCfg_symbols_yI]
    exact yard_of_lt (by omega) (by omega)
  cases hq : a.state with
  | none =>
    have hst : (runCfg (S := S) m a j sT sP).state = some (.run none (capOf a.output)) := by
      simp [runCfg, hostCfg, hq]
    rw [NDTM.stepWith_of_state _ b hst, NDTM.stepWith_of_halt hq]
    simp only [hostTM, clockTr, hY]
    unfold runCfg
    rw [apply_hostCfg, hq]
    host_congr
  | some qa =>
    have hst : (runCfg (S := S) m a j sT sP).state = some (.run (some qa) (capOf a.output)) := by
      simp [runCfg, hostCfg, hq]
    rw [NDTM.stepWith_of_state _ b hst, NDTM.stepWith_of_state A.tm b hq]
    have hsym : (fun i => (runCfg (S := S) m a j sT sP).workTapeSymbols (aI i)) =
        a.workTapeSymbols := funext fun i => by simp [runCfg, hostCfg, Cfg.workTapeSymbols]
    have hin : (runCfg (S := S) m a j sT sP).inputSymbol = a.inputSymbol := rfl
    simp only [hostTM, clockTr, hY]
    rw [hsym, hin]
    unfold runCfg
    rw [apply_hostCfg]
    have hst' : ((A.tm.tr b qa a.inputSymbol a.workTapeSymbols).apply a).state =
        (A.tm.tr b qa a.inputSymbol a.workTapeSymbols).state := rfl
    rw [hst', show ((A.tm.tr b qa a.inputSymbol a.workTapeSymbols).apply a).output =
      a.output ++ (A.tm.tr b qa a.inputSymbol a.workTapeSymbols).output.toList from rfl,
      capOf_append]
    host_congr

/-- **Attempt run**: before the timeout, the host runs `A` under the same coins. -/
theorem run_run (a : Cfg A.k Bool A.State x) (j : ℕ) (sT : Fin S.k → ℤ → Option Bool)
    (sP : Fin S.k → ℤ) (u : List Bool) (hj : j + u.length ≤ m) :
    (hostTM S A loop).runWith u (runCfg m a j sT sP) =
      runCfg m (A.tm.runWith u a) ((j + u.length : ℕ) : ℤ) sT sP := by
  induction u generalizing a j with
  | nil => rfl
  | cons b u ih =>
    simp only [List.length_cons] at hj ⊢
    rw [NDTM.runWith_cons, NDTM.runWith_cons, run_step m b a j (by omega), ih _ _ (by omega)]
    congr 2
    omega

/-- `run_run` from the yardstick's first mark. -/
theorem run_run_zero (a : Cfg A.k Bool A.State x) (sT : Fin S.k → ℤ → Option Bool)
    (sP : Fin S.k → ℤ) (u : List Bool) (hu : u.length ≤ m) :
    (hostTM S A loop).runWith u (runCfg m a 0 sT sP) =
      runCfg m (A.tm.runWith u a) u.length sT sP := by
  have := run_run (loop := loop) m a 0 sT sP u (by omega)
  simpa using this

/-- **Timeout, success**: an attempt that has halted with output `[v]` makes the host emit
`v` and halt. -/
theorem timeout_success (b : Bool) (a : Cfg A.k Bool A.State x) (sT : Fin S.k → ℤ → Option Bool)
    (sP : Fin S.k → ℤ) {v : Bool} (ha : a.state = none) (ho : a.output = [v]) :
    (hostTM S A loop).stepWith b (runCfg m a m sT sP) =
      hostCfg none a.inputPos sT sP a.workTapes a.workTapePos (yard m) m [v] := by
  have hst : (runCfg (S := S) m a m sT sP).state = some (.run none (some (some v))) := by
    simp [runCfg, hostCfg, ha, ho, capOf]
  rw [NDTM.stepWith_of_state _ b hst]
  simp only [hostTM, clockTr, runCfg, hostCfg_symbols_yI, yard_len]
  rw [apply_hostCfg]
  host_congr

/-- **Timeout, failure**: otherwise the host resets (`loop`) or halts silently.

**Proof sketch.** `Y` reads a blank; since `A` has not halted with a one-bit output
(`capOf_eq_some_some`), the transition takes its second branch. -/
theorem timeout_fail (b : Bool) (a : Cfg A.k Bool A.State x) (sT : Fin S.k → ℤ → Option Bool)
    (sP : Fin S.k → ℤ) (hfail : ¬ (a.state = none ∧ ∃ v, a.output = [v])) :
    (hostTM S A loop).stepWith b (runCfg m a m sT sP) =
      if loop then hostCfg (some .p0) a.inputPos sT sP a.workTapes a.workTapePos (yard m)
        ((m : ℤ) - 1) []
      else hostCfg none a.inputPos sT sP a.workTapes a.workTapePos (yard m) m [] := by
  have hst : (runCfg (S := S) m a m sT sP).state = some (.run a.state (capOf a.output)) := by
    simp [runCfg, hostCfg]
  rw [NDTM.stepWith_of_state _ b hst]
  have hY : (runCfg (S := S) (A := A) m a m sT sP).workTapeSymbols yI = none := by
    simp [runCfg]
  have hnot : ∀ v, ¬ (a.state = none ∧ capOf a.output = some (some v)) := fun v h =>
    hfail ⟨h.1, v, capOf_eq_some_some.mp h.2⟩
  have hgo : clockTr S A loop b (.run a.state (capOf a.output))
      (runCfg (S := S) m a m sT sP).inputSymbol (runCfg (S := S) m a m sT sP).workTapeSymbols =
      if loop then ⟨0, slots (fun _ => idle) (fun _ => idle) (none, -1), none, some .p0⟩
      else ⟨0, slots (fun _ => idle) (fun _ => idle) idle, none, none⟩ := by
    simp only [clockTr, hY]
    rcases hq : a.state with _ | qa
    · rcases hc : capOf a.output with _ | _ | v
      · rfl
      · rfl
      · exact absurd ⟨hq, hc⟩ (hnot v)
    · rfl
  change (clockTr S A loop b _ _ _).apply _ = _
  rw [hgo]
  cases loop
  · simp only [Bool.false_eq_true, if_false]
    unfold runCfg
    rw [apply_hostCfg]
    host_congr
  · simp only [if_true]
    unfold runCfg
    rw [apply_hostCfg]
    host_congr

end ClockHost

end Turing
