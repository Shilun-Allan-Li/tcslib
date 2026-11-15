/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Tactic.Ring
import TCSlib.Complexity.TuringMachine.Build.ModuleHost

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The host of the repetition machine

The repetition machine's instance of the clean-module host `Turing.ModuleHost.hostTM`
(`TCSlib.Complexity.TuringMachine.Build.ModuleHost`, host H14 of `machine-library-design.md` §14),
for `Complexity.polyTimeComputable_iterateFind` (`TCSlib.Complexity.Randomized.Build.IterateFind`
assembles the machine; the theorem itself lives in `TCSlib.Complexity.Randomized.Repetition`, the
load-bearing lemma of the Pass–shelat campaign, foundation decision D11 of
`PassShelatChapter2-4Plan.md`). Nothing here mentions the repetition lemma's data.

## Construction (DESIGN.md §2.6, steps 2–5, as built; see its as-built erratum)

* **The copier.** A one-tape, two-state machine (`copyTM`) writes the native input on tape 0 and
  returns both heads (`copy_clean`): the startup module of the loop body, since a clean call sees
  only its tape-resident argument. It re-derives, as a parallel routine and not a copy, the input
  copier of the private emit-iteration body `TCSlib.Complexity.TuringMachine.Build.EmitIterBody`.
* **The host.** Five modules (copier, startup install, verdict install, step install, payload
  emit) run in the clean-module host with three control states (`hostTM`): the loop **anchor**
  `inl 0` (never a module-internal state, the panel repair J2-16/J3-6), which dispatches into the
  verdict module (`host_dispatch`); the **branch** `inl 1`, which reads the first cell of tape 0
  and dispatches into the payload or the step module (`host_branch`); and the **halt** state
  `inl 2` (`host_halt`). Each module's halt passes control to its fixed return state (`hostRet`).
  Module calls inside the host are `Turing.ModuleHost.host_call` and `host_clean`.

## Main definitions

* `Complexity.IterateFind.copyTM` — the input copier.
* `Complexity.IterateFind.hostCtrl`, `hostRet`, `hostTM` — the host's control table over its
  three control states, the return states of the five modules, and the host.

## Main results

* `Complexity.IterateFind.copy_clean` — the copier's contract.
* `Complexity.IterateFind.host_dispatch`, `host_branch`, `host_halt` — the host's control steps.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Algorithm 38.5 and Theorem 35.1: the repeated-adversary machine this host realizes.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2–1.3, time-bounded multi-tape machines.)
-/

namespace Complexity.IterateFind

open Turing

/-! ### The input copier -/

/-- The input copier: a one-tape, two-state machine that writes the native input on tape 0
and returns both heads to their seam positions. State `0` copies (read a bit, write it,
advance both heads; at the right blank move both heads left into state `1`); state `1`
walks both heads left while the input head reads a bit, and at the left blank moves both
heads right and halts. -/
@[simps (config := { isSimp := false }) k]
def copyTM : FinTM Bool where
  k := 1
  State := Fin 2
  tm := { q₀ := 0
          tr := fun q inp _ =>
            if q = 0 then
              match inp with
              | some b => ⟨.pos, fun _ => (some (some b), .pos), none, some 0⟩
              | none => ⟨.neg, fun _ => (none, .neg), none, some 1⟩
            else
              match inp with
              | some _ => ⟨.neg, fun _ => (none, .neg), none, some 1⟩
              | none => ⟨.pos, fun _ => (none, .pos), none, none⟩ }

/-- Configurations of the copier: control `q`, input head at position `i`, tape 0 holding
`w` from the origin with its head at cell `z`, nothing emitted. -/
private def copyCfg (x : List Bool) (q : Option (Fin 2)) (i : ℕ) (hi : i < x.length + 2)
    (w : List Bool) (z : ℤ) : Cfg 1 Bool (Fin 2) x :=
  ⟨q, ⟨i, hi⟩, fun _ => FinTM.bufferTape w, fun _ => z, []⟩

/-- One copying step: bit `j` is read, written at cell `j`, and both heads advance.

**Proof sketch.** The input head at position `j + 1` reads `x[j]` (`inputSymbolInner`); the
action writes it at cell `j`, which turns `bufferTape (x.take j)` into
`bufferTape (x.take (j + 1))` (`List.take_succ_eq_append_getElem`, `bufferTape_append`), and
both heads move right (`moveInputPos_pos_of_ne_right`). -/
private lemma copy_step (x : List Bool) (j : ℕ) (hj : j < x.length) :
    copyTM.tm.step (copyCfg x (some 0) (j + 1) (by omega) (x.take j) j) =
      copyCfg x (some 0) (j + 1 + 1) (by omega) (x.take (j + 1)) ((j + 1 : ℕ) : ℤ) := by
  have hsym : (copyCfg x (some 0) (j + 1) (by omega) (x.take j) j).inputSymbol = some x[j] :=
    inputSymbolInner j (by simp [copyCfg]; omega) hj
  have hs : (copyCfg x (some 0) (j + 1) (by omega) (x.take j) j).state = some 0 := rfl
  unfold MultiTapeTM.step
  rw [hs]
  dsimp only
  rw [hsym]
  show (⟨.pos, fun _ => (some (some x[j]), .pos), none, some 0⟩ :
    Action 1 Bool (Fin 2)).apply _ = _
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · apply Fin.ext
    simp only [Action.apply, copyCfg]
    rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
  · funext i
    simp only [Action.apply, copyCfg]
    rw [List.take_succ_eq_append_getElem hj, FinTM.bufferTape_append, List.length_take,
      Nat.min_eq_left hj.le]
  · funext i
    simp [Action.apply, copyCfg]

/-- At the right blank the copier turns: both heads move left and the control becomes `1`.

**Proof sketch.** At position `|x| + 1` the input symbol is the right blank
(`inputSymbol_at`); the action writes nothing, moves the input head left
(`moveInputPos_neg_val`) and the work head to `|x| - 1`. -/
private lemma copy_turn (x : List Bool) :
    copyTM.tm.step (copyCfg x (some 0) (x.length + 1) (by omega) x x.length) =
      copyCfg x (some 1) x.length (by omega) x (x.length - 1) := by
  have hsym : (copyCfg x (some 0) (x.length + 1) (by omega) x x.length).inputSymbol = none := by
    rw [FinTM.inputSymbol_at _ x.length le_rfl rfl]
    simp
  have hs : (copyCfg x (some 0) (x.length + 1) (by omega) x x.length).state = some 0 := rfl
  unfold MultiTapeTM.step
  rw [hs]
  dsimp only
  rw [hsym]
  show (⟨.neg, fun _ => (none, .neg), none, some 1⟩ : Action 1 Bool (Fin 2)).apply _ = _
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · apply Fin.ext
    simp only [Action.apply, copyCfg]
    rw [FinTM.moveInputPos_neg_val]
    simp
  · funext i
    simp [Action.apply, copyCfg]
  · funext i
    simp [Action.apply, copyCfg, sub_eq_add_neg]

/-- The rewind: from input position `p ≤ |x|` in control `1`, `p` left moves of both heads
reach input position `0`.

**Proof sketch.** Induction on `p`, generalizing the work head: at position `p + 1 ≤ |x|` the
input head reads `x[p]`, so one step moves both heads left without writing, and the
induction hypothesis finishes the remaining `p` steps. -/
private lemma copy_rewind (x : List Bool) (p : ℕ) (hp : p ≤ x.length) (z : ℤ) :
    copyTM.tm.runFrom (copyCfg x (some 1) p (by omega) x z) p =
      copyCfg x (some 1) 0 (by omega) x (z - p) := by
  induction p generalizing z with
  | zero => simp [copyCfg]
  | succ p ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hstep : copyTM.tm.step (copyCfg x (some 1) (p + 1) (by omega) x z) =
        copyCfg x (some 1) p (by omega) x (z - 1) := by
      have hsym : (copyCfg x (some 1) (p + 1) (by omega) x z).inputSymbol = some x[p] :=
        inputSymbolInner p (by simp [copyCfg]; omega) (by omega)
      have hs : (copyCfg x (some 1) (p + 1) (by omega) x z).state = some 1 := rfl
      unfold MultiTapeTM.step
      rw [hs]
      dsimp only
      rw [hsym]
      show (⟨.neg, fun _ => (none, .neg), none, some 1⟩ : Action 1 Bool (Fin 2)).apply _ = _
      refine Cfg.ext rfl ?_ ?_ ?_ rfl
      · apply Fin.ext
        simp only [Action.apply, copyCfg]
        rw [FinTM.moveInputPos_neg_val]
        simp
      · funext i
        simp [Action.apply, copyCfg]
      · funext i
        simp [Action.apply, copyCfg, sub_eq_add_neg]
    rw [hstep, ih (by omega)]
    simp only [copyCfg, Nat.cast_succ]
    congr 1
    funext _
    ring

/-- At the left blank the copier moves both heads right and halts. -/
private lemma copy_finish (x : List Bool) (z : ℤ) :
    copyTM.tm.step (copyCfg x (some 1) 0 (by omega) x z) =
      copyCfg x none 1 (by omega) x (z + 1) := by
  have hsym : (copyCfg x (some 1) 0 (by omega) x z).inputSymbol = none := by
    simp [Cfg.inputSymbol, copyCfg]
  have hs : (copyCfg x (some 1) 0 (by omega) x z).state = some 1 := rfl
  unfold MultiTapeTM.step
  rw [hs]
  dsimp only
  rw [hsym]
  show (⟨.pos, fun _ => (none, .pos), none, none⟩ : Action 1 Bool (Fin 2)).apply _ = _
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · apply Fin.ext
    simp only [Action.apply, copyCfg]
    rw [moveInputPos_pos_of_ne_right _ (by simp)]
  · funext i
    simp [Action.apply, copyCfg]
  · funext i
    simp [Action.apply, copyCfg]

/-- **The copier's contract.** From the empty seam over native input `x`, the copier halts
after exactly `2|x| + 2` steps at the seam holding `x` on tape 0, never halting earlier.

**Proof sketch.** `|x|` copying steps (`copy_step`), the turn (`copy_turn`), `|x|` rewind
steps (`copy_rewind`), the final right move and halt (`copy_finish`); liveness before the
end from the live configuration at time `2|x| + 1` (`Turing.ModuleHost.live_prefix`). -/
lemma copy_clean (x : List Bool) :
    (∀ v < 2 * x.length + 2,
      ¬(copyTM.tm.runFrom (Cfg.ofWords (input := x) (0 : Fin 2) (stateWord 1 [])) v).Halted) ∧
    copyTM.tm.runFrom (Cfg.ofWords (input := x) (0 : Fin 2) (stateWord 1 []))
        (2 * x.length + 2) =
      {Cfg.ofWords (input := x) (0 : Fin 2) (stateWord 1 x) with state := none} := by
  have hi : Cfg.ofWords (input := x) (0 : Fin 2) (stateWord 1 []) =
      copyCfg x (some 0) 1 (by omega) [] 0 := by
    refine Cfg.ext rfl rfl ?_ rfl rfl
    funext i
    simp [Cfg.ofWords, copyCfg, stateWord]
  have hcopy : ∀ j (hj : j ≤ x.length),
      copyTM.tm.runFrom (copyCfg x (some 0) 1 (by omega) [] 0) j =
        copyCfg x (some 0) (j + 1) (by omega) (x.take j) j := by
    intro j
    induction j with
    | zero => intro _; simp [copyCfg]
    | succ j ih =>
      intro hj
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), copy_step x j (by omega)]
  have hmid : copyTM.tm.runFrom (copyCfg x (some 0) 1 (by omega) [] 0) (2 * x.length + 1) =
      copyCfg x (some 1) 0 (by omega) x (-1) := by
    rw [show 2 * x.length + 1 = x.length + 1 + x.length by ring, MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_succ_eq_step', hcopy x.length le_rfl]
    simp only [List.take_length]
    rw [copy_turn, copy_rewind x x.length le_rfl]
    simp only [copyCfg]
    congr 1
    funext _
    ring
  refine ⟨?_, ?_⟩
  · intro v hv
    rw [hi]
    exact ModuleHost.live_prefix copyTM.tm _ (2 * x.length + 1) (by rw [hmid]; simp [copyCfg]) v
      (by omega)
  · rw [hi, MultiTapeTM.runFrom_succ_eq_step', hmid, copy_finish]
    refine Cfg.ext rfl ?_ ?_ ?_ rfl
    · apply Fin.ext; simp [copyCfg, Cfg.ofWords]
    · funext i
      simp [copyCfg, Cfg.ofWords, stateWord]
    · funext i
      simp [copyCfg, Cfg.ofWords]


/-! ### The host -/

/-- The control table of the repetition machine's host over its three control states, each step
stationary and silent: the loop anchor `0` dispatches into the verdict module (`2`); the branch
state `1` reads the first cell of tape 0 and dispatches into the payload module (`4`) if it holds
`true`, into the step module (`3`) otherwise; the halt state `2` halts. -/
def hostCtrl (M : Fin 5 → FinTM Bool) (K : ℕ) (c : Fin 3) (_inp : Option Bool)
    (work : Fin (K + 1) → Option Bool) : Action (K + 1) Bool (ModuleHost.State (Fin 3) M) :=
  if c = 0 then FinTM.controlAction 0 (some (ModuleHost.entry M 2))
  else if c = 1 then
    FinTM.controlAction 0
      (some (if work 0 = some true then ModuleHost.entry M 4 else ModuleHost.entry M 3))
  else FinTM.controlAction 0 none

/-- The control table: `hostCtrl M K c inp work` is the stationary silent action into the
verdict module's entry if `c = 0`, into the payload module's entry (`work 0 = some true`) or the
step module's entry (otherwise) if `c = 1`, and the halting action if `c = 2`. -/
theorem hostCtrl_eq (M : Fin 5 → FinTM Bool) (K : ℕ) (c : Fin 3) (inp : Option Bool)
    (work : Fin (K + 1) → Option Bool) :
    hostCtrl M K c inp work =
      if c = 0 then FinTM.controlAction 0 (some (ModuleHost.entry M 2))
      else if c = 1 then
        FinTM.controlAction 0
          (some (if work 0 = some true then ModuleHost.entry M 4 else ModuleHost.entry M 3))
      else FinTM.controlAction 0 none :=
  rfl

/-- The return states of the five modules: copier (`0`) → startup install's entry; startup
install (`1`) → anchor `inl 0`; verdict (`2`) → branch `inl 1`; step (`3`) → anchor `inl 0`;
payload emit (`4`) → halt state `inl 2`. -/
def hostRet (M : Fin 5 → FinTM Bool) (i : Fin 5) : ModuleHost.State (Fin 3) M :=
  if i = 0 then ModuleHost.entry M 1 else if i = 2 then .inl 1 else if i = 4 then .inl 2
  else .inl 0

/-- The copier returns to the startup install's entry: `hostRet M 0 = entry M 1`. -/
theorem hostRet_zero (M : Fin 5 → FinTM Bool) : hostRet M 0 = ModuleHost.entry M 1 :=
  rfl

/-- The startup install returns to the anchor: `hostRet M 1 = inl 0`. -/
theorem hostRet_one (M : Fin 5 → FinTM Bool) : hostRet M 1 = .inl 0 :=
  rfl

/-- The verdict module returns to the branch state: `hostRet M 2 = inl 1`. -/
theorem hostRet_two (M : Fin 5 → FinTM Bool) : hostRet M 2 = .inl 1 :=
  rfl

/-- The step module returns to the anchor: `hostRet M 3 = inl 0`. -/
theorem hostRet_three (M : Fin 5 → FinTM Bool) : hostRet M 3 = .inl 0 :=
  rfl

/-- The payload module returns to the halt state: `hostRet M 4 = inl 2`. -/
theorem hostRet_four (M : Fin 5 → FinTM Bool) : hostRet M 4 = .inl 2 :=
  rfl

/-- The finite host of the repetition machine: the clean-module host
`Turing.ModuleHost.hostTM` over the five modules `M` with `K + 1` shared tapes (tape 0 carries
the state word), the three control states of `hostCtrl`, the return states `hostRet`, and the
copier's entry as start state. A reducible abbreviation, so the host's lemmas
(`Turing.ModuleHost.host_call`, `host_clean`, `hostTM_step_inl`, …) apply to it directly. -/
abbrev hostTM (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1) : FinTM Bool :=
  ModuleHost.hostTM M (K + 1) hk (hostCtrl M K) (hostRet M) (ModuleHost.entry M 0)

/-- The repetition machine's host is
`Turing.ModuleHost.hostTM M (K + 1) hk (hostCtrl M K) (hostRet M) (entry M 0)`. -/
theorem hostTM_eq (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1) :
    hostTM M K hk =
      ModuleHost.hostTM M (K + 1) hk (hostCtrl M K) (hostRet M) (ModuleHost.entry M 0) :=
  rfl

/-- The anchor dispatches into the verdict module in one stationary step: from the seam at
`inl 0` holding `w`, one step reaches the seam at the verdict module's entry holding `w`. -/
theorem host_dispatch (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1)
    (x w : List Bool) :
    (hostTM M K hk).tm.step (Cfg.ofWords (input := x) (.inl 0) (stateWord (K + 1) w)) =
      Cfg.ofWords (ModuleHost.entry M 2) (stateWord (K + 1) w) := by
  rw [ModuleHost.hostTM_step_inl _ _ _ _ _ _ _ 0 rfl]
  change (FinTM.controlAction 0 (some (ModuleHost.entry M 2))).apply _ = _
  rw [FinTM.controlAction_apply, moveInputPos_zero]
  rfl

/-- The branch state reads the first cell of tape 0 — the verdict `b` of a verdict word `w`
with `w[0]? = some b` — and dispatches, in one stationary step, into the payload module (`b`
true) or the step module (`b` false), at the seam holding `w`. -/
theorem host_branch (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1)
    (x : List Bool) (b : Bool) (w : List Bool) (hw : w[0]? = some b) :
    (hostTM M K hk).tm.step (Cfg.ofWords (input := x) (.inl 1) (stateWord (K + 1) w)) =
      Cfg.ofWords (ModuleHost.entry M (if b then 4 else 3)) (stateWord (K + 1) w) := by
  have hread : (Cfg.ofWords (input := x) (.inl 1 : ModuleHost.State (Fin 3) M)
      (stateWord (K + 1) w)).workTapeSymbols 0 = some b := by
    simp [Cfg.ofWords, Cfg.workTapeSymbols, stateWord, FinTM.bufferTape, hw]
  rw [ModuleHost.hostTM_step_inl _ _ _ _ _ _ _ 1 rfl]
  show (FinTM.controlAction 0 (some (if (Cfg.ofWords (input := x)
    (.inl 1 : ModuleHost.State (Fin 3) M) (stateWord (K + 1) w)).workTapeSymbols 0 = some true
      then ModuleHost.entry M 4 else ModuleHost.entry M 3))).apply _ = _
  rw [hread, FinTM.controlAction_apply, moveInputPos_zero]
  cases b <;> rfl

/-- The halt state halts without emitting: from the seam at `inl 2` holding `w` with output `o`,
one step reaches the same seam with control `none` and output `o`. -/
theorem host_halt (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1)
    (x w o : List Bool) :
    (hostTM M K hk).tm.step
        {Cfg.ofWords (input := x) (.inl 2) (stateWord (K + 1) w) with output := o} =
      {Cfg.ofWords (input := x) (.inl 2 : ModuleHost.State (Fin 3) M) (stateWord (K + 1) w)
        with state := none, output := o} := by
  rw [ModuleHost.hostTM_step_inl _ _ _ _ _ _ _ 2 rfl]
  change (FinTM.controlAction 0 none).apply _ = _
  rw [FinTM.controlAction_apply, moveInputPos_zero]

end Complexity.IterateFind
