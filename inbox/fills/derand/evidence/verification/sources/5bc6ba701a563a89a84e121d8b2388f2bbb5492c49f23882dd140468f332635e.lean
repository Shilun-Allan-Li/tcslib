/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.PTM
import TCSlib.Complexity.SpaceComplexity.Machines.NARMProb

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Repeating a space-bounded PTM

The machine behind error reduction in randomized space [AB09, §7.7, p. 139]: `amp N r dec` runs
the PTM `N` on its input `r + 1` times in sequence, each run on its own block of fresh work
tapes, rewinds the input head between runs, counts the runs that output `[true]` in its finite
control, and finally outputs `[dec count]`.

The analysis composes a run of `N` with what follows it: if a machine simulates `N` step by
step and its continuation from every halted `N`-configuration has a probability depending
only on whether that run accepted, the probabilities combine linearly (`randProb_comp`).
Halting and head bounds compose the same way (`halts_comp`, `reach_comp`).

## Main definitions

* `Randomized.Amplify.amp` — the repeated machine.
* `Randomized.Amplify.emb` — the configuration of `amp` simulating a configuration of `N`.

## Main results

* `Randomized.Amplify.halts_comp_pos` (with an input-head bound) and its corollary
  `Randomized.Amplify.halts_comp`, `Randomized.Amplify.randProb_comp`,
  `Randomized.Amplify.reach_comp` — composing a simulated run with its continuation.
* `Randomized.Amplify.step_emb` — the machine simulates `N` step by step.
* `Randomized.Amplify.rewind_run_pos` and its corollary `Randomized.Amplify.rewind_run`,
  `Randomized.Amplify.rewind_last` — rewinding between runs.

The halting, probability and space analysis is in `TCSlib.Complexity.Randomized.SpaceAmplifyRun`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized.Amplify

open Turing Complexity Complexity.LogProg

/-! ## Composing a run with its continuation -/

section Compose

variable {K K' : ℕ} {S S' : Type} {x : List Bool} {N : NDTM K Bool S} {M : NDTM K' Bool S'}
  {φ : Cfg K Bool S x → Cfg K' Bool S' x}

/-- One step moves the input head at most one cell right. -/
theorem inputPos_stepWith_le (tm : NDTM K Bool S) (b : Bool) (c : Cfg K Bool S x) :
    (tm.stepWith b c).inputPos.val ≤ c.inputPos.val + 1 := by
  have key : ∀ {n : ℕ} (q : Fin (n + 2)) (s : SignType), (moveInputPos q s).val ≤ q.val + 1 := by
    intro n ⟨q, hq⟩ s
    rw [moveInputPos_val _ q hq s]
    cases s <;> dsimp only <;> omega
  unfold NDTM.stepWith
  split
  · omega
  · exact key _ _

/-- `halts_comp` with the input head tracked: the continuation need only halt from halted
configurations whose input head is at most `B`, if the run starts at most `n` cells before `B`
and halts within `n`.

**Proof sketch.** Induction on `n`, as `halts_comp`; each step moves the input head at most one
cell right (`inputPos_stepWith_le`), so the invariant `inputPos + n ≤ B` is kept. -/
theorem halts_comp_pos (hstep : ∀ c b, c.state ≠ none → M.stepWith b (φ c) = φ (N.stepWith b c))
    {m B : ℕ} (hφ : ∀ c, c.state = none → c.inputPos.val ≤ B → ∀ w : List Bool, w.length = m →
      (M.runWith w (φ c)).state = none) :
    ∀ (n : ℕ) (c : Cfg K Bool S x), c.inputPos.val + n ≤ B →
      (∀ u : List Bool, u.length = n → (N.runWith u c).state = none) →
      ∀ w : List Bool, w.length = n + m → (M.runWith w (φ c)).state = none := by
  intro n
  induction n with
  | zero =>
    intro c hB hc w hw
    exact hφ c (hc [] rfl) (by omega) w (by simpa using hw)
  | succ n ih =>
    intro c hB hc w hw
    by_cases hs : c.state = none
    · have h := hφ c hs (by omega) (w.take m) (List.length_take_of_le (by omega))
      rw [← List.take_append_drop m w, NDTM.runWith_append, NDTM.runWith_of_halt _ h]
      exact h
    · obtain ⟨b, w', rfl⟩ : ∃ b w', w = b :: w' := by
        cases w with
        | nil => simp only [List.length_nil] at hw; omega
        | cons b w' => exact ⟨b, w', rfl⟩
      rw [NDTM.runWith_cons, hstep c b hs]
      exact ih _ (by have := inputPos_stepWith_le N b c; omega)
        (fun u hu => hc (b :: u) (by simp [hu])) w' (by simp at hw; omega)

/-- If `M` simulates `N` through `φ` step by step, and from the image of every halted `N`
configuration `M` halts within `m`, then `M` halts within `n + m` from the image of a
configuration from which `N` halts within `n`: `halts_comp_pos` with `B := inputPos + n`. -/
theorem halts_comp (hstep : ∀ c b, c.state ≠ none → M.stepWith b (φ c) = φ (N.stepWith b c))
    {m : ℕ} (hφ : ∀ c, c.state = none → ∀ w : List Bool, w.length = m →
      (M.runWith w (φ c)).state = none) :
    ∀ (n : ℕ) (c : Cfg K Bool S x), (∀ u : List Bool, u.length = n → (N.runWith u c).state = none) →
      ∀ w : List Bool, w.length = n + m → (M.runWith w (φ c)).state = none :=
  fun n c hc => halts_comp_pos hstep (B := c.inputPos.val + n) (fun c' hc' _ => hφ c' hc') n c
    le_rfl hc

/-- **Probabilities compose.** Under the hypotheses of `halts_comp`, if the probability of `Q`
from the image of a halted configuration `c` depends only on the bit `o c`, then from the
image of `c` it is the average of the two values weighted by the distribution of `o`.

**Proof sketch.** Induction on `n`. If `c` is halted both sides are `g (o c)`: `M`'s extra bits do
not matter (`randProb_runWith_mono`) and `N`'s events are constant (`randProb_const`). Otherwise
condition on the first bit on both sides (`randProb_runWith_choose`, `randProb_succ`) and use the
induction hypothesis at the two stepped configurations. -/
theorem randProb_comp (hstep : ∀ c b, c.state ≠ none → M.stepWith b (φ c) = φ (N.stepWith b c))
    {m : ℕ} (hφ : ∀ c, c.state = none → ∀ w : List Bool, w.length = m →
      (M.runWith w (φ c)).state = none)
    (Q : Cfg K' Bool S' x → Prop) [DecidablePred Q] (o : Cfg K Bool S x → Bool) (g : Bool → ℚ)
    (hg : ∀ c, c.state = none → randProb m (fun w => Q (M.runWith w (φ c))) = g (o c)) :
    ∀ (n : ℕ) (c : Cfg K Bool S x), (∀ u : List Bool, u.length = n → (N.runWith u c).state = none) →
      randProb (n + m) (fun w => Q (M.runWith w (φ c))) =
        randProb n (fun u => o (N.runWith u c) = true) * g true +
          randProb n (fun u => o (N.runWith u c) = false) * g false := by
  intro n
  induction n with
  | zero =>
    intro c hc
    have hs : c.state = none := hc [] rfl
    have hrun : ∀ u, N.runWith u c = c := fun u => NDTM.runWith_of_halt c hs
    rw [zero_add, hg c hs]
    simp only [hrun, randProb_const]
    cases o c <;> simp
  | succ n ih =>
    intro c hc
    by_cases hs : c.state = none
    · have hrun : ∀ u, N.runWith u c = c := fun u => NDTM.runWith_of_halt c hs
      rw [randProb_runWith_mono (hφ c hs) (by omega) Q, hg c hs]
      simp only [hrun, randProb_const]
      cases o c <;> simp
    · have e : n + 1 + m = (n + m) + 1 := by omega
      rw [e, randProb_runWith_choose (Cb := fun b => φ (N.stepWith b c)) (fun b => hstep c b hs)
          (n + m) Q,
        ih _ (fun u hu => hc (true :: u) (by simp [hu])),
        ih _ (fun u hu => hc (false :: u) (by simp [hu])),
        randProb_succ n (fun u => o (N.runWith u c) = true),
        randProb_succ n (fun u => o (N.runWith u c) = false)]
      simp only [NDTM.runWith_cons]
      ring

/-- **Reachable configurations compose.** If `P` holds along every `N`-run from `c` (through
`φ`), and along every `M`-run from the image of every halted `N`-configuration reachable
from `c`, then `P` holds along every `M`-run from `φ c`. -/
theorem reach_comp (hstep : ∀ c b, c.state ≠ none → M.stepWith b (φ c) = φ (N.stepWith b c))
    (P : Cfg K' Bool S' x → Prop) :
    ∀ (w : List Bool) (c : Cfg K Bool S x), (∀ u, P (φ (N.runWith u c))) →
      (∀ u, (N.runWith u c).state = none → ∀ w', P (M.runWith w' (φ (N.runWith u c)))) →
      P (M.runWith w (φ c)) := by
  intro w
  induction w with
  | nil => intro c h1 _; exact h1 []
  | cons b w ih =>
    intro c h1 h2
    by_cases hs : c.state = none
    · exact h2 [] hs (b :: w)
    · rw [NDTM.runWith_cons, hstep c b hs]
      exact ih _ (fun u => h1 (b :: u)) (fun u hu w' => h2 (b :: u) hu w')

end Compose

/-! ## The machine -/

/-- The summary of an output word: `none` for `[]`, `some b` for `[b]`, `some false` for any
longer word. A word is `[true]` iff its summary is `some true`. -/
def summ : List Bool → Option Bool
  | [] => none
  | [b] => some b
  | _ :: _ :: _ => some false

/-- The summary after appending one optional symbol. -/
def push : Option Bool → Option Bool → Option Bool
  | o, none => o
  | none, some b => some b
  | some _, some _ => some false

/-- `push` computes the summary of an extended word. -/
theorem summ_append (u : List Bool) (e : Option Bool) :
    summ (u ++ e.toList) = push (summ u) e := by
  rcases e with _ | b
  · cases h : summ u <;> simp [push, h]
  · match u with
    | [] => rfl
    | [_] => rfl
    | _ :: _ :: _ => rfl

/-- The summary is `some true` exactly on `[true]`. -/
theorem summ_eq_some_true (u : List Bool) : summ u = some true ↔ u = [true] := by
  match u with
  | [] => simp [summ]
  | [b] => cases b <;> simp [summ]
  | _ :: _ :: _ => simp [summ]

/-- Control states of `amp N r dec`: simulating run `j` of `N` in state `q` with output
summary `o`; rewinding the input head after run `j`; seeking the left end before run `j`.
Each carries the number `c` of accepting runs so far. -/
inductive Phase (S : Type) (r : ℕ) where
  /-- simulating run `j` of `N` in state `q` -/
  | run (j : Fin (r + 1)) (q : S) (o : Option Bool) (c : Fin (r + 2))
  /-- run `j` has halted -/
  | rewind (j : Fin (r + 1)) (c : Fin (r + 2))
  /-- moving the input head to the left end before run `j` -/
  | seek (j : Fin (r + 1)) (c : Fin (r + 2))
  deriving DecidableEq, Fintype

/-- Increase a count by one if `b` holds (capped at `r + 1`). -/
def bump {r : ℕ} (c : Fin (r + 2)) (b : Bool) : Fin (r + 2) :=
  if b then ⟨min (c.val + 1) (r + 1), by omega⟩ else c

/-- The block (run) a work tape of `amp N r dec` belongs to. -/
def blk {r k : ℕ} (t : Fin ((r + 1) * k)) : Fin (r + 1) := (finProdFinEquiv.symm t).1

/-- The tape of `N` a work tape of `amp N r dec` stands for. -/
def idx {r k : ℕ} (t : Fin ((r + 1) * k)) : Fin k := (finProdFinEquiv.symm t).2

/-- Splitting a tape index of `amp N r dec` into block and index. -/
@[simp]
theorem blk_mk {r k : ℕ} (j : Fin (r + 1)) (i : Fin k) : blk (finProdFinEquiv (j, i)) = j := by
  simp [blk]

/-- Splitting a tape index of `amp N r dec` into block and index. -/
@[simp]
theorem idx_mk {r k : ℕ} (j : Fin (r + 1)) (i : Fin k) : idx (finProdFinEquiv (j, i)) = i := by
  simp [idx]

/-- An action that only moves the input head, emits `out` and enters `st`. -/
def idle {k : ℕ} {St : Type} (inp : SignType) (out : Option Bool) (st : Option St) :
    Action k Bool St :=
  ⟨inp, fun _ => (none, 0), out, st⟩

/-- The transitions of `amp N r dec`. -/
def tr (N : FinNDTM Bool) (r : ℕ) (dec : ℕ → Bool) (b : Bool) :
    Phase N.State r → Option Bool → (Fin ((r + 1) * N.k) → Option Bool) →
      Action ((r + 1) * N.k) Bool (Phase N.State r)
  | .run j q o c, a, ws =>
    let act := N.tm.tr b q a fun i => ws (finProdFinEquiv (j, i))
    { inputTape := act.inputTape
      workTapes := fun t => if blk t = j then act.workTapes (idx t) else (none, 0)
      output := none
      state := some <| match act.state with
        | some q' => .run j q' (push o act.output) c
        | none => .rewind j (bump c (decide (push o act.output = some true))) }
  | .rewind j c, _, _ =>
    if h : j.val < r then idle (-1) none (some (.seek ⟨j.val + 1, by omega⟩ c))
    else idle 0 (some (dec c.val)) none
  | .seek j c, none, _ => idle 1 none (some (.run j N.tm.q₀ none c))
  | .seek j c, some _, _ => idle (-1) none (some (.seek j c))

/-- **The repeated machine**: `r + 1` runs of `N` on fresh blocks of work tapes, rewinding
the input head between runs, then output `dec` of the number of accepting runs.
[AB09, §7.7, p. 139] (error reduction in logarithmic space) -/
def amp (N : FinNDTM Bool) (r : ℕ) (dec : ℕ → Bool) : FinNDTM Bool :=
  ⟨(r + 1) * N.k, Phase N.State r, ⟨.run 0 N.tm.q₀ none 0, tr N r dec⟩⟩

variable {N : FinNDTM Bool} {r : ℕ} {dec : ℕ → Bool} {x : List Bool}

/-- Configurations of `amp N r dec` on `x`. -/
abbrev ACfg (N : FinNDTM Bool) (r : ℕ) (x : List Bool) :=
  Cfg ((r + 1) * N.k) Bool (Phase N.State r) x

/-- The configuration of `amp N r dec` simulating run `j` (count `c`) of `N` at `u`; tapes
outside block `j` are those of `D`. -/
def emb (D : ACfg N r x) (j : Fin (r + 1)) (c : Fin (r + 2)) (u : Cfg N.k Bool N.State x) :
    ACfg N r x where
  state := some <| match u.state with
    | some q => .run j q (summ u.output) c
    | none => .rewind j (bump c (decide (summ u.output = some true)))
  inputPos := u.inputPos
  workTapes t := if blk t = j then u.workTapes (idx t) else D.workTapes t
  workTapePos t := if blk t = j then u.workTapePos (idx t) else D.workTapePos t
  output := []

/-- One step of the simulation is one step of `N`.

**Proof sketch.** Both sides apply the action of `N.tm.tr b q` read from the same input symbol and,
through `blk_mk`/`idx_mk`, the same work symbols. Compare fields: block `j` is written and moved
exactly as `N`'s tapes, other blocks are untouched, the output stays empty and the summary follows
`summ_append`. -/
theorem step_emb (D : ACfg N r x) (j : Fin (r + 1)) (c : Fin (r + 2))
    (u : Cfg N.k Bool N.State x) (b : Bool) (hu : u.state ≠ none) :
    (amp N r dec).tm.stepWith b (emb D j c u) = emb D j c (N.tm.stepWith b u) := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hu
  have hws : (fun i => (emb D j c u).workTapeSymbols (finProdFinEquiv (j, i))) =
      u.workTapeSymbols := by
    funext i
    simp only [Cfg.workTapeSymbols, emb, blk_mk, idx_mk, if_true]
  have hin : (emb D j c u).inputSymbol = u.inputSymbol := rfl
  have hst : (emb D j c u).state = some (.run j q (summ u.output) c) := by simp [emb, hq]
  have lhs : (amp N r dec).tm.stepWith b (emb D j c u) =
      (tr N r dec b (.run j q (summ u.output) c) (emb D j c u).inputSymbol
        (emb D j c u).workTapeSymbols).apply (emb D j c u) := by
    unfold NDTM.stepWith
    rw [hst]
    rfl
  have rhs : N.tm.stepWith b u = (N.tm.tr b q u.inputSymbol u.workTapeSymbols).apply u := by
    unfold NDTM.stepWith
    rw [hq]
  rw [lhs, rhs]
  simp only [tr, hin, hws]
  refine Cfg.ext ?_ rfl ?_ ?_ ?_
  · simp only [Action.apply, emb, summ_append]
  · funext t
    by_cases h : blk t = j <;> simp [Action.apply, emb, h]
  · funext t
    by_cases h : blk t = j <;> simp [Action.apply, emb, h]
  · simp [Action.apply, emb]

/-- Blocks after `j` are blank, with heads at the origin. -/
def Fresh (D : ACfg N r x) (j : ℕ) : Prop :=
  ∀ t, j < (blk t).val → D.workTapes t = (fun _ => none) ∧ D.workTapePos t = 0

/-- `C` rewinds after run `j` with count `c`, has emitted nothing, and blocks after `j` are
fresh. -/
def RewindAt (C : ACfg N r x) (j : Fin (r + 1)) (c : Fin (r + 2)) : Prop :=
  C.state = some (.rewind j c) ∧ C.output = [] ∧ Fresh C j.val

/-- A halted simulated run is a rewinding configuration. -/
theorem rewindAt_emb {D : ACfg N r x} {j : Fin (r + 1)} (c : Fin (r + 2))
    {u : Cfg N.k Bool N.State x} (hu : u.state = none) (hD : Fresh D j.val) :
    RewindAt (emb D j c u) j (bump c (decide (summ u.output = some true))) := by
  refine ⟨by simp [emb, hu], rfl, fun t ht => ?_⟩
  have hne : blk t ≠ j := fun h => by rw [h] at ht; omega
  simp only [emb, if_neg hne]
  exact hD t ht

/-- The configuration starting run `j` after rewinding `C`. -/
def restart (C : ACfg N r x) (j : Fin (r + 1)) (c : Fin (r + 2)) : ACfg N r x :=
  { C with state := some (.run j N.tm.q₀ none c), inputPos := 1 }

/-- Restarting on a fresh block is starting a simulation of `N` from its initial
configuration. -/
theorem restart_eq_emb (C : ACfg N r x) (j : Fin (r + 1)) (c : Fin (r + 2))
    (hF : ∀ t, blk t = j → C.workTapes t = (fun _ => none) ∧ C.workTapePos t = 0)
    (hout : C.output = []) :
    restart C j c = emb (restart C j c) j c (N.tm.initCfg x) := by
  refine Cfg.ext (by simp [restart, emb, summ]) rfl ?_ ?_ (by simp [restart, emb, hout])
  · funext t
    by_cases h : blk t = j
    · simp only [emb, if_pos h, restart, (hF t h).1]
      rfl
    · simp [emb, h, restart]
  · funext t
    by_cases h : blk t = j
    · simp only [emb, if_pos h, restart, (hF t h).2]
      rfl
    · simp [emb, h, restart]

/-- The initial configuration of `amp N r dec` simulates run `0` from the start. -/
theorem init_eq_emb :
    (amp N r dec).tm.initCfg x = emb ((amp N r dec).tm.initCfg x) 0 0 (N.tm.initCfg x) := by
  refine Cfg.ext (by simp [emb, summ, amp]) rfl ?_ ?_ rfl
  · funext t
    simp only [emb]
    split_ifs <;> rfl
  · funext t
    simp only [emb]
    split_ifs <;> rfl

/-! ### Rewinding -/

/-- An idle action changes only the state, the input head and the output. -/
theorem idle_apply {inp : SignType} {out : Option Bool} {st : Option (Phase N.State r)}
    (C : ACfg N r x) :
    (idle inp out st : Action ((r + 1) * N.k) Bool (Phase N.State r)).apply C =
      { C with
        state := st
        inputPos := moveInputPos C.inputPos inp
        output := C.output ++ out.toList } := by
  refine Cfg.ext rfl rfl rfl ?_ rfl
  funext t
  simp [idle]

/-- One step of `amp` from a configuration in state `some p` applies `tr` at `p`. -/
theorem step_of_state {C : ACfg N r x} {p : Phase N.State r} (h : C.state = some p) (b : Bool) :
    (amp N r dec).tm.stepWith b C =
      (tr N r dec b p C.inputSymbol C.workTapeSymbols).apply C := by
  unfold NDTM.stepWith
  rw [h]
  rfl

/-- Moving left from any position lands within the input. -/
theorem moveInputPos_neg_one_le {n : ℕ} (p : Fin (n + 2)) : (moveInputPos p (-1)).val ≤ n := by
  have := p.isLt
  by_cases h : p = 0
  · rw [h, moveInputPos_leftBoundary]
    simp
  · rw [← SignType.neg_eq_neg_one, moveInputPos_neg_of_ne_left p h]
    simp only
    omega

/-- From the left end, seeking enters run `j` at the first input cell. -/
theorem step_seek_zero {C : ACfg N r x} {j : Fin (r + 1)} {c : Fin (r + 2)}
    (hC : C.state = some (.seek j c)) (h0 : C.inputPos = 0) (b : Bool) :
    (amp N r dec).tm.stepWith b C = restart C j c := by
  have hsym : C.inputSymbol = none := by simp [Cfg.inputSymbol, h0]
  rw [step_of_state hC, hsym]
  simp only [tr]
  rw [idle_apply]
  refine Cfg.ext rfl ?_ rfl rfl (by simp [restart])
  ext
  simp [restart, moveInputPos, h0]

/-- Inside the input, seeking moves one cell left. -/
theorem step_seek_pos {C : ACfg N r x} {j : Fin (r + 1)} {c : Fin (r + 2)}
    (hC : C.state = some (.seek j c)) (h0 : C.inputPos.val ≠ 0) (hle : C.inputPos.val ≤ x.length)
    (b : Bool) :
    (amp N r dec).tm.stepWith b C = { C with inputPos := ⟨C.inputPos.val - 1, by omega⟩ } := by
  obtain ⟨a, ha⟩ : ∃ a, C.inputSymbol = some a := by
    refine Option.ne_none_iff_exists'.mp ?_
    have h1 : C.inputPos ≠ 0 := fun h => h0 (by rw [h]; rfl)
    have h2 : (C.inputPos : ℕ) ≠ x.length + 1 := by omega
    simp [Cfg.inputSymbol, h1, h2]
  rw [step_of_state hC, ha]
  simp only [tr]
  rw [idle_apply]
  have h1 : C.inputPos ≠ 0 := fun h => h0 (by rw [h]; rfl)
  refine Cfg.ext (by rw [hC]) ?_ rfl rfl (by simp)
  rw [← SignType.neg_eq_neg_one, moveInputPos_neg_of_ne_left _ h1]

/-- **Seeking** from input position `p` keeps the work tapes for `p + 1` steps and then
restarts.

**Proof sketch.** Induction on `p`. At position `0` the input symbol is blank and one step restarts
(`step_seek_zero`); otherwise one step moves left (`step_seek_pos`) without touching the work tapes,
and the induction hypothesis applies. -/
theorem seek_run {j : Fin (r + 1)} {c : Fin (r + 2)} :
    ∀ (p : ℕ) (C : ACfg N r x), C.state = some (.seek j c) → C.inputPos.val = p →
      p ≤ x.length →
      (∀ u : List Bool, u.length ≤ p + 1 →
        ((amp N r dec).tm.runWith u C).workTapePos = C.workTapePos) ∧
      ∀ u : List Bool, u.length = p + 1 → (amp N r dec).tm.runWith u C = restart C j c := by
  intro p
  induction p with
  | zero =>
    intro C hC hp _
    have h0 : C.inputPos = 0 := Fin.ext hp
    refine ⟨fun u hu => ?_, fun u hu => ?_⟩
    · match u, hu with
      | [], _ => rfl
      | [b], _ => rw [NDTM.runWith_cons, step_seek_zero hC h0]; rfl
    · match u, hu with
      | [b], _ => rw [NDTM.runWith_cons, step_seek_zero hC h0]; rfl
  | succ p ih =>
    intro C hC hp hle
    have hstep := fun b => step_seek_pos (dec := dec) hC (by omega) (by omega) b
    obtain ⟨ih1, ih2⟩ := ih { C with inputPos := ⟨C.inputPos.val - 1, by omega⟩ } hC
      (by simp; omega) (by omega)
    refine ⟨fun u hu => ?_, fun u hu => ?_⟩
    · match u, hu with
      | [], _ => rfl
      | b :: u', hu => rw [NDTM.runWith_cons, hstep]; exact ih1 u' (by simp at hu; omega)
    · match u, hu with
      | b :: u', hu => rw [NDTM.runWith_cons, hstep]; exact ih2 u' (by simp at hu; omega)

/-- **Rewinding** after a run that is not the last, with the step count explicit: for
`p = (moveInputPos C.inputPos (-1)).val`, within `p + 2` steps the work tapes are kept and run
`j + 1` restarts.

**Proof sketch.** The first step moves the input head left (to `p ≤ |x|`,
`moveInputPos_neg_one_le`) and enters the seek phase; then apply `seek_run`. -/
theorem rewind_run_pos {C : ACfg N r x} {j : Fin (r + 1)} {c : Fin (r + 2)}
    (hC : C.state = some (.rewind j c)) (hj : j.val < r) :
    (∀ u : List Bool, u.length ≤ (moveInputPos C.inputPos (-1)).val + 2 →
        ((amp N r dec).tm.runWith u C).workTapePos = C.workTapePos) ∧
      ∀ u : List Bool, u.length = (moveInputPos C.inputPos (-1)).val + 2 →
        (amp N r dec).tm.runWith u C = restart C ⟨j.val + 1, by omega⟩ c := by
  have hstep : ∀ b, (amp N r dec).tm.stepWith b C =
      { C with
        state := some (.seek ⟨j.val + 1, by omega⟩ c)
        inputPos := moveInputPos C.inputPos (-1) } := fun b => by
    rw [step_of_state hC]
    simp only [tr, dif_pos hj]
    rw [idle_apply]
    simp
  obtain ⟨h1, h2⟩ := seek_run (dec := dec) (moveInputPos C.inputPos (-1)).val
    { C with
      state := some (.seek ⟨j.val + 1, by omega⟩ c)
      inputPos := moveInputPos C.inputPos (-1) } rfl rfl (moveInputPos_neg_one_le _)
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · match u, hu with
    | [], _ => rfl
    | b :: u', hu => rw [NDTM.runWith_cons, hstep]; exact h1 u' (by simp at hu; omega)
  · match u, hu with
    | b :: u', hu => rw [NDTM.runWith_cons, hstep]; exact h2 u' (by simp at hu; omega)

/-- **Rewinding** after a run that is not the last: within `p + 2` steps (`p ≤ |x|`) the
work tapes are kept and run `j + 1` restarts (`rewind_run_pos`). -/
theorem rewind_run {C : ACfg N r x} {j : Fin (r + 1)} {c : Fin (r + 2)}
    (hC : C.state = some (.rewind j c)) (hj : j.val < r) :
    ∃ p ≤ x.length,
      (∀ u : List Bool, u.length ≤ p + 2 →
        ((amp N r dec).tm.runWith u C).workTapePos = C.workTapePos) ∧
      ∀ u : List Bool, u.length = p + 2 →
        (amp N r dec).tm.runWith u C = restart C ⟨j.val + 1, by omega⟩ c :=
  ⟨_, moveInputPos_neg_one_le C.inputPos, rewind_run_pos hC hj⟩

/-- The halted configuration after the last run: the decision is emitted. -/
def finish (dec : ℕ → Bool) (C : ACfg N r x) (c : Fin (r + 2)) : ACfg N r x :=
  { C with
    state := none
    output := C.output ++ [dec c.val] }

/-- After the last run, rewinding emits the decision and halts. -/
theorem rewind_last {C : ACfg N r x} {j : Fin (r + 1)} {c : Fin (r + 2)}
    (hC : C.state = some (.rewind j c)) (hj : ¬ j.val < r) (w : List Bool) :
    (amp N r dec).tm.runWith (true :: w) C = finish dec C c ∧
    (amp N r dec).tm.runWith (false :: w) C = finish dec C c := by
  have hstep : ∀ b, (amp N r dec).tm.stepWith b C = finish dec C c := fun b => by
    rw [step_of_state hC]
    simp only [tr, dif_neg hj]
    rw [idle_apply, moveInputPos_zero]
    rfl
  exact ⟨by rw [NDTM.runWith_cons, hstep, NDTM.runWith_of_halt _ rfl],
    by rw [NDTM.runWith_cons, hstep, NDTM.runWith_of_halt _ rfl]⟩

end Randomized.Amplify
