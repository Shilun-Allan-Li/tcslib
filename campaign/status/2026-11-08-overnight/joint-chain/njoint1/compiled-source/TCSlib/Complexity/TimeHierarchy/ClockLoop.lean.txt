/-
Copyright (c) 2026 Hydroxyi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.TimeHierarchy.ClockMachine

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The clocked runner: the loop and its specification

The loop phase of `Complexity.TimeHierarchy.clockTM` (see
`TCSlib.Complexity.TimeHierarchy.ClockMachine` for the machine), and the runner's
specification: on input `x`, with budget word `s = K(x)`, the runner halts within
`t_K + 4|s| + |x| + 4·val(s) + 6` steps and outputs `[b]` with `b = true` exactly when
`W` does **not** halt on `x` with completed output `[true]` within `val(s)` steps.
[AB09, Theorem 3.1, proof: "`D` runs `M_x` for `g(|x|)` steps".]

## Design

* **Amortized decrement cost.** One loop iteration on the counter word
  `0^j 1 r` costs `2j + 2` steps (the borrow sweep over `j` zeros, the fused
  simulation step, and the return sweep) and produces `1^j 0 r`. With the potential
  `B(s) = 4·val(s) + 2·(|s| - pop(s)) + |s| + 1` this cost is exactly
  `B(s) - B(s')`, so the whole loop costs at most `B(s) ≤ 4·val(s) + 3|s| + 1`: a
  budget of `v` simulated steps costs `O(v + log v)` runner steps, matching the
  book's "`D` runs in time `O(g(n))`" up to the constant.

## Main results

* `Complexity.TimeHierarchy.clockTM_loop` — the loop invariant (strong induction on
  the counter value).
* `Complexity.TimeHierarchy.clockTM_spec` — the clocked runner's specification.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.1, Theorem 3.1 and its proof, p. 69.)
-/

namespace Complexity.TimeHierarchy

open Turing Turing.FinTM

/-- Overwriting the cell at index `|l|` of a stored word replaces that letter. -/
lemma bufferTape_update_mid (l m : List Bool) (a b : Bool) :
    Function.update (bufferTape (l ++ a :: m)) (l.length : ℤ) (some b) =
      bufferTape (l ++ b :: m) := by
  funext z
  by_cases hz : z = l.length
  · subst hz
    simp [bufferTape]
  · rw [Function.update_of_ne hz]
    simp only [bufferTape]
    split_ifs with h0
    · have hne : z.toNat ≠ l.length := by omega
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · rw [List.getElem?_append_left hlt, List.getElem?_append_left hlt]
      · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
        obtain ⟨d, hd⟩ : ∃ d, z.toNat - l.length = d + 1 := ⟨z.toNat - l.length - 1, by omega⟩
        rw [hd]
        simp
    · rfl

variable (K W : FinTM Bool)

/-- The borrow sweep over `j` zero bits: each is overwritten with a one, the head
advancing; exactly `j` steps.

**Proof sketch.** Induction on `j`, generalizing the head position `i`. In the
successor case the head reads the `false` at cell `i`; one step of the decrement
state overwrites it with `true` and moves right, which turns the buffer
`1^i 0^(j+1) rest` into `1^(i+1) 0^j rest` with the head at `i + 1`. The induction
hypothesis at `i + 1` finishes the remaining `j` steps, and `i + 1 + j = i + (j + 1)`. -/
lemma borrow_run {x : List Bool} (c : Cfg W.k Bool W.State x) (q : W.State) (r : OutReg)
    (kt : Fin K.k → ℤ → Option Bool) (kh : Fin K.k → ℤ) (rest : List Bool) :
    ∀ j i, (clockTM K W).tm.runFrom
      (ctrCfg K W (some (.dec q r)) c
        (bufferTape (List.replicate i true ++ List.replicate j false ++ rest)) i kt kh []) j =
      ctrCfg K W (some (.dec q r)) c
        (bufferTape (List.replicate (i + j) true ++ rest)) (i + j) kt kh [] := by
  intro j
  induction j with
  | zero => intro i; simp
  | succ j ih =>
    intro i
    have hread : bufferTape (List.replicate i true ++ List.replicate (j + 1) false ++ rest)
        (i : ℤ) = some false := by
      rw [bufferTape_nat]
      simp [List.replicate_succ]
    have hstep : (clockTM K W).tm.step (ctrCfg K W (some (.dec q r)) c
        (bufferTape (List.replicate i true ++ List.replicate (j + 1) false ++ rest)) i kt kh []) =
        ctrCfg K W (some (.dec q r)) c
          (bufferTape (List.replicate (i + 1) true ++ List.replicate j false ++ rest))
          ((i + 1 : ℕ) : ℤ) kt kh [] := by
      rw [clockTM_step_some K W _ (.dec q r) rfl]
      simp only [clockTr, ctrCfg_ctr, hread]
      rw [ctrAction_apply]
      have hl : List.replicate i true ++ List.replicate (j + 1) false ++ rest =
          List.replicate i true ++ false :: (List.replicate j false ++ rest) := by
        simp [List.replicate_succ]
      have hl' : List.replicate (i + 1) true ++ List.replicate j false ++ rest =
          List.replicate i true ++ true :: (List.replicate j false ++ rest) := by
        simp [List.replicate_succ', List.append_assoc]
      have hu := bufferTape_update_mid (List.replicate i true)
        (List.replicate j false ++ rest) false true
      simp only [List.length_replicate] at hu
      simp only [hl, hl', hu]
      congr 1
    rw [MultiTapeTM.runFrom_succ_eq_step, hstep, ih (i + 1)]
    rw [show i + 1 + j = i + (j + 1) by omega]
    congr 1
    push_cast
    ring

/-- The return sweep: from cell `j - 1` over `j` stored cells to the left blank at
cell `-1` and back to cell `0`; exactly `j + 1` steps, ending in the decrement state.

**Proof sketch.** Induction on `j`. For `j = 0` the head sits at cell `-1`, which is
blank, so a single step of the return state turns around to cell `0` and enters the
decrement state. For `j + 1` the head at cell `j` reads a stored (non-blank) cell,
so one step moves left to cell `j - 1` staying in the return state; the induction
hypothesis (whose non-blank hypothesis is inherited) supplies the remaining
`j + 1` steps. -/
lemma ret_run {x : List Bool} (c : Cfg W.k Bool W.State x) (q : W.State) (r : OutReg)
    (kt : Fin K.k → ℤ → Option Bool) (kh : Fin K.k → ℤ) (τ : ℤ → Option Bool)
    (hneg : τ (-1) = none) : ∀ j, (∀ i : ℕ, i < j → τ i ≠ none) →
    (clockTM K W).tm.runFrom (ctrCfg K W (some (.ret q r)) c τ ((j : ℤ) - 1) kt kh []) (j + 1) =
      ctrCfg K W (some (.dec q r)) c τ 0 kt kh [] := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero,
      clockTM_step_some K W _ (.ret q r) rfl]
    simp only [clockTr, ctrCfg_ctr, Nat.cast_zero, zero_sub, hneg, if_true]
    rw [ctrAction_apply]
    simp
  | succ j ih =>
    intro hj
    have hread : τ (((j + 1 : ℕ) : ℤ) - 1) ≠ none := by
      rw [show (((j + 1 : ℕ) : ℤ) - 1) = (j : ℤ) by omega]
      exact hj j (by omega)
    have hstep : (clockTM K W).tm.step
        (ctrCfg K W (some (.ret q r)) c τ (((j + 1 : ℕ) : ℤ) - 1) kt kh []) =
        ctrCfg K W (some (.ret q r)) c τ ((j : ℤ) - 1) kt kh [] := by
      rw [clockTM_step_some K W _ (.ret q r) rfl]
      simp only [clockTr, ctrCfg_ctr, hread, if_false]
      rw [ctrAction_apply]
      congr 1
      push_cast
      simp [SignType.neg_eq_neg_one]
      ring
    rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
    exact ih (fun i hi => hj i (by omega))

/-- The fused simulation step: on reading the low `true` bit, the runner writes `false`,
moves the counter head left, applies `W`'s transition `a` to the right block and the
input head, and either continues in the return state (with the register updated by
`a`'s emission) or — if `a` halts `W` — halts, emitting whether the final summary
differs from `one true`.

**Proof sketch.** Since `W` is in the live state `q`, its step is the application of
its transition action `a` to `c`. Unfolding one step of the clock machine in the
decrement state on a `true` bit, the transition is the fused action; after
generalizing `a`, the two configurations are compared componentwise: the state and
output agree by construction, and the tape contents and head positions agree on
each block of tapes (input, counter, `K`'s tapes, `W`'s tapes) by unfolding the
action application, splitting on whether `a` halts. -/
lemma wstep {x : List Bool} (c : Cfg W.k Bool W.State x) (q : W.State) (r : OutReg)
    (hq : c.state = some q) (kt : Fin K.k → ℤ → Option Bool) (kh : Fin K.k → ℤ)
    (τ : ℤ → Option Bool) (z : ℤ) (hτ : τ z = some true) :
    (clockTM K W).tm.step (ctrCfg K W (some (.dec q r)) c τ z kt kh []) =
      ctrCfg K W ((W.tm.tr q c.inputSymbol c.workTapeSymbols).state.map
          (fun q' => .ret q' (r.push (W.tm.tr q c.inputSymbol c.workTapeSymbols).output)))
        (W.tm.step c) (Function.update τ z (some false)) (z - 1) kt kh
        (if (W.tm.tr q c.inputSymbol c.workTapeSymbols).state = none then
          [decide (r.push (W.tm.tr q c.inputSymbol c.workTapeSymbols).output ≠ .one true)]
        else []) := by
  have hW : W.tm.step c = (W.tm.tr q c.inputSymbol c.workTapeSymbols).apply c := by
    unfold MultiTapeTM.step; rw [hq]
  rw [clockTM_step_some K W _ (.dec q r) rfl, hW]
  simp only [clockTr, ctrCfg_ctr, hτ, ctrCfg_right]
  have hi : (ctrCfg K W (some (.dec q r)) c τ z kt kh []).inputSymbol = c.inputSymbol := rfl
  rw [hi]
  generalize W.tm.tr q c.inputSymbol c.workTapeSymbols = a
  refine Cfg.ext rfl rfl ?_ ?_ ?_
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [ctrCfg, Action.apply]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [ctrCfg, Action.apply]
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [ctrCfg, Action.apply]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;>
        simp [ctrCfg, Action.apply, SignType.neg_eq_neg_one, sub_eq_add_neg]
  · cases h : a.state <;> simp [ctrCfg, Action.apply, h]

/-- Underflow: reading a blank in the decrement state emits `true` and halts. -/
lemma underflow_step {x : List Bool} (c : Cfg W.k Bool W.State x) (q : W.State) (r : OutReg)
    (kt : Fin K.k → ℤ → Option Bool) (kh : Fin K.k → ℤ)
    (τ : ℤ → Option Bool) (z : ℤ) (hτ : τ z = none) :
    ((clockTM K W).tm.step (ctrCfg K W (some (.dec q r)) c τ z kt kh [])).state = none ∧
      ((clockTM K W).tm.step (ctrCfg K W (some (.dec q r)) c τ z kt kh [])).output = [true] := by
  rw [clockTM_step_some K W _ (.dec q r) rfl]
  simp only [clockTr, ctrCfg_ctr, hτ]
  simp [ctrCfg, Action.apply]

/-- The amortization potential of a counter word. -/
def ctrBound (s : List Bool) : ℕ := 4 * ctrVal s + 2 * (s.length - ctrPop s) + s.length + 1

/-- The answer of the loop started from `W`-configuration `c` with budget `v`:
`true` unless `W`, run `v` steps from `c`, has halted with output `[true]`. -/
def loopAnswer {x : List Bool} (c : Cfg W.k Bool W.State x) (v : ℕ) : Bool :=
  !(decide ((W.tm.runFrom c v).state = none ∧ (W.tm.runFrom c v).output = [true]))

/-- **The loop invariant.** From the loop entry with live simulated configuration `c`
(register = summary of `c`'s output) and counter word `s` (head on cell `0`), the runner
halts within `ctrBound s` steps with output `[loopAnswer c (val s)]`.

**Proof sketch.** Strong induction on `val s`. At value zero, `s` is all zeros: the
borrow sweep runs off the word in `|s|` steps and the runner emits `true` (the
simulated machine is live, so the answer is `true`). At positive value write
`s = 0^j 1 r`: sweep `j` zeros (`borrow_run`), then fuse one simulation step
(`wstep`). If that step halts `W`, the runner emits the correct answer at once (the
run from `c` for `val s` steps is absorbed at the halting configuration). Otherwise
return to cell `0` in `j + 1` steps (`ret_run`) with counter `1^j 0 r` of value
`val s - 1` and apply the induction hypothesis; the costs `2j + 2` are absorbed by
the potential drop `ctrBound s - ctrBound s' = 2j + 2`. -/
theorem clockTM_loop {x : List Bool} (kt : Fin K.k → ℤ → Option Bool) (kh : Fin K.k → ℤ)
    (s : List Bool) (c : Cfg W.k Bool W.State x) (q : W.State) (hq : c.state = some q) :
    ∃ t ≤ ctrBound s,
      ((clockTM K W).tm.runFrom
        (ctrCfg K W (some (.dec q (OutReg.ofList c.output))) c (bufferTape s) 0 kt kh []) t).state
          = none ∧
      ((clockTM K W).tm.runFrom
        (ctrCfg K W (some (.dec q (OutReg.ofList c.output))) c (bufferTape s) 0 kt kh []) t).output
          = [loopAnswer W c (ctrVal s)] := by
  obtain ⟨n, hn⟩ : ∃ n, ctrVal s = n := ⟨_, rfl⟩
  induction n generalizing s c q with
  | zero =>
    have hs := ctrVal_zero_eq s hn
    have hb := borrow_run K W c q (OutReg.ofList c.output) kt kh [] s.length 0
    simp only [List.replicate_zero, List.nil_append, List.append_nil, zero_add, Nat.cast_zero] at hb
    rw [← hs] at hb
    have hτ : bufferTape (List.replicate s.length true) (s.length : ℤ) = none := by
      rw [bufferTape_nat]; simp
    obtain ⟨h1, h2⟩ := underflow_step K W c q (OutReg.ofList c.output) kt kh _ _ hτ
    refine ⟨s.length + 1, by unfold ctrBound; omega, ?_, ?_⟩
    · rw [MultiTapeTM.runFrom_succ_eq_step', hb]; exact h1
    · rw [MultiTapeTM.runFrom_succ_eq_step', hb, h2, hn]
      simp [loopAnswer, hq]
  | succ n ih =>
    obtain ⟨j, rest, rfl⟩ := ctrVal_pos_decomp s (by omega)
    have hb := borrow_run K W c q (OutReg.ofList c.output) kt kh (true :: rest) j 0
    simp only [List.replicate_zero, List.nil_append, zero_add, Nat.cast_zero] at hb
    have hτ : bufferTape (List.replicate j true ++ true :: rest) (j : ℤ) = some true := by
      rw [bufferTape_nat]; simp
    have hw := wstep K W c q (OutReg.ofList c.output) hq kt kh _ _ hτ
    have hu := bufferTape_update_mid (List.replicate j true) rest true false
    simp only [List.length_replicate] at hu
    rw [hu] at hw
    have hreg : (OutReg.ofList c.output).push (W.tm.tr q c.inputSymbol c.workTapeSymbols).output =
        OutReg.ofList (W.tm.step c).output := by
      have hW : W.tm.step c = (W.tm.tr q c.inputSymbol c.workTapeSymbols).apply c := by
        unfold MultiTapeTM.step; rw [hq]
      rw [hW, ← OutReg.ofList_push]
      rfl
    have hstate : (W.tm.step c).state = (W.tm.tr q c.inputSymbol c.workTapeSymbols).state := by
      unfold MultiTapeTM.step; rw [hq]; rfl
    have hans : loopAnswer W c (n + 1) = loopAnswer W (W.tm.step c) n := by
      simp only [loopAnswer, MultiTapeTM.runFrom_succ_eq_step]
    have hlen : ctrPop rest ≤ rest.length := ctrPop_le_length rest
    have hpop1 := ctrPop_replicate j false (true :: rest)
    have hpop2 := ctrPop_replicate j true (false :: rest)
    simp only [ctrPop, if_true, Bool.false_eq_true, if_false] at hpop1 hpop2
    have hval := ctrVal_borrow j rest
    cases ha : (W.tm.tr q c.inputSymbol c.workTapeSymbols).state with
    | none =>
      -- the simulated machine halts on this step
      rw [ha] at hw
      simp only [Option.map_none, if_true] at hw
      refine ⟨j + 1, ?_, ?_, ?_⟩
      · unfold ctrBound; simp only [List.length_append, List.length_replicate,
          List.length_cons]; omega
      · rw [MultiTapeTM.runFrom_succ_eq_step', hb, hw]; rfl
      · rw [MultiTapeTM.runFrom_succ_eq_step', hb, hw]
        change [decide (_ ≠ _)] = _
        rw [hn, hans, hreg]
        have hh : (W.tm.step c).state = none := by rw [hstate, ha]
        simp only [loopAnswer, MultiTapeTM.runFrom_of_halt _ hh, hh, true_and]
        simp [OutReg.ofList_eq_one_true]
    | some q' =>
      rw [ha] at hw
      simp only [Option.map_some, reduceCtorEq, if_false] at hw
      rw [hreg] at hw
      have hr := ret_run K W (W.tm.step c) q' (OutReg.ofList (W.tm.step c).output) kt kh
        (bufferTape (List.replicate j true ++ false :: rest)) (bufferTape_left _) j
        (fun i hi => by
          rw [bufferTape_nat]
          rw [List.getElem?_append_left (by simpa using hi)]
          simp [hi])
      have hlive : (W.tm.step c).state = some q' := by rw [hstate, ha]
      obtain ⟨t', ht', h1, h2⟩ := ih (List.replicate j true ++ false :: rest) (W.tm.step c) q'
        hlive (by omega)
      have hrun : (clockTM K W).tm.runFrom
          (ctrCfg K W (some (.dec q (OutReg.ofList c.output))) c
            (bufferTape (List.replicate j false ++ true :: rest)) 0 kt kh [])
          (j + 1 + (j + 1)) =
          ctrCfg K W (some (.dec q' (OutReg.ofList (W.tm.step c).output))) (W.tm.step c)
            (bufferTape (List.replicate j true ++ false :: rest)) 0 kt kh [] := by
        have h1step : (clockTM K W).tm.runFrom
            (ctrCfg K W (some (.dec q (OutReg.ofList c.output))) c
              (bufferTape (List.replicate j false ++ true :: rest)) 0 kt kh []) (j + 1) =
            ctrCfg K W (some (.ret q' (OutReg.ofList (W.tm.step c).output))) (W.tm.step c)
              (bufferTape (List.replicate j true ++ false :: rest)) ((j : ℤ) - 1) kt kh [] := by
          rw [MultiTapeTM.runFrom_succ_eq_step', hb, hw]
        rw [MultiTapeTM.runFrom_add, h1step]
        exact hr
      refine ⟨j + 1 + (j + 1) + t', ?_, ?_, ?_⟩
      · unfold ctrBound at ht' ⊢
        simp only [List.length_append, List.length_replicate, List.length_cons] at ht' ⊢
        omega
      · rw [MultiTapeTM.runFrom_add, hrun]; exact h1
      · rw [MultiTapeTM.runFrom_add, hrun, h2, hn, hans]
        congr 2
        omega

open Classical in
/-- **Specification of the clocked runner** [AB09, Theorem 3.1, proof]. If the budget
machine `K` halts on `x` with output `s` within `tK` steps, then `clockTM K W` halts on
`x` within `tK + 4|s| + |x| + 4·val(s) + 6` steps with output `[b]`, where `b = true`
iff `W` does **not** compute `[true]` on `x` within `val(s)` steps.

**Proof sketch.** `clockTM_setup` reaches the loop entry with counter `s` and `W`'s
initial configuration within `tK + |s| + |x| + 5` steps; `clockTM_loop` finishes within
`ctrBound s ≤ 4·val(s) + 3|s| + 1` further steps with the answer
`loopAnswer (W.init x) (val s)`, which is the stated Boolean by
`Turing.FinTM.computesInTime_iff`. -/
theorem clockTM_spec (x s : List Bool) (tK : ℕ) (hK : K.ComputesInTime x s tK) :
    (clockTM K W).ComputesInTime x [!(decide (W.ComputesInTime x [true] (ctrVal s)))]
      (tK + 4 * s.length + x.length + 4 * ctrVal s + 6) := by
  obtain ⟨a, kt, kh, ha, hsetup⟩ := clockTM_setup K W x s tK hK
  obtain ⟨t, ht, h1, h2⟩ := clockTM_loop K W kt kh s (W.tm.initCfg x) W.tm.q₀ rfl
  have hreg : OutReg.ofList (W.tm.initCfg x).output = .empty := rfl
  rw [hreg] at h1 h2
  have hc : (clockTM K W).ComputesInTime x [!(decide (W.ComputesInTime x [true] (ctrVal s)))]
      (a + t) := by
    rw [computesInTime_iff, MultiTapeTM.runFrom_add, hsetup]
    refine ⟨h1, ?_⟩
    rw [h2]
    by_cases h : W.ComputesInTime x [true] (ctrVal s)
    · have h' := (computesInTime_iff W x [true] (ctrVal s)).mp h
      simp only [loopAnswer, h, h'.1, h'.2, and_self, decide_true]
    · have h' : ¬((W.tm.runFrom (W.tm.initCfg x) (ctrVal s)).state = none ∧
          (W.tm.runFrom (W.tm.initCfg x) (ctrVal s)).output = [true]) :=
        fun hh => h ((computesInTime_iff W x [true] (ctrVal s)).mpr hh)
      simp only [loopAnswer, h, h', decide_false]
  apply hc.mono
  have hb : ctrBound s ≤ 4 * ctrVal s + 3 * s.length + 1 := by
    unfold ctrBound; omega
  omega

end Complexity.TimeHierarchy
