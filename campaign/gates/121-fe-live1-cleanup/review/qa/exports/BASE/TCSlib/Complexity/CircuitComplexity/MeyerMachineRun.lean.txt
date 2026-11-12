/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.MeyerMachineSetup
import TCSlib.Complexity.TimeHierarchy.ClockLoop

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Meyer's theorem: the tableau machine's loops

The run analysis of the two counter loops of `Complexity.Meyer.tabTM`: the simulation
loop (one step of `M` per decrement of the counter `C`) and the walk loop (one head move
per decrement of the offset tape `O`), followed by the final emission (the walk loop is in `MeyerMachineWalk.lean`).

## Main definitions

* `Complexity.Meyer.lcfg` — loop configurations: `M`'s configuration embedded, its input
  head simulated on the copy tape.

## Main results

* `Complexity.Meyer.loop_run` — the simulation loop runs `M` for `val t` steps (or until
  it halts) within `(val t + 1)(2|t| + 3)` steps.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§6.4, Theorem 6.20, pp. 114–115.)
-/

namespace Complexity.Meyer

open Turing Turing.FinTM Complexity.TimeHierarchy

variable (M : FinTM Bool)

/-! ### Loop configurations -/

/-- **A loop configuration**: state `st`, real input head `P`, `M`'s configuration `c`
(its work tapes in `M`'s block, its input head at cell `pos - 1` of the copy tape holding
`x`), the counter `τC` with head `zC`, the offset tape `τO` with head `zO`, empty output.
`M`'s state and output are carried by `st`. -/
def lcfg {y x : List Bool} (st : St M) (P : Fin (y.length + 2))
    (c : Cfg M.k Bool M.State x) (τC : ℤ → Option Bool) (zC : ℤ) (τO : ℤ → Option Bool)
    (zO : ℤ) : Cfg (tabTM M).k Bool (tabTM M).State y :=
  tcfg M (some st) P c.workTapes c.workTapePos ![bufferTape x, τC, τO]
    ![(c.inputPos.val : ℤ) - 1, zC, zO] []

/-- The setup's end configuration is the loop configuration of `M`'s initial
configuration. -/
theorem acfg_eq_lcfg {y : List Bool} (st : St M) (P : Fin (y.length + 2)) (x t a : List Bool) :
    acfg M (some st) P (bufferTape x) (bufferTape t) (bufferTape a) 0 0 0 [] =
      lcfg M st P (M.tm.initCfg x) (bufferTape t) 0 (bufferTape a) 0 := by
  simp only [acfg, lcfg]
  congr

/-- One step from a loop configuration, with the reads made explicit. -/
theorem lcfg_step {y x : List Bool} (st : St M) (P : Fin (y.length + 2))
    (c : Cfg M.k Bool M.State x) (τC : ℤ → Option Bool) (zC : ℤ) (τO : ℤ → Option Bool)
    (zO : ℤ) :
    (tabTM M).tm.step (lcfg M st P c τC zC τO zO) =
      (tabTr M st (lcfg M st P c τC zC τO zO).inputSymbol
        (Fin.addCases c.workTapeSymbols ![c.inputSymbol, τC zC, τO zO])).apply
        (lcfg M st P c τC zC τO zO) := by
  rw [lcfg, tabTM_step]
  congr 2
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j; simp [Cfg.workTapeSymbols]
  · intro j
    simp only [Fin.addCases_right]
    fin_cases j
    · exact bufferTape_inputSymbol c
    · rfl
    · rfl

/-- **Applying an auxiliary-only action** to a loop configuration.

**Proof sketch.** Evaluate the block action on the three auxiliary tapes separately
(`fin_cases`); `M`'s block is idle and the copy tape is untouched by hypothesis. -/
theorem lcfg_apply_aux {y x : List Bool} (aw : Fin 3 → Option (Option Bool) × SignType)
    (o : Option Bool) (q : Option (St M)) (st : St M) (P : Fin (y.length + 2))
    (c : Cfg M.k Bool M.State x) (τC : ℤ → Option Bool) (zC : ℤ) (τO : ℤ → Option Bool)
    (zO : ℤ) (hX : aw 0 = (none, 0)) :
    (tact M 0 idle aw o q).apply (lcfg M st P c τC zC τO zO) =
      tcfg M q P c.workTapes c.workTapePos ![bufferTape x, wr (aw 1).1 τC zC, wr (aw 2).1 τO zO]
        ![(c.inputPos.val : ℤ) - 1, zC + (aw 1).2, zO + (aw 2).2] o.toList := by
  have ha : (fun j => wr (aw j).1 (![bufferTape x, τC, τO] j) (![(c.inputPos.val : ℤ) - 1, zC, zO] j)) =
      ![bufferTape x, wr (aw 1).1 τC zC, wr (aw 2).1 τO zO] := by
    funext j; fin_cases j
    · show wr (aw 0).1 _ _ = _; rw [hX]; rfl
    · rfl
    · rfl
  have hh : (fun j => (![(c.inputPos.val : ℤ) - 1, zC, zO] j) + ((aw j).2 : ℤ)) =
      ![(c.inputPos.val : ℤ) - 1, zC + (aw 1).2, zO + (aw 2).2] := by
    funext j; fin_cases j
    · show _ + ((aw 0).2 : ℤ) = _; rw [hX]; simp
    · rfl
    · rfl
  rw [lcfg, tact_apply, ha, hh]
  simp only [moveInputPos_zero, List.nil_append]
  congr 1
  funext i
  simp [idle]

/-! ### Steps of the simulation loop -/

section loopSteps

variable {y x : List Bool} (bits : Fin (nbits M) → Bool) (P : Fin (y.length + 2))
  (c : Cfg M.k Bool M.State x) (τC τO : ℤ → Option Bool) (zC zO : ℤ)

/-- The `M`-block reads of a loop configuration's work vector. -/
@[simp] theorem mreads (g : Fin 3 → Option Bool) :
    (fun i => (Fin.addCases c.workTapeSymbols g : Fin (M.k + 3) → Option Bool)
      (Fin.castAdd 3 i)) = c.workTapeSymbols := by
  funext i; simp

/-- Counter underflow ends the simulation loop. -/
theorem dec_under (q : M.State) (r : OutReg) (b : Bool) (h : τC zC = none) :
    (tabTM M).tm.step (lcfg M (.dec bits q r b) P c τC zC τO zO) =
      lcfg M (.wdec bits (some q) r b) P c τC zC τO zO := by
  rw [lcfg_step]
  simp only [tabTr, aux_read1, h]
  rw [lcfg_apply_aux M _ _ _ _ _ _ _ _ _ _ rfl]
  simp [lcfg]

/-- A zero counter bit is borrowed through. -/
theorem dec_zero (q : M.State) (r : OutReg) (b : Bool) (h : τC zC = some false) :
    (tabTM M).tm.step (lcfg M (.dec bits q r b) P c τC zC τO zO) =
      lcfg M (.dec bits q r b) P c (Function.update τC zC (some true)) (zC + 1) τO zO := by
  rw [lcfg_step]
  simp only [tabTr, aux_read1, h]
  rw [lcfg_apply_aux M _ _ _ _ _ _ _ _ _ _ rfl]
  simp [lcfg]

/-- Return sweep over a counter cell. -/
theorem ret_some (q : M.State) (r : OutReg) (b v : Bool) (h : τC zC = some v) :
    (tabTM M).tm.step (lcfg M (.ret bits q r b) P c τC zC τO zO) =
      lcfg M (.ret bits q r b) P c τC (zC - 1) τO zO := by
  rw [lcfg_step]
  simp only [tabTr, aux_read1, h]
  rw [lcfg_apply_aux M _ _ _ _ _ _ _ _ _ _ rfl]
  simp [lcfg, sub_eq_add_neg]

/-- End of the return sweep: back to cell `0` and the next decrement. -/
theorem ret_none (q : M.State) (r : OutReg) (b : Bool) (h : τC zC = none) :
    (tabTM M).tm.step (lcfg M (.ret bits q r b) P c τC zC τO zO) =
      lcfg M (.dec bits q r b) P c τC (zC + 1) τO zO := by
  rw [lcfg_step]
  simp only [tabTr, aux_read1, h]
  rw [lcfg_apply_aux M _ _ _ _ _ _ _ _ _ _ rfl]
  simp [lcfg]

/-- The successor control state after a fused step of `M`. -/
def fireNext (q' : Option M.State) (r : OutReg) (b : Bool) : St M :=
  match q' with
  | some q' => .ret bits q' r b
  | none => .wdec bits none r b

/-- **The fused step**: on a `true` counter bit, the bit is cleared and `M` takes one
step — its input read from the copy tape, its input move clamped by the arrival tag —
and the loop proceeds to the return sweep (or, if `M` halted, to the walk loop).

**Proof sketch.** Unfold one transition: the reads are `M`'s reads and the copy-tape symbol
(`bufferTape_inputSymbol`); the action applies `M`'s transition to `M`'s block, moves the
copy head by the clamped virtual move (`virtualMove_correct`) and clears the counter bit;
the new control state records `M`'s successor state and output summary. -/
theorem dec_fire (q : M.State) (b : Bool) (hq : c.state = some q)
    (hb : VirtualTag c.inputPos b) (h : τC zC = some true) :
    ∃ b', VirtualTag (M.tm.step c).inputPos b' ∧
      (tabTM M).tm.step (lcfg M (.dec bits q (OutReg.ofList c.output) b) P c τC zC τO zO) =
        lcfg M (fireNext M bits (M.tm.step c).state (OutReg.ofList (M.tm.step c).output) b')
          P (M.tm.step c) (Function.update τC zC (some false)) (zC - 1) τO zO := by
  set a := M.tm.tr q c.inputSymbol c.workTapeSymbols with ha
  set m := virtualMove b c.inputSymbol a.inputTape with hm
  have hmc := virtualMove_correct c b hb a.inputTape
  have hc : M.tm.step c = a.apply c := by simp only [MultiTapeTM.step, hq, a]
  refine ⟨virtualNextTag b m, by simpa only [hc, Action.apply] using hmc.2, ?_⟩
  rw [lcfg_step]
  simp only [tabTr, aux_read1, aux_read0, h, mreads]
  rw [← ha, ← hm, lcfg, tact_apply, hc]
  have hst : (a.apply c).state = a.state := rfl
  have hout : OutReg.ofList (a.apply c).output = (OutReg.ofList c.output).push a.output := by
    simp [Action.apply, OutReg.ofList_push]
  rw [hst, hout]
  have e4 : (fun j => (![(c.inputPos.val : ℤ) - 1, zC, zO] j) +
      (((two (0 : Fin 3) (none, m) 1 (some (some false), SignType.neg)) j).2 : ℤ)) =
      ![((a.apply c).inputPos.val : ℤ) - 1, zC - 1, zO] := by
    funext j
    fin_cases j
    · show (c.inputPos.val : ℤ) - 1 + (m : ℤ) = ((a.apply c).inputPos.val : ℤ) - 1
      simpa only [Action.apply] using hmc.1
    · show zC + ((SignType.neg : SignType) : ℤ) = zC - 1
      simp [SignType.neg_eq_neg_one, sub_eq_add_neg]
    · show zO + ((0 : SignType) : ℤ) = zO
      simp
  simp only [lcfg, moveInputPos_zero, List.nil_append, Option.toList]
  congr 1
  all_goals first
    | exact e4
    | (funext i; simp only [Action.apply]; cases (a.workTapes i).1 <;> rfl)
    | (funext j; fin_cases j <;> rfl)

end loopSteps

/-! ### The simulation loop -/

section loop

variable {y x : List Bool} (bits : Fin (nbits M) → Bool) (P : Fin (y.length + 2))

/-- Reading a stored word at an in-range cell. -/
theorem bufferTape_at (w : List Bool) (i : ℕ) (hi : i < w.length) :
    bufferTape w (i : ℤ) = some w[i] := by
  rw [bufferTape_nat, List.getElem?_eq_getElem hi]

/-- **The borrow sweep**: `j` zero bits are turned into ones in `j` steps.

**Proof sketch.** Induction on `j`: each step reads a `false`, writes `true`
(`bufferTape_update_mid`) and moves right. -/
theorem dec_sweep (c : Cfg M.k Bool M.State x) (q : M.State) (r : OutReg) (b : Bool)
    (τO : ℤ → Option Bool) (zO : ℤ) (rest : List Bool) :
    ∀ j i, (tabTM M).tm.runFrom (lcfg M (.dec bits q r b) P c
        (bufferTape (List.replicate i true ++ List.replicate j false ++ rest)) i τO zO) j =
      lcfg M (.dec bits q r b) P c (bufferTape (List.replicate (i + j) true ++ rest)) (i + j : ℕ)
        τO zO := by
  intro j
  induction j with
  | zero => intro i; simp
  | succ j ih =>
    intro i
    have hread : bufferTape (List.replicate i true ++ List.replicate (j + 1) false ++ rest)
        (i : ℤ) = some false := by
      rw [bufferTape_at _ _ (by simp)]
      simp [List.getElem_append_right, List.replicate_succ]
    rw [MultiTapeTM.runFrom_succ_eq_step, dec_zero M bits P c _ τO _ zO q r b hread]
    have hw : Function.update (bufferTape (List.replicate i true ++ List.replicate (j + 1) false ++ rest))
        (i : ℤ) (some true) = bufferTape (List.replicate (i + 1) true ++ List.replicate j false ++ rest) := by
      have := bufferTape_update_mid (List.replicate i true) (List.replicate j false ++ rest) false true
      simp only [List.length_replicate] at this
      rw [List.replicate_succ, List.append_assoc, List.cons_append, this, List.replicate_succ',
        List.append_assoc, List.append_assoc]
      rfl
    rw [hw, show (i : ℤ) + 1 = ((i + 1 : ℕ) : ℤ) by push_cast; ring, ih (i + 1)]
    congr 2 <;> simp [Nat.add_assoc, Nat.add_comm 1 j]

/-- **The return sweep** over `j` cells holding ones back to cell `0`: `j + 1` steps.

**Proof sketch.** Induction on `j`: each step reads a `true` and moves left; at cell `-1`
the blank sends the head back to cell `0`. -/
theorem ret_sweep (c : Cfg M.k Bool M.State x) (q : M.State) (r : OutReg) (b : Bool)
    (τO : ℤ → Option Bool) (zO : ℤ) (L : List Bool) :
    ∀ j, (tabTM M).tm.runFrom (lcfg M (.ret bits q r b) P c
        (bufferTape (List.replicate j true ++ L)) ((j : ℤ) - 1) τO zO) (j + 1) =
      lcfg M (.dec bits q r b) P c (bufferTape (List.replicate j true ++ L)) 0 τO zO := by
  intro j
  induction j generalizing L with
  | zero =>
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero,
      ret_none M bits P c _ τO _ zO q r b (by simp)]
    simp
  | succ j ih =>
    have hread : bufferTape (List.replicate (j + 1) true ++ L) (((j + 1 : ℕ) : ℤ) - 1) =
        some true := by
      rw [show (((j + 1 : ℕ) : ℤ) - 1) = (j : ℤ) by push_cast; ring,
        bufferTape_at _ _ (by simp; omega)]
      simp [List.getElem_append_left]
    rw [MultiTapeTM.runFrom_succ_eq_step, ret_some M bits P c _ τO _ zO q r b true hread,
      show (((j + 1 : ℕ) : ℤ) - 1 - 1) = (j : ℤ) - 1 by push_cast; ring]
    have hL : List.replicate (j + 1) true ++ L = List.replicate j true ++ (true :: L) := by
      simp [List.replicate_succ']
    rw [hL]
    exact ih (true :: L)

/-- **The simulation loop** [AB09, Thm 6.20, "`M` runs for `i` steps"]: from the loop
entry with counter word `w` of value `v` (head on cell `0`) and a live `M`
configuration `c`, the machine reaches the walk loop with `M`'s configuration
`runFrom c v` — `M` frozen once halted — within `(v + 1)(2|w| + 3)` steps.

**Proof sketch.** Strong induction on `v`. At `v = 0` the borrow sweep runs off the
all-zero word (`|w| + 1` steps). Otherwise `w = 0^j 1 rest`: the sweep (`j` steps), the
fused step of `M` (`dec_fire`) and, if `M` is still live, the return sweep (`j + 1`
steps) leave the word `1^j 0 rest` of value `v - 1` (`ctrVal_borrow`); if `M` halted,
the walk loop starts at once and `runFrom` is frozen. -/
theorem loop_run (τO : ℤ → Option Bool) (zO : ℤ) :
    ∀ (v : ℕ) (w : List Bool) (c : Cfg M.k Bool M.State x) (q : M.State) (b : Bool),
      ctrVal w = v → c.state = some q → VirtualTag c.inputPos b →
      ∃ s ≤ (v + 1) * (2 * w.length + 3), ∃ (τC : ℤ → Option Bool) (zC : ℤ) (b' : Bool),
        VirtualTag (M.tm.runFrom c v).inputPos b' ∧
        (tabTM M).tm.runFrom (lcfg M (.dec bits q (OutReg.ofList c.output) b) P c
          (bufferTape w) 0 τO zO) s =
          lcfg M (.wdec bits (M.tm.runFrom c v).state
            (OutReg.ofList (M.tm.runFrom c v).output) b') P (M.tm.runFrom c v) τC zC τO zO := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
  intro w c q b hv hq hb
  by_cases h0 : v = 0
  · subst h0
    have hw := ctrVal_zero_eq w hv
    have hs := dec_sweep M bits P c q (OutReg.ofList c.output) b τO zO [] w.length 0
    simp only [List.replicate_zero, List.nil_append, List.append_nil, Nat.zero_add,
      Nat.cast_zero] at hs
    rw [← hw] at hs
    refine ⟨w.length + 1, by simp only [Nat.zero_add, Nat.one_mul]; omega,
      bufferTape (List.replicate w.length true), (w.length : ℤ), b, by simpa using hb, ?_⟩
    rw [MultiTapeTM.runFrom_succ_eq_step', hs,
      dec_under M bits P c _ τO _ zO q _ b (by simp)]
    simp [hq]
  · obtain ⟨j, rest, hw⟩ := ctrVal_pos_decomp w (by omega)
    have hs := dec_sweep M bits P c q (OutReg.ofList c.output) b τO zO (true :: rest) j 0
    simp only [List.replicate_zero, List.nil_append, Nat.zero_add, Nat.cast_zero] at hs
    rw [← hw] at hs
    have hread : bufferTape (List.replicate j true ++ true :: rest) (j : ℤ) = some true := by
      rw [bufferTape_at _ _ (by simp)]; simp
    obtain ⟨b1, hb1, hf⟩ := dec_fire M bits P c (bufferTape (List.replicate j true ++ true :: rest))
      τO (j : ℤ) zO q b hq hb hread
    have hupd : Function.update (bufferTape (List.replicate j true ++ true :: rest)) (j : ℤ)
        (some false) = bufferTape (List.replicate j true ++ false :: rest) := by
      have := bufferTape_update_mid (List.replicate j true) rest true false
      simpa using this
    rw [hupd] at hf
    have hlen : (List.replicate j true ++ false :: rest).length = w.length := by
      rw [hw]; simp
    have hval : ctrVal (List.replicate j true ++ false :: rest) = v - 1 := by
      have := ctrVal_borrow j rest
      rw [← hw, hv] at this
      omega
    have hrun : M.tm.runFrom c v = M.tm.runFrom (M.tm.step c) (v - 1) := by
      rw [show v = (v - 1) + 1 by omega, MultiTapeTM.runFrom_succ_eq_step]
      simp
    cases hst : (M.tm.step c).state with
    | none =>
      -- `M` halted: the walk loop starts at once
      refine ⟨j + 1, ?_, bufferTape (List.replicate j true ++ false :: rest), (j : ℤ) - 1, b1,
        ?_, ?_⟩
      · have : j + 1 ≤ w.length + 1 := by rw [hw]; simp
        calc j + 1 ≤ 1 * (2 * w.length + 3) := by omega
          _ ≤ (v + 1) * (2 * w.length + 3) := Nat.mul_le_mul_right _ (by omega)
      · rw [hrun, MultiTapeTM.runFrom_of_halt _ hst]; exact hb1
      · rw [MultiTapeTM.runFrom_succ_eq_step', hs, hf, hrun,
          MultiTapeTM.runFrom_of_halt _ hst, hst]
        rfl
    | some q' =>
      obtain ⟨s', hs', τC, zC, b', hb', hrest⟩ := ih (v - 1) (by omega)
        (List.replicate j true ++ false :: rest) (M.tm.step c) q' b1 hval hst hb1
      have hret := ret_sweep M bits P (M.tm.step c) q' (OutReg.ofList (M.tm.step c).output) b1
        τO zO (false :: rest) j
      refine ⟨j + 1 + (j + 1) + s', ?_, τC, zC, b', by rw [hrun]; exact hb', ?_⟩
      · rw [hlen] at hs'
        have : j + 1 ≤ w.length := by rw [hw]; simp
        have hv1 : v - 1 + 1 = v := by omega
        calc j + 1 + (j + 1) + s' ≤ 2 * w.length + 3 + (v - 1 + 1) * (2 * w.length + 3) := by
              omega
          _ = (v + 1) * (2 * w.length + 3) := by rw [hv1]; ring
      · have e1 : (tabTM M).tm.runFrom (lcfg M (.dec bits q (OutReg.ofList c.output) b) P c
            (bufferTape w) 0 τO zO) (j + 1) =
            lcfg M (.ret bits q' (OutReg.ofList (M.tm.step c).output) b1) P (M.tm.step c)
              (bufferTape (List.replicate j true ++ false :: rest)) ((j : ℤ) - 1) τO zO := by
          rw [MultiTapeTM.runFrom_succ_eq_step', hs, hf, hst]
          rfl
        rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, e1, hret, hrest, hrun]

end loop

end Complexity.Meyer
