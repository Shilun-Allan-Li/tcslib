/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.MeyerMachineRun

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Meyer's theorem: the tableau machine's walk loop

The second counter loop of `Complexity.Meyer.tabTM`: each decrement of the offset tape
`O` is fused with one move of the selected head, and offset underflow emits the selected
bit of the reached configuration.

## Main definitions

* `Complexity.Meyer.wstep` — one walk move of the selected head.

## Main results

* `Complexity.Meyer.walk_run` — the walk loop moves the selected head `val a` times and
  emits the selected bit, within `(val a + 1)(2|a| + 3)` steps.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§6.4, Theorem 6.20, pp. 114–115.)
-/

namespace Complexity.Meyer

open Turing Turing.FinTM Complexity.TimeHierarchy

variable (M : FinTM Bool)

/-! ### The walk loop -/

/-- **One walk move** of the head selected by `sel`: work head `h` moves one cell in the
selected direction; the input head moves with clamping; a state selector moves nothing. -/
def wstep {x : List Bool} (sel : Sel M) (c : Cfg M.k Bool M.State x) : Cfg M.k Bool M.State x :=
  match sel with
  | .sym (some h) neg _ =>
    { c with workTapePos := Function.update c.workTapePos h (c.workTapePos h + (walkDir neg : ℤ)) }
  | .sym none neg _ => { c with inputPos := moveInputPos c.inputPos (walkDir neg) }
  | .st _ _ => c

section walkSteps

variable {y x : List Bool} (bits : Fin (nbits M) → Bool) (P : Fin (y.length + 2))
  (c : Cfg M.k Bool M.State x) (τC τO : ℤ → Option Bool) (zC zO : ℤ)

/-- Offset underflow: emit the selected bit and halt. -/
theorem wdec_emit (oq : Option M.State) (r : OutReg) (b : Bool) (h : τO zO = none) :
    ((tabTM M).tm.step (lcfg M (.wdec bits oq r b) P c τC zC τO zO)).state = none ∧
      ((tabTM M).tm.step (lcfg M (.wdec bits oq r b) P c τC zC τO zO)).output =
        [selAnswer (decodeSel bits) oq r c.inputSymbol c.workTapeSymbols] := by
  rw [lcfg_step]
  simp only [tabTr, aux_read2, aux_read0, h, mreads]
  rw [lcfg_apply_aux M _ _ _ _ _ _ _ _ _ _ rfl]
  simp [tcfg]

/-- A zero offset bit is borrowed through. -/
theorem wdec_zero (oq : Option M.State) (r : OutReg) (b : Bool) (h : τO zO = some false) :
    (tabTM M).tm.step (lcfg M (.wdec bits oq r b) P c τC zC τO zO) =
      lcfg M (.wdec bits oq r b) P c τC zC (Function.update τO zO (some true)) (zO + 1) := by
  rw [lcfg_step]
  simp only [tabTr, aux_read2, h]
  rw [lcfg_apply_aux M _ _ _ _ _ _ _ _ _ _ rfl]
  simp [lcfg]

/-- Return sweep over an offset cell. -/
theorem wret_some (oq : Option M.State) (r : OutReg) (b v : Bool) (h : τO zO = some v) :
    (tabTM M).tm.step (lcfg M (.wret bits oq r b) P c τC zC τO zO) =
      lcfg M (.wret bits oq r b) P c τC zC τO (zO - 1) := by
  rw [lcfg_step]
  simp only [tabTr, aux_read2, h]
  rw [lcfg_apply_aux M _ _ _ _ _ _ _ _ _ _ rfl]
  simp [lcfg, sub_eq_add_neg]

/-- End of the offset return sweep. -/
theorem wret_none (oq : Option M.State) (r : OutReg) (b : Bool) (h : τO zO = none) :
    (tabTM M).tm.step (lcfg M (.wret bits oq r b) P c τC zC τO zO) =
      lcfg M (.wdec bits oq r b) P c τC zC τO (zO + 1) := by
  rw [lcfg_step]
  simp only [tabTr, aux_read2, h]
  rw [lcfg_apply_aux M _ _ _ _ _ _ _ _ _ _ rfl]
  simp [lcfg]

/-- **The fused walk move**: on a `true` offset bit, the bit is cleared and the selected
head moves one cell.

**Proof sketch.** Case on the decoded selector: a work selector moves that head
(`Function.update` of the head positions), an input selector moves the copy head by the
clamped virtual move, a state selector moves nothing; in each case the offset bit is
cleared. -/
theorem wdec_fire (oq : Option M.State) (r : OutReg) (b : Bool) (hb : VirtualTag c.inputPos b)
    (h : τO zO = some true) :
    ∃ b', VirtualTag (wstep M (decodeSel bits) c).inputPos b' ∧
      (tabTM M).tm.step (lcfg M (.wdec bits oq r b) P c τC zC τO zO) =
        lcfg M (.wret bits oq r b') P (wstep M (decodeSel bits) c) τC zC
          (Function.update τO zO (some false)) (zO - 1) := by
  rw [lcfg_step]
  simp only [tabTr, aux_read2, aux_read0, h]
  cases hsel : decodeSel bits with
  | st σ r₀ =>
    refine ⟨b, hb, ?_⟩
    simp only
    rw [lcfg_apply_aux M _ _ _ _ _ _ _ _ _ _ rfl]
    simp [lcfg, wstep, sub_eq_add_neg]
  | sym h? neg bl =>
    cases h? with
    | some hh =>
      refine ⟨b, by simpa [wstep] using hb, ?_⟩
      simp only
      rw [lcfg, tact_apply]
      simp only [lcfg, wstep, moveInputPos_zero, List.nil_append, Option.toList]
      congr 1
      all_goals first
        | (funext i
           by_cases hi : i = hh
           · subst hi; simp [one]
           · simp [one, idle, Function.update_of_ne hi])
        | (funext j; fin_cases j <;> rfl)
        | (funext j; fin_cases j
           · show _ + ((0 : SignType) : ℤ) = _; simp
           · show _ + ((0 : SignType) : ℤ) = _; simp
           · show zO + ((SignType.neg : SignType) : ℤ) = zO - 1
             simp [SignType.neg_eq_neg_one, sub_eq_add_neg])
    | none =>
      set m := virtualMove b c.inputSymbol (walkDir neg) with hm
      have hmc := virtualMove_correct c b hb (walkDir neg)
      refine ⟨virtualNextTag b m, by simpa [wstep] using hmc.2, ?_⟩
      simp only
      rw [← hm, lcfg, tact_apply]
      simp only [lcfg, wstep, moveInputPos_zero, List.nil_append, Option.toList]
      congr 1
      all_goals first
        | (funext i; simp [idle]; done)
        | (funext j; fin_cases j <;> rfl)
        | (funext j; fin_cases j
           · show (c.inputPos.val : ℤ) - 1 + (m : ℤ) = _
             simpa using hmc.1
           · show _ + ((0 : SignType) : ℤ) = _; simp
           · show zO + ((SignType.neg : SignType) : ℤ) = zO - 1
             simp [SignType.neg_eq_neg_one, sub_eq_add_neg])

end walkSteps

section walk

variable {y x : List Bool} (bits : Fin (nbits M) → Bool) (P : Fin (y.length + 2))

/-- The offset borrow sweep: `j` zero bits turned into ones in `j` steps.

**Proof sketch.** As `dec_sweep`, on the offset tape. -/
theorem wdec_sweep (c : Cfg M.k Bool M.State x) (oq : Option M.State) (r : OutReg) (b : Bool)
    (τC : ℤ → Option Bool) (zC : ℤ) (rest : List Bool) :
    ∀ j i, (tabTM M).tm.runFrom (lcfg M (.wdec bits oq r b) P c τC zC
        (bufferTape (List.replicate i true ++ List.replicate j false ++ rest)) i) j =
      lcfg M (.wdec bits oq r b) P c τC zC (bufferTape (List.replicate (i + j) true ++ rest))
        (i + j : ℕ) := by
  intro j
  induction j with
  | zero => intro i; simp
  | succ j ih =>
    intro i
    have hread : bufferTape (List.replicate i true ++ List.replicate (j + 1) false ++ rest)
        (i : ℤ) = some false := by
      rw [bufferTape_at _ _ (by simp)]
      simp [List.getElem_append_right, List.replicate_succ]
    rw [MultiTapeTM.runFrom_succ_eq_step, wdec_zero M bits P c τC _ zC _ oq r b hread]
    have hw : Function.update (bufferTape (List.replicate i true ++ List.replicate (j + 1) false ++ rest))
        (i : ℤ) (some true) = bufferTape (List.replicate (i + 1) true ++ List.replicate j false ++ rest) := by
      have := bufferTape_update_mid (List.replicate i true) (List.replicate j false ++ rest) false true
      simp only [List.length_replicate] at this
      rw [List.replicate_succ, List.append_assoc, List.cons_append, this, List.replicate_succ',
        List.append_assoc, List.append_assoc]
      rfl
    rw [hw, show (i : ℤ) + 1 = ((i + 1 : ℕ) : ℤ) by push_cast; ring, ih (i + 1)]
    congr 2 <;> simp [Nat.add_assoc, Nat.add_comm 1 j]

/-- The offset return sweep: `j + 1` steps back to cell `0`.

**Proof sketch.** As `ret_sweep`, on the offset tape. -/
theorem wret_sweep (c : Cfg M.k Bool M.State x) (oq : Option M.State) (r : OutReg) (b : Bool)
    (τC : ℤ → Option Bool) (zC : ℤ) (L : List Bool) :
    ∀ j, (tabTM M).tm.runFrom (lcfg M (.wret bits oq r b) P c τC zC
        (bufferTape (List.replicate j true ++ L)) ((j : ℤ) - 1)) (j + 1) =
      lcfg M (.wdec bits oq r b) P c τC zC (bufferTape (List.replicate j true ++ L)) 0 := by
  intro j
  induction j generalizing L with
  | zero =>
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero,
      wret_none M bits P c τC _ zC _ oq r b (by simp)]
    simp
  | succ j ih =>
    have hread : bufferTape (List.replicate (j + 1) true ++ L) (((j + 1 : ℕ) : ℤ) - 1) =
        some true := by
      rw [show (((j + 1 : ℕ) : ℤ) - 1) = (j : ℤ) by push_cast; ring,
        bufferTape_at _ _ (by simp; omega)]
      simp [List.getElem_append_left]
    rw [MultiTapeTM.runFrom_succ_eq_step, wret_some M bits P c τC _ zC _ oq r b true hread,
      show (((j + 1 : ℕ) : ℤ) - 1 - 1) = (j : ℤ) - 1 by push_cast; ring]
    have hL : List.replicate (j + 1) true ++ L = List.replicate j true ++ (true :: L) := by
      simp [List.replicate_succ']
    rw [hL]
    exact ih (true :: L)

/-- **The walk loop**: from the walk entry with offset word `w` of value `v` (head on cell
`0`), the selected head is moved `v` times and the selected bit of the reached
configuration is emitted; the machine halts within `(v + 1)(2|w| + 3)` steps.

**Proof sketch.** As `loop_run`, with the fused walk move `wdec_fire` in place of the
step of `M`, and the emission `wdec_emit` at underflow. -/
theorem walk_run (oq : Option M.State) (r : OutReg) (τC : ℤ → Option Bool) (zC : ℤ) :
    ∀ (v : ℕ) (w : List Bool) (c : Cfg M.k Bool M.State x) (b : Bool),
      ctrVal w = v → VirtualTag c.inputPos b →
      ∃ s ≤ (v + 1) * (2 * w.length + 3),
        ((tabTM M).tm.runFrom (lcfg M (.wdec bits oq r b) P c τC zC (bufferTape w) 0) s).state =
          none ∧
        ((tabTM M).tm.runFrom (lcfg M (.wdec bits oq r b) P c τC zC (bufferTape w) 0) s).output =
          [selAnswer (decodeSel bits) oq r ((wstep M (decodeSel bits))^[v] c).inputSymbol
            ((wstep M (decodeSel bits))^[v] c).workTapeSymbols] := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
  intro w c b hv hb
  by_cases h0 : v = 0
  · subst h0
    have hw := ctrVal_zero_eq w hv
    have hs := wdec_sweep M bits P c oq r b τC zC [] w.length 0
    simp only [List.replicate_zero, List.nil_append, List.append_nil, Nat.zero_add,
      Nat.cast_zero] at hs
    rw [← hw] at hs
    refine ⟨w.length + 1, by simp only [Nat.zero_add, Nat.one_mul]; omega, ?_⟩
    rw [MultiTapeTM.runFrom_succ_eq_step', hs]
    simpa using wdec_emit M bits P c τC _ zC _ oq r b (by simp)
  · obtain ⟨j, rest, hw⟩ := ctrVal_pos_decomp w (by omega)
    have hs := wdec_sweep M bits P c oq r b τC zC (true :: rest) j 0
    simp only [List.replicate_zero, List.nil_append, Nat.zero_add, Nat.cast_zero] at hs
    rw [← hw] at hs
    have hread : bufferTape (List.replicate j true ++ true :: rest) (j : ℤ) = some true := by
      rw [bufferTape_at _ _ (by simp)]; simp
    obtain ⟨b1, hb1, hf⟩ := wdec_fire M bits P c τC
      (bufferTape (List.replicate j true ++ true :: rest)) zC (j : ℤ) oq r b hb hread
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
    obtain ⟨s', hs', hrest⟩ := ih (v - 1) (by omega)
      (List.replicate j true ++ false :: rest) (wstep M (decodeSel bits) c) b1 hval hb1
    have hret := wret_sweep M bits P (wstep M (decodeSel bits) c) oq r b1 τC zC (false :: rest) j
    have hiter : (wstep M (decodeSel bits))^[v] c =
        (wstep M (decodeSel bits))^[v - 1] (wstep M (decodeSel bits) c) := by
      rw [show v = (v - 1) + 1 by omega, Function.iterate_succ_apply]
      simp
    refine ⟨j + 1 + (j + 1) + s', ?_, ?_⟩
    · rw [hlen] at hs'
      have : j + 1 ≤ w.length := by rw [hw]; simp
      have hv1 : v - 1 + 1 = v := by omega
      calc j + 1 + (j + 1) + s' ≤ 2 * w.length + 3 + (v - 1 + 1) * (2 * w.length + 3) := by
            omega
        _ = (v + 1) * (2 * w.length + 3) := by rw [hv1]; ring
    · have e1 : (tabTM M).tm.runFrom (lcfg M (.wdec bits oq r b) P c τC zC (bufferTape w) 0)
          (j + 1) = lcfg M (.wret bits oq r b1) P (wstep M (decodeSel bits) c) τC zC
            (bufferTape (List.replicate j true ++ false :: rest)) ((j : ℤ) - 1) := by
        rw [MultiTapeTM.runFrom_succ_eq_step', hs, hf]
      rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, e1, hret, hiter]
      exact hrest

end walk

end Complexity.Meyer
