/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.CounterLoop

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The bounded input window copier

A counter-driven copy of a bounded window of the native input onto a work tape (user decision 5
of 2026-10-13; the C1 design note §2.2 step U7 and §3.4 device (i)). The universal NDTM cannot
copy its whole input `x`, since its time bound has no `|x|` term; it copies the window
`x.take t` instead, and the input-locality lemma `Turing.NDTM.runWith_initCfg_take` shows that
the window is enough for `t` simulated steps. The in-place suffix device stays with the
universal machine U-1, whose `universal` has no deadline to truncate by.

## Main definitions

No new definitions: the copier is the existential contract `Turing.exists_inputWindowCopyTM`.

## Main results

* `Turing.exists_inputWindowCopyTM` — the window copier's contract (proved).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2: the read-only input tape.)
-/

namespace Turing

/-- The one-step copy body on one work tape. In state `false`, on an input symbol it writes the
symbol, moves the tape head and the input head right and stays in `false`; at the input's right
end it moves to `true` without writing or moving. -/
private def iw_body : MultiTapeTM 1 Bool Bool where
  q₀ := false
  tr := fun q inp _ =>
    if q then FinTM.controlAction 0 (some true)
    else match inp with
      | none => FinTM.controlAction 0 (some true)
      | some b => ⟨1, fun _ => (some (some b), 1), none, some false⟩

/-- One step from a live state applies that state's transition at the scanned symbols. -/
private theorem iw_one {k : ℕ} {S : Type} {z : List Bool} (M : MultiTapeTM k Bool S)
    (c : Cfg k Bool S z) (q : S) (hc : c.state = some q) :
    M.runFrom c 1 = (M.tr q c.inputSymbol c.workTapeSymbols).apply c := by
  calc
    _ = M.step (M.runFrom c 0) := MultiTapeTM.runFrom_succ_eq_step'
    _ = _ := by rw [MultiTapeTM.runFrom_zero, MultiTapeTM.step_of_some hc]

/-- One successful copy step writes the scanned bit, advances both heads and emits nothing. -/
private theorem iw_body_copy {z : List Bool} (c : Cfg 1 Bool Bool z) (b : Bool)
    (hc : c.state = some false) (hb : c.inputSymbol = some b) :
    iw_body.runFrom c 1 =
      { c with
        state := some false, inputPos := moveInputPos c.inputPos 1,
        workTapes := fun i => Function.update (c.workTapes i) (c.workTapePos i) (some b),
        workTapePos := fun i => c.workTapePos i + 1 } := by
  rw [iw_one iw_body c false hc]
  simp only [iw_body, Bool.false_eq_true, if_false, hb]
  apply Cfg.ext
  · rw [Action.apply_state]
  · rw [Action.apply_inputPos]
  · funext i
    simp only [Action.apply_workTapes, Option.getD_some]
  · funext i
    simp only [Action.apply_workTapePos, SignType.coe_one]
  · rw [Action.apply_output]
    exact List.append_nil _

/-- On a blank input cell, the body escapes in one step without changing any data. -/
private theorem iw_body_blank {z : List Bool} (c : Cfg 1 Bool Bool z)
    (hc : c.state = some false) (hb : c.inputSymbol = none) :
    iw_body.runFrom c 1 = { c with state := some true } := by
  rw [iw_one iw_body c false hc]
  simp only [iw_body, Bool.false_eq_true, if_false, hb,
    FinTM.controlAction_apply, moveInputPos_zero]

/-- Overwrite a finite interval of a tape, leaving its exterior intact. -/
private def iw_patch (tape : ℤ → Option Bool) (head : ℤ) (v : List Bool) :
    ℤ → Option Bool := fun q =>
  if head ≤ q ∧ q < head + (v.length : ℤ)
    then FinTM.bufferTape v (q - head) else tape q

/-- Appending a bit to the copied interval changes exactly its next cell.

**Proof sketch.** At the next cell use the buffer's append equation. Inside the old interval
that equation preserves the old symbol; outside the enlarged interval both tapes are framed. -/
private theorem iw_patch_append (tape : ℤ → Option Bool) (head : ℤ)
    (v : List Bool) (b : Bool) :
    iw_patch tape head (v ++ [b]) =
      Function.update (iw_patch tape head v) (head + (v.length : ℤ)) (some b) := by
  funext q
  by_cases he : q = head + (v.length : ℤ)
  · subst q
    rw [Function.update_self]
    simp only [iw_patch, List.length_append, List.length_singleton, Nat.cast_add,
      Nat.cast_one]
    rw [if_pos (by omega), FinTM.bufferTape_append, add_sub_cancel_left, Function.update_self]
  · rw [Function.update_of_ne he]
    by_cases hi : head ≤ q ∧ q < head + (v.length : ℤ)
    · simp only [iw_patch, List.length_append, List.length_singleton, Nat.cast_add,
        Nat.cast_one]
      rw [if_pos hi, if_pos (by omega), FinTM.bufferTape_append,
        Function.update_of_ne (by omega)]
    · simp only [iw_patch, List.length_append, List.length_singleton, Nat.cast_add,
        Nat.cast_one]
      rw [if_neg hi, if_neg (by omega)]

/-- The body configuration after copying `r` input cells starting at input index `p`. -/
private def iw_prefix {z : List Bool} (c : Cfg 1 Bool Bool z) (p r : ℕ)
    (hr : p + r ≤ z.length) : Cfg 1 Bool Bool z where
  state := some false
  inputPos := ⟨p + 1 + r, by omega⟩
  workTapes := fun _ => iw_patch (c.workTapes 0) (c.workTapePos 0) ((z.drop p).take r)
  workTapePos := fun _ => c.workTapePos 0 + (r : ℤ)
  output := c.output

/-- The zero-length copied prefix is the initial configuration. -/
private theorem iw_prefix_zero {z : List Bool} (c : Cfg 1 Bool Bool z) (p : ℕ)
    (hp : p ≤ z.length) (hc : c.state = some false) (hi : c.inputPos.val = p + 1) :
    iw_prefix c p 0 (by omega) = c := by
  apply Cfg.ext hc.symm
  · apply Fin.ext
    simpa only [iw_prefix, Nat.add_zero] using hi.symm
  · funext i q
    have hz : i = 0 := Subsingleton.elim _ _
    subst i
    simp [iw_prefix, iw_patch]
  · funext i
    have hz : i = 0 := Subsingleton.elim _ _
    subst i
    simp only [iw_prefix, Nat.cast_zero, add_zero]
  · rfl

/-- A successful body round extends the copied input prefix by exactly one cell.

**Proof sketch.** The next input bit has index `p + r`. The one-step leaf writes it at the
next free destination cell, which is exactly the interval append equation. -/
private theorem iw_prefix_step {z : List Bool} (c : Cfg 1 Bool Bool z) (p r : ℕ)
    (hr : p + r < z.length) :
    iw_body.runFrom (iw_prefix c p r (by omega)) 1 =
      iw_prefix c p (r + 1) (by omega) := by
  have hdrop : r < (z.drop p).length := by rw [List.length_drop]; omega
  have hlen : ((z.drop p).take r).length = r := List.length_take_of_le hdrop.le
  have hbit : (iw_prefix c p r (by omega)).inputSymbol = some z[p + r] :=
    inputSymbolInner (p + r) (by simp only [iw_prefix]; omega) hr
  rw [iw_body_copy _ _ rfl hbit]
  refine Cfg.ext rfl ?_ ?_ ?_ ?_
  · apply Fin.ext
    rw [← SignType.pos_eq_one,
      moveInputPos_pos_of_ne_right _ (by simp only [iw_prefix]; omega)]
    simp only [iw_prefix]
    omega
  · funext i
    simp only [iw_prefix]
    rw [List.take_succ_eq_append_getElem hdrop, List.getElem_drop, iw_patch_append, hlen]
  · funext i
    simp only [iw_prefix, Nat.cast_add, Nat.cast_one]
    omega
  · rfl

/-- The one-step round orbit is the explicitly copied prefix while input cells remain.

**Proof sketch.** Induct on the number of rounds using the round-orbit equations and
the one-cell extension lemma. -/
private theorem iw_orbit {z : List Bool} (c : Cfg 1 Bool Bool z) (p : ℕ)
    (hc : c.state = some false) (hi : c.inputPos.val = p + 1) (r : ℕ)
    (hr : p + r ≤ z.length) :
    counterLoopOrbit iw_body (fun _ => 1) c r = iw_prefix c p r hr := by
  induction r with
  | zero =>
    simpa only [roundOrbit_zero] using (iw_prefix_zero c p (by omega) hc hi).symm
  | succ r ih =>
    simp only [roundOrbit_succ]
    exact (congrArg (fun x => iw_body.runFrom x 1) (ih (by omega))).trans
      (iw_prefix_step c p r (by omega))

/-- The counter loop's escape anchor takes one silent stationary step to its done anchor.
Every other transition is the counter loop's. -/
private def iw_machine : MultiTapeTM 2 Bool (CounterLoopState Bool) where
  q₀ := .dec .run
  tr := fun q inp work => match q with
    | .escape => FinTM.controlAction 0 (some .done)
    | _ => (counterLoopTM iw_body false (some true)).tr q inp work

/-- Before the escape anchor is visited, adding the exit join does not change the run.

**Proof sketch.** The transition tables agree off the escape anchor, so the runs agree
until it is first visited (`Turing.MultiTapeTM.runFrom_eq_of_agreeOn`). -/
private theorem iw_join_prefix {z : List Bool} (c : Cfg 2 Bool (CounterLoopState Bool) z)
    (t : ℕ) (hcut : ∀ u < t,
      ((counterLoopTM iw_body false (some true)).runFrom c u).state ≠ some .escape) :
    iw_machine.runFrom c t = (counterLoopTM iw_body false (some true)).runFrom c t := by
  apply MultiTapeTM.runFrom_eq_of_agreeOn (Q := {q | q ≠ .escape})
  · apply (MultiTapeTM.agreeOn_iff _ _ _).mpr
    intro q hq inp work
    cases q with
    | escape => exact (hq rfl).elim
    | body _ => rfl
    | dec _ => rfl
    | done => rfl
  · intro u hu q hs he
    exact hcut u hu (hs.trans (congrArg some he))

/-- The join changes only the control state at the escape anchor. -/
private theorem iw_join_step {z : List Bool} (c : Cfg 2 Bool (CounterLoopState Bool) z)
    (hc : c.state = some .escape) :
    iw_machine.runFrom c 1 = { c with state := some .done } := by
  rw [iw_one iw_machine c .escape hc]
  simp only [iw_machine, FinTM.controlAction_apply, moveInputPos_zero]

/-- The all-true underflow word has exactly the counter loop's reported tape contents. -/
private theorem iw_patch_true (ct : ℤ → Option Bool) (cp : ℤ) (width : ℕ) :
    iw_patch ct cp (List.replicate width true) =
      fun q => if cp ≤ q ∧ q < cp + (width : ℤ) then some true else ct q := by
  funext q
  simp only [iw_patch, List.length_replicate]
  split_ifs with h
  · rw [FinTM.bufferTape_eq, if_pos (by omega), List.getElem?_replicate_of_lt (by omega)]
  · rfl

/-- The two-tape copier stops after the available window, with its counter width preserved.

**Proof sketch.** If the counter value fits in the remaining input, use the returning loop
contract and its whole-run underflow bound. Otherwise use the escape contract after one
additional blank-reading round, then the stationary exit join. Both contracts exclude an
earlier exit; their ledgers give the common coefficient six. -/
private theorem iw_local {z : List Bool} (c : Cfg 1 Bool Bool z) (p : ℕ)
    (hc : c.state = some false) (hi : c.inputPos.val = p + 1) (_hp : p ≤ z.length)
    (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ)
    (hw : ∀ q : ℤ, -1 ≤ q → q ≤ (w.length : ℤ) → ct (cp + q) = FinTM.bufferTape w q)
    (n : ℕ) (hn : n = min (Nat.ofDigits 2 (w.map Bool.toNat)) (z.length - p)) :
    ∃ T ≤ 6 * (n + 1) + 2 * w.length, ∃ v : List Bool, v.length = w.length ∧
      iw_machine.runFrom (counterLoopCfg (some (.dec .run)) c ct cp) T =
        counterLoopCfg (some .done)
          (iw_prefix c p n (by
            have := Nat.min_le_right (Nat.ofDigits 2 (w.map Bool.toNat)) (z.length - p)
            omega)) (iw_patch ct cp v) cp ∧
      ∀ u < T,
        (iw_machine.runFrom (counterLoopCfg (some (.dec .run)) c ct cp) u).state ≠ some .done := by
  let d := Nat.ofDigits 2 (w.map Bool.toNat)
  let start := counterLoopCfg (some (.dec .run)) c ct cp
  have horbit (r : ℕ) (hr : p + r ≤ z.length) := iw_orbit c p hc hi r hr
  by_cases hd : d ≤ z.length - p
  · have hnd : n = d := hn.trans (Nat.min_eq_left hd)
    subst hnd
    let t := d + counterOverhead w (d + 1)
    obtain ⟨hend, hcut, _, _⟩ := counterLoopTM_run_done iw_body false (some true)
      (fun _ => 1) c w ct cp hw d rfl (fun r hr => by
        refine ⟨?_, Nat.one_pos, (fun u hu hu' => by dsimp only at hu'; omega), ?_⟩
        · rw [horbit r (by omega)]; rfl
        · rw [horbit (r + 1) (by omega)]; rfl) t (by simp [t])
    have hsame : iw_machine.runFrom start t =
        (counterLoopTM iw_body false (some true)).runFrom start t :=
      iw_join_prefix start t (fun u hu => (hcut u hu).2)
    refine ⟨t, ?_, List.replicate w.length true, List.length_replicate, ?_, ?_⟩
    · have hover := counterOverhead_le w
      change counterOverhead w (d + 1) ≤ 4 * d + 2 * w.length + 2 at hover
      dsimp only [t]
      omega
    · rw [hsame, hend, horbit d (by omega), iw_patch_true]
    · intro u hu
      rw [iw_join_prefix start u (fun s hs => (hcut s (by omega)).2)]
      exact (hcut u hu).1
  · have hnd : n = z.length - p := hn.trans (Nat.min_eq_right (by omega))
    have hpn : p + n = z.length := by omega
    have hnd' : n < d := by omega
    let t := n + 1 + counterOverhead w (n + 1)
    have hfinal : counterLoopOrbit iw_body (fun _ => 1) c (n + 1) =
        { iw_prefix c p n (by omega) with state := some true } := by
      simp only [roundOrbit_succ]
      exact (congrArg (fun x => iw_body.runFrom x 1) (horbit n (by omega))).trans
        (iw_body_blank _ rfl (Cfg.inputSymbol_of_end (by simp only [iw_prefix]; omega)))
    obtain ⟨hend, hcut, _, _⟩ := counterLoopTM_run_escape iw_body false true (by decide)
      (fun _ => 1) c w ct cp hw n hnd' (fun r hr => by
        refine ⟨?_, Nat.one_pos, (fun u hu hu' => by dsimp only at hu'; omega)⟩
        rw [horbit r (by omega)]; rfl) (by rw [hfinal]) t (by simp [t])
    have hsame (u : ℕ) (hu : u ≤ t) : iw_machine.runFrom start u =
        (counterLoopTM iw_body false (some true)).runFrom start u :=
      iw_join_prefix start u (fun s hs => (hcut s (by omega)).2)
    have hex : (iw_machine.runFrom start t).state = some .escape := by
      rw [hsame t le_rfl, hend, counter_cfg_eq]
    refine ⟨t + 1, ?_, counterWord w (n + 1), counterWord_length _ _, ?_, ?_⟩
    · have hover := counterOverhead_le_of_le w (n + 1) hnd'
      dsimp only [t]
      omega
    · rw [MultiTapeTM.runFrom_add, iw_join_step _ hex, hsame t le_rfl, hend, hfinal]
      have hpatch : iw_patch ct cp (counterWord w (n + 1)) = fun q =>
          if cp ≤ q ∧ q < cp + (w.length : ℤ) then
            FinTM.bufferTape (counterWord w (n + 1)) (q - cp)
          else ct q := by
        funext q
        simp only [iw_patch, counterWord_length]
      simp only [counter_cfg_eq, hpatch]
    · intro u hu
      by_cases hut : u < t
      · rw [hsame u (by omega)]
        exact (hcut u hut).1
      · have hut' : u = t := by omega
        subst u
        rw [hex]
        simp

/-- Select the destination as tape zero and the distinct counter as tape one. -/
private def iw_select {k : ℕ} (j dst : Fin k) (hjd : j ≠ dst) : Fin 2 ↪ Fin k :=
  ⟨fun i => if i = 0 then dst else j, by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all⟩

/-- **The bounded input window copier.** For work tapes `j ≠ dst` there is a machine with an
entry state `entry`, a live exit `done` and a constant `C` such that: started at `entry` with its
input head at native position `p + 1` (on the `p`-th input symbol) and a delimited binary counter
word `w` of value `d` on tape `j` from its head (little-endian, blanks at both ends, the
convention of `Turing.counterLoopTM`), it copies the window `y = (z.drop p).take d` (the next
`d` input symbols, fewer if the input ends) onto tape `dst` from that tape's head. It reaches
`done` within `C·(|y| + 1) + 2|w|` steps, and not before, with the input head just after the
window, the head of `dst` just after the copy, the counter head back at its start, the counter
word replaced by some word of the same width, and every other tape, head and the output
unchanged. No `|z|` term. (A leaf row of the construction layer; [AB09, §1.2].)

**Proof sketch.** `Turing.counterLoopTM` over a one-step body on the native input and tape
`dst`: at an input symbol, write it on `dst` and move both heads right, returning to the body's
anchor; at the input's right end, escape. Each round costs a fixed number of steps; the round
count is `|y|`, or `|y| + 1` when the input ends first. The counter ledger has two cases. On
exhaustion (`|y| = d`), the whole counter overhead of the `d + 1` decrements, the final
underflow included, is at most `4d + 2|w| + 2` (`Turing.counterOverhead_le`, used once). On
early input end (`|y| < d`), the loop escapes in round `r = |y| + 1 ≤ d`, after `r`
decrements, which cost at most `4r + 2|w|` (`Turing.counterOverhead_le_of_le`). Either way the
total is at most `C·(|y| + 1) + 2|w|`. The exit-time and endpoint clauses are those of
`Turing.counterLoopTM_run_done` and `Turing.counterLoopTM_run_escape`. -/
theorem exists_inputWindowCopyTM (k : ℕ) (j dst : Fin k) (hjd : j ≠ dst) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (W : MultiTapeTM k Bool Q)
      (entry done : Q) (C : ℕ),
      ∀ {z : List Bool} (d : Cfg k Bool Q z) (p : ℕ) (w : List Bool),
        d.state = some entry → d.inputPos.val = p + 1 →
        (∀ q : ℤ, -1 ≤ q → q ≤ (w.length : ℤ) →
          d.workTapes j (d.workTapePos j + q) = FinTM.bufferTape w q) →
        let y := (z.drop p).take (Nat.ofDigits 2 (w.map Bool.toNat))
        ∃ T ≤ C * (y.length + 1) + 2 * w.length, ∃ w' : List Bool, w'.length = w.length ∧
          (W.runFrom d T).state = some done ∧
          (W.runFrom d T).inputPos.val = p + 1 + y.length ∧
          (W.runFrom d T).workTapes =
            Function.update (Function.update d.workTapes dst (fun q =>
              if d.workTapePos dst ≤ q ∧ q < d.workTapePos dst + (y.length : ℤ) then
                FinTM.bufferTape y (q - d.workTapePos dst)
              else d.workTapes dst q)) j (fun q =>
              if d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ) then
                FinTM.bufferTape w' (q - d.workTapePos j)
              else d.workTapes j q) ∧
          (W.runFrom d T).workTapePos =
            Function.update d.workTapePos dst (d.workTapePos dst + (y.length : ℤ)) ∧
          (W.runFrom d T).output = d.output ∧
          ∀ u < T, (W.runFrom d u).state ≠ some done := by
  let ι := iw_select j dst hjd
  refine ⟨CounterLoopState Bool, inferInstance, inferInstance,
    embedEmitTM ι iw_machine, .dec .run, .done, 6, ?_⟩
  intro z c p w hc hi hw
  let body : Cfg 1 Bool Bool z :=
    ⟨some false, c.inputPos, fun _ => c.workTapes dst,
      fun _ => c.workTapePos dst, c.output⟩
  let y := (z.drop p).take (Nat.ofDigits 2 (w.map Bool.toNat))
  have hp : p ≤ z.length := by have := c.inputPos.isLt; omega
  have hn : y.length = min (Nat.ofDigits 2 (w.map Bool.toNat)) (z.length - p) := by
    simp only [y, List.length_take, List.length_drop]
  have hbound : p + y.length ≤ z.length := by
    have := Nat.min_le_right (Nat.ofDigits 2 (w.map Bool.toNat)) (z.length - p)
    omega
  have htake : (z.drop p).take y.length = y := by
    simpa only [y, List.length_take] using
      (List.take_eq_take_min (l := z.drop p) (i := Nat.ofDigits 2 (w.map Bool.toNat))).symm
  obtain ⟨T, hT, v, hv, hrun, hfirst⟩ :=
    iw_local body p rfl hi hp w (c.workTapes j) (c.workTapePos j) hw y.length hn
  let start := counterLoopCfg (some (.dec .run)) body (c.workTapes j) (c.workTapePos j)
  let finish := counterLoopCfg (some .done) (iw_prefix body p y.length hbound)
    (iw_patch (c.workTapes j) (c.workTapePos j) v) (c.workTapePos j)
  let out : Cfg k Bool (CounterLoopState Bool) z :=
    ⟨some .done, (iw_prefix body p y.length hbound).inputPos,
      Function.update (Function.update c.workTapes dst
        (iw_patch (c.workTapes dst) (c.workTapePos dst) y)) j
        (iw_patch (c.workTapes j) (c.workTapePos j) v),
      Function.update c.workTapePos dst (c.workTapePos dst + (y.length : ℤ)), c.output⟩
  have hstart : embedEmitCfg ι c.workTapes c.workTapePos [] start = c := by
    apply embedEmitCfg_eq
    · simpa only [start, counter_cfg_eq] using hc.symm
    · simp only [start, counter_cfg_eq, body]
    · simp only [start, counter_cfg_eq, body, List.nil_append]
    · intro i
      fin_cases i <;> simp [start, counter_cfg_eq, body, ι, iw_select] <;> exact ⟨rfl, rfl⟩
    · intro i _
      exact ⟨rfl, rfl⟩
  have hend : embedEmitCfg ι c.workTapes c.workTapePos [] finish = out := by
    apply embedEmitCfg_eq
    · simp only [finish, counter_cfg_eq, out]
    · simp only [finish, counter_cfg_eq, out]
    · simp only [finish, counter_cfg_eq, iw_prefix, body, out, List.nil_append]
    · intro i
      fin_cases i <;>
        simp [finish, counter_cfg_eq, out, iw_prefix, body, ι, iw_select, htake, hjd,
          Ne.symm hjd] <;> exact ⟨rfl, rfl⟩
    · intro i hnone
      have hd : i ≠ dst := by
        intro he
        apply hnone
        exact ⟨0, by simp [ι, iw_select, he]⟩
      have hj : i ≠ j := by
        intro he
        apply hnone
        exact ⟨1, by simp [ι, iw_select, he]⟩
      simp [out, hd, hj]
  have hlift (u : ℕ) : (embedEmitTM ι iw_machine).runFrom c u =
      embedEmitCfg ι c.workTapes c.workTapePos [] (iw_machine.runFrom start u) := by
    calc
      _ = (embedEmitTM ι iw_machine).runFrom
          (embedEmitCfg ι c.workTapes c.workTapePos [] start) u :=
        congrArg (fun d => (embedEmitTM ι iw_machine).runFrom d u) hstart.symm
      _ = _ := embedEmitTM_runFrom ι iw_machine c.workTapes c.workTapePos [] start u
  have he : (embedEmitTM ι iw_machine).runFrom c T = out := by
    rw [hlift T, hrun]
    exact hend
  refine ⟨T, hT, v, hv, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [he, out]
  · simp only [he, out, iw_prefix, y]
  · rw [he, ← hv]
    rfl
  · simp only [he, out, y]
  · simp only [he, out]
  · intro u hu
    rw [hlift u, embedEmitCfg_state]
    exact hfirst u hu

end Turing
