/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.StepBlock
import TCSlib.Complexity.TuringMachine.Build.Contract.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The step block's forwarding round loop (H2-F)

**Status: statement gate passed** (2026-10-15, `audits/u2-statements-findings.md`: PASS,
0 blockers, 0 majors, 2 minors; resolutions `audits/u2-statements-resolutions.md`). The contract
`Turing.StepBlock.exists_forwardLoopTM` is sorried with its proof sketch; the encoding is defined.

**H2's unclocked loop form** (host H2, `machine-library-design.md` §14): the step block
`Turing.StepBlock.roundTM` followed by a forwarding leaf, run until the simulated machine halts.
One finite machine per work-tape count `k` simulates any `k`-work-tape binary transition table,
held as data in the `Turing.tableBitsK` layout, in macro-step lockstep (`Turing.Lockstep`) through
the encoding `Turing.StepBlock.forwardLoopCfg`, forwarding each simulated emission to its own
output, with a per-step cost bounded by the table's length and a per-head space ledger. It is the
loop of the `k`-generic universal machine U2 (`TCSlib.Complexity.TuringMachine.UniversalK`;
design note `audits/evidence/u2/U2-design.md` §2.2), and of B6's `U₀` at `k = 1`.

H2's clocked loop form, the counter loop over the step block, is
`TCSlib.Complexity.TuringMachine.Build.StepBlockLoop`. The forwarding form has its own module
(user, 2026-10-15) so that the clocked form's consumers, `CodeSimulator` among them, do not depend
on it.

## Main definitions

* `Turing.StepBlock.forwardLoopCfg` — H2-F's encoding of a source configuration.

## Main results

* `Turing.StepBlock.exists_forwardLoopTM` — H2-F, the forwarding round loop: a macro-step
  lockstep of any `k`-tape table with its emissions forwarded, per-step cost
  `≤ 50 · (|table| + 1) + C`, and the space ledger (sorried).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4.1, proof of Theorem 1.9.)
-/

namespace Turing

namespace StepBlock

/-! ## The forwarding round loop (H2-F) -/

/-- **The forwarding round loop's configuration for a source configuration** (H2-F's encoding):
for a `k`-work-tape binary machine `M` with `n + 1` states and a configuration `c` of `M` on the
input `x`, the `(k + 2)`-tape configuration whose input head and mirrored tapes `0, …, k - 1`
(contents and heads) are `c`'s, whose tape `k` holds the table `tableBitsK M.tr` and tape
`k + 1` the blank summary cell followed by the unary current state (empty when `c` is halted),
both auxiliary heads at `0`, whose output is `c`'s output, and whose control is `entry` while
`c` is live and halted once `c` is. It is the step block's seam relation `Turing.StepBlock.Rep`
for `c` with its output erased (so the summary cell is blank), with the physical output
restored: the reset invariant of `Turing.exists_selfUniversal`'s sketch (the H2-S gate's
finding 4). [AB09, §1.4.1, proof of Theorem 1.9] -/
def forwardLoopCfg {k n : ℕ} {Q : Type} {x : List Bool} (entry : Q)
    (M : MultiTapeTM k Bool (Fin (n + 1))) (c : Cfg k Bool (Fin (n + 1)) x) :
    Cfg (k + 2) Bool Q x where
  state := c.state.map fun _ => entry
  inputPos := c.inputPos
  workTapes := Fin.addCases (motive := fun _ => ℤ → Option Bool) c.workTapes fun j =>
    if j = 0 then FinTM.bufferTape (tableBitsK M.tr)
    else summaryCells none ((c.state.map unaryFin).getD [])
  workTapePos := Fin.addCases (motive := fun _ => ℤ) c.workTapePos fun _ => 0
  output := c.output

/-- Erasing only the simulated output gives the block's reset invariant; the physical
output prefix of the forwarding configuration is retained. -/
private lemma fl_reset {k n : ℕ} {x : List Bool}
    (M : MultiTapeTM k Bool (Fin (n + 1))) (c : Cfg k Bool (Fin (n + 1)) x) :
    Rep M.tr {c with output := []} (forwardLoopCfg (exit k true) M c) := by
  simp [Rep, forwardLoopCfg, tableTape, summaryTape, outputSummary]

/-- The data change of a forwarding leaf: clear the scanned summary cell and append its
optional bit to the physical output, with the supplied successor control. -/
private def fl_flush {k : ℕ} {S Q : Type} {x : List Bool} (next : Option Q)
    (d : Cfg (k + 2) Bool S x) : Cfg (k + 2) Bool Q x where
  state := next
  inputPos := d.inputPos
  workTapes := Function.update d.workTapes (summaryTape k)
    (Function.update (d.workTapes (summaryTape k)) (d.workTapePos (summaryTape k)) none)
  workTapePos := d.workTapePos
  output := d.output ++ (d.workTapeSymbols (summaryTape k)).toList

/-- The forwarding leaf. `some live` reads, emits and clears; `none` is the live return
anchor. There is no public row for this atomic emission and clearing: the step block and
its clocked loop are silent, and `tapeAction` itself emits nothing. The leaf changes only
that action's emission and successor fields and moves no head. -/
private def fl_leafTM (k : ℕ) : MultiTapeTM (k + 2) Bool (Option Bool) where
  q₀ := some true
  tr q _ w := match q with
    | some live => { tapeAction (summaryTape k) 0 (some none) 0 (none : Option Bool) with
        output := w (summaryTape k)
        state := if live then some none else none }
    | none => inputMoveAction 0 none

/-- The leaf's single step has exactly the clearing and emission effect, including when
it halts. All input and work heads keep their positions.

**Proof sketch.** Apply the one-tape action with its emission and successor fields replaced.
Only the selected work tape is written; its head displacement and every other displacement
are zero. -/
private lemma fl_leaf_step {k : ℕ} {x : List Bool} (d : Cfg (k + 2) Bool (Option Bool) x)
    (live : Bool) (hd : d.state = some (some live)) :
    (fl_leafTM k).step d = fl_flush (if live then some none else none) d := by
  simp only [MultiTapeTM.step, hd, fl_leafTM]
  apply Cfg.ext
  · rfl
  · simp [Action.apply, tapeAction, fl_flush]
  · funext j
    by_cases hj : j = summaryTape k <;> simp [Action.apply, tapeAction, fl_flush, hj]
  · funext j
    by_cases hj : j = summaryTape k <;> simp [Action.apply, tapeAction, fl_flush, hj]
  · rfl

/-- A full leaf run takes one step. -/
private lemma fl_leaf_run {k : ℕ} {x : List Bool} (d : Cfg (k + 2) Bool (Option Bool) x)
    (live : Bool) (hd : d.state = some (some live)) :
    (fl_leafTM k).runFrom d 1 = fl_flush (if live then some none else none) d :=
  fl_leaf_step d live hd

/-- Relabelling the forwarding configuration changes only its designated live control. -/
private lemma fl_encode_map {k n : ℕ} {Q R : Type} {x : List Bool} (entry : Q)
    (f : Q → R) (M : MultiTapeTM k Bool (Fin (n + 1)))
    (c : Cfg k Bool (Fin (n + 1)) x) :
    (forwardLoopCfg entry M c).mapState f = forwardLoopCfg (f entry) M c := by
  apply Cfg.ext <;> simp [forwardLoopCfg, Cfg.mapState, Option.map_map, Function.comp_def]

/-- Releasing the block and forwarding its summary are the two phases. -/
private def fl_Ph (k : ℕ) : Bool → Type
  | false => Unit ⊕ (Σ key, Ph k key)
  | true => Option Bool

private instance fl_fintype (k : ℕ) (b : Bool) : Fintype (fl_Ph k b) := by
  cases b <;> dsimp [fl_Ph] <;> infer_instance

private instance fl_decidableEq (k : ℕ) (b : Bool) : DecidableEq (fl_Ph k b) := by
  cases b <;> dsimp [fl_Ph] <;> infer_instance

/-- Each invocation starts at the release adapter's fresh control. -/
private def fl_entry (k : ℕ) : Σ b, fl_Ph k b := ⟨false, Sum.inl ()⟩

/-- The two machines supplied to the existing phase host. -/
private def fl_part (k : ℕ) : (b : Bool) → MultiTapeTM (k + 2) Bool (fl_Ph k b)
  | false => seamReleaseTM (roundTM k) (exit k true)
  | true => fl_leafTM k

/-- Only returned block exits and the leaf's live return anchor dispatch. In particular,
the release adapter's fresh state is never redirected. -/
private def fl_red (k : ℕ) : (b : Bool) → fl_Ph k b → Option (Σ b, fl_Ph k b)
  | false, Sum.inl _ => none
  | false, Sum.inr s =>
    if s = exit k true then some ⟨true, some true⟩
    else if s = exit k false then some ⟨true, some false⟩ else none
  | true, some _ => none
  | true, none => some (fl_entry k)

/-- The forwarding machine uses exactly one public phase host over the released block and
its forwarding leaf. Its finite control depends only on the tape count. -/
private def fl_TM (k : ℕ) : MultiTapeTM (k + 2) Bool (Σ b, fl_Ph k b) :=
  phaseHostTM (fl_part k) (fl_entry k) (fl_red k)

/-- The released block runs unchanged until its positive exit and then dispatches to the
appropriate forwarding leaf.

**Proof sketch.** The release adapter agrees with the block at positive times. At time zero
its fresh control cannot dispatch; at interior positive times the block's strict cut excludes
both redirect states. Apply the public phase lemma to this guard. -/
private lemma fl_block_phase {k : ℕ} {x : List Bool}
    (d : Cfg (k + 2) Bool (Σ key, Ph k key) x) (T : ℕ) (live : Bool)
    (hd : d.state = some (exit k true)) (hT : 0 < T)
    (he : ((roundTM k).runFrom d T).state = some (exit k live))
    (hc : ∀ u, 0 < u → u < T → ∃ s, ((roundTM k).runFrom d u).state = some s ∧
      s ≠ exit k true ∧ s ≠ exit k false) :
    (∀ u ≤ T, (fl_TM k).runFrom (d.mapState fun _ => fl_entry k) u =
      ((fl_part k false).runFrom (d.mapState fun _ => Sum.inl ()) u).mapState
        (Sigma.mk false)) ∧
    (fl_TM k).runFrom (d.mapState fun _ => fl_entry k) (T + 1) =
      ((roundTM k).runFrom d T).mapState (fun _ => ⟨true, some live⟩) := by
  have released := seamReleaseTM_runFrom_pos (roundTM k) (exit k true) d hd T hT
  have dispatched := phaseHostTM_run (fl_part k) (fl_entry k) (fl_red k) false
    (d.mapState fun _ => Sum.inl ()) (((roundTM k).runFrom d T).mapState Sum.inr)
    T released (Sum.inr (exit k live))
    (by simp [Cfg.mapState, he]) ⟨true, some live⟩
    (by cases live <;> simp [fl_red, exit]) (by
      intro u hu s hs
      by_cases hz : u = 0
      · subst u
        simp only [MultiTapeTM.runFrom_zero, Cfg.mapState, hd, Option.map_some,
          Option.some.injEq] at hs
        subst s
        rfl
      · have hp : 0 < u := Nat.pos_of_ne_zero hz
        change ((seamReleaseTM (roundTM k) (exit k true)).runFrom _ u).state = _ at hs
        rw [seamReleaseTM_runFrom_pos (roundTM k) (exit k true) d hd u hp] at hs
        obtain ⟨r, hr, hn, hh⟩ := hc u hp hu
        simp only [Cfg.mapState, hr, Option.map_some, Option.some.injEq] at hs
        subst s
        simp [fl_red, hn, hh])
  simpa only [fl_TM, Cfg.mapState, Option.map_map, Function.comp_def] using dispatched

/-- The leaf keeps its one-step effect inside the public phase host. -/
private lemma fl_hosted_leaf {k : ℕ} {S : Type} {x : List Bool}
    (d : Cfg (k + 2) Bool S x) (live : Bool) (hd : d.state ≠ none) :
    (fl_TM k).step (d.mapState fun _ => ⟨true, some live⟩) =
      fl_flush (if live then some ⟨true, none⟩ else none) d := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hd
  have lifted : (fl_TM k).step (d.mapState fun _ => ⟨true, some live⟩) =
      ((fl_leafTM k).step (d.mapState fun _ => some live)).mapState (Sigma.mk true) := by
    simp only [MultiTapeTM.step, Cfg.mapState, hq, Option.map_some]
    rfl
  rw [lifted, fl_leaf_step _ live (by simp [Cfg.mapState, hq])]
  cases live <;> rfl

/-- The live leaf's return anchor dispatches without moving a head or changing data. -/
private lemma fl_return {k : ℕ} {S : Type} {x : List Bool} (d : Cfg (k + 2) Bool S x) :
    (fl_TM k).step (fl_flush (some ⟨true, none⟩) d) =
      fl_flush (some (fl_entry k)) d := by
  rw [step_of_inputMoveAction (fl_TM k) _ 0 rfl (by rfl)]
  simp only [fl_flush, moveInputPos_zero]

/-- Clearing a represented summary recovers the forwarding encoding, with exactly the
physical prefix and the one summary emission in its output.

**Proof sketch.** The mirrored bank and table are unchanged. At the summary head, which is
home, `summaryCells_update` removes only cell zero. The state word is already the word of
the represented source, even at a halt. -/
private lemma fl_restore {k n : ℕ} {Q : Type} {x : List Bool} (entry : Q)
    (M : MultiTapeTM k Bool (Fin (n + 1))) (c : Cfg k Bool (Fin (n + 1)) x)
    (d : Cfg (k + 2) Bool (Σ key, Ph k key) x) (hr : Rep M.tr c d) :
    fl_flush (c.state.map fun _ => entry) d =
      forwardLoopCfg entry M {c with output := d.output ++ (outputSummary c.output).toList} := by
  obtain ⟨hin, hbank, htable, hsummary, ht, hs⟩ := hr
  have read : d.workTapeSymbols (summaryTape k) = outputSummary c.output := by
    simp only [Cfg.workTapeSymbols, hs, hsummary, summaryCells, ↓reduceIte]
  apply Cfg.ext
  · rfl
  · exact hin
  · funext j
    induction j using Fin.addCases with
    | left i =>
      have hne : Fin.castAdd 2 i ≠ summaryTape k := by
        intro he
        have hv := congrArg Fin.val he
        change i.val = k + 1 at hv
        have hi := i.isLt
        omega
      simpa only [fl_flush, forwardLoopCfg, Fin.addCases_left,
        Function.update_of_ne hne] using (hbank i).1
    | right j =>
      fin_cases j
      · have hne : tableTape k ≠ summaryTape k := by
          simp [tableTape, summaryTape, Fin.ext_iff]
        change Function.update d.workTapes (summaryTape k) _ (tableTape k) = _
        rw [Function.update_of_ne hne, htable]
        simp [forwardLoopCfg]
      · change Function.update d.workTapes (summaryTape k) _ (summaryTape k) = _
        rw [Function.update_self, hs, hsummary, summaryCells_update]
        simp [forwardLoopCfg]
  · funext j
    induction j using Fin.addCases with
    | left i =>
      simpa only [fl_flush, forwardLoopCfg, Fin.addCases_left] using (hbank i).2
    | right j =>
      fin_cases j
      · simpa only [fl_flush, forwardLoopCfg, Fin.addCases_right] using ht
      · simpa only [fl_flush, forwardLoopCfg, Fin.addCases_right] using hs
  · simp only [fl_flush, forwardLoopCfg, read]

/-- One released block followed by its leaf returns or halts with the summary forwarded,
never halts early, and visits no work-head position beyond the block's visited sets.

**Proof sketch.** The phase lemma supplies the block prefix and its one-step dispatch.
The leaf takes one stationary step; a live leaf takes one more stationary dispatch. Split
interior and visiting times at the block exit; all later head positions are its final ones.
This composes the public hosts and does not iterate rounds. -/
private lemma fl_round {k : ℕ} {x : List Bool}
    (d : Cfg (k + 2) Bool (Σ key, Ph k key) x) (T : ℕ) (live : Bool)
    (hd : d.state = some (exit k true)) (hT : 0 < T)
    (he : ((roundTM k).runFrom d T).state = some (exit k live))
    (hc : ∀ u, 0 < u → u < T → ∃ s, ((roundTM k).runFrom d u).state = some s ∧
      s ≠ exit k true ∧ s ≠ exit k false) :
    (fl_TM k).runFrom (d.mapState fun _ => fl_entry k) (T + if live then 3 else 2) =
        fl_flush (if live then some (fl_entry k) else none) ((roundTM k).runFrom d T) ∧
    (∀ u < T + if live then 3 else 2,
      ((fl_TM k).runFrom (d.mapState fun _ => fl_entry k) u).state ≠ none) ∧
    ∀ j, (fl_TM k).visitedByTapeHead (d.mapState fun _ => fl_entry k)
        (T + if live then 3 else 2) j ⊆ (roundTM k).visitedByTapeHead d T j := by
  obtain ⟨hprefix, dispatch⟩ := fl_block_phase d T live hd hT he hc
  have emitted : (fl_TM k).runFrom (d.mapState fun _ => fl_entry k) (T + 2) =
      fl_flush (if live then some ⟨true, none⟩ else none) ((roundTM k).runFrom d T) := by
    rw [show T + 2 = (T + 1) + 1 by omega, MultiTapeTM.runFrom_succ_eq_step', dispatch,
      fl_hosted_leaf _ live (by rw [he]; exact Option.some_ne_none _)]
  have finish : (fl_TM k).runFrom (d.mapState fun _ => fl_entry k)
      (T + if live then 3 else 2) =
      fl_flush (if live then some (fl_entry k) else none) ((roundTM k).runFrom d T) := by
    cases live
    · exact emitted
    · change (fl_TM k).runFrom _ (T + 3) = _
      rw [show T + 3 = (T + 2) + 1 by omega, MultiTapeTM.runFrom_succ_eq_step', emitted]
      exact fl_return _
  refine ⟨finish, ?_, ?_⟩
  · intro u hu
    by_cases hb : u ≤ T
    · rw [hprefix u hb]
      by_cases hz : u = 0
      · simp [hz, Cfg.mapState, hd]
      · change (((seamReleaseTM (roundTM k) (exit k true)).runFrom _ u).mapState _).state ≠ _
        rw [seamReleaseTM_runFrom_pos (roundTM k) (exit k true) d hd u
          (Nat.pos_of_ne_zero hz)]
        by_cases hend : u = T
        · simp [hend, Cfg.mapState, he]
        · obtain ⟨s, hs, _, _⟩ := hc u (Nat.pos_of_ne_zero hz) (by omega)
          simp [Cfg.mapState, hs]
    · have ht : u = T + 1 ∨ (live = true ∧ u = T + 2) := by
        cases live <;> simp at hu ⊢ <;> omega
      rcases ht with rfl | ⟨rfl, rfl⟩
      · rw [dispatch]
        simp [Cfg.mapState, he]
      · rw [emitted]
        simp [fl_flush]
  · intro j p hp
    obtain ⟨u, hu, hpos⟩ := Finset.mem_image.mp hp
    have hu' : u ≤ T + if live then 3 else 2 := by
      simpa only [Finset.mem_range, Nat.lt_succ_iff] using hu
    have heads : ((fl_TM k).runFrom (d.mapState fun _ => fl_entry k) u).workTapePos j =
        ((roundTM k).runFrom d (min u T)).workTapePos j := by
      by_cases hb : u ≤ T
      · rw [min_eq_left hb, hprefix u hb]
        by_cases hz : u = 0
        · simp [hz, Cfg.mapState]
        · rw [show (fl_part k false) = seamReleaseTM (roundTM k) (exit k true) from rfl,
            seamReleaseTM_runFrom_pos (roundTM k) (exit k true) d hd u
              (Nat.pos_of_ne_zero hz)]
          rfl
      · rw [min_eq_right (by omega)]
        have ht : u = T + 1 ∨ u = T + 2 ∨ (live = true ∧ u = T + 3) := by
          cases live <;> simp at hu' ⊢ <;> omega
        rcases ht with rfl | rfl | ⟨rfl, rfl⟩
        · rw [dispatch]; rfl
        · rw [emitted]; rfl
        · rw [show T + 3 = T + if true then 3 else 2 from rfl, finish]; rfl
    apply Finset.mem_image.mpr
    refine ⟨min u T, Finset.mem_range.mpr (by omega), ?_⟩
    exact heads.symm.trans hpos

/-- A live source step has a positive bounded forwarding simulation, its exact successor,
a strict live interior, and the mirrored and auxiliary visited-set bounds.

**Proof sketch.** Apply the block's visited-set contract to the source with erased output,
using the reset invariant but retaining the physical output. Compose its exit with the leaf.
The summary is the single current emission; restoring the blank summary therefore gives
exactly the actual successor, including its original output prefix. -/
private lemma fl_step_exists {k n : ℕ} {x : List Bool}
    (M : MultiTapeTM k Bool (Fin (n + 1))) (c : Cfg k Bool (Fin (n + 1)) x)
    (hl : c.state ≠ none) :
    ∃ t, 0 < t ∧ t ≤ 50 * ((tableBitsK M.tr).length + 1) + 3 ∧
      (fl_TM k).runFrom (forwardLoopCfg (fl_entry k) M c) t =
        forwardLoopCfg (fl_entry k) M (M.step c) ∧
      (∀ u < t, ((fl_TM k).runFrom (forwardLoopCfg (fl_entry k) M c) u).state ≠ none) ∧
      (∀ i : Fin k, (fl_TM k).visitedByTapeHead (forwardLoopCfg (fl_entry k) M c) t
        (Fin.castAdd 2 i) ⊆ {c.workTapePos i, (M.step c).workTapePos i}) ∧
      ∀ j : Fin (k + 2), k ≤ j.val →
        (fl_TM k).visitedByTapeHead (forwardLoopCfg (fl_entry k) M c) t j ⊆
          Finset.Icc (-((50 * ((tableBitsK M.tr).length + 1) + 3 : ℕ) : ℤ))
            ((50 * ((tableBitsK M.tr).length + 1) + 3 : ℕ) : ℤ) := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hl
  let a := M.tr q c.inputSymbol c.workTapeSymbols
  let d := forwardLoopCfg (exit k true) M c
  have hd : d.state = some (exit k true) := by simp [d, forwardLoopCfg, hq]
  obtain ⟨T, hpos, hbound, he, hr, hc, ho, hm, ha⟩ :=
    roundTM_visited M.tr {c with output := []} q hq d hd (fl_reset M c)
  have joined := fl_round d T a.state.isSome hd hpos he hc
  have start : d.mapState (fun _ => fl_entry k) = forwardLoopCfg (fl_entry k) M c :=
    fl_encode_map (exit k true) (fun _ => fl_entry k) M c
  rw [start] at joined
  have emission : outputSummary (a.apply {c with output := []}).output = a.output := by
    simpa only [Action.apply, outputSummary, summaryEmit_none] using
      outputSummary_append [] a.output
  have out : ((roundTM k).runFrom d T).output = c.output := ho T le_rfl
  have source :
      {a.apply {c with output := []} with
        output := ((roundTM k).runFrom d T).output ++
          (outputSummary (a.apply {c with output := []}).output).toList} = M.step c := by
    rw [emission, out]
    simp only [MultiTapeTM.step, hq]
    rfl
  have control : (a.apply {c with output := []}).state.map (fun _ => fl_entry k) =
      if a.state.isSome then some (fl_entry k) else none := by
    cases hs : a.state <;> simp [Action.apply, hs]
  have restored := fl_restore (fl_entry k) M (a.apply {c with output := []})
    ((roundTM k).runFrom d T) hr
  rw [source, control] at restored
  refine ⟨T + if a.state.isSome then 3 else 2, ?_, ?_, joined.1.trans restored,
    joined.2.1, ?_, ?_⟩
  · split <;> omega
  · split <;> omega
  · intro i p hp
    have h := hm i (joined.2.2 (Fin.castAdd 2 i) hp)
    simpa only [MultiTapeTM.step, hq, Action.apply] using h
  · intro j hj p hp
    have h := ha j hj (joined.2.2 j hp)
    simp only [Finset.mem_Icc] at h ⊢
    push_cast
    omega

/-- Both auxiliary heads of every encoding are home, including for halted sources and
zero work tapes. -/
private lemma fl_home {k n : ℕ} {Q : Type} {x : List Bool} (entry : Q)
    (M : MultiTapeTM k Bool (Fin (n + 1))) (c : Cfg k Bool (Fin (n + 1)) x)
    (j : Fin (k + 2)) (hj : k ≤ j.val) : (forwardLoopCfg entry M c).workTapePos j = 0 := by
  induction j using Fin.addCases with
  | left i => have hi := i.isLt; simp only [Fin.coe_castAdd] at hj; omega
  | right j => simp only [forwardLoopCfg, Fin.addCases_right]

/-- **H2-F, the forwarding round loop** (host H2's unclocked loop form; `machine-library-design.md`
§14; U2 design note `audits/evidence/u2/U2-design.md` §2.2). For each work-tape count `k` there
is one finite `(k + 2)`-tape binary machine `L`, with an entry state and a constant `C`, such
that for every `k`-work-tape binary machine `M` with `n + 1` states and every input `x`, `L`
simulates `M` step by step through `forwardLoopCfg`: there is a cost function on `M`'s
configurations with
* **a macro-step lockstep** (`Turing.Lockstep`, exits `{none}` on both sides): from the encoding
  of a live configuration `c`, `L` reaches the encoding of `M.step c` after exactly `cost c`
  steps, without halting before; the encoding of a halted configuration is halted. So `L` halts
  exactly when `M` does, with `M`'s output, which it emits step by step
  (`Turing.Lockstep.runFrom`, `Turing.Lockstep.cut`);
* **a per-step bound**: `0 < cost c ≤ 50 · (|tableBitsK M.tr| + 1) + C` for live `c`, a constant
  for a fixed table (the step block's bound plus the leaf's);
* **a space ledger**: over `t` source steps that are live before `t`, each mirrored head visits
  only cells that `M`'s head visits, and the two auxiliary heads stay within
  `50 · (|tableBitsK M.tr| + 1) + C` of their home.

The control of `L` does not depend on `M`, `n` or `x`. [AB09, §1.4.1, proof of Theorem 1.9:
each step of `M` is simulated in a number of steps depending only on `M`'s table]

**Proof sketch.** `L` is the step block `roundTM k` followed, at either of its exits, by a
forwarding leaf on the summary tape: read the summary cell, emit its bit if it holds one, blank
it, then return to the block's entry (exit `entry`) or halt (exit `halt`). For a live `c`, the
block-control part of `forwardLoopCfg entry M c` represents `{c with output := []}` (`Rep`: a blank
summary, the unary state word, both auxiliary heads home), so `roundTM_effect` gives a first exit
after `T ≤ 50 · (|tableBitsK M.tr| + 1)` steps at the representation of
`a.apply {c with output := []}`, silent before, with summary cell
`summaryEmit none a.output = a.output` (`summaryEmit_none`); the exit time is unique
(`roundTM_firstExit_unique`). The leaf emits `a.output`, making the physical output
`(a.apply c).output`, blanks the cell, and enters `entry` or halts according to the exit: the
result is exactly `forwardLoopCfg entry M (M.step c)`. Take `cost c` the block's exit time plus the
leaf's length (at most `C`); the inner times are live by the block's cut and the leaf's. The space
ledger is `roundTM_visited` per round, summed by `MultiTapeTM.visitedByTapeHead_add_subset`; the
leaf moves no head.

**Fill appendix (H2-F).** The two phases are the released block and the forwarding leaf;
`fl_round` proves their composition from the public phase lemma and the block's cut. The
leaf alone emits and clears, and all its heads are stationary. One exit-time witness is chosen
once per live source configuration, together with all its run and visited-set properties.
The cost is that block time plus three for a live successor, or plus two for a halt, so
`C = 3`. `Lockstep.runFrom` supplies iteration; the mirrored ledger uses visited-set addition,
and the auxiliary ledger uses `Lockstep.locate`. -/
theorem exists_forwardLoopTM (k : ℕ) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (L : MultiTapeTM (k + 2) Bool Q)
      (entry : Q) (C : ℕ),
      ∀ {n : ℕ} {x : List Bool} (M : MultiTapeTM k Bool (Fin (n + 1))),
        ∃ cost : Cfg k Bool (Fin (n + 1)) x → ℕ,
          Lockstep M L (forwardLoopCfg entry M) cost {none} {none} ∧
          (∀ c, c.state ≠ none → 0 < cost c ∧
            cost c ≤ 50 * ((tableBitsK M.tr).length + 1) + C) ∧
          ∀ (c : Cfg k Bool (Fin (n + 1)) x) (t : ℕ), (∀ u < t, (M.runFrom c u).state ≠ none) →
            (∀ i : Fin k, L.visitedByTapeHead (forwardLoopCfg entry M c)
                (∑ u ∈ Finset.range t, cost (M.runFrom c u)) (Fin.castAdd 2 i) ⊆
              M.visitedByTapeHead c t i) ∧
            ∀ j : Fin (k + 2), k ≤ j.val →
              L.visitedByTapeHead (forwardLoopCfg entry M c)
                  (∑ u ∈ Finset.range t, cost (M.runFrom c u)) j ⊆
                Finset.Icc (-((50 * ((tableBitsK M.tr).length + 1) + C : ℕ) : ℤ))
                  ((50 * ((tableBitsK M.tr).length + 1) + C : ℕ) : ℤ) := by
  classical
  refine ⟨(Σ b, fl_Ph k b), inferInstance, inferInstance, fl_TM k, fl_entry k, 3, ?_⟩
  intro n x M
  let cost (c : Cfg k Bool (Fin (n + 1)) x) : ℕ :=
    if h : c.state ≠ none then (fl_step_exists M c h).choose else 1
  have chosen (c : Cfg k Bool (Fin (n + 1)) x) (h : c.state ≠ none) :
      cost c = (fl_step_exists M c h).choose := dif_pos h
  have one (c : Cfg k Bool (Fin (n + 1)) x) (h : c.state ≠ none) :=
    (fl_step_exists M c h).choose_spec
  have lock : Lockstep M (fl_TM k) (forwardLoopCfg (fl_entry k) M) cost {none} {none} := by
    constructor
    · intro c h
      have alive : c.state ≠ none := by simpa only [Set.mem_singleton_iff] using h
      rw [chosen c alive]
      exact (one c alive).2.2.1
    · intro c h
      simp only [Set.mem_singleton_iff] at h ⊢
      simp [forwardLoopCfg, h]
    · intro c h u hu
      have alive : c.state ≠ none := by simpa only [Set.mem_singleton_iff] using h
      rw [chosen c alive] at hu
      exact (one c alive).2.2.2.1 u hu
  refine ⟨cost, lock, ?_, ?_⟩
  · intro c h
    rw [chosen c h]
    exact ⟨(one c h).1, (one c h).2.1⟩
  · intro c t ht
    constructor
    · -- Split visited sets at each completed round; the lockstep supplies its start.
      induction t with
      | zero => simp [MultiTapeTM.visitedByTapeHead, forwardLoopCfg]
      | succ t ih =>
        have ht' : ∀ u < t, (M.runFrom c u).state ≠ none := fun u hu => ht u (by omega)
        have alive := ht t (by omega)
        have atRound := lock.runFrom c t ht'
        intro i p hp
        rw [Finset.sum_range_succ] at hp
        have split := MultiTapeTM.visitedByTapeHead_add_subset (fl_TM k)
          (forwardLoopCfg (fl_entry k) M c)
          (∑ u ∈ Finset.range t, cost (M.runFrom c u)) (cost (M.runFrom c t))
          (Fin.castAdd 2 i) hp
        rcases Finset.mem_union.mp split with before | current
        · have old := ih ht' i before
          exact (Finset.image_subset_image (Finset.range_mono (Nat.le_succ (t + 1)))) old
        · rw [atRound, chosen (M.runFrom c t) alive] at current
          have h := (one (M.runFrom c t) alive).2.2.2.2.1 i current
          rcases Finset.mem_insert.mp h with rfl | hend
          · exact Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr (by omega), rfl⟩
          · have heq := Finset.mem_singleton.mp hend
            apply Finset.mem_image.mpr
            refine ⟨t + 1, Finset.mem_range.mpr (by omega), ?_⟩
            simpa only [MultiTapeTM.runFrom_succ_eq_step'] using heq.symm
    · -- Locate an auxiliary-head visit in one round, or at an encoded start.
      intro j hj p hp
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨u, _, w, hw, run⟩ := lock.locate c t ht v
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hv))
      rw [run]
      rcases hw with rfl | ⟨alive, hw⟩
      · rw [MultiTapeTM.runFrom_zero, fl_home (fl_entry k) M (M.runFrom c u) j hj]
        exact Finset.mem_Icc.mpr ⟨neg_nonpos.mpr (Nat.cast_nonneg _), Nat.cast_nonneg _⟩
      · rw [chosen (M.runFrom c u) alive] at hw
        exact (one (M.runFrom c u) alive).2.2.2.2.2 j hj
          (Finset.mem_image.mpr ⟨w, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hw), rfl⟩)

end StepBlock

end Turing
