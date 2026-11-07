/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.CounterLoop
import TCSlib.Complexity.TuringMachine.Build.Seam

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: modules on the native input (§12.8)

The two native-input modules of the §12.8 rich-alphabet design
(`machine-library-design.md` §12.8a §3): a call of a function-level machine
on the native input at a clean seam (R8.5e), and a seek of the input head to a
position held in binary on a work tape (R8.5b). Both are `Bool` modules; a
rich host runs them lifted along its digit embedding
(`Turing.MultiTapeTM.liftSymbols`), with unchanged time and space.

**Status: §12.8 fill C (status update; refreshed at the A–C fill gate, minor 4).** The
input seek is proved with its restoration, first-exit and workspace clauses. The clean input
call is proved; it cites stream B's `Turing.inputCopyTM_run_ofCfg`, now proved, and its
interface remains time-only.

## Main results

* `Turing.FinTM.exists_inputCallTM` — compute `f` on the native input from a
  blank seam and install the result on tape `0` (proved; the copier
  `inputCopyTM_run_ofCfg` is a proved dependency; status refreshed at the A–C fill gate).
* `Turing.exists_inputSeekTM` — move the input head to the binary value on a
  counter tape, restoring every work tape (proved; fill-C status update).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2: the read-only input tape, whose
  head a work-tape counter can position; the space-bounded simulations of
  §4.1 locate the input head of a simulated configuration this way.)
-/

namespace Turing.FinTM

/-- On a blank seam, the public native copier installs exactly the argument seam.
It cites stream B's framed input-copy contract, which is proved. -/
private theorem inputCall_copy (k : ℕ) (hk : 0 < k) (x : List Bool) :
    (inputCopyTM k ⟨0, hk⟩).runFrom (Cfg.ofWords (input := x) SweepPhase.sweep (fun _ => []))
        (2 * x.length + 2) = Cfg.ofWords SweepPhase.done (stateWord k x) := by
  rw [(inputCopyTM_run_ofCfg ⟨0, hk⟩ _ rfl rfl).1]
  apply Cfg.ext <;> try rfl
  funext j z
  simp only [Cfg.ofWords, stateWord]
  by_cases hj : j = ⟨0, hk⟩
  · subst j
    simp only [true_and, zero_add, sub_zero, bufferTape_nil, if_true]
    unfold bufferTape
    by_cases hzero : 0 ≤ z <;> by_cases hlen : z < (x.length : ℤ) <;> simp [hzero, hlen]
  · have hjval : (j : ℕ) ≠ 0 := fun hz => hj (Fin.ext hz)
    simp [hj, hjval]

/-- **R8.5e, the clean call on the native input** (design §12.8a §3). For any
witness `M` computing `f` within `T`, there is a callable module with entry and
exit states and a positive tape count with the following contract. From the
blank seam `Cfg.ofWords entry` (every tape empty, input head at `1`, empty
output) over the native input `x`, the module reaches, at its first positive
visit to `exit`, exactly the seam with `f x` installed on tape `0`, within
`c·(T |x| + |x| + |f x| + 1)` steps. It is the function-level contract run at a
seam that the next phase of a host can consume.

**Proof sketch.** Seam-compose (`Turing.seamCompTM_run_ofCfg`) the input
copier on tape `0` (`Turing.inputCopyTM_run_ofCfg`, `2|x| + 2` steps, which
from the blank seam yields `Cfg.ofWords` with `x` on tape `0`) with the install
call of `Turing.FinTM.exists_installCallTM` on the argument `x`, whose
coefficient absorbs the copy and the dispatch step. The first-return clause is
`Turing.seamCompTM_firstReturn_ofCfg`, which also needs the callee's exit
excluded at time `0`; the install call's contract excludes it only at positive
times. So split on whether its entry equals its exit. If it does, first wrap it
by `Turing.seamReleaseTM`, whose `Turing.seamReleaseTM_firstReturn` supplies a
fresh entry. The positive tape count is the install call's. -/
theorem exists_inputCallTM (M : FinTM Bool) (f : List Bool → List Bool)
    (T : ℕ → ℕ) (hM : M.ComputesFunInTime f T) :
    ∃ (C : FinTM Bool) (entry exit : C.State) (c : ℕ), 0 < C.k ∧
      ∀ x : List Bool,
        ∃ t ≤ c * (T x.length + x.length + (f x).length + 1),
          0 < t ∧
          (∀ t', 0 < t' → t' < t →
            (C.tm.runFrom (Cfg.ofWords (input := x) entry (fun _ => [])) t').state ≠
              some exit) ∧
          C.tm.runFrom (Cfg.ofWords (input := x) entry (fun _ => [])) t =
            Cfg.ofWords exit (stateWord C.k (f x)) := by
  obtain ⟨C₀, en₀, ex₀, b, hk₀, hC₀⟩ := exists_installCallTM M f T hM
  -- Supply the time-zero cut once, then use the same copier and seam in both cases.
  have hcallee : ∃ (C : FinTM Bool) (en ex : C.State), 0 < C.k ∧
      ∀ x : List Bool, ∃ t ≤ b * (T x.length + x.length + (f x).length + 1),
        0 < t ∧
        (∀ u < t, (C.tm.runFrom (Cfg.ofWords (input := x) en (stateWord C.k x)) u).state ≠
          some ex) ∧
        C.tm.runFrom (Cfg.ofWords (input := x) en (stateWord C.k x)) t =
          Cfg.ofWords ex (stateWord C.k (f x)) := by
    by_cases he : en₀ = ex₀
    · subst ex₀
      let C : FinTM Bool := ⟨C₀.k, Unit ⊕ C₀.State, seamReleaseTM C₀.tm en₀⟩
      refine ⟨C, Sum.inl (), Sum.inr en₀, hk₀, ?_⟩
      intro x
      obtain ⟨t, ht, hpos, hfirst, hrun⟩ := hC₀ x x
      have hr := seamReleaseTM_firstReturn C₀.tm en₀ rfl hpos hrun rfl hfirst
      exact ⟨t, ht, hpos, hr.2, hr.1⟩
    · refine ⟨C₀, en₀, ex₀, hk₀, ?_⟩
      intro x
      obtain ⟨t, ht, hpos, hfirst, hrun⟩ := hC₀ x x
      refine ⟨t, ht, hpos, ?_, hrun⟩
      intro u hu
      rcases Nat.eq_zero_or_pos u with rfl | hupos
      · simpa [Cfg.ofWords] using he
      · exact hfirst u hupos hu
  obtain ⟨C, en, ex, hk, hC⟩ := hcallee
  let D : FinTM Bool := ⟨C.k, SweepPhase ⊕ C.State,
    seamCompTM (inputCopyTM C.k ⟨0, hk⟩) .done C.tm en⟩
  refine ⟨D, Sum.inl .sweep, Sum.inr ex, b + 3, hk, ?_⟩
  intro x
  obtain ⟨t, ht, hpos, hfirst, hrun⟩ := hC x
  have hcopy := inputCall_copy C.k hk x
  have hcut := (inputCopyTM_run_ofCfg (x := x) ⟨0, hk⟩
    (Cfg.ofWords SweepPhase.sweep (fun _ => [])) rfl rfl).2.1
  have hall := seamCompTM_run_ofCfg (inputCopyTM C.k ⟨0, hk⟩) .done C.tm en
    hcopy rfl hcut hrun
  have hfirst' := seamCompTM_firstReturn_ofCfg (inputCopyTM C.k ⟨0, hk⟩) .done C.tm en ex
    hcopy rfl hcut hrun rfl hfirst
  refine ⟨2 * x.length + 2 + 1 + t, ?_, by omega, (fun u _ hu => hfirst' u hu), hall⟩
  rw [Nat.add_mul]
  omega

end Turing.FinTM

namespace Turing

/-- The seek's rewind needs one additional left move after the public rewind returns at `1`:
there is no public native-input-head primitive with that exit convention. -/
private inductive InputSeekRw where
  | start | scan | left | done
deriving DecidableEq, Fintype

/-- The four-state input rewind; no public native-input-head primitive finishes at marker `0`.
The public `FinTM.rewind_heads` supplies its scan and all prefix work-head bounds. -/
private def inputSeekRewind : MultiTapeTM 2 Bool InputSeekRw where
  q₀ := .start
  tr := fun q inp _ => match q with
    | .start => FinTM.controlAction .neg (some .scan)
    | .scan => match inp with
      | some _ => FinTM.controlAction .neg (some .scan)
      | none => FinTM.controlAction .pos (some .left)
    | .left => FinTM.controlAction .neg (some .done)
    | .done => FinTM.controlAction 0 (some .done)

/-- Rewind to the left marker, keeping all work heads fixed and excluding an earlier exit.

**Proof sketch.** Invoke the public rewind with exit `left`, then move left once. Since
`done` is stationary, reaching it before the public rewind's `left` endpoint is impossible. -/
private theorem inputSeekRewind_run {x : List Bool} (d : Cfg 2 Bool InputSeekRw x)
    (hd : d.state = some .start) :
    ∃ r ≤ d.inputPos.val + 3,
      inputSeekRewind.runFrom d r = { d with state := some .done, inputPos := 0 } ∧
      (∀ u < r, (inputSeekRewind.runFrom d u).state ≠ some .done) ∧
      ∀ u ≤ r, (inputSeekRewind.runFrom d u).workTapePos = d.workTapePos := by
  obtain ⟨r, hr, hrun, hheads⟩ := FinTM.rewind_heads inputSeekRewind .start .scan
    (some .left) (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl) d hd
  have hcut (u : ℕ) (hu : u ≤ r) : (inputSeekRewind.runFrom d u).state ≠ some .done := by
    intro hdone
    have hfix : inputSeekRewind.step (inputSeekRewind.runFrom d u) =
        inputSeekRewind.runFrom d u := by
      rw [step_of_inputMoveAction _ _ 0 hdone rfl]
      apply Cfg.ext
      · exact hdone.symm
      · simp
      · rfl
      · rfl
      · rfl
    have hsame : inputSeekRewind.runFrom d r = inputSeekRewind.runFrom d u := by
      rw [show r = u + (r - u) by omega, MultiTapeTM.runFrom_add]
      exact Function.iterate_fixed hfix _
    have := congrArg Cfg.state hsame
    simp [hrun, hdone] at this
  have hend : inputSeekRewind.runFrom d (r + 1) =
      { d with state := some .done, inputPos := 0 } := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hrun]
    change (FinTM.controlAction SignType.neg (some InputSeekRw.done)).apply
      ({ d with state := some .left, inputPos := 1 } : Cfg 2 Bool InputSeekRw x) = _
    rw [FinTM.controlAction_apply]
    apply Cfg.ext rfl _ rfl rfl rfl
    apply Fin.ext
    rw [FinTM.moveInputPos_neg_val]
  refine ⟨r + 1, by omega, hend, (fun u hu => hcut u (by omega)), ?_⟩
  intro u hu
  by_cases hur : u ≤ r
  · exact hheads u hur
  · have : u = r + 1 := by omega
    subst u
    rw [hend]

/-- A seek round moves the input right once; there is no public native-input-head primitive
for the counter host's cyclic one-step body. -/
private def inputSeekStep : MultiTapeTM 1 Bool Unit where
  q₀ := ()
  tr := fun _ _ _ => inputMoveAction 1 ()

/-- The input-only seek body preserves the entire work bank and output at every prefix.

**Proof sketch.** Induct on the number of right moves, using the public input-action step. -/
private theorem inputSeekStep_run {x : List Bool} (c : Cfg 1 Bool Unit x)
    (hc : c.state = some ()) (r : ℕ) :
    inputSeekStep.runFrom c r =
      { c with inputPos := (fun p : Fin (x.length + 2) => moveInputPos p 1)^[r] c.inputPos } := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih]
    rw [step_of_inputMoveAction inputSeekStep
      ({ c with inputPos := (fun p : Fin (x.length + 2) => moveInputPos p 1)^[r] c.inputPos })
      1 hc rfl, Function.iterate_succ_apply']
    simp only [hc]

/-- Before the right boundary is reached, repeated native right moves add their count. -/
private theorem inputSeek_right_value {n : ℕ} (p : Fin (n + 2)) (r : ℕ)
    (hr : p.val + r ≤ n + 1) :
    ((fun q : Fin (n + 2) => moveInputPos q 1)^[r] p).val = p.val + r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have ih' := ih (by omega)
    rw [Function.iterate_succ_apply']
    change (moveInputPos _ SignType.pos).val = _
    rw [moveInputPos_pos_of_ne_right _ (by omega)]
    simp only
    omega

/-- Copy, marker rewind, binary countdown, and cleanup, joined by three public seams. -/
private def inputSeekMachine : MultiTapeTM 2 Bool
    (((SweepPhase ⊕ InputSeekRw) ⊕ CounterLoopState Unit) ⊕ SweepPhase) :=
  seamCompTM
    (seamCompTM (seamCompTM (copyTM 2 0 1) .done inputSeekRewind .start)
      (Sum.inr .done) (counterLoopTM inputSeekStep () none) (.dec .run))
    (Sum.inr .done) (clearTM 2 1) .sweep

/-- The public seam visited-set inclusion transfers a common interval bound through dispatch.
This is used at all three seams of the seek, with intervals measured at its original heads. -/
private theorem inputSeek_seam_range {S₁ S₂ : Type} [DecidableEq S₁] {x : List Bool}
    (M₁ : MultiTapeTM 2 Bool S₁) (ex : S₁) (M₂ : MultiTapeTM 2 Bool S₂) (en : S₂)
    {c₀ c₁ : Cfg 2 Bool S₁ x} {t₁ t₂ : ℕ}
    (h₁ : M₁.runFrom c₀ t₁ = c₁) (hex : c₁.state = some ex)
    (hcut : ∀ u < t₁, (M₁.runFrom c₀ u).state ≠ some ex)
    (lo hi : Fin 2 → ℤ)
    (hleft : ∀ u ≤ t₁, ∀ j, (M₁.runFrom c₀ u).workTapePos j ∈ Finset.Icc (lo j) (hi j))
    (hright : ∀ u ≤ t₂, ∀ j,
      (M₂.runFrom (c₁.mapState fun _ => en) u).workTapePos j ∈ Finset.Icc (lo j) (hi j)) :
    ∀ u ≤ t₁ + 1 + t₂, ∀ j,
      ((seamCompTM M₁ ex M₂ en).runFrom (c₀.mapState Sum.inl) u).workTapePos j ∈
        Finset.Icc (lo j) (hi j) := by
  intro u hu j
  have hv := seamCompTM_visitedByTapeHead_ofCfg M₁ ex M₂ en (T₂ := t₂) h₁ hex hcut j
    (Finset.mem_image.mpr ⟨u, Finset.mem_range.mpr (by omega), rfl⟩)
  rcases Finset.mem_union.mp hv with hv | hv
  · obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hv
    rw [← heq]
    exact hleft v (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hv) j
  · obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hv
    rw [← heq]
    exact hright v (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hv) j

/-- **R8.5b, the input seek** (design §12.8a §3). There is a two-tape `Bool`
module with entry and exit states with the following contract. Let tape `0`
hold, from its head, a delimited word `w` whose little-endian value `p` is a
valid input position, at most `|x| + 1`, and let tape `1` be blank. From the
entry, with the input head anywhere, the module reaches `exit` with the input
head at `p` within `C·(|w| + pos + p + 1)` steps, where `pos` is the starting
input position, and not earlier. Every work tape, every work head and the
output are restored. Up to the exit every work head stays within
`C·(|w| + 1)` cells of its entry position. So the module's work space is
`O(|w| + 1)`, however far the input head travels, and repeated calls compose.
A rich host runs it lifted on two dedicated digit tapes.

**Proof sketch.** Copy `w` to the scratch tape (`Turing.copyTM_run_ofCfg`,
`2|w| + 2`). Rewind the input head: `timed_rewind` returns it to position `1`
within `pos + 2` steps, and one further left move reaches the left end marker
`0`. Run `Turing.counterLoopTM` with the scratch copy as the
counter and the one-step round "input head right", `p` rounds
(`Turing.counterLoopTM_run_done`, `p + counterOverhead w (p + 1)`, at most
`5p + 2|w| + 2` by `Turing.counterOverhead_le`). The counter ends all `true`
with its head back; `Turing.clearTM_run_ofCfg` blanks it. The phases join by
R2 seams, whose dispatch steps add a constant. The work heads move only in the
copy, the counter loop and the clear, whose trajectory clauses keep each one
within `[pos - 1, pos + |w|]` of its tape. -/
theorem exists_inputSeekTM :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM 2 Bool S) (entry exit : S)
      (C : ℕ),
      ∀ {x : List Bool} (p : ℕ) (w : List Bool), Nat.ofDigits 2 (w.map Bool.toNat) = p →
        p ≤ x.length + 1 → ∀ d : Cfg 2 Bool S x, d.state = some entry →
        (∀ q : ℤ, -1 ≤ q → q ≤ (w.length : ℤ) →
          d.workTapes 0 (d.workTapePos 0 + q) = FinTM.bufferTape w q) →
        (∀ q, d.workTapes 1 q = none) →
        ∃ t ≤ C * (w.length + d.inputPos.val + p + 1),
          (∀ u < t, (R.runFrom d u).state ≠ some exit) ∧
          (∀ u ≤ t, ∀ j : Fin 2,
            |(R.runFrom d u).workTapePos j - d.workTapePos j| ≤ ((C * (w.length + 1) : ℕ) : ℤ)) ∧
          (R.runFrom d t).state = some exit ∧ ((R.runFrom d t).inputPos : ℕ) = p ∧
          (R.runFrom d t).workTapes = d.workTapes ∧ (R.runFrom d t).workTapePos = d.workTapePos ∧
          (R.runFrom d t).output = d.output := by
  refine ⟨_, inferInstance, inferInstance, inputSeekMachine,
    Sum.inl (Sum.inl (Sum.inl .sweep)), Sum.inr .done, 13, ?_⟩
  intro x p w hp hpx d hd hw hblank
  let d₀ : Cfg 2 Bool SweepPhase x :=
    ⟨some .sweep, d.inputPos, d.workTapes, d.workTapePos, d.output⟩
  let d₁ : Cfg 2 Bool SweepPhase x :=
    { d₀ with
      state := some .done
      workTapes := fun j z => if j = 1 then FinTM.bufferTape w (z - d.workTapePos 1)
        else d.workTapes j z }
  have hcopy₀ := copyTM_run_ofCfg 0 1 (by decide) w d₀ rfl hw
  have hcopy : (copyTM 2 0 1).runFrom d₀ (2 * w.length + 2) = d₁ := by
    rw [hcopy₀.1]
    apply Cfg.ext <;> try rfl
    funext j z
    by_cases hj : j = 1
    · subst j
      simp only [d₀, d₁, true_and, if_true]
      by_cases hz : d.workTapePos 1 ≤ z ∧ z < d.workTapePos 1 + (w.length : ℤ)
      · simp [hz]
      · rw [if_neg hz, hblank]
        unfold FinTM.bufferTape
        split_ifs with hz₀
        · rw [List.getElem?_eq_none (by omega)]
        · rfl
    · simp [d₀, d₁, hj]
  let rw₀ := d₁.mapState (fun _ => InputSeekRw.start)
  obtain ⟨r, hr, hrewind, hrCut, hrHeads⟩ := inputSeekRewind_run rw₀ rfl
  let rw₁ : Cfg 2 Bool InputSeekRw x := { rw₀ with state := some .done, inputPos := 0 }
  let c : Cfg 1 Bool Unit x :=
    ⟨some (), 0, fun _ => d.workTapes 0, fun _ => d.workTapePos 0, d.output⟩
  let ct := fun z => FinTM.bufferTape w (z - d.workTapePos 1)
  have hct : ∀ z : ℤ, -1 ≤ z → z ≤ (w.length : ℤ) →
      ct (d.workTapePos 1 + z) = FinTM.bufferTape w z := by
    intro z _ _
    simp [ct]
  have hstart : rw₁.mapState (fun _ => CounterLoopState.dec FlagPhase.run) =
      counterLoopCfg (some (.dec .run)) c ct (d.workTapePos 1) := by
    rw [counter_cfg_eq]
    apply Cfg.ext <;> try rfl
    · funext j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [Fin.lastCases_last]
        rfl
      · simp only [Fin.lastCases_castSucc]
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        rfl
    · funext j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [Fin.lastCases_last]
        rfl
      · simp only [Fin.lastCases_castSucc]
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        rfl
  have horbit (a : ℕ) : counterLoopOrbit inputSeekStep (fun _ => 1) c a =
      inputSeekStep.runFrom c a := rfl
  have hstate (a : ℕ) : (counterLoopOrbit inputSeekStep (fun _ => 1) c a).state = some () := by
    rw [horbit, inputSeekStep_run c rfl]
  have hround : ∀ a < p,
      (counterLoopOrbit inputSeekStep (fun _ => 1) c a).state = some () ∧
      0 < (1 : ℕ) ∧
      (∀ u, 0 < u → u < (1 : ℕ) →
        ∃ q, (inputSeekStep.runFrom (counterLoopOrbit inputSeekStep (fun _ => 1) c a) u).state =
          some q ∧ q ≠ () ∧ (none : Option Unit) ≠ some q) ∧
      (counterLoopOrbit inputSeekStep (fun _ => 1) c (a + 1)).state = some () := by
    intro a _
    exact ⟨hstate a, Nat.one_pos, fun u hu hu' => by omega, hstate (a + 1)⟩
  let l := p + counterOverhead w (p + 1)
  have hloop₀ := counterLoopTM_run_done inputSeekStep () none (fun _ => 1) c w ct
    (d.workTapePos 1) hct p hp hround l (by simp [l])
  let lc : Cfg 2 Bool (CounterLoopState Unit) x :=
    ⟨some .done, ⟨p, by omega⟩,
      (fun j z => if j = 1 then
        FinTM.bufferTape (List.replicate w.length true) (z - d.workTapePos 1)
        else d.workTapes j z), d.workTapePos, d.output⟩
  have hloop : (counterLoopTM inputSeekStep () none).runFrom
      (rw₁.mapState fun _ => .dec .run) l = lc := by
    rw [hstart, hloop₀.1, counter_cfg_eq, horbit, inputSeekStep_run c rfl]
    apply Cfg.ext <;> try rfl
    · apply Fin.ext
      simpa [c, lc] using inputSeek_right_value (0 : Fin (x.length + 2)) p (by simpa using hpx)
    · funext j z
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [Fin.lastCases_last]
        change (if d.workTapePos 1 ≤ z ∧ z < d.workTapePos 1 + (w.length : ℤ)
          then some true else ct z) =
            FinTM.bufferTape (List.replicate w.length true) (z - d.workTapePos 1)
        by_cases hz : d.workTapePos 1 ≤ z ∧ z < d.workTapePos 1 + (w.length : ℤ)
        · simp [hz, FinTM.bufferTape,
            show (z - d.workTapePos 1).toNat < w.length by omega]
        · rw [if_neg hz]
          unfold ct FinTM.bufferTape
          split_ifs with hzero
          · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
          · rfl
      · simp only [Fin.lastCases_castSucc]
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        rfl
    · funext j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [Fin.lastCases_last]
        rfl
      · simp only [Fin.lastCases_castSucc]
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        rfl
  have hlCut : ∀ u < l,
      ((counterLoopTM inputSeekStep () none).runFrom (rw₁.mapState fun _ => .dec .run) u).state ≠
        some .done := by
    rw [hstart]
    exact fun u hu => (hloop₀.2.1 u hu).1
  have hclear₀ := clearTM_run_ofCfg 1 (List.replicate w.length true)
    (lc.mapState fun _ => SweepPhase.sweep) rfl (by
      intro z _ _
      simp [lc, Cfg.mapState])
  let finish : Cfg 2 Bool SweepPhase x :=
    ⟨some .done, ⟨p, by omega⟩, d.workTapes, d.workTapePos, d.output⟩
  have hclear : (clearTM 2 1).runFrom (lc.mapState fun _ => .sweep)
      (2 * w.length + 2) = finish := by
    simpa only [List.length_replicate] using hclear₀.1.trans (by
      apply Cfg.ext <;> try rfl
      funext j z
      by_cases hj : j = 1
      · subst j
        simp only [lc, finish, Cfg.mapState, Option.map_some, List.length_replicate,
          true_and, if_true]
        rw [hblank]
        split_ifs with hz
        · rfl
        · unfold FinTM.bufferTape
          split_ifs with hzero
          · rw [List.getElem?_eq_none (by simp; omega)]
          · rfl
      · simp [lc, finish, Cfg.mapState, hj])
  have hcCut : ∀ u < 2 * w.length + 2,
      ((clearTM 2 1).runFrom (lc.mapState fun _ => .sweep) u).state ≠ some .done := by
    simpa only [List.length_replicate] using hclear₀.2.1
  -- The three stationary dispatches preserve the original work-head intervals.
  have hcr := seamCompTM_run_ofCfg (copyTM 2 0 1) .done inputSeekRewind .start
    hcopy rfl hcopy₀.2.1 hrewind
  have hcrCut := seamCompTM_firstReturn_ofCfg (copyTM 2 0 1) .done inputSeekRewind .start .done
    hcopy rfl hcopy₀.2.1 hrewind rfl hrCut
  have hcl := seamCompTM_run_ofCfg
    (seamCompTM (copyTM 2 0 1) .done inputSeekRewind .start) (Sum.inr .done)
    (counterLoopTM inputSeekStep () none) (.dec .run) hcr rfl hcrCut hloop
  have hclCut := seamCompTM_firstReturn_ofCfg
    (seamCompTM (copyTM 2 0 1) .done inputSeekRewind .start) (Sum.inr .done)
    (counterLoopTM inputSeekStep () none) (.dec .run) .done hcr rfl hcrCut hloop rfl hlCut
  have hall := seamCompTM_run_ofCfg
    (seamCompTM (seamCompTM (copyTM 2 0 1) .done inputSeekRewind .start) (Sum.inr .done)
      (counterLoopTM inputSeekStep () none) (.dec .run)) (Sum.inr .done)
    (clearTM 2 1) .sweep hcl rfl hclCut hclear
  have hallCut := seamCompTM_firstReturn_ofCfg
    (seamCompTM (seamCompTM (copyTM 2 0 1) .done inputSeekRewind .start) (Sum.inr .done)
      (counterLoopTM inputSeekStep () none) (.dec .run)) (Sum.inr .done)
    (clearTM 2 1) .sweep .done hcl rfl hclCut hclear rfl hcCut
  have hdmap : ((d₀.mapState Sum.inl).mapState Sum.inl).mapState Sum.inl = d := by
    apply Cfg.ext <;> try rfl
    simpa [d₀, Cfg.mapState] using hd.symm
  have hcSpan : ∀ u ≤ 2 * w.length + 2, ∀ j,
      ((copyTM 2 0 1).runFrom d₀ u).workTapePos j ∈
        Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (w.length : ℤ)) := by
    intro u hu j
    have h := hcopy₀.2.2 j u hu
    fin_cases j <;> simpa [d₀] using h
  have hrSpan : ∀ u ≤ r, ∀ j, (inputSeekRewind.runFrom rw₀ u).workTapePos j ∈
      Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (w.length : ℤ)) := by
    intro u hu j
    rw [hrHeads u hu]
    simp [rw₀, d₁, d₀, Cfg.mapState, Finset.mem_Icc]
  have hlSpan : ∀ u ≤ l, ∀ j,
      ((counterLoopTM inputSeekStep () none).runFrom
        (rw₁.mapState fun _ => .dec .run) u).workTapePos j ∈
          Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (w.length : ℤ)) := by
    intro u hu j
    rw [hstart]
    fin_cases j
    · obtain ⟨a, v, _, hv⟩ := hloop₀.2.2.2 u hu
      have hh := hv 0
      rw [inputSeekStep_run _ (hstate a), horbit, inputSeekStep_run c rfl] at hh
      have hh' : ((counterLoopTM inputSeekStep () none).runFrom
          (counterLoopCfg (some (.dec .run)) c ct (d.workTapePos 1)) u).workTapePos 0 =
            d.workTapePos 0 := hh
      change ((counterLoopTM inputSeekStep () none).runFrom
        (counterLoopCfg (some (.dec .run)) c ct (d.workTapePos 1)) u).workTapePos 0 ∈
          Finset.Icc (d.workTapePos 0 - 1) (d.workTapePos 0 + (w.length : ℤ))
      rw [hh']
      simp [Finset.mem_Icc]
    · exact hloop₀.2.2.1 u hu
  have hclearSpan : ∀ u ≤ 2 * w.length + 2, ∀ j,
      ((clearTM 2 1).runFrom (lc.mapState fun _ => .sweep) u).workTapePos j ∈
        Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (w.length : ℤ)) := by
    intro u hu j
    have h := hclear₀.2.2 j u (by simpa using hu)
    fin_cases j
    · change (if (0 : Fin 2) = 1 then _ else _) at h
      rw [if_neg (by decide)] at h
      have h' : ((clearTM 2 1).runFrom (lc.mapState fun _ => .sweep) u).workTapePos 0 =
          d.workTapePos 0 := h
      change ((clearTM 2 1).runFrom (lc.mapState fun _ => .sweep) u).workTapePos 0 ∈
        Finset.Icc (d.workTapePos 0 - 1) (d.workTapePos 0 + (w.length : ℤ))
      rw [h']
      simp [Finset.mem_Icc]
    · simpa [lc, Cfg.mapState] using h
  have hcrSpan := inputSeek_seam_range _ _ _ _ hcopy rfl hcopy₀.2.1 _ _ hcSpan hrSpan
  have hclSpan := inputSeek_seam_range _ _ _ _ hcr rfl hcrCut _ _ hcrSpan hlSpan
  have hallSpan := inputSeek_seam_range _ _ _ _ hcl rfl hclCut _ _ hclSpan hclearSpan
  rw [hdmap] at hall hallCut hallSpan
  refine ⟨((2 * w.length + 2 + 1 + r) + 1 + l) + 1 + (2 * w.length + 2), ?_,
    hallCut, ?_, ?_⟩
  · have ho := counterOverhead_le w
    rw [hp] at ho
    change r ≤ d.inputPos.val + 3 at hr
    dsimp [l]
    omega
  · intro u hu j
    have h := Finset.mem_Icc.mp (hallSpan u hu j)
    rw [abs_le]
    constructor <;> omega
  · change (inputSeekMachine.runFrom d _).state = _ ∧ _
    rw [show inputSeekMachine.runFrom d _ = finish.mapState Sum.inr from hall]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end Turing
