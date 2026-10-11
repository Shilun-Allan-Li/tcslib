/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.SpaceClasses
import TCSlib.Complexity.ClassNP.SAT
-- B2b sanctioned imports (briefs/ch34-b2b.md).
import TCSlib.Complexity.TuringMachine.Build.CounterLoop
import TCSlib.Complexity.TuringMachine.Build.VirtualInput
import TCSlib.Complexity.TuringMachine.Build.Seam
import TCSlib.Complexity.SpaceComplexity.Machines.Clean
import TCSlib.Complexity.CircuitComplexity.MeyerTableau

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Time against space: the easy inclusions

The first two inclusions of [AB09, Theorem 4.2]
(`DTIME(S) ⊆ SPACE(S) ⊆ NSPACE(S)`), the polynomial-level corollaries on the
p. 92 chain (`P ⊆ PSPACE`), and the certificate-cycling memberships of
[AB09, Example 4.6] (`NP ⊆ PSPACE`, `3SAT ∈ PSPACE`). The third inclusion of
Theorem 4.2 (`NSPACE(S) ⊆ DTIME(2^{O(S)})`) needs the configuration-graph layer
and is phase P4.2; the parity example of [AB09, Example 4.7] lives in
`TCSlib.Complexity.SpaceComplexity.Examples`.

## Main results (first two proved; remaining phase-P4.1 statements sorried)

* `Complexity.DTIME_subset_SPACE` — [AB09, Theorem 4.2, first inclusion].
* `Complexity.P_subset_PSPACE` — the polynomial corollary.
* `Complexity.NP_subset_PSPACE` — [AB09, Example 4.6].
* `Complexity.SAT3_mem_PSPACE` — [AB09, Example 4.6].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1, Theorem 4.2, Example 4.6.)
-/

namespace Complexity

open Turing

/-- **Time bounds space**: `DTIME T ⊆ SPACE T` — a machine can visit at most one
new cell per head per step. [AB09, Theorem 4.2, first inclusion]

**Proof sketch.** Let `M` decide `L` within `c · T n` steps. Each of `M`'s `k`
work-tape heads visits at most `c · T n + 1` cells in `c · T n` steps
(`Turing.MultiTapeTM.visitedByTapeHead` is an image of `Finset.range
(c·T n + 1)`, so `Finset.card_image_le` bounds it), hence
`spaceUsed ≤ k · (c · T n + 1) ≤ (k · c + k) · T n` whenever `T n ≥ 1`. If
`T n = 0` for some `n` then every `c · T` vanishes there and `DTIME T = ∅` by
the `Complexity.DTIME_eq_empty_of_exists_zero` argument (no machine halts in
`0` steps from a live initial state), so the inclusion is vacuous. The space
witness reuses `M` itself with the absorbed constant `k · c + k`, and the
halting time `c · T |x|` instantiates `Turing.FinTM.ComputesInSpace`'s
existential time. -/
theorem DTIME_subset_SPACE (T : ℕ → ℕ) : DTIME T ⊆ SPACE T := by
  classical
  by_cases hzero : ∃ n, T n = 0
  · rw [DTIME_eq_empty_of_exists_zero hzero]
    exact Set.empty_subset _
  have hpos (n : ℕ) : 1 ≤ T n := by
    by_contra hn
    exact hzero ⟨n, by omega⟩
  rintro L ⟨c, M, hM⟩
  refine ⟨M.k * c + M.k, M, fun x => ?_⟩
  refine ⟨c * T x.length, hM x, ?_⟩
  calc
    M.tm.spaceUsed (M.tm.initCfg x) (c * T x.length)
        ≤ M.k * (c * T x.length + 1) := M.tm.spaceUsed_le_mul_succ _ _
    _ = M.k * c * T x.length + M.k := by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
    _ ≤ M.k * c * T x.length + M.k * T x.length :=
      Nat.add_le_add_left
        (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left M.k (hpos x.length)) _
    _ = (M.k * c + M.k) * T x.length := (Nat.add_mul _ _ _).symm

/-- `P ⊆ PSPACE` — the polynomial-level corollary, on the p. 92 chain.

**Proof sketch.** Degree by degree: `DTIME (n^c + 1) ⊆ SPACE (n^c + 1)` by
`Complexity.DTIME_subset_SPACE`, then `Set.iUnion_mono` across the unions
defining `Complexity.P` and `Complexity.PSPACE`. -/
theorem P_subset_PSPACE : P ⊆ PSPACE := by
  exact Set.iUnion_mono fun c => DTIME_subset_SPACE (fun n => n ^ c + 1)

/-! ## B2b private assembly -/

/-- A proved computation and its space bound supply a reusable clean call.

**Proof sketch.** Convert the bundled computation to its halt and output equations,
bound each tape by total space, and apply the received cleanup contract. This is the
same cleanup argument for the verifier, identity copy, and unary setup machine. -/
private theorem b2b_clean_run (M : FinTM Bool) (x y : List Bool) (t s : ℕ)
    (ht : M.ComputesInTime x y t)
    (hs : M.tm.spaceUsed (M.tm.initCfg x) t ≤ s) :
    ∃ T : ℕ,
      ((LogProg.cleanTM M.tm M.tm.q₀).runFrom
        (Cfg.init (LogProg.CleanSt.init M.tm.q₀) x) T).state = none ∧
      ((LogProg.cleanTM M.tm M.tm.q₀).runFrom
        (Cfg.init (LogProg.CleanSt.init M.tm.q₀) x) T).output = y ∧
      ((LogProg.cleanTM M.tm M.tm.q₀).runFrom
        (Cfg.init (LogProg.CleanSt.init M.tm.q₀) x) T).workTapes = (fun _ _ => none) ∧
      ((LogProg.cleanTM M.tm M.tm.q₀).runFrom
        (Cfg.init (LogProg.CleanSt.init M.tm.q₀) x) T).workTapePos = (fun _ => 0) ∧
      ∀ u ≤ T, ∀ j, |((LogProg.cleanTM M.tm M.tm.q₀).runFrom
        (Cfg.init (LogProg.CleanSt.init M.tm.q₀) x) u).workTapePos j| ≤ (s : ℤ) := by
  obtain ⟨hh, ho⟩ := (FinTM.computesInTime_iff _ _ _ _).mp ht
  obtain ⟨T, h1, h2, h3, h4, h5⟩ := LogProg.cleanTM_run M.tm M.tm.q₀ M.tm.q₀ x t hh s
    (fun i => (M.tm.spaceUsedByTape_le_spaceUsed _ t i).trans hs)
  exact ⟨T, h1, h2.trans ho, h3, h4, h5⟩

/-- The verifier's polynomial-time membership supplies polynomial-radius clean calls.
This is route B of the B2b brief, through the frozen time-to-space inclusion. -/
private theorem b2b_clean_verifier (V : Language Bool) (hV : V ∈ P) :
    ∃ (e cV : ℕ) (MV : FinTM Bool), ∀ y : List Bool,
      LogProg.CleanRun (LogProg.cleanTM MV.tm MV.tm.q₀)
        (LogProg.CleanSt.init MV.tm.q₀) y
        (MultiTapeTM.indicator (V : Set (List Bool)) y) (cV * (y.length ^ e + 1)) := by
  obtain ⟨e, he⟩ := Set.mem_iUnion.mp (P_subset_PSPACE hV)
  obtain ⟨cV, MV, hMV⟩ := he
  refine ⟨e, cV, MV, fun y => ?_⟩
  obtain ⟨t, ht, hs⟩ := hMV y
  exact b2b_clean_run MV y _ t _ ht hs

/-- The three states of the sanctioned input-rewind glue. -/
private inductive B2bRewindState | start | scan | done
  deriving DecidableEq, Fintype

/-- Halting rewind glue, instantiated only through the public `rewind_heads` row.
The unused stationary state keeps the brief's three-state interface. -/
private def b2b_rewindTM (k : ℕ) : MultiTapeTM k Bool B2bRewindState where
  q₀ := .start
  tr := fun q inp _ =>
    match q with
    | .start => FinTM.controlAction .neg (some .scan)
    | .scan =>
      match inp with
      | some _ => FinTM.controlAction .neg (some .scan)
      | none => FinTM.controlAction .pos none
    | .done => FinTM.controlAction 0 (some .done)

/-- The native and virtual rewinds share this single instance of `rewind_heads`. -/
private theorem b2b_rewind_run {k : ℕ} {x : List Bool}
    (c : Cfg k Bool B2bRewindState x) (hs : c.state = some .start) :
    ∃ r ≤ c.inputPos.val + 2,
      (b2b_rewindTM k).runFrom c r = { c with state := none, inputPos := 1 } ∧
      ∀ u ≤ r, ((b2b_rewindTM k).runFrom c u).workTapePos = c.workTapePos :=
  FinTM.rewind_heads (b2b_rewindTM k) .start .scan none
    (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl) c hs

/-- The setup's work-tape rewind is the public virtual-input host applied to
the same halting rewind; it preserves the entire buffered word. -/
private theorem b2b_vhost_rewind {x y : List Bool}
    (c : Cfg 0 Bool B2bRewindState y) (hs : c.state = some .start)
    (b : Bool) (hb : FinTM.VirtualTag c.inputPos b)
    (p : Fin (x.length + 2)) (pre : List Bool) :
    ∃ u ≤ c.inputPos.val + 2, ∃ b',
      (vhostEmitTM (b2b_rewindTM 0)).runFrom (vhostCfg c b p pre) u =
        vhostCfg ({ c with state := none, inputPos := 1 } : Cfg 0 Bool B2bRewindState y)
          b' p pre ∧
      ((vhostEmitTM (b2b_rewindTM 0)).runFrom (vhostCfg c b p pre) u).workTapePos
        (vhostBuffer 0) = 0 ∧
      ((vhostEmitTM (b2b_rewindTM 0)).runFrom (vhostCfg c b p pre) u).workTapes
        (vhostBuffer 0) = FinTM.bufferTape y := by
  obtain ⟨u, hu, hrun, _⟩ := b2b_rewind_run c hs
  obtain ⟨b', _, he⟩ := vhostEmitTM_runFrom (b2b_rewindTM 0) c b hb p pre u
  rw [hrun] at he
  refine ⟨u, hu, b', he, ?_, ?_⟩
  · rw [he]; simp only [vhostCfg, vhostBuffer, Fin.addCases_left]; simp
  · rw [he]; simp only [vhostCfg, vhostBuffer, Fin.addCases_left]

/-- The verdict reader returns one of two live exits. -/
private inductive B2bVerdictState | left | read | done (b : Bool)
  deriving DecidableEq, Fintype

/-- The sanctioned two-step verdict glue: move left, then read and erase. -/
private def b2b_verdictTM (k : ℕ) (i : Fin k) : MultiTapeTM k Bool B2bVerdictState where
  q₀ := .left
  tr := fun q _ w =>
    match q with
    | .left => tapeAction i 0 none .neg .read
    | .read =>
      match w i with
      | some b => tapeAction i 0 (some none) 0 (.done b)
      | none => tapeAction i 0 none 0 (.done false)
    | .done b => inputMoveAction 0 (.done b)

/-- The verdict reader's complete two-step trace, preserving the surrounding frame.

**Proof sketch.** The public non-writing one-tape step moves to the captured bit.
The public writing one-tape step erases it and records its value in the exit state.
There are only three times, so the trace and all its prefix facts need no induction. -/
private theorem b2b_verdict_trace {k : ℕ} {x : List Bool} (i : Fin k)
    (d : Cfg k Bool B2bVerdictState x) (b : Bool)
    (hs : d.state = some .left)
    (hb : d.workTapes i (d.workTapePos i - 1) = some b) (t : ℕ) (ht : t ≤ 2) :
    (b2b_verdictTM k i).runFrom d t =
      if t = 0 then d else if t = 1 then
        { d with
          state := some .read
          workTapePos := Function.update d.workTapePos i (d.workTapePos i - 1) }
      else
        { d with
          state := some (.done b)
          workTapes := Function.update d.workTapes i
            (Function.update (d.workTapes i) (d.workTapePos i - 1) none),
          workTapePos := Function.update d.workTapePos i (d.workTapePos i - 1) } := by
  have h1 : (b2b_verdictTM k i).runFrom d 1 =
      { d with
        state := some .read
        workTapePos := Function.update d.workTapePos i (d.workTapePos i - 1) } := by
    simpa [MultiTapeTM.runFrom, moveInputPos_zero, sub_eq_add_neg] using
      step_of_tapeAction_move (b2b_verdictTM k i) d i 0 .neg hs rfl
  have h2 := step_of_tapeAction_write (q' := .done b) (b2b_verdictTM k i)
    ({ d with
        state := some .read
        workTapePos := Function.update d.workTapePos i (d.workTapePos i - 1) } :
      Cfg k Bool B2bVerdictState x) i 0 none 0 rfl
      (by simp [b2b_verdictTM, Cfg.workTapeSymbols, hb])
  interval_cases t
  · rfl
  · simpa using h1
  · rw [MultiTapeTM.runFrom_succ_eq_step', h1, h2]
    simp [moveInputPos_zero]

/-- The stationary loop-anchor phase; the phase host immediately redirects it. -/
private def b2b_anchorTM (k : ℕ) : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr := fun _ _ _ => inputMoveAction 0 ()

/-- The host's only physical output is this final singleton emission. -/
private def b2b_answerTM (k : ℕ) (b : Bool) : MultiTapeTM k Bool (Fin 2) where
  q₀ := 0
  tr := fun q _ _ => FinTM.emitAction [b] id q

/-- The final answer emits its one bit and halts, by the public emission row. -/
private theorem b2b_answer_run {k : ℕ} {x : List Bool}
    (b : Bool) (c : Cfg k Bool (Fin 2) x) (hs : c.state = some 0) :
    ((b2b_answerTM k b).runFrom c 2).state = none ∧
      ((b2b_answerTM k b).runFrom c 2).output = c.output ++ [b] :=
  FinTM.emit_halts (b2b_answerTM k b) [b] id (fun _ _ _ => rfl) c hs

/-- The verifier's hosted source: rewind its input, run and clean the verifier,
then rewind again. This is exactly the two R2 seams specified in route D. -/
private noncomputable def b2b_hostedSource (MV : FinTM Bool) :
    MultiTapeTM (MV.k + MV.k) Bool
      ((B2bRewindState ⊕ Unit) ⊕
        ((LogProg.CleanSt MV.State MV.k ⊕ Unit) ⊕ B2bRewindState)) :=
  seamCompTM (embedEmitRetTM (Function.Embedding.refl _) (b2b_rewindTM _)) (Sum.inr ())
    (seamCompTM (embedEmitRetTM (Function.Embedding.refl _)
        (LogProg.cleanTM MV.tm MV.tm.q₀)) (Sum.inr ())
      (b2b_rewindTM _) .start)
    (Sum.inl (Sum.inl (LogProg.CleanSt.init MV.tm.q₀)))

/-- Forwarding along the identity selection with an empty prefix is the identity.
The proof uses the public selected-tape projections, not embedding internals. -/
private theorem b2b_embed_refl {k : ℕ} {S : Type} {x : List Bool}
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ) (c : Cfg k Bool S x) :
    embedEmitCfg (Function.Embedding.refl _) tapes heads [] c = c := by
  apply Cfg.ext <;> try rfl
  · funext i
    exact embedEmitCfg_selected_tape (Function.Embedding.refl _) tapes heads [] c i
  · funext i
    exact embedEmitCfg_selected_pos (Function.Embedding.refl _) tapes heads [] c i

/-- The hosted verifier source returns its input head to one, with the correct
single bit and completely clean work banks, from any initial input position,
with every bank head inside the clean call's fixed radius.

**Proof sketch.** Take first halts using the public first-halt lemma, convert the
first rewind and the clean call to live returns with R1', and compose the two R2
seams. The final rewind is the same public rewind instance. No new first-halt,
rewind, or virtual-input simulation argument is needed. The two public R2 visited-set
containments reduce each bank position to a rewind or clean-call position. -/
private theorem b2b_hostedSource_run (MV : FinTM Bool) (y : List Bool) (b : Bool) (B : ℕ)
    (hclean : LogProg.CleanRun (LogProg.cleanTM MV.tm MV.tm.q₀)
      (LogProg.CleanSt.init MV.tm.q₀) y b B) (p : Fin (y.length + 2)) :
    ∃ t : ℕ, (b2b_hostedSource MV).runFrom
        { Cfg.init (b2b_hostedSource MV).q₀ y with inputPos := p } t =
      { Cfg.init (b2b_hostedSource MV).q₀ y with state := none, output := [b] } ∧
      ∀ u ≤ t, ∀ j, |((b2b_hostedSource MV).runFrom
        { Cfg.init (b2b_hostedSource MV).q₀ y with inputPos := p } u).workTapePos j| ≤ (B : ℤ) := by
  let k := MV.k + MV.k
  let r0 : Cfg k Bool B2bRewindState y := { Cfg.init .start y with inputPos := p }
  let E1 := embedEmitRetTM (Function.Embedding.refl _) (b2b_rewindTM k)
  obtain ⟨r, _, hr, hrew1⟩ := b2b_rewind_run r0 rfl
  obtain ⟨r1, hr1le, hrlive, hrfirst⟩ := MultiTapeTM.exists_first_halt (b2b_rewindTM k) r0
    (show ((b2b_rewindTM k).runFrom r0 r).state = none by rw [hr])
  have hr1 := hrfirst.trans hr
  have er1 := embedEmitRetTM_run (Function.Embedding.refl _) (b2b_rewindTM k)
    (fun _ _ => none) (fun _ => 0) [] r0 r1 (by simp [r0, Cfg.init]) hrlive
    (by rw [hr1])
  have he1 : E1.runFrom (r0.mapState Sum.inl) r1 = Cfg.init (Sum.inr ()) y := by
    have h := er1.2.1
    simp only [b2b_embed_refl] at h
    rw [hr1] at h
    exact h
  have cut1 : ∀ t < r1, (E1.runFrom (r0.mapState Sum.inl) t).state ≠ some (Sum.inr ()) := by
    simpa only [E1, b2b_embed_refl] using er1.2.2
  let c0 : Cfg k Bool (LogProg.CleanSt MV.State MV.k) y :=
    Cfg.init (LogProg.CleanSt.init MV.tm.q₀) y
  let E2 := embedEmitRetTM (Function.Embedding.refl _) (LogProg.cleanTM MV.tm MV.tm.q₀)
  obtain ⟨T, hhalt, hout, htapes, hheads, hbound⟩ := hclean
  obtain ⟨r2, hr2le, hclive, hcfirst⟩ := MultiTapeTM.exists_first_halt
    (LogProg.cleanTM MV.tm MV.tm.q₀) c0 hhalt
  have ec2 := embedEmitRetTM_run (Function.Embedding.refl _)
    (LogProg.cleanTM MV.tm MV.tm.q₀) (fun _ _ => none) (fun _ => 0) [] c0 r2
    (by simp [c0, Cfg.init]) hclive (by rw [hcfirst]; exact hhalt)
  let c2 : Cfg k Bool (LogProg.CleanSt MV.State MV.k ⊕ Unit) y :=
    { Cfg.init (Sum.inr ()) y with
      inputPos := ((LogProg.cleanTM MV.tm MV.tm.q₀).runFrom c0 T).inputPos,
      output := [b] }
  have he2 : E2.runFrom (c0.mapState Sum.inl) r2 = c2 := by
    have h := ec2.2.1
    simp only [b2b_embed_refl] at h
    rw [hcfirst] at h
    change ((LogProg.cleanTM MV.tm MV.tm.q₀).runFrom c0 T).output = [b] at hout
    change ((LogProg.cleanTM MV.tm MV.tm.q₀).runFrom c0 T).workTapes = (fun _ _ => none) at htapes
    change ((LogProg.cleanTM MV.tm MV.tm.q₀).runFrom c0 T).workTapePos = (fun _ => 0) at hheads
    rw [htapes, hheads, hout] at h
    exact h
  have cut2 : ∀ t < r2, (E2.runFrom (c0.mapState Sum.inl) t).state ≠ some (Sum.inr ()) := by
    simpa only [E2, b2b_embed_refl] using ec2.2.2
  let c3 := c2.mapState (fun _ => B2bRewindState.start)
  obtain ⟨r3, _, hr3, hrew3⟩ := b2b_rewind_run c3 rfl
  have hinner := seamCompTM_run_ofCfg E2 (Sum.inr ()) (b2b_rewindTM k) .start
    he2 rfl cut2 hr3
  have hfull := seamCompTM_run_ofCfg E1 (Sum.inr ())
    (seamCompTM E2 (Sum.inr ()) (b2b_rewindTM k) .start)
    (Sum.inl (Sum.inl (LogProg.CleanSt.init MV.tm.q₀))) he1 rfl cut1 hinner
  have hb1 : ∀ u ≤ r1, ∀ j,
      |(E1.runFrom (r0.mapState Sum.inl) u).workTapePos j| ≤ (B : ℤ) := by
    intro u hu j
    rcases lt_or_eq_of_le hu with hlt | rfl
    · have h := er1.1 u hlt
      simp only [b2b_embed_refl] at h
      rw [h]
      change |((b2b_rewindTM k).runFrom r0 u).workTapePos j| ≤ (B : ℤ)
      rw [hrew1 u (hu.trans hr1le)]
      simp [r0, Cfg.init]
    · rw [he1]; simp [Cfg.init]
  have hb2 : ∀ u ≤ r2, ∀ j,
      |(E2.runFrom (c0.mapState Sum.inl) u).workTapePos j| ≤ (B : ℤ) := by
    intro u hu j
    rcases lt_or_eq_of_le hu with hlt | rfl
    · have h := ec2.1 u hlt
      simp only [b2b_embed_refl] at h
      rw [h]
      exact hbound u (hu.trans hr2le) j
    · rw [he2]; simp [c2, Cfg.init]
  have hb3 : ∀ u ≤ r3, ∀ j,
      |((b2b_rewindTM k).runFrom c3 u).workTapePos j| ≤ (B : ℤ) := by
    intro u hu j
    rw [hrew3 u hu]
    simp [c3, c2, Cfg.mapState, Cfg.init]
  refine ⟨r1 + 1 + (r2 + 1 + r3), ?_, ?_⟩
  · simpa [b2b_hostedSource, E1, E2, r0, c0, c2, c3, Cfg.mapState, Cfg.init]
      using hfull
  · intro u hu j
    have hmem : ((b2b_hostedSource MV).runFrom
        { Cfg.init (b2b_hostedSource MV).q₀ y with inputPos := p } u).workTapePos j ∈
        (b2b_hostedSource MV).visitedByTapeHead
          { Cfg.init (b2b_hostedSource MV).q₀ y with inputPos := p }
          (r1 + 1 + (r2 + 1 + r3)) j :=
      Finset.mem_image.mpr ⟨u, Finset.mem_range.mpr (by omega), rfl⟩
    have houter := seamCompTM_visitedByTapeHead_ofCfg (T₂ := r2 + 1 + r3)
      E1 (Sum.inr ()) (seamCompTM E2 (Sum.inr ()) (b2b_rewindTM k) .start)
      (Sum.inl (Sum.inl (LogProg.CleanSt.init MV.tm.q₀))) he1 rfl cut1 j
    rcases Finset.mem_union.mp (houter hmem) with hleft | hright
    · obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hleft
      rw [← heq]
      exact hb1 v (by have := Finset.mem_range.mp hv; omega) j
    · have hinside := seamCompTM_visitedByTapeHead_ofCfg (T₂ := r3)
        E2 (Sum.inr ()) (b2b_rewindTM k) .start he2 rfl cut2 j
      rcases Finset.mem_union.mp (hinside hright) with hclean' | hrewind'
      · obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hclean'
        rw [← heq]
        exact hb2 v (by have := Finset.mem_range.mp hv; omega) j
      · obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hrewind'
        rw [← heq]
        exact hb3 v (by have := Finset.mem_range.mp hv; omega) j

/-- The phase host's dispatch result is the next phase's tagged start. -/
private theorem b2b_dispatch_retag {k : ℕ} {I : Type} {Ph : I → Type}
    {S : Type} {x : List Bool} (c : Cfg k Bool S x) (j : I) (q : Ph j) :
    c.mapState (fun _ => (⟨j, q⟩ : Σ i, Ph i)) =
      (c.mapState (fun _ => q)).mapState (Sigma.mk j) := by
  cases c
  simp [Cfg.mapState]
  cases ‹Option S› <;> rfl

/-- The all-true counter counts all certificates except the final continuation. -/
private theorem b2b_counter_value (Q : ℕ) :
    Nat.ofDigits 2 ((List.replicate Q true).map Bool.toNat) = 2 ^ Q - 1 := by
  induction Q with
  | zero => rfl
  | succ Q ih =>
    rw [List.replicate_succ, List.map_cons, Nat.ofDigits_cons, ih]
    have : 1 ≤ 2 ^ Q := Nat.one_le_two_pow
    simp only [Bool.toNat_true, pow_succ]
    omega

/-- Iterated fixed-width increment is Meyer's public certificate enumeration.
The strict bound excludes overflow; width zero still has its initial word. -/
private theorem b2b_certificate_orbit (Q r : ℕ) (hr : r < 2 ^ Q) :
    (fun u => (incFixed u).getD u)^[r] (List.replicate Q false) = enumWord Q r := by
  induction r with
  | zero => exact (Meyer.enumWord_zero Q).symm
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih (by omega),
      Meyer.incFixed_enumWord Q r hr, Option.getD_some]

/-- Testing the counted rounds and final word is exactly the received NP witness
quantifier, including the empty certificate. Only Meyer's public word arithmetic is used. -/
private theorem b2b_verifies_iff (x : List Bool) (V : Language Bool) (Q : ℕ) :
    (∃ r ≤ 2 ^ Q - 1, x ++ enumWord Q r ∈ V) ↔
      ∃ u, u.length = Q ∧ x ++ u ∈ V := by
  constructor
  · rintro ⟨r, _, hr⟩
    exact ⟨enumWord Q r, Meyer.length_enumWord Q r, hr⟩
  · rintro ⟨u, hu, hv⟩
    refine ⟨TimeHierarchy.ctrVal u, ?_, ?_⟩
    · have h := Meyer.ctrVal_lt u
      rw [hu] at h
      omega
    · simpa only [← hu, Meyer.enumWord_ctrVal] using hv

/-- Copying the certificate at the captured input's right blank installs the
entire concatenated virtual-input tape, including both blank exterior regions.

**Proof sketch.** Split the cell into the input prefix, the copied certificate
interval, or the exterior. Nonnegative cells reduce to the list-append lookup rule. -/
private theorem b2b_buffer_concat (x u : List Bool) :
    (fun z : ℤ =>
      if (x.length : ℤ) ≤ z ∧ z < (x.length : ℤ) + (u.length : ℤ)
        then FinTM.bufferTape u (z - (x.length : ℤ))
        else FinTM.bufferTape x z) = FinTM.bufferTape (x ++ u) := by
  funext z
  by_cases hx : (x.length : ℤ) ≤ z
  · have hz : 0 ≤ z := by omega
    have hxn : ¬z.toNat < x.length := by omega
    have hsub : (z - (x.length : ℤ)).toNat = z.toNat - x.length := by omega
    by_cases hu : z < (x.length : ℤ) + (u.length : ℤ)
    · simp [hx, hu, FinTM.bufferTape, hz, hsub]
    · simp [hx, hu, FinTM.bufferTape, hz, hxn]
  · by_cases hz : 0 ≤ z
    · simp [hx, FinTM.bufferTape, hz, List.getElem?_append,
        show z.toNat < x.length by omega]
    · simp [hx, FinTM.bufferTape, hz]

/-- A polynomial fixed-window ledger packages a halting decider into PSPACE.
This is precisely the normalization requested in P4.1 Question 5. -/
private theorem b2b_mem_PSPACE_of_ledger (L : Language Bool) (M : FinTM Bool) (D f : ℕ)
    (h : ∀ x : List Bool, ∃ t,
      M.ComputesInTime x [MultiTapeTM.indicator (L : Set (List Bool)) x] t ∧
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ D * (x.length + 1) ^ f) :
    L ∈ PSPACE := by
  have hS : L ∈ SPACE (fun n => D * (n + 1) ^ f) := ⟨1, M, fun x => by
    obtain ⟨t, ht, hs⟩ := h x
    exact ⟨t, ht, by simpa using hs⟩⟩
  refine space_poly_subset_PSPACE f (SPACE.mono_const (a := D * 2 ^ f) (fun n => ?_) hS)
  calc
    D * (n + 1) ^ f ≤ D * (2 ^ f * (n ^ f + 1)) :=
      Nat.mul_le_mul_left D (succ_pow_le n f)
    _ = D * 2 ^ f * (n ^ f + 1) := (Nat.mul_assoc _ _ _).symm

/-- The body reserves three words and the three doubled clean-machine banks. -/
private def b2b_tapeCount (v i p : ℕ) : ℕ := 3 + (v + v) + (i + i) + (p + p)

/-- Tapes zero, one and two are respectively the certificate, buffer and verdict. -/
private def b2b_wordTape (v i p : ℕ) (j : Fin 3) : Fin (b2b_tapeCount v i p) :=
  ⟨j.val, by have := j.isLt; dsimp [b2b_tapeCount]; omega⟩

/-- Contiguous bank selection, with its explicit offset and size proof. -/
private def b2b_bankEmb (off m K : ℕ) (h : off + m ≤ K) : Fin m ↪ Fin K where
  toFun j := ⟨off + j.val, by have := j.isLt; omega⟩
  inj' := by
    intro a b hab
    apply Fin.ext
    have := congrArg Fin.val hab
    dsimp at this
    omega

/-- The virtual-input host's buffer selects tape one; its bank starts at tape three. -/
private def b2b_callEmb (v i p : ℕ) : Fin (1 + (v + v)) ↪ Fin (b2b_tapeCount v i p) where
  toFun j := ⟨if j.val = 0 then 1 else j.val + 2, by
    have := j.isLt
    dsimp [b2b_tapeCount]
    split_ifs <;> omega⟩
  inj' := by
    intro a b hab
    apply Fin.ext
    have hh := congrArg Fin.val hab
    dsimp at hh
    split_ifs at hh <;> omega

/-- A one-tape selection used for the setup's virtual rewind of the certificate. -/
private def b2b_singleEmb {K : ℕ} (i : Fin K) : Fin 1 ↪ Fin K :=
  ⟨fun _ => i, fun _ _ _ => Subsingleton.elim _ _⟩

/-- The six phases of the single reusable certificate test. -/
private inductive B2bTestPhase | anchor | identity | rewind | copy | call | verdict
  deriving DecidableEq, Fintype

/-- The test's dependent finite control, with no auxiliary dispatch machine. -/
private def b2b_testState (MV MI : FinTM Bool) : B2bTestPhase → Type
  | .anchor => Unit
  | .identity => LogProg.CleanSt MI.State MI.k ⊕ Unit
  | .rewind => B2bRewindState ⊕ Unit
  | .copy => SweepPhase
  | .call =>
      (((B2bRewindState ⊕ Unit) ⊕
        ((LogProg.CleanSt MV.State MV.k ⊕ Unit) ⊕ B2bRewindState)) × Bool) ⊕ Unit
  | .verdict => B2bVerdictState

private instance (MV MI : FinTM Bool) (i : B2bTestPhase) :
    Fintype (b2b_testState MV MI i) := by
  cases i <;> dsimp [b2b_testState] <;> infer_instance

private noncomputable instance (MV MI : FinTM Bool) (i : B2bTestPhase) :
    DecidableEq (b2b_testState MV MI i) := Classical.decEq _

/-- The test phases are exactly the public rows specified in route D. -/
private noncomputable def b2b_testPhases (MV MI MP : FinTM Bool) (j : B2bTestPhase) :
    MultiTapeTM (b2b_tapeCount MV.k MI.k MP.k) Bool (b2b_testState MV MI j) :=
  let K := b2b_tapeCount MV.k MI.k MP.k
  let U := b2b_wordTape MV.k MI.k MP.k 0
  let BUF := b2b_wordTape MV.k MI.k MP.k 1
  let CAP := b2b_wordTape MV.k MI.k MP.k 2
  match j with
  | .anchor => b2b_anchorTM K
  | .identity =>
      embedSilentRetTM
        (b2b_bankEmb (3 + (MV.k + MV.k)) (MI.k + MI.k) K
          (by dsimp [K, b2b_tapeCount]; omega))
        BUF (LogProg.cleanTM MI.tm MI.tm.q₀)
  | .rewind => embedEmitRetTM (Function.Embedding.refl _) (b2b_rewindTM K)
  | .copy => copyTM K U BUF
  | .call => embedSilentRetTM (b2b_callEmb MV.k MI.k MP.k) CAP
      (vhostEmitTM (b2b_hostedSource MV))
  | .verdict => b2b_verdictTM K CAP

/-- Test redirects, leaving both verdict exits live and unredirected. -/
private def b2b_testRedirect (MV MI : FinTM Bool) :
    (j : B2bTestPhase) → b2b_testState MV MI j → Option (Σ j, b2b_testState MV MI j)
  | .anchor, _ => some ⟨.identity, Sum.inl (.init MI.tm.q₀)⟩
  | .identity, Sum.inr _ => some ⟨.rewind, Sum.inl .start⟩
  | .rewind, Sum.inr _ => some ⟨.copy, .sweep⟩
  | .copy, .done => some ⟨.call, Sum.inl (Sum.inl (Sum.inl .start), true)⟩
  | .call, Sum.inr _ => some ⟨.verdict, .left⟩
  | _, _ => none

/-- One test definition, shared by every counted round and the final continuation. -/
private noncomputable def b2b_testTM (MV MI MP : FinTM Bool) :
    MultiTapeTM (b2b_tapeCount MV.k MI.k MP.k) Bool (Σ j, b2b_testState MV MI j) :=
  phaseHostTM (b2b_testPhases MV MI MP) ⟨.anchor, ()⟩ (b2b_testRedirect MV MI)

/-- A rejected test clears its buffer and increments its certificate. -/
private inductive B2bBodyPhase | test | clear | increment
  deriving DecidableEq, Fintype

/-- The body's control is the public phase host's dependent sum. -/
private def b2b_bodyState (MV MI : FinTM Bool) : B2bBodyPhase → Type
  | .test => Σ j, b2b_testState MV MI j
  | .clear => SweepPhase
  | .increment => FlagPhase

private instance (MV MI : FinTM Bool) (i : B2bBodyPhase) :
    Fintype (b2b_bodyState MV MI i) := by
  cases i <;> dsimp [b2b_bodyState] <;> infer_instance

private noncomputable instance (MV MI : FinTM Bool) (i : B2bBodyPhase) :
    DecidableEq (b2b_bodyState MV MI i) := by
  cases i <;> dsimp [b2b_bodyState] <;> infer_instance

/-- The body phases use the one test, the framed clear, and the framed increment. -/
private noncomputable def b2b_bodyPhases (MV MI MP : FinTM Bool) (j : B2bBodyPhase) :
    MultiTapeTM (b2b_tapeCount MV.k MI.k MP.k) Bool (b2b_bodyState MV MI j) :=
  match j with
  | .test => b2b_testTM MV MI MP
  | .clear => clearTM _ (b2b_wordTape MV.k MI.k MP.k 1)
  | .increment => incrementTM _ (b2b_wordTape MV.k MI.k MP.k 0)

/-- Return to the test's anchor only after a successful increment. -/
private def b2b_bodyRedirect (MV MI : FinTM Bool) :
    (j : B2bBodyPhase) → b2b_bodyState MV MI j → Option (Σ j, b2b_bodyState MV MI j)
  | .test, ⟨.verdict, .done false⟩ => some ⟨.clear, .sweep⟩
  | .clear, .done => some ⟨.increment, .run⟩
  | .increment, .done true => some ⟨.test, ⟨.anchor, ()⟩⟩
  | _, _ => none

/-- The sole loop body, assembled by `phaseHostTM`; the counter is external. -/
private noncomputable def b2b_bodyTM (MV MI MP : FinTM Bool) :
    MultiTapeTM (b2b_tapeCount MV.k MI.k MP.k) Bool (Σ j, b2b_bodyState MV MI j) :=
  phaseHostTM (b2b_bodyPhases MV MI MP) ⟨.test, ⟨.anchor, ()⟩⟩ (b2b_bodyRedirect MV MI)

/-- Setup, the counted loop, its final test, and the two final answers. -/
private inductive B2bHostPhase | setup | origin | counter | zero | rewind | loop | last
  | answer (b : Bool)
  deriving DecidableEq, Fintype

/-- The outer phase family's control types. -/
private def b2b_hostState (MV MI MP : FinTM Bool) : B2bHostPhase → Type
  | .setup => LogProg.CleanSt MP.State MP.k ⊕ Unit
  | .origin => (B2bRewindState × Bool) ⊕ Unit
  | .counter => SweepPhase
  | .zero => FlagPhase
  | .rewind => B2bRewindState ⊕ Unit
  | .loop => CounterLoopState (Σ j, b2b_bodyState MV MI j)
  | .last => Σ j, b2b_testState MV MI j
  | .answer _ => Fin 2

private instance (MV MI MP : FinTM Bool) (i : B2bHostPhase) :
    Fintype (b2b_hostState MV MI MP i) := by
  cases i <;> dsimp [b2b_hostState] <;> infer_instance

private noncomputable instance (MV MI MP : FinTM Bool) (i : B2bHostPhase) :
    DecidableEq (b2b_hostState MV MI MP i) := by
  cases i <;> dsimp [b2b_hostState] <;> infer_instance

/-- The host's phases, using only the brief's rows and sanctioned glue. -/
private noncomputable def b2b_hostPhases (MV MI MP : FinTM Bool) (j : B2bHostPhase) :
    MultiTapeTM (b2b_tapeCount MV.k MI.k MP.k + 1) Bool (b2b_hostState MV MI MP j) :=
  let K := b2b_tapeCount MV.k MI.k MP.k
  let U := (b2b_wordTape MV.k MI.k MP.k 0).castSucc
  match j with
  | .setup =>
      embedSilentRetTM
        (b2b_bankEmb (3 + (MV.k + MV.k) + (MI.k + MI.k)) (MP.k + MP.k) (K + 1)
          (by dsimp [K, b2b_tapeCount]; omega))
        U (LogProg.cleanTM MP.tm MP.tm.q₀)
  | .origin => embedEmitRetTM (b2b_singleEmb U) (vhostEmitTM (b2b_rewindTM 0))
  | .counter => copyTM (K + 1) U (Fin.last K)
  | .zero => incrementTM (K + 1) U
  | .rewind => embedEmitRetTM (Function.Embedding.refl _) (b2b_rewindTM (K + 1))
  | .loop => counterLoopTM (b2b_bodyTM MV MI MP)
      ⟨.test, ⟨.anchor, ()⟩⟩ (some ⟨.test, ⟨.verdict, .done true⟩⟩)
  | .last => embedEmitTM Fin.castSuccEmb (b2b_testTM MV MI MP)
  | .answer b => b2b_answerTM (K + 1) b

/-- Setup dispatch, both loop continuations, and the final verdict dispatch. -/
private def b2b_hostRedirect (MV MI MP : FinTM Bool) :
    (j : B2bHostPhase) → b2b_hostState MV MI MP j → Option (Σ j, b2b_hostState MV MI MP j)
  | .setup, Sum.inr _ => some ⟨.origin, Sum.inl (.start, true)⟩
  | .origin, Sum.inr _ => some ⟨.counter, .sweep⟩
  | .counter, .done => some ⟨.zero, .run⟩
  | .zero, .done false => some ⟨.rewind, Sum.inl .start⟩
  | .rewind, Sum.inr _ => some ⟨.loop, .dec .run⟩
  | .loop, .done => some ⟨.last, ⟨.anchor, ()⟩⟩
  | .loop, .escape => some ⟨.answer true, (0 : Fin 2)⟩
  | .last, ⟨.verdict, .done b⟩ => some ⟨.answer b, (0 : Fin 2)⟩
  | _, _ => none

/-- The concrete certificate-cycling decider. `counterLoopTM` is its only loop host. -/
private noncomputable def b2b_host (MV MI MP : FinTM Bool) : FinTM Bool where
  k := b2b_tapeCount MV.k MI.k MP.k + 1
  State := Σ j, b2b_hostState MV MI MP j
  tm := phaseHostTM (b2b_hostPhases MV MI MP)
    ⟨.setup, Sum.inl (.init MP.tm.q₀)⟩ (b2b_hostRedirect MV MI MP)

/-- The fixed-window ledger is polynomial, independently of the number of trials.

**Proof sketch.** Use degree `(c+1)(e+1)`, which dominates the linear setup,
certificate degree, and the verifier's composed degree. Bound all tape radii by
their sum; the total of `K` intervals of radius that sum is at most `K(2R+1)`.
This arithmetic introduces no factor depending on the number of certificates. -/
private theorem b2b_ledger_bound (C c cV e cI cP K : ℕ) :
    ∃ D f : ℕ, ∀ n : ℕ,
      K * (2 * (n + C * (n + 1) ^ c + cV * ((n + C * (n + 1) ^ c) ^ e + 1) +
        cI + cP * (n + 1) + 1) + 1) ≤ D * (n + 1) ^ f := by
  let f := (c + 1) * (e + 1)
  let A := (C + 1) + cV * ((C + 1) ^ e + 1) + cI + cP + 1
  refine ⟨K * (2 * A + 1), f, fun n => ?_⟩
  let R := (n + 1) ^ f
  have hf : c + 1 ≤ f := Nat.le_mul_of_pos_right _ (Nat.succ_pos e)
  have hfe : (c + 1) * e ≤ f := Nat.mul_le_mul_left _ (by omega)
  have hR : 1 ≤ R := Nat.one_le_pow _ _ (by omega)
  have hlin : n + 1 ≤ R := by
    simpa only [pow_one] using Nat.pow_le_pow_right (Nat.succ_pos n)
      (show 1 ≤ f by omega)
  have hsmall : n + 1 ≤ (n + 1) ^ (c + 1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (Nat.succ_pos n)
      (show 1 ≤ c + 1 by omega)
  have hcert : n + C * (n + 1) ^ c ≤ (C + 1) * (n + 1) ^ (c + 1) := by
    calc
      _ ≤ (n + 1) ^ (c + 1) + C * (n + 1) ^ (c + 1) :=
        Nat.add_le_add (by omega) (Nat.mul_le_mul_left C
          (Nat.pow_le_pow_right (Nat.succ_pos n) (by omega)))
      _ = _ := by ring
  have hcert' : n + C * (n + 1) ^ c ≤ (C + 1) * R :=
    hcert.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos n) hf))
  have hver : (n + C * (n + 1) ^ c) ^ e ≤ (C + 1) ^ e * R := by
    calc
      _ ≤ ((C + 1) * (n + 1) ^ (c + 1)) ^ e := Nat.pow_le_pow_left hcert e
      _ = (C + 1) ^ e * (n + 1) ^ ((c + 1) * e) := by rw [mul_pow, ← pow_mul]
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos n) hfe)
  have hspace : cV * ((n + C * (n + 1) ^ c) ^ e + 1) ≤
      cV * ((C + 1) ^ e + 1) * R := by
    calc
      _ ≤ cV * ((C + 1) ^ e * R + R) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add hver hR)
      _ = _ := by ring
  have hsum : n + C * (n + 1) ^ c + cV * ((n + C * (n + 1) ^ c) ^ e + 1) +
      cI + cP * (n + 1) + 1 ≤ A * R := by
    calc
      _ ≤ (C + 1) * R + cV * ((C + 1) ^ e + 1) * R + cI * R + cP * R + R :=
        Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hcert' hspace)
          (Nat.le_mul_of_pos_right _ (by omega))) (Nat.mul_le_mul_left _ hlin)) hR
      _ = _ := by dsimp [A]; ring
  calc
    _ ≤ K * (2 * (A * R) + R) :=
      Nat.mul_le_mul_left K (Nat.add_le_add (Nat.mul_le_mul_left 2 hsum) hR)
    _ = _ := by dsimp [R]; ring

/-- The assembled host decides the exact certificate predicate within fixed windows.

**Proof sketch.** First apply the five setup rows: capture the unary polynomial,
virtually rewind it, copy it to the last tape, overflow-increment the certificate
to zeros, and rewind the native input. For the shared test, capture the identity
call, rewind, apply `copyTM_run_ofCfg` and `b2b_buffer_concat`, run the verifier
under `vhostEmitTM`, and erase/read the captured bit. Use `exists_first_halt` at
each halting source, the returning embeddings for live exits, and `phaseHostTM_run`
with `b2b_dispatch_retag` for every dispatch. One round lemma covers both verdicts;
on rejection, clear the buffer and apply the framed increment. Choose the exact
round durations classically. Apply `counterLoopTM_run_escape` to the first
accepting counted round, or `counterLoopTM_run_done` and the final shared test.
`b2b_counter_value`, `b2b_certificate_orbit`, and `b2b_verifies_iff` identify the
enumerated predicate, including width zero. The loop trajectory clauses reduce
all body-head positions to a single round's positions; the row trajectories keep
them within the seven fixed windows of route H. Their common enclosing radius is
the sum below. `Finset.card_le_card` and `Int.card_Icc`, summed over the fixed
number of tapes, give the ledger. Only the final `b2b_answer_run` emits physically.

Continuation frontier: the concrete host and component lemmas above are present;
the composed round proof, setup proof and global trajectory proof remain open. -/
private theorem b2b_host_contract (C c e cV cI cP : ℕ) (V : Language Bool)
    (MV MI MP : FinTM Bool)
    (hV : ∀ y : List Bool,
      LogProg.CleanRun (LogProg.cleanTM MV.tm MV.tm.q₀)
        (LogProg.CleanSt.init MV.tm.q₀) y
        (MultiTapeTM.indicator (V : Set (List Bool)) y) (cV * (y.length ^ e + 1)))
    (hI : MI.ComputesFunInTime id (fun n => cI * (n + 1)))
    (hIs : ∀ (x : List Bool) (t : ℕ), MI.tm.spaceUsed (MI.tm.initCfg x) t ≤ cI)
    (hP : MP.ComputesFunInTime
      (fun x => List.replicate (C * (x.length + 1) ^ c) true)
      (fun n => cP * (n + 1) ^ (c + 1)))
    (hPs : ∀ (x : List Bool) (t : ℕ), MP.tm.spaceUsed (MP.tm.initCfg x) t ≤ cP * (x.length + 1))
    (x : List Bool) :
    ∃ t : ℕ,
      (b2b_host MV MI MP).ComputesInTime x
        [MultiTapeTM.indicator
          {z : List Bool | ∃ u, u.length = C * (z.length + 1) ^ c ∧ z ++ u ∈ V} x] t ∧
      (b2b_host MV MI MP).tm.spaceUsed ((b2b_host MV MI MP).tm.initCfg x) t ≤
        (b2b_tapeCount MV.k MI.k MP.k + 1) *
          (2 * (x.length + C * (x.length + 1) ^ c +
            cV * ((x.length + C * (x.length + 1) ^ c) ^ e + 1) +
            cI + cP * (x.length + 1) + 1) + 1) := by
  sorry

/-- **Certificates can be cycled through in polynomial space**: `NP ⊆ PSPACE`.
[AB09, Example 4.6: "a similar idea of cycling through all potential
certificates applies to any NP language"]

**Proof sketch.** Let `L ∈ NP` with verifier language `V ∈ P` and certificate
length `C·(n+1)^c` (`Complexity.mem_NP_iff`-shape data). Fill obligations,
named for the brief: (i) a certificate enumerator holding the current
certificate `u` on a work tape and stepping it in place by fixed-width binary
increment (`incrementTM`, P11/§12 R3 — the space-annotated form), never using
more than `C·(n+1)^c + O(1)` cells; (ii) for each `u`, a run of `V`'s decider
on the **virtual input** `x ++ u` assembled from the input tape and the
certificate tape (the virtual-input idiom of
`TCSlib.Complexity.TuringMachine.UniversalStartup`), with the decider's space
bounded through `Complexity.DTIME_subset_SPACE` applied to `V`'s polynomial
time bound — this is where the run is *re-executed* rather than stored, the
space-reuse point of [AB09, Example 4.6]; (iii) accept as soon as one `u`
verifies, reject after the last. Total space: certificate + decider + control,
all polynomial in `n`. (The decider-subroutine space composition is a §12
space-clause consumer — `machine-library-design.md` §12, R1/R3.)

**Fill appendix (B2b).** The prescribed assembly uses `counterLoopTM` for the
round counter, `phaseHostTM` for dispatch, and `LogProg.cleanTM_run` for reset.
The virtual input is a copy-assembled buffer: capture `x`, then append the
certificate using `copyTM`. This is the optional copying implementation of
P4.1 Question 5. The counted rounds test all but the final certificate; a
continuation tests that final word, including the sole empty word at width zero. -/
theorem NP_subset_PSPACE : NP ⊆ PSPACE := by
  classical
  rintro L ⟨C, c, V, hV, hL⟩
  obtain ⟨e, cV, MV, hMV⟩ := b2b_clean_verifier V hV
  obtain ⟨MI, cI, hI, hIs⟩ := FinTM.computesFunInTime_id_spaceUsed
  obtain ⟨MP, cP, hP, hPs⟩ := FinTM.computesFunInTime_polyUnary_spaceUsed C c
  obtain ⟨D, f, hledger⟩ := b2b_ledger_bound C c cV e cI cP
    (b2b_tapeCount MV.k MI.k MP.k + 1)
  apply b2b_mem_PSPACE_of_ledger L (b2b_host MV MI MP) D f
  intro x
  obtain ⟨t, ht, hs⟩ := b2b_host_contract C c e cV cI cP V MV MI MP hMV hI hIs hP hPs x
  have hlang : (L : Set (List Bool)) =
      {z : List Bool | ∃ u, u.length = C * (z.length + 1) ^ c ∧ z ++ u ∈ V} := Set.ext hL
  rw [← hlang] at ht
  exact ⟨t, ht, hs.trans (hledger x.length)⟩

/-- `3SAT` is decidable in polynomial space. [AB09, Example 4.6]

**Proof sketch.** `Complexity.SAT3_mem_NP` with `Complexity.NP_subset_PSPACE`.
Delivered strength: **polynomial** space (the route through arbitrary `NP`
membership fixes no degree); the book example's sharper linear-space direct
machine is not claimed (P4.1 round 1, note 9). -/
theorem SAT3_mem_PSPACE : SAT3 ∈ PSPACE := by
  exact NP_subset_PSPACE SAT3_mem_NP

end Complexity
