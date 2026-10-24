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

## Main results (proved)

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

/-- A cleaned source's silent embedding has a single captured word and otherwise
exactly the ambient frame. This pure configuration identity supplies both the
startup and final configurations of setup and identity capture.

**Proof sketch.** On the selected banks use the embedding's tape and head
projections; elsewhere use the frame theorem. At the capture tape the captured-output
entry and its head at the word's length are `Turing.embedSilentCfg_cap`. -/
private theorem b2b_capture_shape {k m : ℕ} {S : Type} {x : List Bool}
    (M : MultiTapeTM m Bool S) (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι) (tapes : Fin k → ℤ → Option Bool)
    (hbank : ∀ a, tapes (ι a) = fun _ => none) (s : S)
    (p : Fin (x.length + 2)) (y : List Bool) :
    embedSilentCfg ι cap tapes (fun _ => 0) [] []
        { Cfg.init s x with inputPos := p, output := y } =
      { Cfg.init (k := k) s x with
        inputPos := p,
        workTapes := Function.update tapes cap (FinTM.bufferTape y),
        workTapePos := Function.update (fun _ => (0 : ℤ)) cap (y.length : ℤ) } := by
  classical
  let d : Cfg m Bool S x := { Cfg.init s x with inputPos := p, output := y }
  apply Cfg.ext <;> try rfl
  · funext j
    change (embedSilentCfg ι cap tapes (fun _ => 0) [] [] d).workTapes j =
      Function.update tapes cap (FinTM.bufferTape y) j
    by_cases hc : j = cap
    · subst j
      rw [(embedSilentCfg_cap ι cap hcap tapes (fun _ => 0) [] [] d).1, Function.update_self]
      rfl
    · by_cases hj : j ∈ Set.range ι
      · obtain ⟨a, rfl⟩ := hj
        rw [embedSilentCfg_selected_tape, Function.update_of_ne hc, hbank]
        rfl
      · rw [Function.update_of_ne hc]
        exact (embedSilentTM_frame ι cap hcap M tapes (fun _ => 0) [] [] d 0).1 j hj hc |>.1
  · funext j
    change (embedSilentCfg ι cap tapes (fun _ => 0) [] [] d).workTapePos j =
      Function.update (fun _ => (0 : ℤ)) cap (y.length : ℤ) j
    by_cases hc : j = cap
    · subst j
      rw [(embedSilentCfg_cap ι cap hcap tapes (fun _ => 0) [] [] d).2, Function.update_self]
      rfl
    · rw [Function.update_of_ne hc]
      by_cases hj : j ∈ Set.range ι
      · obtain ⟨a, rfl⟩ := hj
        exact embedSilentCfg_selected_pos ι cap tapes (fun _ => 0) [] [] d a
      · exact (embedSilentTM_frame ι cap hcap M tapes (fun _ => 0) [] [] d 0).1 j hj hc |>.2

/-- The two clean captures (unary setup and identity) share one through-halt
contract, including the fixed capture interval and the clean bank radius.

**Proof sketch.** Apply the existing cleaned-run theorem, take its first halt,
and use the returning silent embedding. Selected heads inherit the clean
bound. The capture head is the length of an output prefix of the final word;
unselected heads are fixed by the public frame theorem. -/
private theorem b2b_clean_capture {k : ℕ} (M : FinTM Bool)
    (ι : Fin (M.k + M.k) ↪ Fin k) (cap : Fin k) (hcap : cap ∉ Set.range ι)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (x y : List Bool) (t s : ℕ) (ht : M.ComputesInTime x y t)
    (hs : M.tm.spaceUsed (M.tm.initCfg x) t ≤ s) :
    let N := LogProg.cleanTM M.tm M.tm.q₀
    let c₀ : Cfg (M.k + M.k) Bool (LogProg.CleanSt M.State M.k) x :=
    Cfg.init (LogProg.CleanSt.init M.tm.q₀) x
    let E := embedSilentRetTM ι cap N
    let d₀ := (embedSilentCfg ι cap tapes heads [] [] c₀).mapState Sum.inl
    ∃ T : ℕ, ∃ p : Fin (x.length + 2),
      E.runFrom d₀ T =
        { embedSilentCfg ι cap tapes heads [] []
            { c₀ with inputPos := p, output := y } with state := some (Sum.inr ()) } ∧
      (∀ u < T, (E.runFrom d₀ u).state ≠ some (Sum.inr ())) ∧
      (∀ u ≤ T, (E.runFrom d₀ u).state ≠ none ∧ (E.runFrom d₀ u).output = []) ∧
      (∀ u ≤ T, ∀ j,
        if j = cap then (E.runFrom d₀ u).workTapePos j ∈ Finset.Icc 0 (y.length : ℤ)
        else if j ∈ Set.range ι then |(E.runFrom d₀ u).workTapePos j| ≤ (s : ℤ)
        else (E.runFrom d₀ u).workTapePos j = heads j) := by
  classical
  dsimp only
  let N := LogProg.cleanTM M.tm M.tm.q₀
  let c₀ : Cfg (M.k + M.k) Bool (LogProg.CleanSt M.State M.k) x :=
    Cfg.init (LogProg.CleanSt.init M.tm.q₀) x
  obtain ⟨T₀, hhalt, hout, htapes, hheads, hbound⟩ := b2b_clean_run M x y t s ht hs
  obtain ⟨T, hT, hlive, hfirst⟩ := MultiTapeTM.exists_first_halt N c₀ hhalt
  have hfinal : N.runFrom c₀ T =
      { c₀ with state := none, inputPos := (N.runFrom c₀ T₀).inputPos, output := y } := by
    rw [hfirst]
    apply Cfg.ext
    · exact hhalt
    · rfl
    · exact htapes
    · exact hheads
    · exact hout
  have he := embedSilentRetTM_run ι cap hcap N tapes heads [] [] c₀ T
    (by simp [c₀, Cfg.init]) hlive (by rw [hfirst]; exact hhalt)
  have hpos (d : Cfg (M.k + M.k) Bool (LogProg.CleanSt M.State M.k) x) :
      (embedSilentCfg ι cap tapes heads [] [] d).workTapePos cap = (d.output.length : ℤ) := by
    simp only [embedSilentCfg]
    split
    · rename_i a ha
      have hh := List.find?_some (p := fun j : Fin (M.k + M.k) => decide (ι j = cap)) ha
      exact False.elim (hcap ⟨a, of_decide_eq_true hh⟩)
    · simp
  refine ⟨T, (N.runFrom c₀ T₀).inputPos, ?_, he.2.2, ?_, ?_⟩
  · rw [he.2.1, hfinal]
    rfl
  · intro u hu
    rcases lt_or_eq_of_le hu with hu' | rfl
    · rw [he.1 u hu']
      constructor
      · simpa [Cfg.mapState, embedSilentCfg, Cfg.Halted] using hlive u hu'
      · rfl
    · rw [he.2.1]
      exact ⟨by simp, rfl⟩
  · intro u hu j
    have hp : ((embedSilentRetTM ι cap N).runFrom
        ((embedSilentCfg ι cap tapes heads [] [] c₀).mapState Sum.inl) u).workTapePos =
        (embedSilentCfg ι cap tapes heads [] [] (N.runFrom c₀ u)).workTapePos := by
      rcases lt_or_eq_of_le hu with hu' | rfl
      · rw [he.1 u hu']; rfl
      · rw [he.2.1]
    rw [hp]
    by_cases hj : j = cap
    · subst j
      simp only [ite_true, hpos, Finset.mem_Icc]
      have houtlen := (N.output_prefix c₀ (hu.trans hT)).length_le
      change (N.runFrom c₀ T₀).output = y at hout
      rw [hout] at houtlen
      constructor <;> omega
    · simp only [hj, ite_false]
      by_cases hsel : j ∈ Set.range ι
      · obtain ⟨a, rfl⟩ := hsel
        rw [if_pos ⟨a, rfl⟩, embedSilentCfg_selected_pos]
        exact hbound u (hu.trans hT) a
      · rw [if_neg hsel]
        exact (embedSilentTM_frame ι cap hcap N tapes heads [] [] (N.runFrom c₀ u) 0).1
          j hsel hj |>.2

/-- Setup phase S1 captures the unary certificate width, cleans its bank, and
silently dispatches to the virtual origin finder with the capture head at the
word's right blank. Its entire trajectory has a fixed, input-dependent radius.

**Proof sketch.** Instantiate the shared clean-capture contract with the setup
bank, identify the blank startup by the pure capture identity, and apply the
public phase-host lemma at the first live return. The final dispatch moves no
head; every earlier head belongs to the shared capture trajectory. -/
private theorem b2b_setup_capture (MV MI MP : FinTM Bool) (x y : List Bool)
    (t s : ℕ) (ht : MP.ComputesInTime x y t)
    (hs : MP.tm.spaceUsed (MP.tm.initCfg x) t ≤ s) :
    let K := b2b_tapeCount MV.k MI.k MP.k
    let U := (b2b_wordTape MV.k MI.k MP.k 0).castSucc
    ∃ T : ℕ, ∃ p : Fin (x.length + 2),
      (b2b_host MV MI MP).tm.runFrom ((b2b_host MV MI MP).tm.initCfg x) T =
        { Cfg.init (k := K + 1) (⟨B2bHostPhase.origin, Sum.inl (.start, true)⟩ :
            Σ j, b2b_hostState MV MI MP j) x with
          inputPos := p,
          workTapes := Function.update (fun _ _ => none) U (FinTM.bufferTape y),
          workTapePos := Function.update (fun _ => (0 : ℤ)) U (y.length : ℤ) } ∧
      ∀ u ≤ T, ∀ j,
        |((b2b_host MV MI MP).tm.runFrom ((b2b_host MV MI MP).tm.initCfg x) u).workTapePos j|
          ≤ (s + y.length : ℕ) := by
  classical
  dsimp only
  let K := b2b_tapeCount MV.k MI.k MP.k
  let U := (b2b_wordTape MV.k MI.k MP.k 0).castSucc
  let ι := b2b_bankEmb (3 + (MV.k + MV.k) + (MI.k + MI.k)) (MP.k + MP.k) (K + 1)
    (by dsimp [K, b2b_tapeCount]; omega)
  have hcap : U ∉ Set.range ι := by
    rintro ⟨a, ha⟩
    have := congrArg Fin.val ha
    dsimp [ι, U, b2b_bankEmb, b2b_wordTape] at this
    omega
  let N := LogProg.cleanTM MP.tm MP.tm.q₀
  let c₀ : Cfg (MP.k + MP.k) Bool (LogProg.CleanSt MP.State MP.k) x :=
    Cfg.init (LogProg.CleanSt.init MP.tm.q₀) x
  obtain ⟨T, p, hrun, hcut, _, hheads⟩ :=
    b2b_clean_capture MP ι U hcap (fun _ _ => none) (fun _ => 0) x y t s ht hs
  let d₀ : Cfg (K + 1) Bool (b2b_hostState MV MI MP .setup) x :=
    Cfg.init (Sum.inl (.init MP.tm.q₀)) x
  let d₁ : Cfg (K + 1) Bool (b2b_hostState MV MI MP .setup) x :=
    { Cfg.init (k := K + 1) (Sum.inr ()) x with
      inputPos := p,
      workTapes := Function.update (fun _ _ => none) U (FinTM.bufferTape y),
      workTapePos := Function.update (fun _ => (0 : ℤ)) U (y.length : ℤ) }
  have hstart : (embedSilentCfg ι U (fun _ _ => none) (fun _ => 0) [] [] c₀).mapState
      Sum.inl = d₀ := by
    have h := b2b_capture_shape N ι U hcap (fun _ _ => none) (fun _ => rfl)
      (LogProg.CleanSt.init MP.tm.q₀) (1 : Fin (x.length + 2)) []
    change embedSilentCfg ι U (fun _ _ => none) (fun _ => 0) [] [] c₀ = _ at h
    rw [h]
    simp [d₀, Cfg.init, Cfg.mapState]
  have hend : { embedSilentCfg ι U (fun _ _ => none) (fun _ => 0) [] []
        { c₀ with inputPos := p, output := y } with state := some (Sum.inr ()) } = d₁ := by
    rw [b2b_capture_shape N ι U hcap (fun _ _ => none) (fun _ => rfl)]
    rfl
  rw [hstart, hend] at hrun
  rw [hstart] at hcut hheads
  have hp := phaseHostTM_run (b2b_hostPhases MV MI MP)
    ⟨.setup, Sum.inl (.init MP.tm.q₀)⟩ (b2b_hostRedirect MV MI MP) .setup
    d₀ d₁ T hrun (Sum.inr ()) rfl ⟨.origin, Sum.inl (.start, true)⟩ rfl (by
      intro u hu q hq
      cases q with
      | inl a => rfl
      | inr a => exact False.elim (hcut u hu (by simpa using hq)))
  have hinit : d₀.mapState (Sigma.mk B2bHostPhase.setup) =
      (b2b_host MV MI MP).tm.initCfg x := rfl
  refine ⟨T + 1, p, ?_, ?_⟩
  · simpa only [hinit, b2b_host, b2b_dispatch_retag, d₁, Cfg.mapState, Cfg.init,
      Option.map_some] using hp.2
  · intro u hu j
    change |((phaseHostTM (b2b_hostPhases MV MI MP)
      ⟨.setup, Sum.inl (.init MP.tm.q₀)⟩ (b2b_hostRedirect MV MI MP)).runFrom
      (d₀.mapState (Sigma.mk B2bHostPhase.setup)) u).workTapePos j| ≤ _
    by_cases hu' : u ≤ T
    · rw [hp.1 u hu']
      have hh := hheads u hu' j
      by_cases hj : j = U
      · subst j
        simp only [ite_true, Finset.mem_Icc] at hh
        change |((b2b_hostPhases MV MI MP .setup).runFrom d₀ u).workTapePos U| ≤ _
        rw [abs_of_nonneg hh.1]
        exact hh.2.trans (by omega)
      · simp only [hj, ite_false] at hh
        split_ifs at hh with hsel
        · exact hh.trans (by omega)
        · change |((b2b_hostPhases MV MI MP .setup).runFrom d₀ u).workTapePos j| ≤ _
          rw [hh]; simp only [abs_zero]; omega
    · have heq : u = T + 1 := by omega
      rw [heq, hp.2]
      change |Function.update (fun _ => (0 : ℤ)) U (y.length : ℤ) j| ≤ _
      by_cases hj : j = U
      · subst j
        rw [Function.update_self, abs_of_nonneg (Nat.cast_nonneg _)]
        omega
      · rw [Function.update_of_ne hj]
        simp only [abs_zero]
        omega

/-- Relocating the zero-bank virtual rewind selects exactly its buffered word;
all other tapes and heads are blank. This is a pure configuration identity.

**Proof sketch.** At the selected tape use the public embedding projections;
at every other tape use the public frame theorem at time zero. -/
private theorem b2b_origin_shape {k : ℕ} {x y : List Bool} (U : Fin k)
    (c : Cfg 0 Bool B2bRewindState y) (b : Bool) (p : Fin (x.length + 2)) :
    embedEmitCfg (b2b_singleEmb U) (fun _ _ => none) (fun _ => 0) [] (vhostCfg c b p []) =
      { state := c.state.map (fun q => (q, b)), inputPos := p,
        workTapes := Function.update (fun _ _ => none) U (FinTM.bufferTape y),
        workTapePos := Function.update (fun _ => (0 : ℤ)) U ((c.inputPos.val : ℤ) - 1),
        output := c.output } := by
  classical
  let d := vhostCfg c b p []
  have hn (j : Fin k) (h : j ≠ U) : j ∉ Set.range (b2b_singleEmb U) := by
    rintro ⟨a, ha⟩
    exact h ha.symm
  apply Cfg.ext <;> try rfl
  · funext j
    change (embedEmitCfg (b2b_singleEmb U) (fun _ _ => none) (fun _ => 0) [] d).workTapes j =
      Function.update (fun _ _ => none) U (FinTM.bufferTape y) j
    by_cases hj : j = U
    · subst j
      have hp := embedEmitCfg_selected_tape (b2b_singleEmb U) (fun _ _ => none)
        (fun _ => 0) [] d (vhostBuffer 0)
      simpa [b2b_singleEmb, d, vhostCfg, vhostBuffer] using hp
    · rw [Function.update_of_ne hj]
      exact (embedEmitTM_frame (b2b_singleEmb U) (vhostEmitTM (b2b_rewindTM 0))
        (fun _ _ => none) (fun _ => 0) [] d 0).1 j (hn j hj) |>.1
  · funext j
    change (embedEmitCfg (b2b_singleEmb U) (fun _ _ => none) (fun _ => 0) [] d).workTapePos j =
      Function.update (fun _ => (0 : ℤ)) U ((c.inputPos.val : ℤ) - 1) j
    by_cases hj : j = U
    · subst j
      have hp := embedEmitCfg_selected_pos (b2b_singleEmb U) (fun _ _ => none)
        (fun _ => 0) [] d (vhostBuffer 0)
      simpa [b2b_singleEmb, d, vhostCfg, vhostBuffer] using hp
    · rw [Function.update_of_ne hj]
      exact (embedEmitTM_frame (b2b_singleEmb U) (vhostEmitTM (b2b_rewindTM 0))
        (fun _ _ => none) (fun _ => 0) [] d 0).1 j (hn j hj) |>.2

/-- S2 returns the captured word's work head to zero without changing that
word or the native input position; all prefixes stay in the word's fixed window.

**Proof sketch.** Apply the already proved virtual rewind and take its first
halt. The returning forwarding embedding supplies a live exit and no earlier
exit. Its prefix equality transports the public virtual-buffer window; other
heads stay fixed by the embedding frame theorem. -/
private theorem b2b_origin_run {k : ℕ} {x : List Bool} (U : Fin k)
    (y : List Bool) (p : Fin (x.length + 2)) :
    let E := embedEmitRetTM (b2b_singleEmb U) (vhostEmitTM (b2b_rewindTM 0))
    let d₀ : Cfg k Bool ((B2bRewindState × Bool) ⊕ Unit) x :=
      { Cfg.init (k := k) (Sum.inl (.start, true)) x with
        inputPos := p,
        workTapes := Function.update (fun _ _ => none) U (FinTM.bufferTape y),
        workTapePos := Function.update (fun _ => (0 : ℤ)) U (y.length : ℤ) }
    let d₁ : Cfg k Bool ((B2bRewindState × Bool) ⊕ Unit) x :=
      { Cfg.init (k := k) (Sum.inr ()) x with
        inputPos := p,
        workTapes := Function.update (fun _ _ => none) U (FinTM.bufferTape y) }
    ∃ T : ℕ, E.runFrom d₀ T = d₁ ∧
      (∀ u < T, (E.runFrom d₀ u).state ≠ some (Sum.inr ())) ∧
      ∀ u ≤ T, ∀ j, if j = U then
        (E.runFrom d₀ u).workTapePos j ∈ Finset.Icc (-1 : ℤ) (y.length : ℤ)
        else (E.runFrom d₀ u).workTapePos j = 0 := by
  classical
  dsimp only
  let c : Cfg 0 Bool B2bRewindState y :=
    { Cfg.init .start y with inputPos := ⟨y.length + 1, by omega⟩ }
  have htag : FinTM.VirtualTag c.inputPos true := by
    simp [FinTM.VirtualTag, c]
  let d := vhostCfg c true p []
  let N := vhostEmitTM (b2b_rewindTM 0)
  obtain ⟨r, _, b', hrun, _, _⟩ := b2b_vhost_rewind c rfl true htag p []
  have hh : (N.runFrom d r).state = none := by rw [hrun]; rfl
  obtain ⟨T, _, hlive, hfirst⟩ := MultiTapeTM.exists_first_halt N d hh
  have hstop := hfirst.trans hrun
  have he := embedEmitRetTM_run (b2b_singleEmb U) N
    (fun _ _ => none) (fun _ => 0) [] d T (by simp [d, vhostCfg, c, Cfg.init])
    hlive (by rw [hfirst]; exact hh)
  have hstart : (embedEmitCfg (b2b_singleEmb U) (fun _ _ => none) (fun _ => 0) [] d).mapState
      (Sum.inl : _ → (B2bRewindState × Bool) ⊕ Unit) = { Cfg.init (k := k) (Sum.inl (.start, true)) x with
        inputPos := p,
        workTapes := Function.update (fun _ _ => none) U (FinTM.bufferTape y),
        workTapePos := Function.update (fun _ => (0 : ℤ)) U (y.length : ℤ) } := by
    rw [b2b_origin_shape]
    simp [c, Cfg.init, Cfg.mapState]
  refine ⟨T, ?_, ?_, ?_⟩
  · have h := he.2.1
    rw [hstart, hstop, b2b_origin_shape] at h
    simpa [c, Cfg.init] using h
  · simpa only [hstart] using he.2.2
  · intro u hu j
    have hp : ((embedEmitRetTM (b2b_singleEmb U) N).runFrom
        ((embedEmitCfg (b2b_singleEmb U) (fun _ _ => none) (fun _ => 0) [] d).mapState Sum.inl)
        u).workTapePos =
        (embedEmitCfg (b2b_singleEmb U) (fun _ _ => none) (fun _ => 0) [] (N.runFrom d u)).workTapePos := by
      rcases lt_or_eq_of_le hu with hu' | rfl
      · rw [he.1 u hu']; rfl
      · rw [he.2.1]
    rw [hstart] at hp
    rw [hp]
    by_cases hj : j = U
    · subst j
      simp only [ite_true]
      have hpos := embedEmitCfg_selected_pos (b2b_singleEmb U) (fun _ _ => none)
        (fun _ => 0) [] (N.runFrom d u) (vhostBuffer 0)
      rw [show b2b_singleEmb U (vhostBuffer 0) = U from rfl] at hpos
      rw [hpos]
      exact vhostCfg_buffer_head_mem (b2b_rewindTM 0) c true htag p [] u
    · simp only [hj, ite_false]
      have hn : j ∉ Set.range (b2b_singleEmb U) := by
        rintro ⟨a, ha⟩
        exact hj ha.symm
      exact (embedEmitTM_frame (b2b_singleEmb U) N (fun _ _ => none) (fun _ => 0)
        [] (N.runFrom d u) 0).1 j hn |>.2

/-- The native rewind becomes a live return through the prescribed identity
embedding, preserving every work head throughout. Both native rewind phases use
this same instance of the public first-halt and returning-embedding contracts. -/
private theorem b2b_rewind_return {k : ℕ} {x : List Bool}
    (c : Cfg k Bool B2bRewindState x) (hs : c.state = some .start) :
    let E := embedEmitRetTM (Function.Embedding.refl _) (b2b_rewindTM k)
    ∃ T : ℕ, E.runFrom (c.mapState Sum.inl) T =
        { c with state := some (Sum.inr ()), inputPos := 1 } ∧
      (∀ u < T, (E.runFrom (c.mapState Sum.inl) u).state ≠ some (Sum.inr ())) ∧
      ∀ u ≤ T, (E.runFrom (c.mapState Sum.inl) u).workTapePos = c.workTapePos := by
  obtain ⟨r, _, hrun, hheads⟩ := b2b_rewind_run c hs
  obtain ⟨T, hTr, hlive, hfirst⟩ := MultiTapeTM.exists_first_halt (b2b_rewindTM k) c
    (show ((b2b_rewindTM k).runFrom c r).state = none by rw [hrun])
  have he := embedEmitRetTM_run (Function.Embedding.refl _) (b2b_rewindTM k)
    c.workTapes c.workTapePos [] c T (by rw [hs]; simp) hlive (by rw [hfirst, hrun])
  simp only [b2b_embed_refl] at he
  refine ⟨T, ?_, he.2.2, ?_⟩
  · rw [he.2.1, hfirst, hrun]
  · intro u hu
    rcases lt_or_eq_of_le hu with hu' | rfl
    · rw [he.1 u hu']
      exact hheads u (hu.trans hTr)
    · rw [he.2.1, hfirst, hrun]

/-- The setup seam has words only on the certificate and final counter tape,
with every head at its fixed origin and no physical output. -/
private def b2b_setupCfg {S : Type} {x : List Bool} (MV MI MP : FinTM Bool)
    (q : S) (p : Fin (x.length + 2)) (u w : List Bool) :
    Cfg (b2b_tapeCount MV.k MI.k MP.k + 1) Bool S x :=
  { Cfg.init q x with
    inputPos := p,
    workTapes := fun j => if j = (b2b_wordTape MV.k MI.k MP.k 0).castSucc then
      FinTM.bufferTape u else if j = Fin.last (b2b_tapeCount MV.k MI.k MP.k) then
      FinTM.bufferTape w else fun _ => none }

/-- S3 and S4 install the all-true round counter and the all-false first
certificate, then dispatch to S5. They also cover certificate width zero.

**Proof sketch.** The framed copy installs the counter. The all-true certificate
has no fixed-width successor, so the framed overflow increment replaces it by
zeros. Use the public phase-host contract for the two silent dispatches. Each
row's trajectory stays between minus one and the fixed certificate width. -/
private theorem b2b_seed_run (MV MI MP : FinTM Bool) {x : List Bool}
    (p : Fin (x.length + 2)) (Q : ℕ) :
    let H := (b2b_host MV MI MP).tm
    let d₀ := b2b_setupCfg MV MI MP (⟨B2bHostPhase.counter, SweepPhase.sweep⟩ :
      Σ j, b2b_hostState MV MI MP j) p (List.replicate Q true) []
    let d₁ := b2b_setupCfg MV MI MP (⟨B2bHostPhase.rewind, Sum.inl B2bRewindState.start⟩ :
      Σ j, b2b_hostState MV MI MP j) p (List.replicate Q false) (List.replicate Q true)
    H.runFrom d₀ ((2 * Q + 3) + (2 * Q + 3)) = d₁ ∧
      ∀ u ≤ (2 * Q + 3) + (2 * Q + 3), ∀ j,
        |(H.runFrom d₀ u).workTapePos j| ≤ (Q + 1 : ℕ) := by
  classical
  dsimp only
  let K := b2b_tapeCount MV.k MI.k MP.k
  let U := (b2b_wordTape MV.k MI.k MP.k 0).castSucc
  let Ctr := Fin.last K
  have hne : U ≠ Ctr := by
    intro h
    have := congrArg Fin.val h
    dsimp [U, Ctr, b2b_wordTape, K, b2b_tapeCount] at this
    omega
  let w := List.replicate Q true
  let z := List.replicate Q false
  let a : Cfg (K + 1) Bool SweepPhase x := b2b_setupCfg MV MI MP .sweep p w []
  let b : Cfg (K + 1) Bool SweepPhase x := b2b_setupCfg MV MI MP .done p w w
  let c : Cfg (K + 1) Bool FlagPhase x := b2b_setupCfg MV MI MP .run p w w
  let d : Cfg (K + 1) Bool FlagPhase x := b2b_setupCfg MV MI MP (.done false) p z w
  have ha : ∀ r : ℤ, -1 ≤ r → r ≤ (w.length : ℤ) →
      a.workTapes U (a.workTapePos U + r) = FinTM.bufferTape w r := by
    intro r _ _
    simp [a, b2b_setupCfg, Cfg.init, U]
  have hc : ∀ r : ℤ, -1 ≤ r → r ≤ (w.length : ℤ) →
      c.workTapes U (c.workTapePos U + r) = FinTM.bufferTape w r := by
    intro r _ _
    simp [c, b2b_setupCfg, Cfg.init, U]
  have hcopy := copyTM_run_ofCfg U Ctr hne w a rfl ha
  have hcopyend : (b2b_hostPhases MV MI MP .counter).runFrom a (2 * Q + 2) = b := by
    have hh := hcopy.1
    simp only [w, List.length_replicate] at hh
    rw [hh]
    apply Cfg.ext <;> try rfl
    funext j r
    by_cases hj : j = Ctr
    · subst j
      have hcat := congrFun (b2b_buffer_concat [] w) r
      simpa [a, b, b2b_setupCfg, Cfg.init, Ctr, U, Ne.symm hne, w, K] using hcat
    · have hj' : j ≠ Fin.last (b2b_tapeCount MV.k MI.k MP.k) := hj
      simp [a, b, b2b_setupCfg, Cfg.init, Ctr, hj, K]
  have hov : incFixed w = none := by
    dsimp [w]
    have hall : ∀ n, incFixed (List.replicate n true) = none := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => simp [List.replicate_succ, incFixed, ih]
    exact hall Q
  have hinc := incrementTM_run_overflow_ofCfg U w hov c rfl hc
  have hincend : (b2b_hostPhases MV MI MP .zero).runFrom c (2 * Q + 2) = d := by
    have hh := hinc.1
    simp only [w, List.length_replicate] at hh
    rw [hh]
    apply Cfg.ext <;> try rfl
    funext j r
    by_cases hj : j = U
    · subst j
      by_cases hr : 0 ≤ r
      · by_cases hq : r < (Q : ℤ)
        · simp [c, d, b2b_setupCfg, Cfg.init, U, hr, hq, z]
        · have hn : Q ≤ r.toNat := by omega
          simp [c, d, b2b_setupCfg, Cfg.init, U, hr, hq, z, w, FinTM.bufferTape,
            show ¬r.toNat < Q by omega]
      · simp [c, d, b2b_setupCfg, Cfg.init, U, hr, z, w, FinTM.bufferTape]
    · simp [c, d, b2b_setupCfg, Cfg.init, U, hj]
  have hp := phaseHostTM_run (b2b_hostPhases MV MI MP)
    ⟨.setup, Sum.inl (.init MP.tm.q₀)⟩ (b2b_hostRedirect MV MI MP) .counter
    a b (2 * Q + 2) hcopyend .done rfl ⟨.zero, .run⟩ rfl (by
      intro u hu q hq
      have hn := hcopy.2.1 u (by simpa [w] using hu)
      cases q <;> simp_all [b2b_hostRedirect])
  have hi := phaseHostTM_run (b2b_hostPhases MV MI MP)
    ⟨.setup, Sum.inl (.init MP.tm.q₀)⟩ (b2b_hostRedirect MV MI MP) .zero
    c d (2 * Q + 2) hincend (.done false) rfl ⟨.rewind, Sum.inl .start⟩ rfl (by
      intro u hu q hq
      have hn := hinc.2.1 u (by simpa [w] using hu)
      cases q <;> simp_all [b2b_hostRedirect])
  have hmid : b.mapState (fun _ => (⟨.zero, .run⟩ : Σ j, b2b_hostState MV MI MP j)) =
      c.mapState (Sigma.mk B2bHostPhase.zero) := rfl
  constructor
  · rw [MultiTapeTM.runFrom_add]
    change (b2b_host MV MI MP).tm.runFrom
      ((b2b_host MV MI MP).tm.runFrom (a.mapState (Sigma.mk B2bHostPhase.counter))
        ((2 * Q + 2) + 1)) ((2 * Q + 2) + 1) = _
    rw [hp.2, b2b_dispatch_retag]
    change (b2b_host MV MI MP).tm.runFrom (c.mapState (Sigma.mk B2bHostPhase.zero))
      ((2 * Q + 2) + 1) = _
    rw [hi.2, b2b_dispatch_retag]
    rfl
  · intro u hu j
    change |((b2b_host MV MI MP).tm.runFrom
      (a.mapState (Sigma.mk B2bHostPhase.counter)) u).workTapePos j| ≤ _
    by_cases hpre : u ≤ 2 * Q + 2
    · rw [hp.1 u hpre]
      have hb := hcopy.2.2 j u (by simpa [w] using hpre)
      simp only [show a.workTapePos j = 0 from rfl, show w.length = Q by simp [w],
        zero_sub, zero_add, Finset.mem_Icc] at hb
      split_ifs at hb <;> change |((copyTM _ U Ctr).runFrom a u).workTapePos j| ≤ _
      · exact abs_le.mpr ⟨by omega, by omega⟩
      · rw [hb]; simp only [abs_zero]; omega
    · have hsplit : u = (2 * Q + 2 + 1) + (u - (2 * Q + 3)) := by omega
      rw [hsplit, MultiTapeTM.runFrom_add, hp.2, b2b_dispatch_retag]
      change |((b2b_host MV MI MP).tm.runFrom (c.mapState (Sigma.mk B2bHostPhase.zero))
        (u - (2 * Q + 3))).workTapePos j| ≤ _
      by_cases hpost : u - (2 * Q + 3) ≤ 2 * Q + 2
      · rw [hi.1 _ hpost]
        have hb := hinc.2.2 j (u - (2 * Q + 3)) (by simpa [w] using hpost)
        simp only [show c.workTapePos j = 0 from rfl, show w.length = Q by simp [w],
          zero_sub, zero_add, Finset.mem_Icc] at hb
        split_ifs at hb <;> change |((incrementTM _ U).runFrom c (u - (2 * Q + 3))).workTapePos j| ≤ _
        · exact abs_le.mpr ⟨by omega, by omega⟩
        · rw [hb]; simp only [abs_zero]; omega
      · have hend : u - (2 * Q + 3) = (2 * Q + 2) + 1 := by omega
        rw [hend, hi.2]
        change |(0 : ℤ)| ≤ _
        simp only [abs_zero]
        omega

/-- All five setup phases reach the counter loop with the zero certificate,
all-true counter, restored native input, blank scratch, and origin heads. The
entire setup uses one fixed radius, including at certificate width zero.

**Proof sketch.** Concatenate the proved setup capture, the returning virtual
rewind, the copy/overflow pair, and the returning native rewind. Each live exit
uses the public phase host. Split a prefix at the three joins to inherit the
component head bounds; none depends on the number of certificate trials. -/
private theorem b2b_setup_run (MV MI MP : FinTM Bool) (x : List Bool) (Q t s : ℕ)
    (ht : MP.ComputesInTime x (List.replicate Q true) t)
    (hs : MP.tm.spaceUsed (MP.tm.initCfg x) t ≤ s) :
    ∃ T : ℕ,
      (b2b_host MV MI MP).tm.runFrom ((b2b_host MV MI MP).tm.initCfg x) T =
        b2b_setupCfg MV MI MP (⟨B2bHostPhase.loop, CounterLoopState.dec .run⟩ :
          Σ j, b2b_hostState MV MI MP j) 1 (List.replicate Q false) (List.replicate Q true) ∧
      ∀ u ≤ T, ∀ j,
        |((b2b_host MV MI MP).tm.runFrom ((b2b_host MV MI MP).tm.initCfg x) u).workTapePos j|
          ≤ (s + Q + 1 : ℕ) := by
  classical
  let K := b2b_tapeCount MV.k MI.k MP.k
  let U := (b2b_wordTape MV.k MI.k MP.k 0).castSucc
  let H := (b2b_host MV MI MP).tm
  let w := List.replicate Q true
  let z := List.replicate Q false
  obtain ⟨T₁, p, h₁, h₁heads⟩ := b2b_setup_capture MV MI MP x w t s ht hs
  let a₀ : Cfg (K + 1) Bool (b2b_hostState MV MI MP .origin) x :=
    { Cfg.init (k := K + 1) (Sum.inl (.start, true)) x with
      inputPos := p,
      workTapes := Function.update (fun _ _ => none) U (FinTM.bufferTape w),
      workTapePos := Function.update (fun _ => (0 : ℤ)) U (w.length : ℤ) }
  let a₁ : Cfg (K + 1) Bool (b2b_hostState MV MI MP .origin) x :=
    { Cfg.init (k := K + 1) (Sum.inr ()) x with
      inputPos := p,
      workTapes := Function.update (fun _ _ => none) U (FinTM.bufferTape w) }
  obtain ⟨T₂, h₂, h₂cut, h₂heads⟩ := b2b_origin_run U w p
  have hp₂ := phaseHostTM_run (b2b_hostPhases MV MI MP)
    ⟨.setup, Sum.inl (.init MP.tm.q₀)⟩ (b2b_hostRedirect MV MI MP) .origin
    a₀ a₁ T₂ h₂ (Sum.inr ()) rfl ⟨.counter, .sweep⟩ rfl (by
      intro u hu q hq
      cases q with
      | inl a => rfl
      | inr a => exact False.elim (h₂cut u hu (by simpa using hq)))
  let c₀ := b2b_setupCfg MV MI MP (⟨B2bHostPhase.counter, SweepPhase.sweep⟩ :
    Σ j, b2b_hostState MV MI MP j) p w []
  let c₁ := b2b_setupCfg MV MI MP (⟨B2bHostPhase.rewind, Sum.inl B2bRewindState.start⟩ :
    Σ j, b2b_hostState MV MI MP j) p z w
  change H.runFrom (H.initCfg x) T₁ = a₀.mapState (Sigma.mk B2bHostPhase.origin) at h₁
  have h₂end : H.runFrom (a₀.mapState (Sigma.mk B2bHostPhase.origin)) (T₂ + 1) = c₀ := by
    rw [hp₂.2, b2b_dispatch_retag]
    apply Cfg.ext <;> try rfl
    funext j
    simp [a₁, c₀, b2b_setupCfg, Cfg.mapState, Cfg.init, Function.update_apply, U]
  have h₂bound (u : ℕ) (hu : u ≤ T₂ + 1) (j : Fin (K + 1)) :
      |(H.runFrom (a₀.mapState (Sigma.mk B2bHostPhase.origin)) u).workTapePos j| ≤ (Q + 1 : ℕ) := by
    by_cases hpre : u ≤ T₂
    · rw [hp₂.1 u hpre]
      have hb := h₂heads u hpre j
      change (if j = U then
        ((b2b_hostPhases MV MI MP .origin).runFrom a₀ u).workTapePos j ∈
          Finset.Icc (-1 : ℤ) (w.length : ℤ)
        else ((b2b_hostPhases MV MI MP .origin).runFrom a₀ u).workTapePos j = 0) at hb
      simp only [show w.length = Q by simp [w], Finset.mem_Icc] at hb
      change |((b2b_hostPhases MV MI MP .origin).runFrom a₀ u).workTapePos j| ≤ _
      split_ifs at hb
      · exact abs_le.mpr ⟨by omega, by omega⟩
      · rw [hb]; simp only [abs_zero]; omega
    · have heq : u = T₂ + 1 := by omega
      rw [heq, h₂end]
      change |(0 : ℤ)| ≤ _
      simp only [abs_zero]; omega
  have h₃ := b2b_seed_run MV MI MP p Q
  change H.runFrom c₀ ((2 * Q + 3) + (2 * Q + 3)) = c₁ ∧ _ at h₃
  let r₀ : Cfg (K + 1) Bool B2bRewindState x := b2b_setupCfg MV MI MP .start p z w
  let r₁ : Cfg (K + 1) Bool (b2b_hostState MV MI MP .rewind) x :=
    b2b_setupCfg MV MI MP (Sum.inr ()) 1 z w
  obtain ⟨T₄, h₄, h₄cut, h₄heads⟩ := b2b_rewind_return r₀ rfl
  have hp₄ := phaseHostTM_run (b2b_hostPhases MV MI MP)
    ⟨.setup, Sum.inl (.init MP.tm.q₀)⟩ (b2b_hostRedirect MV MI MP) .rewind
    (r₀.mapState Sum.inl) r₁ T₄ h₄ (Sum.inr ()) rfl ⟨.loop, .dec .run⟩ rfl (by
      intro u hu q hq
      cases q with
      | inl a => rfl
      | inr a => exact False.elim (h₄cut u hu (by simpa using hq)))
  have h₄end : H.runFrom c₁ (T₄ + 1) = b2b_setupCfg MV MI MP
      (⟨B2bHostPhase.loop, CounterLoopState.dec .run⟩ : Σ j, b2b_hostState MV MI MP j)
      1 z w := by
    change H.runFrom ((r₀.mapState Sum.inl).mapState (Sigma.mk B2bHostPhase.rewind)) (T₄ + 1) = _
    rw [hp₄.2, b2b_dispatch_retag]
    rfl
  have h₄bound (u : ℕ) (hu : u ≤ T₄ + 1) (j : Fin (K + 1)) :
      (H.runFrom c₁ u).workTapePos j = 0 := by
    change (H.runFrom ((r₀.mapState Sum.inl).mapState (Sigma.mk B2bHostPhase.rewind)) u).workTapePos j = 0
    by_cases hpre : u ≤ T₄
    · rw [hp₄.1 u hpre]
      exact congrFun (h₄heads u hpre) j
    · have heq : u = T₄ + 1 := by omega
      rw [heq, hp₄.2]
      rfl
  let A := T₁ + (T₂ + 1)
  let B := (2 * Q + 3) + (2 * Q + 3)
  have hA : H.runFrom (H.initCfg x) A = c₀ := by
    rw [MultiTapeTM.runFrom_add, h₁, h₂end]
  have hB : H.runFrom (H.initCfg x) (A + B) = c₁ := by
    rw [MultiTapeTM.runFrom_add, hA]
    exact h₃.1
  refine ⟨A + B + (T₄ + 1), ?_, ?_⟩
  · rw [MultiTapeTM.runFrom_add, hB, h₄end]
  · intro u hu j
    change |(H.runFrom (H.initCfg x) u).workTapePos j| ≤ _
    by_cases hb : u ≤ A + B
    · by_cases ha : u ≤ A
      · by_cases hfirst : u ≤ T₁
        · have hb := h₁heads u hfirst j
          simp only [w, List.length_replicate] at hb
          exact hb.trans (by omega)
        · have heq : u = T₁ + (u - T₁) := by omega
          rw [heq, MultiTapeTM.runFrom_add, h₁]
          exact (h₂bound _ (by dsimp [A] at ha; omega) j).trans (by omega)
      · have heq : u = A + (u - A) := by omega
        rw [heq, MultiTapeTM.runFrom_add, hA]
        exact (h₃.2 (u - A) (by dsimp [B] at hb; omega) j).trans (by omega)
    · have heq : u = (A + B) + (u - (A + B)) := by omega
      rw [heq, MultiTapeTM.runFrom_add, hB, h₄bound _ (by omega)]
      simp only [abs_zero]; omega

/-- The shared trial's three word tapes, with blank banks and empty physical
output. The two displaced heads are the buffer and verdict heads; the
certificate head and all bank heads are at their origins. -/
private def b2b_trialCfg {S : Type} {x : List Bool} (MV MI MP : FinTM Bool)
    (q : S) (p : Fin (x.length + 2)) (u y z : List Bool) (bp cp : ℤ) :
    Cfg (b2b_tapeCount MV.k MI.k MP.k) Bool S x :=
  { Cfg.init (k := b2b_tapeCount MV.k MI.k MP.k) q x with
    inputPos := p,
    workTapes := fun j => if j = b2b_wordTape MV.k MI.k MP.k 0 then
      FinTM.bufferTape u else if j = b2b_wordTape MV.k MI.k MP.k 1 then
      FinTM.bufferTape y else if j = b2b_wordTape MV.k MI.k MP.k 2 then
      FinTM.bufferTape z else fun _ => none,
    workTapePos := fun j => if j = b2b_wordTape MV.k MI.k MP.k 1 then bp
      else if j = b2b_wordTape MV.k MI.k MP.k 2 then cp else 0 }

/-- The identity phase silently installs the native input in the trial buffer,
leaving the certificate intact and the identity bank clean.

**Proof sketch.** Instantiate the existing clean-capture theorem with the
identity bank and the buffer tape. The existing capture-shape identity gives
both seams. Its trajectory bounds the buffer by the input length and the
selected bank by the identity machine's constant space bound. -/
private theorem b2b_trial_capture (MV MI MP : FinTM Bool) (x u : List Bool)
    (t s : ℕ) (ht : MI.ComputesInTime x x t)
    (hs : MI.tm.spaceUsed (MI.tm.initCfg x) t ≤ s) :
    let E := b2b_testPhases MV MI MP .identity
    let d := b2b_trialCfg MV MI MP (Sum.inl (LogProg.CleanSt.init MI.tm.q₀) :
      b2b_testState MV MI .identity) (x := x) 1 u [] [] 0 0
    ∃ T : ℕ, ∃ p : Fin (x.length + 2),
      E.runFrom d T = b2b_trialCfg MV MI MP (Sum.inr ()) p u x [] x.length 0 ∧
      (∀ r < T, (E.runFrom d r).state ≠ some (Sum.inr ())) ∧
      ∀ r ≤ T, ∀ j, |(E.runFrom d r).workTapePos j| ≤ (x.length + s : ℕ) := by
  classical
  dsimp only
  let K := b2b_tapeCount MV.k MI.k MP.k
  let U := b2b_wordTape MV.k MI.k MP.k 0
  let BUF := b2b_wordTape MV.k MI.k MP.k 1
  let CAP := b2b_wordTape MV.k MI.k MP.k 2
  let ι := b2b_bankEmb (3 + (MV.k + MV.k)) (MI.k + MI.k) K
    (by dsimp [K, b2b_tapeCount]; omega)
  let tapes : Fin K → ℤ → Option Bool := fun j =>
    if j = U then FinTM.bufferTape u else fun _ => none
  have hcap : BUF ∉ Set.range ι := by
    rintro ⟨a, ha⟩
    have := congrArg Fin.val ha
    dsimp [ι, BUF, b2b_bankEmb, b2b_wordTape] at this
    omega
  have hbank : ∀ a, tapes (ι a) = fun _ => none := by
    intro a
    have hn : ι a ≠ U := by
      intro ha
      have := congrArg Fin.val ha
      dsimp [ι, U, b2b_bankEmb, b2b_wordTape] at this
      omega
    simp [tapes, hn]
  let N := LogProg.cleanTM MI.tm MI.tm.q₀
  let c₀ : Cfg (MI.k + MI.k) Bool (LogProg.CleanSt MI.State MI.k) x :=
    Cfg.init (.init MI.tm.q₀) x
  have hshape (p : Fin (x.length + 2)) (y : List Bool) :
      embedSilentCfg ι BUF tapes (fun _ => 0) [] []
        { c₀ with inputPos := p, output := y } =
      b2b_trialCfg MV MI MP (LogProg.CleanSt.init MI.tm.q₀) p u y [] y.length 0 := by
    rw [b2b_capture_shape N ι BUF hcap tapes hbank]
    apply Cfg.ext <;> try rfl
    · funext j
      by_cases hbuf : j = BUF
      · subst j
        simp [b2b_trialCfg, tapes, BUF, U, b2b_wordTape]
      · simp only [Function.update_of_ne hbuf]
        simp [b2b_trialCfg, tapes, BUF, U, hbuf]
    · funext j
      by_cases hbuf : j = BUF
      · subst j
        simp [b2b_trialCfg, BUF]
      · simp [b2b_trialCfg, BUF, hbuf]
  obtain ⟨T, p, he, hcut, _, hb⟩ :=
    b2b_clean_capture MI ι BUF hcap tapes (fun _ => 0) x x t s ht hs
  have hstart : (embedSilentCfg ι BUF tapes (fun _ => 0) [] [] c₀).mapState Sum.inl =
      b2b_trialCfg MV MI MP (Sum.inl (LogProg.CleanSt.init MI.tm.q₀) :
        b2b_testState MV MI .identity) (x := x) 1 u [] [] 0 0 := by
    have hh := hshape 1 []
    change embedSilentCfg ι BUF tapes (fun _ => 0) [] [] c₀ = _ at hh
    rw [hh]
    rfl
  have hend : { embedSilentCfg ι BUF tapes (fun _ => 0) [] []
      { c₀ with inputPos := p, output := x } with state := some (Sum.inr ()) } =
      b2b_trialCfg MV MI MP (Sum.inr () : b2b_testState MV MI .identity)
        p u x [] x.length 0 := by
    rw [hshape]
    rfl
  rw [hstart, hend] at he
  rw [hstart] at hcut hb
  refine ⟨T, p, he, hcut, ?_⟩
  intro r hr j
  have hh := hb r hr j
  split_ifs at hh with hj hj'
  · have hmem := Finset.mem_Icc.mp hh
    exact abs_le.mpr ⟨by omega, by omega⟩
  · exact hh.trans (by omega)
  · rw [hh]
    positivity

/-- The silent virtual call uses the trial buffer and verifier bank, while the
certificate stays in the frame. This identifies both call seams, including
the captured singleton and the buffer head's return to zero.

**Proof sketch.** Split host tapes into the virtual buffer, selected verifier
bank, capture tape and unselected frame. Use the public selected projections
and frame theorem; the two special heads are the virtual input position minus
one and the length of the captured output. -/
private theorem b2b_call_shape (MV MI MP : FinTM Bool) {x y : List Bool}
    (u : List Bool) (p : Fin (x.length + 2))
    (c : Cfg (MV.k + MV.k) Bool
      ((B2bRewindState ⊕ Unit) ⊕
        ((LogProg.CleanSt MV.State MV.k ⊕ Unit) ⊕ B2bRewindState)) y)
    (ht : c.workTapes = fun _ _ => none) (hh : c.workTapePos = fun _ => 0) (b : Bool) :
    embedSilentCfg (b2b_callEmb MV.k MI.k MP.k) (b2b_wordTape MV.k MI.k MP.k 2)
      (b2b_trialCfg MV MI MP () p u [] [] 0 0).workTapes (fun _ => 0) [] []
      (vhostCfg c b p []) =
    { b2b_trialCfg MV MI MP ((b2b_hostedSource MV).q₀, b) p u y c.output
        ((c.inputPos.val : ℤ) - 1) c.output.length with
      state := c.state.map (fun q => (q, b)) } := by
  classical
  let ι := b2b_callEmb MV.k MI.k MP.k
  let CAP := b2b_wordTape MV.k MI.k MP.k 2
  let BUF := b2b_wordTape MV.k MI.k MP.k 1
  let tapes := (b2b_trialCfg MV MI MP () p u [] [] 0 0).workTapes
  let d := vhostCfg c b p []
  have hcap : CAP ∉ Set.range ι := by
    rintro ⟨a, ha⟩
    have he := congrArg Fin.val ha
    dsimp [ι, CAP, b2b_callEmb, b2b_wordTape] at he
    split_ifs at he <;> omega
  have hbuf : ι (vhostBuffer (MV.k + MV.k)) = BUF := by
    apply Fin.ext
    rfl
  have hbank (a : Fin (MV.k + MV.k)) :
      ι (vhostBank a) ≠ b2b_wordTape MV.k MI.k MP.k 0 ∧
      ι (vhostBank a) ≠ BUF ∧ ι (vhostBank a) ≠ CAP := by
    refine ⟨?_, ?_, ?_⟩ <;> intro heq
    all_goals
      have he := congrArg Fin.val heq
      dsimp [ι, BUF, CAP, b2b_callEmb, b2b_wordTape, vhostBank] at he
      split_ifs at he <;> omega
  apply Cfg.ext <;> try rfl
  · funext j
    change (embedSilentCfg ι CAP tapes (fun _ => 0) [] [] d).workTapes j = _
    by_cases hsel : j ∈ Set.range ι
    · obtain ⟨a, rfl⟩ := hsel
      rw [embedSilentCfg_selected_tape]
      refine Fin.addCases (fun a => ?_) (fun a => ?_) a
      · have ha : a = 0 := Subsingleton.elim _ _
        subst a
        change FinTM.bufferTape y = _
        change FinTM.bufferTape y =
          (b2b_trialCfg MV MI MP ((b2b_hostedSource MV).q₀, b) p u y c.output
            ((c.inputPos.val : ℤ) - 1) c.output.length).workTapes
              (ι (vhostBuffer (MV.k + MV.k)))
        rw [hbuf]
        simp [b2b_trialCfg, BUF, b2b_wordTape]
      · have ha := hbank a
        dsimp only [BUF, CAP, vhostBank] at ha
        simp only [d, vhostCfg, Fin.addCases_right, ht]
        simp [b2b_trialCfg, ha.1, ha.2.1, ha.2.2]
    · by_cases hc : j = CAP
      · subst j
        simp only [embedSilentCfg]
        split
        · rename_i a ha
          have hfind := List.find?_some (p := fun a => decide (ι a = CAP)) ha
          exact False.elim (hcap ⟨a, of_decide_eq_true hfind⟩)
        · simp [d, vhostCfg, b2b_trialCfg, CAP, b2b_wordTape]
      · have hjb : j ≠ BUF := by
          intro hj
          exact hsel ⟨vhostBuffer _, hbuf.trans hj.symm⟩
        have hf : (embedSilentCfg ι CAP tapes (fun _ => 0) [] [] d).workTapes j = tapes j := by
          simpa only [MultiTapeTM.runFrom_zero] using
            ((embedSilentTM_frame ι CAP hcap (vhostEmitTM (b2b_hostedSource MV))
              tapes (fun _ => 0) [] [] d 0).1 j hsel hc).1
        rw [hf]
        dsimp only [BUF, CAP] at hjb hc
        simp [tapes, b2b_trialCfg, hjb, hc]
  · funext j
    change (embedSilentCfg ι CAP tapes (fun _ => 0) [] [] d).workTapePos j = _
    by_cases hsel : j ∈ Set.range ι
    · obtain ⟨a, rfl⟩ := hsel
      rw [embedSilentCfg_selected_pos]
      refine Fin.addCases (fun a => ?_) (fun a => ?_) a
      · have ha : a = 0 := Subsingleton.elim _ _
        subst a
        change (c.inputPos.val : ℤ) - 1 = _
        change (c.inputPos.val : ℤ) - 1 =
          (b2b_trialCfg MV MI MP ((b2b_hostedSource MV).q₀, b) p u y c.output
            ((c.inputPos.val : ℤ) - 1) c.output.length).workTapePos
              (ι (vhostBuffer (MV.k + MV.k)))
        rw [hbuf]
        simp [b2b_trialCfg, BUF]
      · have ha := hbank a
        dsimp only [BUF, CAP, vhostBank] at ha
        simp only [d, vhostCfg, Fin.addCases_right, hh]
        simp [b2b_trialCfg, ha.2.1, ha.2.2]
    · by_cases hc : j = CAP
      · subst j
        simp only [embedSilentCfg]
        split
        · rename_i a ha
          have hfind := List.find?_some (p := fun a => decide (ι a = CAP)) ha
          exact False.elim (hcap ⟨a, of_decide_eq_true hfind⟩)
        · simp [d, vhostCfg, b2b_trialCfg, CAP, b2b_wordTape]
      · have hjb : j ≠ BUF := by
          intro hj
          exact hsel ⟨vhostBuffer _, hbuf.trans hj.symm⟩
        have hf : (embedSilentCfg ι CAP tapes (fun _ => 0) [] [] d).workTapePos j = 0 := by
          simpa only [MultiTapeTM.runFrom_zero] using
            ((embedSilentTM_frame ι CAP hcap (vhostEmitTM (b2b_hostedSource MV))
              tapes (fun _ => 0) [] [] d 0).1 j hsel hc).2
        rw [hf]
        dsimp only [BUF, CAP] at hjb hc
        simp [b2b_trialCfg, hjb, hc]

/-- The shared verifier phase captures its one bit, returns the buffer head to
zero, and cleans the verifier bank, with a fixed radius throughout.

**Proof sketch.** Use the proved hosted-source run at virtual position
`|x| + 1`, take its first halt, and transport it through the public virtual
host and silent returning embedding. The call-shape identity identifies the
seams. Public buffer and bank trajectories give the selected-head windows;
output-prefix monotonicity confines the capture head to zero or one. -/
private theorem b2b_trial_call (MV MI MP : FinTM Bool) (x u : List Bool)
    (b : Bool) (s : ℕ)
    (hclean : LogProg.CleanRun (LogProg.cleanTM MV.tm MV.tm.q₀)
      (LogProg.CleanSt.init MV.tm.q₀) (x ++ u) b s) :
    let E := b2b_testPhases MV MI MP .call
    let d := b2b_trialCfg MV MI MP
      (Sum.inl ((b2b_hostedSource MV).q₀, true) : b2b_testState MV MI .call)
      (x := x) 1 u (x ++ u) [] x.length 0
    ∃ T : ℕ, E.runFrom d T =
        b2b_trialCfg MV MI MP (Sum.inr ()) 1 u (x ++ u) [b] 0 1 ∧
      (∀ r < T, (E.runFrom d r).state ≠ some (Sum.inr ())) ∧
      ∀ r ≤ T, ∀ j, |(E.runFrom d r).workTapePos j| ≤ (x.length + u.length + s + 1 : ℕ) := by
  classical
  dsimp only
  let D := b2b_hostedSource MV
  let y := x ++ u
  let p : Fin (y.length + 2) := ⟨x.length + 1, by simp [y]; omega⟩
  let c₀ := { D.initCfg y with inputPos := p }
  let N := vhostEmitTM D
  let v₀ := vhostCfg c₀ true (1 : Fin (x.length + 2)) []
  let ι := b2b_callEmb MV.k MI.k MP.k
  let CAP := b2b_wordTape MV.k MI.k MP.k 2
  let tapes := (b2b_trialCfg MV MI MP () (x := x) 1 u [] [] 0 0).workTapes
  have hcap : CAP ∉ Set.range ι := by
    rintro ⟨a, ha⟩
    have he := congrArg Fin.val ha
    dsimp [ι, CAP, b2b_callEmb, b2b_wordTape] at he
    split_ifs at he <;> omega
  have htag : FinTM.VirtualTag c₀.inputPos true := by
    simp [FinTM.VirtualTag, c₀, p]
  obtain ⟨t, ht, hbound⟩ := b2b_hostedSource_run MV y b s hclean p
  obtain ⟨T, hT, hlive, hfirst⟩ := MultiTapeTM.exists_first_halt D c₀
    (show (D.runFrom c₀ t).state = none from congrArg Cfg.state ht)
  have hsrc : D.runFrom c₀ T = { D.initCfg y with state := none, output := [b] } :=
    hfirst.trans ht
  obtain ⟨tag, _, hv⟩ := vhostEmitTM_runFrom D c₀ true htag
    (1 : Fin (x.length + 2)) [] T
  rw [hsrc] at hv
  have hvLive : ∀ r < T, (N.runFrom v₀ r).state ≠ none := by
    intro r hr
    obtain ⟨tag, _, he⟩ := vhostEmitTM_runFrom D c₀ true htag
      (1 : Fin (x.length + 2)) [] r
    rw [he]
    exact fun hn => hlive r hr (Option.map_eq_none_iff.mp hn)
  have he := embedSilentRetTM_run ι CAP hcap N tapes (fun _ => 0) [] [] v₀ T
    (by simp [v₀, vhostCfg, c₀, MultiTapeTM.initCfg, Cfg.init]) hvLive
    (by rw [hv]; rfl)
  let d₀ := b2b_trialCfg MV MI MP
    (Sum.inl (D.q₀, true) : b2b_testState MV MI .call) (x := x) 1 u y [] x.length 0
  have hstart : (embedSilentCfg ι CAP tapes (fun _ => 0) [] [] v₀).mapState Sum.inl = d₀ := by
    have hh := b2b_call_shape MV MI MP u (1 : Fin (x.length + 2)) c₀ rfl rfl true
    change embedSilentCfg ι CAP tapes (fun _ => 0) [] [] v₀ = _ at hh
    rw [hh]
    simp [d₀, b2b_trialCfg, Cfg.mapState, c₀, MultiTapeTM.initCfg, Cfg.init, p]
  have hend : { embedSilentCfg ι CAP tapes (fun _ => 0) [] [] (N.runFrom v₀ T) with
      state := some (Sum.inr ()) } =
      b2b_trialCfg MV MI MP (Sum.inr () : b2b_testState MV MI .call)
        (x := x) 1 u y [b] 0 1 := by
    rw [hv, b2b_call_shape MV MI MP u 1 _ rfl rfl tag]
    simp [b2b_trialCfg, MultiTapeTM.initCfg, Cfg.init]
  have hrun := he.2.1
  rw [hstart, hend] at hrun
  have hcut := he.2.2
  rw [hstart] at hcut
  refine ⟨T, hrun, hcut, ?_⟩
  intro r hr j
  have hheads : ((embedSilentRetTM ι CAP N).runFrom d₀ r).workTapePos =
      (embedSilentCfg ι CAP tapes (fun _ => 0) [] [] (N.runFrom v₀ r)).workTapePos := by
    rw [← hstart]
    rcases lt_or_eq_of_le hr with hr' | rfl
    · rw [he.1 r hr']; rfl
    · rw [he.2.1]
  change |((embedSilentRetTM ι CAP N).runFrom d₀ r).workTapePos j| ≤ _
  rw [hheads]
  by_cases hsel : j ∈ Set.range ι
  · obtain ⟨a, rfl⟩ := hsel
    rw [embedSilentCfg_selected_pos]
    refine Fin.addCases (fun a => ?_) (fun a => ?_) a
    · have ha : a = 0 := Subsingleton.elim _ _
      subst a
      have hb := vhostCfg_buffer_head_mem D c₀ true htag
        (1 : Fin (x.length + 2)) [] r
      have hm := Finset.mem_Icc.mp hb
      change -1 ≤ (N.runFrom v₀ r).workTapePos (vhostBuffer (MV.k + MV.k)) ∧
        (N.runFrom v₀ r).workTapePos (vhostBuffer (MV.k + MV.k)) ≤ (y.length : ℤ) at hm
      change |(N.runFrom v₀ r).workTapePos (vhostBuffer (MV.k + MV.k))| ≤ _
      simp only [y, List.length_append, Nat.cast_add] at hm
      exact abs_le.mpr ⟨by omega, by omega⟩
    · have hm : (N.runFrom v₀ r).workTapePos (vhostBank a) ∈
          N.visitedByTapeHead v₀ T (vhostBank a) :=
        Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr (by omega), rfl⟩
      rw [vhostEmitTM_visitedByTapeHead_bank D c₀ true htag] at hm
      obtain ⟨v, hv', hpos⟩ := Finset.mem_image.mp hm
      have hvT : v ≤ T := by have := Finset.mem_range.mp hv'; omega
      change |(N.runFrom v₀ r).workTapePos (vhostBank a)| ≤ _
      rw [← hpos]
      exact (hbound v (hvT.trans hT) a).trans (by omega)
  · by_cases hj : j = CAP
    · subst j
      have hp : (embedSilentCfg ι CAP tapes (fun _ => 0) [] []
          (N.runFrom v₀ r)).workTapePos CAP = ((N.runFrom v₀ r).output.length : ℤ) := by
        simp only [embedSilentCfg]
        split
        · rename_i a ha
          have hf := List.find?_some (p := fun a => decide (ι a = CAP)) ha
          exact False.elim (hcap ⟨a, of_decide_eq_true hf⟩)
        · simp
      rw [hp, abs_of_nonneg (Nat.cast_nonneg _)]
      have hout := (N.output_prefix v₀ hr).length_le
      rw [hv] at hout
      simp only [vhostCfg, Cfg.init, MultiTapeTM.initCfg, List.nil_append,
        List.length_singleton] at hout
      omega
    · have hf := ((embedSilentTM_frame ι CAP hcap N tapes (fun _ => 0) [] []
        (N.runFrom v₀ r) 0).1 j hsel hj).2
      have hf' : (embedSilentCfg ι CAP tapes (fun _ => 0) [] []
          (N.runFrom v₀ r)).workTapePos j = 0 := by
        simpa only [MultiTapeTM.runFrom_zero] using hf
      rw [hf']
      positivity

/-- The trial's framed copy appends the certificate to the captured native
input, preserving its source and both origin conventions.

**Proof sketch.** Apply the public framed copy at destination head `|x|`.
The inherited concatenation identity identifies the whole destination tape,
including the blank exterior. The public trajectory bounds both moving heads. -/
private theorem b2b_trial_copy (MV MI MP : FinTM Bool) (x u : List Bool) :
    let d := b2b_trialCfg MV MI MP SweepPhase.sweep (x := x) 1 u x [] x.length 0
    let E := b2b_testPhases MV MI MP .copy
    E.runFrom d (2 * u.length + 2) =
        b2b_trialCfg MV MI MP SweepPhase.done 1 u (x ++ u) [] x.length 0 ∧
      (∀ r < 2 * u.length + 2, (E.runFrom d r).state ≠ some SweepPhase.done) ∧
      ∀ r ≤ 2 * u.length + 2, ∀ j,
        |(E.runFrom d r).workTapePos j| ≤ (x.length + u.length + 1 : ℕ) := by
  classical
  dsimp only
  let U := b2b_wordTape MV.k MI.k MP.k 0
  let BUF := b2b_wordTape MV.k MI.k MP.k 1
  let d := b2b_trialCfg MV MI MP SweepPhase.sweep (x := x) 1 u x [] x.length 0
  have hne : U ≠ BUF := by simp [U, BUF, b2b_wordTape, Fin.ext_iff]
  have hsrc : ∀ z : ℤ, -1 ≤ z → z ≤ (u.length : ℤ) →
      d.workTapes U (d.workTapePos U + z) = FinTM.bufferTape u z := by
    intro z _ _
    simp [d, b2b_trialCfg, U, b2b_wordTape]
  have hc := copyTM_run_ofCfg U BUF hne u d rfl hsrc
  refine ⟨?_, hc.2.1, ?_⟩
  · rw [hc.1]
    apply Cfg.ext <;> try rfl
    funext j z
    by_cases hj : j = BUF
    · subst j
      have hcat := congrFun (b2b_buffer_concat x u) z
      simpa [d, b2b_trialCfg, BUF, b2b_wordTape] using hcat
    · simp [d, b2b_trialCfg, BUF, hj]
  · intro r hr j
    have hh := hc.2.2 j r hr
    change |((copyTM _ U BUF).runFrom d r).workTapePos j| ≤ _
    have hpos : 0 ≤ d.workTapePos j ∧ d.workTapePos j ≤ (x.length : ℤ) := by
      simp only [d, b2b_trialCfg]
      split_ifs <;> simp
    split_ifs at hh with hj
    · have hm := Finset.mem_Icc.mp hh
      exact abs_le.mpr ⟨by omega, by omega⟩
    · rw [hh, abs_of_nonneg hpos.1]
      exact hpos.2.trans (by omega)

/-- Reading the trial's captured bit erases the verdict tape and restores its
head to zero, without changing the certificate or virtual-input buffer.

**Proof sketch.** Instantiate the inherited two-step verdict trace. The only
nonblank verdict cell is at zero, so the trace's write clears the whole tape;
its three prefix configurations have heads zero or one. -/
private theorem b2b_trial_verdict (MV MI MP : FinTM Bool) (x u y : List Bool) (b : Bool) :
    let d := b2b_trialCfg MV MI MP B2bVerdictState.left (x := x) 1 u y [b] 0 1
    let E := b2b_testPhases MV MI MP .verdict
    E.runFrom d 2 = b2b_trialCfg MV MI MP (B2bVerdictState.done b) 1 u y [] 0 0 ∧
      (∀ r < 2, ∀ b', (E.runFrom d r).state ≠ some (B2bVerdictState.done b')) ∧
      ∀ r ≤ 2, ∀ j, |(E.runFrom d r).workTapePos j| ≤ (1 : ℤ) := by
  classical
  dsimp only
  let CAP := b2b_wordTape MV.k MI.k MP.k 2
  let d := b2b_trialCfg MV MI MP B2bVerdictState.left (x := x) 1 u y [b] 0 1
  have hb : d.workTapes CAP (d.workTapePos CAP - 1) = some b := by
    simp [d, b2b_trialCfg, CAP, b2b_wordTape, FinTM.bufferTape]
  have ht := b2b_verdict_trace CAP d b rfl hb
  constructor
  · rw [ht 2 le_rfl]
    simp only [show ¬(2 : ℕ) = 0 by decide, show ¬(2 : ℕ) = 1 by decide, ite_false]
    apply Cfg.ext <;> try rfl
    · funext j z
      by_cases hj : j = CAP
      · subst j
        simp only [Function.update_self]
        have hp : d.workTapePos CAP - 1 = 0 := by
          simp [d, b2b_trialCfg, CAP, b2b_wordTape]
        rw [hp]
        by_cases hz : z = 0
        · subst z
          simp [b2b_trialCfg, CAP, b2b_wordTape]
        · simp only [Function.update_of_ne hz]
          simp [d, b2b_trialCfg, CAP, b2b_wordTape, FinTM.bufferTape]
          by_cases hpos : 0 ≤ z
          · simp [hpos]
            omega
          · simp [hpos]
      · simp [d, b2b_trialCfg, CAP, hj]
    · funext j
      by_cases hj : j = CAP
      · subst j
        simp [d, b2b_trialCfg, CAP, b2b_wordTape]
      · simp [d, b2b_trialCfg, CAP, hj]
  · constructor
    · intro r hr b'
      rw [ht r (by omega)]
      interval_cases r <;> simp [d, b2b_trialCfg, Cfg.init]
    · intro r hr j
      rw [ht r hr]
      interval_cases r <;> simp [d, b2b_trialCfg, CAP, b2b_wordTape]
      all_goals try simp only [Function.update_apply]
      all_goals split_ifs <;> norm_num

/-- One shared trial tests the certificate, without physical output, and
finishes at its first verdict exit. Every head stays in a fixed window.

**Proof sketch.** Dispatch from the anchor, compose the proved identity
capture, native returning rewind, append copy and captured verifier call,
and run the two-step verdict reader. The public phase-host lemma supplies
each prefix and dispatch. Splitting at these five joins proves the exit
avoidance and head bounds. The final live, silent configuration implies
liveness and empty physical output at every earlier time. -/
private theorem b2b_trial_run (MV MI MP : FinTM Bool) (x u : List Bool)
    (b : Bool) (ti si sv : ℕ) (hi : MI.ComputesInTime x x ti)
    (his : MI.tm.spaceUsed (MI.tm.initCfg x) ti ≤ si)
    (hv : LogProg.CleanRun (LogProg.cleanTM MV.tm MV.tm.q₀)
      (LogProg.CleanSt.init MV.tm.q₀) (x ++ u) b sv) :
    let H := b2b_testTM MV MI MP
    let d := b2b_trialCfg MV MI MP (⟨B2bTestPhase.anchor, ()⟩ :
      Σ j, b2b_testState MV MI j) (x := x) 1 u [] [] 0 0
    ∃ T : ℕ, 0 < T ∧
      H.runFrom d T = b2b_trialCfg MV MI MP
        (⟨B2bTestPhase.verdict, B2bVerdictState.done b⟩ : Σ j, b2b_testState MV MI j)
        1 u (x ++ u) [] 0 0 ∧
      (∀ r < T, (0 < r → (H.runFrom d r).state ≠ some ⟨.anchor, ()⟩) ∧
        ∀ b', (H.runFrom d r).state ≠ some ⟨.verdict, B2bVerdictState.done b'⟩) ∧
      (∀ r ≤ T, (H.runFrom d r).state ≠ none ∧ (H.runFrom d r).output = []) ∧
      ∀ r ≤ T, ∀ j, |(H.runFrom d r).workTapePos j| ≤
        (x.length + u.length + sv + si + 1 : ℕ) := by
  classical
  dsimp only
  let H := b2b_testTM MV MI MP
  let a := b2b_trialCfg MV MI MP () (x := x) 1 u [] [] 0 0
  let d : Cfg (b2b_tapeCount MV.k MI.k MP.k) Bool (Σ j, b2b_testState MV MI j) x :=
    a.mapState (Sigma.mk B2bTestPhase.anchor)
  let i := b2b_trialCfg MV MI MP (Sum.inl (LogProg.CleanSt.init MI.tm.q₀) :
    b2b_testState MV MI .identity) (x := x) 1 u [] [] 0 0
  obtain ⟨I, p, hiRun, hiCut, hiHeads⟩ := b2b_trial_capture MV MI MP x u ti si hi his
  let i' := b2b_trialCfg MV MI MP (Sum.inr () : b2b_testState MV MI .identity)
    p u x [] x.length 0
  let r := b2b_trialCfg MV MI MP B2bRewindState.start p u x [] x.length 0
  let r' := b2b_trialCfg MV MI MP (Sum.inr () : b2b_testState MV MI .rewind)
    (x := x) 1 u x [] x.length 0
  obtain ⟨R, hrRun, hrCut, hrHeads⟩ := b2b_rewind_return r rfl
  have hrEnd : (b2b_testPhases MV MI MP .rewind).runFrom (r.mapState Sum.inl) R = r' := by
    rw [hrRun]
    rfl
  let c := b2b_trialCfg MV MI MP SweepPhase.sweep (x := x) 1 u x [] x.length 0
  let c' := b2b_trialCfg MV MI MP SweepPhase.done (x := x) 1 u (x ++ u) [] x.length 0
  obtain ⟨hcRun, hcCut, hcHeads⟩ := b2b_trial_copy MV MI MP x u
  let v := b2b_trialCfg MV MI MP
    (Sum.inl ((b2b_hostedSource MV).q₀, true) : b2b_testState MV MI .call)
    (x := x) 1 u (x ++ u) [] x.length 0
  let v' := b2b_trialCfg MV MI MP (Sum.inr () : b2b_testState MV MI .call)
    (x := x) 1 u (x ++ u) [b] 0 1
  obtain ⟨V, hvRun, hvCut, hvHeads⟩ := b2b_trial_call MV MI MP x u b sv hv
  let z := b2b_trialCfg MV MI MP B2bVerdictState.left (x := x) 1 u (x ++ u) [b] 0 1
  let z' := b2b_trialCfg MV MI MP (B2bVerdictState.done b) (x := x) 1 u (x ++ u) [] 0 0
  obtain ⟨hzRun, hzCut, hzHeads⟩ := b2b_trial_verdict MV MI MP x u (x ++ u) b
  have ha := phaseHostTM_run (b2b_testPhases MV MI MP) ⟨.anchor, ()⟩
    (b2b_testRedirect MV MI) .anchor a a 0 rfl () rfl
    ⟨.identity, Sum.inl (.init MI.tm.q₀)⟩ rfl (by intros; omega)
  have hpi := phaseHostTM_run (b2b_testPhases MV MI MP) ⟨.anchor, ()⟩
    (b2b_testRedirect MV MI) .identity i i' I hiRun (Sum.inr ()) rfl
    ⟨.rewind, Sum.inl B2bRewindState.start⟩ rfl (by
      intro t ht q hq
      cases q with
      | inl q => rfl
      | inr q => exact False.elim (hiCut t ht (by simpa using hq)))
  have hpr := phaseHostTM_run (b2b_testPhases MV MI MP) ⟨.anchor, ()⟩
    (b2b_testRedirect MV MI) .rewind (r.mapState Sum.inl) r' R hrEnd (Sum.inr ()) rfl
    ⟨.copy, SweepPhase.sweep⟩ rfl (by
      intro t ht q hq
      cases q with
      | inl q => rfl
      | inr q => exact False.elim (hrCut t ht (by simpa using hq)))
  have hpc := phaseHostTM_run (b2b_testPhases MV MI MP) ⟨.anchor, ()⟩
    (b2b_testRedirect MV MI) .copy c c' (2 * u.length + 2) hcRun SweepPhase.done rfl
    ⟨.call, Sum.inl ((b2b_hostedSource MV).q₀, true)⟩ rfl (by
      intro t ht q hq
      cases q with
      | sweep => rfl
      | rewind => rfl
      | done => exact False.elim (hcCut t ht hq))
  have hpv := phaseHostTM_run (b2b_testPhases MV MI MP) ⟨.anchor, ()⟩
    (b2b_testRedirect MV MI) .call v v' V hvRun (Sum.inr ()) rfl
    ⟨.verdict, B2bVerdictState.left⟩ rfl (by
      intro t ht q hq
      cases q with
      | inl q => rfl
      | inr q => exact False.elim (hvCut t ht (by simpa using hq)))
  have hpz (t : ℕ) : H.runFrom (z.mapState (Sigma.mk B2bTestPhase.verdict)) t =
      ((b2b_testPhases MV MI MP .verdict).runFrom z t).mapState
        (Sigma.mk B2bTestPhase.verdict) :=
    phaseHostTM_run_le (b2b_testPhases MV MI MP) ⟨.anchor, ()⟩ (b2b_testRedirect MV MI)
      .verdict z t (fun _ _ _ _ => rfl) t le_rfl
  let A := 1 + (I + 1)
  let B := A + (R + 1)
  let C := B + (2 * u.length + 2 + 1)
  let F := C + (V + 1)
  let T := F + 2
  have h0 : H.runFrom d 1 = i.mapState (Sigma.mk B2bTestPhase.identity) := by
    exact ha.2
  have h1 : H.runFrom d A = (r.mapState Sum.inl).mapState (Sigma.mk B2bTestPhase.rewind) := by
    rw [show A = 1 + (I + 1) from rfl, MultiTapeTM.runFrom_add, h0, hpi.2]
    rfl
  have h2 : H.runFrom d B = c.mapState (Sigma.mk B2bTestPhase.copy) := by
    rw [show B = A + (R + 1) from rfl, MultiTapeTM.runFrom_add, h1, hpr.2]
    rfl
  have h3 : H.runFrom d C = v.mapState (Sigma.mk B2bTestPhase.call) := by
    rw [show C = B + (2 * u.length + 2 + 1) from rfl, MultiTapeTM.runFrom_add, h2, hpc.2]
    rfl
  have h4 : H.runFrom d F = z.mapState (Sigma.mk B2bTestPhase.verdict) := by
    rw [show F = C + (V + 1) from rfl, MultiTapeTM.runFrom_add, h3, hpv.2]
    rfl
  have hfinal : H.runFrom d T = z'.mapState (Sigma.mk B2bTestPhase.verdict) := by
    rw [show T = F + 2 from rfl, MultiTapeTM.runFrom_add, h4, hpz, hzRun]
  have hcover (t : ℕ) (ht : t ≤ T) :
      t = 0 ∨
      (∃ w ≤ I, t = 1 + w ∧ H.runFrom d t =
        ((b2b_testPhases MV MI MP .identity).runFrom i w).mapState (Sigma.mk B2bTestPhase.identity)) ∨
      (∃ w ≤ R, t = A + w ∧ H.runFrom d t =
        ((b2b_testPhases MV MI MP .rewind).runFrom (r.mapState Sum.inl) w).mapState
          (Sigma.mk B2bTestPhase.rewind)) ∨
      (∃ w ≤ 2 * u.length + 2, t = B + w ∧ H.runFrom d t =
        ((b2b_testPhases MV MI MP .copy).runFrom c w).mapState (Sigma.mk B2bTestPhase.copy)) ∨
      (∃ w ≤ V, t = C + w ∧ H.runFrom d t =
        ((b2b_testPhases MV MI MP .call).runFrom v w).mapState (Sigma.mk B2bTestPhase.call)) ∨
      (∃ w ≤ 2, t = F + w ∧ H.runFrom d t =
        ((b2b_testPhases MV MI MP .verdict).runFrom z w).mapState (Sigma.mk B2bTestPhase.verdict)) := by
    by_cases ht0 : t = 0
    · exact Or.inl ht0
    right
    by_cases htI : t ≤ 1 + I
    · left
      refine ⟨t - 1, by omega, by omega, ?_⟩
      conv_lhs => rw [show t = 1 + (t - 1) by omega, MultiTapeTM.runFrom_add, h0]
      exact hpi.1 _ (by omega)
    right
    by_cases htR : t ≤ A + R
    · left
      refine ⟨t - A, by omega, by dsimp [A]; omega, ?_⟩
      conv_lhs => rw [show t = A + (t - A) by dsimp [A]; omega, MultiTapeTM.runFrom_add, h1]
      exact hpr.1 _ (by omega)
    right
    by_cases htC : t ≤ B + (2 * u.length + 2)
    · left
      refine ⟨t - B, by omega, by dsimp [B]; omega, ?_⟩
      conv_lhs => rw [show t = B + (t - B) by dsimp [B]; omega, MultiTapeTM.runFrom_add, h2]
      exact hpc.1 _ (by omega)
    right
    by_cases htV : t ≤ C + V
    · left
      refine ⟨t - C, by omega, by dsimp [C]; omega, ?_⟩
      conv_lhs => rw [show t = C + (t - C) by dsimp [C]; omega, MultiTapeTM.runFrom_add, h3]
      exact hpv.1 _ (by omega)
    right
    refine ⟨t - F, by dsimp [T] at ht; omega, by dsimp [F]; omega, ?_⟩
    conv_lhs => rw [show t = F + (t - F) by dsimp [F]; omega, MultiTapeTM.runFrom_add, h4, hpz]
  refine ⟨T, by dsimp [T]; omega, hfinal, ?_, ?_, ?_⟩
  · intro t ht
    change (0 < t → (H.runFrom d t).state ≠ some ⟨B2bTestPhase.anchor, ()⟩) ∧
      ∀ b', (H.runFrom d t).state ≠ some ⟨B2bTestPhase.verdict, B2bVerdictState.done b'⟩
    rcases hcover t (by omega) with h | h | h | h | h | h
    · subst t
      simp [d, a, b2b_trialCfg, Cfg.init, Cfg.mapState]
    · obtain ⟨w, hw, heq, he⟩ := h
      rw [he]
      simp [Cfg.mapState, Option.map_eq_some_iff]
    · obtain ⟨w, hw, heq, he⟩ := h
      rw [he]
      simp [Cfg.mapState, Option.map_eq_some_iff]
    · obtain ⟨w, hw, heq, he⟩ := h
      rw [he]
      simp [Cfg.mapState, Option.map_eq_some_iff]
    · obtain ⟨w, hw, heq, he⟩ := h
      rw [he]
      simp [Cfg.mapState, Option.map_eq_some_iff]
    · obtain ⟨w, hw, heq, he⟩ := h
      rw [he]
      constructor
      · intro _
        simp [Cfg.mapState, Option.map_eq_some_iff]
      · intro b'
        have hw' : w < 2 := by dsimp [T] at ht; omega
        simpa [Cfg.mapState, Option.map_eq_some_iff] using hzCut w hw' b'
  · intro t ht
    change (H.runFrom d t).state ≠ none ∧ (H.runFrom d t).output = []
    constructor
    · intro hh
      have hf := hfinal
      rw [show T = t + (T - t) by omega, MultiTapeTM.runFrom_add,
        MultiTapeTM.runFrom_of_halt _ hh] at hf
      have he := congrArg Cfg.state hf
      rw [hh] at he
      simp [z', b2b_trialCfg, Cfg.init, Cfg.mapState] at he
    · have ho := (H.output_prefix d ht).length_le
      rw [hfinal] at ho
      simpa [z', b2b_trialCfg, Cfg.init, Cfg.mapState] using ho
  · intro t ht j
    change |(H.runFrom d t).workTapePos j| ≤ _
    rcases hcover t ht with h | h | h | h | h | h
    · subst t
      simp [d, a, b2b_trialCfg, Cfg.init, Cfg.mapState]
      positivity
    · obtain ⟨w, hw, _, he⟩ := h
      rw [he]
      exact (hiHeads w hw j).trans (by omega)
    · obtain ⟨w, hw, _, he⟩ := h
      rw [he]
      change |((embedEmitRetTM (Function.Embedding.refl _) (b2b_rewindTM _)).runFrom
        (r.mapState Sum.inl) w).workTapePos j| ≤ _
      rw [hrHeads w hw]
      simp only [r, b2b_trialCfg]
      split_ifs <;> simp <;> omega
    · obtain ⟨w, hw, _, he⟩ := h
      rw [he]
      exact (hcHeads w hw j).trans (by omega)
    · obtain ⟨w, hw, _, he⟩ := h
      rw [he]
      exact (hvHeads w hw j).trans (by omega)
    · obtain ⟨w, hw, _, he⟩ := h
      rw [he]
      exact (hzHeads w hw j).trans (by omega)

/-- Rejection clears the shared buffer and advances the certificate once,
returning to the body's anchor with blank scratch and origin heads.

**Proof sketch.** Compose the public framed clear and successful increment
contracts through the existing body phase host. Equal certificate lengths
identify the increment's whole-tape result. Before the final dispatch every
state is in the clear or increment phase; their public trajectories stay
inside the buffer-length window. -/
private theorem b2b_reject_suffix (MV MI MP : FinTM Bool) (x u v : List Bool)
    (hsucc : incFixed u = some v) (hlen : v.length = u.length) :
    let H := b2b_bodyTM MV MI MP
    let d := b2b_trialCfg MV MI MP (⟨B2bBodyPhase.clear, SweepPhase.sweep⟩ :
      Σ j, b2b_bodyState MV MI j) (x := x) 1 u (x ++ u) [] 0 0
    ∃ T : ℕ, 0 < T ∧ H.runFrom d T =
        b2b_trialCfg MV MI MP (⟨B2bBodyPhase.test, ⟨B2bTestPhase.anchor, ()⟩⟩ :
          Σ j, b2b_bodyState MV MI j) 1 v [] [] 0 0 ∧
      (∀ r < T,
        (H.runFrom d r).state ≠ some ⟨.test, ⟨.anchor, ()⟩⟩ ∧
        (H.runFrom d r).state ≠ some ⟨.test, ⟨.verdict, B2bVerdictState.done true⟩⟩) ∧
      ∀ r ≤ T, ∀ j, |(H.runFrom d r).workTapePos j| ≤ (x.length + u.length + 1 : ℕ) := by
  classical
  dsimp only
  let H := b2b_bodyTM MV MI MP
  let U := b2b_wordTape MV.k MI.k MP.k 0
  let BUF := b2b_wordTape MV.k MI.k MP.k 1
  let y := x ++ u
  let a := b2b_trialCfg MV MI MP SweepPhase.sweep (x := x) 1 u y [] 0 0
  let a' := b2b_trialCfg MV MI MP SweepPhase.done (x := x) 1 u [] [] 0 0
  let b := b2b_trialCfg MV MI MP FlagPhase.run (x := x) 1 u [] [] 0 0
  let b' := b2b_trialCfg MV MI MP (FlagPhase.done true) (x := x) 1 v [] [] 0 0
  let C := 2 * y.length + 2
  let I := 2 * (u.takeWhile id).length + 2
  let T := (C + 1) + (I + 1)
  let d : Cfg (b2b_tapeCount MV.k MI.k MP.k) Bool (Σ j, b2b_bodyState MV MI j) x :=
    a.mapState (Sigma.mk B2bBodyPhase.clear)
  have hc := clearTM_run_ofCfg BUF y a rfl (by
    intro z _ _
    simp [a, b2b_trialCfg, BUF, b2b_wordTape])
  have hcEnd : (b2b_bodyPhases MV MI MP .clear).runFrom a C = a' := by
    rw [hc.1]
    apply Cfg.ext <;> try rfl
    funext j z
    by_cases hj : j = BUF
    · subst j
      by_cases h0 : 0 ≤ z
      · by_cases hn : z < (y.length : ℤ)
        · simp [a, a', b2b_trialCfg, BUF, b2b_wordTape, h0, hn]
        · have hg : y.length ≤ z.toNat := by omega
          simp [a, a', b2b_trialCfg, BUF, b2b_wordTape, h0, hn,
            FinTM.bufferTape]
      · simp [a, a', b2b_trialCfg, BUF, b2b_wordTape, h0, FinTM.bufferTape]
    · simp [a, a', b2b_trialCfg, BUF, hj]
  have hi := incrementTM_run_succ_ofCfg U u v hsucc b rfl (by
    intro z _ _
    simp [b, b2b_trialCfg, U, b2b_wordTape])
  have hiEnd : (b2b_bodyPhases MV MI MP .increment).runFrom b I = b' := by
    rw [hi.1]
    apply Cfg.ext <;> try rfl
    funext j z
    by_cases hj : j = U
    · subst j
      by_cases h0 : 0 ≤ z
      · by_cases hn : z < (u.length : ℤ)
        · simp [b, b', b2b_trialCfg, U, b2b_wordTape, h0, hn]
        · have hu : u.length ≤ z.toNat := by omega
          have hv : v.length ≤ z.toNat := by omega
          simp [b, b', b2b_trialCfg, U, b2b_wordTape, h0, hn,
            FinTM.bufferTape, List.getElem?_eq_none hv]
      · simp [b, b', b2b_trialCfg, U, b2b_wordTape, h0, FinTM.bufferTape]
    · simp [b, b', b2b_trialCfg, U, hj]
  have pc := phaseHostTM_run (b2b_bodyPhases MV MI MP)
    ⟨.test, ⟨.anchor, ()⟩⟩ (b2b_bodyRedirect MV MI) .clear a a' C hcEnd SweepPhase.done rfl
    ⟨.increment, FlagPhase.run⟩ rfl (by
      intro r hr q hq
      cases q with
      | sweep => rfl
      | rewind => rfl
      | done => exact False.elim (hc.2.1 r hr hq))
  have pi := phaseHostTM_run (b2b_bodyPhases MV MI MP)
    ⟨.test, ⟨.anchor, ()⟩⟩ (b2b_bodyRedirect MV MI) .increment b b' I hiEnd (FlagPhase.done true) rfl
    ⟨.test, ⟨.anchor, ()⟩⟩ rfl (by
      intro r hr q hq
      cases q with
      | run => rfl
      | rewind b => rfl
      | done b => exact False.elim (hi.2.1 r hr b hq))
  have hmid : H.runFrom d (C + 1) = b.mapState (Sigma.mk B2bBodyPhase.increment) := pc.2
  have hfinal : H.runFrom d T =
      b2b_trialCfg MV MI MP (⟨B2bBodyPhase.test, ⟨B2bTestPhase.anchor, ()⟩⟩ :
        Σ j, b2b_bodyState MV MI j) (x := x) 1 v [] [] 0 0 := by
    rw [show T = (C + 1) + (I + 1) from rfl, MultiTapeTM.runFrom_add, hmid, pi.2]
    rfl
  have hcover (r : ℕ) (hr : r < T) :
      (∃ t ≤ C, H.runFrom d r =
        ((b2b_bodyPhases MV MI MP .clear).runFrom a t).mapState (Sigma.mk B2bBodyPhase.clear)) ∨
      (∃ t ≤ I, H.runFrom d r =
        ((b2b_bodyPhases MV MI MP .increment).runFrom b t).mapState (Sigma.mk B2bBodyPhase.increment)) := by
    by_cases hpre : r ≤ C
    · exact Or.inl ⟨r, hpre, pc.1 r hpre⟩
    · right
      refine ⟨r - (C + 1), by dsimp [T] at hr; omega, ?_⟩
      conv_lhs => rw [show r = (C + 1) + (r - (C + 1)) by omega,
        MultiTapeTM.runFrom_add, hmid]
      exact pi.1 _ (by dsimp [T] at hr; omega)
  refine ⟨T, by dsimp [T]; omega, hfinal, ?_, ?_⟩
  · intro r hr
    change (H.runFrom d r).state ≠ some ⟨B2bBodyPhase.test, ⟨B2bTestPhase.anchor, ()⟩⟩ ∧
      (H.runFrom d r).state ≠ some ⟨B2bBodyPhase.test, ⟨B2bTestPhase.verdict, B2bVerdictState.done true⟩⟩
    rcases hcover r hr with ⟨t, _, he⟩ | ⟨t, _, he⟩ <;>
      rw [he] <;> simp [Cfg.mapState, Option.map_eq_some_iff]
  · intro r hr j
    change |(H.runFrom d r).workTapePos j| ≤ _
    rcases lt_or_eq_of_le hr with hr' | rfl
    · rcases hcover r hr' with ⟨t, ht, he⟩ | ⟨t, ht, he⟩
      · rw [he]
        have hh := hc.2.2 j t ht
        change |((clearTM _ BUF).runFrom a t).workTapePos j| ≤ _
        have hz : a.workTapePos j = 0 := by simp [a, b2b_trialCfg]
        rw [hz] at hh
        split_ifs at hh
        · have hm := Finset.mem_Icc.mp hh
          simp only [y, List.length_append, Nat.cast_add] at hm
          exact abs_le.mpr ⟨by omega, by omega⟩
        · rw [hh]; positivity
      · rw [he]
        have hh := hi.2.2 j t ht
        change |((incrementTM _ U).runFrom b t).workTapePos j| ≤ _
        have hz : b.workTapePos j = 0 := by simp [b, b2b_trialCfg]
        rw [hz] at hh
        have hw := (List.takeWhile_sublist (p := id) (l := u)).length_le
        split_ifs at hh
        · have hm := Finset.mem_Icc.mp hh
          exact abs_le.mpr ⟨by omega, by omega⟩
        · rw [hh]; positivity
    · rw [hfinal]
      simp only [b2b_trialCfg, ite_self, abs_zero]
      positivity

/-- A counted round uses the shared trial once: acceptance reaches the escape
anchor, while rejection clears the buffer and returns with the successor
certificate. No interior state is either loop anchor.

**Proof sketch.** Transfer the shared trial into the body's test phase using
public machine agreement. On rejection use the public phase dispatch and the
proved clear/increment suffix. A prefix split proves the same fixed radius
for both outcomes. The final live configuration excludes earlier halting. -/
private theorem b2b_round_run (MV MI MP : FinTM Bool) (x u v : List Bool)
    (b : Bool) (ti si sv : ℕ) (hi : MI.ComputesInTime x x ti)
    (his : MI.tm.spaceUsed (MI.tm.initCfg x) ti ≤ si)
    (hv : LogProg.CleanRun (LogProg.cleanTM MV.tm MV.tm.q₀)
      (LogProg.CleanSt.init MV.tm.q₀) (x ++ u) b sv)
    (hsucc : incFixed u = some v) (hlen : v.length = u.length) :
    let H := b2b_bodyTM MV MI MP
    let a : Σ j, b2b_bodyState MV MI j := ⟨.test, ⟨.anchor, ()⟩⟩
    let e : Σ j, b2b_bodyState MV MI j := ⟨.test, ⟨.verdict, B2bVerdictState.done true⟩⟩
    let d := b2b_trialCfg MV MI MP a (x := x) 1 u [] [] 0 0
    ∃ T : ℕ, 0 < T ∧ H.runFrom d T =
        (if b then b2b_trialCfg MV MI MP e 1 u (x ++ u) [] 0 0
         else b2b_trialCfg MV MI MP a 1 v [] [] 0 0) ∧
      (∀ r, 0 < r → r < T → ∃ q, (H.runFrom d r).state = some q ∧ q ≠ a ∧ q ≠ e) ∧
      ∀ r ≤ T, ∀ j, |(H.runFrom d r).workTapePos j| ≤
        (x.length + u.length + sv + si + 1 : ℕ) := by
  classical
  dsimp only
  let H := b2b_bodyTM MV MI MP
  let a : Σ j, b2b_bodyState MV MI j := ⟨.test, ⟨.anchor, ()⟩⟩
  let e : Σ j, b2b_bodyState MV MI j := ⟨.test, ⟨.verdict, B2bVerdictState.done true⟩⟩
  let c := b2b_trialCfg MV MI MP (⟨B2bTestPhase.anchor, ()⟩ : Σ j, b2b_testState MV MI j)
    (x := x) 1 u [] [] 0 0
  let c' := b2b_trialCfg MV MI MP (⟨B2bTestPhase.verdict, B2bVerdictState.done b⟩ :
    Σ j, b2b_testState MV MI j) (x := x) 1 u (x ++ u) [] 0 0
  let d := b2b_trialCfg MV MI MP a (x := x) 1 u [] [] 0 0
  let final := if b then b2b_trialCfg MV MI MP e (x := x) 1 u (x ++ u) [] 0 0
    else b2b_trialCfg MV MI MP a 1 v [] [] 0 0
  suffices h : ∃ T : ℕ, 0 < T ∧ H.runFrom d T = final ∧
      (∀ r, 0 < r → r < T → (H.runFrom d r).state ≠ some a ∧
        (H.runFrom d r).state ≠ some e) ∧
      ∀ r ≤ T, ∀ j, |(H.runFrom d r).workTapePos j| ≤
        (x.length + u.length + sv + si + 1 : ℕ) by
    obtain ⟨T, hT, he, hcut, hheads⟩ := h
    refine ⟨T, hT, he, ?_, hheads⟩
    intro r hr hrT
    have hlive : (H.runFrom d r).state ≠ none := by
      intro hh
      have hf := he
      rw [show T = r + (T - r) by omega, MultiTapeTM.runFrom_add,
        MultiTapeTM.runFrom_of_halt _ hh] at hf
      have hh' := congrArg Cfg.state hf
      rw [hh] at hh'
      cases b <;> simp [final, b2b_trialCfg, Cfg.init] at hh'
    obtain ⟨q, hq⟩ := Option.ne_none_iff_exists.mp hlive
    exact ⟨q, hq.symm, fun h => (hcut r hr hrT).1 (hq.symm.trans (congrArg some h)),
      fun h => (hcut r hr hrT).2 (hq.symm.trans (congrArg some h))⟩
  obtain ⟨T, hT, htRun, htCut, _, htHeads⟩ := b2b_trial_run MV MI MP x u b ti si sv hi his hv
  have hguard (t : ℕ) (htt : t < T) (q : Σ j, b2b_testState MV MI j)
      (hq : ((b2b_testTM MV MI MP).runFrom c t).state = some q) :
      b2b_bodyRedirect MV MI .test q = none := by
    rcases q with ⟨j, q⟩
    cases j <;> try rfl
    cases q with
    | left => rfl
    | read => rfl
    | done b' =>
      exact False.elim ((htCut t htt).2 b' hq)
  have hprefix (t : ℕ) (htt : t ≤ T) : H.runFrom d t =
      ((b2b_testTM MV MI MP).runFrom c t).mapState (Sigma.mk B2bBodyPhase.test) :=
    phaseHostTM_run_le (b2b_bodyPhases MV MI MP) ⟨.test, ⟨.anchor, ()⟩⟩
      (b2b_bodyRedirect MV MI) .test c T hguard t htt
  cases b with
  | true =>
    refine ⟨T, hT, ?_, ?_, ?_⟩
    · rw [hprefix T le_rfl, htRun]
      rfl
    · intro t hpos hlt
      rw [hprefix t (by omega)]
      have ha := (htCut t hlt).1 hpos
      have he := (htCut t hlt).2 true
      simpa [a, e, Cfg.mapState, Option.map_eq_some_iff] using And.intro ha he
    · intro t ht j
      rw [hprefix t ht]
      exact htHeads t ht j
  | false =>
    have hp := phaseHostTM_run (b2b_bodyPhases MV MI MP)
      ⟨.test, ⟨.anchor, ()⟩⟩ (b2b_bodyRedirect MV MI) .test c c' T htRun
      ⟨.verdict, B2bVerdictState.done false⟩ rfl ⟨.clear, SweepPhase.sweep⟩ rfl hguard
    let s := b2b_trialCfg MV MI MP (⟨B2bBodyPhase.clear, SweepPhase.sweep⟩ :
      Σ j, b2b_bodyState MV MI j) (x := x) 1 u (x ++ u) [] 0 0
    have hmid : H.runFrom d (T + 1) = s := hp.2
    obtain ⟨S, hS, hsRun, hsCut, hsHeads⟩ := b2b_reject_suffix MV MI MP x u v hsucc hlen
    refine ⟨(T + 1) + S, by omega, ?_, ?_, ?_⟩
    · rw [MultiTapeTM.runFrom_add, hmid, hsRun]
      rfl
    · intro t hpos hlt
      by_cases hpre : t < T
      · rw [hprefix t (by omega)]
        have ha := (htCut t hpre).1 hpos
        have he := (htCut t hpre).2 true
        simpa [a, e, Cfg.mapState, Option.map_eq_some_iff] using And.intro ha he
      · by_cases htEq : t = T
        · subst t
          rw [hprefix T le_rfl, htRun]
          simp [a, e, b2b_trialCfg, Cfg.mapState, Cfg.init]
          constructor <;> intro hh <;> cases hh
        · have heq : H.runFrom d t = H.runFrom s (t - (T + 1)) := by
            conv_lhs => rw [show t = (T + 1) + (t - (T + 1)) by omega,
              MultiTapeTM.runFrom_add, hmid]
          rw [heq]
          exact hsCut _ (by omega)
    · intro t ht j
      by_cases hpre : t ≤ T
      · rw [hprefix t hpre]
        exact htHeads t hpre j
      · have heq : H.runFrom d t = H.runFrom s (t - (T + 1)) := by
          conv_lhs => rw [show t = (T + 1) + (t - (T + 1)) by omega,
            MultiTapeTM.runFrom_add, hmid]
        rw [heq]
        exact (hsHeads _ (by omega) j).trans (by omega)

/-- The host's answer phase emits its singleton and halts in two steps,
leaving all work heads fixed throughout.

**Proof sketch.** Transfer the existing answer contract into its unredirected
host phase. The two emission actions have zero movement on every work tape,
so their three prefix configurations have the same work heads. -/
private theorem b2b_finish_answer (MV MI MP : FinTM Bool) {x : List Bool} (b : Bool)
    (c : Cfg (b2b_tapeCount MV.k MI.k MP.k + 1) Bool (Fin 2) x)
    (hc : c.state = some 0) :
    let H := (b2b_host MV MI MP).tm
    let d := c.mapState (Sigma.mk (B2bHostPhase.answer b))
    (H.runFrom d 2).state = none ∧ (H.runFrom d 2).output = c.output ++ [b] ∧
      ∀ r ≤ 2, (H.runFrom d r).workTapePos = c.workTapePos := by
  classical
  dsimp only
  let H := (b2b_host MV MI MP).tm
  let M := b2b_answerTM (b2b_tapeCount MV.k MI.k MP.k + 1) b
  have hp (t : ℕ) : H.runFrom (c.mapState (Sigma.mk (B2bHostPhase.answer b))) t =
      (M.runFrom c t).mapState (Sigma.mk (B2bHostPhase.answer b)) :=
    phaseHostTM_run_le (b2b_hostPhases MV MI MP) _ (b2b_hostRedirect MV MI MP)
      (.answer b) c t (fun _ _ _ _ => rfl) t le_rfl
  obtain ⟨hh, ho⟩ := b2b_answer_run b c hc
  refine ⟨?_, ?_, ?_⟩
  · rw [hp]
    simp only [Cfg.mapState, hh, Option.map_none]
  · rw [hp]
    exact ho
  · intro r hr
    rw [hp]
    change (M.runFrom c r).workTapePos = c.workTapePos
    have h1 : M.runFrom c 1 = { c with state := some 1, output := c.output ++ [b] } := by
      simp [M, b2b_answerTM, MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.step, hc,
        FinTM.emitAction, Action.apply]
    interval_cases r
    · rfl
    · rw [h1]
    · rw [MultiTapeTM.runFrom_succ_eq_step', h1]
      simp [M, b2b_answerTM, MultiTapeTM.step, FinTM.emitAction, Action.apply]

/-- After counter exhaustion the host reuses the shared trial and emits its
answer. The counter tape is arbitrary and stays at its fixed origin.

**Proof sketch.** Embed the shared trial along the first-tape bank, apply the
public phase-host dispatch at its first verdict, and invoke the proved final
answer phase. Selected heads follow the shared trial and the counter head is
fixed by the embedding frame. The answer preserves those same heads. -/
private theorem b2b_finish_last (MV MI MP : FinTM Bool) (x u : List Bool)
    (ct : ℤ → Option Bool) (b : Bool) (ti si sv : ℕ)
    (hi : MI.ComputesInTime x x ti) (his : MI.tm.spaceUsed (MI.tm.initCfg x) ti ≤ si)
    (hv : LogProg.CleanRun (LogProg.cleanTM MV.tm MV.tm.q₀)
      (LogProg.CleanSt.init MV.tm.q₀) (x ++ u) b sv) :
    let H := (b2b_host MV MI MP).tm
    let c := b2b_trialCfg MV MI MP (⟨B2bBodyPhase.test, ⟨B2bTestPhase.anchor, ()⟩⟩ :
      Σ j, b2b_bodyState MV MI j) (x := x) 1 u [] [] 0 0
    let d := (counterLoopCfg (some .done) c ct 0).mapState
      (fun _ => (⟨B2bHostPhase.last, ⟨B2bTestPhase.anchor, ()⟩⟩ : Σ j, b2b_hostState MV MI MP j))
    ∃ T : ℕ, (H.runFrom d T).state = none ∧ (H.runFrom d T).output = [b] ∧
      ∀ r ≤ T, ∀ j, |(H.runFrom d r).workTapePos j| ≤
        (x.length + u.length + sv + si + 1 : ℕ) := by
  classical
  dsimp only
  let K := b2b_tapeCount MV.k MI.k MP.k
  let H := (b2b_host MV MI MP).tm
  let M := b2b_testTM MV MI MP
  let c := b2b_trialCfg MV MI MP (⟨B2bTestPhase.anchor, ()⟩ : Σ j, b2b_testState MV MI j)
    (x := x) 1 u [] [] 0 0
  let c' := b2b_trialCfg MV MI MP (⟨B2bTestPhase.verdict, B2bVerdictState.done b⟩ :
    Σ j, b2b_testState MV MI j) (x := x) 1 u (x ++ u) [] 0 0
  let E := embedEmitTM Fin.castSuccEmb M
  let d := embedEmitCfg Fin.castSuccEmb (fun _ => ct) (fun _ => 0) [] c
  let d' := embedEmitCfg Fin.castSuccEmb (fun _ => ct) (fun _ => 0) [] c'
  obtain ⟨T, _, hrun, hcut, _, hheads⟩ := b2b_trial_run MV MI MP x u b ti si sv hi his hv
  have ep (t : ℕ) : E.runFrom d t =
      embedEmitCfg Fin.castSuccEmb (fun _ => ct) (fun _ => 0) [] (M.runFrom c t) :=
    embedEmitTM_runFrom Fin.castSuccEmb M (fun _ => ct) (fun _ => 0) [] c t
  have he : E.runFrom d T = d' := by rw [ep, hrun]
  have hp := phaseHostTM_run (b2b_hostPhases MV MI MP)
    ⟨.setup, Sum.inl (.init MP.tm.q₀)⟩ (b2b_hostRedirect MV MI MP) .last d d' T he
    ⟨.verdict, B2bVerdictState.done b⟩ rfl ⟨.answer b, (0 : Fin 2)⟩ rfl (by
      intro t ht q hq
      rw [ep] at hq
      change (M.runFrom c t).state = some q at hq
      rcases q with ⟨j, q⟩
      cases j <;> try rfl
      cases q with
      | left => rfl
      | read => rfl
      | done b' => exact False.elim ((hcut t ht).2 b' hq))
  let ans := d'.mapState (fun _ => (0 : Fin 2))
  have hans := b2b_finish_answer MV MI MP b ans rfl
  have hfinal : H.runFrom (d.mapState (Sigma.mk B2bHostPhase.last)) ((T + 1) + 2) =
      H.runFrom (ans.mapState (Sigma.mk (B2bHostPhase.answer b))) 2 := by
    rw [MultiTapeTM.runFrom_add, hp.2, b2b_dispatch_retag]
    rfl
  have hlast : Fin.last K ∉ Set.range (Fin.castSuccEmb : Fin K ↪ Fin (K + 1)) := by
    rintro ⟨i, hi⟩
    exact Fin.castSucc_ne_last i hi
  have hb (t : ℕ) (ht : t ≤ T) (j : Fin (K + 1)) :
      |(E.runFrom d t).workTapePos j| ≤ (x.length + u.length + sv + si + 1 : ℕ) := by
    rw [ep]
    refine Fin.lastCases ?_ (fun i => ?_) j
    · have hf := ((embedEmitTM_frame Fin.castSuccEmb M (fun _ => ct) (fun _ => 0) []
        (M.runFrom c t) 0).1 (Fin.last K) hlast).2
      have hf' : (embedEmitCfg Fin.castSuccEmb (fun _ => ct) (fun _ => 0) []
          (M.runFrom c t)).workTapePos (Fin.last K) = 0 := by
        simpa only [MultiTapeTM.runFrom_zero] using hf
      rw [hf']; positivity
    · rw [show i.castSucc = Fin.castSuccEmb i from rfl, embedEmitCfg_selected_pos]
      exact hheads t ht i
  have hbEnd (j : Fin (K + 1)) : |ans.workTapePos j| ≤
      (x.length + u.length + sv + si + 1 : ℕ) := by
    have hh := hb T le_rfl j
    rw [he] at hh
    exact hh
  change ∃ T', (H.runFrom (d.mapState (Sigma.mk B2bHostPhase.last)) T').state = none ∧
    (H.runFrom (d.mapState (Sigma.mk B2bHostPhase.last)) T').output = [b] ∧
    ∀ r ≤ T', ∀ j, |(H.runFrom (d.mapState (Sigma.mk B2bHostPhase.last)) r).workTapePos j| ≤ _
  refine ⟨(T + 1) + 2, ?_, ?_, ?_⟩
  · rw [hfinal]
    exact hans.1
  · rw [hfinal, hans.2.1]
    rfl
  · intro r hr j
    by_cases hpre : r ≤ T
    · rw [hp.1 r hpre]
      exact hb r hpre j
    · have heq : H.runFrom (d.mapState (Sigma.mk B2bHostPhase.last)) r =
          H.runFrom (ans.mapState (Sigma.mk (B2bHostPhase.answer b))) (r - (T + 1)) := by
        conv_lhs => rw [show r = (T + 1) + (r - (T + 1)) by omega,
          MultiTapeTM.runFrom_add, hp.2, b2b_dispatch_retag]
        rfl
      rw [heq, hans.2.2 _ (by omega)]
      exact hbEnd j

/-- The remaining certificate search starts at the established setup seam and
halts with its single decision bit, within fixed windows independent of the
number of counted trials.

**Proof sketch.** Prove one shared test contract by composing the identity
capture, native rewind, framed append copy, captured virtual verifier call,
and verdict reader through the existing phase host. On rejection clear the
buffer and increment the certificate. Apply the counter loop's escape or done
contract along the existing certificate orbit, using classically chosen exact
round durations. On exhaustion reuse the test for the final certificate,
including the sole empty certificate when the width is zero. Compose with the
answer emitter. The counter/body trajectory clauses and the shared test's
fixed windows give the radius below, without any factor counting trials.

Status: proved (B2b fill, delivery 3). Setup is `b2b_setup_run`; this helper
covers the shared trial (`b2b_trial_run`), the counted loop, the final trial and
the answer. -/
private theorem b2b_search_contract (Q e cV cI : ℕ) (V : Language Bool)
    (MV MI MP : FinTM Bool)
    (hV : ∀ y : List Bool,
      LogProg.CleanRun (LogProg.cleanTM MV.tm MV.tm.q₀)
        (LogProg.CleanSt.init MV.tm.q₀) y
        (MultiTapeTM.indicator (V : Set (List Bool)) y) (cV * (y.length ^ e + 1)))
    (hI : MI.ComputesFunInTime id (fun n => cI * (n + 1)))
    (hIs : ∀ (x : List Bool) (t : ℕ), MI.tm.spaceUsed (MI.tm.initCfg x) t ≤ cI)
    (x : List Bool) :
    let H := (b2b_host MV MI MP).tm
    let d := b2b_setupCfg MV MI MP (⟨B2bHostPhase.loop, CounterLoopState.dec .run⟩ :
      Σ j, b2b_hostState MV MI MP j) (x := x) 1 (List.replicate Q false) (List.replicate Q true)
    ∃ t : ℕ, (H.runFrom d t).state = none ∧
      (H.runFrom d t).output =
        [MultiTapeTM.indicator {z : List Bool | ∃ u, u.length = Q ∧ z ++ u ∈ V} x] ∧
      ∀ u ≤ t, ∀ j, |(H.runFrom d u).workTapePos j| ≤
        (x.length + Q + cV * ((x.length + Q) ^ e + 1) + cI + 1 : ℕ) := by
  classical
  dsimp only
  let K := b2b_tapeCount MV.k MI.k MP.k
  let H := (b2b_host MV MI MP).tm
  let B := b2b_bodyTM MV MI MP
  let a : Σ j, b2b_bodyState MV MI j := ⟨.test, ⟨.anchor, ()⟩⟩
  let e' : Σ j, b2b_bodyState MV MI j := ⟨.test, ⟨.verdict, B2bVerdictState.done true⟩⟩
  let G (u : List Bool) := b2b_trialCfg MV MI MP a (x := x) 1 u [] [] 0 0
  let A (u : List Bool) := b2b_trialCfg MV MI MP e' (x := x) 1 u (x ++ u) [] 0 0
  let word (r : ℕ) := enumWord Q r
  let yes (r : ℕ) := MultiTapeTM.indicator (V : Set (List Bool)) (x ++ word r)
  let d := 2 ^ Q - 1
  let sv := cV * ((x.length + Q) ^ e + 1)
  let W := x.length + Q + sv + cI + 1
  let init := G (List.replicate Q false)
  let w := List.replicate Q true
  let dc := counterLoopCfg (some (CounterLoopState.dec FlagPhase.run)) init (FinTM.bufferTape w) 0
  have hpow : 1 ≤ 2 ^ Q := Nat.one_le_two_pow
  have hclean (r : ℕ) : LogProg.CleanRun (LogProg.cleanTM MV.tm MV.tm.q₀)
      (LogProg.CleanSt.init MV.tm.q₀) (x ++ word r) (yes r) sv := by
    simpa only [yes, word, List.length_append, Meyer.length_enumWord] using hV (x ++ enumWord Q r)
  have hround (r : ℕ) (hr : r < d) : ∃ T : ℕ, 0 < T ∧
      B.runFrom (G (word r)) T = (if yes r then A (word r) else G (word (r + 1))) ∧
      (∀ t, 0 < t → t < T → ∃ q,
        (B.runFrom (G (word r)) t).state = some q ∧ q ≠ a ∧ q ≠ e') ∧
      ∀ t ≤ T, ∀ j, |(B.runFrom (G (word r)) t).workTapePos j| ≤ (W : ℤ) := by
    have hinc := Meyer.incFixed_enumWord Q r (by dsimp [d] at hr; omega)
    have hh := b2b_round_run MV MI MP x (word r) (word (r + 1)) (yes r)
      (cI * (x.length + 1)) cI sv (hI x) (hIs x _) (hclean r) hinc
      (by simp [word])
    simpa only [B, G, A, a, e', W, word, Meyer.length_enumWord] using hh
  let duration (r : Fin d) : ℕ := Classical.choose (hround r r.isLt)
  have duration_spec (r : Fin d) := Classical.choose_spec (hround r r.isLt)
  have index_inj {r s : Fin d} (hc : G (word r) = G (word s)) : r = s := by
    have hw : word r = word s := by
      apply List.ext_getElem?
      intro n
      have he := congrFun (congrFun (congrArg Cfg.workTapes hc)
        (b2b_wordTape MV.k MI.k MP.k 0)) (n : ℤ)
      simpa [G, b2b_trialCfg, b2b_wordTape, FinTM.bufferTape] using he
    apply Fin.ext
    have hn := congrArg TimeHierarchy.ctrVal hw
    rw [Meyer.ctrVal_enumWord Q r (by have := r.isLt; dsimp [d] at this; omega),
      Meyer.ctrVal_enumWord Q s (by have := s.isLt; dsimp [d] at this; omega)] at hn
    exact hn
  let τ (c : Cfg K Bool (Σ j, b2b_bodyState MV MI j) x) : ℕ :=
    if h : ∃ r : Fin d, c = G (word r) then duration (Classical.choose h) else 0
  have τ_eq (r : Fin d) : τ (G (word r)) = duration r := by
    have hx : ∃ s : Fin d, G (word r) = G (word s) := ⟨r, rfl⟩
    dsimp only [τ]
    rw [dif_pos hx]
    exact congrArg duration (index_inj (Classical.choose_spec hx)).symm
  have round_spec (r : ℕ) (hr : r < d) :
      0 < τ (G (word r)) ∧
      B.runFrom (G (word r)) (τ (G (word r))) =
        (if yes r then A (word r) else G (word (r + 1))) ∧
      (∀ t, 0 < t → t < τ (G (word r)) → ∃ q,
        (B.runFrom (G (word r)) t).state = some q ∧ q ≠ a ∧ q ≠ e') ∧
      ∀ t ≤ τ (G (word r)), ∀ j,
        |(B.runFrom (G (word r)) t).workTapePos j| ≤ (W : ℤ) := by
    have hh := duration_spec ⟨r, hr⟩
    have he := τ_eq ⟨r, hr⟩
    simpa only [he] using hh
  have orbit (r : ℕ) (hr : r ≤ d) (hn : ∀ s < r, yes s = false) :
      counterLoopOrbit B τ init r = G (word r) := by
    induction r with
    | zero =>
      have hz := b2b_certificate_orbit Q 0 (by omega)
      simpa only [counterLoopOrbit, Function.iterate_zero_apply, init, word] using congrArg G hz
    | succ r ih =>
      have hrd : r < d := by omega
      change (fun c => B.runFrom c (τ c))^[r + 1] init = _
      rw [Function.iterate_succ_apply']
      change B.runFrom (counterLoopOrbit B τ init r) (τ (counterLoopOrbit B τ init r)) = _
      rw [ih (by omega) (fun s hs => hn s (by omega)), (round_spec r hrd).2.1,
        hn r (by omega)]
      rfl
  have hstart : b2b_setupCfg MV MI MP
      (⟨B2bHostPhase.loop, CounterLoopState.dec FlagPhase.run⟩ : Σ j, b2b_hostState MV MI MP j)
      (x := x) 1 (List.replicate Q false) w = dc.mapState (Sigma.mk B2bHostPhase.loop) := by
    dsimp only [dc]
    rw [counter_cfg_eq]
    apply Cfg.ext <;> try rfl
    · funext j z
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp [Cfg.mapState, b2b_setupCfg, G, init, b2b_trialCfg, Ne.symm (Fin.castSucc_ne_last _)]
      · simp [Cfg.mapState, b2b_setupCfg, G, init, b2b_trialCfg, Fin.castSucc_inj, Fin.castSucc_ne_last]
    · funext j
      refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [Cfg.mapState, G, init, b2b_trialCfg, b2b_setupCfg, Cfg.init]
  rw [hstart]
  change ∃ t, (H.runFrom (dc.mapState (Sigma.mk B2bHostPhase.loop)) t).state = none ∧
    (H.runFrom (dc.mapState (Sigma.mk B2bHostPhase.loop)) t).output =
      [MultiTapeTM.indicator {z : List Bool | ∃ u, u.length = Q ∧ z ++ u ∈ V} x] ∧
    ∀ u ≤ t, ∀ j, |(H.runFrom (dc.mapState (Sigma.mk B2bHostPhase.loop)) u).workTapePos j| ≤ (W : ℤ)
  by_cases hex : ∃ r < d, x ++ word r ∈ V
  · let r₀ := Nat.find hex
    have hr₀ : r₀ < d := (Nat.find_spec hex).1
    have hy₀ : yes r₀ = true := by
      have hm : x ++ word r₀ ∈ V := (Nat.find_spec hex).2
      simp [yes, MultiTapeTM.indicator, hm]
    have hbefore (r : ℕ) (hr : r < r₀) : yes r = false := by
      have hn : x ++ word r ∉ V := by
        intro hm
        exact Nat.find_min hex hr ⟨by omega, hm⟩
      simp [yes, MultiTapeTM.indicator, hn]
    have horbit (r : ℕ) (hr : r ≤ r₀) : counterLoopOrbit B τ init r = G (word r) :=
      orbit r (by omega) (fun s hs => hbefore s (by omega))
    have hend : counterLoopOrbit B τ init (r₀ + 1) = A (word r₀) := by
      change (fun c => B.runFrom c (τ c))^[r₀ + 1] init = _
      rw [Function.iterate_succ_apply']
      change B.runFrom (counterLoopOrbit B τ init r₀) (τ (counterLoopOrbit B τ init r₀)) = _
      rw [horbit r₀ le_rfl, (round_spec r₀ hr₀).2.1, hy₀]
      rfl
    let T := (∑ r ∈ Finset.range (r₀ + 1), τ (counterLoopOrbit B τ init r)) +
      counterOverhead w (r₀ + 1)
    have hl := counterLoopTM_run_escape B a e' (by simp [a, e']; intro hh; cases hh) τ init
      w (FinTM.bufferTape w) 0 (by intros; simp) r₀
      (by simpa only [w, b2b_counter_value] using hr₀) (by
        intro r hr
        rw [horbit r hr]
        exact ⟨rfl, (round_spec r (by omega)).1, (round_spec r (by omega)).2.2.1⟩)
      (by rw [hend]; rfl) T rfl
    let L := counterLoopTM B a (some e')
    let ct := fun q => if (0 : ℤ) ≤ q ∧ q < 0 + (w.length : ℤ)
      then FinTM.bufferTape (counterWord w (r₀ + 1)) (q - 0) else FinTM.bufferTape w q
    let c' := counterLoopCfg (some CounterLoopState.escape) (A (word r₀)) ct 0
    have he : L.runFrom dc T = c' := by
      simpa only [hend] using hl.1
    have hb (t : ℕ) (ht : t ≤ T) (j : Fin (K + 1)) :
        |(L.runFrom dc t).workTapePos j| ≤ (W : ℤ) := by
      refine Fin.lastCases ?_ (fun i => ?_) j
      · have hh : (L.runFrom dc t).workTapePos (Fin.last K) ∈ Finset.Icc (-1) (Q : ℤ) := by
          simpa only [w, List.length_replicate, zero_sub, zero_add] using hl.2.2.1 t ht
        obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hh
        exact abs_le.mpr ⟨by dsimp [W]; omega, by dsimp [W]; omega⟩
      · obtain ⟨r, u, hr, hpos⟩ := hl.2.2.2 t ht
        change |((counterLoopTM B a (some e')).runFrom dc t).workTapePos i.castSucc| ≤ _
        rw [hpos i]
        rcases hr with ⟨hr, hu⟩ | ⟨rfl, rfl⟩
        · rw [horbit r hr] at hu ⊢
          exact (round_spec r (by omega)).2.2.2 u hu i
        · rw [hend]
          simp only [MultiTapeTM.runFrom_zero, A, b2b_trialCfg]
          simp only [ite_self, abs_zero]
          positivity
    have hp := phaseHostTM_run (b2b_hostPhases MV MI MP)
      ⟨.setup, Sum.inl (.init MP.tm.q₀)⟩ (b2b_hostRedirect MV MI MP) .loop dc c' T he
      CounterLoopState.escape rfl ⟨.answer true, (0 : Fin 2)⟩ rfl (by
        intro t ht q hq
        cases q with
        | dec q => rfl
        | body q => rfl
        | done => exact False.elim ((hl.2.1 t ht).1 hq)
        | escape => exact False.elim ((hl.2.1 t ht).2 hq))
    let ans := c'.mapState (fun _ => (0 : Fin 2))
    have hans := b2b_finish_answer MV MI MP true ans rfl
    have hfinal : H.runFrom (dc.mapState (Sigma.mk B2bHostPhase.loop)) ((T + 1) + 2) =
        H.runFrom (ans.mapState (Sigma.mk (B2bHostPhase.answer true))) 2 := by
      rw [MultiTapeTM.runFrom_add, hp.2, b2b_dispatch_retag]
      rfl
    have hbEnd (j : Fin (K + 1)) : |ans.workTapePos j| ≤ (W : ℤ) := by
      have hh := hb T le_rfl j
      rw [he] at hh
      exact hh
    have hm : ∃ u, u.length = Q ∧ x ++ u ∈ V :=
      ⟨word r₀, Meyer.length_enumWord Q r₀, (Nat.find_spec hex).2⟩
    refine ⟨(T + 1) + 2, ?_, ?_, ?_⟩
    · rw [hfinal]
      exact hans.1
    · rw [hfinal, hans.2.1]
      simp [ans, c', counter_cfg_eq, A, b2b_trialCfg, Cfg.mapState,
        MultiTapeTM.indicator, hm]
    · intro t ht j
      by_cases hpre : t ≤ T
      · rw [hp.1 t hpre]
        exact hb t hpre j
      · have htEq : H.runFrom (dc.mapState (Sigma.mk B2bHostPhase.loop)) t =
            H.runFrom (ans.mapState (Sigma.mk (B2bHostPhase.answer true))) (t - (T + 1)) := by
          conv_lhs => rw [show t = (T + 1) + (t - (T + 1)) by omega,
            MultiTapeTM.runFrom_add, hp.2, b2b_dispatch_retag]
          rfl
        rw [htEq, hans.2.2 _ (by omega)]
        exact hbEnd j
  · have hno (r : ℕ) (hr : r < d) : yes r = false := by
      have hn : x ++ word r ∉ V := fun hm => hex ⟨r, hr, hm⟩
      simp [yes, MultiTapeTM.indicator, hn]
    have horbit (r : ℕ) (hr : r ≤ d) : counterLoopOrbit B τ init r = G (word r) :=
      orbit r hr (fun s hs => hno s (by omega))
    let T := (∑ r ∈ Finset.range d, τ (counterLoopOrbit B τ init r)) + counterOverhead w (d + 1)
    have hl := counterLoopTM_run_done B a (some e') τ init w (FinTM.bufferTape w) 0
      (by intros; simp) d (b2b_counter_value Q) (by
        intro r hr
        rw [horbit r (by omega), horbit (r + 1) (by omega)]
        refine ⟨rfl, (round_spec r hr).1, ?_, rfl⟩
        intro u hu hut
        obtain ⟨s, hs, hsa, hse⟩ := (round_spec r hr).2.2.1 u hu hut
        exact ⟨s, hs, hsa, fun hh => hse (Option.some.inj hh).symm⟩) T rfl
    let L := counterLoopTM B a (some e')
    let ct := fun q => if (0 : ℤ) ≤ q ∧ q < 0 + (w.length : ℤ)
      then some true else FinTM.bufferTape w q
    let c' := counterLoopCfg (some CounterLoopState.done) (G (word d)) ct 0
    have he : L.runFrom dc T = c' := by
      simpa only [horbit d le_rfl] using hl.1
    have hb (t : ℕ) (ht : t ≤ T) (j : Fin (K + 1)) :
        |(L.runFrom dc t).workTapePos j| ≤ (W : ℤ) := by
      refine Fin.lastCases ?_ (fun i => ?_) j
      · have hh : (L.runFrom dc t).workTapePos (Fin.last K) ∈ Finset.Icc (-1) (Q : ℤ) := by
          simpa only [w, List.length_replicate, zero_sub, zero_add] using hl.2.2.1 t ht
        obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hh
        exact abs_le.mpr ⟨by dsimp [W]; omega, by dsimp [W]; omega⟩
      · obtain ⟨r, u, hr, hpos⟩ := hl.2.2.2 t ht
        change |((counterLoopTM B a (some e')).runFrom dc t).workTapePos i.castSucc| ≤ _
        rw [hpos i]
        rcases hr with ⟨hr, hu⟩ | ⟨rfl, rfl⟩
        · rw [horbit r (by omega)] at hu ⊢
          exact (round_spec r hr).2.2.2 u hu i
        · rw [horbit d le_rfl]
          simp only [MultiTapeTM.runFrom_zero, G, b2b_trialCfg]
          simp only [ite_self, abs_zero]
          positivity
    have hp := phaseHostTM_run (b2b_hostPhases MV MI MP)
      ⟨.setup, Sum.inl (.init MP.tm.q₀)⟩ (b2b_hostRedirect MV MI MP) .loop dc c' T he
      CounterLoopState.done rfl ⟨.last, ⟨.anchor, ()⟩⟩ rfl (by
        intro t ht q hq
        cases q with
        | dec q => rfl
        | body q => rfl
        | done => exact False.elim ((hl.2.1 t ht).1 hq)
        | escape => exact False.elim ((hl.2.1 t ht).2 hq))
    obtain ⟨Tlast, hhalt, hout, hheads⟩ := b2b_finish_last MV MI MP x (word d) ct (yes d)
      (cI * (x.length + 1)) cI sv (hI x) (hIs x _) (hclean d)
    let last := c'.mapState (fun _ =>
      (⟨B2bHostPhase.last, ⟨B2bTestPhase.anchor, ()⟩⟩ : Σ j, b2b_hostState MV MI MP j))
    have hfinal : H.runFrom (dc.mapState (Sigma.mk B2bHostPhase.loop)) ((T + 1) + Tlast) =
        H.runFrom last Tlast := by
      rw [MultiTapeTM.runFrom_add, hp.2]
      rfl
    have hiff : (∃ u, u.length = Q ∧ x ++ u ∈ V) ↔ x ++ word d ∈ V := by
      constructor
      · intro hm
        obtain ⟨r, hr, hv⟩ := (b2b_verifies_iff x V Q).mpr hm
        have heq : r = d := by
          by_contra hne
          exact hex ⟨r, by dsimp [d]; omega, hv⟩
        simpa only [heq] using hv
      · intro hm
        exact (b2b_verifies_iff x V Q).mp ⟨d, le_rfl, hm⟩
    refine ⟨(T + 1) + Tlast, ?_, ?_, ?_⟩
    · rw [hfinal]
      exact hhalt
    · rw [hfinal, hout]
      simp only [yes, MultiTapeTM.indicator, Set.mem_setOf_eq, hiff]
    · intro t ht j
      by_cases hpre : t ≤ T
      · rw [hp.1 t hpre]
        exact hb t hpre j
      · have htEq : H.runFrom (dc.mapState (Sigma.mk B2bHostPhase.loop)) t =
            H.runFrom last (t - (T + 1)) := by
          conv_lhs => rw [show t = (T + 1) + (t - (T + 1)) by omega,
            MultiTapeTM.runFrom_add, hp.2]
          rfl
        rw [htEq]
        simpa only [word, Meyer.length_enumWord, W] using hheads (t - (T + 1)) (by omega) j

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

Status: proved. Setup is `b2b_setup_run`; the search, with its counted loop over
`b2b_round_run` and its global trajectory bound, is `b2b_search_contract`. -/
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
  classical
  let Q := C * (x.length + 1) ^ c
  let W := x.length + Q + cV * ((x.length + Q) ^ e + 1) + cI + cP * (x.length + 1) + 1
  let H := (b2b_host MV MI MP).tm
  obtain ⟨T, hsetup, hsetupHeads⟩ := b2b_setup_run MV MI MP x Q
    (cP * (x.length + 1) ^ (c + 1)) (cP * (x.length + 1)) (hP x) (hPs x _)
  obtain ⟨t, hhalt, hout, hsearchHeads⟩ := b2b_search_contract Q e cV cI V MV MI MP hV hI hIs x
  have hheads (u : ℕ) (hu : u ≤ T + t) (j : Fin (b2b_host MV MI MP).k) :
      |(H.runFrom (H.initCfg x) u).workTapePos j| ≤ (W : ℤ) := by
    by_cases hpre : u ≤ T
    · exact (hsetupHeads u hpre j).trans (by
        exact_mod_cast (show cP * (x.length + 1) + Q + 1 ≤ W by dsimp [W]; omega))
    · have heq : u = T + (u - T) := by omega
      rw [heq, MultiTapeTM.runFrom_add, hsetup]
      exact (hsearchHeads (u - T) (by omega) j).trans (by
        exact_mod_cast (show x.length + Q + cV * ((x.length + Q) ^ e + 1) + cI + 1 ≤ W by
          dsimp [W]; omega))
  refine ⟨T + t, (FinTM.computesInTime_iff _ _ _ _).mpr ⟨?_, ?_⟩, ?_⟩
  · rw [MultiTapeTM.runFrom_add, hsetup]
    exact hhalt
  · rw [MultiTapeTM.runFrom_add, hsetup]
    simpa only [MultiTapeTM.indicator, Set.mem_setOf_eq, Q] using hout
  · change H.spaceUsed (H.initCfg x) (T + t) ≤ (b2b_host MV MI MP).k * (2 * W + 1)
    calc
      _ ≤ ∑ _j : Fin (b2b_host MV MI MP).k, (Finset.Icc (-(W : ℤ)) (W : ℤ)).card := by
        apply Finset.sum_le_sum
        intro j _
        apply Finset.card_le_card
        intro z hz
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
        have hu' : u ≤ T + t := by have := Finset.mem_range.mp hu; omega
        exact Finset.mem_Icc.mpr (abs_le.mp (hheads u hu' j))
      _ = (b2b_host MV MI MP).k * (2 * W + 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Int.card_Icc]
        congr 1
        omega

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
