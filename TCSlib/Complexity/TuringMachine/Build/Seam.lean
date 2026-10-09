/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.Convention
import TCSlib.Complexity.TuringMachine.StateRenaming

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: seam composition (R2)

The configuration-level sequencing layer of the machine-construction
library (`machine-library-design.md` §12, R2): sequential composition of
two controllers at the canonical `Turing.Cfg.ofWords` seam of
`TCSlib.Complexity.TuringMachine.Build.Convention`. If `M₁` carries seam
`c₀` to seam `c₁` within `T₁` under a first-return cut, and `M₂` carries
`c₁` to `c₂` within `T₂`, the dispatch-glued composite carries `c₀` to
`c₂` within `T₁ + 1 + T₂` — the explicit constant is `1`, one silent
stationary dispatch step at the seam. This is the generic form of the
per-batch dispatch gluing re-proved in every A-chain and emitter batch,
and it exists at the configuration level precisely because the emitter
round-1 finding stands: *function-level* contracts cannot deliver
clean-return seams, so composing `ComputesFunInTime` contracts can never
replace this combinator.

**Status: statement skeleton (§12 statement phase).** The composite is a
real definition (state-sum dispatch in `Turing.bufferedCompTM`'s style,
kept minimal); every contract is sorried, each with a proof sketch naming
its fill obligations.

## Design

* The glue is a **state sum** `S₁ ⊕ S₂`: left states run `M₁`'s table,
  right states run `M₂`'s, and the designated left anchor `exit` takes one
  stationary, silent, write-free transition to the right anchor `entry`.
  Dispatch-on-anchor (rather than dispatch-on-halt) matches the ABI: seam
  contracts end at a **live** anchor (`Build/Loop.lean`'s `hstart`/
  `hround` shape), and the catalog routines of
  `TCSlib.Complexity.TuringMachine.Build.Catalog` exit at live anchors.
* The space clause is stated in the **sharp per-tape form** (frozen
  decision 12.1): the headline is per-tape containment of visited sets —
  the composite's visited set on every work tape is contained in the
  union of the phases' — which implies both the per-tape sum bound and
  the max bound for disjointly-owned tapes, stated as corollaries.

## Main definitions

* `Turing.seamCompTM` — the dispatch-glued composite of two machines at
  `Turing.Cfg.ofWords` seams.

## Main results

All sorried (statement phase):

* `Turing.seamCompTM_run` — seam-to-seam composition within
  `T₁ + 1 + T₂`.
* `Turing.seamCompTM_firstReturn` — the composite inherits a first-return
  cut at the final anchor, so composites **whose phases satisfy the stated
  cuts** chain (round-1 finding R3: the cut excludes positive
  entry-equals-exit calls — those route through the release adapter below).
* `Turing.seamCompTM_run_ofCfg`, `Turing.seamCompTM_firstReturn_ofCfg`,
  `Turing.seamCompTM_visitedByTapeHead_ofCfg` — the **general-configuration**
  composition (round-1 repair R2): phase two starts from phase one's
  returned configuration with only the control state replaced, so arbitrary
  frames, displaced inactive heads, and accumulated output cross the
  dispatch intact; the canonical `Cfg.ofWords` theorems are its instances.
* `Turing.seamReleaseTM`, `Turing.seamReleaseTM_firstReturn`,
  `Turing.seamReleaseTM_visitedByTapeHead` — the **fresh-entry/release
  adapter** (round-1 repair R3): the entry action executes unconditionally
  from a fresh start state, so a positive call that returns to its own
  anchor becomes seam-consumable.
* `Turing.seamCompTM_visitedByTapeHead` — per-tape visited-set
  containment (the headline space clause, decision 12.1).
* `Turing.seamCompTM_spaceUsedByTape_le_add`,
  `Turing.seamCompTM_spaceUsed_le_add`,
  `Turing.seamCompTM_spaceUsedByTape_le_max` — the sum and
  max-for-disjointly-owned-tapes corollaries.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2; phase-sequenced simulations
  are the folklore engine of §1.4–§1.7.)
* [Balbach22] F. Balbach, *The Cook–Levin theorem*, Isabelle AFP entry
  `Cook_Levin`, 2022. (The composition-combinator architecture precedent,
  as in `TCSlib.Complexity.TuringMachine.Composition`.)
* [Bon26] É. Bonnet, *classical-complexity*, Lax Archive entry lax-434930,
  module `proofs/Lax434930Proofs/InclusionAux/TimeCompiler/`, commit
  `0c0840319318215fd7b36a9a822b81ce55cf6941`, Apache-2.0, examined
  2026-10-05. Design adaptation with nothing transcribed (different
  toolchain and machine model): the seam-composition shape is
  `StackRename`'s `executes_in_sum`.
-/

namespace Turing

variable {k : ℕ} {S₁ S₂ : Type*} {x : List Bool}

/-- **R2, the seam composite** (design §12; [Bon26], `executes_in_sum`).
The dispatch-glued sequential composite of `M₁` and `M₂` at
`Turing.Cfg.ofWords` seams: states are the sum `S₁ ⊕ S₂`, left states run
`M₁`'s transition table and right states `M₂`'s (each halting where its
phase halts), except that the designated left anchor `exit` takes one
stationary, silent, write-free dispatch step to the right anchor `entry`.
The composite starts at `M₁`'s initial state; a run launched at a left
seam anchor is the intended use. -/
def seamCompTM [DecidableEq S₁] (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂) :
    MultiTapeTM k Bool (S₁ ⊕ S₂) where
  q₀ := Sum.inl M₁.q₀
  tr := fun q inp w =>
    match q with
    | Sum.inl s =>
      if s = exit then ⟨0, fun _ => (none, 0), none, some (Sum.inr entry)⟩
      else
        let a := M₁.tr s inp w
        ⟨a.inputTape, a.workTapes, a.output, a.state.map Sum.inl⟩
    | Sum.inr s =>
      let a := M₂.tr s inp w
      ⟨a.inputTape, a.workTapes, a.output, a.state.map Sum.inr⟩

/-- Away from the exit, one left step is exactly the state-mapped source step,
including the absorbing halted case. -/
private lemma seamComp_step_left [DecidableEq S₁]
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    (c : Cfg k Bool S₁ x) (hc : c.state ≠ some exit) :
    (seamCompTM M₁ exit M₂ entry).step (c.mapState Sum.inl) =
      (M₁.step c).mapState Sum.inl := by
  cases hs : c.state with
  | none => simp [MultiTapeTM.step, Cfg.mapState, hs]
  | some q =>
    have hq : q ≠ exit := fun h => hc (hs.trans (congrArg some h))
    simp only [MultiTapeTM.step, Cfg.mapState, hs, Option.map_some]
    dsimp only [seamCompTM]
    rw [if_neg hq]
    rfl

/-- Right steps commute with state mapping, even after a source halt. -/
private lemma seamComp_step_right [DecidableEq S₁]
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂) (c : Cfg k Bool S₂ x) :
    (seamCompTM M₁ exit M₂ entry).step (c.mapState Sum.inr) =
      (M₂.step c).mapState Sum.inr := by
  cases hs : c.state with
  | none => simp [MultiTapeTM.step, Cfg.mapState, hs]
  | some q =>
    simp only [MultiTapeTM.step, Cfg.mapState, hs, Option.map_some]
    rfl

/-- A stationary, silent, write-free action changes only the control field. -/
private lemma seam_stationary_apply (c : Cfg k Bool S₁ x) (q : S₁) :
    (Action.mk 0 (fun _ => (none, 0)) none (some q)).apply c =
      { c with state := some q } := by
  simp [Action.apply]

/-- Dispatch preserves all data of an arbitrary live exit configuration. -/
private lemma seamComp_dispatch [DecidableEq S₁]
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    (c : Cfg k Bool S₁ x) (hc : c.state = some exit) :
    (seamCompTM M₁ exit M₂ entry).step (c.mapState Sum.inl) =
      (c.mapState fun _ => entry).mapState Sum.inr := by
  unfold MultiTapeTM.step
  simp only [Cfg.mapState, hc, Option.map_some]
  dsimp only [seamCompTM]
  rw [if_pos rfl, seam_stationary_apply]

/-- The whole left trajectory agrees through the exit time.
**Proof sketch.** Induct on the time; the cut licenses the left-step
identity at every predecessor strictly before the endpoint. -/
private lemma seamComp_left [DecidableEq S₁]
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    {c : Cfg k Bool S₁ x} {T : ℕ}
    (hcut : ∀ t < T, (M₁.runFrom c t).state ≠ some exit)
    (t : ℕ) (ht : t ≤ T) :
    (seamCompTM M₁ exit M₂ entry).runFrom (c.mapState Sum.inl) t =
      (M₁.runFrom c t).mapState Sum.inl := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
      seamComp_step_left M₁ exit M₂ entry _ (hcut t (by omega)),
      MultiTapeTM.runFrom_succ_eq_step']

/-- After the one-step dispatch, the entire right trajectory agrees.
**Proof sketch.** Split the run at the dispatch, use left lockstep and
the exit equation, then iterate the unconditional right-step identity. -/
private lemma seamComp_right [DecidableEq S₁]
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    {c₀ c₁ : Cfg k Bool S₁ x} {T₁ : ℕ}
    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit) (t : ℕ) :
    (seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl)
        (T₁ + 1 + t) =
      (M₂.runFrom (c₁.mapState fun _ => entry) t).mapState Sum.inr := by
  rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_succ_eq_step',
    seamComp_left M₁ exit M₂ entry hcut T₁ le_rfl, h₁,
    seamComp_dispatch M₁ exit M₂ entry c₁ hexit]
  exact MultiTapeTM.runFrom_comm_of_step (Cfg.mapState Sum.inr)
    (seamComp_step_right M₁ exit M₂ entry) _ t

/-- General endpoint composition, shared by the frozen public forms. -/
private lemma seamComp_run_general [DecidableEq S₁]
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    {c₀ c₁ : Cfg k Bool S₁ x} {c₃ : Cfg k Bool S₂ x} {T₁ T₂ : ℕ}
    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit)
    (h₂ : M₂.runFrom (c₁.mapState fun _ => entry) T₂ = c₃) :
    (seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl)
        (T₁ + 1 + T₂) = c₃.mapState Sum.inr :=
  (seamComp_right M₁ exit M₂ entry h₁ hexit hcut T₂).trans
    (congrArg (Cfg.mapState Sum.inr) h₂)

/-- The right final anchor is absent before the total time.
**Proof sketch.** Through the left endpoint, constructor disjointness
excludes the anchor. Afterwards, right lockstep transports the phase-two
cut at the time remaining after dispatch. -/
private lemma seamComp_firstReturn_general [DecidableEq S₁]
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (entry q₂ : S₂)
    {c₀ c₁ : Cfg k Bool S₁ x} {T₁ T₂ : ℕ}
    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit)
    (hcut₂ : ∀ t < T₂,
      (M₂.runFrom (c₁.mapState fun _ => entry) t).state ≠ some q₂) :
    ∀ t < T₁ + 1 + T₂,
      ((seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl) t).state ≠
        some (Sum.inr q₂) := by
  intro t ht
  by_cases hleft : t ≤ T₁
  · rw [seamComp_left M₁ exit M₂ entry hcut t hleft]
    cases (M₁.runFrom c₀ t).state <;> simp [Cfg.mapState]
  · have htime : t = T₁ + 1 + (t - (T₁ + 1)) := by omega
    rw [htime, seamComp_right M₁ exit M₂ entry h₁ hexit hcut]
    intro heq
    apply hcut₂ (t - (T₁ + 1)) (by omega)
    change Option.map Sum.inr
      (M₂.runFrom (c₁.mapState fun _ => entry) (t - (T₁ + 1))).state =
        some (Sum.inr q₂) at heq
    obtain ⟨q, hq, heq⟩ := Option.map_eq_some_iff.mp heq
    exact hq.trans (congrArg some (Sum.inr.inj heq))

/-- Every visited position belongs to one of the two exact run segments.
**Proof sketch.** A time at most the left duration uses left lockstep.
Every later time is dispatch time plus a unique nonnegative offset, at
most the right duration; right lockstep supplies its image witness. -/
private lemma seamComp_visited_general [DecidableEq S₁]
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    {c₀ c₁ : Cfg k Bool S₁ x} {T₁ T₂ : ℕ}
    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit) (i : Fin k) :
    (seamCompTM M₁ exit M₂ entry).visitedByTapeHead (c₀.mapState Sum.inl)
        (T₁ + 1 + T₂) i ⊆
      M₁.visitedByTapeHead c₀ T₁ i ∪
        M₂.visitedByTapeHead (c₁.mapState fun _ => entry) T₂ i := by
  intro z hz
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
  have ht' := Finset.mem_range.mp ht
  by_cases hleft : t ≤ T₁
  · rw [seamComp_left M₁ exit M₂ entry hcut t hleft]
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr (by omega), rfl⟩
  · have htime : t = T₁ + 1 + (t - (T₁ + 1)) := by omega
    rw [htime, seamComp_right M₁ exit M₂ entry h₁ hexit hcut]
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr
      ⟨t - (T₁ + 1), Finset.mem_range.mpr (by omega), rfl⟩

/-- State mapping of a canonical seam changes only its anchor. -/
private lemma seam_ofWords_mapState {S₃ : Type*} (f : S₁ → S₃)
    (q : S₁) (w : Fin k → List Bool) :
    (Cfg.ofWords (input := x) q w).mapState f = Cfg.ofWords (f q) w := rfl

/-- **R2, seam-to-seam composition** (spec, fill pending — design §12;
[Bon26], `executes_in_sum`). If `M₁` carries the seam
`Cfg.ofWords start w₀` to the seam `Cfg.ofWords exit w₁` in exactly `T₁`
steps without visiting the anchor `exit` earlier (the first-return cut),
and `M₂` carries `Cfg.ofWords entry w₁` to `Cfg.ofWords q₂ w₂` in exactly
`T₂` steps, then the composite carries the left-mapped first seam to the
right-mapped last seam in exactly `T₁ + 1 + T₂` steps — the explicit
dispatch constant is `1`, not `O(1)`.

**Proof sketch.** Three segments composed with
`Turing.MultiTapeTM.runFrom_add`. (i) *Phase one lockstep*: on left
states other than the anchor, one composite step is the `Sum.inl`-mapped
`M₁` step; the cut guarantees the anchor is not visited before `T₁`, so
induction carries the left-mapped configuration to time `T₁`, where it is
`Cfg.ofWords (Sum.inl exit) w₁`. (ii) *Dispatch*: at the anchor the
composite takes the stationary silent step, and a stationary write-free
action fixes every tape, head, and the output of a seam configuration, so
time `T₁ + 1` is exactly `Cfg.ofWords (Sum.inr entry) w₁`. (iii) *Phase
two lockstep*: on right states one composite step is the
`Sum.inr`-mapped `M₂` step (`Turing.MultiTapeTM.runFrom_comm_of_step`),
carrying the seam to the right-mapped `Cfg.ofWords q₂ w₂` at time
`T₁ + 1 + T₂`. The degenerate case `T₁ = 0` (so `start = exit`,
`w₀ = w₁`) is covered because the dispatch step alone performs the
phase-one handover. -/
theorem seamCompTM_run [DecidableEq S₁] (M₁ : MultiTapeTM k Bool S₁)
    (exit : S₁) (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    (start : S₁) (q₂ : S₂) (w₀ w₁ w₂ : Fin k → List Bool) (T₁ T₂ : ℕ)
    (h₁ : M₁.runFrom (Cfg.ofWords (input := x) start w₀) T₁ =
      Cfg.ofWords exit w₁)
    (hcut : ∀ t < T₁,
      (M₁.runFrom (Cfg.ofWords (input := x) start w₀) t).state ≠ some exit)
    (h₂ : M₂.runFrom (Cfg.ofWords (input := x) entry w₁) T₂ =
      Cfg.ofWords q₂ w₂) :
    (seamCompTM M₁ exit M₂ entry).runFrom
        (Cfg.ofWords (input := x) (Sum.inl start) w₀) (T₁ + 1 + T₂) =
      Cfg.ofWords (Sum.inr q₂) w₂ := by
  have h₂' : M₂.runFrom
      ((Cfg.ofWords (input := x) exit w₁).mapState fun _ => entry) T₂ =
        Cfg.ofWords q₂ w₂ := by
    simpa only [seam_ofWords_mapState] using h₂
  simpa only [seam_ofWords_mapState] using
    seamComp_run_general M₁ exit M₂ entry h₁ rfl hcut h₂'

/-- **R2, the inherited first-return cut** (spec, fill pending — design
§12). Under the hypotheses of `seamCompTM_run`, if additionally `M₂` does
not visit its final anchor `q₂` strictly before `T₂`, then the composite
does not visit `Sum.inr q₂` strictly before `T₁ + 1 + T₂` — so a
composite is itself a seam-to-seam routine and chains under further
`seamCompTM` applications.

**Proof sketch.** Split the window. Before and at `T₁` the composite's
state is a left state (phase-one lockstep of `seamCompTM_run`), never
`Sum.inr q₂` by constructor disjointness. From `T₁ + 1` on, the
composite's state is the `Sum.inr` image of `M₂`'s state at the shifted
time (phase-two lockstep), and `Sum.inr` injectivity turns the `M₂` cut
into the composite cut; a mid-phase `M₂` halt is excluded because halting
absorbs and would contradict `h₂`'s live anchor at `T₂`. -/
theorem seamCompTM_firstReturn [DecidableEq S₁] (M₁ : MultiTapeTM k Bool S₁)
    (exit : S₁) (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    (start : S₁) (q₂ : S₂) (w₀ w₁ w₂ : Fin k → List Bool) (T₁ T₂ : ℕ)
    (h₁ : M₁.runFrom (Cfg.ofWords (input := x) start w₀) T₁ =
      Cfg.ofWords exit w₁)
    (hcut : ∀ t < T₁,
      (M₁.runFrom (Cfg.ofWords (input := x) start w₀) t).state ≠ some exit)
    (h₂ : M₂.runFrom (Cfg.ofWords (input := x) entry w₁) T₂ =
      Cfg.ofWords q₂ w₂)
    (hcut₂ : ∀ t < T₂,
      (M₂.runFrom (Cfg.ofWords (input := x) entry w₁) t).state ≠ some q₂) :
    ∀ t < T₁ + 1 + T₂,
      ((seamCompTM M₁ exit M₂ entry).runFrom
          (Cfg.ofWords (input := x) (Sum.inl start) w₀) t).state ≠
        some (Sum.inr q₂) := by
  have hcut₂' : ∀ t < T₂,
      (M₂.runFrom ((Cfg.ofWords (input := x) exit w₁).mapState fun _ => entry)
        t).state ≠ some q₂ := by
    simpa only [seam_ofWords_mapState] using hcut₂
  simpa only [seam_ofWords_mapState] using
    seamComp_firstReturn_general M₁ exit M₂ entry q₂ h₁ rfl hcut hcut₂'

/-- **R2 space, the per-tape headline** (spec, fill pending — design §12,
frozen decision 12.1: the sharp per-tape form). On every work tape `i`,
the composite's visited set over the whole composed run is contained in
the union of the two phases' visited sets. This is the statement the sum
and max corollaries below both project from; it is deliberately the
containment itself, since downstream applications may depend on the
sharpness.

**Proof sketch.** Decompose the trajectory by the two lockstep segments
of `seamCompTM_run`: times `0, …, T₁` reproduce `M₁`'s head positions
(phase-one lockstep), time `T₁ + 1` is the dispatch step, which is
stationary — the head sits at the seam origin, already visited by both
phases' initial configurations — and times `T₁ + 1, …, T₁ + 1 + T₂`
reproduce `M₂`'s positions shifted by `T₁ + 1` (phase-two lockstep).
Every trajectory point therefore lies in one of the two phases' images;
conclude by `Finset.image` monotonicity over the split of
`Finset.range`. -/
theorem seamCompTM_visitedByTapeHead [DecidableEq S₁]
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    (start : S₁) (q₂ : S₂) (w₀ w₁ w₂ : Fin k → List Bool) (T₁ T₂ : ℕ)
    (h₁ : M₁.runFrom (Cfg.ofWords (input := x) start w₀) T₁ =
      Cfg.ofWords exit w₁)
    (hcut : ∀ t < T₁,
      (M₁.runFrom (Cfg.ofWords (input := x) start w₀) t).state ≠ some exit)
    (h₂ : M₂.runFrom (Cfg.ofWords (input := x) entry w₁) T₂ =
      Cfg.ofWords q₂ w₂) (i : Fin k) :
    (seamCompTM M₁ exit M₂ entry).visitedByTapeHead
        (Cfg.ofWords (input := x) (Sum.inl start) w₀) (T₁ + 1 + T₂) i ⊆
      M₁.visitedByTapeHead (Cfg.ofWords (input := x) start w₀) T₁ i ∪
        M₂.visitedByTapeHead (Cfg.ofWords (input := x) entry w₁) T₂ i := by
  simpa only [seam_ofWords_mapState] using
    seamComp_visited_general (T₂ := T₂) M₁ exit M₂ entry h₁ rfl hcut i

/-- **R2 space, the per-tape sum corollary** (spec, fill pending — design
§12, decision 12.1). On every work tape, the composite's space usage is
at most the sum of the phases' space usages on that tape.

**Proof sketch.** `Finset.card_le_card` on
`seamCompTM_visitedByTapeHead`, then `Finset.card_union_le`. -/
theorem seamCompTM_spaceUsedByTape_le_add [DecidableEq S₁]
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    (start : S₁) (q₂ : S₂) (w₀ w₁ w₂ : Fin k → List Bool) (T₁ T₂ : ℕ)
    (h₁ : M₁.runFrom (Cfg.ofWords (input := x) start w₀) T₁ =
      Cfg.ofWords exit w₁)
    (hcut : ∀ t < T₁,
      (M₁.runFrom (Cfg.ofWords (input := x) start w₀) t).state ≠ some exit)
    (h₂ : M₂.runFrom (Cfg.ofWords (input := x) entry w₁) T₂ =
      Cfg.ofWords q₂ w₂) (i : Fin k) :
    (seamCompTM M₁ exit M₂ entry).spaceUsedByTape
        (Cfg.ofWords (input := x) (Sum.inl start) w₀) (T₁ + 1 + T₂) i ≤
      M₁.spaceUsedByTape (Cfg.ofWords (input := x) start w₀) T₁ i +
        M₂.spaceUsedByTape (Cfg.ofWords (input := x) entry w₁) T₂ i := by
  exact (Finset.card_le_card
    (seamCompTM_visitedByTapeHead M₁ exit M₂ entry start q₂ w₀ w₁ w₂
      T₁ T₂ h₁ hcut h₂ i)).trans (Finset.card_union_le _ _)

/-- **R2 space, the total sum corollary** (spec, fill pending — design
§12). The composite's total space usage is at most the sum of the
phases' total space usages.

**Proof sketch.** Sum `seamCompTM_spaceUsedByTape_le_add` over all tapes
(`Finset.sum_le_sum`), then distribute the sum over the addition. -/
theorem seamCompTM_spaceUsed_le_add [DecidableEq S₁]
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    (start : S₁) (q₂ : S₂) (w₀ w₁ w₂ : Fin k → List Bool) (T₁ T₂ : ℕ)
    (h₁ : M₁.runFrom (Cfg.ofWords (input := x) start w₀) T₁ =
      Cfg.ofWords exit w₁)
    (hcut : ∀ t < T₁,
      (M₁.runFrom (Cfg.ofWords (input := x) start w₀) t).state ≠ some exit)
    (h₂ : M₂.runFrom (Cfg.ofWords (input := x) entry w₁) T₂ =
      Cfg.ofWords q₂ w₂) :
    (seamCompTM M₁ exit M₂ entry).spaceUsed
        (Cfg.ofWords (input := x) (Sum.inl start) w₀) (T₁ + 1 + T₂) ≤
      M₁.spaceUsed (Cfg.ofWords (input := x) start w₀) T₁ +
        M₂.spaceUsed (Cfg.ofWords (input := x) entry w₁) T₂ := by
  unfold MultiTapeTM.spaceUsed
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ =>
    seamCompTM_spaceUsedByTape_le_add M₁ exit M₂ entry start q₂ w₀ w₁ w₂
      T₁ T₂ h₁ hcut h₂ i

/-- **R2 space, the max corollary for disjointly-owned tapes** (spec, fill
pending — design §12, frozen decision 12.1: the sharpest available form).
If one of the two phases is *idle* on tape `i` — its visited set is the
seam-origin singleton `{0}` — then the composite's space usage on `i` is
bounded by the **max** of the phases' usages, not their sum. Under a
tape-ownership discipline (each work tape owned by one phase, the other
phase never moving its head there) this gives per-tape space equal to the
owner's, which is what the chapter-4 consumers depend on.

**Proof sketch.** From `seamCompTM_visitedByTapeHead` the composite's
visited set is contained in the union, and the idle side's singleton
`{0}` is already contained in the other side's visited set — a seam
configuration has every head at the origin, so `0` is in every phase's
visited set at every horizon. The union collapses to the non-idle side's
set; `Finset.card_le_card` and `le_max_left/right` finish. -/
theorem seamCompTM_spaceUsedByTape_le_max [DecidableEq S₁]
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    (start : S₁) (q₂ : S₂) (w₀ w₁ w₂ : Fin k → List Bool) (T₁ T₂ : ℕ)
    (h₁ : M₁.runFrom (Cfg.ofWords (input := x) start w₀) T₁ =
      Cfg.ofWords exit w₁)
    (hcut : ∀ t < T₁,
      (M₁.runFrom (Cfg.ofWords (input := x) start w₀) t).state ≠ some exit)
    (h₂ : M₂.runFrom (Cfg.ofWords (input := x) entry w₁) T₂ =
      Cfg.ofWords q₂ w₂) (i : Fin k)
    (hown : M₁.visitedByTapeHead (Cfg.ofWords (input := x) start w₀) T₁ i
        = {0} ∨
      M₂.visitedByTapeHead (Cfg.ofWords (input := x) entry w₁) T₂ i = {0}) :
    (seamCompTM M₁ exit M₂ entry).spaceUsedByTape
        (Cfg.ofWords (input := x) (Sum.inl start) w₀) (T₁ + 1 + T₂) i ≤
      max (M₁.spaceUsedByTape (Cfg.ofWords (input := x) start w₀) T₁ i)
        (M₂.spaceUsedByTape (Cfg.ofWords (input := x) entry w₁) T₂ i) := by
  have hzero₁ : (0 : ℤ) ∈
      M₁.visitedByTapeHead (Cfg.ofWords (input := x) start w₀) T₁ i :=
    Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ T₁), rfl⟩
  have hzero₂ : (0 : ℤ) ∈
      M₂.visitedByTapeHead (Cfg.ofWords (input := x) entry w₁) T₂ i :=
    Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ T₂), rfl⟩
  have hsub := seamCompTM_visitedByTapeHead M₁ exit M₂ entry start q₂
    w₀ w₁ w₂ T₁ T₂ h₁ hcut h₂ i
  rcases hown with hown | hown
  · rw [hown, Finset.union_eq_right.mpr
      (Finset.singleton_subset_iff.mpr hzero₂)] at hsub
    exact (Finset.card_le_card hsub).trans (le_max_right _ _)
  · rw [hown, Finset.union_eq_left.mpr
      (Finset.singleton_subset_iff.mpr hzero₁)] at hsub
    exact (Finset.card_le_card hsub).trans (le_max_left _ _)

/-- **R2′, general-configuration seam-to-seam composition** (spec, fill
pending — round-1 repair R2): the `Cfg.ofWords` restriction of
`Turing.seamCompTM_run` is lifted. If `M₁` carries an arbitrary
configuration `c₀` to `c₁` in exactly `T₁` steps, first reaching the anchor
`exit` there, and `M₂` carries `c₁` **with only the control state replaced
by `entry`** to `c₃` in `T₂` steps, then the composite carries the
`Sum.inl`-mapped `c₀` to the `Sum.inr`-mapped `c₃` in exactly
`T₁ + 1 + T₂` steps: the dispatch step is stationary, silent, and
write-free, so displaced inactive heads, noncanonical tape contents, the
input position, and **accumulated output** all cross it intact — exactly
the seams the round-1 audit exhibited (`emitterP2_relocate_run`'s arbitrary
frames, `exists_emitCallTM`'s nonempty output) that no `Cfg.ofWords`
endpoint can describe. The canonical `seamCompTM_run` is the
`Cfg.ofWords` instance.

**Proof sketch.** Identical three-segment decomposition to
`seamCompTM_run` — phase-one `Sum.inl` lockstep under the cut, one
dispatch step, phase-two `Sum.inr` lockstep via `Cfg.mapState_apply` —
with the single new observation that a stationary write-free action fixes
**every** field of an arbitrary configuration, not only a canonical one
(`Turing.Action.apply` componentwise). Fill obligations, named: the two
lockstep inductions over `Cfg.mapState`, the dispatch-step field check,
and the `ofWords` specialization recovering the canonical theorem. -/
theorem seamCompTM_run_ofCfg [DecidableEq S₁] (M₁ : MultiTapeTM k Bool S₁)
    (exit : S₁) (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    {c₀ c₁ : Cfg k Bool S₁ x} {c₃ : Cfg k Bool S₂ x} {T₁ T₂ : ℕ}
    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit)
    (h₂ : M₂.runFrom (c₁.mapState fun _ => entry) T₂ = c₃) :
    (seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl)
        (T₁ + 1 + T₂) =
      c₃.mapState Sum.inr := by
  exact seamComp_run_general M₁ exit M₂ entry h₁ hexit hcut h₂

/-- **R2′, the general inherited first-return cut** (spec, fill pending —
round-1 repair R2): under the hypotheses of
`Turing.seamCompTM_run_ofCfg`, if `M₂` first reaches `q₂` at `T₂`, the
composite first reaches `Sum.inr q₂` at `T₁ + 1 + T₂`.

**Proof sketch.** As `seamCompTM_firstReturn`, over the general lockstep
segments: left times produce `Sum.inl` states, right times the
`Sum.inr`-mapped `M₂` states at shifted time, and injectivity of the
constructors transports the cuts. -/
theorem seamCompTM_firstReturn_ofCfg [DecidableEq S₁]
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂) (q₂ : S₂)
    {c₀ c₁ : Cfg k Bool S₁ x} {c₃ : Cfg k Bool S₂ x} {T₁ T₂ : ℕ}
    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit)
    (h₂ : M₂.runFrom (c₁.mapState fun _ => entry) T₂ = c₃)
    (hq : c₃.state = some q₂)
    (hcut₂ : ∀ t < T₂,
      (M₂.runFrom (c₁.mapState fun _ => entry) t).state ≠ some q₂) :
    ∀ t < T₁ + 1 + T₂,
      ((seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl) t).state ≠
        some (Sum.inr q₂) := by
  exact seamComp_firstReturn_general M₁ exit M₂ entry q₂ h₁ hexit hcut hcut₂

/-- **R2′ space, the general per-tape headline** (spec, fill pending —
round-1 repair R2): under the hypotheses of `Turing.seamCompTM_run_ofCfg`,
on every work tape the composite's visited set over the composed run is
contained in the union of the two phases' visited sets — the
general-configuration form of `Turing.seamCompTM_visitedByTapeHead`, from
which the canonical corollaries project.

**Proof sketch.** As the canonical headline: the two lockstep segments
reproduce the phases' trajectories, and the dispatch step is stationary at
a point both phases' endpoint/start configurations already visit. -/
theorem seamCompTM_visitedByTapeHead_ofCfg [DecidableEq S₁]
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    {c₀ c₁ : Cfg k Bool S₁ x} {T₁ T₂ : ℕ}
    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit) (i : Fin k) :
    (seamCompTM M₁ exit M₂ entry).visitedByTapeHead (c₀.mapState Sum.inl)
        (T₁ + 1 + T₂) i ⊆
      M₁.visitedByTapeHead c₀ T₁ i ∪
        M₂.visitedByTapeHead (c₁.mapState fun _ => entry) T₂ i := by
  exact seamComp_visited_general M₁ exit M₂ entry h₁ hexit hcut i

variable {S : Type*}

/-- **R3′, the fresh-entry/release adapter** (round-1 repair R3). The seam
combinator dispatches at its exit anchor **before** that state's action, so
a positive call that starts and ends at one anchor cannot be cut
(`seamCompTM_firstReturn`'s cut is contradictory at zero — the round-1
finding, witnessed by `exists_installCallTM`/`exists_emitCallTM`'s
strictly-positive interior promises and `emitterP2_call_segment`'s
execute-first discipline). The adapter runs `M` on states `Unit ⊕ S` with a
fresh start `Sum.inl ()` that executes the anchor's action
**unconditionally**, after which control lives in the `Sum.inr` copy — so
the *first re-arrival* at `Sum.inr anchor` is a genuine positive-time
event a seam can consume as its left exit. -/
def seamReleaseTM (M : MultiTapeTM k Bool S) (anchor : S) :
    MultiTapeTM k Bool (Unit ⊕ S) where
  q₀ := Sum.inl ()
  tr := fun q inp w =>
    match q with
    | Sum.inl _ =>
      let a := M.tr anchor inp w
      ⟨a.inputTape, a.workTapes, a.output, a.state.map Sum.inr⟩
    | Sum.inr s =>
      let a := M.tr s inp w
      ⟨a.inputTape, a.workTapes, a.output, a.state.map Sum.inr⟩

/-- The fresh state executes the anchor action without a dispatch step. -/
private lemma seamRelease_fresh_step (M : MultiTapeTM k Bool S) (anchor : S)
    (c : Cfg k Bool S x) (hc : c.state = some anchor) :
    (seamReleaseTM M anchor).step (c.mapState fun _ => Sum.inl ()) =
      (M.step c).mapState Sum.inr := by
  simp only [MultiTapeTM.step, Cfg.mapState, hc, Option.map_some]
  rfl

/-- In the right copy, release steps commute with state mapping. -/
private lemma seamRelease_step_right (M : MultiTapeTM k Bool S) (anchor : S)
    (c : Cfg k Bool S x) :
    (seamReleaseTM M anchor).step (c.mapState Sum.inr) =
      (M.step c).mapState Sum.inr := by
  cases hs : c.state with
  | none => simp [MultiTapeTM.step, Cfg.mapState, hs]
  | some q =>
    simp only [MultiTapeTM.step, Cfg.mapState, hs, Option.map_some]
    rfl

/-- At every positive time, release runs are the right-mapped source runs.
**Proof sketch.** Execute the fresh step once, then iterate the right-step
identity. This also covers a source that halts or never returns. -/
private lemma seamRelease_run_pos (M : MultiTapeTM k Bool S) (anchor : S)
    (c : Cfg k Bool S x) (hc : c.state = some anchor) (t : ℕ) (ht : 0 < t) :
    (seamReleaseTM M anchor).runFrom (c.mapState fun _ => Sum.inl ()) t =
      (M.runFrom c t).mapState Sum.inr := by
  cases t with
  | zero => omega
  | succ t =>
    rw [MultiTapeTM.runFrom_succ_eq_step, seamRelease_fresh_step M anchor c hc,
      MultiTapeTM.runFrom_succ_eq_step]
    exact MultiTapeTM.runFrom_comm_of_step (Cfg.mapState Sum.inr)
      (seamRelease_step_right M anchor) _ t

/-- **R3′, the positive first return through the adapter** (spec, fill
pending — round-1 repair R3): if `M`, started at its anchor, first
re-visits the anchor at a strictly positive time `T`, then the adapter,
started at its fresh state over the same configuration, reaches
`Sum.inr anchor` first at exactly `T`, over the `Sum.inr`-transported run.
The audit's S7 check is the smallest case: a two-step write-then-return
call executes both source actions before any seam dispatch can fire.

**Proof sketch.** The fresh step applies the anchor's action verbatim
(`Cfg.mapState_apply` at the constant relabeling), after which every step
is `Sum.inr`-lockstep with `M`'s run; the first-visit clause is the
transported cut, with time zero excluded by the fresh constructor
(`Sum.inl ≠ Sum.inr`). Fill obligations, named: the fresh-step equation,
the lockstep induction, and the cut transport. -/
theorem seamReleaseTM_firstReturn (M : MultiTapeTM k Bool S) (anchor : S)
    {c c' : Cfg k Bool S x} {T : ℕ}
    (hc : c.state = some anchor) (hT : 0 < T) (h : M.runFrom c T = c')
    (hc' : c'.state = some anchor)
    (hcut : ∀ t, 0 < t → t < T → (M.runFrom c t).state ≠ some anchor) :
    (seamReleaseTM M anchor).runFrom (c.mapState fun _ => Sum.inl ()) T =
        c'.mapState Sum.inr ∧
      ∀ t < T,
        ((seamReleaseTM M anchor).runFrom
            (c.mapState fun _ => Sum.inl ()) t).state ≠
          some (Sum.inr anchor) := by
  constructor
  · rw [seamRelease_run_pos M anchor c hc T hT, h]
  · intro t ht
    by_cases htpos : 0 < t
    · rw [seamRelease_run_pos M anchor c hc t htpos]
      intro heq
      apply hcut t htpos ht
      change Option.map Sum.inr (M.runFrom c t).state =
        some (Sum.inr anchor) at heq
      obtain ⟨q, hq, heq⟩ := Option.map_eq_some_iff.mp heq
      exact hq.trans (congrArg some (Sum.inr.inj heq))
    · have htzero : t = 0 := by omega
      simp [htzero, Cfg.mapState, hc]

/-- **R3′ space** (spec, fill pending — round-1 repair R3): the adapter's
visited sets equal `M`'s at every time and on every tape — the trajectories
coincide step for step.

**Proof sketch.** Every adapter step applies the very action `M` applies at
the corresponding state (the fresh step at the anchor, `Sum.inr` steps at
their carried state), so the head trajectories agree; project
`seamReleaseTM_firstReturn`'s lockstep. -/
theorem seamReleaseTM_visitedByTapeHead (M : MultiTapeTM k Bool S)
    (anchor : S) {c : Cfg k Bool S x} (hc : c.state = some anchor)
    (t : ℕ) (i : Fin k) :
    (seamReleaseTM M anchor).visitedByTapeHead
        (c.mapState fun _ => Sum.inl ()) t i =
      M.visitedByTapeHead c t i := by
  unfold MultiTapeTM.visitedByTapeHead
  apply Finset.image_congr
  intro s _
  dsimp only
  by_cases hs : s = 0
  · subst s
    rfl
  · rw [seamRelease_run_pos M anchor c hc s (Nat.pos_of_ne_zero hs)]
    rfl

end Turing
