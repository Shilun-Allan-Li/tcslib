/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.Convention
import TCSlib.Complexity.TuringMachine.StateRenaming
import TCSlib.Complexity.TuringMachine.Build.Embed

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: seam composition (R2)

The configuration-level sequencing layer of the machine-construction
library (`machine-library-design.md` §12, R2): sequential composition of
two controllers over **any tape alphabet and from arbitrary
configurations** (the `_ofCfg` theorems; alphabet-generic since §13d G1). If
`M₁` carries a configuration `c₀` to `c₁` within `T₁` under a first-return
cut, and `M₂` carries `c₁` to `c₂` within `T₂`, the dispatch-glued
composite carries `c₀` to `c₂` within `T₁ + 1 + T₂` — the explicit
constant is `1`, one silent stationary dispatch step at the seam. The
canonical `Turing.Cfg.ofWords` seams of
`TCSlib.Complexity.TuringMachine.Build.Convention` are the `Bool`
specialization (`Turing.seamCompTM_run` and its siblings). This is the generic form of the
per-batch dispatch gluing re-proved in every A-chain and emitter batch,
and it exists at the configuration level precisely because the emitter
round-1 finding stands: *function-level* contracts cannot deliver
clean-return seams, so composing `ComputesFunInTime` contracts can never
replace this combinator.

**Status: proved.** The composite is a real definition
(state-sum dispatch in `Turing.bufferedCompTM`'s style, kept minimal), and
every §12 contract is proved (§12 fill epoch F1, gate closed 2026-10-09). The
§12.8 two-exit row `Turing.seamCompTM₂_run_ofCfg` (R8.8) is proved from the left
prefix `Turing.seamCompTM_runFrom_left` and the existing right lockstep.
The **phase host** `Turing.phaseHostTM`, with `Turing.phaseHostTM_run` (proved), is the
finite-dispatch generalization: many phases and a redirect table, one dispatch step per
redirect (landed before the §12.8 fill for the record rows). Its table off the redirects is
`Turing.phaseHostTM_tr_of_red_none`, and `Turing.phaseHostTM_run_le` runs a last phase up to its
exit without a dispatch.

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

* `Turing.seamCompTM` — the dispatch-glued composite of two machines over
  any alphabet; at `Bool`, its canonical use is between `Turing.Cfg.ofWords`
  seams.
* `Turing.seamCompTM₂` — a continuation on each of two exit anchors (§12.8,
  R8.8).

## Main results

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
* `Turing.seamCompTM_runFrom_left`, `Turing.seamCompTM₂_run_ofCfg` — the left
  prefix of a seam under a strict exit cut, and the two-exit composition
  (§12.8, R8.8; the latter a statement).
* `Turing.seamCompTM_runFrom_right` — the right segment after the dispatch, at any
  offset (promoted from the private `seamComp_right` at MIG-0b; set-valued exits need it).
* `Turing.seamReleaseTM_step_fresh`, `Turing.seamReleaseTM_step_inr`,
  `Turing.seamReleaseTM_runFrom_pos` — the release adapter's steps and its pointwise
  lockstep at every positive time (promoted from the private `seamRelease_*` lemmas at
  MIG-0b, design §16a item 5).
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
The dispatch-glued sequential composite of `M₁` and `M₂`, over any tape
alphabet (at `Bool`, typically between `Turing.Cfg.ofWords` seams): states
are the sum `S₁ ⊕ S₂`, left states run
`M₁`'s transition table and right states `M₂`'s (each halting where its
phase halts), except that the designated left anchor `exit` takes one
stationary, silent, write-free dispatch step to the right anchor `entry`.
The composite starts at `M₁`'s initial state; a run launched at a left
seam anchor is the intended use. -/
def seamCompTM {Symbol : Type*} [DecidableEq S₁] (M₁ : MultiTapeTM k Symbol S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry : S₂) :
    MultiTapeTM k Symbol (S₁ ⊕ S₂) where
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
private lemma seamComp_step_left {Symbol : Type*} {x : List Symbol} [DecidableEq S₁]
    (M₁ : MultiTapeTM k Symbol S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry : S₂)
    (c : Cfg k Symbol S₁ x) (hc : c.state ≠ some exit) :
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
private lemma seamComp_step_right {Symbol : Type*} {x : List Symbol} [DecidableEq S₁]
    (M₁ : MultiTapeTM k Symbol S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry : S₂) (c : Cfg k Symbol S₂ x) :
    (seamCompTM M₁ exit M₂ entry).step (c.mapState Sum.inr) =
      (M₂.step c).mapState Sum.inr := by
  cases hs : c.state with
  | none => simp [MultiTapeTM.step, Cfg.mapState, hs]
  | some q =>
    simp only [MultiTapeTM.step, Cfg.mapState, hs, Option.map_some]
    rfl

/-- A stationary, silent, write-free action changes only the control field. -/
private lemma seam_stationary_apply {Symbol : Type*} {x : List Symbol} (c : Cfg k Symbol S₁ x) (q : S₁) :
    (Action.mk 0 (fun _ => (none, 0)) none (some q)).apply c =
      { c with state := some q } := by
  simp [Action.apply]

/-- Dispatch preserves all data of an arbitrary live exit configuration. -/
private lemma seamComp_dispatch {Symbol : Type*} {x : List Symbol} [DecidableEq S₁]
    (M₁ : MultiTapeTM k Symbol S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry : S₂)
    (c : Cfg k Symbol S₁ x) (hc : c.state = some exit) :
    (seamCompTM M₁ exit M₂ entry).step (c.mapState Sum.inl) =
      (c.mapState fun _ => entry).mapState Sum.inr := by
  unfold MultiTapeTM.step
  simp only [Cfg.mapState, hc, Option.map_some]
  dsimp only [seamCompTM]
  rw [if_pos rfl, seam_stationary_apply]

/-- **R8.8, the left prefix of a seam** (design §12.8a; promoted from the
private `seamComp_left`, finding SC-4 of the §12.7 statement gate). If `M₁`,
started from an arbitrary configuration `c`, avoids its exit anchor at every
time strictly below `T`, then for every `t ≤ T` the composite started from the
left-mapped `c` is at the left-mapped `M₁` configuration at `t`. No endpoint
equation is required, and the endpoint itself is included. This is the
trajectory statement a host with two exits needs on the branch it does not
take.

**Proof sketch.** Induct on the time; the cut licenses the left-step
identity at every predecessor strictly before the endpoint. -/
theorem seamCompTM_runFrom_left {Symbol : Type*} {x : List Symbol} [DecidableEq S₁]
    (M₁ : MultiTapeTM k Symbol S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry : S₂)
    {c : Cfg k Symbol S₁ x} {T : ℕ}
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

/-- **The seam's right segment** (promoted from the private `seamComp_right` at MIG-0b, with its
universes and its proof; MIG-0a's export of the same name, over `Type`, is this statement's
instance): after the dispatch step, the composite runs the second machine in lockstep, for any
number of steps, from the first machine's endpoint with its state replaced by the second entry.
Set-valued exits need it.

**Proof sketch.** Split the run at the dispatch, use left lockstep and
the exit equation, then iterate the unconditional right-step identity. -/
theorem seamCompTM_runFrom_right {Symbol : Type*} {x : List Symbol} [DecidableEq S₁]
    (M₁ : MultiTapeTM k Symbol S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry : S₂)
    {c₀ c₁ : Cfg k Symbol S₁ x} {T₁ : ℕ}
    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit) (t : ℕ) :
    (seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl)
        (T₁ + 1 + t) =
      (M₂.runFrom (c₁.mapState fun _ => entry) t).mapState Sum.inr := by
  rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_succ_eq_step',
    seamCompTM_runFrom_left M₁ exit M₂ entry hcut T₁ le_rfl, h₁,
    seamComp_dispatch M₁ exit M₂ entry c₁ hexit]
  exact MultiTapeTM.runFrom_comm_of_step (Cfg.mapState Sum.inr)
    (seamComp_step_right M₁ exit M₂ entry) _ t

/-- General endpoint composition, shared by the frozen public forms. -/
private lemma seamComp_run_general {Symbol : Type*} {x : List Symbol} [DecidableEq S₁]
    (M₁ : MultiTapeTM k Symbol S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry : S₂)
    {c₀ c₁ : Cfg k Symbol S₁ x} {c₃ : Cfg k Symbol S₂ x} {T₁ T₂ : ℕ}
    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit)
    (h₂ : M₂.runFrom (c₁.mapState fun _ => entry) T₂ = c₃) :
    (seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl)
        (T₁ + 1 + T₂) = c₃.mapState Sum.inr :=
  (seamCompTM_runFrom_right M₁ exit M₂ entry h₁ hexit hcut T₂).trans
    (congrArg (Cfg.mapState Sum.inr) h₂)

/-- The right final anchor is absent before the total time.
**Proof sketch.** Through the left endpoint, constructor disjointness
excludes the anchor. Afterwards, right lockstep transports the phase-two
cut at the time remaining after dispatch. -/
private lemma seamComp_firstReturn_general {Symbol : Type*} {x : List Symbol} [DecidableEq S₁]
    (M₁ : MultiTapeTM k Symbol S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry q₂ : S₂)
    {c₀ c₁ : Cfg k Symbol S₁ x} {T₁ T₂ : ℕ}
    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit)
    (hcut₂ : ∀ t < T₂,
      (M₂.runFrom (c₁.mapState fun _ => entry) t).state ≠ some q₂) :
    ∀ t < T₁ + 1 + T₂,
      ((seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl) t).state ≠
        some (Sum.inr q₂) := by
  intro t ht
  by_cases hleft : t ≤ T₁
  · rw [seamCompTM_runFrom_left M₁ exit M₂ entry hcut t hleft]
    cases (M₁.runFrom c₀ t).state <;> simp [Cfg.mapState]
  · have htime : t = T₁ + 1 + (t - (T₁ + 1)) := by omega
    rw [htime, seamCompTM_runFrom_right M₁ exit M₂ entry h₁ hexit hcut]
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
private lemma seamComp_visited_general {Symbol : Type*} {x : List Symbol} [DecidableEq S₁]
    (M₁ : MultiTapeTM k Symbol S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry : S₂)
    {c₀ c₁ : Cfg k Symbol S₁ x} {T₁ T₂ : ℕ}
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
  · rw [seamCompTM_runFrom_left M₁ exit M₂ entry hcut t hleft]
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr (by omega), rfl⟩
  · have htime : t = T₁ + 1 + (t - (T₁ + 1)) := by omega
    rw [htime, seamCompTM_runFrom_right M₁ exit M₂ entry h₁ hexit hcut]
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr
      ⟨t - (T₁ + 1), Finset.mem_range.mpr (by omega), rfl⟩

/-- State mapping of a canonical seam changes only its anchor. -/
private lemma seam_ofWords_mapState {S₃ : Type*} (f : S₁ → S₃)
    (q : S₁) (w : Fin k → List Bool) :
    (Cfg.ofWords (input := x) q w).mapState f = Cfg.ofWords (f q) w := rfl

/-- **R2, seam-to-seam composition** (design §12;
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

/-- **R2, the inherited first-return cut** (design
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

/-- **R2 space, the per-tape headline** (design §12,
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

/-- **R2 space, the per-tape sum corollary** (design
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

/-- **R2 space, the total sum corollary** (design
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
theorem seamCompTM_run_ofCfg {Symbol : Type*} {x : List Symbol} [DecidableEq S₁] (M₁ : MultiTapeTM k Symbol S₁)
    (exit : S₁) (M₂ : MultiTapeTM k Symbol S₂) (entry : S₂)
    {c₀ c₁ : Cfg k Symbol S₁ x} {c₃ : Cfg k Symbol S₂ x} {T₁ T₂ : ℕ}
    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit)
    (h₂ : M₂.runFrom (c₁.mapState fun _ => entry) T₂ = c₃) :
    (seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl)
        (T₁ + 1 + T₂) =
      c₃.mapState Sum.inr := by
  exact seamComp_run_general M₁ exit M₂ entry h₁ hexit hcut h₂

/-- **R2′, the general inherited first-return cut**
(round-1 repair R2): under the hypotheses of
`Turing.seamCompTM_run_ofCfg`, if `M₂` first reaches `q₂` at `T₂`, the
composite first reaches `Sum.inr q₂` at `T₁ + 1 + T₂`.

**Proof sketch.** As `seamCompTM_firstReturn`, over the general lockstep
segments: left times produce `Sum.inl` states, right times the
`Sum.inr`-mapped `M₂` states at shifted time, and injectivity of the
constructors transports the cuts. -/
theorem seamCompTM_firstReturn_ofCfg {Symbol : Type*} {x : List Symbol} [DecidableEq S₁]
    (M₁ : MultiTapeTM k Symbol S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry : S₂) (q₂ : S₂)
    {c₀ c₁ : Cfg k Symbol S₁ x} {c₃ : Cfg k Symbol S₂ x} {T₁ T₂ : ℕ}
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

/-- **R2′ space, the general per-tape headline**
(round-1 repair R2): under the hypotheses of `Turing.seamCompTM_run_ofCfg`,
on every work tape the composite's visited set over the composed run is
contained in the union of the two phases' visited sets — the
general-configuration form of `Turing.seamCompTM_visitedByTapeHead`, from
which the canonical corollaries project.

**Proof sketch.** As the canonical headline: the two lockstep segments
reproduce the phases' trajectories, and the dispatch step is stationary at
a point both phases' endpoint/start configurations already visit. -/
theorem seamCompTM_visitedByTapeHead_ofCfg {Symbol : Type*} {x : List Symbol} [DecidableEq S₁]
    (M₁ : MultiTapeTM k Symbol S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry : S₂)
    {c₀ c₁ : Cfg k Symbol S₁ x} {T₁ T₂ : ℕ}
    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit) (i : Fin k) :
    (seamCompTM M₁ exit M₂ entry).visitedByTapeHead (c₀.mapState Sum.inl)
        (T₁ + 1 + T₂) i ⊆
      M₁.visitedByTapeHead c₀ T₁ i ∪
        M₂.visitedByTapeHead (c₁.mapState fun _ => entry) T₂ i := by
  exact seamComp_visited_general M₁ exit M₂ entry h₁ hexit hcut i

/-- **R8.8, the two-exit seam** (design §12.8a). Attach a continuation to each
of two exit anchors of a host: `M₁` after `e₁` and `M₂` after `e₂`, by nesting
two `Turing.seamCompTM`s. The host `M₀` with two live anchors is typically
`Turing.counterLoopTM` with its `done` and `escape`. -/
def seamCompTM₂ {Symbol : Type*} {S₀ : Type*} [DecidableEq S₀] [DecidableEq S₁]
    (M₀ : MultiTapeTM k Symbol S₀) (e₁ e₂ : S₀) (M₁ : MultiTapeTM k Symbol S₁) (entry₁ : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry₂ : S₂) :
    MultiTapeTM k Symbol ((S₀ ⊕ S₁) ⊕ S₂) :=
  seamCompTM (seamCompTM M₀ e₁ M₁ entry₁) (Sum.inl e₂) M₂ entry₂

/-- **R8.8, the two-exit seam, general configurations** (design §12.8a).
Suppose the host `M₀`, from an arbitrary configuration `c₀`, reaches `c₁` at
exactly `T₀` and meets neither of the distinct anchors `e₁`, `e₂` earlier.
If `c₁` is at `e₁`, then for every `t` the two-exit composite at `T₀ + 1 + t`
is `M₁`'s run, from `c₁` with only the control state replaced by `entry₁`, at
`t`, mapped into the composite's states; the `M₂` summand is never entered.
Symmetrically, if `c₁` is at `e₂`, the composite at `T₀ + 1 + t` is `M₂`'s run
from `c₁` at `entry₂`. The dispatch costs one stationary step in either branch,
and the continuation runs unboundedly, halting included, so its own first-return
and trajectory statements transfer.

**Proof sketch.** Branch `e₁`: the outer seam's left machine is the inner
composite, whose states stay away from the outer exit `Sum.inl e₂`: before
`T₀` by the cut, at `T₀` because `e₁ ≠ e₂`, and afterwards because they are
`Sum.inr` states or halted. So `Turing.seamCompTM_runFrom_left` for the outer
seam reduces the run to the inner composite's, which `Turing.seamCompTM_run_ofCfg`
and the right lockstep of the inner seam evaluate. Branch `e₂`: the inner
composite reaches `Sum.inl e₂` at `T₀` by `Turing.seamCompTM_runFrom_left`,
never having met `e₁`, and the outer dispatch and right lockstep finish. -/
theorem seamCompTM₂_run_ofCfg {Symbol : Type*} {S₀ : Type*} {x : List Symbol}
    [DecidableEq S₀] [DecidableEq S₁]
    (M₀ : MultiTapeTM k Symbol S₀) (e₁ e₂ : S₀) (he : e₁ ≠ e₂)
    (M₁ : MultiTapeTM k Symbol S₁) (entry₁ : S₁) (M₂ : MultiTapeTM k Symbol S₂) (entry₂ : S₂)
    {c₀ c₁ : Cfg k Symbol S₀ x} {T₀ : ℕ}
    (h₀ : M₀.runFrom c₀ T₀ = c₁)
    (hcut : ∀ t < T₀, (M₀.runFrom c₀ t).state ≠ some e₁ ∧ (M₀.runFrom c₀ t).state ≠ some e₂) :
    (c₁.state = some e₁ → ∀ t : ℕ,
      (seamCompTM₂ M₀ e₁ e₂ M₁ entry₁ M₂ entry₂).runFrom
          ((c₀.mapState Sum.inl).mapState Sum.inl) (T₀ + 1 + t) =
        ((M₁.runFrom (c₁.mapState fun _ => entry₁) t).mapState Sum.inr).mapState Sum.inl) ∧
    (c₁.state = some e₂ → ∀ t : ℕ,
      (seamCompTM₂ M₀ e₁ e₂ M₁ entry₁ M₂ entry₂).runFrom
          ((c₀.mapState Sum.inl).mapState Sum.inl) (T₀ + 1 + t) =
        (M₂.runFrom (c₁.mapState fun _ => entry₂) t).mapState Sum.inr) := by
  constructor
  · intro h1 t
    have hcut₁ : ∀ s < T₀, (M₀.runFrom c₀ s).state ≠ some e₁ := fun s hs => (hcut s hs).1
    have hinner : ∀ s, (seamCompTM M₀ e₁ M₁ entry₁).runFrom (c₀.mapState Sum.inl)
        (T₀ + 1 + s) = (M₁.runFrom (c₁.mapState fun _ => entry₁) s).mapState Sum.inr :=
      fun s => seamCompTM_run_ofCfg M₀ e₁ M₁ entry₁ h₀ h1 hcut₁ rfl
    have hcutO : ∀ s < T₀ + 1 + t, ((seamCompTM M₀ e₁ M₁ entry₁).runFrom
        (c₀.mapState Sum.inl) s).state ≠ some (Sum.inl e₂) := by
      intro s hs h
      by_cases hle : s ≤ T₀
      · rw [seamCompTM_runFrom_left M₀ e₁ M₁ entry₁ hcut₁ s hle] at h
        rcases Nat.lt_or_ge s T₀ with hlt | hge
        · exact (hcut s hlt).2 (by simpa [Cfg.mapState] using h)
        · obtain rfl : s = T₀ := by omega
          rw [h₀] at h
          exact he (by simpa [Cfg.mapState, h1] using h)
      · obtain ⟨r, rfl⟩ : ∃ r, s = T₀ + 1 + r := ⟨s - (T₀ + 1), by omega⟩
        rw [hinner r] at h
        simp [Cfg.mapState] at h
    have h := seamCompTM_runFrom_left (seamCompTM M₀ e₁ M₁ entry₁) (Sum.inl e₂) M₂ entry₂
      hcutO (T₀ + 1 + t) le_rfl
    rw [hinner t] at h
    exact h
  · intro h2 t
    have hcut₁ : ∀ s < T₀, (M₀.runFrom c₀ s).state ≠ some e₁ := fun s hs => (hcut s hs).1
    have hin : (seamCompTM M₀ e₁ M₁ entry₁).runFrom (c₀.mapState Sum.inl) T₀ =
        c₁.mapState Sum.inl := by
      rw [seamCompTM_runFrom_left M₀ e₁ M₁ entry₁ hcut₁ T₀ le_rfl, h₀]
    have hcutO : ∀ s < T₀, ((seamCompTM M₀ e₁ M₁ entry₁).runFrom
        (c₀.mapState Sum.inl) s).state ≠ some (Sum.inl e₂) := by
      intro s hs h
      rw [seamCompTM_runFrom_left M₀ e₁ M₁ entry₁ hcut₁ s hs.le] at h
      exact (hcut s hs).2 (by simpa [Cfg.mapState] using h)
    have hmap : ((c₁.mapState (Sum.inl : S₀ → S₀ ⊕ S₁)).mapState (fun _ => entry₂) :
        Cfg k Symbol S₂ x) = c₁.mapState (fun _ => entry₂) := by
      apply Cfg.ext <;> simp [Cfg.mapState, h2]
    have h := seamCompTM_run_ofCfg (seamCompTM M₀ e₁ M₁ entry₁) (Sum.inl e₂) M₂ entry₂ hin
      (by simp [Cfg.mapState, h2]) hcutO
      (rfl : M₂.runFrom ((c₁.mapState (Sum.inl : S₀ → S₀ ⊕ S₁)).mapState fun _ => entry₂) t = _)
    rw [hmap] at h
    exact h

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
def seamReleaseTM {Symbol : Type*} (M : MultiTapeTM k Symbol S) (anchor : S) :
    MultiTapeTM k Symbol (Unit ⊕ S) where
  q₀ := Sum.inl ()
  tr := fun q inp w =>
    match q with
    | Sum.inl _ =>
      let a := M.tr anchor inp w
      ⟨a.inputTape, a.workTapes, a.output, a.state.map Sum.inr⟩
    | Sum.inr s =>
      let a := M.tr s inp w
      ⟨a.inputTape, a.workTapes, a.output, a.state.map Sum.inr⟩

/-- **The release's fresh step** (promoted from the private `seamRelease_fresh_step` at MIG-0b):
from a configuration at the anchor, the release adapter's fresh state applies the anchor's action,
and the resulting state is right-tagged. There is no dispatch step. -/
theorem seamReleaseTM_step_fresh {Symbol : Type*} {x : List Symbol} (M : MultiTapeTM k Symbol S)
    (anchor : S) (c : Cfg k Symbol S x) (hc : c.state = some anchor) :
    (seamReleaseTM M anchor).step (c.mapState fun _ => Sum.inl ()) =
      (M.step c).mapState Sum.inr := by
  simp only [MultiTapeTM.step, Cfg.mapState, hc, Option.map_some]
  rfl

/-- **The release's right-tagged steps** (promoted from the private `seamRelease_step_right` at
MIG-0b): on a right-tagged configuration, a step of the release adapter is the source step,
right-tagged; a halted configuration stays halted. -/
theorem seamReleaseTM_step_inr {Symbol : Type*} {x : List Symbol} (M : MultiTapeTM k Symbol S)
    (anchor : S) (c : Cfg k Symbol S x) :
    (seamReleaseTM M anchor).step (c.mapState Sum.inr) =
      (M.step c).mapState Sum.inr := by
  cases hs : c.state with
  | none => simp [MultiTapeTM.step, Cfg.mapState, hs]
  | some q =>
    simp only [MultiTapeTM.step, Cfg.mapState, hs, Option.map_some]
    rfl

/-- **The pointwise release lockstep** (design §16a item 5; promoted from the private
`seamRelease_run_pos` at MIG-0b, with its universes and its proof): started at its fresh state
over a configuration at the anchor, the release adapter is, at every positive time, the source
run with its states right-tagged. This also covers a source that halts or never returns.

**Proof sketch.** Execute the fresh step once (`Turing.seamReleaseTM_step_fresh`), then iterate
the right-step identity (`Turing.seamReleaseTM_step_inr`). -/
theorem seamReleaseTM_runFrom_pos {Symbol : Type*} {x : List Symbol} (M : MultiTapeTM k Symbol S)
    (anchor : S) (c : Cfg k Symbol S x) (hc : c.state = some anchor) (t : ℕ) (ht : 0 < t) :
    (seamReleaseTM M anchor).runFrom (c.mapState fun _ => Sum.inl ()) t =
      (M.runFrom c t).mapState Sum.inr := by
  cases t with
  | zero => omega
  | succ t =>
    rw [MultiTapeTM.runFrom_succ_eq_step, seamReleaseTM_step_fresh M anchor c hc,
      MultiTapeTM.runFrom_succ_eq_step]
    exact MultiTapeTM.runFrom_comm_of_step (Cfg.mapState Sum.inr)
      (seamReleaseTM_step_inr M anchor) _ t

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
theorem seamReleaseTM_firstReturn {Symbol : Type*} {x : List Symbol} (M : MultiTapeTM k Symbol S) (anchor : S)
    {c c' : Cfg k Symbol S x} {T : ℕ}
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
  · rw [seamReleaseTM_runFrom_pos M anchor c hc T hT, h]
  · intro t ht
    by_cases htpos : 0 < t
    · rw [seamReleaseTM_runFrom_pos M anchor c hc t htpos]
      intro heq
      apply hcut t htpos ht
      change Option.map Sum.inr (M.runFrom c t).state =
        some (Sum.inr anchor) at heq
      obtain ⟨q, hq, heq⟩ := Option.map_eq_some_iff.mp heq
      exact hq.trans (congrArg some (Sum.inr.inj heq))
    · have htzero : t = 0 := by omega
      simp [htzero, Cfg.mapState, hc]

/-- **R3′ space** (round-1 repair R3): the adapter's
visited sets equal `M`'s at every time and on every tape — the trajectories
coincide step for step.

**Proof sketch.** Every adapter step applies the very action `M` applies at
the corresponding state (the fresh step at the anchor, `Sum.inr` steps at
their carried state), so the head trajectories agree; project
`seamReleaseTM_firstReturn`'s lockstep. -/
theorem seamReleaseTM_visitedByTapeHead {Symbol : Type*} {x : List Symbol} (M : MultiTapeTM k Symbol S)
    (anchor : S) {c : Cfg k Symbol S x} (hc : c.state = some anchor)
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
  · rw [seamReleaseTM_runFrom_pos M anchor c hc s (Nat.pos_of_ne_zero hs)]
    rfl

/-! ### The phase host: finite dispatch over many phases (§12.8 fill)

`Turing.seamCompTM` dispatches one exit and `Turing.seamCompTM₂` two. A module that branches
on finite data, or repeats a row a data-dependent but bounded number of times, needs one host
over a finite family of phases with a redirect table. -/

/-- **The phase host** (design §12.8a, record rows; §12.8 fill). Phase `i` runs `M i`. A
state that `red` maps to `some q` takes one stationary, silent dispatch step to `q`; every
other state follows its phase's table. With two phases and one redirect it is the seam
discipline of `Turing.seamCompTM`. -/
def phaseHostTM {k : ℕ} {Γ : Type} {I : Type} {Ph : I → Type}
    (M : (i : I) → MultiTapeTM k Γ (Ph i)) (q0 : Σ i, Ph i)
    (red : (i : I) → Ph i → Option (Σ i, Ph i)) : MultiTapeTM k Γ (Σ i, Ph i) where
  q₀ := q0
  tr := fun q inp w =>
    match red q.1 q.2 with
    | some q' => ⟨0, fun _ => (none, 0), none, some q'⟩
    | none => ((M q.1).tr q.2 inp w).mapState (Sigma.mk q.1)

/-- **The phase lemma** (§12.8 fill). Run phase `i` from `c` for `T` steps to `c'`, ending in
a state that `red` redirects to `q'`, with no redirect earlier. Then, up to `T`, the host is
the phase run with states tagged by `i`; one dispatch step later it is `c'` with only its
control replaced by `q'`.

**Proof sketch.** Before the exit the host's table agrees with the tagged phase table on every
reached state, so the agreement transfer `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`
gives the prefix; the dispatch is one explicit step. No seam induction is repeated. -/
theorem phaseHostTM_run {k : ℕ} {Γ : Type} {I : Type} {Ph : I → Type}
    (M : (i : I) → MultiTapeTM k Γ (Ph i)) (q0 : Σ i, Ph i)
    (red : (i : I) → Ph i → Option (Σ i, Ph i)) (i : I) {x : List Γ}
    (c c' : Cfg k Γ (Ph i) x) (T : ℕ) (h : (M i).runFrom c T = c') (s' : Ph i)
    (hs' : c'.state = some s') (q' : Σ i, Ph i) (hred : red i s' = some q')
    (hguard : ∀ u < T, ∀ s, ((M i).runFrom c u).state = some s → red i s = none) :
    (∀ u ≤ T, (phaseHostTM M q0 red).runFrom (c.mapState (Sigma.mk i)) u =
        ((M i).runFrom c u).mapState (Sigma.mk i)) ∧
      (phaseHostTM M q0 red).runFrom (c.mapState (Sigma.mk i)) (T + 1) =
        c'.mapState (fun _ => q') := by
  have hpre : ∀ u ≤ T, (phaseHostTM M q0 red).runFrom (c.mapState (Sigma.mk i)) u =
      ((M i).runFrom c u).mapState (Sigma.mk i) := by
    intro u hu
    exact MultiTapeTM.runFrom_mapState_of_agreeOn (M i) (phaseHostTM M q0 red)
      ⟨Sigma.mk i, sigma_mk_injective⟩ (fun s => red i s = none)
      (fun s hs inp work => by simp only [phaseHostTM, Function.Embedding.coeFn_mk, hs])
      c u (fun v hv s hs => hguard v (by omega) s hs)
  refine ⟨hpre, ?_⟩
  rw [MultiTapeTM.runFrom_succ_eq_step', hpre T le_rfl, h]
  have hst : (c'.mapState (Sigma.mk i)).state = some ⟨i, s'⟩ := by
    simp [Cfg.mapState, hs']
  simp only [MultiTapeTM.step, hst, phaseHostTM, hred]
  apply Cfg.ext <;> simp [Cfg.mapState, hs']

/-- **The phase host's table off the redirects**: at a state `s` of phase `i` that `red` does
not redirect, the host takes phase `i`'s action, with the successor state tagged by `i`. -/
theorem phaseHostTM_tr_of_red_none {k : ℕ} {Γ : Type} {I : Type} {Ph : I → Type}
    (M : (i : I) → MultiTapeTM k Γ (Ph i)) (q0 : Σ i, Ph i)
    (red : (i : I) → Ph i → Option (Σ i, Ph i)) (i : I) (s : Ph i) (hs : red i s = none)
    (inp : Option Γ) (w : Fin k → Option Γ) :
    (phaseHostTM M q0 red).tr ⟨i, s⟩ inp w = ((M i).tr s inp w).mapState (Sigma.mk i) := by
  simp only [phaseHostTM, hs]

/-- **The phase lemma for a last phase.** Run phase `i` from `c` for `T` steps, with no
redirect strictly before `T`. Then, up to and including `T`, the host is the phase run with
states tagged by `i`. Unlike `Turing.phaseHostTM_run`, nothing is assumed of the state at `T`:
it may be a live exit that `red` does not redirect, so this serves a host's last phase.

**Proof sketch.** On every state reached before `T` the host's table is the tagged phase table
(`Turing.phaseHostTM_tr_of_red_none`), so the agreement transfer
`Turing.MultiTapeTM.runFrom_mapState_of_agreeOn` gives the run up to `T`. -/
theorem phaseHostTM_run_le {k : ℕ} {Γ : Type} {I : Type} {Ph : I → Type}
    (M : (i : I) → MultiTapeTM k Γ (Ph i)) (q0 : Σ i, Ph i)
    (red : (i : I) → Ph i → Option (Σ i, Ph i)) (i : I) {x : List Γ}
    (c : Cfg k Γ (Ph i) x) (T : ℕ)
    (hguard : ∀ u < T, ∀ s, ((M i).runFrom c u).state = some s → red i s = none) :
    ∀ u ≤ T, (phaseHostTM M q0 red).runFrom (c.mapState (Sigma.mk i)) u =
        ((M i).runFrom c u).mapState (Sigma.mk i) := by
  intro u hu
  exact MultiTapeTM.runFrom_mapState_of_agreeOn (M i) (phaseHostTM M q0 red)
    ⟨Sigma.mk i, sigma_mk_injective⟩ (fun s => red i s = none)
    (fun s hs inp work => phaseHostTM_tr_of_red_none M q0 red i s hs inp work)
    c u (fun v hv s hs => hguard v (by omega) s hs)

end Turing
