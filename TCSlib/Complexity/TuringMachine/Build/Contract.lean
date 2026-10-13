/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Tactic.Linarith
import TCSlib.Complexity.TuringMachine.Build.Seam
import TCSlib.Complexity.TuringMachine.Build.Catalog

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Framed contracts (MIG-0a)

**Status: proved; landed 2026-10-13 after the MIG-0a gate closed at round 2**
(`audits/mig0a-findings.md`, `audits/mig0a-r2-findings.md`; resolutions
`audits/mig0a-resolutions.md`). Every definition and theorem is proved: the draft by two
read-only fit tests (2026-10-12) that changed no statement, and the gate additions (`live`, the
two exports, `frames_iff`) by the maintainer. No statement or proof changed between the two
rounds. Round 2 repaired the documentation, and imports `Build/Catalog` and
`Mathlib.Tactic.Linarith` in place of `Build/CounterLoop`, none of whose own declarations the file
uses. `clearTM_contract` and `clearTM_contract_frames` are the routine instance. MIG-0b (design
§16a) follows.

A *contract* packages what the library's framed rows state one by one (design §14 item 0,
§16): started at `entry` in a configuration satisfying the precondition, the machine reaches
the endpoint `post` after **exactly** `time` steps, has **not** reached an exit before, and
keeps every work head inside an interval. "Within `B`" and the space bound are derived. It is
the **first-exit** specialization: segments whose endpoint need not be a first exit,
return-or-escape rounds and joint head trajectories are MIG-0b's layers (below).

## Design

* **Exact time and the cut are fields** (§16). The cut includes time `0`, as in about 45 of the
  library's rows. A row that returns to its own anchor, so that its cut starts at time `1` (the
  advancing writer `Turing.writeAdvTM_run_ofCfg`), is a `Turing.ReturnContract`, turned into a
  contract by the release adapter (`Turing.ReturnContract.release`, over
  `Turing.seamReleaseTM`). The install and emit calls (`Turing.FinTM.exists_installCallTM`,
  `Turing.FinTM.exists_emitCallTM`) quantify separate `entry` and `exit` states that may
  coincide: with arbitrary witnesses, split on `entry = exit` (see `Turing.ReturnContract`).
* **Exits form a set**, so one structure covers single anchors, verdict pairs (`yes`/`no`),
  loop exits (`done`/`escape`) and halting (`none`).
* **The endpoint is a function** of a data index `i : ι` and the start configuration. Data the
  module reads (a stored word, a record's fields) is the index; the precondition says where it
  is stored.
* **Head envelopes are intervals** `[lo, hi]` per tape, functions of the index and the start
  configuration. The radius form is a special case (`Turing.Contract.mem_Icc_of_abs_le`); space
  follows from `MultiTapeTM.spaceUsedByTape_le_card_Icc`.
* **Frames are part of the endpoint** (rows already state them as `{ d with … }`); a derived
  layer names them for composition proofs (user decision, 2026-10-12): `Turing.Cfg.SameOutside`,
  its `.keep` lemmas, and `Turing.Contract.Frames`, adapted from [AFM26]'s framing.
  `Turing.Cfg.SameOutside` is an endpoint relation on work-tape contents only.
* **Universes:** alphabet, states and index in `Type`, the universe of `FinTM`, `phaseHostTM`
  and `counterLoopTMVia` (backlog UNIV-1 folds in here).

## Main definitions

* `Turing.Contract`: the structure.
* `Turing.Contract.trans`: first-exit sequencing on one machine, with no dispatch step. It is
  not a general `RecordRun` concatenation (MIG-0b's segment layer).
* `Turing.Contract.seq`: sequencing through the R2 seam `Turing.seamCompTM`, after a first
  phase with a single live exit.
* `Turing.Contract.inPhase`: a phase run inside the phase host `Turing.phaseHostTM`, with an
  arbitrary set of live exits, each redirected.
* `Turing.Contract.embed`: transport along the R1 embedding `Turing.embedEmitTM`, for
  output-normalized preconditions.
* `Turing.Contract.branch`: the two-way seam `Turing.seamCompTM₂`, after a first phase with two
  live exits.
* `Turing.ReturnContract`, `Turing.ReturnContract.release`: returning modules and the release
  adapter.
* `Turing.Cfg.SameOutside`, `Turing.Contract.Frames`: the derived frame layer.
* `Turing.clearTM_contract`: R3 clear as a contract (the routine instance).

**Routing.** `seq` is the single-live-exit seam, `branch` the binary case, and the phase host
(`inPhase`) handles an arbitrary set of live exits, several of which may share one continuation.
A first phase that halts cannot resume through a seam, which dispatches only at a live anchor.

## Main results

* `Turing.Contract.within`: the derived "within `B`" form.
* `Turing.Contract.spaceUsedByTape_le`: the derived per-tape space bound.
* `Turing.Cfg.SameOutside.keep_word`, `Turing.Cfg.SameOutside.keep_blank`: frame preservation.
* `Turing.clearTM_contract_frames`: R3 clear frames exactly the cleared cells.
* `Turing.Contract.live`: a contract run is live before its endpoint.
* `Turing.embedEmitCfg_unselected`, `Turing.seamCompTM_runFrom_right`: two exports the library
  lacks, derived here from public rows. They move to `Build/Embed` and `Build/Seam` with MIG-0b's
  layering split (backlog MIG-0). The pointwise release export `seamReleaseTM_runFrom_pos` is
  deferred to MIG-0b.

## Later rows (MIG-0b; design §16a)

MIG-0b, as revised after the MIG-0a gate's round 1 (major 1, minors 2 and 6, note 20), covers
these before any dependent migration; `Turing.Contract` stays the first-exit specialization.

* A **segment and round layer.** Segments: fixed-length runs that avoid a forbidden set, whose
  endpoint need not be a first exit, with same-machine concatenation (`CfgRecord`'s `RecordRun`
  and `recordRun_trans`), and a bridge to `Turing.Contract` when the endpoint is a first exit.
  Rounds: return-or-escape runs with positive cuts against both the anchor and the escape
  (`RecordTable`'s `rt_find_round_entry`, the counter loop's rounds).
* A **joint-trajectory layer**: a relation on the whole head vector along the run, derived like
  `Turing.Contract.Frames` and preserved by the compositions (`CounterLoop`'s `counterSpan`).
* The **layering split**: a core contract module that `Build/Loop` and `Build/CounterLoop` can
  import, with the seam and embedding adapters and the routine instance elsewhere; the two
  exports then move to `Build/Embed` and `Build/Seam`.
* The pointwise release export `seamReleaseTM_runFrom_pos`.
* The symbol lift (`MultiTapeTM.liftSymbols_runFrom`, through `Cfg.decodeSymbols`), the counter
  loop (`counterLoopTMVia_run_done`/`_run_escape`, over the round layer), and state renaming
  along an embedding (`runFrom_mapState_of_agreeOn`).
* The tactics.
* The alphabet-reduction and robustness-lockstep adapters (round 1, note 20).

## References

* [AFM26] Anthropic, PBC, `anthropics/formal-math` (https://github.com/anthropics/formal-math),
  project `3sum-apsp`, commit `e1a4e650` (2026-10-05), Apache-2.0, © Anthropic, PBC; examined
  2026-10-12 (design §15, *Prior art examined*). Design adaptation (policy §2): the framing of
  `ThreeSumApsp/Lang/Regions.lean` (`SameOn`, `SameOutside` and the `.keep` lemmas), adapted as
  `Turing.Cfg.SameOutside`, its `.keep` lemmas and `Turing.Contract.Frames`; and the
  specification-only calls of `ThreeSumApsp/Lang/Calls.lean` (`Meets`, over the program logic
  `Ends` of `ThreeSumApsp/Lang/Logic.lean`), adapted as `Turing.Contract`, through which the
  compositions use their operands. These upstream files are vendored, with the local changes
  their headers list, as `TCSlib/Programs/Light/Regions.lean`, `Calls.lean` and `Logic.lean`.
  The treatment of time differs: exact time and a no-earlier-exit cut, not "within `T`" (§16).
-/

namespace Turing

variable {k : ℕ} {Γ : Type}

/-- **A framed contract** (design §14 item 0, §16). For every data index `i` and every start
configuration `d` at `entry` satisfying `pre i d` (an *admissible* start), the machine reaches
`post i d` after exactly `time i d` steps; `post i d` is at an exit; no exit is reached earlier
(the cut includes time `0`); and through the endpoint every work head `j` stays in
`[lo i d j, hi i d j]`. Nothing is asserted for other starts. This is the first-exit
specialization (see the module docstring for the segment, round and joint-trajectory layers of
MIG-0b).

[AFM26], design adaptation: a specification that a caller uses instead of the run, as with the
specification-only calls (`Meets`) of `Lang/Calls.lean`. Unlike there, the time is exact and
comes with a no-earlier-exit cut, rather than "within `T`" (§16). -/
structure Contract {S : Type} (M : MultiTapeTM k Γ S) (entry : S) (exits : Set (Option S))
    (ι : Type) (x : List Γ) where
  /-- The precondition on the start configuration, for data `i`. -/
  pre : ι → Cfg k Γ S x → Prop
  /-- The exact running time. -/
  time : ι → Cfg k Γ S x → ℕ
  /-- The endpoint. -/
  post : ι → Cfg k Γ S x → Cfg k Γ S x
  /-- The lower ends of the head envelope. -/
  lo : ι → Cfg k Γ S x → Fin k → ℤ
  /-- The upper ends of the head envelope. -/
  hi : ι → Cfg k Γ S x → Fin k → ℤ
  run : ∀ i d, d.state = some entry → pre i d → M.runFrom d (time i d) = post i d
  exit_mem : ∀ i d, d.state = some entry → pre i d → (post i d).state ∈ exits
  cut : ∀ i d, d.state = some entry → pre i d →
    ∀ u < time i d, (M.runFrom d u).state ∉ exits
  env : ∀ i d, d.state = some entry → pre i d → ∀ u ≤ time i d, ∀ j,
    (M.runFrom d u).workTapePos j ∈ Finset.Icc (lo i d j) (hi i d j)

namespace Contract

section Derived

variable {S : Type} {M : MultiTapeTM k Γ S} {entry : S} {exits : Set (Option S)} {ι : Type}
  {x : List Γ}

/-- The derived "within `B`" form, the shape of the library's existential rows. -/
theorem within (C : Contract M entry exits ι x) (i : ι) (d : Cfg k Γ S x)
    (hd : d.state = some entry) (hp : C.pre i d) {B : ℕ} (hB : C.time i d ≤ B) :
    ∃ t ≤ B, (∀ u < t, (M.runFrom d u).state ∉ exits) ∧ M.runFrom d t = C.post i d :=
  ⟨C.time i d, hB, C.cut i d hd hp, C.run i d hd hp⟩

/-- The derived per-tape space bound: the envelope's width. -/
theorem spaceUsedByTape_le (C : Contract M entry exits ι x) (i : ι) (d : Cfg k Γ S x)
    (hd : d.state = some entry) (hp : C.pre i d) (j : Fin k) :
    M.spaceUsedByTape d (C.time i d) j ≤ (C.hi i d j + 1 - C.lo i d j).toNat :=
  M.spaceUsedByTape_le_card_Icc d (C.time i d) j (C.lo i d j) (C.hi i d j)
    fun u hu => C.env i d hd hp u hu j

/-- A positive running time on every admissible start: what a loop round needs. -/
def Positive (C : Contract M entry exits ι x) : Prop :=
  ∀ i d, d.state = some entry → C.pre i d → 0 < C.time i d

/-- The radius form of an envelope is the interval form about the start position. -/
theorem mem_Icc_of_abs_le {p q R : ℤ} (h : |p - q| ≤ R) : p ∈ Finset.Icc (q - R) (q + R) := by
  rw [Finset.mem_Icc]
  constructor <;> linarith [abs_le.mp h]

end Derived

section Compose

private lemma mem_hull_left {p a b c e : ℤ} (h : p ∈ Finset.Icc a b) :
    p ∈ Finset.Icc (min a c) (max b e) := by
  rw [Finset.mem_Icc] at h ⊢
  exact ⟨min_le_of_left_le h.1, le_max_of_le_left h.2⟩

private lemma mem_hull_right {p a b c e : ℤ} (h : p ∈ Finset.Icc c e) :
    p ∈ Finset.Icc (min a c) (max b e) := by
  rw [Finset.mem_Icc] at h ⊢
  exact ⟨min_le_of_right_le h.1, le_max_of_le_right h.2⟩

/-- A halted run stays halted. -/
private lemma runFrom_state_none_mono {S : Type} {M : MultiTapeTM k Γ S} {x : List Γ}
    {c : Cfg k Γ S x} {u t : ℕ} (h : (M.runFrom c u).state = none) (hut : u ≤ t) :
    (M.runFrom c t).state = none := by
  obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le hut
  rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ h]
  exact h

/-- **First-exit sequencing on one machine**: run `C₁` to its single exit `e₂`, then `C₂` from
there. Times add with no dispatch step; the envelopes take the pointwise hull. `C₂`'s
precondition is needed only at `C₁`'s actual endpoint (`hlink`), for the linked index. `hX` says
that `C₁` does not pass through an exit of `C₂` before its own exit; it cannot be dropped, since
`C₁`'s cut excludes only `e₂`. This is not a general `RecordRun` concatenation: a segment whose
endpoint need not be a first exit belongs to MIG-0b's segment layer.

**Proof sketch.** Split the time at `C₁`'s time `t₁`. By `C₁`'s run, the run for `t₁ + v` steps
is `C₂`'s run for `v` steps from `C₁`'s endpoint, which is at `e₂` and satisfies `C₂`'s
precondition; this gives the run and the exit. Before `t₁` the cut is `hX`; at a time `t₁ + v`
below the total it is `C₂`'s cut at `v`. Up to `t₁` the heads are in `C₁`'s envelope, and after
it in `C₂`'s; the hull contains both. -/
def trans {S : Type} {M : MultiTapeTM k Γ S} {e₁ e₂ : S} {X : Set (Option S)} {ι κ : Type}
    {x : List Γ} (C₁ : Contract M e₁ {some e₂} ι x) (C₂ : Contract M e₂ X κ x) (link : ι → κ)
    (hlink : ∀ i d, d.state = some e₁ → C₁.pre i d → C₂.pre (link i) (C₁.post i d))
    (hX : ∀ i d, d.state = some e₁ → C₁.pre i d →
      ∀ u < C₁.time i d, (M.runFrom d u).state ∉ X) :
    Contract M e₁ X ι x where
  pre := C₁.pre
  time i d := C₁.time i d + C₂.time (link i) (C₁.post i d)
  post i d := C₂.post (link i) (C₁.post i d)
  lo i d j := min (C₁.lo i d j) (C₂.lo (link i) (C₁.post i d) j)
  hi i d j := max (C₁.hi i d j) (C₂.hi (link i) (C₁.post i d) j)
  run i d hd hp := by
    have hx := Set.mem_singleton_iff.mp (C₁.exit_mem i d hd hp)
    show M.runFrom d (C₁.time i d + C₂.time (link i) (C₁.post i d)) =
      C₂.post (link i) (C₁.post i d)
    rw [MultiTapeTM.runFrom_add, C₁.run i d hd hp]
    exact C₂.run _ _ hx (hlink i d hd hp)
  exit_mem i d hd hp :=
    C₂.exit_mem _ _ (Set.mem_singleton_iff.mp (C₁.exit_mem i d hd hp)) (hlink i d hd hp)
  cut i d hd hp u hu := by
    have hx := Set.mem_singleton_iff.mp (C₁.exit_mem i d hd hp)
    change u < C₁.time i d + C₂.time (link i) (C₁.post i d) at hu
    by_cases h : u < C₁.time i d
    · exact hX i d hd hp u h
    · obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp h)
      rw [MultiTapeTM.runFrom_add, C₁.run i d hd hp]
      exact C₂.cut _ _ hx (hlink i d hd hp) v (by omega)
  env i d hd hp u hu j := by
    have hx := Set.mem_singleton_iff.mp (C₁.exit_mem i d hd hp)
    change u ≤ C₁.time i d + C₂.time (link i) (C₁.post i d) at hu
    by_cases h : u ≤ C₁.time i d
    · exact mem_hull_left (C₁.env i d hd hp u h j)
    · obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le (le_of_lt (not_le.mp h))
      rw [MultiTapeTM.runFrom_add, C₁.run i d hd hp]
      exact mem_hull_right (C₂.env _ _ hx (hlink i d hd hp) v (by omega) j)

private lemma mapState_state {S S' : Type} {x : List Γ} (f : S → S') (c : Cfg k Γ S x) :
    (c.mapState f).state = c.state.map f := rfl

/-- The composed start is the left-mapped first-phase start. -/
private lemma mapState_const_inl {S₁ S₂ : Type} {x : List Γ} {e : S₁}
    {d : Cfg k Γ (S₁ ⊕ S₂) x} (hd : d.state = some (Sum.inl e)) :
    (d.mapState fun _ => e).mapState Sum.inl = d :=
  Cfg.ext (by simp [Cfg.mapState, hd]) rfl rfl rfl rfl

/-- The seam trajectory of a contract run: the left segment up to the first exit (live
throughout), and the right segment after the dispatch, at every offset. The composite starts
at `Sum.inl entry₁`; the first phase runs from that start with its state replaced by `entry₁`.

**Proof sketch.** Re-tagging the replaced start by `Sum.inl` gives back the composite start.
`C₁`'s cut is the strict exit cut of `Turing.seamCompTM_runFrom_left`, which gives the left
segment up to `t₁`. It is live: a halt before `t₁` would persist to the endpoint, which is at
`exit₁`. The right segment is `Turing.seamCompTM_run_ofCfg` with second-phase time `v` and that
run's endpoint taken to be itself. The replaced endpoint is at `entry₂` by construction. -/
private lemma seq_traj {S₁ S₂ : Type} [DecidableEq S₁] {M₁ : MultiTapeTM k Γ S₁}
    {M₂ : MultiTapeTM k Γ S₂} {entry₁ exit₁ : S₁} (entry₂ : S₂) {ι : Type} {x : List Γ}
    (C₁ : Contract M₁ entry₁ {some exit₁} ι x) (i : ι) (d : Cfg k Γ (S₁ ⊕ S₂) x)
    (hd : d.state = some (Sum.inl entry₁)) (hp : C₁.pre i (d.mapState fun _ => entry₁)) :
    (∀ u ≤ C₁.time i (d.mapState fun _ => entry₁),
      (seamCompTM M₁ exit₁ M₂ entry₂).runFrom d u =
          (M₁.runFrom (d.mapState fun _ => entry₁) u).mapState Sum.inl ∧
        (M₁.runFrom (d.mapState fun _ => entry₁) u).state ≠ none) ∧
    (∀ v, (seamCompTM M₁ exit₁ M₂ entry₂).runFrom d
        (C₁.time i (d.mapState fun _ => entry₁) + 1 + v) =
      (M₂.runFrom ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂)
        v).mapState Sum.inr) ∧
    ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂).state =
      some entry₂ := by
  have hd' := mapState_const_inl (S₂ := S₂) hd
  have hd₁ : (d.mapState fun _ => entry₁).state = some entry₁ := by simp [Cfg.mapState, hd]
  have h1 := C₁.run i _ hd₁ hp
  have hx := Set.mem_singleton_iff.mp (C₁.exit_mem i _ hd₁ hp)
  have hcut : ∀ t < C₁.time i (d.mapState fun _ => entry₁),
      (M₁.runFrom (d.mapState fun _ => entry₁) t).state ≠ some exit₁ :=
    fun t ht => C₁.cut i _ hd₁ hp t ht
  refine ⟨fun u hu => ⟨?_, ?_⟩, fun v => ?_, by rw [mapState_state, hx]; rfl⟩
  · have hl := seamCompTM_runFrom_left M₁ exit₁ M₂ entry₂ hcut u hu
    rwa [hd'] at hl
  · intro h
    have h' := runFrom_state_none_mono h hu
    rw [h1, hx] at h'
    exact Option.some_ne_none _ h'
  · have hr := seamCompTM_run_ofCfg M₁ exit₁ M₂ entry₂ h1 hx hcut (T₂ := v) rfl
    rwa [hd'] at hr

/-- **Sequencing through the R2 seam** (`Turing.seamCompTM_run_ofCfg`,
`Turing.seamCompTM_firstReturn_ofCfg`): run `C₁` to its single live exit `exit₁`, take one
stationary dispatch step, and run `C₂`, so the time is `t₁ + 1 + t₂`. The second phase starts
from the first's endpoint with its state replaced by `entry₂`; the endpoint and the exits are
right-tagged, and the envelopes take the hull.

This is the **single-live-exit seam**. Two live exits go through `Turing.Contract.branch`, and
an arbitrary set of live exits through the phase host (`Turing.Contract.inPhase`). A first phase
that halts cannot resume through a seam, which dispatches only at a live anchor.

**Proof sketch.** By the seam trajectory (`seq_traj`): up to `t₁` the composite is the
left-tagged first phase, live throughout, and at `t₁ + 1 + v` it is the right-tagged second
phase at `v`, from its entry. The run is `Turing.seamCompTM_run_ofCfg` with `C₂`'s run, and the
exit is `C₂`'s, right-tagged. For the cut, a time up to `t₁` carries a live left-tagged state,
which is no right-tagged exit; a later time is `t₁ + 1 + v` with `v < t₂`, and injectivity of the
right tag reduces it to `C₂`'s cut at `v`. The envelope is `C₁`'s up to `t₁` and `C₂`'s after
the dispatch (offset `0` is the dispatch step), inside the hull. -/
def seq {S₁ S₂ : Type} [DecidableEq S₁] {M₁ : MultiTapeTM k Γ S₁} {M₂ : MultiTapeTM k Γ S₂}
    {entry₁ exit₁ : S₁} {entry₂ : S₂} {X₂ : Set (Option S₂)} {ι κ : Type} {x : List Γ}
    (C₁ : Contract M₁ entry₁ {some exit₁} ι x) (C₂ : Contract M₂ entry₂ X₂ κ x) (link : ι → κ)
    (hlink : ∀ i d, d.state = some entry₁ → C₁.pre i d →
      C₂.pre (link i) ((C₁.post i d).mapState fun _ => entry₂)) :
    Contract (seamCompTM M₁ exit₁ M₂ entry₂) (Sum.inl entry₁) (Option.map Sum.inr '' X₂) ι x where
  pre i d := C₁.pre i (d.mapState fun _ => entry₁)
  time i d := C₁.time i (d.mapState fun _ => entry₁) + 1 +
    C₂.time (link i) ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂)
  post i d :=
    (C₂.post (link i) ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂)).mapState
      Sum.inr
  lo i d j := min (C₁.lo i (d.mapState fun _ => entry₁) j)
    (C₂.lo (link i) ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂) j)
  hi i d j := max (C₁.hi i (d.mapState fun _ => entry₁) j)
    (C₂.hi (link i) ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂) j)
  run i d hd hp := by
    have hd' := mapState_const_inl (S₂ := S₂) hd
    have hd₁ : (d.mapState fun _ => entry₁).state = some entry₁ := by simp [Cfg.mapState, hd]
    have hx := Set.mem_singleton_iff.mp (C₁.exit_mem i _ hd₁ hp)
    have hd₂ := (seq_traj (M₂ := M₂) entry₂ C₁ i d hd hp).2.2
    have hr := seamCompTM_run_ofCfg M₁ exit₁ M₂ entry₂ (C₁.run i _ hd₁ hp) hx
      (fun t ht => C₁.cut i _ hd₁ hp t ht) (C₂.run _ _ hd₂ (hlink i _ hd₁ hp))
    rw [hd'] at hr
    exact hr
  exit_mem i d hd hp := by
    have hd₁ : (d.mapState fun _ => entry₁).state = some entry₁ := by simp [Cfg.mapState, hd]
    have hd₂ := (seq_traj (M₂ := M₂) entry₂ C₁ i d hd hp).2.2
    exact ⟨_, C₂.exit_mem _ _ hd₂ (hlink i _ hd₁ hp), rfl⟩
  cut i d hd hp u hu := by
    have hd₁ : (d.mapState fun _ => entry₁).state = some entry₁ := by simp [Cfg.mapState, hd]
    obtain ⟨hL, hR, hd₂⟩ := seq_traj (M₂ := M₂) entry₂ C₁ i d hd hp
    change u < C₁.time i (d.mapState fun _ => entry₁) + 1 +
      C₂.time (link i) ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂) at hu
    rintro ⟨q, hq, heq⟩
    by_cases hle : u ≤ C₁.time i (d.mapState fun _ => entry₁)
    · obtain ⟨hrun, hlive⟩ := hL u hle
      rw [hrun] at heq
      obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp hlive
      rw [mapState_state, hs] at heq
      cases q <;> simp at heq
    · obtain ⟨v, rfl⟩ : ∃ v, u = C₁.time i (d.mapState fun _ => entry₁) + 1 + v :=
        ⟨u - (C₁.time i (d.mapState fun _ => entry₁) + 1), by omega⟩
      rw [hR v] at heq
      have hq' : q = (M₂.runFrom ((C₁.post i (d.mapState fun _ => entry₁)).mapState
          fun _ => entry₂) v).state := Option.map_injective Sum.inr_injective heq
      exact C₂.cut _ _ hd₂ (hlink i _ hd₁ hp) v (by omega) (hq' ▸ hq)
  env i d hd hp u hu j := by
    have hd₁ : (d.mapState fun _ => entry₁).state = some entry₁ := by simp [Cfg.mapState, hd]
    obtain ⟨hL, hR, hd₂⟩ := seq_traj (M₂ := M₂) entry₂ C₁ i d hd hp
    change u ≤ C₁.time i (d.mapState fun _ => entry₁) + 1 +
      C₂.time (link i) ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂) at hu
    by_cases hle : u ≤ C₁.time i (d.mapState fun _ => entry₁)
    · rw [(hL u hle).1]
      exact mem_hull_left (C₁.env i _ hd₁ hp u hle j)
    · obtain ⟨v, rfl⟩ : ∃ v, u = C₁.time i (d.mapState fun _ => entry₁) + 1 + v :=
        ⟨u - (C₁.time i (d.mapState fun _ => entry₁) + 1), by omega⟩
      rw [hR v]
      exact mem_hull_right (C₂.env _ _ hd₂ (hlink i _ hd₁ hp) v (by omega) j)

/-- **The seam's right segment**: after the dispatch step, the composite runs the second
machine in lockstep for any number of steps. The public form of `Build/Seam.lean`'s private
right-segment lemma, which set-valued exits need. It moves to `Build/Seam` with MIG-0b's
layering split (backlog MIG-0).

**Proof sketch.** `Turing.seamCompTM_run_ofCfg` at second-phase time `v`, with the second run's
endpoint taken to be itself. -/
theorem _root_.Turing.seamCompTM_runFrom_right {S₁ S₂ : Type} [DecidableEq S₁] {x : List Γ}
    (M₁ : MultiTapeTM k Γ S₁) (exit : S₁) (M₂ : MultiTapeTM k Γ S₂) (entry : S₂)
    {c₀ c₁ : Cfg k Γ S₁ x} {T₁ : ℕ} (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit) (v : ℕ) :
    (seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl) (T₁ + 1 + v) =
      (M₂.runFrom (c₁.mapState fun _ => entry) v).mapState Sum.inr :=
  seamCompTM_run_ofCfg M₁ exit M₂ entry h₁ hexit hcut rfl

/-- Re-type a configuration's control state through a partial map: the phase host's redirect.
A halted configuration stays halted; every other field is kept. -/
def _root_.Turing.Cfg.bindState {S S' : Type} {x : List Γ} (d : Cfg k Γ S x) (f : S → Option S') :
    Cfg k Γ S' x :=
  ⟨d.state.bind f, d.inputPos, d.workTapes, d.workTapePos, d.output⟩

/-- The phase-host trajectory of a contract run: the tagged prefix through the phase's exit,
the redirected endpoint one dispatch step later, and the live exit state.

**Proof sketch.** The endpoint's state lies in `X`, which excludes `none`, so it is a live exit
`s'`, which `red p` redirects (`hsome`). Before the endpoint the cut keeps every state out of
`X`, so `hred` says that none of them is redirected. `Turing.phaseHostTM_run` then gives the
prefix tagged with `p` up to the time and, one dispatch step later, the endpoint with its state
replaced by the target of `s'`, which is the endpoint's state bound through `red p`. The
other-phase clause of `hsome` is not used here. -/
private lemma inPhase_traj {I : Type} {Ph : I → Type} (Mf : (i : I) → MultiTapeTM k Γ (Ph i))
    (q0 : Σ i, Ph i) (red : (i : I) → Ph i → Option (Σ i, Ph i)) (p : I) {s₀ : Ph p}
    {X : Set (Option (Ph p))} {ι : Type} {x : List Γ} (C : Contract (Mf p) s₀ X ι x)
    (hnone : none ∉ X) (hred : ∀ s, some s ∉ X → red p s = none)
    (hsome : ∀ s, some s ∈ X → ∃ q, red p s = some q ∧ q.1 ≠ p)
    (i : ι) (d : Cfg k Γ (Σ i, Ph i) x) (hd : d.state = some ⟨p, s₀⟩)
    (hp : C.pre i (d.mapState fun _ => s₀)) :
    (∀ u ≤ C.time i (d.mapState fun _ => s₀),
      (phaseHostTM Mf q0 red).runFrom d u =
        ((Mf p).runFrom (d.mapState fun _ => s₀) u).mapState (Sigma.mk p)) ∧
    (phaseHostTM Mf q0 red).runFrom d (C.time i (d.mapState fun _ => s₀) + 1) =
      (C.post i (d.mapState fun _ => s₀)).bindState (red p) ∧
    ∃ s', (C.post i (d.mapState fun _ => s₀)).state = some s' ∧ some s' ∈ X := by
  have hd' : (d.mapState fun _ => s₀).mapState (Sigma.mk p) = d :=
    Cfg.ext (by simp [Cfg.mapState, hd]) rfl rfl rfl rfl
  have hc : (d.mapState fun _ => s₀).state = some s₀ := by simp [Cfg.mapState, hd]
  have hx := C.exit_mem i _ hc hp
  obtain ⟨s', hs'⟩ : ∃ s', (C.post i (d.mapState fun _ => s₀)).state = some s' := by
    cases h : (C.post i (d.mapState fun _ => s₀)).state with
    | none => rw [h] at hx; exact absurd hx hnone
    | some s' => exact ⟨s', rfl⟩
  have hs'X : some s' ∈ X := by rw [← hs']; exact hx
  obtain ⟨q', hq', -⟩ := hsome s' hs'X
  have H := phaseHostTM_run Mf q0 red p (d.mapState fun _ => s₀) _ _ (C.run i _ hc hp) s' hs'
    q' hq' (fun u hu s hs => hred s (fun hm => C.cut i _ hc hp u hu (by rw [hs]; exact hm)))
  rw [hd'] at H
  refine ⟨H.1, ?_, s', hs', hs'X⟩
  rw [H.2]
  refine Cfg.ext ?_ rfl rfl rfl rfl
  show Option.map (fun _ => q') (C.post i (d.mapState fun _ => s₀)).state =
    (C.post i (d.mapState fun _ => s₀)).state.bind (red p)
  rw [hs']
  simp [hq']

/-- **A phase inside the phase host** (`Turing.phaseHostTM_run`). Phase `p` runs under its own
contract, whose exits are live (`hnone`) and are exactly the states of phase `p` that the host
redirects (`hred`, `hsome`), each to a state of another phase. The host's exits are the
redirect targets, the time gains one dispatch step, and the envelopes are the phase's. The
phase host thus handles an **arbitrary set of live exits**, each sent to its own target, and
several may share one continuation; `Turing.Contract.seq` and `Turing.Contract.branch` are the
one- and two-exit seams.

The other-phase condition `q.1 ≠ p` is **sufficient, not necessary**. What the cut needs is that
the run avoids every redirect target up to its endpoint; up to there the host run is tagged with
phase `p`, so it never meets a state of another phase. A same-phase target that the run avoids
up to its endpoint would also do, while a redirect back to the entry fails at time `0`; a
generalization could ask for that avoidance instead.

**Proof sketch.** By the phase-host trajectory (`inPhase_traj`): up to the phase's time the
host is the phase run tagged with `p`, and one dispatch step later it is the phase's endpoint
with its state bound through `red p`. This gives the run, and the exit is the target of the
phase's live exit. For the cut, a time up to the phase's time carries a state tagged with `p`,
or `none`; a target equal to it would lie in phase `p`, against `q.1 ≠ p`. The envelope is the
phase's up to its time; at the dispatch step the heads are those of the phase's endpoint. -/
def inPhase {I : Type} {Ph : I → Type} (Mf : (i : I) → MultiTapeTM k Γ (Ph i)) (q0 : Σ i, Ph i)
    (red : (i : I) → Ph i → Option (Σ i, Ph i)) (p : I) {s₀ : Ph p} {X : Set (Option (Ph p))}
    {ι : Type} {x : List Γ} (C : Contract (Mf p) s₀ X ι x) (hnone : none ∉ X)
    (hred : ∀ s, some s ∉ X → red p s = none)
    (hsome : ∀ s, some s ∈ X → ∃ q, red p s = some q ∧ q.1 ≠ p) :
    Contract (phaseHostTM Mf q0 red) ⟨p, s₀⟩ {q | ∃ s, some s ∈ X ∧ q = red p s} ι x where
  pre i d := C.pre i (d.mapState fun _ => s₀)
  time i d := C.time i (d.mapState fun _ => s₀) + 1
  post i d := (C.post i (d.mapState fun _ => s₀)).bindState (red p)
  lo i d := C.lo i (d.mapState fun _ => s₀)
  hi i d := C.hi i (d.mapState fun _ => s₀)
  run i d hd hp := (inPhase_traj Mf q0 red p C hnone hred hsome i d hd hp).2.1
  exit_mem i d hd hp := by
    obtain ⟨-, -, s', hs', hs'X⟩ := inPhase_traj Mf q0 red p C hnone hred hsome i d hd hp
    refine ⟨s', hs'X, ?_⟩
    show (C.post i (d.mapState fun _ => s₀)).state.bind (red p) = red p s'
    rw [hs']
    rfl
  cut i d hd hp u hu := by
    change u < C.time i (d.mapState fun _ => s₀) + 1 at hu
    obtain ⟨hL, -, -⟩ := inPhase_traj Mf q0 red p C hnone hred hsome i d hd hp
    rw [hL u (by omega)]
    rintro ⟨s, hsX, heq⟩
    obtain ⟨q, hq, hqp⟩ := hsome s hsX
    rw [hq, mapState_state] at heq
    obtain ⟨a, -, ha⟩ := Option.map_eq_some_iff.mp heq
    exact hqp (by rw [← ha])
  env i d hd hp u hu j := by
    change u ≤ C.time i (d.mapState fun _ => s₀) + 1 at hu
    have hc : (d.mapState fun _ => s₀).state = some s₀ := by simp [Cfg.mapState, hd]
    obtain ⟨hL, hE, -⟩ := inPhase_traj Mf q0 red p C hnone hred hsome i d hd hp
    rcases Nat.lt_or_ge u (C.time i (d.mapState fun _ => s₀) + 1) with h | h
    · rw [hL u (by omega)]
      exact C.env i _ hc hp u (by omega) j
    · obtain rfl : u = C.time i (d.mapState fun _ => s₀) + 1 := by omega
      rw [hE]
      have h' := C.env i _ hc hp _ le_rfl j
      rw [C.run i _ hc hp] at h'
      exact h'

/-- The source configuration seen through an R1 selection: selected tapes and heads, the same
state and input position, and an **empty output**. The selection empties the source output, so
a source precondition is always tested on the output `[]`: `Turing.Contract.embed` transports
output-normalized preconditions only. -/
def _root_.Turing.Cfg.select {m : ℕ} {S : Type} {x : List Γ} (σ : Fin m ↪ Fin k)
    (d : Cfg k Γ S x) : Cfg m Γ S x :=
  ⟨d.state, d.inputPos, fun i => d.workTapes (σ i), fun i => d.workTapePos (σ i), []⟩

/-- Every host configuration is the forwarding embedding of its selection, framed by itself:
embedding the selection of `d` into `d`'s own tapes, heads and output gives back `d`.

**Proof sketch.** Compare field by field. The state and the input position are the
selection's, which are `d`'s. A selected tape or head is the selection's, which is `d`'s, by the
public selected-field lemmas. An unselected tape or head is the frame, which is `d`'s, by the
public frame lemma at time `0` for a trivial machine on `Unit` (the transport's tape fields do not
depend on the state type). The output is `d`'s followed by the selection's empty output. -/
theorem _root_.Turing.embedEmitCfg_select {m : ℕ} {S : Type} {x : List Γ} (σ : Fin m ↪ Fin k)
    (d : Cfg k Γ S x) :
    embedEmitCfg σ d.workTapes d.workTapePos d.output (d.select σ) = d := by
  -- Unselected tapes: the public frame lemma at time `0`, for a trivial machine on `Unit`
  -- (the transport's tape fields do not depend on the state type; `S` may be empty).
  have hframe : ∀ j : Fin k, j ∉ Set.range σ →
      (embedEmitCfg σ d.workTapes d.workTapePos d.output (d.select σ)).workTapes j =
          d.workTapes j ∧
        (embedEmitCfg σ d.workTapes d.workTapePos d.output (d.select σ)).workTapePos j =
          d.workTapePos j := by
    intro j hj
    let M0 : MultiTapeTM m Γ Unit := ⟨(), fun _ _ _ => ⟨0, fun _ => (none, 0), none, none⟩⟩
    let c0 : Cfg m Γ Unit x :=
      ⟨none, d.inputPos, fun i => d.workTapes (σ i), fun i => d.workTapePos (σ i), []⟩
    have h := (embedEmitTM_frame σ M0 d.workTapes d.workTapePos d.output c0 0).1 j hj
    simp only [MultiTapeTM.runFrom_zero] at h
    exact h
  refine Cfg.ext rfl rfl ?_ ?_ ?_
  · funext j
    by_cases hj : j ∈ Set.range σ
    · obtain ⟨i, rfl⟩ := hj
      exact embedEmitCfg_selected_tape σ _ _ _ _ i
    · exact (hframe j hj).1
  · funext j
    by_cases hj : j ∈ Set.range σ
    · obtain ⟨i, rfl⟩ := hj
      exact embedEmitCfg_selected_pos σ _ _ _ _ i
    · exact (hframe j hj).2
  · simp [embedEmitCfg, Cfg.select]

/-- The forwarding embedding keeps an unselected tape and head as its frame: the export missing
from `Build/Embed.lean` beside `Turing.embedEmitCfg_selected_tape` and `_pos`. It moves to
`Build/Embed` with MIG-0b's layering split (backlog MIG-0).

**Proof sketch.** At time `0`, `Turing.embedEmitTM_frame` for a one-state machine says exactly
this; the transport's tape fields do not depend on the state type. -/
theorem _root_.Turing.embedEmitCfg_unselected {m : ℕ} {S : Type} {x : List Γ} (σ : Fin m ↪ Fin k)
    (tapes : Fin k → ℤ → Option Γ) (heads : Fin k → ℤ) (pre : List Γ) (c : Cfg m Γ S x)
    (j : Fin k) (hj : j ∉ Set.range σ) :
    (embedEmitCfg σ tapes heads pre c).workTapes j = tapes j ∧
      (embedEmitCfg σ tapes heads pre c).workTapePos j = heads j := by
  let M0 : MultiTapeTM m Γ Unit := ⟨(), fun _ _ _ => ⟨0, fun _ => (none, 0), none, none⟩⟩
  let c0 : Cfg m Γ Unit x := ⟨none, c.inputPos, c.workTapes, c.workTapePos, c.output⟩
  have h := (embedEmitTM_frame σ M0 tapes heads pre c0 0).1 j hj
  simp only [MultiTapeTM.runFrom_zero] at h
  exact h

/-- **Transport along the R1 embedding** (`Turing.embedEmitTM_runFrom`): the source contract
holds on the selected tapes; unselected tapes and heads are framed, and output is appended.
The precondition and the time are the source contract's at the selection `d.select σ`, and so
is the envelope of a selected head; an unselected head has the one-point envelope at its start.
The endpoint embeds the source endpoint into `d`'s tapes, heads and output.

The selection empties the source output, so `embed` transports **output-normalized**
preconditions only: a source precondition that inspects the output is tested on `[]` and is not
preserved (one asking for output `[true]` becomes false for every host). The intended
clean-call and tape-word instances fit; output-sensitive contracts would need a transport with
an explicit decomposition of the host output.

**Proof sketch.** By `Turing.embedEmitCfg_select`, `d` is the embedding of its own selection, so
`Turing.embedEmitTM_runFrom` makes the host run, at every time, the embedding of the source run
from the selection. The run is the embedded source run, and the exit and the cut are the
source's, since the selection and the embedding keep the state. For the envelope, a selected
head is the source head (`Turing.embedEmitCfg_selected_pos`), with the source bounds; an
unselected head stays at its start by the frame lemma `Turing.embedEmitTM_frame`, inside its
one-point interval. -/
noncomputable def embed {m : ℕ} (σ : Fin m ↪ Fin k) {S : Type} {M : MultiTapeTM m Γ S}
    {entry : S} {X : Set (Option S)} {ι : Type} {x : List Γ} (C : Contract M entry X ι x) :
    Contract (embedEmitTM σ M) entry X ι x where
  pre i d := C.pre i (d.select σ)
  time i d := C.time i (d.select σ)
  post i d := embedEmitCfg σ d.workTapes d.workTapePos d.output (C.post i (d.select σ))
  lo i d := Function.extend σ (C.lo i (d.select σ)) d.workTapePos
  hi i d := Function.extend σ (C.hi i (d.select σ)) d.workTapePos
  run i d hd hp := by
    have hr := embedEmitTM_runFrom σ M d.workTapes d.workTapePos d.output (d.select σ)
      (C.time i (d.select σ))
    rw [embedEmitCfg_select σ d] at hr
    rw [hr, C.run i _ hd hp]
  exit_mem i d hd hp := C.exit_mem i _ hd hp
  cut i d hd hp u hu := by
    have hr := embedEmitTM_runFrom σ M d.workTapes d.workTapePos d.output (d.select σ) u
    rw [embedEmitCfg_select σ d] at hr
    rw [hr]
    exact C.cut i _ hd hp u hu
  env i d hd hp u hu j := by
    have hr := embedEmitTM_runFrom σ M d.workTapes d.workTapePos d.output (d.select σ) u
    rw [embedEmitCfg_select σ d] at hr
    show ((embedEmitTM σ M).runFrom d u).workTapePos j ∈
      Finset.Icc (Function.extend σ (C.lo i (d.select σ)) d.workTapePos j)
        (Function.extend σ (C.hi i (d.select σ)) d.workTapePos j)
    rw [hr]
    by_cases hj : j ∈ Set.range σ
    · obtain ⟨a, rfl⟩ := hj
      rw [embedEmitCfg_selected_pos, σ.injective.extend_apply, σ.injective.extend_apply]
      exact C.env i _ hd hp u hu a
    · have hf := (embedEmitTM_frame σ M d.workTapes d.workTapePos d.output (d.select σ) u).1 j hj
      rw [embedEmitTM_runFrom] at hf
      have hne : ¬∃ a, σ a = j := fun ⟨a, ha⟩ => hj ⟨a, ha⟩
      rw [hf.2, Function.extend_apply' _ _ _ hne, Function.extend_apply' _ _ _ hne]
      exact Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩

end Compose

end Contract

/-- **R3 clear as a contract** (the fit test, from `Turing.clearTM_run_ofCfg`): the index is the
stored word `w`. Started in the sweep phase with `w`, delimited, at the head of tape `i`, the
routine reaches `done` in exactly `2|w| + 2` steps, and not earlier, with the cells
`[pos, pos + |w|)` of tape `i` blank and every other field unchanged; through the endpoint the
head of tape `i` stays in `[pos - 1, pos + |w|]` and every other head is fixed.

**Proof sketch.** Each field is the corresponding clause of `Turing.clearTM_run_ofCfg`; a fixed
head lies in its one-point interval. -/
def clearTM_contract (i : Fin k) (x : List Γ) :
    Contract (clearTM k i) SweepPhase.sweep {some SweepPhase.done} (List Γ) x where
  pre w d := ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
    d.workTapes i (d.workTapePos i + p) = FinTM.bufferTape w p
  time w _ := 2 * w.length + 2
  post w d :=
    { d with
      state := some SweepPhase.done
      workTapes := fun j q =>
        if j = i ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ) then none
        else d.workTapes j q }
  lo w d j := if j = i then d.workTapePos j - 1 else d.workTapePos j
  hi w d j := if j = i then d.workTapePos j + w.length else d.workTapePos j
  run w d hd hp := (clearTM_run_ofCfg i w d hd hp).1
  exit_mem _ _ _ _ := Set.mem_singleton _
  cut w d hd hp u hu h := (clearTM_run_ofCfg i w d hd hp).2.1 u hu (Set.mem_singleton_iff.mp h)
  env w d hd hp u hu j := by
    have h := (clearTM_run_ofCfg i w d hd hp).2.2 j u hu
    by_cases hj : j = i
    · subst hj
      simpa using h
    · simp only [hj, if_false] at h ⊢
      rw [h]
      exact Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩

end Turing

namespace Turing

variable {k : ℕ} {Γ : Type}

/-! ## Frames: the derived layer (user decision, 2026-10-12)

A contract's endpoint already states its frame (`{ d with … }`). The predicates below name the
frame for composition proofs: a *footprint* per tape, `Turing.Cfg.SameOutside`, its `.keep`
lemmas, and `Turing.Contract.Frames`. They are derived properties, not fields. The layer is
[AFM26]'s framing (`SameOn` and the `.keep` lemmas of `Lang/Regions.lean`), adapted from memory
cells to the cells of each work tape (design adaptation). -/

/-- `d'` agrees with `d` outside the footprint: every work-tape cell off `fp j` is unchanged.
This is an **endpoint relation on work-tape contents only**: it constrains neither the control
state, the heads, the input position nor the output, and says nothing about intermediate
times. A consumer that needs a cell kept at every time must keep the corresponding trajectory
fact. The two configurations may have different state types.

[AFM26], design adaptation: `SameOn` of `Lang/Regions.lean` (cells kept off a set, as in its
`SameOutside`), here per work tape. -/
def Cfg.SameOutside {S S' : Type} {x : List Γ} (fp : Fin k → Set ℤ) (d : Cfg k Γ S x)
    (d' : Cfg k Γ S' x) : Prop :=
  ∀ j q, q ∉ fp j → d'.workTapes j q = d.workTapes j q

/-- Footprints compose by union. -/
theorem Cfg.SameOutside.trans {S S' S'' : Type} {x : List Γ} {fp fp' : Fin k → Set ℤ}
    {d : Cfg k Γ S x} {d' : Cfg k Γ S' x} {d'' : Cfg k Γ S'' x} (h : Cfg.SameOutside fp d d')
    (h' : Cfg.SameOutside fp' d' d'') : Cfg.SameOutside (fun j => fp j ∪ fp' j) d d'' := by
  intro j q hq
  simp only [Set.mem_union, not_or] at hq
  rw [h' j q hq.2, h j q hq.1]

/-- Replacing the control state keeps the frame. -/
theorem Cfg.SameOutside.mapState {S S' S'' : Type} {x : List Γ} {fp : Fin k → Set ℤ}
    {d : Cfg k Γ S x} {d' : Cfg k Γ S' x} (h : Cfg.SameOutside fp d d') (f : S' → S'') :
    Cfg.SameOutside fp d (d'.mapState f) := fun j q hq => h j q hq

/-- **`.keep`, a stored word**: a delimited word lying outside the footprint survives. If `d`
holds `w` at offset `o` of tape `j`, its two blank delimiters included, and none of those cells
is in the footprint, then `d'` holds `w` there too. [AFM26], design adaptation: the `.keep`
lemmas of `Lang/Regions.lean`. -/
theorem Cfg.SameOutside.keep_word {S S' : Type} {x : List Γ} {fp : Fin k → Set ℤ}
    {d : Cfg k Γ S x} {d' : Cfg k Γ S' x} (h : Cfg.SameOutside fp d d') (j : Fin k) (o : ℤ)
    (w : List Γ) (hout : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → o + p ∉ fp j)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → d.workTapes j (o + p) = FinTM.bufferTape w p) :
    ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → d'.workTapes j (o + p) = FinTM.bufferTape w p :=
  fun p hp₁ hp₂ => (h j (o + p) (hout p hp₁ hp₂)).trans (hw p hp₁ hp₂)

/-- **`.keep`, a blank tape**: a tape with an empty footprint that was blank stays blank.
[AFM26], design adaptation: the `.keep` lemmas of `Lang/Regions.lean`. -/
theorem Cfg.SameOutside.keep_blank {S S' : Type} {x : List Γ} {fp : Fin k → Set ℤ}
    {d : Cfg k Γ S x} {d' : Cfg k Γ S' x} (h : Cfg.SameOutside fp d d') (j : Fin k)
    (hfp : fp j = ∅) (hb : ∀ q, d.workTapes j q = none) : ∀ q, d'.workTapes j q = none :=
  fun q => (h j q (by simp [hfp])).trans (hb q)

namespace Contract

variable {S : Type} {M : MultiTapeTM k Γ S} {entry : S} {exits : Set (Option S)} {ι : Type}
  {x : List Γ}

/-- A contract **frames** the footprint `fp` when every endpoint agrees with its start outside
it: for every index `i` and every admissible start `d`, `Turing.Cfg.SameOutside (fp i d)` holds
between `d` and `C.post i d`. [AFM26], design adaptation: a routine's `SameOn` promise for the
cells it leaves alone (`Lang/Regions.lean`). -/
def Frames (C : Contract M entry exits ι x) (fp : ι → Cfg k Γ S x → Fin k → Set ℤ) : Prop :=
  ∀ i d, d.state = some entry → C.pre i d → Cfg.SameOutside (fp i d) d (C.post i d)

/-- A contract frames `fp` exactly when, for every index `i` and every admissible start `d`,
every cell `q` of every work tape `j` outside `fp i d j` holds at the endpoint what it held at
the start. This is the definition unfolded, as a `@[simp]` lemma, so that `simp` and `rw` see
the footprint. -/
@[simp] theorem frames_iff (C : Contract M entry exits ι x)
    (fp : ι → Cfg k Γ S x → Fin k → Set ℤ) :
    C.Frames fp ↔ ∀ i d, d.state = some entry → C.pre i d →
      ∀ j q, q ∉ fp i d j → (C.post i d).workTapes j q = d.workTapes j q :=
  Iff.rfl

end Contract

/-- R3 clear frames the cleared word's cells on its tape, and nothing else: its footprint is
`[pos, pos + |w|)` on tape `i` and empty on every other tape.

**Proof sketch.** The endpoint blanks a cell only when the cell lies in the footprint; any other
cell takes the `else` branch of its definition, which is the start's cell. -/
theorem clearTM_contract_frames (i : Fin k) (x : List Γ) :
    (clearTM_contract i x).Frames fun w d j =>
      if j = i then Set.Ico (d.workTapePos j) (d.workTapePos j + w.length) else ∅ := by
  intro w d _ _ j q hq
  show (if j = i ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ) then none
      else d.workTapes j q) = d.workTapes j q
  rw [if_neg]
  rintro ⟨rfl, h₁, h₂⟩
  apply hq
  show q ∈ if j = j then Set.Ico (d.workTapePos j) (d.workTapePos j + w.length) else ∅
  rw [if_pos rfl]
  exact ⟨h₁, h₂⟩

/-! ## Returning contracts and the release adapter -/

/-- **A returning contract**: from every admissible start at `anchor`, the run first comes back
to `anchor` at a positive exact time. The endpoint is at the anchor, no strictly positive
earlier time is at the anchor (the cut starts at time `1`, since time `0` is at the anchor),
and through the endpoint every head stays in its interval. `Turing.ReturnContract.release`
turns it into a `Turing.Contract`.

The advancing writer (`Turing.writeAdvTM_run_ofCfg` in `Build/Scan`, anchor `0`, time
`|w₀| + 1`) genuinely returns to its anchor and has this shape. The install and emit calls
(`Turing.FinTM.exists_installCallTM`, `Turing.FinTM.exists_emitCallTM`, in `Build/Loop`) also
have positive cuts, but quantify separate `entry` and `exit` states that may coincide. With
arbitrary witnesses, split on `entry = exit`: when they are equal, use a `ReturnContract`; when
they differ, use an ordinary `Turing.Contract` with exits `{some exit}`, whose cut at time `0`
follows from `entry ≠ exit` and at positive times is the row's positive cut. Either way the
canonical `Cfg.ofWords` start goes into the precondition, and the time bound is kept. A round
that may instead end at a distinct escape is not a `ReturnContract`: it belongs to MIG-0b's
round layer. -/
structure ReturnContract {S : Type} (M : MultiTapeTM k Γ S) (anchor : S) (ι : Type)
    (x : List Γ) where
  /-- The precondition. -/
  pre : ι → Cfg k Γ S x → Prop
  /-- The exact, positive running time. -/
  time : ι → Cfg k Γ S x → ℕ
  /-- The endpoint, back at the anchor. -/
  post : ι → Cfg k Γ S x → Cfg k Γ S x
  /-- The lower ends of the head envelope. -/
  lo : ι → Cfg k Γ S x → Fin k → ℤ
  /-- The upper ends of the head envelope. -/
  hi : ι → Cfg k Γ S x → Fin k → ℤ
  pos : ∀ i d, d.state = some anchor → pre i d → 0 < time i d
  run : ∀ i d, d.state = some anchor → pre i d → M.runFrom d (time i d) = post i d
  exit_eq : ∀ i d, d.state = some anchor → pre i d → (post i d).state = some anchor
  cut : ∀ i d, d.state = some anchor → pre i d →
    ∀ u, 0 < u → u < time i d → (M.runFrom d u).state ≠ some anchor
  env : ∀ i d, d.state = some anchor → pre i d → ∀ u ≤ time i d, ∀ j,
    (M.runFrom d u).workTapePos j ∈ Finset.Icc (lo i d j) (hi i d j)

/-- The release start is the anchor-mapped start, re-tagged fresh. -/
private lemma release_start {S : Type} {anchor : S} {x : List Γ} {d : Cfg k Γ (Unit ⊕ S) x}
    (hd : d.state = some (Sum.inl ())) :
    (d.mapState fun _ => anchor).mapState (fun _ => (Sum.inl () : Unit ⊕ S)) = d :=
  Cfg.ext (by simp [Cfg.mapState, hd]) rfl rfl rfl rfl

/-- **The release adapter** (`Turing.seamReleaseTM_firstReturn`): a fresh start state executes the
anchor's first step, so the returning run becomes an ordinary contract whose cut includes time
`0`, at the same time and with no dispatch step. Its single exit is the right-tagged anchor, and
the envelopes are unchanged.

**Proof sketch.** The release start is the anchor-mapped start re-tagged fresh
(`release_start`). Fed the returning contract's positivity, run, return and positive cut,
`Turing.seamReleaseTM_firstReturn` gives the run to the right-tagged endpoint at the same time,
and the cut against the right-tagged anchor at every earlier time, time `0` included since the
fresh state is left-tagged. The exit is the endpoint's state, the anchor, right-tagged. For the
envelope, a head position up to the endpoint lies in the release machine's visited set, which
is the source's (`Turing.seamReleaseTM_visitedByTapeHead`); so it is the source head at some
time up to the endpoint, inside the source envelope. The visited-set theorem is used because
the pointwise lemma is private in `Build/Seam`; its export, `seamReleaseTM_runFrom_pos`, is
deferred to MIG-0b. -/
def ReturnContract.release {S : Type} {M : MultiTapeTM k Γ S} {anchor : S} {ι : Type}
    {x : List Γ} (C : ReturnContract M anchor ι x) :
    Contract (seamReleaseTM M anchor) (Sum.inl ()) {some (Sum.inr anchor)} ι x where
  pre i d := C.pre i (d.mapState fun _ => anchor)
  time i d := C.time i (d.mapState fun _ => anchor)
  post i d := (C.post i (d.mapState fun _ => anchor)).mapState Sum.inr
  lo i d := C.lo i (d.mapState fun _ => anchor)
  hi i d := C.hi i (d.mapState fun _ => anchor)
  run i d hd hp := by
    have hc : (d.mapState fun _ => anchor).state = some anchor := by simp [Cfg.mapState, hd]
    have H := seamReleaseTM_firstReturn M anchor hc (C.pos i _ hc hp) (C.run i _ hc hp)
      (C.exit_eq i _ hc hp) (C.cut i _ hc hp)
    rw [release_start hd] at H
    exact H.1
  exit_mem i d hd hp := by
    have hc : (d.mapState fun _ => anchor).state = some anchor := by simp [Cfg.mapState, hd]
    show Option.map Sum.inr (C.post i (d.mapState fun _ => anchor)).state ∈ _
    rw [C.exit_eq i _ hc hp]
    rfl
  cut i d hd hp u hu hmem := by
    have hc : (d.mapState fun _ => anchor).state = some anchor := by simp [Cfg.mapState, hd]
    have H := seamReleaseTM_firstReturn M anchor hc (C.pos i _ hc hp) (C.run i _ hc hp)
      (C.exit_eq i _ hc hp) (C.cut i _ hc hp)
    rw [release_start hd] at H
    exact H.2 u hu (Set.mem_singleton_iff.mp hmem)
  env i d hd hp u hu j := by
    have hc : (d.mapState fun _ => anchor).state = some anchor := by simp [Cfg.mapState, hd]
    change u ≤ C.time i (d.mapState fun _ => anchor) at hu
    have hv := seamReleaseTM_visitedByTapeHead M anchor hc (C.time i (d.mapState fun _ => anchor)) j
    rw [release_start hd] at hv
    have hmem : ((seamReleaseTM M anchor).runFrom d u).workTapePos j ∈
        (seamReleaseTM M anchor).visitedByTapeHead d (C.time i (d.mapState fun _ => anchor)) j :=
      Finset.mem_image.mpr ⟨u, Finset.mem_range.mpr (by omega), rfl⟩
    rw [hv] at hmem
    obtain ⟨s, hs, hseq⟩ := Finset.mem_image.mp hmem
    rw [← hseq]
    exact C.env i _ hc hp s (Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)) j

/-! ## The two-way branch -/

namespace Contract

/-- **Liveness**: a contract run is live strictly before its endpoint. A halt would persist to
the endpoint, putting `none` among the exits, which the cut excludes.

**Proof sketch.** Halting is absorbing, so a halt before the time would make the endpoint's
state `none`; `exit_mem` then puts `none` among the exits, against the cut at that time. -/
theorem live {S : Type} {M : MultiTapeTM k Γ S} {entry : S}
    {exits : Set (Option S)} {ι : Type} {x : List Γ} (C : Contract M entry exits ι x) (i : ι)
    (d : Cfg k Γ S x) (hd : d.state = some entry) (hp : C.pre i d) {u : ℕ}
    (hu : u < C.time i d) : (M.runFrom d u).state ≠ none := by
  intro h
  have h' := runFrom_state_none_mono h hu.le
  rw [C.run i d hd hp] at h'
  have hx := C.exit_mem i d hd hp
  rw [h'] at hx
  exact C.cut i d hd hp u hu (h ▸ hx)

/-- The two-way composed start is the doubly left-mapped first-phase start. -/
private lemma mapState_const_inl_inl {S₀ S₁ S₂ : Type} {x : List Γ} {e : S₀}
    {d : Cfg k Γ ((S₀ ⊕ S₁) ⊕ S₂) x} (hd : d.state = some (Sum.inl (Sum.inl e))) :
    ((d.mapState fun _ => e).mapState (Sum.inl : S₀ → S₀ ⊕ S₁)).mapState
      (Sum.inl : S₀ ⊕ S₁ → (S₀ ⊕ S₁) ⊕ S₂) = d :=
  Cfg.ext (by simp [Cfg.mapState, hd]) rfl rfl rfl rfl

/-- The two-way seam trajectory of a contract run: the doubly left-mapped first phase up to
its exit (live throughout), then, per exit, the matching continuation at every offset.

**Proof sketch.** The two-way seam nests two seams: the inner one dispatches `e₁` to the first
continuation, and the outer one dispatches the inner machine's `Sum.inl e₂` to the second.
`C₀`'s cut excludes both exits before its time. By the inner seam's left segment
(`Turing.seamCompTM_runFrom_left`), the inner machine therefore avoids `Sum.inl e₂` before that
time, so the outer seam's left segment, rewritten by the inner one, is the doubly tagged first
phase up to its time. It is live, since a halt would persist to the endpoint, which is at an
exit. The two continuations are the two halves of `Turing.seamCompTM₂_run_ofCfg`. -/
private lemma branch_traj {S₀ S₁ S₂ : Type} [DecidableEq S₀] [DecidableEq S₁]
    {M₀ : MultiTapeTM k Γ S₀} (M₁ : MultiTapeTM k Γ S₁) (M₂ : MultiTapeTM k Γ S₂)
    {entry₀ e₁ e₂ : S₀} (entry₁ : S₁) (entry₂ : S₂) {ι : Type} {x : List Γ} (he : e₁ ≠ e₂)
    (C₀ : Contract M₀ entry₀ {some e₁, some e₂} ι x) (i : ι)
    (d : Cfg k Γ ((S₀ ⊕ S₁) ⊕ S₂) x) (hd : d.state = some (Sum.inl (Sum.inl entry₀)))
    (hp : C₀.pre i (d.mapState fun _ => entry₀)) :
    (∀ u ≤ C₀.time i (d.mapState fun _ => entry₀),
      (seamCompTM₂ M₀ e₁ e₂ M₁ entry₁ M₂ entry₂).runFrom d u =
          ((M₀.runFrom (d.mapState fun _ => entry₀) u).mapState Sum.inl).mapState Sum.inl ∧
        (M₀.runFrom (d.mapState fun _ => entry₀) u).state ≠ none) ∧
    ((C₀.post i (d.mapState fun _ => entry₀)).state = some e₁ → ∀ v,
      (seamCompTM₂ M₀ e₁ e₂ M₁ entry₁ M₂ entry₂).runFrom d
          (C₀.time i (d.mapState fun _ => entry₀) + 1 + v) =
        ((M₁.runFrom ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁)
          v).mapState Sum.inr).mapState Sum.inl) ∧
    ((C₀.post i (d.mapState fun _ => entry₀)).state = some e₂ → ∀ v,
      (seamCompTM₂ M₀ e₁ e₂ M₁ entry₁ M₂ entry₂).runFrom d
          (C₀.time i (d.mapState fun _ => entry₀) + 1 + v) =
        (M₂.runFrom ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂)
          v).mapState Sum.inr) := by
  have hd' := mapState_const_inl_inl (S₁ := S₁) (S₂ := S₂) hd
  have hc : (d.mapState fun _ => entry₀).state = some entry₀ := by simp [Cfg.mapState, hd]
  have h0 := C₀.run i _ hc hp
  have hx := C₀.exit_mem i _ hc hp
  have hcut₁ : ∀ t < C₀.time i (d.mapState fun _ => entry₀),
      (M₀.runFrom (d.mapState fun _ => entry₀) t).state ≠ some e₁ :=
    fun t ht h => C₀.cut i _ hc hp t ht (by rw [h]; exact Set.mem_insert _ _)
  have hcut₂ : ∀ t < C₀.time i (d.mapState fun _ => entry₀),
      (M₀.runFrom (d.mapState fun _ => entry₀) t).state ≠ some e₂ :=
    fun t ht h => C₀.cut i _ hc hp t ht (by rw [h]; exact Set.mem_insert_of_mem _ rfl)
  have hcutO : ∀ t < C₀.time i (d.mapState fun _ => entry₀),
      ((seamCompTM M₀ e₁ M₁ entry₁).runFrom ((d.mapState fun _ => entry₀).mapState Sum.inl)
        t).state ≠ some (Sum.inl e₂) := by
    intro t ht h
    rw [seamCompTM_runFrom_left M₀ e₁ M₁ entry₁ hcut₁ t ht.le] at h
    exact hcut₂ t ht (by simpa [Cfg.mapState] using h)
  have H := seamCompTM₂_run_ofCfg M₀ e₁ e₂ he M₁ entry₁ M₂ entry₂ h0
    (fun t ht => ⟨hcut₁ t ht, hcut₂ t ht⟩)
  rw [hd'] at H
  refine ⟨fun u hu => ⟨?_, ?_⟩, H.1, H.2⟩
  · have h := seamCompTM_runFrom_left (seamCompTM M₀ e₁ M₁ entry₁) (Sum.inl e₂) M₂ entry₂
      hcutO u hu
    rw [seamCompTM_runFrom_left M₀ e₁ M₁ entry₁ hcut₁ u hu, hd'] at h
    exact h
  · intro h
    have h' := runFrom_state_none_mono h hu
    rw [h0] at h'
    rw [h'] at hx
    simp at hx

/-- **The two-way branch** (`Turing.seamCompTM₂_run_ofCfg`): the first phase ends at one of two
distinct live exits, and the seam dispatches, in one step, to the matching continuation, which
starts from the first phase's endpoint with its state replaced by its entry. Each
continuation's precondition is needed only when its exit is the one reached. The time, the
endpoint and the continuation part of the envelope hull are the selected continuation's.

This is the **binary case** of the routing: `Turing.Contract.seq` is the single-live-exit seam,
and the phase host (`Turing.Contract.inPhase`) handles an arbitrary set of live exits. Halted
endpoints of the two continuations share the untagged `none`, so a consumer that must recover
the branch from the final state needs live tagged exits or an explicit verdict.

**Proof sketch.** By the two-way trajectory (`branch_traj`), and by cases on the exit reached
(`e₁`, or else `e₂` by `exit_mem`). Up to the first phase's time the composite is the doubly
left-tagged first phase, live throughout, so it meets no exit of either continuation. At time
`t₀ + 1 + v` it is the selected continuation's run at `v`, tagged, which gives the run, the exit
and the envelope. For the cut at `v` below the continuation's time, a tagged exit of the
selected continuation is excluded by that continuation's cut, through injectivity of the tags;
an exit of the other continuation carries the other tag or is `none`, and the state is live by
`Turing.Contract.live`. -/
def branch {S₀ S₁ S₂ : Type} [DecidableEq S₀] [DecidableEq S₁] {M₀ : MultiTapeTM k Γ S₀}
    {M₁ : MultiTapeTM k Γ S₁} {M₂ : MultiTapeTM k Γ S₂} {entry₀ e₁ e₂ : S₀} {entry₁ : S₁}
    {entry₂ : S₂} {X₁ : Set (Option S₁)} {X₂ : Set (Option S₂)} {ι κ₁ κ₂ : Type} {x : List Γ}
    (he : e₁ ≠ e₂) (C₀ : Contract M₀ entry₀ {some e₁, some e₂} ι x)
    (C₁ : Contract M₁ entry₁ X₁ κ₁ x) (C₂ : Contract M₂ entry₂ X₂ κ₂ x) (l₁ : ι → κ₁)
    (l₂ : ι → κ₂)
    (h₁ : ∀ i d, d.state = some entry₀ → C₀.pre i d → (C₀.post i d).state = some e₁ →
      C₁.pre (l₁ i) ((C₀.post i d).mapState fun _ => entry₁))
    (h₂ : ∀ i d, d.state = some entry₀ → C₀.pre i d → (C₀.post i d).state = some e₂ →
      C₂.pre (l₂ i) ((C₀.post i d).mapState fun _ => entry₂)) :
    Contract (seamCompTM₂ M₀ e₁ e₂ M₁ entry₁ M₂ entry₂) (Sum.inl (Sum.inl entry₀))
      ((Option.map (Sum.inl ∘ Sum.inr) '' X₁) ∪ (Option.map Sum.inr '' X₂)) ι x where
  pre i d := C₀.pre i (d.mapState fun _ => entry₀)
  time i d :=
    C₀.time i (d.mapState fun _ => entry₀) + 1 +
      if (C₀.post i (d.mapState fun _ => entry₀)).state = some e₁ then
        C₁.time (l₁ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁)
      else C₂.time (l₂ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂)
  post i d :=
    if (C₀.post i (d.mapState fun _ => entry₀)).state = some e₁ then
      ((C₁.post (l₁ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁)).mapState
        Sum.inr).mapState Sum.inl
    else
      (C₂.post (l₂ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂)).mapState
        Sum.inr
  lo i d j := min (C₀.lo i (d.mapState fun _ => entry₀) j)
    (if (C₀.post i (d.mapState fun _ => entry₀)).state = some e₁ then
      C₁.lo (l₁ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁) j
    else C₂.lo (l₂ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂) j)
  hi i d j := max (C₀.hi i (d.mapState fun _ => entry₀) j)
    (if (C₀.post i (d.mapState fun _ => entry₀)).state = some e₁ then
      C₁.hi (l₁ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁) j
    else C₂.hi (l₂ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂) j)
  run i d hd hp := by
    have hc : (d.mapState fun _ => entry₀).state = some entry₀ := by simp [Cfg.mapState, hd]
    obtain ⟨-, H₁, H₂⟩ := branch_traj M₁ M₂ entry₁ entry₂ he C₀ i d hd hp
    by_cases h : (C₀.post i (d.mapState fun _ => entry₀)).state = some e₁
    · have hd₁ : ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁).state =
          some entry₁ := by rw [mapState_state, h]; rfl
      rw [if_pos h, if_pos h, H₁ h, C₁.run _ _ hd₁ (h₁ i _ hc hp h)]
    · have h' : (C₀.post i (d.mapState fun _ => entry₀)).state = some e₂ := by
        rcases C₀.exit_mem i _ hc hp with h'' | h''
        · exact absurd h'' h
        · exact h''
      have hd₂ : ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂).state =
          some entry₂ := by rw [mapState_state, h']; rfl
      rw [if_neg h, if_neg h, H₂ h', C₂.run _ _ hd₂ (h₂ i _ hc hp h')]
  exit_mem i d hd hp := by
    have hc : (d.mapState fun _ => entry₀).state = some entry₀ := by simp [Cfg.mapState, hd]
    by_cases h : (C₀.post i (d.mapState fun _ => entry₀)).state = some e₁
    · have hd₁ : ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁).state =
          some entry₁ := by rw [mapState_state, h]; rfl
      rw [if_pos h]
      refine Or.inl ⟨_, C₁.exit_mem _ _ hd₁ (h₁ i _ hc hp h), ?_⟩
      rw [mapState_state, mapState_state, Option.map_map]
    · have h' : (C₀.post i (d.mapState fun _ => entry₀)).state = some e₂ := by
        rcases C₀.exit_mem i _ hc hp with h'' | h''
        · exact absurd h'' h
        · exact h''
      have hd₂ : ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂).state =
          some entry₂ := by rw [mapState_state, h']; rfl
      rw [if_neg h]
      exact Or.inr ⟨_, C₂.exit_mem _ _ hd₂ (h₂ i _ hc hp h'), rfl⟩
  cut i d hd hp u hu := by
    have hc : (d.mapState fun _ => entry₀).state = some entry₀ := by simp [Cfg.mapState, hd]
    obtain ⟨HL, H₁, H₂⟩ := branch_traj M₁ M₂ entry₁ entry₂ he C₀ i d hd hp
    by_cases hle : u ≤ C₀.time i (d.mapState fun _ => entry₀)
    · obtain ⟨hrun, hlive⟩ := HL u hle
      rw [hrun]
      obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp hlive
      rintro (⟨q, -, heq⟩ | ⟨q, -, heq⟩) <;>
        rw [mapState_state, mapState_state, hs] at heq <;> cases q <;> simp at heq
    · obtain ⟨v, rfl⟩ : ∃ v, u = C₀.time i (d.mapState fun _ => entry₀) + 1 + v :=
        ⟨u - (C₀.time i (d.mapState fun _ => entry₀) + 1), by omega⟩
      by_cases h : (C₀.post i (d.mapState fun _ => entry₀)).state = some e₁
      · have hd₁ : ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁).state =
            some entry₁ := by rw [mapState_state, h]; rfl
        rw [if_pos h] at hu
        have hv : v < C₁.time (l₁ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState
            fun _ => entry₁) := by omega
        have hcut := C₁.cut _ _ hd₁ (h₁ i _ hc hp h) v hv
        have hlive := live C₁ _ _ hd₁ (h₁ i _ hc hp h) hv
        rw [H₁ h v]
        rintro (⟨q, hq, heq⟩ | ⟨q, -, heq⟩)
        · rw [mapState_state, mapState_state, Option.map_map] at heq
          exact hcut (Option.map_injective (Sum.inl_injective.comp Sum.inr_injective) heq ▸ hq)
        · obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp hlive
          rw [mapState_state, mapState_state, hs] at heq
          cases q <;> simp at heq
      · have h' : (C₀.post i (d.mapState fun _ => entry₀)).state = some e₂ := by
          rcases C₀.exit_mem i _ hc hp with h'' | h''
          · exact absurd h'' h
          · exact h''
        have hd₂ : ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂).state =
            some entry₂ := by rw [mapState_state, h']; rfl
        rw [if_neg h] at hu
        have hv : v < C₂.time (l₂ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState
            fun _ => entry₂) := by omega
        have hcut := C₂.cut _ _ hd₂ (h₂ i _ hc hp h') v hv
        have hlive := live C₂ _ _ hd₂ (h₂ i _ hc hp h') hv
        rw [H₂ h' v]
        rintro (⟨q, -, heq⟩ | ⟨q, hq, heq⟩)
        · obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp hlive
          rw [mapState_state, hs] at heq
          cases q <;> simp at heq
        · rw [mapState_state] at heq
          exact hcut (Option.map_injective Sum.inr_injective heq ▸ hq)
  env i d hd hp u hu j := by
    have hc : (d.mapState fun _ => entry₀).state = some entry₀ := by simp [Cfg.mapState, hd]
    obtain ⟨HL, H₁, H₂⟩ := branch_traj M₁ M₂ entry₁ entry₂ he C₀ i d hd hp
    by_cases hle : u ≤ C₀.time i (d.mapState fun _ => entry₀)
    · rw [(HL u hle).1]
      exact mem_hull_left (C₀.env i _ hc hp u hle j)
    · obtain ⟨v, rfl⟩ : ∃ v, u = C₀.time i (d.mapState fun _ => entry₀) + 1 + v :=
        ⟨u - (C₀.time i (d.mapState fun _ => entry₀) + 1), by omega⟩
      by_cases h : (C₀.post i (d.mapState fun _ => entry₀)).state = some e₁
      · have hd₁ : ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁).state =
            some entry₁ := by rw [mapState_state, h]; rfl
        rw [if_pos h] at hu
        rw [if_pos h, if_pos h, H₁ h v]
        exact mem_hull_right (C₁.env _ _ hd₁ (h₁ i _ hc hp h) v (by omega) j)
      · have h' : (C₀.post i (d.mapState fun _ => entry₀)).state = some e₂ := by
          rcases C₀.exit_mem i _ hc hp with h'' | h''
          · exact absurd h'' h
          · exact h''
        have hd₂ : ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂).state =
            some entry₂ := by rw [mapState_state, h']; rfl
        rw [if_neg h] at hu
        rw [if_neg h, if_neg h, H₂ h' v]
        exact mem_hull_right (C₂.env _ _ hd₂ (h₂ i _ hc hp h') v (by omega) j)

end Contract

end Turing
