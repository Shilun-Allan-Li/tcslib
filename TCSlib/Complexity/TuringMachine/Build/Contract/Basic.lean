/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Tactic.Linarith
import TCSlib.Complexity.TuringMachine.Simulation
import TCSlib.Complexity.TuringMachine.StateRenaming

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Framed contracts: the core

**Status: proved; landed with MIG-0b, whose gate closed at round 2 (2026-10-14)**
(`audits/mig0b-findings.md`, `audits/mig0b-r2-findings.md`; resolutions
`audits/mig0b-resolutions.md`, `audits/mig0b-r2-resolutions.md`).
This module is the core of the layering split (design §16a item 4). It holds the MIG-0a core,
moved here from `Build/Contract.lean` as landed on 2026-10-13 (after the MIG-0a gate closed at
round 2) with no statement changed, and MIG-0b's segment, round and joint-trajectory layers, the
sanity lemmas, state renaming and the macro-step lockstep. It imports only the machine core
(`Simulation`, `StateRenaming`) and `Mathlib.Tactic.Linarith`, so that `Build/Loop` and
`Build/CounterLoop` can import it. The seam, embedding and routine adapters are in
`Build/Contract/Seam`, `Build/Contract/Embed` and `Build/Contract/Catalog`, and the symbol lift in
`Build/Contract/Lift` (the facade `Build/Contract` lists them).

A *contract* packages what the library's framed rows state one by one (design §14 item 0,
§16): started at `entry` in a configuration satisfying the precondition, the machine reaches
the endpoint `post` after **exactly** `time` steps, has **not** reached an exit before, and
keeps every work head inside an interval. "Within `B`" and the space bound are derived. It is
the **first-exit** specialization; the layers below cover what it cannot: *segments*, whose
endpoint need not be a first exit; *rounds*, which return to their anchor or escape; and *joint
trajectories*, relations on the whole head vector.

## Design

* **Exact time and the cut are fields** (§16). The cut includes time `0`, as in about 45 of the
  library's rows. A row that returns to its own anchor, so that its cut starts at time `1` (the
  advancing writer `Turing.writeAdvTM_run_ofCfg`), is a `Turing.ReturnContract`, turned into a
  contract by the release adapter (`Turing.ReturnContract.release` in `Build/Contract/Seam`,
  over `Turing.seamReleaseTM`). The install and emit calls (`Turing.FinTM.exists_installCallTM`,
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
* **Segments** (MIG-0b; `Turing.Segment`): fixed-length runs, possibly of length zero, between
  two actual configurations, avoiding a forbidden set strictly before the end, with a relation on
  the whole head vector through the end (`CfgRecord`'s `RecordRun`, `SingleTape`'s `DGSpan`,
  `EmitIterEmbed`'s `SafeRun`, `CounterLoop`'s `counterSpan`). `Turing.SafeSegment` also keeps
  the endpoint off the set (`Primitives`' `splitSafe`).
* **Rounds** (MIG-0b; `Turing.Round`, `Turing.RoundContract`): positive runs from an anchor that
  end at the anchor or in an escape set, live and off both strictly in between (the find round
  of `RecordTable`, the counter loop's body interface).
* **Joint trajectories** (MIG-0b; `Turing.Contract.Traj`): a relation on the head vector at
  every time through the endpoint, derived like `Turing.Contract.Frames`.
* **Universes:** alphabet, states and index in `Type`, the universe of `FinTM`, `phaseHostTM`
  and `counterLoopTMVia` (backlog UNIV-1 folds in here).

## Main definitions

* `Turing.Contract`: the structure; `Turing.Contract.Positive`.
* `Turing.Contract.trans`: first-exit sequencing on one machine, with no dispatch step.
* `Turing.Cfg.SameOutside`, `Turing.Contract.Frames`: the derived frame layer.
* `Turing.ReturnContract`: returning modules.
* `Turing.HeadBox`, `Turing.Segment`, `Turing.SafeSegment`, `Turing.Contract.ofSegment`: the
  segment layer and its bridge to contracts.
* `Turing.roundStop`, `Turing.Round`, `Turing.roundOrbit`, `Turing.RoundContract` (with
  `returning` and `escaping`), `Turing.ReturnContract.toRound`, `Turing.RoundContract.hullLo`
  and `hullHi`: the round layer.
* `Turing.Contract.Traj`: the joint-trajectory layer.
* `Turing.Contract.mapState`: state renaming along an embedding.
* `Turing.Lockstep`, `Turing.Contract.lockstep`: the macro-step lockstep and its transport.

## Main results

* `Turing.Contract.within`, `Turing.Contract.spaceUsedByTape_le`: the derived forms.
* `Turing.Contract.live`: a contract run is live before its endpoint.
* `Turing.Cfg.SameOutside.keep_word`, `Turing.Cfg.SameOutside.keep_blank`: frame preservation.
* `Turing.Segment.trans`, `Turing.Segment.live`, `Turing.Segment.time_eq`,
  `Turing.SafeSegment.trans`, `Turing.Contract.segment`: segment concatenation, liveness,
  uniqueness of first exits, and the contract bridge.
* `Turing.Round.iterate`, `Turing.RoundContract.orbit_round`: round iteration along an orbit.
* `Turing.Contract.Traj.trans`, `Turing.Contract.Frames.trans`: preservation by `trans`.
* `Turing.Contract.time_eq_zero_iff`, `Turing.Contract.trans_positive`: sanity lemmas.
* `Turing.Contract.lockstep_admissible`: the target entry compatible with the encoding.
* `Turing.Contract.trans_pre`, `_time`, `_post`, `_lo`, `_hi` — the specification API
  (user, 2026-10-16): the fields of a sequenced contract as equations, generated by
  `simps` without the `simp` attribute, so that consumers never unfold the definition.

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
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Claim 1.5, p. 16: the alphabet-reduction simulation, the
  model case of `Turing.Lockstep`.)
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

/-- **First-exit sequencing on one machine**: run `C₁` to its single exit `e₂`, then `C₂` from
there. Times add with no dispatch step; the envelopes take the pointwise hull. `C₂`'s
precondition is needed only at `C₁`'s actual endpoint (`hlink`), for the linked index. `hX` says
that `C₁` does not pass through an exit of `C₂` before its own exit; it cannot be dropped, since
`C₁`'s cut excludes only `e₂`. This is not a general `RecordRun` concatenation: a segment whose
endpoint need not be a first exit belongs to the segment layer (`Turing.Segment.trans`).

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
    · exact Finset.Icc_subset_Icc (min_le_left _ _) (le_max_left _ _) (C₁.env i d hd hp u h j)
    · obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le (le_of_lt (not_le.mp h))
      rw [MultiTapeTM.runFrom_add, C₁.run i d hd hp]
      exact Finset.Icc_subset_Icc (min_le_right _ _) (le_max_right _ _)
        (C₂.env _ _ hx (hlink i d hd hp) v (by omega) j)

/-! The specification API (user, 2026-10-16): `Turing.Contract.trans`'s data fields as
equations, without the `simp` attribute. -/
attribute [simps (config := { isSimp := false }) pre time post lo hi] trans

/-- **Liveness**: a contract run is live strictly before its endpoint. A halt would persist to
the endpoint, putting `none` among the exits, which the cut excludes.

**Proof sketch.** Halting is absorbing, so a halt before the time would make the endpoint's
state `none`; `exit_mem` then puts `none` among the exits, against the cut at that time. -/
theorem live {S : Type} {M : MultiTapeTM k Γ S} {entry : S}
    {exits : Set (Option S)} {ι : Type} {x : List Γ} (C : Contract M entry exits ι x) (i : ι)
    (d : Cfg k Γ S x) (hd : d.state = some entry) (hp : C.pre i d) {u : ℕ}
    (hu : u < C.time i d) : (M.runFrom d u).state ≠ none := by
  intro h
  have hend : (M.runFrom d (C.time i d)).state ≠ none := by
    intro h'
    have hx := C.exit_mem i d hd hp
    rw [← C.run i d hd hp, h'] at hx
    exact C.cut i d hd hp u hu (h ▸ hx)
  exact MultiTapeTM.runFrom_state_ne_none_of_le M d _ hend u hu.le h

end Contract

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

/-! ## Returning contracts

Their release adapter is in `Build/Contract/Seam`. -/

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

/-! ## The segment layer (design §16a, MIG-0b item 1)

A *segment* is a run of a fixed length, possibly zero, between two actual configurations (the
configuration seam), that avoids a forbidden set of states before its end, with a relation on the
whole head vector at every time up to and including its end: `CfgRecord`'s `RecordRun` (its
verdict pair forbidden, a radius about a base), `EmitIterEmbed`'s `SafeRun` (one avoided state),
`SingleTape`'s `DGSpan` (nothing forbidden, an interval on one tape) and `CounterLoop`'s
`counterSpan` (both exits forbidden, the counter head's interval and a relation on the body heads,
with a genuine zero-time case in `counter_rounds`). The relation is the **joint-trajectory layer
for general segments**: it constrains the whole head vector, so a shared witness for all heads
(the counter loop's round and offset) survives concatenation. Its endpoint need not be a first
visit of anything: the MIG-0a auditor's idling machine (round 1, counterexample 4) gives a
length-2 segment from `a` to `a`. A segment whose endpoint lies in its forbidden set is a first
exit, and then it is a contract (`Turing.Contract.ofSegment`).

An **endpoint-inclusive** segment (`Turing.SafeSegment`) also keeps its endpoint off the forbidden
set: `Primitives`' `splitSafe` and `Catalog`'s `f2_splitSafe`, whose phase traces avoid the anchor
at every time through the endpoint. Such a segment is never a first exit (MIG-0a gate, round 2):
a positive stationary run away from the anchor is one, but no first-exit contract of that
duration exists. -/

/-- The **interval box** `∏ⱼ [lo j, hi j]`, as a predicate on head vectors: the per-tape
envelope of `Turing.Contract`, seen as one relation on the whole head vector. -/
def HeadBox (lo hi : Fin k → ℤ) (p : Fin k → ℤ) : Prop :=
  ∀ j, p j ∈ Finset.Icc (lo j) (hi j)

/-- **A segment**: the run of `M` from `a` reaches `b` after exactly `t` steps, no state at a
time before `t` lies in the forbidden set `F`, and the head vector satisfies `P` at every time up
to `t`. Nothing is said about the endpoint's state. -/
def Segment {S : Type} {x : List Γ} (M : MultiTapeTM k Γ S) (F : Set (Option S))
    (P : (Fin k → ℤ) → Prop) (a b : Cfg k Γ S x) (t : ℕ) : Prop :=
  M.runFrom a t = b ∧ (∀ u < t, (M.runFrom a u).state ∉ F) ∧
    ∀ u ≤ t, P (M.runFrom a u).workTapePos

namespace Segment

variable {S : Type} {x : List Γ} {M : MultiTapeTM k Γ S} {F : Set (Option S)}
  {P : (Fin k → ℤ) → Prop}

/-- The empty segment: zero steps, with the start's head vector satisfying the relation. -/
theorem zero {a : Cfg k Γ S x} (h : P a.workTapePos) : Segment M F P a a 0 :=
  ⟨rfl, fun _ hu => absurd hu (Nat.not_lt_zero _), fun u hu => by
    obtain rfl : u = 0 := Nat.le_zero.mp hu
    exact h⟩

/-- A single step from a start outside the forbidden set. -/
theorem one {a : Cfg k Γ S x} (ha : a.state ∉ F) (h₀ : P a.workTapePos)
    (h₁ : P (M.step a).workTapePos) : Segment M F P a (M.step a) 1 := by
  refine ⟨rfl, fun u hu => ?_, fun u hu => ?_⟩
  · obtain rfl : u = 0 := by omega
    exact ha
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hu with rfl | rfl
    · exact h₀
    · exact h₁

/-- **Same-machine concatenation** (the `recordRun_trans` pattern): segments sharing the forbidden
set and the relation concatenate, with lengths adding and **no dispatch step**.

**Proof sketch.** Split a time at the first length `t`. Before it, use the first segment; after
it, the run is the second segment's from `b` (`Turing.MultiTapeTM.runFrom_add`). -/
theorem trans {a b c : Cfg k Γ S x} {t v : ℕ} (h : Segment M F P a b t)
    (g : Segment M F P b c v) : Segment M F P a c (t + v) := by
  refine ⟨by rw [MultiTapeTM.runFrom_add, h.1, g.1], ?_, ?_⟩
  · intro u hu
    by_cases hut : u < t
    · exact h.2.1 u hut
    · have he : u = t + (u - t) := by omega
      rw [he, MultiTapeTM.runFrom_add, h.1]
      exact g.2.1 _ (by omega)
  · intro u hu
    by_cases hut : u ≤ t
    · exact h.2.2 u hut
    · have he : u = t + (u - t) := by omega
      rw [he, MultiTapeTM.runFrom_add, h.1]
      exact g.2.2 _ (by omega)

/-- Weakening: a smaller forbidden set and a weaker relation. -/
theorem mono {F' : Set (Option S)} {P' : (Fin k → ℤ) → Prop} {a b : Cfg k Γ S x} {t : ℕ}
    (h : Segment M F P a b t) (hF : F' ⊆ F) (hP : ∀ p, P p → P' p) : Segment M F' P' a b t :=
  ⟨h.1, fun u hu hm => h.2.1 u hu (hF hm), fun u hu => hP _ (h.2.2 u hu)⟩

/-- Two relations along one segment hold jointly. -/
theorem and {Q : (Fin k → ℤ) → Prop} {a b : Cfg k Γ S x} {t : ℕ} (h : Segment M F P a b t)
    (g : Segment M F Q a b t) : Segment M F (fun p => P p ∧ Q p) a b t :=
  ⟨h.1, h.2.1, fun u hu => ⟨h.2.2 u hu, g.2.2 u hu⟩⟩

/-- An initial part of a segment is a segment. -/
theorem take {a b : Cfg k Γ S x} {t u : ℕ} (h : Segment M F P a b t) (hu : u ≤ t) :
    Segment M F P a (M.runFrom a u) u :=
  ⟨rfl, fun v hv => h.2.1 v (by omega), fun v hv => h.2.2 v (by omega)⟩

/-- A final part of a segment is a segment.

**Proof sketch.** Shift every time by `u` (`Turing.MultiTapeTM.runFrom_add`). -/
theorem drop {a b : Cfg k Γ S x} {t u : ℕ} (h : Segment M F P a b t) (hu : u ≤ t) :
    Segment M F P (M.runFrom a u) b (t - u) := by
  refine ⟨?_, fun v hv => ?_, fun v hv => ?_⟩
  · rw [← MultiTapeTM.runFrom_add, Nat.add_sub_cancel' hu]
    exact h.1
  · rw [← MultiTapeTM.runFrom_add]
    exact h.2.1 _ (by omega)
  · rw [← MultiTapeTM.runFrom_add]
    exact h.2.2 _ (by omega)

/-- **First exits are unique**: two segments from one start, each ending in its forbidden set,
have the same length. This is what a proof clock (`RecordTable`'s `rt_findClock`) needs.

**Proof sketch.** If one were shorter, its endpoint, which is in the forbidden set, would be a
state of the longer one before its end. -/
theorem time_eq {a b b' : Cfg k Γ S x} {t t' : ℕ} {P' : (Fin k → ℤ) → Prop}
    (h : Segment M F P a b t) (hb : b.state ∈ F) (h' : Segment M F P' a b' t')
    (hb' : b'.state ∈ F) : t = t' := by
  rcases Nat.lt_trichotomy t t' with hlt | heq | hgt
  · exact absurd (h.1 ▸ hb) (h'.2.1 t hlt)
  · exact heq
  · exact absurd (h'.1 ▸ hb') (h.2.1 t' hgt)

/-- Prepending one step from outside the forbidden set (the `SafeRun.cons` pattern). -/
theorem cons {a a₁ b : Cfg k Γ S x} {t : ℕ} (hstep : M.step a = a₁) (ha : a.state ∉ F)
    (h₀ : P a.workTapePos) (h : Segment M F P a₁ b t) : Segment M F P a b (1 + t) := by
  have h₁ : P a₁.workTapePos := by
    have := h.2.2 0 (Nat.zero_le _)
    rwa [MultiTapeTM.runFrom_zero] at this
  have hs : Segment M F P a a₁ 1 := by
    have h1 := one (M := M) ha h₀ (by rw [hstep]; exact h₁)
    rwa [hstep] at h1
  exact hs.trans h

/-- **Liveness**: a segment whose endpoint is live is live throughout, so `none` can be added to
its forbidden set. Halting is absorbing.

**Proof sketch.** A halt before the end would persist to the endpoint
(`Turing.MultiTapeTM.runFrom_state_ne_none_of_le`). -/
theorem live {a b : Cfg k Γ S x} {t : ℕ} (h : Segment M F P a b t) (hb : b.state ≠ none) :
    Segment M (insert none F) P a b t := by
  refine ⟨h.1, fun u hu hm => ?_, h.2.2⟩
  rcases hm with hm | hm
  · exact MultiTapeTM.runFrom_state_ne_none_of_le M a t (by rw [h.1]; exact hb) u hu.le hm
  · exact h.2.1 u hu hm

end Segment

/-- **An endpoint-inclusive segment**: a segment whose endpoint is also off the forbidden set, so
that no time up to and including the end is in it. This is `splitSafe`'s shape; it is never a
first exit. -/
def SafeSegment {S : Type} {x : List Γ} (M : MultiTapeTM k Γ S) (F : Set (Option S))
    (P : (Fin k → ℤ) → Prop) (a b : Cfg k Γ S x) (t : ℕ) : Prop :=
  Segment M F P a b t ∧ b.state ∉ F

/-- An endpoint-inclusive segment avoids the forbidden set at every time through its end.

**Proof sketch.** Times before the end are the segment's cut; the end is the endpoint. -/
theorem safeSegment_iff {S : Type} {x : List Γ} {M : MultiTapeTM k Γ S} {F : Set (Option S)}
    {P : (Fin k → ℤ) → Prop} {a b : Cfg k Γ S x} {t : ℕ} :
    SafeSegment M F P a b t ↔ M.runFrom a t = b ∧ (∀ u ≤ t, (M.runFrom a u).state ∉ F) ∧
      ∀ u ≤ t, P (M.runFrom a u).workTapePos := by
  constructor
  · rintro ⟨⟨hr, hc, hp⟩, hb⟩
    refine ⟨hr, fun u hu => ?_, hp⟩
    rcases Nat.lt_or_ge u t with h | h
    · exact hc u h
    · obtain rfl : u = t := le_antisymm hu h
      rw [hr]
      exact hb
  · rintro ⟨hr, hc, hp⟩
    refine ⟨⟨hr, fun u hu => hc u hu.le, hp⟩, ?_⟩
    rw [← hr]
    exact hc t le_rfl

namespace SafeSegment

variable {S : Type} {x : List Γ} {M : MultiTapeTM k Γ S} {F : Set (Option S)}
  {P : (Fin k → ℤ) → Prop}

/-- The empty endpoint-inclusive segment, at a start off the forbidden set. -/
theorem zero {a : Cfg k Γ S x} (ha : a.state ∉ F) (h : P a.workTapePos) :
    SafeSegment M F P a a 0 :=
  ⟨Segment.zero h, ha⟩

/-- Endpoint-inclusive segments concatenate at their configuration seam (`splitSafe_add`). -/
theorem trans {a b c : Cfg k Γ S x} {t v : ℕ} (h : SafeSegment M F P a b t)
    (g : SafeSegment M F P b c v) : SafeSegment M F P a c (t + v) :=
  ⟨h.1.trans g.1, g.2⟩

/-- Weakening an endpoint-inclusive segment. -/
theorem mono {F' : Set (Option S)} {P' : (Fin k → ℤ) → Prop} {a b : Cfg k Γ S x} {t : ℕ}
    (h : SafeSegment M F P a b t) (hF : F' ⊆ F) (hP : ∀ p, P p → P' p) :
    SafeSegment M F' P' a b t :=
  ⟨h.1.mono hF hP, fun hm => h.2 (hF hm)⟩

/-- **Never a first exit**: the endpoint of an endpoint-inclusive segment is off the forbidden
set, so a contract with those exits cannot end there. -/
theorem endpoint_not_mem {a b : Cfg k Γ S x} {t : ℕ} (h : SafeSegment M F P a b t) :
    b.state ∉ F :=
  h.2

end SafeSegment

namespace Contract

variable {S : Type} {M : MultiTapeTM k Γ S} {entry : S} {exits : Set (Option S)} {ι : Type}
  {x : List Γ}

/-- **Contract to segment**: every admissible run of a contract is a segment that avoids the
exits, ends at the endpoint, and keeps the heads in the envelope box. -/
theorem segment (C : Contract M entry exits ι x) (i : ι) (d : Cfg k Γ S x)
    (hd : d.state = some entry) (hp : C.pre i d) :
    Segment M exits (HeadBox (C.lo i d) (C.hi i d)) d (C.post i d) (C.time i d) :=
  ⟨C.run i d hd hp, C.cut i d hd hp, fun u hu j => C.env i d hd hp u hu j⟩

/-- **Segment to contract** (the bridge when the endpoint is a first exit): a family of segments
that avoid `exits` and end in `exits`, with an interval box, is a contract. A segment avoiding a
larger forbidden set is first weakened by `Turing.Segment.mono`. -/
def ofSegment (pre : ι → Cfg k Γ S x → Prop) (time : ι → Cfg k Γ S x → ℕ)
    (post : ι → Cfg k Γ S x → Cfg k Γ S x) (lo hi : ι → Cfg k Γ S x → Fin k → ℤ)
    (seg : ∀ i d, d.state = some entry → pre i d →
      Segment M exits (HeadBox (lo i d) (hi i d)) d (post i d) (time i d))
    (exit_mem : ∀ i d, d.state = some entry → pre i d → (post i d).state ∈ exits) :
    Contract M entry exits ι x where
  pre := pre
  time := time
  post := post
  lo := lo
  hi := hi
  run i d hd hp := (seg i d hd hp).1
  exit_mem := exit_mem
  cut i d hd hp := (seg i d hd hp).2.1
  env i d hd hp u hu j := (seg i d hd hp).2.2 u hu j

/-- **The time-derived envelope of a contract**: every head stays within `time` cells of its
start, whatever the contract's own envelope says. -/
theorem time_envelope (C : Contract M entry exits ι x) (i : ι) (d : Cfg k Γ S x) (u : ℕ)
    (hu : u ≤ C.time i d) (j : Fin k) :
    (M.runFrom d u).workTapePos j ∈
      Finset.Icc (d.workTapePos j - C.time i d) (d.workTapePos j + C.time i d) := by
  have h := MultiTapeTM.workTapePos_runFrom_mem_Icc M d u j
  rw [Finset.mem_Icc] at h ⊢
  have hu' : (u : ℤ) ≤ C.time i d := by exact_mod_cast hu
  constructor <;> omega

end Contract

/-! ## The round layer (design §16a, MIG-0b item 2)

A *round* starts at its anchor `a` and ends, after a positive exact time, back at `a` or in an
escape set `E`; at every strictly intermediate time it is live and visits neither `a` nor `E`.
This is the shape of `RecordTable`'s `rt_find_round_entry` and of the counter loop's **body
interface** (the round hypothesis of `counterLoopTMVia_run_done`, `_run_escape`): a
`Turing.Contract` fails its time-zero cut there, and a `Turing.ReturnContract` excludes the escape
(MIG-0a gate, round 1, counterexample 5). The counter loop's **host** runs are not rounds: they,
and the private `counterSpan` that describes them, are segments with a joint relation, with a
genuine zero-time case (MIG-0a gate, round 2). The counter loop over round contracts is in
`Build/CounterLoop`. -/

/-- The states a round's interior avoids: halting, the anchor and the escapes. -/
def roundStop {S : Type} (a : S) (E : Set (Option S)) : Set (Option S) :=
  insert none (insert (some a) E)

/-- Outside the round stop set means live, off the anchor and off the escapes: the form in which
the rows state their round cuts. -/
theorem not_mem_roundStop {S : Type} {a : S} {E : Set (Option S)} {q : Option S} :
    q ∉ roundStop a E ↔ ∃ s, q = some s ∧ s ≠ a ∧ some s ∉ E := by
  constructor
  · intro h
    cases q with
    | none => exact absurd (Set.mem_insert _ _) h
    | some s =>
      refine ⟨s, rfl, fun hs => h ?_, fun hs => h ?_⟩
      · rw [hs]
        exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hs)
  · rintro ⟨s, rfl, hsa, hsE⟩ h
    rcases h with h | h | h
    · exact Option.some_ne_none s h
    · exact hsa (Option.some.inj h)
    · exact hsE h

/-- **A round** of `M` from `c`, with anchor `a` and escape set `E`: `c` is at the anchor, the
exact time `t` is positive, the run reaches `c'` at `t`, `c'` is at the anchor or in `E`, every
strictly intermediate state is live and off the anchor and `E`, and the head vector satisfies
`P` at every time up to `t`. -/
def Round {S : Type} {x : List Γ} (M : MultiTapeTM k Γ S) (a : S) (E : Set (Option S))
    (P : (Fin k → ℤ) → Prop) (c c' : Cfg k Γ S x) (t : ℕ) : Prop :=
  c.state = some a ∧ 0 < t ∧ M.runFrom c t = c' ∧ c'.state ∈ insert (some a) E ∧
    (∀ u, 0 < u → u < t → (M.runFrom c u).state ∉ roundStop a E) ∧
    ∀ u ≤ t, P (M.runFrom c u).workTapePos

namespace Round

variable {S : Type} {x : List Γ} {M : MultiTapeTM k Γ S} {a : S} {E : Set (Option S)}
  {P : (Fin k → ℤ) → Prop}

/-- **A round avoiding its escapes is a segment against them**, whatever its endpoint: at time
`0` it is at the anchor, which is no escape, and later it avoids the stop set. When the endpoint
is an escape, this segment is a first exit. -/
theorem segment {c c' : Cfg k Γ S x} {t : ℕ} (h : Round M a E P c c' t) (ha : some a ∉ E) :
    Segment M E P c c' t := by
  obtain ⟨hc, -, hrun, -, hcut, henv⟩ := h
  refine ⟨hrun, fun u hu hm => ?_, henv⟩
  rcases Nat.eq_zero_or_pos u with rfl | hpos
  · rw [MultiTapeTM.runFrom_zero, hc] at hm
    exact ha hm
  · exact hcut u hpos hu (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hm))

/-- The round cut in the rows' form: every intermediate state is `some s` with `s` off the anchor
and the escapes. -/
theorem cut_some {c c' : Cfg k Γ S x} {t : ℕ} (h : Round M a E P c c' t) :
    ∀ u, 0 < u → u < t → ∃ s, (M.runFrom c u).state = some s ∧ s ≠ a ∧ some s ∉ E :=
  fun u hu hut => not_mem_roundStop.mp (h.2.2.2.2.1 u hu hut)

/-- **Rounds from the rows' form** (the fit for `rt_find_round_entry` and the counter loop): a
positive-time run from the anchor whose intermediate states are live and off both the anchor `a`
and a single escape `e`, ending at one of them, is a round with escape set `{some e}`.

**Proof sketch.** Rewrite the cut by `Turing.not_mem_roundStop`; the endpoint is in
`{some a, some e}`; the relation is trivial. -/
theorem of_cut {e : S} {c : Cfg k Γ S x} {t : ℕ} (hc : c.state = some a) (ht : 0 < t)
    (hcut : ∀ u, 0 < u → u < t → ∃ s, (M.runFrom c u).state = some s ∧ s ≠ a ∧ s ≠ e)
    (hend : (M.runFrom c t).state = some a ∨ (M.runFrom c t).state = some e) :
    Round M a {some e} (fun _ => True) c (M.runFrom c t) t := by
  refine ⟨hc, ht, rfl, ?_, fun u hu hut => ?_, fun _ _ => trivial⟩
  · rcases hend with h | h
    · rw [h]
      exact Set.mem_insert _ _
    · rw [h]
      exact Set.mem_insert_of_mem _ rfl
  · obtain ⟨s, hs, hsa, hse⟩ := hcut u hu hut
    exact not_mem_roundStop.mpr ⟨s, hs, hsa, fun h => hse (Option.some.inj h)⟩

/-- A round's relation can be replaced by the time-derived box about its start. -/
theorem time_box {c c' : Cfg k Γ S x} {t : ℕ} (h : Round M a E P c c' t) :
    Round M a E (HeadBox (fun j => c.workTapePos j - t) (fun j => c.workTapePos j + t)) c c' t := by
  obtain ⟨hc, ht, hrun, hend, hcut, -⟩ := h
  refine ⟨hc, ht, hrun, hend, hcut, fun u hu j => ?_⟩
  have h := MultiTapeTM.workTapePos_runFrom_mem_Icc M c u j
  simp only [Finset.mem_Icc] at h ⊢
  have hu' : (u : ℤ) ≤ t := by exact_mod_cast hu
  constructor <;> omega

end Round

/-- **The round orbit**: the round-start configurations when each round from `c` lasts `τ c`
steps, stated in the core so that round iteration needs no counter. `CounterLoop`'s
`Turing.counterLoopOrbit` is an abbreviation of it. -/
def roundOrbit {S : Type} {x : List Γ} (M : MultiTapeTM k Γ S) (τ : Cfg k Γ S x → ℕ)
    (c : Cfg k Γ S x) (r : ℕ) : Cfg k Γ S x :=
  (fun c => M.runFrom c (τ c))^[r] c

/-- The next round starts where the current one ends. -/
theorem roundOrbit_succ {S : Type} {x : List Γ} (M : MultiTapeTM k Γ S) (τ : Cfg k Γ S x → ℕ)
    (c : Cfg k Γ S x) (r : ℕ) :
    roundOrbit M τ c (r + 1) = M.runFrom (roundOrbit M τ c r) (τ (roundOrbit M τ c r)) :=
  Function.iterate_succ_apply' _ _ _

/-- **Round iteration on one machine** (the counter loop's composition, without the counter):
if the first `n` rounds of the orbit are rounds, each lasting `τ` of its start, then the whole
orbit prefix is one segment against the escapes, of length the sum of the round times. When the
last round ends in an escape, the segment is a first exit (`Turing.Contract.ofSegment`).

**Proof sketch.** Induction on `n`, appending each round as a segment (`Turing.Round.segment`)
by `Turing.Segment.trans`. -/
theorem Round.iterate {S : Type} {x : List Γ} {M : MultiTapeTM k Γ S} {a : S}
    {E : Set (Option S)} {P : (Fin k → ℤ) → Prop} (τ : Cfg k Γ S x → ℕ) (c : Cfg k Γ S x)
    (ha : some a ∉ E) (h0 : P c.workTapePos) (n : ℕ)
    (hround : ∀ r < n, Round M a E P (roundOrbit M τ c r) (roundOrbit M τ c (r + 1))
      (τ (roundOrbit M τ c r))) :
    Segment M E P c (roundOrbit M τ c n) (∑ r ∈ Finset.range n, τ (roundOrbit M τ c r)) := by
  induction n with
  | zero => exact Segment.zero h0
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact (ih fun r hr => hround r (by omega)).trans ((hround n (by omega)).segment ha)

/-- **A round contract** (design §16a item 2): from every admissible start at `anchor`, the run
ends after a positive exact time back at the anchor or in the escape set; strictly in between it
is live and avoids both; and every head stays in its interval. A `Turing.ReturnContract` is the
case without escapes (`Turing.ReturnContract.toRound`). -/
structure RoundContract {S : Type} (M : MultiTapeTM k Γ S) (anchor : S) (escape : Set (Option S))
    (ι : Type) (x : List Γ) where
  /-- The precondition. -/
  pre : ι → Cfg k Γ S x → Prop
  /-- The exact, positive running time. -/
  time : ι → Cfg k Γ S x → ℕ
  /-- The endpoint, at the anchor or an escape. -/
  post : ι → Cfg k Γ S x → Cfg k Γ S x
  /-- The lower ends of the head envelope. -/
  lo : ι → Cfg k Γ S x → Fin k → ℤ
  /-- The upper ends of the head envelope. -/
  hi : ι → Cfg k Γ S x → Fin k → ℤ
  pos : ∀ i d, d.state = some anchor → pre i d → 0 < time i d
  run : ∀ i d, d.state = some anchor → pre i d → M.runFrom d (time i d) = post i d
  exit_mem : ∀ i d, d.state = some anchor → pre i d →
    (post i d).state ∈ insert (some anchor) escape
  cut : ∀ i d, d.state = some anchor → pre i d →
    ∀ u, 0 < u → u < time i d → (M.runFrom d u).state ∉ roundStop anchor escape
  env : ∀ i d, d.state = some anchor → pre i d → ∀ u ≤ time i d, ∀ j,
    (M.runFrom d u).workTapePos j ∈ Finset.Icc (lo i d j) (hi i d j)

namespace RoundContract

variable {S : Type} {M : MultiTapeTM k Γ S} {anchor : S} {escape : Set (Option S)} {ι : Type}
  {x : List Γ}

/-- Every admissible run of a round contract is a round. -/
theorem round (R : RoundContract M anchor escape ι x) (i : ι) (d : Cfg k Γ S x)
    (hd : d.state = some anchor) (hp : R.pre i d) :
    Round M anchor escape (HeadBox (R.lo i d) (R.hi i d)) d (R.post i d) (R.time i d) :=
  ⟨hd, R.pos i d hd hp, R.run i d hd hp, R.exit_mem i d hd hp, R.cut i d hd hp,
    fun u hu j => R.env i d hd hp u hu j⟩

/-- **The returning case** is a `Turing.ReturnContract`: restrict the precondition to the starts
whose endpoint is back at the anchor. -/
def returning (R : RoundContract M anchor escape ι x) : ReturnContract M anchor ι x where
  pre i d := R.pre i d ∧ (R.post i d).state = some anchor
  time := R.time
  post := R.post
  lo := R.lo
  hi := R.hi
  pos i d hd hp := R.pos i d hd hp.1
  run i d hd hp := R.run i d hd hp.1
  exit_eq _ _ _ hp := hp.2
  cut i d hd hp u hu hut h := R.cut i d hd hp.1 u hu hut (by
    rw [h]
    exact Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  env i d hd hp := R.env i d hd hp.1

/-- **The escaping case** is a `Turing.Contract` with the escapes as exits: restrict the
precondition to the starts whose endpoint escapes. The time-zero cut needs the anchor to be no
escape.

**Proof sketch.** At time `0` the state is the anchor, which is no escape; later it avoids the
stop set, which contains the escapes. -/
def escaping (R : RoundContract M anchor escape ι x) (ha : some anchor ∉ escape) :
    Contract M anchor escape ι x where
  pre i d := R.pre i d ∧ (R.post i d).state ∈ escape
  time := R.time
  post := R.post
  lo := R.lo
  hi := R.hi
  run i d hd hp := R.run i d hd hp.1
  exit_mem _ _ _ hp := hp.2
  cut i d hd hp := ((R.round i d hd hp.1).segment ha).2.1
  env i d hd hp := R.env i d hd hp.1

end RoundContract

/-- **A returning contract is a round contract without escapes.** Its intermediate states are
live, since a halt would persist to the endpoint, which is at the anchor.

**Proof sketch.** Off the anchor is the returning cut. Liveness: halting is absorbing
(`Turing.MultiTapeTM.runFrom_state_ne_none_of_le`), so a halt before the time would make
the endpoint's state `none`, not the anchor. -/
def ReturnContract.toRound {S : Type} {M : MultiTapeTM k Γ S} {anchor : S} {ι : Type}
    {x : List Γ} (C : ReturnContract M anchor ι x) : RoundContract M anchor ∅ ι x where
  pre := C.pre
  time := C.time
  post := C.post
  lo := C.lo
  hi := C.hi
  pos := C.pos
  run := C.run
  exit_mem i d hd hp := by
    rw [C.exit_eq i d hd hp]
    exact Set.mem_insert _ _
  cut i d hd hp u hu hut := by
    apply not_mem_roundStop.mpr
    cases hs : (M.runFrom d u).state with
    | none =>
      refine absurd hs (MultiTapeTM.runFrom_state_ne_none_of_le M d _ ?_ u hut.le)
      rw [C.run i d hd hp, C.exit_eq i d hd hp]
      exact Option.some_ne_none _
    | some s =>
      refine ⟨s, rfl, fun h => C.cut i d hd hp u hu hut (by rw [hs, h]), fun h => h⟩
  env := C.env

/-! ## Hulls of round boxes along an orbit (MIG-0b)

The envelope of an iterated round contract: the tape-wise hull of the first `n` round boxes and
of the final orbit head. `Build/CounterLoop`'s round-contract compositions use it. -/

namespace RoundContract

variable {S : Type} {M : MultiTapeTM k Γ S} {a : S} {E : Set (Option S)} {ι : Type}
  {x : List Γ}

/-- The lower ends of the **hull of an orbit's round boxes**: tape by tape, the least lower end
of the envelopes of the first `n` rounds of the orbit from `c` (each lasting the round
contract's time), and of the head at the `n`-th orbit point. -/
def hullLo (R : RoundContract M a E ι x) (i : ι) (c : Cfg k Γ S x) (n : ℕ) (j : Fin k) : ℤ :=
  (Finset.range (n + 1)).inf' Finset.nonempty_range_add_one fun r =>
    if r < n then R.lo i (roundOrbit M (R.time i) c r) j
    else (roundOrbit M (R.time i) c r).workTapePos j

/-- The upper ends of the hull of an orbit's round boxes (see `Turing.RoundContract.hullLo`). -/
def hullHi (R : RoundContract M a E ι x) (i : ι) (c : Cfg k Γ S x) (n : ℕ) (j : Fin k) : ℤ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun r =>
    if r < n then R.hi i (roundOrbit M (R.time i) c r) j
    else (roundOrbit M (R.time i) c r).workTapePos j

/-- Along admissible rounds of the orbit, each returning except possibly the last, every orbit
point before `n` is at the anchor.

**Proof sketch.** Induction: a round from the anchor ends at the round contract's endpoint
(`run`), which is the next orbit point, and that endpoint is at the anchor when the round
returns. -/
theorem orbit_anchor (R : RoundContract M a E ι x) (i : ι) (c : Cfg k Γ S x)
    (hc : c.state = some a) (n : ℕ) (hpre : ∀ r < n, R.pre i (roundOrbit M (R.time i) c r))
    (hret : ∀ r, r + 1 < n → (R.post i (roundOrbit M (R.time i) c r)).state = some a) :
    ∀ r < n, (roundOrbit M (R.time i) c r).state = some a := by
  intro r hr
  induction r with
  | zero => exact hc
  | succ r ih =>
    rw [roundOrbit_succ, R.run i _ (ih (by omega)) (hpre r (by omega))]
    exact hret r hr

/-- **The orbit's rounds** under the hull box: each of the first `n` orbit rounds is a round,
ending at the next orbit point, with its heads in the hull of all the round boxes.

**Proof sketch.** `Turing.RoundContract.round` at each orbit point, which is at the anchor by
`Turing.RoundContract.orbit_anchor`; its endpoint is the next orbit point (`run`), and its own box
lies in the hull (`Finset.inf'_le`, `Finset.le_sup'`). -/
theorem orbit_round (R : RoundContract M a E ι x) (i : ι) (c : Cfg k Γ S x)
    (hc : c.state = some a) (n : ℕ) (hpre : ∀ r < n, R.pre i (roundOrbit M (R.time i) c r))
    (hret : ∀ r, r + 1 < n → (R.post i (roundOrbit M (R.time i) c r)).state = some a) :
    ∀ r < n, Round M a E (HeadBox (R.hullLo i c n) (R.hullHi i c n))
      (roundOrbit M (R.time i) c r) (roundOrbit M (R.time i) c (r + 1))
      (R.time i (roundOrbit M (R.time i) c r)) := by
  intro r hr
  have ha := R.orbit_anchor i c hc n hpre hret r hr
  have hR := R.round i _ ha (hpre r hr)
  have hnext : roundOrbit M (R.time i) c (r + 1) = R.post i (roundOrbit M (R.time i) c r) := by
    rw [roundOrbit_succ, R.run i _ ha (hpre r hr)]
  rw [hnext]
  refine ⟨hR.1, hR.2.1, hR.2.2.1, hR.2.2.2.1, hR.2.2.2.2.1, fun u hu j => ?_⟩
  have hb := hR.2.2.2.2.2 u hu j
  have hmem : r ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  rw [Finset.mem_Icc] at hb ⊢
  constructor
  · refine le_trans (Finset.inf'_le (fun r => if r < n then R.lo i (roundOrbit M (R.time i) c r) j
      else (roundOrbit M (R.time i) c r).workTapePos j) hmem) ?_
    simp only [if_pos hr]
    exact hb.1
  · refine le_trans ?_ (Finset.le_sup' (fun r => if r < n then
      R.hi i (roundOrbit M (R.time i) c r) j else (roundOrbit M (R.time i) c r).workTapePos j) hmem)
    simp only [if_pos hr]
    exact hb.2

/-- The start of the orbit lies in the hull box.

**Proof sketch.** With no round, the hull is the start itself; otherwise the start is time `0`
of the first round. -/
theorem orbit_start (R : RoundContract M a E ι x) (i : ι) (c : Cfg k Γ S x)
    (hc : c.state = some a) (n : ℕ) (hpre : ∀ r < n, R.pre i (roundOrbit M (R.time i) c r))
    (hret : ∀ r, r + 1 < n → (R.post i (roundOrbit M (R.time i) c r)).state = some a) :
    HeadBox (R.hullLo i c n) (R.hullHi i c n) c.workTapePos := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · intro j
    simp [hullLo, hullHi, roundOrbit]
  · exact (R.orbit_round i c hc n hpre hret 0 hn).2.2.2.2.2 0 (Nat.zero_le _)

end RoundContract

/-- The host box of a counter loop: the counter interval on the last tape, and a body box on the
others. -/
theorem headBox_lastCases {lo hi : Fin k → ℤ} {clo chi : ℤ} {p : Fin (k + 1) → ℤ}
    (hc : p (Fin.last k) ∈ Finset.Icc clo chi) (hb : HeadBox lo hi fun j => p j.castSucc) :
    HeadBox (Fin.lastCases (motive := fun _ => ℤ) clo lo)
      (Fin.lastCases (motive := fun _ => ℤ) chi hi) p := by
  intro j
  induction j using Fin.lastCases with
  | last => simpa only [Fin.lastCases_last] using hc
  | cast i => simpa only [Fin.lastCases_castSucc] using hb i

/-! ## The joint-trajectory layer (design §16a, MIG-0b item 3)

Per-tape intervals cannot express a relation between heads, such as "the two heads are equal"
(MIG-0a gate, round 1, counterexample 6), and `CounterLoop`'s `counterSpan` carries exactly such a
relation on the body heads. `Turing.Contract.Traj` names one, as a derived property in the manner
of `Turing.Contract.Frames`: it is not a field, every contract has its envelope box as one
(`Turing.Contract.traj_env`), and the compositions preserve them (`trans` here; `seq`, `inPhase`
and `branch` in `Build/Contract/Seam`; `embed` in `Build/Contract/Embed`). -/

namespace Contract

/-- A contract **has the joint trajectory** `R` when, for every index `i` and every admissible
start `d`, the whole head vector satisfies `R i d` at every time up to the endpoint. -/
def Traj {S : Type} {M : MultiTapeTM k Γ S} {entry : S} {exits : Set (Option S)} {ι : Type}
    {x : List Γ} (C : Contract M entry exits ι x)
    (R : ι → Cfg k Γ S x → (Fin k → ℤ) → Prop) : Prop :=
  ∀ i d, d.state = some entry → C.pre i d → ∀ u ≤ C.time i d, R i d (M.runFrom d u).workTapePos

section TrajBasic

variable {S : Type} {M : MultiTapeTM k Γ S} {entry : S} {exits : Set (Option S)} {ι : Type}
  {x : List Γ}

/-- Every contract has its envelope box as a joint trajectory. -/
theorem traj_env (C : Contract M entry exits ι x) :
    C.Traj fun i d => HeadBox (C.lo i d) (C.hi i d) :=
  fun i d hd hp u hu j => C.env i d hd hp u hu j

/-- Weakening a joint trajectory. -/
theorem Traj.mono {C : Contract M entry exits ι x} {R R' : ι → Cfg k Γ S x → (Fin k → ℤ) → Prop}
    (h : C.Traj R) (hR : ∀ i d p, R i d p → R' i d p) : C.Traj R' :=
  fun i d hd hp u hu => hR i d _ (h i d hd hp u hu)

/-- Two joint trajectories hold jointly. -/
theorem Traj.and {C : Contract M entry exits ι x} {R R' : ι → Cfg k Γ S x → (Fin k → ℤ) → Prop}
    (h : C.Traj R) (h' : C.Traj R') : C.Traj fun i d p => R i d p ∧ R' i d p :=
  fun i d hd hp u hu => ⟨h i d hd hp u hu, h' i d hd hp u hu⟩

/-- **A joint trajectory is a segment relation**: every admissible run is a segment against the
exits, ending at the endpoint, with the relation along it. -/
theorem Traj.segment {C : Contract M entry exits ι x}
    {R : ι → Cfg k Γ S x → (Fin k → ℤ) → Prop} (h : C.Traj R) (i : ι) (d : Cfg k Γ S x)
    (hd : d.state = some entry) (hp : C.pre i d) :
    Segment M exits (R i d) d (C.post i d) (C.time i d) :=
  ⟨C.run i d hd hp, C.cut i d hd hp, h i d hd hp⟩

/-- **`trans` preserves joint trajectories**: up to the first contract's time the first relation
holds, and after it the second, at the linked index and the first endpoint.

**Proof sketch.** Split the time at the first contract's time, as in `Turing.Contract.trans`'s
envelope. -/
theorem Traj.trans {e₁ e₂ : S} {X : Set (Option S)} {κ : Type} {C₁ : Contract M e₁ {some e₂} ι x}
    {C₂ : Contract M e₂ X κ x} {link : ι → κ}
    {hlink : ∀ i d, d.state = some e₁ → C₁.pre i d → C₂.pre (link i) (C₁.post i d)}
    {hX : ∀ i d, d.state = some e₁ → C₁.pre i d → ∀ u < C₁.time i d, (M.runFrom d u).state ∉ X}
    {R₁ : ι → Cfg k Γ S x → (Fin k → ℤ) → Prop} {R₂ : κ → Cfg k Γ S x → (Fin k → ℤ) → Prop}
    (h₁ : C₁.Traj R₁) (h₂ : C₂.Traj R₂) :
    (C₁.trans C₂ link hlink hX).Traj fun i d p => R₁ i d p ∨ R₂ (link i) (C₁.post i d) p := by
  intro i d hd hp u hu
  have hx := Set.mem_singleton_iff.mp (C₁.exit_mem i d hd hp)
  change u ≤ C₁.time i d + C₂.time (link i) (C₁.post i d) at hu
  by_cases h : u ≤ C₁.time i d
  · exact Or.inl (h₁ i d hd hp u h)
  · obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le (le_of_lt (not_le.mp h))
    rw [MultiTapeTM.runFrom_add, C₁.run i d hd hp]
    exact Or.inr (h₂ _ _ hx (hlink i d hd hp) v (by omega))

/-- **`trans` preserves frames**: footprints add up (`Turing.Cfg.SameOutside.trans`). -/
theorem Frames.trans {e₁ e₂ : S} {X : Set (Option S)} {κ : Type}
    {C₁ : Contract M e₁ {some e₂} ι x} {C₂ : Contract M e₂ X κ x} {link : ι → κ}
    {hlink : ∀ i d, d.state = some e₁ → C₁.pre i d → C₂.pre (link i) (C₁.post i d)}
    {hX : ∀ i d, d.state = some e₁ → C₁.pre i d → ∀ u < C₁.time i d, (M.runFrom d u).state ∉ X}
    {fp₁ : ι → Cfg k Γ S x → Fin k → Set ℤ} {fp₂ : κ → Cfg k Γ S x → Fin k → Set ℤ}
    (h₁ : C₁.Frames fp₁) (h₂ : C₂.Frames fp₂) :
    (C₁.trans C₂ link hlink hX).Frames fun i d j => fp₁ i d j ∪ fp₂ (link i) (C₁.post i d) j :=
  fun i d hd hp => (h₁ i d hd hp).trans
    (h₂ _ _ (Set.mem_singleton_iff.mp (C₁.exit_mem i d hd hp)) (hlink i d hd hp))

end TrajBasic

end Contract

/-! ## Sanity lemmas (design §16a, MIG-0b item 7; MIG-0a gate, round 1, counterexample 1)

The positivity of the seam compositions and of the releases is in `Build/Contract/Seam`, and that
of `embed` in `Build/Contract/Embed`. -/

namespace Contract

section Sanity

variable {S : Type} {M : MultiTapeTM k Γ S} {entry : S} {exits : Set (Option S)} {ι : Type}
  {x : List Γ}

/-- **The zero-time characterization**: on an admissible start, a contract's time is `0` exactly
when its entry is among its exits.

**Proof sketch.** If the time is `0`, the endpoint is the start, which is at the entry, and the
endpoint is at an exit. If the entry is an exit and the time were positive, the cut at time `0`
would exclude it. -/
theorem time_eq_zero_iff (C : Contract M entry exits ι x) (i : ι) (d : Cfg k Γ S x)
    (hd : d.state = some entry) (hp : C.pre i d) : C.time i d = 0 ↔ some entry ∈ exits := by
  constructor
  · intro h
    have hx := C.exit_mem i d hd hp
    rw [← C.run i d hd hp, h, MultiTapeTM.runFrom_zero, hd] at hx
    exact hx
  · intro h
    by_contra hne
    exact C.cut i d hd hp 0 (Nat.pos_of_ne_zero hne) (by rw [MultiTapeTM.runFrom_zero, hd]; exact h)

/-- A contract whose entry is no exit is positive. -/
theorem positive_of_not_mem (C : Contract M entry exits ι x) (h : some entry ∉ exits) :
    C.Positive :=
  fun i d hd hp => Nat.pos_of_ne_zero fun h0 => h ((C.time_eq_zero_iff i d hd hp).mp h0)

/-- A positive contract with an admissible start has its entry outside its exits. -/
theorem not_mem_of_positive (C : Contract M entry exits ι x) (h : C.Positive) (i : ι)
    (d : Cfg k Γ S x) (hd : d.state = some entry) (hp : C.pre i d) : some entry ∉ exits :=
  fun hm => (Nat.pos_iff_ne_zero.mp (h i d hd hp)) ((C.time_eq_zero_iff i d hd hp).mpr hm)

/-- `trans` of a positive first contract is positive. -/
theorem trans_positive {e₁ e₂ : S} {X : Set (Option S)} {κ : Type}
    (C₁ : Contract M e₁ {some e₂} ι x) (C₂ : Contract M e₂ X κ x) (link : ι → κ)
    (hlink : ∀ i d, d.state = some e₁ → C₁.pre i d → C₂.pre (link i) (C₁.post i d))
    (hX : ∀ i d, d.state = some e₁ → C₁.pre i d → ∀ u < C₁.time i d, (M.runFrom d u).state ∉ X)
    (h : C₁.Positive) : (C₁.trans C₂ link hlink hX).Positive :=
  fun i d hd hp => Nat.lt_of_lt_of_le (h i d hd hp) (Nat.le_add_right _ _)

end Sanity

end Contract

/-! ## Transports (design §16a, MIG-0b item 6; §16, *transports*)

Contract-to-contract theorems along the library's simulations: state renaming along an embedding,
and the macro-step lockstep (`Turing.Lockstep`), the common shape of alphabet reduction
([AB09, Claim 1.5]; `Robustness/AlphabetReduction`, `L = 3(|Γ| + 1) + 2` steps per source step)
and of the robustness layer's lockstep combinators. The alphabet-reduction adapter (the
lockstep instance and its contract theorem) lands with RS-5 in `Robustness/AlphabetReduction`,
where its lockstep is proved; the symbol lift (through `Cfg.decodeSymbols`) is in
`Build/Contract/Lift`. -/

namespace Contract

/-- The renamed prefix of a contract run: up to its time, the host run from a start at the renamed
entry is the source run from the state-replaced start, renamed.

**Proof sketch.** The renamed source start is the host start. The guard holds before the time,
so `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn` transports every prefix. -/
private lemma mapState_traj {S H : Type} {M : MultiTapeTM k Γ S} {entry : S} {X : Set (Option S)}
    {ι : Type} {x : List Γ} (C : Contract M entry X ι x) (N : MultiTapeTM k Γ H) (emb : S ↪ H)
    (good : S → Prop)
    (hagree : ∀ q, good q → ∀ inp work, N.tr (emb q) inp work = (M.tr q inp work).mapState emb)
    (hgood : ∀ i d, d.state = some entry → C.pre i d →
      ∀ u < C.time i d, ∀ q, (M.runFrom d u).state = some q → good q)
    (i : ι) (d : Cfg k Γ H x) (hd : d.state = some (emb entry))
    (hp : C.pre i (d.mapState fun _ => entry)) :
    ∀ u ≤ C.time i (d.mapState fun _ => entry),
      N.runFrom d u = (M.runFrom (d.mapState fun _ => entry) u).mapState emb := by
  have hc : (d.mapState fun _ => entry).state = some entry := by simp [Cfg.mapState, hd]
  have hd' : (d.mapState fun _ => entry).mapState emb = d :=
    Cfg.ext (by simp [Cfg.mapState, hd]) rfl rfl rfl rfl
  intro u hu
  have H := MultiTapeTM.runFrom_mapState_of_agreeOn M N emb good hagree _ u
    (fun v hv => hgood i _ hc hp v (by omega))
  rwa [hd'] at H

/-- **State renaming along an embedding** (`Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`): a
host whose table agrees, on the renamed good states, with the source table renamed, runs every
contract of the source whose runs stay in good states before their time. The host's entry and
exits are the renamed ones; the time and the envelope are the source's, at the state-replaced
start, and the endpoint is the source endpoint, renamed. This is the transport behind the phase
host, the counter loop's body phase and the call controllers.

**Proof sketch.** By the renamed prefix (`mapState_traj`): the run and the exit are the source's,
renamed; a renamed state is a renamed exit only if the source state is an exit, by injectivity;
and the heads are the source's. -/
def mapState {S H : Type} {M : MultiTapeTM k Γ S} {entry : S} {X : Set (Option S)} {ι : Type}
    {x : List Γ} (C : Contract M entry X ι x) (N : MultiTapeTM k Γ H) (emb : S ↪ H)
    (good : S → Prop)
    (hagree : ∀ q, good q → ∀ inp work, N.tr (emb q) inp work = (M.tr q inp work).mapState emb)
    (hgood : ∀ i d, d.state = some entry → C.pre i d →
      ∀ u < C.time i d, ∀ q, (M.runFrom d u).state = some q → good q) :
    Contract N (emb entry) (Option.map emb '' X) ι x where
  pre i d := C.pre i (d.mapState fun _ => entry)
  time i d := C.time i (d.mapState fun _ => entry)
  post i d := (C.post i (d.mapState fun _ => entry)).mapState emb
  lo i d := C.lo i (d.mapState fun _ => entry)
  hi i d := C.hi i (d.mapState fun _ => entry)
  run i d hd hp := by
    have hc : (d.mapState fun _ => entry).state = some entry := by simp [Cfg.mapState, hd]
    rw [mapState_traj C N emb good hagree hgood i d hd hp _ le_rfl, C.run i _ hc hp]
  exit_mem i d hd hp := by
    have hc : (d.mapState fun _ => entry).state = some entry := by simp [Cfg.mapState, hd]
    exact ⟨_, C.exit_mem i _ hc hp, rfl⟩
  cut i d hd hp u hu := by
    have hc : (d.mapState fun _ => entry).state = some entry := by simp [Cfg.mapState, hd]
    rw [mapState_traj C N emb good hagree hgood i d hd hp u hu.le]
    rintro ⟨q, hq, heq⟩
    have hq' : q = (M.runFrom (d.mapState fun _ => entry) u).state :=
      Option.map_injective emb.injective heq
    exact C.cut i _ hc hp u hu (hq' ▸ hq)
  env i d hd hp u hu j := by
    have hc : (d.mapState fun _ => entry).state = some entry := by simp [Cfg.mapState, hd]
    rw [mapState_traj C N emb good hagree hgood i d hd hp u hu]
    exact C.env i _ hc hp u hu j

end Contract

/-- **A macro-step lockstep** (design §16, *lockstep combinators*): every source step from a
configuration off the exits `X` is simulated by exactly `cost c` target steps through the
encoding `enc`; an encoded exit is a target exit in `X'`; and inside a simulated step the target
meets no target exit. Alphabet reduction ([AB09, Claim 1.5]) is the case
`cost = 3(|Γ| + 1) + 2`; a lockstep decoration is the case `cost = 1`. Neither a positive cost
nor an injective encoding is required. -/
structure Lockstep {k' : ℕ} {Γ' S S' : Type} {x : List Γ} {x' : List Γ'}
    (M : MultiTapeTM k Γ S) (N : MultiTapeTM k' Γ' S') (enc : Cfg k Γ S x → Cfg k' Γ' S' x')
    (cost : Cfg k Γ S x → ℕ) (X : Set (Option S)) (X' : Set (Option S')) : Prop where
  step : ∀ c, c.state ∉ X → N.runFrom (enc c) (cost c) = enc (M.step c)
  exit : ∀ c, c.state ∈ X → (enc c).state ∈ X'
  inner : ∀ c, c.state ∉ X → ∀ v < cost c, (N.runFrom (enc c) v).state ∉ X'

namespace Lockstep

variable {k' : ℕ} {Γ' S S' : Type} {x : List Γ} {x' : List Γ'} {M : MultiTapeTM k Γ S}
  {N : MultiTapeTM k' Γ' S'} {enc : Cfg k Γ S x → Cfg k' Γ' S' x'} {cost : Cfg k Γ S x → ℕ}
  {X : Set (Option S)} {X' : Set (Option S')}

/-- **The lockstep over a run**: a source run of `t` steps that avoids `X` before `t` is simulated
by the sum of its step costs.

**Proof sketch.** Induction on `t`, with one `step` per source step
(`Turing.MultiTapeTM.runFrom_add`). -/
theorem runFrom (L : Lockstep M N enc cost X X') (d : Cfg k Γ S x) (t : ℕ)
    (ht : ∀ u < t, (M.runFrom d u).state ∉ X) :
    N.runFrom (enc d) (∑ u ∈ Finset.range t, cost (M.runFrom d u)) = enc (M.runFrom d t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, MultiTapeTM.runFrom_add, ih fun u hu => ht u (by omega),
      L.step _ (ht t (by omega)), MultiTapeTM.runFrom_succ_eq_step']

/-- **The lockstep cut**: a simulated run that avoids `X` before `t` avoids `X'` before the sum
of its step costs.

**Proof sketch.** Induction on `t`: a time in the last simulated step is an inner time of that
step, from the encoded configuration reached by `Turing.Lockstep.runFrom`. -/
theorem cut (L : Lockstep M N enc cost X X') (d : Cfg k Γ S x) (t : ℕ)
    (ht : ∀ u < t, (M.runFrom d u).state ∉ X) :
    ∀ v < ∑ u ∈ Finset.range t, cost (M.runFrom d u), (N.runFrom (enc d) v).state ∉ X' := by
  induction t with
  | zero => simp
  | succ t ih =>
    intro v hv
    rw [Finset.sum_range_succ] at hv
    by_cases hlt : v < ∑ u ∈ Finset.range t, cost (M.runFrom d u)
    · exact ih (fun u hu => ht u (by omega)) v hlt
    · obtain ⟨w, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hlt)
      rw [MultiTapeTM.runFrom_add, L.runFrom d t fun u hu => ht u (by omega)]
      exact L.inner _ (ht t (by omega)) w (by omega)

/-- **Locating a target time**: every target time up to the simulated length of a source run
lies in one simulated step, at an offset inside it (or is the start of the step after the last).

**Proof sketch.** Induction on `t`: a time beyond the first `t` simulated steps is an offset in
the last one, from the encoded configuration reached by `Turing.Lockstep.runFrom`. -/
theorem locate (L : Lockstep M N enc cost X X') (d : Cfg k Γ S x) (t : ℕ)
    (ht : ∀ u < t, (M.runFrom d u).state ∉ X) :
    ∀ v ≤ ∑ u ∈ Finset.range t, cost (M.runFrom d u), ∃ u ≤ t, ∃ w,
      (w = 0 ∨ ((M.runFrom d u).state ∉ X ∧ w ≤ cost (M.runFrom d u))) ∧
      N.runFrom (enc d) v = N.runFrom (enc (M.runFrom d u)) w := by
  induction t with
  | zero =>
    intro v hv
    simp only [Finset.range_zero, Finset.sum_empty, Nat.le_zero] at hv
    exact ⟨0, le_rfl, 0, Or.inl rfl, by rw [hv]; rfl⟩
  | succ t ih =>
    intro v hv
    rw [Finset.sum_range_succ] at hv
    by_cases hle : v ≤ ∑ u ∈ Finset.range t, cost (M.runFrom d u)
    · obtain ⟨u, hu, w, hw, he⟩ := ih (fun u hu => ht u (by omega)) v hle
      exact ⟨u, by omega, w, hw, he⟩
    · obtain ⟨w, rfl⟩ := Nat.exists_eq_add_of_le (le_of_lt (not_le.mp hle))
      refine ⟨t, by omega, w, Or.inr ⟨ht t (by omega), by omega⟩, ?_⟩
      rw [MultiTapeTM.runFrom_add, L.runFrom d t fun u hu => ht u (by omega)]

end Lockstep

/-- **Transport along a macro-step lockstep**. A source contract becomes a
target contract whose index also records the source start: an admissible target start is the
encoding of an admissible source start. The time is the sum of the step costs along the source
run, the endpoint is the encoded source endpoint, and the envelope is the hull of per-step boxes
`blo`, `bhi`, which `hbox` asserts for every simulated step and every encoded configuration.

**Proof sketch.** The run is `Turing.Lockstep.runFrom` and the cut `Turing.Lockstep.cut`, fed the
source cut; the exit is `exit` at the source endpoint. For the envelope, a target time lies in
one simulated step, at an offset inside it (`Turing.Lockstep.locate`); `hbox` bounds the heads
there by that step's box, which lies inside the hull over the source run.

The target entry `entry'` is a free parameter: no premise relates it to the encoding. The
admissible target starts are the encodings of admissible source starts that lie at `entry'`.
A sufficient condition for every admissible source start to transport is that the encoding
sends every source configuration at `entry` to one at `entry'`
(`Turing.Contract.lockstep_admissible`; for a state-renaming encoding,
`Turing.Contract.lockstep_admissible_map`); compatibility on the admissible source starts
alone also suffices. Without any compatibility the contract may have no admissible start. -/
def Contract.lockstep {k' : ℕ} {Γ' S S' : Type} {x : List Γ} {x' : List Γ'}
    {M : MultiTapeTM k Γ S} {N : MultiTapeTM k' Γ' S'} {enc : Cfg k Γ S x → Cfg k' Γ' S' x'}
    {cost : Cfg k Γ S x → ℕ} {entry : S} {X : Set (Option S)} {X' : Set (Option S')} {ι : Type}
    (C : Contract M entry X ι x) (L : Lockstep M N enc cost X X') (entry' : S')
    (blo bhi : Cfg k Γ S x → Fin k' → ℤ)
    (hbox : ∀ c v, (v = 0 ∨ (c.state ∉ X ∧ v ≤ cost c)) → ∀ j,
      (N.runFrom (enc c) v).workTapePos j ∈ Finset.Icc (blo c j) (bhi c j)) :
    Contract N entry' X' (ι × Cfg k Γ S x) x' where
  pre p d' := d' = enc p.2 ∧ p.2.state = some entry ∧ C.pre p.1 p.2
  time p _ := ∑ u ∈ Finset.range (C.time p.1 p.2), cost (M.runFrom p.2 u)
  post p _ := enc (C.post p.1 p.2)
  lo p _ j := (Finset.range (C.time p.1 p.2 + 1)).inf' Finset.nonempty_range_add_one
    fun u => blo (M.runFrom p.2 u) j
  hi p _ j := (Finset.range (C.time p.1 p.2 + 1)).sup' Finset.nonempty_range_add_one
    fun u => bhi (M.runFrom p.2 u) j
  run p d' _ hp := by
    obtain ⟨rfl, hs, hc⟩ := hp
    rw [L.runFrom p.2 _ (C.cut p.1 p.2 hs hc), C.run p.1 p.2 hs hc]
  exit_mem p d' _ hp := by
    obtain ⟨rfl, hs, hc⟩ := hp
    exact L.exit _ (C.exit_mem p.1 p.2 hs hc)
  cut p d' _ hp := by
    obtain ⟨rfl, hs, hc⟩ := hp
    exact L.cut p.2 _ (C.cut p.1 p.2 hs hc)
  env p d' _ hp v hv j := by
    obtain ⟨rfl, hs, hc⟩ := hp
    obtain ⟨u, hu, w, hw, he⟩ := L.locate p.2 _ (C.cut p.1 p.2 hs hc) v hv
    have hb := hbox (M.runFrom p.2 u) w hw j
    rw [he]
    have hmem : u ∈ Finset.range (C.time p.1 p.2 + 1) := Finset.mem_range.mpr (by omega)
    rw [Finset.mem_Icc] at hb ⊢
    exact ⟨(Finset.inf'_le (fun u => blo (M.runFrom p.2 u) j) hmem).trans hb.1,
      hb.2.trans (Finset.le_sup' (fun u => bhi (M.runFrom p.2 u) j) hmem)⟩

/-- **Admissible starts of a lockstep transport** (the entry-compatibility condition, MIG-0b
gate, round 1, minor 3). If the encoding sends every source configuration at `entry` to a target
configuration at `entry'`, then every admissible source start `c` gives an admissible target start
`enc c`, at the index `(i, c)`. The condition is sufficient, not necessary: the transported
contract's admissible starts are the encodings of admissible source starts that lie at
`entry'`, so compatibility on the admissible source starts alone also suffices (the proof uses
`hentry` only at `c`; MIG-0b gate, round 2, minor 3). Without any compatibility the contract
may have no admissible start: with an identity encoding and `entry' ≠ entry` it has none. -/
theorem Contract.lockstep_admissible {k' : ℕ} {Γ' S S' : Type} {x : List Γ} {x' : List Γ'}
    {M : MultiTapeTM k Γ S} {N : MultiTapeTM k' Γ' S'} {enc : Cfg k Γ S x → Cfg k' Γ' S' x'}
    {cost : Cfg k Γ S x → ℕ} {entry : S} {X : Set (Option S)} {X' : Set (Option S')} {ι : Type}
    (C : Contract M entry X ι x) (L : Lockstep M N enc cost X X') (entry' : S')
    (blo bhi : Cfg k Γ S x → Fin k' → ℤ)
    (hbox : ∀ c v, (v = 0 ∨ (c.state ∉ X ∧ v ≤ cost c)) → ∀ j,
      (N.runFrom (enc c) v).workTapePos j ∈ Finset.Icc (blo c j) (bhi c j))
    (hentry : ∀ c : Cfg k Γ S x, c.state = some entry → (enc c).state = some entry')
    (i : ι) (c : Cfg k Γ S x) (hc : c.state = some entry) (hp : C.pre i c) :
    (enc c).state = some entry' ∧ (C.lockstep L entry' blo bhi hbox).pre (i, c) (enc c) :=
  ⟨hentry c hc, rfl, hc, hp⟩

/-- **Admissible starts for a state-renaming encoding**: when the encoding renames states by `ρ`
(as alphabet reduction's does), the renamed entry `ρ entry` is compatible, so every admissible
source start `c` gives the admissible target start `enc c`. -/
theorem Contract.lockstep_admissible_map {k' : ℕ} {Γ' S S' : Type} {x : List Γ} {x' : List Γ'}
    {M : MultiTapeTM k Γ S} {N : MultiTapeTM k' Γ' S'} {enc : Cfg k Γ S x → Cfg k' Γ' S' x'}
    {cost : Cfg k Γ S x → ℕ} {entry : S} {X : Set (Option S)} {X' : Set (Option S')} {ι : Type}
    (C : Contract M entry X ι x) (L : Lockstep M N enc cost X X') (ρ : S → S')
    (hρ : ∀ c, (enc c).state = c.state.map ρ)
    (blo bhi : Cfg k Γ S x → Fin k' → ℤ)
    (hbox : ∀ c v, (v = 0 ∨ (c.state ∉ X ∧ v ≤ cost c)) → ∀ j,
      (N.runFrom (enc c) v).workTapePos j ∈ Finset.Icc (blo c j) (bhi c j))
    (i : ι) (c : Cfg k Γ S x) (hc : c.state = some entry) (hp : C.pre i c) :
    (enc c).state = some (ρ entry) ∧
      (C.lockstep L (ρ entry) blo bhi hbox).pre (i, c) (enc c) :=
  C.lockstep_admissible L (ρ entry) blo bhi hbox
    (fun c hc => by rw [hρ, hc]; rfl) i c hc hp

end Turing
