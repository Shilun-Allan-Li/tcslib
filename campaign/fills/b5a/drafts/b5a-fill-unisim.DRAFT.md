# Ch3–4 fill campaign — B5a, H1: the uniform simulator (`Turing.MachineFormat.exists_uniformSimulator`, `TuringMachine/CodeSimulator.lean`)

<!-- DRAFT (drafting agent), 2026-10-24, for megafill C. Drafting base: the campaign tip
`77f1eb4fb74deb7a1ac7bae7bc4e98d5d0f9a532` (TCSlib as after #155; #156 open). Pre-ship measured
there, against a fresh bootstrap of the order list:
`campaign/fills/b5a/drafts/b5a-fill-unisim/preship-77f1eb4f/`.
**Q-B1, ruled (user, 2026-10-24): option A**, the startup kit published first (PR #162,
`Build/InterpreterStartup`); this text keeps option A, and option B's paragraphs are removed.
Issue-time items: @ANCESTOR@, ⟨BASE⟩, ⟨IN-FLIGHT⟩, the megafill banner, the semantic-duplication
requirement (gates 69 and 72; megafill D's drafting brief §5), and re-running the pre-ship at the
issue commit.
**Issue base (review, 2026-10-24):** after #156 (merged; its round-2 head `0e5f210b` edits this
file's `canonEmitVerdict`, 4593–4603), the follow-up phase-host API PR #159 (merged; it edits
`canonEmitVerdict` again) and the startup kit's PR #162. Regenerate the overlay (six imports, the
kit's module the sixth) and every line number, count, blob and screen figure there; the numbers
below are the drafting base's, measured with the first five imports.
**Pre-ship re-run at the issue base (maintainer, 2026-10-25):** the campaign tip `a524c36f`, Lean
equal to #162's merge `5a258cc2` (the snapshot `oleans-lkit2`), with the six imports:
`campaign/fills/b5a/drafts/b5a-fill-unisim/preship-a524c36f/`. The line numbers, counts and blob
below are that base's; ⟨BASE⟩ and ⟨IN-FLIGHT⟩ are filled at issue. -->

> **⟨Megafill C, item N⟩** (cover brief ⟨…⟩; addendum v2.5, Part 3). The preflight, the toolchain,
> the clone and the cache are done once for the whole queue. For this item: create its branch from
> the shared base (below), make your first edit, **re-bootstrap your order list**, then follow this
> brief. **Budget:** 5 hours (the cover's proposal) from your branch's creation. Deliver a
> checkpoint zip after each checkpoint: the session may end at any time.

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If it
  fails, **stop**. That commit contains:
  - **your target as a gated statement**: `Turing.MachineFormat.exists_uniformSimulator`, B5a's
    statement (wave-1 statement gate, `campaign/gates/wave1-statements/`, round 2; its note 34:
    "preserve the uniform quantifier order; per-code constants would not suffice for EXPCOM");
  - **the canonizer, proved** (PR #152, gate 67): `Turing.MachineFormat.exists_polyCanonizer`, in
    your file, with no admission. Your target is the module's last admitted stub, behind targets
    3–8 (`Turing.exists_uniformMachineCode2`, `Turing.exists_uniformMachineCode`,
    `Complexity.EXP_subset_POracle_EXPCOM`, `Complexity.POracle_EXPCOM_eq_EXP`,
    `Complexity.NPOracle_EXPCOM_eq_EXP`, `Complexity.POracle_EXPCOM_eq_NPOracle_EXPCOM`) and
    `Complexity.baker_gill_solovay`;
  - **H1's hosted clock and verdict, proved** in your file: the generic step block
    (`Build/StepBlock`, H2), its hosted counter loop `Turing.StepBlock.hostedLoopTM_run`
    (`Build/StepBlockLoop`), and your file's private verdict `h1HostedVerdictTM`,
    `h1HostedVerdict_effect`, `h1HostedVerdict_accepts`, from the prepared round seam;
  - **the rows the startup composes, all proved**: the prefix canonizer (`UniversalStartup`), the
    pair extractors (`Build/Primitives`), the returning capture (`Build/Embed`), the input rewind
    (`Build/InputRewind`, PR #153), the work-tape rewind (`Build/Rewind`), the counter copy
    (`Build/Catalog`), the window copier (`Build/InputWindow`), the install call
    (`Build/Loop`), the seam layout (`Build/SeamLayout`), and the seams and phase host
    (`Build/Seam`);
  - **the model for your startup:** C1's interpreter core `Turing.exists_ndInterpreterCore`
    (`NDCodeSimulator`, PR #151, gate 66), the same twelve-phase startup over these rows for the
    replay machine; and its review (`campaign/fills/c1/reviews/core-cont2/REVIEW.md`);
  - **the startup kit, published** (PR #162, `Build/InterpreterStartup`): `Turing.seamCompTM_step`,
    `Turing.prefixCanon_pairExtract_halt`, `Turing.embedSilentRetTM_firstReturn`,
    `Turing.headerCapture_run`, `Turing.exists_windowCall`, `Turing.installCall_releasePhase`,
    `Turing.exists_layoutCall` (stated over `pairEncode n.bits (unaryFin M.q₀ ++ tableBitsK M.tr)`)
    and `Turing.embedSilentCfg_initCfg`, harvested from `NDCodeSimulator`'s startup privates and
    `UniversalK`'s `ss_captureInitial`;
  - **the phase host's last phase** (PR #156, gate 69: `Turing.phaseHostTM_tr_of_red_none`,
    `Turing.phaseHostTM_run_le`) and its start-state and redirect-branch equations (PR #159,
    gate 71: `Turing.phaseHostTM_q₀`, `Turing.phaseHostTM_tr_of_red_some`). Both PRs edit your
    file's `canonEmitVerdict` (not yours);
  - the fill-agent environment addendum `campaign/standards/fill-environment-addendum.md`
    (**v2.5**: Part 1, the resources and the cache for the Mathlib roots only, with the cache
    store logged first; **Part 3, the megafill**, under which this session runs), and the
    copy-text screen v3 `scripts/copy-text-screen-v3.py`;
  - **this round's inputs** (`campaign/fills/b5a/inputs/b5a-fill-unisim/`): the overlay
    `CodeSimulatorOverlay.lean.txt` (your file with the six imports of region (a)), the import
    probe, the route and verdict probes with their seal controls, and the screen population; the
    order list `campaign/fills/b5a/orders/b5a-fill-unisim.txt`, the base sorry set, the screen
    base and the pre-ship log (`campaign/fills/b5a/logs/b5a-fill-unisim-*`).
- **The environment was set up once, at the session's start** (the cover brief; Part 1 of
  `campaign/standards/fill-environment-addendum.md` and its Part 3): the preflight, the
  toolchain, the clone and the cache for the whole queue's Mathlib roots. If Lean cannot start,
  Part 2 applies. **If Lean never runs, do not draft proofs blind.**
- **Branch at exactly that commit, not at the campaign tip:**

  ```sh
  git checkout -b fill/b5a-unisim @ANCESTOR@
  git rev-parse HEAD        # must print @ANCESTOR@
  git rev-parse HEAD:TCSlib/Complexity/TuringMachine/CodeSimulator.lean
  # must print 733a9a463e6bac937ef16ff95a8cb4d287bda725
  # (the base's blob, from git rev-parse)
  ```

  Record the base hash in `REPORT.md`. Never rebase, merge or cherry-pick.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-b5a-unisim.zip`. It contains:
  - `REPORT.md` and the full modified source;
  - a `git format-patch` series against your base, and a git bundle whose only prerequisite is
    your base;
  - **the session's shared environment logs** (`evidence/logs/` at the clone's root: preflight,
    cache store, roots, cache fetch, manifest check), this item's bootstrap and final sweep logs
    with **each module's time and maximum memory**, and the axiom log;
  - the seal test's source, its controls and both outputs; both screen outputs; and
    `SHA256SUMS`.
- **Checkpoint zips.** After each checkpoint below, commit and write `fill-b5a-unisim-cp<N>.zip`
  with the same contents as of that commit (the final sweep may be your module's check only), so
  that a lost workspace loses at most one checkpoint. Deliver the latest if the session ends
  early.

## Base, line numbers and what lands around you

- **Your base's Lean content is the campaign tip ⟨BASE⟩.** Lines in this brief are those of your
  base's tree, where `CodeSimulator.lean` is 8,666 lines (12 public, 185 private): #152's landing
  with #156's and #159's edits to `canonEmitVerdict`.
- **Your first edit makes your file equal to the overlay** (`CodeSimulatorOverlay.lean.txt`): the
  six imports of region (a) after line 15. **Line numbers below are the base's, and the
  overlay's are 6 more** (the stub at 8654, overlay 8660). Every probe and measurement below was
  run on the overlay or at the base, as marked.
- **In flight, merging after your base and invisible to it:** ⟨IN-FLIGHT⟩ (at drafting: #135,
  chapter 7 onto `main`; #156, #159 and #162 are in your base, above); on
  their own branch in this session, the other megafill item, **U2** (`UniversalK`, downstream of
  your file).
  Cite nothing they add.

## Parallel batches this round

None in `CodeSimulator.lean`. U2 runs in this megafill on its own branch, downstream of your file,
and does not cite your target.

## What this is

**B5a's H1: the uniform bounded-acceptance simulator.** One target, frozen:
**`Turing.MachineFormat.exists_uniformSimulator`** (line 8654): for each machine format `F`, one
finite binary machine `S` and one degree `d` such that on `⟨⟨bits t, α⟩, x⟩` it answers `[true]`
if the machine `α` denotes halts on `x` with output exactly `[true]` within `t` steps, and
`[false]` otherwise, within `d · (|α| + |x| + t + 1)^d` steps. **`S` and `d` are uniform in the
code**: no per-code constant (note 34).

**The statement and the docstring's statement and sketch, frozen verbatim** (lines 8552–8580 and
8654–8662; the fill appendices 8582–8651 and the `-/` alone on 8653 are frozen byte for byte too):

```lean
/-- **The uniform bounded-acceptance simulator** (spec, fill pending — batch
B5a): one finite binary machine and one degree such that, on
`⟨⟨bits t, α⟩, x⟩`, the machine answers `[true]` if the machine `α` denotes
halts on `x` with output exactly `[true]` within `t` steps, and `[false]`
otherwise, within `d · (|α| + |x| + t + 1)^d` steps. [AB09, §1.4.1, Theorem 1.9,
time-bounded form; Example 3.6(3)'s uniformity]

**Proof sketch.** Parse the nested input onto tapes: the deadline word
`bits t` on a counter tape, `α` on a table tape, `x` on a buffer tape. Canonize
`α` in place by `Turing.MachineFormat.exists_polyCanonizer` through
`Turing.FinTM.exists_installCallTM`; by `F.serialize_eq` the table is
`serializeK (F.machine (F.decode α))`, of length at most
`max |α| |F.serialize F.fallback|` (`Turing.CodeFormat.serialize_decode_length_le`).
The body is **one step block**: for the current simulated state (unary on a
state tape), input read and `k` work reads, seek the record at index
`q · 3^(k+1) + rank(inp, w)`, read it by the `Turing.codeReadActionK` grammar
(`Turing.codeReadActionK_append`), apply it to `k` mirrored work tapes and the
simulated input head, and update a finite output summary (empty, exactly
`[true]`, other) instead of emitting. Its cost is at most `B · (|table| + 1)`,
independent of `t`, `x` and the tape contents. The block reads the simulated
input through its own input head and is hosted on the buffer by
`Turing.vhostEmitTM` (`Turing.vhostEmitTM_runFrom`); the clock is
`Turing.counterLoopTM` over `bits t` (`Turing.counterLoopTM_run_done`,
`Turing.counterLoopTM_run_escape`), a simulated halt being the live exit. At
`done` the simulated machine is live after `t` steps, so the answer is `false`;
at `escape` it has halted within `t`, and the answer is the summary's
`[true]` test. The ledger: polynomial startup, `t` rounds of at most
`B · (|table| + 1)` (`Turing.counterLoop_time_le`), and the verdict, all at most
`d · (|α| + |x| + t + 1)^d`.
…
-/
theorem exists_uniformSimulator :
    ∃ (S : FinTM Bool) (d : ℕ), ∀ (α x : List Bool) (t : ℕ),
      ((F.toFinTM (F.decode α)).ComputesInTime x [true] t →
        S.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [true]
          (d * (α.length + x.length + t + 1) ^ d)) ∧
      (¬(F.toFinTM (F.decode α)).ComputesInTime x [true] t →
        S.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [false]
          (d * (α.length + x.length + t + 1) ^ d)) := by
  sorry
```

**Where it stands** (the module's status text, lines 56–63, and the fill appendices): the step
block, its hosted counter loop and the one-bit verdict from the prepared round seam are proved
(`h1HostedVerdict_accepts`: from a represented start `d` of the decoded machine on a buffered
input, with `bits t` on the counter, the hosted verdict halts within
`t · (50 (|table| + 1)) + 4t + 2|bits t| + 3` steps, emitting one bit that is `true` exactly when
the decoded machine accepts that input within `t`). **Open:** the nested-input startup, the
canonizer's installation, the assembly and the joint polynomial ledger.

**Proved modulo, exactly:** none. Every row the route composes is admission-free (the import
probe's eight axiom prints). **A complete delivery has no `sorryAx` in your target**, and then
targets 3–8 and `Complexity.baker_gill_solovay` have none from your file.

**Read first:**
- the target's docstring, whose sketch is binding where this brief does not refine it. Two
  refinements: the buffer holds the **window `x.take t`**, not all of `x` (the window copier is
  the published row that places a suffix window; bounded acceptance on the window is bounded
  acceptance on `x` by input locality, below); and the clock and verdict are the landed
  `h1HostedVerdict_accepts`, not a second loop;
- C1's interpreter core `Turing.exists_ndInterpreterCore` and its `**Implementation.**` paragraph
  (`NDCodeSimulator.lean`): **the same startup**, for a replay machine and a per-code constant.
  Its private pieces are the pattern of your phases 1–3, **not citable** (another file's
  privates) **except through their published versions**, the startup kit (below);
- `h1HostedVerdict_accepts` and `StepBlock.hostedLoopTM_run`: your loop's entry configuration is
  `vhostCfg (counterLoopCfg (some (.dec .run)) d (FinTM.bufferTape t.bits) 0) true p []` with
  `d` representing the decoded machine's initial configuration on the window (`StepBlock.Rep`);
- the pre-ship probes (below): their proofs may be copied into your home as `us_` privates.

**Pre-ship check** (the maintainer, re-run at your base; the drafting agent's first run was at the
drafting base; `campaign/fills/b5a/logs/b5a-fill-unisim-preship.log`):
- **The overlay** elaborates with exactly one sorry warning, the target's (overlay line 8660). The
  six imports create no cycle (none of their closures contains your file). Together with every
  module downstream of your file they import without a clash (`ImportClashProbe.lean.txt`:
  0 diagnostics).
- **The import probe** (`B5aUSImportProbe.lean.txt`, a standalone import of your module and the
  six, **157 checks of 157 names**, and 26 axiom prints): 0 errors, 0 warnings. Every print is
  within the standard three axioms (the input rewind, the seam step and the seam runs on two). The
  names are the drafting probe's 109, the review's 28 more (the start's
  `MultiTapeTM.initCfg_with_q₀` and `runFrom_with_q₀`, the `Cfg.init` fields, `stateWord_eq`,
  `seamReleaseTM_runFrom_pos`, R1's frame and field equations, and the definitions the route
  names), the kit's eight, the phase host's four, and the step reader, virtual host and clock of
  the H1 loop. **Re-run it after your delivery**, extended by every further name you cite.
- **The route probe** (`B5aUSRouteProbe.lean.txt`), sealed over 12 TCSlib definitions (the two
  `@[simp]` ones, `MultiTapeTM.initCfg` and `NDTM.initCfg`, also erased): 0 diagnostics. It proves
  `b5a_install` (the polynomial canonizer through the install call: one module, a first return
  at `t ≤ a · ((|α| + 1)^d + |α| + max |α| |F.serialize F.fallback| + 1)` with
  `serializeK (F.machine (F.decode α))` installed), `b5a_locality` and `b5a_accepts_take` (input
  locality for a deterministic machine), `b5a_verdict` (a halt with output `[answer]` gives both
  clauses) and `b5a_table_le` (`|tableBitsK| ≤ max |α| |F.serialize F.fallback|`). The review
  re-ran all five as `us_` privates at your home (region (b)), also sealing `tableBitsK`,
  `pairEncode` and `unaryFin`, which `b5a_table_le` touches: still clean. At your base the same
  home probes (`HomeProbe.lean.txt`, and `HomeProbeSealed.lean.txt` sealed over 18) give only the
  target's sorry warning, on the standard three axioms.
- **The start probe** (`StartProbe.lean.txt`, sealed): `S`'s initial configuration as the first
  phase's transported start, read through `MultiTapeTM.initCfg_with_q₀`, `runFrom_with_q₀`, the
  kit's `Turing.embedSilentCfg_initCfg` and a five-line `Cfg.init` relabelling: 0 diagnostics.
- **The verdict probe** (`B5aUSVerdictProbe.append.lean.txt`, appended to the overlay, sealed over
  4 more): `h1HostedVerdict_accepts` on the window decides bounded acceptance on `x`
  (`b5a_window_verdict`): only the target's sorry warning; the standard three axioms.
- **The seal controls** (`B5aUSSealControl.lean.txt`, 18 `rfl` goals, one per definition sealed by
  the route, verdict and home probes): every one closes unsealed and fails sealed, each at its own
  goal.

## Owned regions and targets (modify these and nothing else)

| # | File:line (base) | Target |
|---|---|---|
| 1 | `CodeSimulator.lean:8654` | `Turing.MachineFormat.exists_uniformSimulator` (frozen statement) |

Your regions:
- **(a) the imports**, as your first edit: exactly these six, after line 15 (the overlay):

  ```lean
  import TCSlib.Complexity.TuringMachine.UniversalStartup
  import TCSlib.Complexity.TuringMachine.Build.Rewind
  import TCSlib.Complexity.TuringMachine.Build.SeamLayout
  import TCSlib.Complexity.TuringMachine.Build.InputWindow
  import TCSlib.Complexity.TuringMachine.Nondeterministic
  import TCSlib.Complexity.TuringMachine.Build.InterpreterStartup
  ```

  No other import.
- **(b) the home**, the blank line 8549, inside `section StepBlockClients` (where `open StepBlock`
  is in force, line 8422), between `h1HostedVerdict_accepts`'s last line (8548) and
  `end StepBlockClients` (8550), inside `namespace MachineFormat` with `F` the section variable:
  your `private` declarations. `private` only, and no `section`, `open` or `variable` that leaks
  past one (`open … in` on one declaration is fine).
- **(c) the body**, the `sorry` on line 8662.
- **(d) for a partial only, a paragraph headed `**Implementation status.**`** at the end of the
  target's docstring, before its `-/` (alone on 8653). It is public-facing library text: what
  is proved and what is open, in mathematical terms, with no campaign labels (brief, gate, finding,
  continuation or escalation names), no dates and no session narrative. The same holds for the
  docstrings of your new declarations; provenance goes in `REPORT.md`. **Every new declaration has a
  docstring, and every proof over 20 lines a literal `**Proof sketch.**` paragraph** (`policy.md`
  §3; the canonizer's and the seam layout's landings each needed a follow-up PR for missing ones).

**Not yours:** every other line, including the target's docstring before (d) (its fill
appendices too: the maintainer rewrites the status text, the module's lines 56–63, the target's
appendices, and `Codes2Tape`/`EXPCOM`'s, at integration; report any text that reads wrong),
every existing declaration (the canonizer and H1's privates included: cite them, adjust none),
and every other file.

### Hosts (binding; the host-first rule, `policy.md` §1, `workflow.md` §2)

- **The loop and the verdict:** cite `h1HostedVerdict_accepts` (your file) or, for its parts,
  `h1HostedVerdict_effect` and `StepBlock.hostedLoopTM_run`. **Never write a second step block,
  counter loop, virtual-input host or verdict.**
- **Compose by the public combinators:** R2 seams (`seamCompTM`, `seamCompTM_run_ofCfg`,
  `seamCompTM_firstReturn_ofCfg`, `seamCompTM_runFrom_left`/`_right`, `seamReleaseTM`,
  `seamReleaseTM_firstReturn`, `seamReleaseTM_runFrom_pos`; the kit's `seamCompTM_step`), R1 and
  R1′ embeddings (`embedEmitTM`, `embedEmitTM_runFrom`, `embedEmitCfg_eq` for the emitting
  verdict; `embedSilentTM`, `embedSilentRetTM`, `embedSilentRetTM_run` for the silent phases).
- **The phase host** is not needed: seams join every phase. If you host a phase in
  `phaseHostTM`, read it only through `phaseHostTM_run`, `phaseHostTM_run_le`,
  `phaseHostTM_tr_of_red_none`, `phaseHostTM_q₀` and `phaseHostTM_tr_of_red_some`.
- **The rows:** the prefix canonizer with the pair extractors (`prefixCanonTM`,
  `prefixCanonTM_eq`, `prefixCanon_complete`, `FinTM.pairExtractTM_fst`/`_snd`); the input rewind
  `Turing.inputRewindTM`/`inputRewindTM_run`; the work-tape rewind `rewindTM_run_ofCfg`; the
  counter copy `copyTM_run_ofCfg`; the window `exists_inputWindowCopyTM`; the install
  `FinTM.exists_installCallTM`; the layout `exists_seamLayoutTM`. **Never write a private input
  rewind** (IR-1 is being retired; `Turing.inputRewindTM` is the published one). Through
  the published kit: `headerCapture_run` (both passes), `exists_windowCall`,
  `installCall_releasePhase`, `exists_layoutCall`, `embedSilentCfg_initCfg`: cite them, never
  re-prove them.
- **Leaves you may write:** none is expected. A further leaf is an escalation.
- **Promotion candidates** (notes only, in `REPORT.md`): the deterministic input-locality lemma
  (`us_locality`; a candidate beside `MultiTapeTM.toNDTM_runWith`).

### The route (binding where it names a row)

Write `M := F.machine (F.decode α)`, `u := pairEncode (bits t) α`, `z := pairEncode u x`. The
machine is chosen before `α`, `x`, `t`; so is `d`.

0. **The first edit**: the six imports (region (a)).
   **The start.** `S.tm` is your seam composite `W` restarted at its first phase's initial
   state (`{ W with q₀ := q }`, `q` the nested `Sum.inl` of the first pass's `q₀`), read only
   through `MultiTapeTM.initCfg_with_q₀` and `MultiTapeTM.runFrom_with_q₀`: no lemma publishes
   `seamCompTM`'s or `embedSilentRetTM`'s `q₀`, so never read them by `rfl`, `show` or `simp`.
   `Cfg.init` at the nested state is the first phase's transported start by the kit's
   `embedSilentCfg_initCfg`, and a relabelling of `Cfg.init` from the `Cfg.init_*` and
   `Cfg.mapState_*` field equations (U2-S's `ss_capture_run` is the pattern).
1. **The header** (checkpoint 1). As in the core's phases 1–5:
   - **pass 1**, `prefixCanonTM (FinTM.pairExtractTM true false)` embedded silently with a first
     live return (`embedSilentRetTM`, `embedSilentRetTM_run`, `MultiTapeTM.exists_first_halt`):
     `bits t` on its capture tape, the native head at the suffix, `2|u| + 3`, time
     `16|bits t| + 8|α| + 25`, independent of `x` (by `prefixCanon_complete`,
     `pairDecode_pairEncode`, `length_pairEncode`);
   - **the input rewind** to `1` by `Turing.inputRewindTM_run` (exact time `p + 1`, every work
     tape, head and the output fixed);
   - **pass 2**, `prefixCanonTM (FinTM.pairExtractTM false true)`: `α` on its capture tape;
   - **the rewind of `bits t`'s tape** (`rewindTM_run_ofCfg` at `n = |bits t|`) and **the counter
     copy** (`copyTM_run_ofCfg`, onto a blank tape at head `0`): the window consumes one counter,
     the loop needs the other.
   Cite the published kit's header passes, capture and seam step for these
   (`headerCapture_run`, `prefixCanon_pairExtract_halt`, `embedSilentRetTM_firstReturn`,
   `seamCompTM_step`).
2. **The window and the locality bridge** (checkpoint 2):
   - **the window** by `exists_inputWindowCopyTM` from the suffix (through
     `exists_windowCall`): `x.take t` on a blank tape, the counter consumed, cost
     `C · (min t |x| + 1) + 2 |bits t|`;
   - **the input rewind** to `1`;
   - **`us_locality`** and **`us_accepts_take`** (the route probe's `b5a_locality`,
     `b5a_accepts_take`; copy them): `(F.toFinTM (F.decode α)).ComputesInTime (x.take t) [true] t
     ↔ (F.toFinTM (F.decode α)).ComputesInTime x [true] t`, by `MultiTapeTM.toNDTM_runWith`,
     `MultiTapeTM.toNDTM_initCfg` and `NDTM.runWith_initCfg_take` at the all-`false` word of
     length `t` (`List.length_replicate`), through `FinTM.computesInTime_iff`.
3. **The table** (checkpoint 3):
   - **the rewind of `α`'s tape**, then **the install**: `us_install` (the route probe's
     `b5a_install`; copy it) gives one module `C`, uniform in the code, with a first positive
     return at `t ≤ a · ((|α| + 1)^d + |α| + max |α| |F.serialize F.fallback| + 1)` and
     `serializeK M` installed (`F.serialize_eq`). Embed `C`'s bank so that its tape `0` is `α`'s
     tape and the rest blank, which is exactly `Cfg.ofWords … (stateWord C.k α)`, behind
     `seamReleaseTM` for the positive first return (`installCall_releasePhase`);
   - **the layout** by `exists_seamLayoutTM` (through `exists_layoutCall`, its source
     word rewritten by `simp only [← serializeK_eq]`; `src` the installed tape, three distinct
     tapes): the table tape `FinTM.bufferTape (tableBitsK M.tr)`, the summary tape
     `StepBlock.summaryCells none (unaryFin M.q₀)` (`serializeK_eq`, `unaryFin_eq`,
     `StepBlock.summaryCells_eq`, `FinTM.bufferTape_of_neg`), its time `C · (|serializeK M| + 1)`.
4. **The loop and the assembly** (checkpoint 4):
   - **the rewind of the window** (its head from `|x.take t|` to `0`);
   - **the loop's entry**: the represented start `d` of `M.initCfg (x.take t)` by
     `StepBlock.Rep_iff` (the mirrored tapes blank with heads at `0`, the table and the summary
     from the layout, the summary head at `0`, the state word from cell `2`), its control
     `StepBlock.exit F.k true`, and the host configuration
     `vhostCfg (counterLoopCfg (some (.dec .run)) d (FinTM.bufferTape t.bits) 0) true p []`, read
     through `vhostCfg`'s and `counterLoopCfg`'s field equations (`counter_cfg_eq`): the buffer is
     the window, the bank the loop's tapes, the counter the second copy of `bits t`;
   - **the verdict**: `us_window_verdict` (the verdict probe's `b5a_window_verdict`; copy it):
     `h1HostedVerdict_accepts` on the window, then `us_accepts_take`. It halts, emitting one bit
     that is `true` exactly when `M` accepts `x` within `t`;
   - **the assembly**: phases 1–3 and the window's rewind are silent; join them by seams; embed
     `h1HostedVerdictTM F.k` by R1 (`embedEmitTM`: it emits), its tapes `[window, the k mirrored
     tapes, table, summary, counter]`. The startup's output is `[]`, so `S`'s output is
     `[answer]` (`List.nil_append`).
5. **The target** (checkpoint 5): `b5a_verdict` (copy it as `us_verdict`) turns the halt with
   output `[answer]` into both clauses at the bound, given the ledger:
   - **the ledger**, uniform: with `N = |α| + |x| + t + 1` and `L₀ = |F.serialize F.fallback|` (a
     constant of `F`), `|bits t| ≤ t` (`length_bits_le_self`) and `|tableBitsK M.tr| ≤ max |α| L₀`
     (`b5a_table_le`), every phase is at most `c · N^e` with `c`, `e` depending on `F` only: the
     passes and rewinds `O(N)`; the window `O(N)`; the install
     `a · ((|α| + 1)^d + |α| + max |α| L₀ + 1)`; the layout
     `C · (|serializeK M| + 1) ≤ C · (max |α| L₀ + 1)` (`F.serialize_eq`,
     `serialize_decode_length_le`), `O(N)`; the loop `t · 50 (max |α| L₀ + 1) + 4t + 2|bits t| + 3`,
     `O(N^2)`; the seams and the verdict step `O(1)`. Take `d ≥ ` the sum of the coefficients and
     the largest exponent, and close with `ComputesInTime.mono`.
6. **Edge cases that must stay true of your proof:**
   - `t = 0`: `bits 0 = []`, the window and both counters empty; the loop runs no round, and `S`
     answers `[false]`, since an initial configuration is live (`summaryClock_zero`);
   - `|x| < t`: the window copy stops early; `x.take t = x`;
   - a code `α` whose decoding is `F`'s fallback (which need not reject): `F.decode` is total, and
     the simulation runs the fallback (note 34);
   - `α = []`, `x = []`: the rewinds of empty words take `2` steps.

**Do not run the canonizer through `prefixCanonTM`'s time bound**; the canonizer runs inside the
install call, whose bound is polynomial (`b5a_install`). **Do not copy** `UniversalK`'s `ss_`
startup or `Diagonalization/NTimeHierarchy`'s `un_` setup, and do not re-prove the published
kit's eight startup facts: cite them.

## Gate guidance (binding)

- **The wave-1 statement gate**, note 34: the quantifier order is binding (`S` and `d` before
  `α`, `x`, `t`); per-code constants would not suffice for `EXPCOM`. The deadline is inclusive: a
  halt at step `t` is accepted at deadline `t` (`summaryClock_accepts`).
- **The H1 harvest gate** (`campaign/gates/20-h1-harvest-statements/`): cite the hosted loop and
  its reading lemma as stated.
- **The seam layout's gate** (gate 46: `campaign/gates/43-seam-layout-statements/`, round 2):
  its time is chosen before the configuration; cite it as stated.

## Cited infrastructure (public and proved at the issue commit; all in `B5aUSImportProbe.lean.txt`)

The probe's 157 names: the target, the format and the canonizer; the header passes and the
capture; the rewinds and the counter copy; the window and deterministic input locality; the
install and the layout; the loop's entry and the hosted loop with `vhostCfg`'s and
`counterLoopCfg`'s equations; composition and embedding; the model's run algebra and field
equations. In your file you also cite the canonizer, `h1HostedVerdictTM`,
`h1HostedVerdict_effect`, `h1HostedVerdict_accepts` and `summaryClock_*`.

## Ground rules (binding)

1. **File ownership, by region.** Only regions (a)–(d) of `TuringMachine/CodeSimulator.lean`.
   List every new declaration with its role.
2. **Statement freeze** over every landed declaration and the target: no renames,
   re-signatures, restatements or attribution edits.
3. **No new public declaration.** No status text outside (d).
4. **Escalation, item by item:** on anything unprovable as stated, including a cited row that
   does not compose as the route says, stop **on that item only**, record the obstruction
   mathematically, and continue with every item that does not depend on it.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports.** Exactly the six of region (a). A Mathlib
   import only if a needed lemma requires it; flag it.
7. **One proof per shared argument.** Never re-walk a landed contract (the canonizer's, H1's, the
   core's). Never write a second host, loop, seam, embedding, input rewind, prefix parser or
   layout machine.
8. **Size.** No cap; file size alone is not a driver. Report the final line count and the public
   and private declaration counts (base: 8,666 lines; 12 public, 185 private).
9. **Continuation budget.** A partial zip states the checkpoints reached, the open declarations
   (each with a literal "Proof sketch"), and the target's axiom walk. A partial is expected and
   fine; an unreported gap is not.
10. **The pinned base, and no unfolding (user, 2026-10-16).**
    - Cite only declarations public at your base, and your file's own privates.
    - **Never unfold a definition of another file**, and **no definitional closure either**: a
      `rfl`, `exact`, `show`, `decide`, `simp` or `simpa` step that closes only because another
      file's definition reduces counts as unfolding. Read `prefixCanonTM` only through
      `prefixCanonTM_eq` and `prefixCanon_complete`; `vhostCfg` and `counterLoopCfg` only through
      their field equations and `counter_cfg_eq`; `Cfg.ofWords` and `stateWord` through theirs;
      `serializeK` through `serializeK_eq`; `MultiTapeTM.toNDTM` through `toNDTM_runWith` and
      `toNDTM_initCfg`; `rewindTM` only through `rewindTM_run_ofCfg`.
    - **Scope (user, 2026-10-23):** this binds TCSlib's own definitions. Core and Mathlib
      definitions may reduce in a `rfl`, `decide` or `show` step, but are never passed to `simp`,
      `rw` or `unfold`; use their equation lemmas (`Bool.toNat_true`, not `simp [Bool.toNat]`;
      `List.nil_append`, not `simp [List.append]`).
    - **The machine model's primitives** (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
      `Cfg.mapState`) are read through their lemmas. Unfold `step` and `Action.apply` only for a
      leaf defined in your own file. `phaseHostTM`'s table is read through `phaseHostTM_run`.
    - Your own file's definitions may be unfolded (`MachineFormat.toFinTM`, H1's privates, your
      `us_` declarations).
    - If a fact you need about another file's definition has no published lemma, **stop on that
      item and escalate** (ground rule 4), naming the lemma you need.
    - **Self-check by both methods** (neither alone is complete):
      - a **seal test**: a scratch copy of your module with `attribute [local irreducible]` on
        every other-file TCSlib definition your new proofs mention (start from the pre-ship's 16
        and extend by every one you reach), and `attribute [-simp]` on the `@[simp]` definitions
        among them (`MultiTapeTM.initCfg`, `NDTM.initCfg`, `Cfg.init`, `Action.apply` if
        reached), which must still elaborate, **with controls**: for each sealed definition, a
        goal that closes by `rfl` with nothing sealed and fails under the seal;
      - an **inspection table** of every `rw`/`simp`/`simpa`/`dsimp`/`unfold`/`show`/`change`
        argument in your diff, each other-file name classified (a theorem, or a definition: a
        finding).
      - **Ship the raw outputs** of the seal and its controls, with their commands and exit
        statuses. **A seal not run, or a seal without controls that fail sealed and close
        unsealed, is a checklist failure** (megafill A's interpreter core ran none, and six steps
        closed only by unfolding).
    - List every declaration you cite outside your file. If you cite more than the probe's list,
      add them to a copy of the probe and run it.
11. **MIG-1 compatibility.** Keep `canonPreserveInstall` byte-identical. Cite none of the six R3
    rows anew (`copyTM_run`, `transferTM_run`, `clearTM_run`, `compareTM_run`,
    `incrementTM_run_succ`, `incrementTM_run_overflow`); use their framed `_ofCfg` forms. Cite no
    private declaration of another file. Keep your new privates under the `us_` prefix (unused in
    the tree at the drafting base).

### Checkpoints (for a partial; ground rule 9)

The route's checkpoints 1–5. Each may land alone. **Add no new admission:** a component you state
for yourself goes in only once proved. The freeze check for a partial is the **axiom walk**:
`sorryAx` reaches the headline only through its own body.

## Duplication governance (binding)

Run the text-level screen **before and after**, **one run at a time, under `nice -n 10`**
(`campaign/standards/TEMPLATE.md` failure mode 5; `policy.md`, **Duplication**). Run the before
screen after your first edit: it must equal the screen base (the overlay changes only imports).
- **The population** is 57 files
  (`campaign/fills/b5a/inputs/b5a-fill-unisim/screen-population.txt`): continuation 7's 45, the
  route's new imports (`Build/InputRewind`, `Build/Rewind`, `Build/InputWindow`,
  `Build/SeamLayout`, `BufferWords`, `Nondeterministic`), the two model files whose lemmas the
  route reads (`Configuration`, `StateRenaming`), the kit's module, and the remaining
  hazards: `Diagonalization/NTimeHierarchy` (UN's setup), `UniversalK` (U2-S's startup) and
  `ClassNP/ExhaustiveReplay` (IR-1's remaining input rewind). It contains `Simulation` and
  `Build/InputRewind` (the megafill A lesson for any item near an input rewind).
- **The screen** is `scripts/copy-text-screen-v3.py`, on the repository paths.
- **The base** is `campaign/fills/b5a/logs/b5a-fill-unisim-screen-base.txt`: **2,756
  declarations, 3,005 pairs, 973,130 characters** (MEASURED at the drafting base; 87 minutes under
  `nice -n 10`). 99 pairs have a declaration of your file on one side: 58 within it (four at 90%
  or more, all CC7-1's: the cut-leg pair and two leg-template pairs), 41 across files.
- **The screen is long:** start the before run in the background right after your first edit (it
  may run beside the one Lean process, never beside another screen), and the after run as soon as
  the owned file is final. Run each on a frozen copy of its commit (`git worktree add <dir> HEAD`,
  the screen's root `<dir>`), so that later edits cannot race its reads. Expect the after run to
  be longer than the before run: your target's body, `sorry` at the base and so not screened,
  becomes one of the largest screened declarations.

```sh
P=campaign/fills/b5a/inputs/b5a-fill-unisim
nice -n 10 python3 -I scripts/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-before.txt
# after your changes, again, only when the first run has finished
nice -n 10 python3 -I scripts/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-after.txt
```

- **No new cross-file pair** with an owned-file declaration on one side.
- **Recorded, add nothing to them:** CC7-1 (the canonizer's cut-leg, leg-template and per-record
  families), the earlier canonizer in-file pairs, and the uniform-code mirror pair.
- **Known hazards** (a proof reproducing one at 90% or more must be factored if both sides are
  yours; if the other side is another file's, stop on that item and escalate):
  - **the startup kit's proofs** (`Build/InterpreterStartup`, harvested from `NDCodeSimulator`'s
    startup), `NDCodeSimulator`'s `ic_time_ledger` and the core's twelve-phase assembly: the same
    mathematics; cite the kit, never re-walk it;
  - UN's setup (`un_step'`, `un_canon_halt`, `un_setup`) and U2-S's startup
    (`ss_capturedPrefix_run`, `ss_capture_run`, `ss_serialized_layout`), the other header passes;
  - the start identity: `UniversalK`'s `ss_captureInitial` and `ExhaustiveReplay`'s `xr_E_initCfg`
    (the `initCfg_with_q₀` idiom);
  - **the core's startup assembly** (`exists_ndInterpreterCore`'s body, its twelve phases at lines
    983–2049): your target's body will be compared with it. ⟨D-3: the user's ruling⟩ A pair
    below 90% is pre-disclosed: list it with its shared fragments; at 90% or more stop and
    escalate;
  - the input rewinds of IR-1 (`xr_inRewindTM`, `ss_inputRewind`): cite `Turing.inputRewindTM`;
  - the first-halt captures (`Build/CertShell`'s `certCore_run`); the R1 reconstruction family
    (cite `embedEmitCfg_eq`); `Cfg.mapState_mapState`'s field-equation idiom (two idiom pairs
    already accepted, UN's and the core's: say so if yours is a third).
- List every new in-file pair with a one-line justification. Quote both outputs in `REPORT.md`,
  which carries **"new copies: none"** (or lists each pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; the cache **for the queue's Mathlib roots only** (addendum v2.5,
  fetched once at the session's start; your order list's modules import 41 roots directly, at the
  overlay as at the base); **never `lake build`**, and never the unfiltered `lake exe cache get`.
  Use `scripts/lean_check_tree.sh` for every check, one Lean process at a time.
- **Re-bootstrap** (addendum Part 3, item 3.2) from `campaign/fills/b5a/orders/b5a-fill-unisim.txt`
  (**120 modules**, computed on the overlay: the base list's set, with `Build/Rewind`,
  `BufferWords`, `Build/SeamLayout`, `Build/InputWindow` and `Build/InterpreterStartup` now before
  your file), **after your
  first edit**, logging each module's start and end time and maximum memory. **The base
  sorry-warning set has 30 entries in 14 modules**
  (`campaign/fills/b5a/logs/b5a-fill-unisim-base-sorries.txt`). Yours is `CodeSimulator`'s only
  one. Record the base list by name first, and report any difference.
- **Final checks:**
  1. `CodeSimulator`: zero errors, **no sorry warning** (for a partial, exactly the target's), and
     no other warning in anything you added.
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's
     minus yours (30 for a complete delivery).
  3. Re-run `B5aUSImportProbe.lean.txt` (extended by your citations) and the inherited probes:
     continuation 7's import probe
     (`campaign/fills/b5a/inputs/b5a-fill-canon-cont7/CanonCont7ImportProbe.lean.txt`), the
     statements probe (`campaign/gates/wave1-statements/evidence/B5aStatementsProbe.lean.txt`)
     and the note-50 file (`campaign/fills/b5a/evidence/b5a-canon-cont4/CanonNote50.lean.txt`,
     whose `note50_cases` is admission-free since the canonizer's landing): 0 errors.
- **Axiom prints**, within `[propext, Classical.choice, Quot.sound]`, for the target, every new
  private (in an in-module probe), `exists_polyCanonizer`, targets 3–8 and
  `Complexity.baker_gill_solovay`. At the base the target is the only admission of targets 3–8
  and Baker–Gill–Solovay (the review's admission walk), so for a complete delivery all of them
  print within the standard three.
- **Lint:** `python3 -I scripts/campaign_style_lint.py` over `TCSlib/Complexity/TuringMachine`
  (base: 0 FAIL, 68 WARN over 83 files; `CodeSimulator`'s are its size and three public
  definitions without a lemma, `MachineFormat.toFinTM`, `codeSkipTableK`, `oneTapeMachineFormat`)
  and `TCSlib/Complexity/Diagonalization` (base: 0 FAIL, 2 WARN over 5 files), 0 FAIL. Add no
  line over 100 characters and no Lean linter warning in your region.

## Out-of-scope sorries you will see (leave every one untouched)

Everything in the base sorry set except your target: MIG-1 stage S's sorried specs
(`Simulation`, `Composition`, `Encoding`, `ClassP/TimeConstructible`, `Build/Wrappers`,
`Build/Loop`, `Build/Primitives`); `Build/RecordTable`'s four rows; `Build/ZoneRebalance`'s two;
`NDCodeSimulator`'s `exists_replayCanonizer`; `UniversalK`'s two; `ClassNP/NDNormalForm`'s,
`Diagonalization/NTimeHierarchy`'s and `Diagonalization/NTimeDiagonalizer`'s. If a proof seems to
*need* one of these beyond a named citation, that is an escalation, not a license.

## REPORT.md checklist

- [ ] The session's shared preflight and cache numbers (quoted from its logs, the cache store's
      log included), **the shared logs copied into this zip**, this item's bootstrap with
      per-module time and memory, and the base blob check.
- [ ] The overlay as the first edit, byte for byte; nothing else outside regions (b)–(d).
- [ ] The checkpoints reached (1–5); the base hash and the ancestor check; the checkpoint zips.
- [ ] Every new declaration with its role; the tapes chosen for each phase; the status paragraph,
      if a partial; for a complete delivery, a proposed `**Implementation.**` paragraph for the
      target's docstring (public-facing; the maintainer edits it in at integration).
- [ ] The ledger, phase by phase, and the final `d`.
- [ ] Promotion candidates, requested shared lemmas and escalations (each stated
      mathematically), or "none".
- [ ] Rule 10: the declarations cited outside your file (from an elaborated-constant walk), the
      probe re-run as "N checks of M names", **the seal test with its controls and both raw
      outputs**, and the inspection table. Rule 11: `canonPreserveInstall` unchanged; a grep of
      your diff for the six R3 rows and for other files' private names.
- [ ] Duplication: both v3 screens, every new pair justified, "new copies: none" otherwise.
- [ ] File size; the final sweep tail; the re-run probes; every axiom print; the lint lines. The
      diff touches only your owned regions.

## Known pitfalls at this pin (hard-won)

- **`Cfg.inputPos` is shifted by one.** In `pairEncode u x` the suffix `x` starts at index
  `2|u| + 2`, native position `2|u| + 3` (`= 4|bits t| + 2|α| + 7`), where `prefixCanon_complete`
  leaves the head and where the window copier must start.
- **`pairEncode` doubles its first component:** `u` takes `2|u|` cells, then `[false, true]`.
- **The hosted verdict's tapes** are `1 + (F.k + 2 + 1)`: the virtual-input buffer first, then the
  loop's `F.k + 2` body tapes and the counter last (`vhostBank`, `Fin.castSucc`); the summary's
  bank tape is `vhostBank (summaryTape F.k).castSucc`.
- **The loop's entry control** is `StepBlock.exit F.k true` (a sigma: rewrite it with `exit_true`
  and `exit_false`), and the counter starts at `counterLoopCfg (some (.dec .run))`.
- **The seam layout's three tapes must be distinct**, and it clears `src`: install the
  serialization on a scratch tape, not on a tape you still need.
- **The simps field equations are pointwise** (`Cfg.mapState_*`, `vhostCfg_*`, `embedSilentCfg_*`,
  `Cfg.init_*`, `Cfg.ofWords_*`): `funext` before `simp`/`rw`, or the step closes by unfolding and
  the seal rejects it.
- **`MultiTapeTM.initCfg` and `NDTM.initCfg` are `@[simp]` definitions:** an unrestricted `simp`
  unfolds them; erase them in the seal and use `MultiTapeTM.initCfg_eq` and
  `MultiTapeTM.toNDTM_initCfg`.
- **Locality is for the run, not the machine**: `NDTM.runWith_initCfg_take` is stated with
  `let`s; `simp only [MultiTapeTM.toNDTM_runWith, MultiTapeTM.toNDTM_initCfg,
  List.length_replicate] at h` exposes the two runs (the route probe).
- **`S` starts from `S.tm.initCfg`**, unlike the core's explicit start: see the route's start
  (`initCfg_with_q₀`, `runFrom_with_q₀`); the composite's `q₀` has no other published equation.
- **H1's proofs predate rule 10**: `h1HostedVerdict_effect` passes `MultiTapeTM.initCfg`,
  `Cfg.init`, `FinTM.VirtualTag`, `Action.apply` and `vhostCfg` to `simp` and unfolds
  `MultiTapeTM.step` (8497–8526). Cite it; do not imitate its proof text.
- **`prefix` is a reserved keyword**; do not name a hypothesis `prefix`.
- **Phase-indexed configurations do not match by `rw`**: close by `exact`.
- **`counterLoopOrbit` is an `abbrev`:** `rw` may not fire on it; `exact` and `simp only` do.
- `omega` with products and powers as atoms (`ring` first). The linter needs a literal "Proof
  sketch" before every `sorry` (partial only).
