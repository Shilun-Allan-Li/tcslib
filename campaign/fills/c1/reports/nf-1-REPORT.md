# C1 normal form — final partial delivery through checkpoint 2

**Partial, checkpoints 1–2 of 8 completed. The target theorem is not proved.** The only admission in
the owned module remains the original body of
`Turing.FinNDTM.exists_codeNDTM_accepts_linear`. No new helper is admitted or depends on
`sorryAx`. Checkpoints 3–8 remain open. This archive is the final partial delivery of this run, with a continuation plan; it is not a
claim of the linear simulation theorem.

## Pin, inputs, ownership, and delivery

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Initially checked out `complexity/arora-barak-ch3-4`; the required ancestor check exited 0.
- Working branch: `fill/c1-nf`, created at exactly
  `951251f641f9e2436429c282e4e199a9c9b79420`. No merge, rebase, cherry-pick, push, or PR.
- Base owned-file blob: `5150734a89b935396dee9516911030497f2034d1`, verified before edits.
- Final source commit: **4af97d4679f8024ea5bcbf11c04d1e4e5e0373cb**.
- Checkpoint 1 was committed as `2dc36b95d04a8095a4419304602f5308dcaf953a` and delivered immediately as `fill-c1-nf-cp1.zip` (SHA-256 `607146950672fd41c46e887a81454ea0a1321752a28fd3901a99fa695b1b042e`). Checkpoint 2 adds the second commit and patch.
- Brief SHA-256: `a37eaed4ee429bb6ea7a94009b82fa1184290e95cc92785ec39664da3af770d9`.
- Environment addendum v2.6 SHA-256:
  `9f5bd5e74bb767e50a6e7a372e98a5567998ec14be432c1dfb7ff8856eb9bd28`.
- Only tracked modification: `TCSlib/Complexity/ClassNP/NDNormalForm.lean`, and only its
  four authorized regions. First edit was the supplied import overlay, byte-for-byte.
  Imports are exactly the original two plus `Build.NDHost` and `Build.StepBlock`.
- The target's signature and body are unchanged. Its permitted status phrases and the
  permitted module status text are now public-facing. The rest of its original sketch is
  intentionally untouched; the refined implementation paragraph below is proposed only.
- Comment-aware census: 88 → 752 lines; 1 → 1 public source declarations, 0 → 39 private
  declarations. No instance declarations or derived instances were introduced. The 39 privates are 28 theorems, 9 definitions, and 2 abbreviations.
- Checkpoint 2 was delivered immediately as `fill-c1-nf-cp2.zip` (SHA-256 `0979a110a4b70c6a8549ffc67abcd8fa31a5ea6651c6cd01e66c57ea1e955107`). The final source is the same commit, without a third proof commit.
- The patch series is against the exact base; the bundle has that base as its only
  prerequisite. Source, evidence, probes, and checksums are included. No build products.

## Environment and process evidence

Part 1 ran before cloning, fetching, or running Lean. `preflight.log` records 9 processors,
63,763,922,944 bytes (59.385 GiB) free on the disk-backed clone filesystem, and
9,770,741,760 bytes (9.100 GiB) available memory. Cgroup memory files were absent, so the
addendum's `/proc/meminfo` fallback was used. `/tmp` and `/home/agent` are tmpfs; the
toolchain, archive store, temporary files, and all build products used the clone filesystem.

The unmodified official Lean 4.25.0 executable ran normally. Part 2's fallback was therefore
not used. Toolchain archive SHA-256:
`97bee7bda676ca54f4b1cebe323242a08323d75134fecd1ba31cee4db66abb8a`.

Exactly **39 Mathlib roots** were supplied to the cache command. The first attempt was
interrupted during the initial dependency clone after the cache-store log exposed the
default tmpfs location. No mathlib archive store existed there and no archives were fetched
there. The incomplete clone had no HEAD. The single authorized cleaned retry removed this
session's new package checkouts and compiled Lake configuration; its preflight recorded
8.843 GiB available memory and 55.564 GiB free disk. The retry used a new disk-backed
`XDG_CACHE_HOME`, fetched and unpacked **1,007 files**, and ended:

> Decompressing 1007 file(s)
> Unpacked in 3992 ms
> Completed successfully!
> cache-get-clean-retry exit=0

The manifest check found **11 present packages matching URL and revision, 0 mismatches**,
and 4 absent packages (`doc-gen4`, `UnicodeBasic`, `BibtexQuery`, `MD4Lean`). The order list
imports none of the absent packages. No zero-byte olean was found. Package source was not
patched, no missing product was fabricated, and no dependency cache was copied elsewhere.

Every Lean check used `scripts/lean_check_tree.sh`, one at a time. There was no `lake build`
or unfiltered cache fetch. The supplied 112-module bootstrap passed; `bootstrap.log` records
every module's start/end UTC times, elapsed seconds, and maximum RSS. The maximum recorded
bootstrap module RSS was 3,000,872 KiB. There were exactly the 20 expected base sorry
warnings. Both checkpoints were validated with the full 46-module tail. The final delivery additionally passed all 112 modules from the pinned order, with the after screen alongside it. Every log included is complete, or explicitly identifies an interrupted/expected-failure experiment.

Two process details are disclosed in `process-notes.log`: `/usr/bin/time` was unavailable,
so resource accounting uses Python `os.wait4`/`resource`; and logs created before cloning
are exposed at the clone root through an `evidence` symlink, without moving a log being
written. The first screen launch exited 127 before Python started; its subsequent run was
the sole actual before screen. The first interrupted cache run and all unsuccessful scratch
proof checks are included and labeled by their actual exit statuses.

## Completed construction and declarations

Checkpoint 2 implements sweep zero as a finite bit fold and proves its record-prefix, whole-record, multi-record, genuine-run, and scan laws. It proves that a display whose branch first halts at its end with output `[true]` passes the control check. It does not yet verify the input or work-tape claims.

The record width is `W = 2 * N.k + 4`. Slot 0 is the branch choice; read `i`, input first,
uses slots `2*i+1` and `2*i+2`; slot `2*N.k+3` is the end flag. Presence/value codes are
`00` for blank, `10` for false, and `11` for true. `nf_decode` maps the unused `01` code to blank; `nf_decode_absent` proves this choice.

`nf_display N x w` encodes the read configuration before each choice in `w`. It sets only
the last record's flag. It is defined for every word, not only accepting or first-halting
words; the forward transfer must still select the first-halting prefix before using it.
States and actions are not recorded or guessed.

The controller has type `Fin W × Bool`: position and last completed flag. It resets to
position zero and stores the bit on the final slot; otherwise it increments the position.
It stops exactly at position zero with a true saved flag.

| Private declaration | Role |
|---|---|
| `nf_pack` | Exact CodeNDTM packaging through finite relabeling; copied from `nfr_pack` as directed. |
| `nf_setup` | The trivial setup's five hypotheses at time zero; copied from `nfr_setup` as directed. |
| `nf_ctlStep` | Display-controller transition. |
| `nf_ctlStop` | Display-controller stopping predicate. |
| `nf_ctl_position` | Folded position equals prefix length modulo the width. |
| `nf_ctl_stop_iff` | Stopping iff nonempty, whole-record length, and true last bit. |
| `nf_record` | Fixed-width choice/read/end encoding. |
| `nf_record_last` | End-slot equation. |
| `nf_record_choice` | Choice-slot equation. |
| `nf_record_read` | Presence and value equations for each claimed read. |
| `nf_display` | Complete bit display of a branch word. |
| `nf_display_length` | Length is `W * w.length`. |
| `nf_display_flag` | Record-end bit is true exactly on the last record. |
| `nf_display_firstStop` | Every nonempty displayed branch first stops at its end. |
| `nf_firstStop_records` | Every first-stopped stream is a positive number of records, with only the last flagged. |
| `nf_display_prefix_length` | Displaying the first `t` choices uses exactly `W*t` bits when `t ≤ w.length`. |
| `nf_decode` | Presence/value decoder, with `01` mapped to blank. |
| `nf_decode_record` | Encoding then decoding recovers each claimed read. |
| `nf_decode_absent` | A false presence bit decodes to blank independently of its value bit. |
| `nf_Control` | Finite simulated state, output summary, and failure flag. |
| `nf_SweepState` | Finite parser position, finite optional-bit record buffer, and control data. |
| `nf_complete` | Recompute a record's action and check the end flag, updating the summary. |
| `nf_sweepStep` | One-bit parser update, with completion at the last position. |
| `nf_sweepInit` | Initial parser and original machine state, empty output, no failure. |
| `nf_sweepPass` | Complete boundary, halted simulated state, accepting summary, and no failure. |
| `nf_complete_record` | Completion equation on an encoded record. |
| `nf_complete_failed` | Failure is irreversible. |
| `nf_complete_other` | A rejecting output summary is irreversible. |
| `nf_sweep_prefix` | A proper record prefix stores precisely its read bits, without changing control data. |
| `nf_sweep_record` | A full record resets the parser and applies exactly one completion update. |
| `nf_complete_output` | Completion incorporates the optional emission, including on halting transitions. |
| `nf_sweepPass_output` | An accepting summary means output exactly `[true]`. |
| `nf_sweep_run` | Published scan-fold specialization: first done at `2*|s|+2`, with all tape/head/input/output data unchanged. |
| `nf_sweep_records` | Concatenated records become a fold of completion updates. |
| `nf_display_records` | Existing display equals concatenation of its fixed-width records. |
| `nf_sweep_display` | Display's bit fold is its record fold from the prescribed initial data. |
| `nf_complete_step` | Completing a genuine live record agrees with the real next state and output. |
| `nf_sweep_control_prefix` | Every prefix of a first-halting display has the genuine state/summary and no failure. |
| `nf_sweep_display_pass` | A first-halting accepting branch display passes sweep zero. |

Every declaration has a docstring, and every proof longer than 20 lines has a literal
`**Proof sketch.**` paragraph. No hand-built machine, new host, replay leaf, or writer has
been introduced. The sweep uses `scanTM 2 0 (scanFold (nf_sweepStep N)) scanKeep (nf_sweepInit N)`; its finite state has both `Fintype` and `DecidableEq`, checked by inference in the scratch seal probe. The display and controller are finite data operations, not alternate
implementations of the catalog rows.

## Verification and axiom boundary

- Full 112-module bootstrap: pass; 20 base sorry warnings, no other warning introduced.
- Full final 112-module sweep: **pass, 112/112 modules, zero errors; all 20 base sorry warnings and all 596 warning messages match the bootstrap exactly by module. Summed module wall time: 1,210.759 seconds; peak module RSS: 2,953,440 KiB. The fresh final axiom, seal, and import-probe reruns also passed (3/3)**.
- Full 46-module tail after the proof edit: **pass, 46/46 modules, zero errors; exactly 3 expected sorry warnings (the target and two in NTimeDiagonalizer), with all 205 warning messages matching the bootstrap module-by-module**.
- Owned module: exactly the target's sorry warning, zero errors, no other warnings.
- Axiom prints for all 39 privates: subsets of `[propext, Classical.choice, Quot.sound]`.
- Target axiom walk: **`[propext, sorryAx, Classical.choice, Quot.sound]`; the target is the sole direct local user of `sorryAx`**. No helper has a `sorryAx` dependency.
- Public-constant census: **only the original target, with no new public constant, compiler auxiliary, or derived instance from the owned source**.
- Extended import probe: **578 checks of 577 names, zero errors; two probe-only deprecation warnings identify the existing omega-generated `Int.ofNat_mul` and `Int.ofNat_nonneg` references**.
- Lint: `style_lint: 0 FAIL, 17 WARN over 21 files`, exactly the baseline; policy linter
  `0 findings in 1 files`. No source line exceeds 100 characters.
- Statement/census check: 1 public declaration before and after, no public addition/removal,
  unchanged target statement; 39 new private declarations only.

The base sorry set, untouched, is also shipped as `base-sorries-by-name.txt`:

| Module | Declarations |
|---|---|
| `TuringMachine/Simulation` | `branchTM_spaceUsed` |
| `TuringMachine/Composition` | `idTM_computes`, `ifEqTM_computes`, `condTM_computes_iff` |
| `TuringMachine/Encoding` | `pairDiagTM_computes` |
| `ClassP/TimeConstructible` | `Turing.FinTM.lengthBitsTM_computes`, `Turing.FinTM.lengthBitsTM_spaceUsed` |
| `TuringMachine/Build/Wrappers` | `timedCondTM_computes`, `timedCondTM_spaceUsed` |
| `TuringMachine/Build/Loop` | `loopHostTM_contracts`, `loopHostTM_decides`, `loopHostTM_finds`, `loopHostTM_spaceUsed_le_budget`, `emitLoopTM_computes` |
| `TuringMachine/Build/Primitives` | `polyUnaryTM_spaceUsed`, `unaryTokenTM_computes`, `appendBitTM_computes` |
| `ClassNP/NDNormalForm` | `exists_codeNDTM_accepts_linear` |
| `Diagonalization/NTimeDiagonalizer` | `exists_queryTM`, `exists_diagonalizer` |

## No-unfolding and citation evidence

`evidence/external-constants-cp2.tsv` lists all **463 external constants** reached by walking
the elaborated new declarations, recursively through their own local auxiliaries. The
walk stops at imported constants and records each constant's module and kind. It includes
the core proof machinery and generated theorem references, not just hand-written names.
The explicit invocation list also includes the field equations erased by elaboration.

The 39-definition seal removes the four designated definition simp rules and makes every
required non-projection definition irreducible. It passes on the new declarations and on
the exact owned-source copy. All **39 controls pass unsealed and fail sealed**. The two
fiber-sensitive controls also fail at their `rfl` with `CtlState` unsealed, as required.
Sources and raw commands, exit statuses, and diagnostics are shipped. The extra experiment
sealing the structure projections failed at attribute installation because Lean marks
those projections reducible; no unsafe override was used. The original ten-projection experiment is disclosed in
`cp1-strong-seal.log`; the additional `Action.output`, `Action.state`, and `NDTM.tr` projection experiment is in `cp2-projection-seal.log` and is not counted as a successful seal.

`evidence/inspection-cp2.md` inventories every rewrite/simplification/reduction argument in
the added code, including `rwa`. All explicit other-file rewrite arguments are published
theorems. Own definitions are reduced explicitly; no other-file definition is passed to
`rw`, `simp`, or `unfold`. The six forbidden R3 rows and named foreign-private families
have no matches; the constant walk contains no imported `_private` name. No own leaf
exception to the primitive no-unfolding rule is used.

## Duplication evidence

The before screen ran on a frozen worktree at the exact base, under `nice -n 10`, beside
the serial bootstrap. Its output is byte-identical to the supplied base screen:

> declarations screened: 1351; copy pairs (target reproduces >= half of source): 865; reproduced text: 274,870 chars

It completed in 1,513.873 seconds, maximum RSS 799,200 KiB. The final after screen ran once, under `nice -n 10`, on a separate frozen worktree at checkpoint 2.

The after screen completed successfully in 1,487.279 seconds, maximum RSS 800,772 KiB:

> declarations screened: 1379; copy pairs (target reproduces >= half of source): 866; reproduced text: 274,994 chars

There is exactly one new cross-file pair and no new in-file pair; no old pair disappeared.
The screen reports `NTimeHierarchy.lean::un_setup` reproducing
`NDNormalForm.lean::nf_setup`: 124/218 characters (57%). Its exact normalized shared tiles are:

- `MultiTapeTM.initCfg_eq,Cfg.init_workTapes]·`
- `rw[MultiTapeTM.initCfg_eq,Cfg.init_state]`
- `MultiTapeTM.initCfg_eq,Cfg.init_workTape`

**Disposition: idiom.** These are invocations of the published initial-configuration field
equations for the state and blank work tapes; the composite setup theorem `un_setup` is
not re-derived, and the brief explicitly directs transcription of `nf_setup` from its probe.
The raw pair and extracted tiles are in `evidence/screen-new-pairs.json`; both full screen
outputs and their timing logs are shipped. The tile extraction inspected only the new pair
and did not repeat the full screen.

Semantic name and statement searches cover the entire base tree and both open PR heads
retrieved for this run: #176 at `cecd76a0f996411d5371f91e8d4e3757e122fd60` and #177 at
`2c21370875a576db9b2d72967f75058e20eb4a19`. Neither branch is merged or imported. The raw
searches and PR inventory are included. Each new lemma was also separately submitted to
`exact?` before its own declaration was present, with a 200,000-heartbeat search bound.

| Lemma | Name/statement search | `exact?` result |
|---|---|---|
| `nf_pack` | Finite CodeNDTM packaging and relabeling statements; only supporting APIs found. | No closure. |
| `nf_setup` | Zero-time run and blank initial-tape conditions; only supporting APIs found. | No closure. |
| `nf_ctl_position` | Modular position of a fold and record-width controllers. | No closure. |
| `nf_ctl_stop_iff` | Fold stopping and last-bit conditions. | No closure. |
| `nf_record_last` | Record end flags and final-slot equations. | No closure. |
| `nf_record_choice` | Choice fields and first-slot equations. | Only `exact rfl`, reducing this file's own encoder; no published lemma. |
| `nf_record_read` | Record-read and presence-bit equations. | No closure. |
| `nf_display_length` | Fixed-width display lengths. | No closure. |
| `nf_display_flag` | Display flags and record-end positions. | No closure. |
| `nf_display_firstStop` | Displays and first-stop contracts. | No closure. |
| `nf_firstStop_records` | First-stopped streams and complete records. | No closure. |
| `nf_display_prefix_length` | Prefix displays and their lengths. | No closure. |
| `nf_decode_record` | Decoder/record/presence statements. | No closure. |
| `nf_decode_absent` | Blank decoding and unused code statements. | No closure. |
| `nf_complete_record` | Recomputed actions and control records. | No closure. |
| `nf_complete_failed` | Irreversible failure and record updates. | No closure. |
| `nf_complete_other` | Output summary irreversibility; cites `summaryEmit_other`. | No closure. |
| `nf_sweep_prefix` | Finite-array prefixes and folds of `ofFn`. | No closure. |
| `nf_sweep_record` | Whole-record fold and completion statements. | No closure. |
| `nf_complete_output` | Output-summary append/emission statements; cites the published law. | No closure. |
| `nf_sweepPass_output` | Accepting output-summary characterization; cites the published law. | No closure. |
| `nf_sweep_run` | Framed scan, fold result, and stream-start statements; cites both scan laws. | No closure. |
| `nf_sweep_records` | `flatMap`/fold composition and completion. | No closure. |
| `nf_display_records` | Product-index `ofFn` and concatenated records; cites `List.ofFn_mul'`. | No closure. |
| `nf_sweep_display` | Displays and folds. | No closure. |
| `nf_complete_step` | Live NDTM step and summary append; cites both APIs. | No closure. |
| `nf_sweep_control_prefix` | Prefix runs, displays, and control folds. | No closure. |
| `nf_sweep_display_pass` | First-halting displays and pass verdicts. | No closure. |

The required `nf_pack` and `nf_setup` are the explicitly authorized transcriptions of the
supplied route probe, not copies from other library files. `nf_sweep_run` is specialized from the supplied, sealed `rv_sweep0` review probe; its proof is the catalog invocation and configuration field equations. These three supplied-probe adaptations are explicitly disclosed provenance. No published theorem was
re-derived. A draft `nf_sweepInit_summary` was removed as unnecessary; its `exact?` probe suggested `rfl`, which would reduce the external summary definition. The landed genuine-prefix proof cites `outputSummary_nil` directly. **new copies: none**. The sole new text pair is the 57% field-equation idiom above; there is no new pair at or above 90%. Promotion requests for landed declarations: none. Escalations: none; the unfinished obligations below are explicitly retained as continuation work.

## Edge cases and remaining obligations

| Edge case | Status after checkpoint 2 |
|---|---|
| `N.k = 0` | All width/record/controller lemmas are uniform; width is 4 and positive. No work-tape indexing is assumed nonempty. |
| One-step halt | The nonempty-display first-stop theorem applies to a singleton word. Sweep zero acceptance follows from `nf_sweep_display_pass`; full verifier acceptance remains open. |
| Input at either blank boundary | The display records `Cfg.inputSymbol` itself. The input-replay comparison remains open. |
| Work-tape write of blank | Record format supports the blank read. Visited-block replay semantics remain open. |
| Emission on halt, or twice | `nf_complete_output` and `nf_complete_step` include the halting emission; `nf_complete_other` and `nf_sweepPass_output` handle irreversible rejection and exact singleton output. |
| Incorrect claims | The controller theorem and the scan-run theorem apply to arbitrary content. Sweep zero always finishes; rejection of wrong tape claims and totality of the full verifier remain open. |
| Unused fourth read code | `nf_decode` and `nf_decode_absent` implement and prove decoding `01` as blank. |

No constant `C` has been established. The required ledger still has to bound the host's
`2*|s| + TQ + 11` by `C*(t+1)`, with `|s| = (2*N.k+4)*t₀` and `t₀ ≤ t`. Sweep zero is now proved to cost exactly `2*|s|+2`. The guess/rewind
contribution, input replay/return, all work replays/returns/clears, the verifier's
redirects, and the host's `+11` must all appear in that bound. This report does not supply
an unproved numerical value of `C`.

The following are **proposed continuation declarations, not declarations admitted in the
source**. Each names an open obligation and its Proof sketch.

1. **Checkpoint 3 — `nf_replayTM` (common replay-leaf definition, not implemented).**
   **Proof sketch.** Define one finite-state leaf parameterized by input versus work-tape
   index. Reuse the finite record decoder and action recomputation; move A only while
   reading its record, and keep it fixed during B's block operations. The leaf's docstring
   must distinguish it from the one-tape scan and StepBlock's `k+2`-tape record reader.
2. **Checkpoint 3 — `nf_replay_input_run`.**
   **Proof sketch.** Compare each decoded input claim with the native input head, then
   perform the recomputed input move. Induct on records via `step_of_some` and the action
   field equations. Return A with `skipTM` on the empty suffix followed by `skipBackTM` on
   the display. The input head need not return, since subsequent phases do not inspect it.
3. **Checkpoint 4 — `nf_replay_work_run`.**
   **Proof sketch.** Instantiate the same leaf at a work-tape index. Represent each visited
   cell by a nonblank two-bit block on B. Prove the content, doubled-head-position, and
   contiguous visited-region invariants record by record. A simulated blank write changes
   the block's encoded content while retaining two nonblank cells. Initialize a previously
   blank destination block as two nonblank bits encoding blank: after the final simulated
   move, the current B head must still lie inside the visited region. Otherwise starting
   the prescribed skip/back/clear sequence from a blank left of the region would not meet
   its contracts. This is an implementation invariant, not a missing public API. Include
   the second-bit accesses in the head-envelope and time bounds.
4. **Checkpoint 4 — `nf_replay_clear`.**
   **Proof sketch.** Use the visited-region invariant to instantiate `skipTM_run_ofCfg`,
   `skipBackTM_run_ofCfg`, and `clearTM_run_ofCfg` in order, with the whole visited region
   as the latter two rows' word. The region is nonempty after any record. Sum their exact
   bounds and return B blank at its first visited position.
5. **Checkpoint 5 — `nf_verifier` (phase composition, not implemented).**
   **Proof sketch.** Use `phaseHostTM` over sweep zero, input replay and A's return, then
   each work replay, A's return, and B's clear. Redirect a failed check to rejection and
   all passed sweeps to acceptance. Use finite state fibers with explicit decidable equality.
6. **Checkpoint 5 — `nf_verifier_total` (the separate `hV` lemma).**
   **Proof sketch.** For every stream that first stops the controller, use the completed
   boundary theorem, total scan theorem, finite replay scans, and bounded visited region
   to obtain a first verdict time, with neither verdict earlier and empty output. This
   lemma must include malformed content and wrong claims; it must not assume a genuine run.
7. **Checkpoint 5 — `nf_verifier_display`.**
   **Proof sketch.** Combine `nf_sweep_display_pass` with the genuine input and work replay
   invariants and the public phase-host run theorem. The first verdict is acceptance, and
   all phases are silent. Keep the exact phase times for the ledger.
8. **Checkpoint 6 — `nf_ledger`.**
   **Proof sketch.** Add the exact catalog bounds, the replay leaf's record costs, and
   redirects. Sweep zero already costs `2*|s|+2`; the host contributes `2*|s|+11` with
   zero setup time. Bound work replay/clear using at most two B-head cells per record.
   Choose one natural constant depending only on N, covering zero work tapes and constants.
9. **Checkpoint 6 — `nf_forward`.**
   **Proof sketch.** Select the first halting prefix of an accepting branch using public
   run algebra. Apply the proved display/controller and sweep-zero lemmas, the full
   verifier's display result, and the ledger to `guessCtlRunTM_accepts_of`, using its
   exact-budget conclusion at `C*(t+1)` rather than constructing a new choice-word wrapper.
10. **Checkpoint 7 — `nf_backward`.**
    **Proof sketch.** Apply `guessCtlRunTM_stream_of_accepts` with `nf_verifier_total`.
    Induct on records: passed replay checks make all reads genuine, hence each recomputed
    action genuine. The final flag gives halting and the summary gives exactly `[true]`.
    Because `01` also decodes to blank, reason via the decoded fields of a raw record; do
    not assume every guessed record equals the canonical image of `nf_record`. Decompose
    an arbitrary stopped stream using `nf_firstStop_records` and the public finite-list
    product-index laws, then apply `nf_sweep_records`.
11. **Checkpoint 8 — `exists_codeNDTM_accepts_linear`.**
    **Proof sketch.** Instantiate the prescribed controller-stopped host with trivial
    setup and the finite verifier, package it with `nf_pack`, and combine both transfers
    and the uniform ledger. The target's statement remains frozen.

No mathematical impossibility or missing published interface has been established in this
partial run. The remaining items are unfinished proofs, not escalations asserting that the
brief cannot be followed. No other file's admission has been used to advance them.

## Proposed target-docstring paragraph (not landed)

**Implementation.** A controller guesses a display with one fixed-width record per step:
the choice bit, the input and work-tape reads, and an end flag. The state and transition are
recomputed in finite control. A silent deterministic verifier uses the published scan fold
for the control and output checks, then one shared replay leaf for the input and each work
tape, with the published rewind and clear routines between sweeps. The controller-stopped
guess-run host emits the verdict, and finite-state relabeling packages it as a two-work-tape
code. The present partial development establishes the display, controller, setup, packaging,
and sweep-zero control check, including its verdict on first-halting accepting displays;
the replay sweeps, full verifier, and acceptance transfers remain to be proved.

## Delivery verification

The final owned-source SHA-256 is
`91e42c2bbe11881630ba59605fb6636a8c6bca00f4b1f786a1770ff3dac9c3fd`.
The final source matches checkpoint 2 exactly. There is no third proof commit. The two
checkpoint archives were delivered at their respective commits; this final archive adds the
completed full sweep, fresh final probes, completed after screen, and final report.

The report covers every checklist item that applies to the completed checkpoints. The
remaining verifier, separate `hV`, full edge-case proofs, transfers, and term-by-term `C`
ledger are open as listed above; they are not certified by this partial delivery. No helper
statement is admitted in anticipation of that continuation. Both full screens, all raw seal
controls and outputs, all cited-constant and inspection inventories, the two patches, and a
bundle with the required sole prerequisite are included, with per-file SHA-256 checksums.

## Reproduction

Apply the patch series on the pinned base, or fetch the bundled branch after making the
base available. Use the pinned Lean 4.25.0 and manifest, the shipped 39-root list, and the
brief's 112-module order. The commands and resource measurements are in `evidence/logs`.
All probe sources are supplied under `probes/`; run each with `scripts/lean_check_tree.sh`.
The intentionally failing seal controls and `exact?` searches are labeled expected failures;
they are not substituted for the passing owned-file and downstream checks.

Glossary: `W` is the record width `2*N.k+4`; `t₀` is the still-to-be-selected first-halting
prefix length; `TQ` is the verifier's still-to-be-proved running time; `C` is the theorem's
uniform overhead constant, not yet constructed.
