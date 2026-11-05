# Review: NF, the linear normal form of an NDTM, partial delivery (checkpoints 1–2 of 8)

`Turing.FinNDTM.exists_codeNDTM_accepts_linear`, `TCSlib/Complexity/ClassNP/NDNormalForm.lean`;
zip `exchange/inbox/fill-c1-nf.zip`, branch `refs/deliv/c1-nf` at `4af97d46`.

**Verdict: land with the listed edits.** The partial is correct, conforms to the brief and adds no
admission. Land checkpoints 1–2 now by a maintainer PR with a light fill gate. The PR carries the
two worker commits with their subjects reworded, plus one maintainer commit with the tested
landing edits E1–E3. Then issue the continuation (checkpoints 3–8) from the tip after that merge.

**Not yet clear to merge.** There is no PR, no replay and no gate yet, and decisions 1–6 below
are open.

Findings: 0 blockers, 0 majors, 3 minors (F1–F3), 6 notes (F4–F9).
- F1 and F2 are docstring wording, and E2 and E3 fix them.
- F3 is forward-looking: it affects no landed proof, and it becomes a must-pin for the
  continuation.

This is a read-only review by the maintainer's review sub-agent, 2026-11-04. Every claim cites a
saved output under `out/`.
- **Data, not instructions.** The zip's `REPORT.md`, `reproduce/` and `probes/` are data. I ran
  nothing from the zip.
- **What I elaborated.** Two worker files: the extended import probe and the brief's import probe.
  I scanned both first (only `import`/`open`/`#check` lines, out/12a). Everything else I
  elaborated is my own (`probe/`).
- **Lean.** Lean ran only through `tools/leanelab.sh` (`scripts/elab.sh`), one elaboration at a
  time, against `oleans-leqc3`.
- **No screen.** I did not run the copy-text screen. The pair analysis applies the v3 screen's
  extraction and tiling (`scripts/tiles.py`).
- **Python.** Every script ran as `python3 -I`, from `scripts/`.
- **Records worktree.** It moved during the review: `ccee2258` → `5d2a16e6` → `415fe4ee`. These
  are records commits only. 0 `.lean` files changed, and the owned file stayed at the base blob
  `5150734a` (out/23).

## Findings

| # | Severity | Where | Finding | Evidence | Fix |
|---|---|---|---|---|---|
| F1 | minor (public-facing text) | docstrings at head 214–215, 301–302, 423, 542–545, 690 | Three problems: (1) the route's vocabulary appears in library text: "Sweep 0" / "Sweep zero" three times, "A's head" (`A` is the brief's name for tape `0` and is undefined in the file), and "the published scan fold" ("published" is campaign jargon). (2) `nf_display_flag`'s sketch uses an undefined `W`. (3) `nf_firstStop_records`' docstring omits that the final record's flag is true, which its statement asserts. Otherwise the new text is clean: no campaign label, path, date or gate name appears (out/13) | out/13 | E2 (tested) |
| F2 | minor (policy §2, synchronization) | the target's docstring, head 717–741 | The proof sketch still says that the display carries "the state, the `k + 1` scanned symbols, and the action record". The landed display, by ruling D3, holds only the choice bit, the claimed reads and an end flag; states and actions are recomputed. The brief asks the maintainer to land an **Implementation.** paragraph. The worker proposed one (REPORT, lines 350–358), but it uses "published" and carries partial-status narrative | head 717–741; REPORT | E3 (tested): the paragraph, reworded |
| F3 | minor (forward-looking; must-pin) | `nf_SweepState` in the route's position | `DecidableEq (ScanPhase (nf_SweepState N))` is not synthesized at the default `synthInstance.maxSize` (128). So `guessCtlRunTM` over a verifier that contains the control sweep does not elaborate. Raising the limit fixes it (out/11b), and so do two named instances for `nf_SweepState` (`DecidableEq`, `Fintype`); with them, the host and `nf_pack` over it elaborate (out/11c, R2 and R3). The landed code is unaffected: it needs no such instance yet | out/11b, out/11c | Must-pin MP4 |
| F4 | note (rule 10) | head 137, 145, 153, 519, 574, 580 | Each is permitted, and none unfolds another file's definition. **Unrestricted simp:** the three `simp [nf_ctlStop, …]` calls and the `simp_all` (transcribed from the maintainer's `rv_sweep0`) use only core/Mathlib theorems, two simprocs and the own `nf_ctlStop` (`simp?`, out/07). **`Fin.last` (519):** it reduces only inside the `rfl` proof of a local rewrite rule, which the 2026-10-23 scope permits. **The `show` at 574:** it names `streamStartCfg` and `FinTM.bufferTape` without unfolding them; it reduces only a structure-update projection and `Prod.snd`. **Sealed:** everything elaborates with all 223 definitions sealed (out/06d) | out/04c, out/06d, out/07 | None (optional: `simp only` lists) |
| F5 | note (style) | head 91–92, 540–541, 584–585, 626–627 | Four double blank lines | out/02c | E1 (tested) |
| F6 | note (duplication; decision 3) | `NTimeHierarchy.lean::un_setup` ← `nf_setup`, 124/218 = 57% | **The one new pair.** It is three tiles (43, 41, 40 characters) of the published initial-configuration field equations (`MultiTapeTM.initCfg_eq`, `Cfg.init_state`, `Cfg.init_workTapes`) inside a 31,091-character setup proof. Nothing is re-derived. The brief mandated `nf_setup`'s text verbatim (out/22). **Disclosure:** the worker disclosed it, with the same tiles. **Consequence for H:** H's screen population contains `NDNormalForm`, so after this landing the pair is a base pair with H's own `un_setup` on one side | out/08, out/09, out/22 | Accept as idiom; record a ledger exclusion; re-take H's screen base (decision 6) |
| F7 | note (row candidates; the dedup window) | `nf_pack`, the `hnext` step of `nf_sweep_control_prefix`, `nf_sweep_run` | None of these is a copy. Each is not published, and none reaches the screen threshold (out/09, out/10). **`nf_pack`** is the third relabel-to-code packaging. The other two are `Encoding`'s `FinTM.toCodeTM` / `exists_codeTM_spaceUsed` (for `CodeTM`) and `BPPHard`'s `exists_codePTM` (for `CodePTM`). No `CodeNDTM` row exists. **`hnext`** is the one-step identity on a choice prefix (`runWith (w.take (n+1)) = stepWith w[n] (runWith (w.take n))`). `Nondeterminism` states it inline at line 386, and `ConfigGraph.take_succ_action` is weaker. **`nf_sweep_run`** is `rv_sweep0` specialized; the generic form would serve any fold | out/09, out/10, out/22 | Ledger "row candidates" entry (optional); no landing action |
| F8 | note (history) | commit subjects | "… (checkpoint 1)" and "… (checkpoint 2)" are campaign labels | out/01 | Reword at landing (below) |
| F9 | note (process; budget) | the session | **The tail check.** After each checkpoint it ran the order list's 46-module tail: 720 s per checkpoint, 24 of the 50 minutes between the bootstrap's end and the second commit. Only 4 of those modules are downstream of the owned file (out/15, out/17). **Unexplained stop.** REPORT does not say why proof work ended at 09:24Z. **Missing zips.** The two checkpoint zips are not in the inbox (only the final zip; out/23). **Disclosed deviations, immaterial:** the interrupted first cache fetch and its one cleaned retry, `/usr/bin/time` missing, the `evidence` symlink, and the screen's exit 127 before Python started (item 11 below) | out/16, out/17, out/23 | Continuation: tail = the downstream closure (MP3); REPORT states what ended the work |

## 1. Integrity and scope

| Check | Result | Evidence |
|---|---|---|
| Zip | SHA-256 `1558c81e…58ca`; 189 members, no unsafe path or link; 188/188 sums OK, no unlisted file; extraction holds regular files only | out/01 |
| Bundle | `verify` okay; sole prerequisite `951251f6`; one ref `fill/c1-nf` = `4af97d46` = `refs/deliv/c1-nf` | out/01 |
| Commits | `2dc36b95` (+333/−7) and `4af97d46` (+338/−0), linear on the base, author Codex, owned file only (+671/−7). Patch-ids equal the commits'. The patches equal this host's `format-patch` except the git-version trailer | out/01 |
| Blobs | base `5150734a` (as the brief says); head `4d32cd27` = the zip's source (SHA-256 `91e42c2b…`) | out/01 |
| Imports | lines 1–13 are byte-equal to `NDNormalFormOverlay.lean.txt`; the four imports are the base's two plus `Build.NDHost` and `Build.StepBlock` | out/01b |
| Regions | (a) 2 import lines. (b) 664 lines, from head 45 to 708, between `namespace FinNDTM` and the target's docstring. (d) module docstring lines 20–22 → 1 line and 30–31 → 2 lines; the target docstring's lines 46 and 66 (status phrase; "(round-1 finding 6)" removed). Nothing else changed. Widest added line 99; no line over 100 | out/02c |
| Target | statement and body byte-identical to the base (`sorry`); only the permitted docstring phrases changed | out/02b |
| Brief, addendum | brief `a37eaed4…` = the dispatched copy; addendum v2.6 `9f5bd5e7…` = the records copy | out/01 |
| Closure | the head's TCSlib import closure is 26 modules plus the file itself. None of `PClosure`, `TMSAT`, `NTimeDiagonalizer` (changed between the base and the tip) is in it, so `oleans-leqc3` serves for the base and the merged tree | out/15 |

## 2. Statements frozen

- **declfreeze.** 1 → 1 public declaration; none added or removed. The target's text change is
  its docstring only, which the brief authorizes. 0 → 39 privates: 28 theorems, 9 definitions,
  2 abbrevs, all named `nf_` (out/02).
- **Census of the module's constants.** 121 constants, exactly one of them public: the target.
  The 120 private ones are the 39 declarations and 81 compiler auxiliaries (71 `_proof_N`, 9
  equation lemmas `eq_N`, 1 matcher). There is no public auxiliary, no instance and no derived
  instance (out/02d). This matches REPORT.
- **The `nf_` prefix** names no declaration or identifier outside this file on any of the 318
  local and remote refs (out/18).

## 3. Elaboration and axioms

- **The head file.** Against `oleans-leqc3`: exit 0, exactly `742:8: declaration uses 'sorry'`
  (the target), no other warning, about 10 s (out/03). The base file gives `78:8` alone
  (out/03b).
- **Axioms.** I printed them for all 40 declarations from a copy of the head module with the audit
  appended (out/05, out/05d). Every one of the 39 privates is within
  `[propext, Classical.choice, Quot.sound]`; `nf_ctlStop` has none. The target has those three
  plus `sorryAx`.
- **The only direct `sorryAx` user** is the target itself. Of the probe's 157 local constants
  (the module's 121 and the audit's own), 156 are within the standard three; the target is the
  one outside them (out/05).

## 4. Rule 10

- **The walk.** I walked from every module constant (out/05). It reaches 80 direct TCSlib
  constants and 388 core/Mathlib ones. That agrees with the worker's 463, which walks the new
  declarations only: the target adds `sorryAx` and four `Lean.Name` constants. Of the 80, 21 are
  semireducible definitions, each reached only as a term (the rest are theorems, constructors,
  inductives and reducible structure projections):
  - `Action.apply`;
  - `Cfg.init`, `Cfg.inputSymbol`, `Cfg.mapState`, `Cfg.workTapeSymbols`;
  - `CodeNDTM.toFinNDTM`, `FinNDTM.AcceptsWithin`, `FinTM.bufferTape`;
  - `MultiTapeTM.initCfg`, `MultiTapeTM.runFrom`;
  - `NDTM.initCfg`, `NDTM.relabelState`, `NDTM.runWith`, `NDTM.stepWith`;
  - `StepBlock.outputSummary`, `StepBlock.summaryEmit`;
  - `scanFold`, `scanKeep`, `scanResult`, `scanTM`, `streamStartCfg`.

  The new code does not reach the host family (`guessCtlRunTM`, `GuessRunPhase.CtlState`'s
  fibers) at this checkpoint.
- **Two auxiliary proofs.** `streamStartCfg._proof_1` and `instInhabitedCfg.default._proof_1`
  come from the statements of `streamStartCfg_inputPos` and `Cfg.init_inputPos`, not from an
  unfolding (out/05b).
- **The seal.** Mine is maximal (`scripts/mkseal.py`). It applies `attribute [local irreducible]`
  to all 223 semireducible, non-instance, non-projection, non-matcher TCSlib definitions in the
  environment: the brief's whole list and all 21 reached ones. It applies `attribute [-simp]` to
  all four `@[simp]` TCSlib definitions. It is placed before `nf_pack`.
  - **Body:** 0 errors, only the target's warning.
  - **Controls:** 223 `rfl`, 223 equation and 4 `simp` controls. All 450 fail sealed. 439 close
    unsealed. Every one of the 223 definitions has a control that fails sealed and closes
    unsealed. The ten recursive definitions (`NDTM.runWith`, `mealyRun`, …) get usage controls by
    their first equation lemma (out/06d).
- **Tactic arguments.** 424 rows, 176 identifiers (out/04a–c).
  - Every other-file name passed to `rw`, `rwa`, `simp only` or `simpa only` is a theorem: 33 TCSlib
    field equations and laws, the rest core/Mathlib.
  - The table shows two "definitions", and neither is a finding:
    - `FinNDTM.k` is the local `k : ℕ`, which the kinds probe resolved to the projection;
    - `Fin.last` sits inside a local `rfl` rule (F4).
  - `show` terms name `streamStartCfg` (574) without unfolding it.
  - There is no `unfold`, `dsimp`, `change` or `delta`.
  - The worker's `inspection-cp2.md` lists the same arguments with the same classes.
- **The worker's seal.** 39 definitions plus 4 erasures, 39 controls (38 + 1 errors sealed, 0
  unsealed) and 2 fiber controls. It is sound; mine supersedes it (out/21).
- **Probes.** I elaborated them in my head worktree, one at a time (out/12b–d):
  - the brief's `NFImportProbe`: 149 checks, 0 errors, 0 warnings;
  - the worker's `NFImportExtended2`: 578 checks, 0 errors, and the two deprecation warnings that
    REPORT discloses;
  - coverage: the worker's probe covers all 80 direct TCSlib constants. It omits 9 core basics
    (`rfl`, `true_and`, …), which need no check.

**Rule 11 and the other addendum rules:**
- no R3 row and no other file's private, in the walk or in the added text (out/05, out/18);
- the `_ofCfg` forms only (`scanTM_run_ofCfg`);
- the `nf_` prefix only; no instance;
- one Lean process at a time: the logs hold 374 Lean runs with start and end times, and no two
  overlap (out/24);
- the cache fetched for 39 roots only.

## 5. The mathematics of checkpoints 1–2

**They match the brief's checkpoint definitions.**
- **Checkpoint 1.** It is all present and proved:
  - the overlay;
  - the record layout `nf_record`, with `W = 2k + 4`: choice bit; read `i` at `2i+1`/`2i+2`, coded
    `00` blank, `10` false, `11` true; end flag at `2k+3`;
  - the display `nf_display` of any word, with its length `W·|w|` and its prefix form
    `nf_display_prefix_length`;
  - the controller, exactly the route's `Q`, `q₀`, `δ` and `stop` (`nf_ctlStep`, `nf_ctlStop`);
  - "a display first stops the controller at its end" (`nf_display_firstStop`);
  - "conversely, a stopped stream is `n ≥ 1` records with only the last flagged"
    (`nf_firstStop_records`);
  - `nf_setup` and `nf_pack`.
- **Checkpoint 2.** The fold `δ₀` (`nf_sweepStep`) has the state the brief prescribes:
  - the position, and the record as `Fin W → Option Bool`;
  - the simulated state from `q₀`;
  - the output summary, updated by `summaryEmit`;
  - a failure flag.

  At each record's end, `nf_complete` recomputes the action from `N`'s table and checks the end
  flag against `a.state = none`.

  **The pass condition.** `nf_sweepPass` adds two conjuncts to the brief's "no failure and summary
  `some true`": position `0` and simulated state halted. On a stream that first stops the
  controller, both follow from the flag check. They make the backward argument direct.

  **Its laws:** `nf_sweep_prefix`, `_record`, `_records`, `nf_display_records`,
  `nf_sweep_display`, `nf_complete_*`. Its run is `nf_sweep_run`, the review probe `rv_sweep0`
  specialized.

**The host's interface fits.**
- **Types and controller.** `Q = Fin (2k+4) × Bool`, `δ` and `stop` have the types
  `guessCtlRunTM` takes. `nf_display_firstStop`'s two conjuncts are exactly `hslive` and `hsstop`
  of `guessCtlRunTM_accepts_of`, and `nf_firstStop_records`' hypotheses are exactly those of
  `guessCtlRunTM_stream_of_accepts`. `Fintype` and `DecidableEq` hold for `Q` and for
  `nf_SweepState` (out/11).
- **The packaging.** With two named instances, `guessCtlRunTM` over the control sweep elaborates,
  and `nf_pack` applies to it (out/11c; F3).

**The statements are not vacuous (out/11).**
- **`nf_firstStop_records`.** Its hypotheses hold, by `decide`, for a one-record stream (`k = 0`)
  and a two-record stream (`k = 1`).
- **Controller semantics.** A first record with its flag set stops early, and an incomplete record
  never stops.
- **`nf_sweep_display_pass`.** Its three hypotheses hold for a toy machine (no work tape, one
  state, halting at once with output `true`). Its conclusion is then proved. The same toy's
  display on `[]` is `[false, false, false, true]`, by `decide`.
- **`nf_sweep_control_prefix`** shares those hypotheses.
- **What the forward transfer needs.** Take an `N.AcceptsWithin x t` word, cut at the first
  halting time `t₀ ≤ t` (`t₀ ≥ 1`), and the result meets `hlive`/`hhalt`/`hout` exactly.
  `nf_sweep_display_pass` then gives the control sweep's pass on the display, and `nf_sweep_run`
  gives its exact time `2|s| + 2` and the unchanged configuration.
- **What the backward transfer needs from `nf_firstStop_records`:** the length `W·n` with
  `n ≥ 1`, and the flags. It still needs the record split of a raw stream (a product-index law, as
  in `nf_display_records`).

**Is `nf_decode` mapping `01` to blank sound for the backward direction? Yes, on one condition:**
every later sweep must read a claimed read through `nf_decode`, or through a check at least as
strict (out/11, S5).
- **Why it is sound.** The control sweep recomputes the actions from the decoded reads. If the
  replay sweeps check the decoded reads against the genuine tapes, then induction on the records
  makes the decoded reads genuine. That makes the recomputed run genuine, whatever the raw bits.
  A replay that compares raw bits against an encoding of the genuine cell is stricter, since it
  rejects `01`, and is also sound.
- **The one unsound combination.** A replay that decodes `01` differently from `nf_decode`.
- **Completeness is untouched.** Displays never contain `01`.
- **The pin.** MP5 pins the condition. REPORT's item 10 already draws the consequence: the
  backward proof must reason over raw records' decoded fields, not over `nf_record` images.

## 6. The continuation plan (REPORT items 1–11)

The plan is consistent with the brief's binding route and hosts, and I found nothing that blocks a
continuation.
- **Items 1–2, the one replay leaf.** It is parameterized by the replayed tape. A moves one cell
  per step and stays stationary during B's work. The input is replayed by the native `moveInputPos`
  and is not returned. A returns by `skipTM` at `w := []`, then `skipBackTM` at `u := s`. All of
  this is the brief's route.
- **Item 3, the work-tape replay on B.** The design is two-bit blocks, B's head at `2×` the
  simulated head, and a contiguous nonblank visited region. **The key point is correct.**
  - `skipTM_run_ofCfg` from a cell left of the region (with `w := []`) ends on the region's first
    cell, not one past its right blank, so `skipBackTM_run_ofCfg` (with `u :=` the region) would
    not apply.
  - So at the leaf's exit, B's head must lie inside the region, or on its right delimiter.
  - The head can leave the region only by the last record's move to the left.
  - **The worker's fix works:** write a blank destination block as two nonblank bits encoding
    blank.
  - **So does a cheaper one:** skip the end-flagged record's move. The leaf knows the record is
    the last when it completes it, and the move affects no later check.

  The continuation must pin one of the two (MP5).
- **Item 4, B's clear.** `skipTM` runs over the region's suffix from B's head, `skipBackTM` over
  the whole region, and `clearTM_run_ofCfg` over the region. The contracts fit
  (`Build/Catalog.lean` 1520, 12240, 12302). After the clear, B is blank with its head at the
  region's first cell, not at `0`. **So the leaf's run lemma must be framed over B's start
  position (MP5).**
- **Items 5–7.** The phase-host composition, totality and the verdict on displays are as the brief
  says. `phaseHostTM` is generic over the phase index (`Build/Seam.lean` 835–898). The index type
  for `k + 2` sweeps with returns and clears has not been designed yet (MP7).
- **Item 8, the ledger.**
  - **The host's term.** `TP = 0`, so it contributes `2|s| + 11` with `|s| = (2k+4)·t₀`.
  - **`TQ(s)`.** The control sweep costs `2|s| + 2`, each replay `O(|s|)` with `O(1)` B operations
    per record, each return `|s| + 4`, and each clear `O(t₀)`. That gives `TQ ≤ c_k·|s| + c'_k`.
  - **The bound.** `t₀ ≤ t` gives `0 + 2|s| + TQ + 11 ≤ C(t+1)` with
    `C = (2 + c_k)(2k+4) + c'_k + 11`, which depends on `N` only.

  The shape is right.
- **Item 6 (`hV`).** It must range over every first-stopping stream. The control sweep runs on
  every stream (`nf_sweep_run`; out/11, S8). After a passing control sweep, the replays end at A's
  blank or reject earlier. Rejection is a verdict, and needs no clear.
- **Items 9–11** follow the binding transfers: the forward one through
  `guessCtlRunTM_accepts_of`'s exact budget, the backward one through
  `guessCtlRunTM_stream_of_accepts` with `hV`.

**Scope (decision 4).** One continuation for checkpoints 3–8, with checkpoint zips (recommended).
- **Why one.** The partial mechanism already covers an early stop. The worker was fast: its
  work checks for checkpoint 1 ran 08:34–08:43Z and for checkpoint 2 08:57–09:10Z, each followed
  by a 12-minute tail (out/17).
- **What it needs.** The brief pins the leaf and the verifier's layout (MP5–MP7), so that the
  worker composes rather than designs.
- **The alternative.** Split it into 3–5 (the leaf, the clears, the verifier and `hV`) and 6–8
  (the transfers, the ledger and the target). That costs one more landing and brief cycle.

### The continuation's must-pins

- **MP1. Base and regions.**
  - **Base:** the tip after this landing merges, plus the issuing records commit. No overlay.
  - **The 39 privates stay frozen.** Their statements, and their proofs unless a change is
    authorized.
  - **Regions:**
    - (b) new `nf_` privates after `nf_sweep_display_pass`;
    - (c) the target's body;
    - (d) the status text, plus E3's paragraph, updated at completion.
- **MP2. Lists re-taken at that tree.**
  - The order list (`NDHost` and `StepBlock` are already in it).
  - **Base sorries: 19 in 9 modules.** #176 proved `exists_queryTM`. The count drops to 18 in 8
    if E-D lands first.
  - The screen base, with the `un_setup` pair disclosed as an accepted idiom.
- **MP3. The per-checkpoint tail is the owned file's downstream closure** (`NDNormalForm`,
  `NTimeHierarchy`, the `ClassNP` and `Diagonalization` facades: about 20 s). The whole order
  list runs only at the final sweep. Measured on this fill host: tail 720 s, bootstrap and sweep
  about 20 minutes each, screens 1,514 s and 1,487 s (out/16, out/17).
- **MP4. Named instances** (`private instance`, or `local instance`) for `DecidableEq` and
  `Fintype` of `nf_SweepState`, of the leaf's state and of `V`'s state. Do not rely on default
  synthesis through `ScanPhase`, `Σ` or the host's fibers (F3; out/11b, out/11c).
- **MP5. The replay leaf.**
  - **Shape.** One own-file two-tape machine, parameterized by the replayed tape. Its docstring
    names the rows it is not: `scanTM` reads one tape; `StepBlock`'s `recordTM` reads records on
    `k + 2` tapes.
  - **Claims.** It reads every claim through `nf_decode`.
  - **Its run lemma** has the shape "after `r` records, a pure fold". It is framed over:
    - A's position, with the stream from A's head;
    - B's head position (B blank or holding the region);
    - the input position.

    It gives the exact time as a function of the stream.
  - **Its exit** is A's blank after `s`, or a reject state.
  - **For the work-tape instance, the exit invariant** is "B's head is on a cell of the
    nonempty, contiguous, nonblank visited region". Pin how it is kept: the worker's
    initialization, or skipping the end-flagged record's move.
- **MP6. Rows.**
  - A's return: `skipTM` (`w := []`) then `skipBackTM` (`u := s`).
  - B's clear: `skipTM` (the region's suffix from B's head), `skipBackTM` (the whole region),
    `clearTM_run_ofCfg` (the region).
  - The `_ofCfg` forms only; no R3 row.
- **MP7. `V`'s layout.**
  - **Pin `V`'s phase index type and redirect table:** the control sweep, the input replay, A's
    return, then per work tape `j < k` its replay, A's return and B's three clear phases, then a
    verdict park.
  - **Allow the stationary park leaf** (`rvPark` of `NFReviewVProbe`), or name a published
    stationary row.
  - **Ship a pre-ship route probe** in which `V` and its instances elaborate and
    `phaseHostTM_run` chains two phases, as `rv_V_verdict` did for one.
- **MP8. Authorized transcriptions,** as `nf_pack` and `nf_setup` were:
  - `rv_entry` (`V`'s entry is `streamStartCfg x 0 q s`);
  - `rv_tag` (the tagged stream start is a `mapState`);
  - `rv_inputSymbol_congr` (stated once, with a promotion request);
  - `rv_moveInputPos_le`.
- **MP9. `hV` and the transfers.**
  - **`hV`** is its own lemma over every first-stopping stream, malformed ones included.
  - **The backward transfer:**
    - it works over raw records' decoded fields;
    - it splits the stream by `nf_firstStop_records` and a product-index law;
    - it then applies `nf_sweep_records`.
  - **The forward transfer** cuts at the first halting time and uses the host's exact budget.
- **MP10. The ledger's shape.** `0 + 2|s| + TQ(s) + 11 ≤ C·(t+1)`, with `|s| = (2k+4)·t₀`,
  `t₀ ≤ t`, and `TQ(s)` from the phase times. `C` is a closed form in `N.k`.
- **MP11. The seal.** At least every TCSlib definition the walk reaches, and all four `@[simp]`
  erasures. This review's maximal 223-definition seal (`scripts/mkseal.py`, out/06) can be given
  as the reference.

## 7. Duplication

- **The screens.** The before screen is byte-identical to the screen base (1,351 / 865 /
  274,870). The after screen (1,379 / 866 / 274,994) adds exactly one pair, removes none, and
  has no in-file pair (out/09).
- **The one pair** (F6) is an idiom of the published field equations: accept it, and record an
  exclusion in `campaign/duplication-ledger.md` (not counted). It does not block landing.
- **Transcriptions** (out/22):
  - `nf_pack` and `nf_setup` are `nfr_pack` and `nfr_setup` verbatim, up to the name, as the brief
    directs;
  - `nf_sweep_run` is `rv_sweep0` with `δ := nf_sweepStep N` and `a₀ := nf_sweepInit N`,
    rewrapped. The brief does not name it for copying, but it is the maintainer's own proof of the
    route's sweep-0 fact, disclosed by the worker. That is acceptable: probes are not library text,
    and the screen pairs `nf_sweep_run` with nothing.
- **Semantic.** My `exact?` closes none of four generic forms of the new content (out/10, E1–E4):
  - the control sweep from the stream start;
  - the one-step prefix identity;
  - the fold over concatenated blocks;
  - the `CodeNDTM` packaging.

  E5 there was ill-posed and is not counted. The worker's per-lemma table agrees, and its logs
  show `exact?` failing.
- **For the ledger:** the F6 exclusion, and optionally F7's row candidates. Nothing is a copy at
  90% or more, and nothing blocks.

## 8. Docstrings and policy

- **Coverage.**
  - Every new declaration has a docstring.
  - The seven proofs over 20 lines carry a literal `**Proof sketch.**`, and six shorter ones do
    too.
  - The new privates are technical glue, so they need no `[Tag, location]`.
  - The module keeps `## References`.
  - Lint passes: `campaign_style_lint` 0 FAIL, 17 WARN over 21 files at both the base and the head;
    `style_lint` 0 findings; `NDNormalForm` 752 lines, INFO only (out/13, out/14).
- **Public-facing text.**
  - **What is clean.** No campaign label, `campaign/` or `audits/` path, gate or finding label, or
    dated ruling in the new text (out/13). The (d) rewrites are public-facing: "(statement; proof
    incomplete)" and "This module isolates the normal-form statement and its supporting
    construction".
  - **What needs edits.** The route words of F1 (E2) and the stale sketch of F2 (E3).
  - **Left for the deferred cleanup.** The unchanged base text "Fill obligations, named:" in the
    target's sketch, where it predates this delivery.

## 9. Landing

**Recommended: a maintainer PR into `complexity/arora-barak-ch3-4` with a light fill gate.**

- **Commits.** Cherry-pick `2dc36b95` and `4af97d46`; they touch only the owned file. That file is
  still `5150734a` at the tip, so both apply as delivered (out/01, out/23). Reword:
  - `2dc36b95`: "Prove the normal form's display and stopping controller";
  - `4af97d46`: "Prove the normal form's control sweep and its verdict on displays";
  - then one maintainer commit, for example "Reword the normal form's sweep docstrings and add its
    implementation paragraph", with `out/19-landing-edits.diff`.
- **The landing edits** (`scripts/landing_edits.py`, asserted; out/19). The landed file is
  `land/NDNormalForm.lean`: git blob `e6432b1e`, SHA-256 `b3fa9998…1279`, 762 lines (out/20g).
  - **E1.** Remove the four double blank lines.
  - **E2.** Five docstrings:
    - `nf_sweepInit` and `nf_sweep_display_pass`: "The control sweep …";
    - `nf_sweep_run`: "**The control sweep is the fold instance of `Turing.scanTM`.** … the head
      of tape `0` is back at cell `0` …";
    - `nf_display_flag`'s sketch: "With the width `W = 2k + 4`, …";
    - `nf_firstStop_records`: "…, whose end flag is true".
  - **E3.** The target's **Implementation.** paragraph, after the sketch: the display by records
    (choice bit, two-bit claimed reads, end flag on the last record only), states and actions
    recomputed, the controller-stopped host with a trivial setup, the silent verifier (control
    sweep by `Turing.scanTM`, replay sweeps, the clear by `Turing.skipTM`, `Turing.skipBackTM`,
    `Turing.clearTM`).
- **The edits are tested** against `oleans-leqc3`:
  - exactly the target's sorry warning (752:8, out/20a);
  - axioms unchanged, and still only one direct `sorryAx` user (out/20b);
  - the maximal seal: body 0 errors, 223 of 223 definitions with a working control (out/20e);
  - code byte-identical to the head with comments stripped; target statement and body unchanged;
    no statement of the 40 declarations changed (`privstmt`, out/20f);
  - widths at most 100, no double blank line, lint 0 FAIL / 17 WARN, `style_lint` 0 findings
    (out/20f).
  - Since the code is identical, the screen's measurements cannot change.
- **The replay.** The owned file's downstream closure in the tip's tree, in order (out/15):
  1. `TCSlib/Complexity/ClassNP/NDNormalForm`;
  2. `TCSlib/Complexity/Diagonalization/NTimeHierarchy`;
  3. `TCSlib/Complexity/ClassNP` (the facade);
  4. `TCSlib/Complexity/Diagonalization` (the facade).

  Never the root `TCSlib`. Chain from the snapshot of exactly the tree the PR merges into:
  `oleans-leqc3` today, since the tip's Lean is #176's merge. If #181, #182, E-D or H merges first,
  use the snapshot its merged-tree replay leaves; never compose snapshots. Expected:
  - 0 errors;
  - `NDNormalForm` with only the target's warning;
  - `NTimeHierarchy` and the facades with no sorry warning (the base set has none there).

  The worker's own runs show the same: 112/112 modules, 20 sorry warnings equal to the base set by
  module (out/16).
- **Clear to merge** when four things hold: the PR is based on the campaign branch, not stacked;
  decisions 1–3 and 6 are taken; the replay above passes; and the gate records zero blockers and
  zero majors.

**What the light gate's pack should ask.**
- **Attach:** `TEMPLATE.md`, `policy.md`, `workflow.md`, the brief and addendum v2.6, the
  delivery's REPORT and evidence, this review with `out/` and the landing diff.
- **Ask:**
  - correctness of the 39 privates and their fitness for the transfers (§5), and the soundness
    of `01` → blank;
  - rule 10 (the seal sets; F4) and rule 11;
  - the pair's disposition (F6);
  - the public-facing text, E2 and E3;
  - the replay;
  - the findings as a downloadable `nf-cp2-fill-findings.md`.

## 10. Process (REPORT's disclosed deviations)

None of them matters to the delivered content.
- **The first cache fetch.** It was interrupted while cloning, because the default archive store
  (`~/.cache`) was on tmpfs, which the addendum forbids. No archive had been fetched. The worker
  used the one cleaned retry of Part 1, item 4, with a disk-backed `XDG_CACHE_HOME`: 1,007 files,
  exit 0.
  - Strictly, "store on tmpfs" is not one of item 4's listed triggers; the worker's choice
    respected the tmpfs ban.
  - An addendum note would avoid the question: "set `XDG_CACHE_HOME` to the clone's filesystem
    before the first fetch".
- **`/usr/bin/time` was absent.** Python's `wait4` was used instead, which the addendum permits
  ("where available").
- **The `evidence` symlink.** It joined pre-clone logs without moving a running log (Part 1,
  item 7). The zip holds regular files.
- **The screen's first launch** exited 127 before Python started; one real before screen ran.
- **The process cost** is F9: two 12-minute tail checks, and no stated reason for ending proof
  work at 09:24Z. The timeline is in out/17:
  - preflight 08:06Z, bootstrap 08:14–08:34;
  - checkpoint 1's commit at 08:56, checkpoint 2's at 09:24;
  - the final sweep and the after screen 09:24–09:50; the zip 09:53.

## Decisions for the user

1. **Landing.** (a) Land checkpoints 1–2 now by a maintainer PR and a light gate, with E1–E3 and
   the reworded subjects, then base the continuation on the merged tip. **Recommended:** it is
   the E-Q cp1 precedent, the replay is 4 modules, and the continuation then starts from a
   campaign commit. (b) Land as delivered. (c) Let the partial travel with the continuation as
   patch inputs.
2. **E3 now, or at completion.** **Recommended: now.** The sketch's display sentence contradicts
   the landed display (F2), and the brief already assigns this paragraph to the maintainer.
3. **The duplication disposition.** Accept `un_setup` ← `nf_setup` (57%) as an idiom pair, and
   record an exclusion in the ledger, not counted (**recommended**). Optionally, record F7's
   three row candidates for the dedup window.
4. **The continuation's scope.** One continuation for checkpoints 3–8 with MP1–MP11 pinned
   (**recommended**), or a split into 3–5 and 6–8.
5. **The continuation's agent** (a soft suggestion): Codex again. Its first session was fast and
   conformant.
6. **Order against H and E-D.**
   - **H.** Land this before H issues. H's screen population contains `NDNormalForm`, so re-take
     H's screen base at the landing tree. The base gains the 28 screened privates and the pair
     with H's own `un_setup`; disclose that pair as accepted. H's order list is unchanged, since
     `NDHost` and `StepBlock` are already in it (out/23).
   - **E-D** (dispatched; its population excludes `NDNormalForm`) is unaffected, except that its
     landing replay is at the merged tree, where `NTimeHierarchy` sits downstream of both files.
