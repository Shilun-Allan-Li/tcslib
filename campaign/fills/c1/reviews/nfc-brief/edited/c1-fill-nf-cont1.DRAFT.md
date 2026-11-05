# Ch3–4 fill campaign — NF cont1, the linear normal form of an NDTM, checkpoints 3–8 (`Turing.FinNDTM.exists_codeNDTM_accepts_linear`, `ClassNP/NDNormalForm.lean`)

> **A single fill, continuing a partial** (addendum v2.6, Parts 1 and 2; Part 3, the megafill,
> does not apply, except its one-Lean rule and its no-stop rule, items 5 and 7, which "Environment
> and verification" restates). The first round proved checkpoints 1–2; you prove 3–8. Deliver a
> checkpoint zip after each checkpoint: the session may end at any time. **Agent: Claude.**

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- **Your base is on branch `lean/c1-nf-partial`**, NOT `complexity/arora-barak-ch3-4` and NOT
  `main`. That branch holds the first round's work, which has not landed: it lands with yours.
  ```sh
  git fetch origin lean/c1-nf-partial
  git merge-base --is-ancestor @ANCESTOR@ origin/lean/c1-nf-partial   # must succeed; else stop
  git checkout -b fill/c1-nf-cont1 @ANCESTOR@
  git rev-parse HEAD        # must print @ANCESTOR@
  git rev-parse HEAD:TCSlib/Complexity/ClassNP/NDNormalForm.lean
  # must print e6432b1e6cf6eb33f81bff05eb389b09dd7cb9f0
  git diff --quiet 5241eb8257bdeb5b5c274145575749dd186ec65f HEAD -- '*.lean' && echo same-Lean
  # must print same-Lean: your base's Lean is that of the first round's branch tip
  ```
  Record the base hash in `REPORT.md`. Never rebase, merge or cherry-pick.
- **That commit contains:**
  - **your target as a gated statement** (the P3.3 statement gate, `campaign/gates/ch3-p33/`;
    moved into its own module by PR #120, gate 38) and **the first round's checkpoints 1–2**: 39
    private declarations in `NDNormalForm.lean` (the display, the controller, the packaging, the
    trivial setup, the control sweep and its verdict on displays), proved, with no new admission,
    and reviewed (`campaign/fills/c1/reviews/nf-fill/REVIEW.md`: 0 blockers, 0 majors). The
    docstring edits E1–E3 of that review are applied, among them the target's
    `**Implementation.**` paragraph;
  - the host of PR #174 (gate 85) in `TuringMachine/Build/NDHost` and the rest of the first round's
    infrastructure (the first round's brief, `campaign/fills/c1/briefs/c1-fill-nf.md`, lists it);
  - the fill-agent environment addendum `campaign/standards/fill-environment-addendum.md`
    (**v2.6**; Part 1 applies on every host; the cache is fetched for your brief's Mathlib roots
    only) and the copy-text screen v3 `scripts/copy-text-screen-v3.py`;
  - **this round's inputs** (`campaign/fills/c1/inputs/c1-fill-nf-cont1/`):
    - the import probe `NFContImportProbe.lean.txt` (588 checks);
    - **the route probe** `NFContRouteTail.lean.txt`, appended to a copy of the module: the
      verifier's phase layout, its instances, the host and packaging over it, and a two-phase
      chain through `phaseHostTM_run`. Its seal controls are `NFContSealControl_*.lean.txt`;
    - the seal reference `NFSealDefs.txt`: the 223 TCSlib definitions of the review's maximal
      seal;
    - the screen population.

    The first round's inputs (`campaign/fills/c1/inputs/c1-fill-nf/`) still apply, in particular
    `NFReviewProbe.lean.txt` (`rv_entry`, `rv_inputSymbol_congr`, `rv_moveInputPos_le`, and
    `rv_skeleton`: the target assembled from the obligations on `V`, sealed, the model for
    checkpoint 8) and `NFReviewVProbe.lean.txt` (`rv_tag`, `rvPark`).

    The order list, base sorries, screen base and pre-ship log are
    `campaign/fills/c1/orders/c1-fill-nf-cont1.txt` and `campaign/fills/c1/logs/c1-fill-nf-cont1-*`.
- **Before anything else, run Part 1 of the addendum**: the preflight, with its stop rule
  (E-RES). Fetch the cache for your roots only (39); never run the unfiltered
  `lake exe cache get`. If Lean cannot start, follow Part 2 exactly. **If Lean never runs, do not
  draft proofs blind**: deliver the environment report only.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-c1-nf-cont1.zip`. It contains:
  - `REPORT.md` and the full modified source;
  - a `git format-patch` series against your base, and a git bundle whose only prerequisite is
    your base;
  - **the environment logs** (`evidence/logs/` at the clone's root: preflight, cache store, roots,
    cache fetch, manifest check), the bootstrap and final sweep logs with **each module's time and
    maximum memory**, and the axiom log;
  - the seal test's source, its controls and both outputs; both screen outputs; `SHA256SUMS`.
- **Checkpoint zips.** After each checkpoint below, commit and write
  `fill-c1-nf-cont1-cp<N>.zip` (`N` from 3 to 8) with the same contents as of that commit (its
  sweep may be the four-module tail only; every log in it is a finished run, or is marked
  partial). Deliver the latest if the session ends early.

## Base, line numbers and what lands around you

- **Your base's Lean** is the campaign's tree after PR #176 (`711f5444`'s Lean) with
  `NDNormalForm.lean` at blob `e6432b1e`: 762 lines, 1 public declaration (the target, line 752; its
  `sorry` is line 758), 39 private. Lines in this brief are your base's.
- **In flight, merging after your base and invisible to it:**
  - E-D, the fill of `exists_diagonalizer` in `Diagonalization/NTimeDiagonalizer`. That file is in
    your order list and upstream of `NTimeHierarchy`. Its sorry stays in your base set.
  - PR #181 (`SpaceComplexity`) and PR #182 (`SpaceComplexity/Machines`, `SavitchARM`), both
    outside your order list.
- Nothing cites your file but `NTimeHierarchy`, by statement.

## What this is

**The linear-overhead coded normal form** ([AB09, §3.2]; [BGW70]-style guess-then-verify). For
every `N : FinNDTM Bool` there are `M : CodeNDTM` and `C` such that:
- **forward**, `N.AcceptsWithin x t → M.toFinNDTM.AcceptsWithin x (C * (t + 1))`;
- **backward**, `M.toFinNDTM.AcceptsWithin x t → ∃ t', N.AcceptsWithin x t'`.

`CodeNDTM` fixes two binary work tapes. `AcceptsWithin x t` asks for a choice word of length
**exactly** `t` whose run halts with output **exactly** `[true]`; read it through
`acceptsWithin_iff`. `C` depends on `N` only. The backward direction is unbounded.

**Where it stands.** The first round's 39 privates (read their docstrings; the table below names
those you build on):

| Private | Role |
|---|---|
| `nf_pack` | the packaging into a `CodeNDTM`, for any finite-state two-tape `H` |
| `nf_setup` | the trivial setup's five host hypotheses at time `0` |
| `nf_ctlStep`, `nf_ctlStop`, `nf_ctl_stop_iff` | the controller `Q = Fin (2k+4) × Bool` |
| `nf_record`, `nf_record_last`, `_choice`, `_read` | the record of width `W = 2k + 4` |
| `nf_display`, `nf_display_length`, `_flag`, `_prefix_length`, `nf_display_records` | a branch's display and its record split |
| `nf_display_firstStop` | a nonempty display first stops the controller at its end (`hslive`, `hsstop`) |
| `nf_firstStop_records` | a first-stopped stream is `n ≥ 1` records, only the last flagged |
| `nf_decode`, `nf_decode_record`, `nf_decode_absent` | the claimed-read decoder (`01` decodes to blank) |
| `nf_SweepState`, `nf_sweepStep`, `nf_sweepInit`, `nf_sweepPass`, `nf_complete*` | the control sweep's fold |
| `nf_sweep_run` | the control sweep is `scanTM_run_ofCfg`'s fold: `done` at exactly `2|s| + 2`, all else unchanged |
| `nf_sweep_records`, `nf_sweep_display`, `nf_complete_step` | the fold over records; the genuine step |
| `nf_sweep_control_prefix`, `nf_sweep_display_pass` | a first-halting accepting branch's display passes the control sweep |

**Proved modulo, exactly:** none. **A complete delivery has no `sorryAx` in the target.**

**Read first:**
- `NDNormalForm.lean` whole (762 lines);
- the review `campaign/fills/c1/reviews/nf-fill/REVIEW.md` §5–6: the continuation's must-pins,
  restated as binding below;
- the route probe `NFContRouteTail.lean.txt`;
- the first round's brief, §"Hosts" and §"The route" (its text is restated below where it binds);
- `Build/NDHost.lean` from `Turing.GuessRunPhase.CtlState` (line 571) to the end;
- `Build/Catalog.lean`'s `skipTM_run_ofCfg` (12240), `skipBackTM_run_ofCfg` (12302),
  `clearTM_run_ofCfg` (1520), `scanTM_run_ofCfg`; `Build/Seam.lean`'s `phaseHostTM` (835) and
  `phaseHostTM_run` (898).

**Pre-ship check** (the maintainer, at your base's Lean, against the replay snapshot `oleans-leqc3`;
log `campaign/fills/c1/logs/c1-fill-nf-cont1-preship.log`):
- the module elaborates with exactly the target's sorry warning (line 752);
- the import probe: **588 checks, 0 errors** (two deprecation warnings from `omega`'s generated
  references, as the first round found);
- **the route probe** (appended to a copy of the module), 0 errors, exactly the target's sorry
  warning:
  - the phase index `NfcPh`, the state family `NfcSt` with **named** `DecidableEq` and `Fintype`
    instances, the machines `nfcM`, the redirects `nfcRed` and the verifier `nfcV` (over an
    abstract replay leaf) all elaborate;
  - the host `guessCtlRunTM` over `nfcV` elaborates, and `nf_pack` applies to it;
  - `nfc_aReturn`, sealed (10 definitions, 4 erased): A's return after a replay, chaining
    `skipTM` and `skipBackTM` through `phaseHostTM_run`. It is on the standard three axioms;
    `nfc_retag` uses `[propext, Quot.sound]`;
  - its 10 controls close unsealed and fail sealed;
- the order list: **112 modules, 39 Mathlib roots, 19 base sorries in 9 modules**;
- the screen base (21 files): 1,379 declarations, 866 pairs, 274,994 characters, which is the first
  round's after screen exactly. Your file is in one pair, the accepted idiom NF-X1;
- lint: `ClassNP` 0 FAIL, 17 WARN over 21 files; the policy linter 0 findings on your file.

## Owned regions and targets (modify these and nothing else)

`TCSlib/Complexity/ClassNP/NDNormalForm.lean`:
- **(b)** new private declarations after `nf_sweep_display_pass` (lines 693–704) and before the
  target's docstring (line 706), or in a `namespace` or `section` of your own opened there and closed
  before it. Every new declaration has a docstring, and every proof over 20 lines a literal
  `**Proof sketch.**` paragraph (`policy.md` §3). Docstrings are public-facing library text: no
  campaign labels ("NF", "checkpoint", "cont1", "sweep 0"), dates or session narrative; provenance
  goes in `REPORT.md`. "A" and "B" are this brief's names, not the library's: in docstrings write
  tape `0` (the stream) and tape `1` (the replay tape). The route probe's docstrings use "A" and
  "B"; rewrite them when you copy its layout. The replay leaf's docstring says which public rows
  it is not and what was missing (`policy.md` §1): `scanTM` reads one tape, and `StepBlock`'s
  `recordTM` reads records on `k + 2` tapes;
- **(c)** the target's body, line 758 (`sorry`);
- **(d)** at completion only: the module docstring's and the target docstring's status phrases
  ("(statement; proof incomplete)", lines 30–31, and "statement; proof incomplete", line 707;
  public-facing; no campaign labels). If your route departs from the target's
  `**Implementation.**` paragraph, propose its new text in `REPORT.md`; the maintainer lands it.

**Frozen:** the target's statement, and the first round's 39 privates: their statements and their
proofs. If one must change, stop on that item and escalate (ground rule 4). Imports: none added.

**Target:** `Turing.FinNDTM.exists_codeNDTM_accepts_linear` (line 752), its statement frozen.

### Hosts (binding; the host-first rule, `policy.md` §1, `workflow.md` §2)

- **`M` is the controller-stopped instance of the host**, packaged by `nf_pack`:
  `guessCtlRunTM P pexit 0 q₀ (nf_ctlStep N.k) (nf_ctlStop N.k) false V qentry acc rej`, with
  `k = 2` (tape `0` is A, the display; tape `1` is B, the replay tape). Never compose `phaseHostND`
  yourself, never write a second writer, and never re-prove a handoff, a stop or an acceptance
  lemma of the host.
- **The setup `P` is trivial** (`nf_setup`), so `TP = 0`.
- **The verifier `V`** is a deterministic two-tape machine composed by `Turing.phaseHostTM` over:
  - the published rows `scanTM` (the control sweep, already proved: `nf_sweep_run`), `skipTM` and
    `skipBackTM` (A's return and the first two steps of B's clear) and `clearTM` (B's clear);
  - your one replay leaf;
  - a stationary verdict park.

  Use the `_ofCfg` run forms only. Its entry configuration is the host's
  `guessRunCfg cP 0 s qentry`, read as `streamStartCfg x 0 qentry s` (`rv_entry`).
- **`V` is silent**: no leaf of `V` emits output.

### The route (binding where it names a row or a pin; the rest is the recommended shape)

**V's layout (pinned; the route probe).** Copy the probe's layout as your own privates under the
`nf_` prefix: the phase index (`NfcPh` there), the state family, the named instances, the
machines, the redirect table and the verifier. The phases, in order:
1. the control sweep;
2. the input's replay, then A's return (`skipTM` on A at `w := []`, then `skipBackTM` on A at
   `u := s`);
3. for each work tape `j < k`: its replay on B; A's return; then B's clear (`skipTM` on B over the
   visited region's suffix from B's head, `skipBackTM` on B with `u :=` the whole region, then
   `clearTM_run_ofCfg` on the region);
4. the verdict park.

`nfc_aReturn` is A's return chained through `phaseHostTM_run`, `nfc_retag` the step from a
redirected configuration to the next phase's start. Keep both, renamed. `nfc_aReturn` is stated
for the input's return: state it once for every replayed tape, whose last redirect is
`nfcAfter N L none` for the input and `⟨.bFwd j, .run⟩` for work tape `j`. A layout of equal
strength is allowed if you say why in `REPORT.md`, for example the leaf's verdict exits read
through another function than the probe's `exit : SL → Option Bool`.

**Named instances (pinned).** As in the probe: `DecidableEq` and `Fintype` for the phase family's
fibers (`nfcStDecEq`, `nfcStFintype`), with the control sweep's `ScanPhase (nf_SweepState N)`
inside them (`@instDecidableEqScanPhase _ inferInstance`, `@instFintypeScanPhase _ inferInstance`),
and for the leaf's state, each as a `private instance` (or `local instance`). `V`'s state then has
both by inference (the probe's two `example`s). Default synthesis does not reach
`DecidableEq (ScanPhase (nf_SweepState N))` at the default instance size (the review's F3). Never
raise `synthInstance.maxSize` instead.

**The replay leaf (pinned).**
- **One own-file two-tape machine, parameterized by the replayed tape** (`none` the input,
  `some j` work tape `j` on B), not `k + 1` copies.
- **It reads every claim through `nf_decode`** (MP5). This is what makes `01 ↦ blank` sound for the
  backward direction.
- **It reads A one cell per step,** keeps A stationary while it works on B, and recomputes each
  record's action `N.tm.tr bᵣ qᵣ σᵣ` in its finite control.
- **The input instance** compares each decoded input claim with the cell under the native input
  head, then performs the recomputed input move (`moveInputPos`). The input head is not returned.
- **A work-tape instance** keeps tape `j` on B as two-bit blocks: a visited cell is two nonblank
  bits encoding its `Option Bool` content, an unvisited cell two blanks. B's head sits at its
  start position plus twice the simulated head, so a simulated move is two cells on B. It checks
  each decoded claim against B's block, then **writes the block at every record**: two nonblank
  bits encoding the cell's content after the step, `(a.workTapes j).1.getD old` (the shape of
  `Action.apply_workTapes`). An action that writes nothing (`(a.workTapes j).1 = none`) still
  writes its block, so an unvisited cell under the head becomes the nonblank code of blank.
  Otherwise the visited region can have blank holes, and B's clear either does not apply or leaves
  cells that a later work tape's replay reads, rejecting a genuine display.
- **Its exits** are a pass state, entered after the end-flagged record with A's head on the blank
  after `s` (cell `|s|`, not past it: `nfc_aReturn`'s `hpos`), or a reject state.
- **Its run lemma** has the shape "after `r` records, a pure fold of the stream". It is framed over
  A's position, with the stream read from A's head; B's head position, with B blank or holding the
  region; and the input position. It gives the exact time as a function of the stream. Prove it
  by induction over records through `MultiTapeTM.step_of_some` and the `Action.apply_*` field
  equations; no private loop driver.
- **The exit invariant on B (pinned).** At a work-tape instance's exit, B is blank outside the
  visited region, which is nonempty, contiguous and nonblank (every record writes its block), and
  B's head is on a cell of it. B's clear also applies from the region's right delimiter, but not
  from the block left of the region: there `skipTM_run_ofCfg` at `w := []` ends on the left
  delimiter, and `skipBackTM_run_ofCfg` at `u :=` the region does not apply. Since every record
  writes its block, the head can leave the region only by the last record's move, and only a
  move to the left is harmful. **Keep the invariant by not performing the end-flagged record's
  head move** (the leaf knows the record is the last when it completes it, and that move affects
  no later check), or else by the first round's proposal: initialize a previously blank
  destination block as two nonblank bits encoding blank. Say which in `REPORT.md`. If the work
  tape's head never moves, the region is the one block at B's start.

**Authorized transcriptions** (`rv_entry`, `rv_inputSymbol_congr` and `rv_moveInputPos_le` from
`NFReviewProbe.lean.txt`, `rv_tag` and `rvPark` from `NFReviewVProbe.lean.txt`, as `nf_pack` and
`nf_setup` were; renamed `nf_`):
- `rv_entry`: `V`'s entry is `streamStartCfg x 0 q s`;
- `rv_tag`: the tagged stream start is a `mapState`;
- `rv_inputSymbol_congr`: stated once, and listed as a promotion request;
- `rv_moveInputPos_le`;
- `rvPark`: the stationary verdict park.

**`hV`, the backward lemma's obligation (binding).** For **every** stream `s` that first stops the
controller at its end, well formed or not in content, `V` reaches a verdict, `acc` or `rej`, from
`guessRunCfg cP 0 s qentry`, and is at neither before. Prove it as a lemma of its own, not inside
the backward transfer. Why it holds:
- the control sweep runs on every stream (`nf_sweep_run`);
- each replay ends at A's blank after `s`, or rejects earlier;
- B's replay moves its head at most two cells per record;
- B's clear runs over the visited region, which is contiguous, nonblank and holds B's head by the
  exit invariant.

**Recommended shape.** State `V`'s lemma as a characterization: its first verdict at a time
`TQ(s)`, `acc` iff every fold passes. That one lemma gives `hV`, the forward `hacc` and `hfirst`,
and the backward "accepted ⇒ every check passed". The transfers then never touch a machine.

**The transfers.**
- **Forward** (`guessCtlRunTM_accepts_of`):
  - from `N.AcceptsWithin x t`, cut its word at the first halting time `t₀ ≤ t` (`t₀ ≥ 1`);
  - the display `s` of those `t₀` steps (`|s| = W · t₀`) gives `hslive` and `hsstop`
    (`nf_display_firstStop`);
  - the control sweep passes (`nf_sweep_display_pass`) and every replay passes, so `hacc`,
    `hfirst` and `hnil` hold;
  - the lemma's exact budget is `C · (t + 1)`.
- **Backward** (`guessCtlRunTM_stream_of_accepts`, with `hV`):
  - work over raw records' decoded fields, never over `nf_record` images, since `01` also decodes
    to blank;
  - split the stopped stream by `nf_firstStop_records` and a product-index law (as
    `nf_display_records` does), then apply `nf_sweep_records`;
  - by induction on records, passed checks make every decoded read genuine, hence every
    recomputed action genuine;
  - the flagged record halts, with output `[true]`, so `N.AcceptsWithin x t'`, with `t'` the
    record count and the records' choice bits as the word.

**The ledger (pinned shape).** `0 + 2|s| + TQ(s) + 11 ≤ C · (t + 1)`, with `|s| = (2k + 4) · t₀`,
`t₀ ≤ t`, and `TQ(s)` the sum of the phase times:
- the control sweep, `2|s| + 2`;
- each replay, `O(|s|)`, with `O(1)` B operations per record;
- each return of A, `|s| + 6`, its two redirects included (`nfc_aReturn`);
- each clear of B, `(|R| − i + 1) + (|R| + 3) + (2|R| + 2)` with `R` the region and `i` B's
  head's offset in it, plus its three redirects: `4|R| − i + 9 = O(t₀)`;
- one step for each other redirect (after the control sweep and after each replay).

`C` is a closed form in `N.k`, uniform in `x` and `t`. Give it term by term in `REPORT.md`.

**Edge cases that must stay true:**
- `N.k = 0`: no work-tape phase. After the input's return the redirect goes to the verdict
  (`nfcAfter none`), and `W = 4`;
- `t₀ = 1`: one record;
- the input head left of the first cell or past the input: the claimed read is the blank there;
- a work-tape write of a blank: the block encodes `none` and stays nonblank;
- a work-tape action that writes nothing: its block is still written, so the region has no hole;
  a work tape whose head never moves: the region is one block;
- a halting transition that emits (`summaryEmit`), or a run emitting twice (rejected by the
  control sweep);
- wrong claims: rejected, and the verdict still reached (`hV`);
- the code `01`: decoded as blank (`nf_decode_absent`).

## Gate guidance (binding)

- **The P3.3 statement gate and gate 38** froze the statement: `C` uniform, the forward budget
  `C · (t + 1)` exactly, the backward direction unbounded.
- **Gate 85:** the host's acceptance lemmas are the route. Their hypotheses (`hslive`, `hsstop`,
  `hacc`, `hfirst`, `hnil` and `hV`) are your obligations, stated as they are.

## Cited infrastructure (public and proved at your base; `NFContImportProbe.lean.txt`)

The first round's names (the host, its families and case lemmas, its run and acceptance lemmas,
`phaseHostTM` and its runs, the rows and their framed runs, the output summary and its laws, the
relabeling, the run algebra, the field equations), and in addition: `instDecidableEqScanPhase`,
`instFintypeScanPhase`, `SeekPhase` and `SweepPhase` with their instances,
`FinTM.bufferTape_nil`, `moveInputPos`.

## Ground rules (binding)

1. **File ownership, by region.** Only regions (b)–(d). List every new declaration with its role.
2. **Statement freeze** over the target and the first round's 39 privates.
3. **No new public declaration.**
4. **Escalation, item by item:** on anything unprovable as stated, stop **on that item only**,
   record the obstruction mathematically, and **continue with every item that does not depend on
   it**. The forward transfer does not depend on `hV`.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports.** Exactly your base's four; add none.
7. **One proof per shared argument.** Never write a second host, writer, phase composition,
   handoff, scan, clear, step right, rewind or run decomposition. Never re-walk the private
   families named in the first round's ground rule 7: `ClassNP/ExhaustiveReplay`'s `xr_`,
   `ClassNP/Nondeterminism`'s `choiceCore`, `Build/NDHost`'s `wr_` and `gr_`, `Build/StepBlock`'s
   `recordTM` family, `CodeSimulator`'s `h1`.
8. **Size.** No cap; file size alone is not a driver. Report the final line count and the
   declaration counts (base: 762 lines; 1 public, 39 private).
9. **Continuation budget.** A partial zip states the checkpoints reached, the open declarations
   (each with a literal "Proof sketch") and the target's axiom walk.
10. **The pinned base, and no unfolding (user, 2026-10-16).** As the first round's ground rule 10,
    in full: cite only declarations public at your base, and your file's own. **Never unfold a
    definition of another file**, and no definitional closure either; read them through their
    published equations. **Scope (user, 2026-10-23):** TCSlib's own definitions; core and Mathlib
    definitions may reduce in `rfl`, `decide` or `show`, but are never passed to `simp`, `rw` or
    `unfold`. Unfold `MultiTapeTM.step` and `Action.apply` only for a leaf of your own file, and
    prefer `step_of_some` and the `Action.apply_*` equations there too. **`N.tm.tr`** is `N`'s
    table: apply it, never unfold it.
    - **Self-check by both methods:**
      - a **seal test**: a scratch copy of your module with `attribute [local irreducible]` on
        every other-file TCSlib definition your new proofs reach, from your first new private on.
        `NFSealDefs.txt` lists the review's maximal 223. Add `attribute [-simp]` on the four
        `@[simp]` TCSlib definitions. **With controls:** for each sealed definition, a goal that
        closes unsealed and fails sealed (recursive ones get equation or usage controls);
      - an **inspection table** of every `rw`/`simp`/`simpa`/`dsimp`/`unfold`/`show`/`change`
        argument in your diff.
      - **Ship the raw outputs.** A seal not run, or one without discriminating controls, is a
        checklist failure.
    - List every declaration you cite outside your file. If it is more than the probe's list, add
      the extra names to a copy of the probe and run it.
11. **MIG-1 compatibility.** Cite none of the six R3 canonical rows (`copyTM_run`,
    `transferTM_run`, `clearTM_run`, `compareTM_run`, `incrementTM_run_succ`,
    `incrementTM_run_overflow`); use the `_ofCfg` forms. Cite no private declaration of another
    file. Keep your new privates under the `nf_` prefix, clear of the 39 existing names. A
    `private inductive` with `deriving` gets public instance names: the probe's phase index gets
    `Turing.FinNDTM.instDecidableEqNfcPh` and `Turing.FinNDTM.instFintypeNfcPh`, with their
    auxiliaries. These are public constants, not public declarations (`workflow.md` §4, counting
    public names): check that no file or open PR has your renamed ones and report them, or write
    the instances as `private instance`s.

### Checkpoints (for a partial; ground rule 9)

3. **The input's replay:** the leaf, its run lemma at the input instance, `V`'s layout (generic
   over the leaf, as in the probe), A's return after it.
4. **A work tape's replay on B and B's clear:** the leaf at a work-tape instance, the exit
   invariant, and B's three clear phases.
5. **`V`:** its characterization, `hV`, and its verdict on a display.
6. **The forward transfer** and the ledger.
7. **The backward transfer**: a passing display is a genuine accepting run.
8. **The target.**

**Add no new admission:** a helper is inserted only once proved. For a partial, the freeze check is
the axiom walk: `sorryAx` reaches the target only through its own open body. **One checkpoint, one
commit, one zip, delivered at once.**

## Duplication governance (binding)

Run the text-level screen **before and after**, **one run at a time, under `nice -n 10`**, each on a
frozen copy of its commit (`git worktree add <dir> HEAD`). The before screen runs right after
branching, beside the bootstrap, and must equal the screen base. The after screen runs once, at the
end, beside the final sweep. Checkpoint zips carry the tail check, the seal and the axiom prints,
not a screen.
- **Semantic duplication (required).** For **every** private lemma you add, search for a published
  declaration that states it or a generalization of it: in the tree and on every open PR branch, by
  name and statement (`git grep`), and by an `exact?` or `apply?` probe. **Cite proved material;
  never re-prove it.** `REPORT.md` lists, for each new private, the search made and its result.
- **The population** is the first round's 21 files
  (`campaign/fills/c1/inputs/c1-fill-nf-cont1/screen-population.txt`).
- **The screen** is `scripts/copy-text-screen-v3.py`, on the repository paths.
- **The base** is `campaign/fills/c1/logs/c1-fill-nf-cont1-screen-base.txt`: **1,379 declarations, 866 pairs,
  274,994 characters** (MEASURED at your base; 842 seconds under `nice -n 10` on the maintainer's
  host, peak 2.5 GB). It
  holds one pair with your file, `NTimeHierarchy.lean::un_setup` reproducing `nf_setup` (57%).
  That pair is an accepted idiom (the duplication ledger's NF-X1); do not re-justify it.

```sh
P=campaign/fills/c1/inputs/c1-fill-nf-cont1
nice -n 10 python3 -I scripts/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-before.txt
# after your changes, again, only when the first run has finished
nice -n 10 python3 -I scripts/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-after.txt
```

- **A new cross-file pair** with an owned-file declaration on one side goes in `REPORT.md` with its
  shared tiles and one disposition. **None of these ends the item.** A pair at 90% or more is a
  copy.
  - **idiom:** a public row's invocation and the standard conversion around it, with no lemma
    re-derived;
  - **re-derivation of a published lemma:** cite the lemma instead, before the zip;
  - **re-derivation of another file's private:** keep yours, and list it as a promotion request.
- **Known hazards:**
  - the one-step identity `M.runFrom c 1 = M.step c` (private in `CfgRecord` as
    `recordStep_runFrom_one`): `MultiTapeTM.runFrom_succ_eq_step'` at `t := 0` and `runFrom_zero`
    give it in one `rw`, so no lemma is needed;
  - `ExhaustiveReplay`'s replays and `Nondeterminism`'s `choiceCore`: your sweeps replay claimed
    actions, not a fixed machine's run on a word;
  - the record readers of `StepBlock` and `CodeSimulator`: fixed-width readers on `k + 2` tapes.
    Yours is on two, and is new;
  - the input read's congruence: use the authorized `rv_inputSymbol_congr`, stated once.
- List every new in-file pair with a one-line justification. Quote each screen's summary line and
  new pairs in `REPORT.md`, which carries **"new copies: none"** (or lists each pair), and ship
  both full outputs (`screens/`).

## Environment and verification

- Lean 4 v4.25.0, Mathlib pinned. Fetch the cache **for your roots only** (39; addendum v2.6,
  Part 1, items 2–4). **Never `lake build`**, and never the unfiltered `lake exe cache get`. Use
  `scripts/lean_check_tree.sh` for every check, one Lean process at a time. The cache tool's own
  compilation inside `lake exe cache get` is outside the one-Lean rule: do not stop or escalate for
  it. **A process deviation never ends the item**: disclose it with its evidence and continue.
- **Budget, measured on the first round's fill host:**

  | Task | Time |
  |---|---|
  | the 112-module bootstrap | about 20 minutes |
  | the final sweep | about 20 minutes |
  | each screen | about 25 minutes |
  | the module's elaboration | under a minute |

  Reserve about an hour for the finishing sequence (the final sweep with the after screen beside
  it, then the REPORT and the zip), and use the rest for proofs.
- **Bootstrap** (addendum Part 1, item 5) from `campaign/fills/c1/orders/c1-fill-nf-cont1.txt`
  (**112 modules**), right after branching. Log each module's start and end time and maximum
  memory. **The base sorry-warning set has 19 entries in 9 modules**
  (`campaign/fills/c1/logs/c1-fill-nf-cont1-base-sorries.txt`); yours is the target's. Record the
  base list by name first, and report any difference.
- **After every proof edit, run the owned file's downstream tail:** `ClassNP/NDNormalForm`, the
  `ClassNP` facade, `Diagonalization/NTimeHierarchy` and the `Diagonalization` facade, in the order
  list's order. That is four modules, about 20 seconds plus your module. The whole order list runs
  only at the final sweep.
- **Final checks:**
  1. `NDNormalForm`: zero errors, no sorry warning (for a partial, the target's only), and no
     other warning in anything you added.
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's.
  3. Re-run `NFContImportProbe.lean.txt`, extended by your citations: 0 errors.
- **Axiom prints** (a scratch copy of your module with `#print axioms` appended) for the target and
  every new private: within `[propext, Classical.choice, Quot.sound]`, and no `sorryAx` for a
  complete delivery.
- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/ClassNP` must show 0 FAIL
  (base: 0 FAIL, 17 WARN over 21 files). `python3 -I scripts/style_lint.py` on your file. No new
  line over 100 characters. The file-size WARN that follows from your additions is expected.

## Out-of-scope sorries you will see (leave every one untouched)

Everything in the base sorry set except your target: `exists_diagonalizer`
(`Diagonalization/NTimeDiagonalizer`), and the older function-level and space stubs of
`Simulation`, `Composition`, `Encoding`, `ClassP/TimeConstructible`, `Build/Wrappers`,
`Build/Loop` and `Build/Primitives`. If a proof seems to *need* one of these beyond a named
citation, that is an escalation, not a license.

## REPORT.md checklist

- [ ] The preflight's numbers, the roots' count and the cache fetch's (quoted from the logs, the
      cache store's log included), **the logs copied into this zip**, the bootstrap with
      per-module time and memory, and the base blob check.
- [ ] Nothing outside regions (b)–(d); the 39 privates unchanged (a freeze check against your base).
- [ ] The checkpoints reached (3–8), **one zip each**, the base hash and the ancestor check; if
      the session stopped before checkpoint 8, what ended it.
- [ ] Every new declaration with its role: the leaf and its run lemma, the exit invariant (which of
      the two ways), the instances, `V`'s phases and redirects, each hand-built machine's
      docstring naming the row it is not.
- [ ] `hV` as its own lemma, and each edge case with the lemma that covers it.
- [ ] `C`, term by term: the guess, the control sweep, each replay and return, B's clears, the
      redirects, and the host's `+ 11`.
- [ ] The base sorry list by name.
- [ ] Promotion candidates and escalations (each stated mathematically), or "none". The proposed
      `**Implementation.**` paragraph, if your route departs from the landed one.
- [ ] Rule 10:
      - the declarations cited outside your file, from an elaborated-constant walk;
      - the probe re-run, as "N checks of M names";
      - **the seal test, with its controls and both raw outputs**;
      - the inspection table.
- [ ] Rule 11: a grep of your diff for the six R3 rows and for other files' private names.
- [ ] Duplication: both v3 screens, every new pair justified, the semantic search per private, and
      "new copies: none".
- [ ] File size, the final sweep, the axiom prints and the lint line. The diff touches only your
      owned regions.

## Known pitfalls at this pin (hard-won)

- **Named instances, not default synthesis** (above): `DecidableEq (ScanPhase (nf_SweepState N))`
  fails at the default instance size, and so does anything built over it (`Σ i, …`, the host's
  fibers).
- **A redirected configuration is the next phase's start only up to `mapState`.**
  `phaseHostTM_run` ends at `c'.mapState (fun _ => q')`. Rewrite it with the probe's
  `nfc_retag` into `c''.mapState (Sigma.mk i)` before the next `phaseHostTM_run`, as
  `nfc_aReturn` does.
- **`skipTM_run_ofCfg` reads `w` and then one blank.** From A's blank after `s`, use `w := []`.
  Its result is one cell right, as `skipBackTM_run_ofCfg` at `u := s` needs.
- **The simps field equations are pointwise** (`Cfg.init_workTapes`, `streamStartCfg_workTapes`,
  `Cfg.mapState_workTapes`): use `funext i p` before `rw`.
- **`AcceptsWithin` is exact length.** Choose `B := C * (t + 1)` and prove `2|s| + TQ + 11 ≤ B`.
- **The acceptance lemmas hide the word:** the forward one returns it, and the backward one returns
  the stream. Never build or split a choice word yourself.
- **Under the seal, never write a host state yourself.** With `GuessRunPhase.CtlState` sealed,
  `CtlState SP SQ Q .run` does not reduce. Cite only `guessCtlRunTM_accepts_of` and
  `guessCtlRunTM_stream_of_accepts`.
- **No core or Mathlib definition is reduced outside `rfl`, `decide` or `show`.** Recursive
  definitions get usage or equation controls, not delta controls.
- `omega` treats products as atoms (`ring` first). The linter needs a literal "Proof sketch" before
  every `sorry` (partial only).
