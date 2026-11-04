# Ch3–4 fill campaign — NF, the linear normal form of an NDTM (`Turing.FinNDTM.exists_codeNDTM_accepts_linear`, `ClassNP/NDNormalForm.lean`)

> **DRAFT** (maintainer, 2026-10-27). **Agent: Codex** (user, 2026-10-27). ⟨…⟩ marks what the
> pre-ship fills in.

> **A single fill** (addendum v2.6, Parts 1 and 2; Part 3, the megafill, does not apply, except
> its one-Lean rule and its no-stop rule, items 5 and 7, which "Environment and verification"
> restates). Deliver a checkpoint zip after each checkpoint: the session may end at any time.

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If it
  fails, **stop**. That commit contains:
  - **your target as a gated statement**: the P3.3 statement gate (`campaign/gates/ch3-p33/`),
    moved unchanged into its own module by PR #120 (gate 38, `campaign/gates/38-nd-normalform/`);
  - **the guess-then-run host over the controller-stopped writer (PR #174, gate 85)**, in
    `TuringMachine/Build/NDHost`: `Turing.guessCtlRunTM` with its state family
    `Turing.GuessRunPhase.CtlState`, phases `Turing.guessCtlRunPhases`, redirects
    `Turing.guessCtlRunRed` and their 19 case lemmas; the run lemmas
    `guessCtlRunTM_runWith_handoff` and `guessCtlRunTM_runWith`; and the three acceptance lemmas
    your transfers are built on, `guessCtlRunTM_stop_of_halted`, `guessCtlRunTM_accepts_of`
    (forward) and `guessCtlRunTM_stream_of_accepts` (backward); the writer's contract
    `Turing.ndWriterTM_run_controller`;
  - the deterministic phase host `Turing.phaseHostTM` (`Build/Seam`), the rewinds
    `Turing.skipBackTM` (`Build/Catalog`) and `Turing.inputRewindTM` (`Build/InputRewind`), the
    output summary `Turing.StepBlock.outputSummary` and `summaryEmit` with their laws
    (`Build/StepBlock`), the relabeling `Turing.NDTM.relabelState` with `relabelState_runWith`,
    and the run algebra of `TuringMachine/Nondeterministic`;
  - the fill-agent environment addendum `campaign/standards/fill-environment-addendum.md`
    (**v2.6**: Part 1, the resources and the cache, applies on every host; the cache is fetched
    for your brief's Mathlib roots only), and the copy-text screen v3
    `scripts/copy-text-screen-v3.py`;
  - **this round's inputs** (`campaign/fills/c1/inputs/c1-fill-nf/`): the import probe
    (`NFImportProbe.lean.txt`), the route probe with its seal controls (`NFRouteProbe.lean.txt`,
    `NFRouteSealControl.lean.txt`), the semantic-duplication probe (`NFDupProbe.lean.txt`), the
    brief review's probes (`NFReviewProbe.lean.txt`: the route's skeleton `rv_skeleton`, the
    verifier's entry `rv_entry`, sweep 0 as the scan fold `rv_sweep0`, the readings
    `rv_inputSymbol_congr` and `rv_moveInputPos_le`; `NFReviewVProbe.lean.txt`: a one-sweep `V`
    meeting the acceptance lemmas' hypotheses; their 30 seal controls
    `NFReviewSealControl.lean.txt`; `NFReviewDupProbe.lean.txt`), the import overlay
    (`NDNormalFormOverlay.lean.txt`) and the screen population; the order list
    `campaign/fills/c1/orders/c1-fill-nf.txt`, the base sorry
    set, the screen base and the pre-ship log (`campaign/fills/c1/logs/c1-fill-nf-*`). The route's
    design note is `campaign/items/c1/nf/NF-route-design.md`.
- **Before anything else, run Part 1 of the addendum**: the preflight, with its stop rule
  (E-RES). Fetch the cache for your roots only (39); never run the unfiltered
  `lake exe cache get`. If Lean cannot start, follow Part 2 exactly. **If Lean never runs, do not
  draft proofs blind**: deliver the environment report only.
- **Branch at exactly that commit, not at the campaign tip:**

  ```sh
  git checkout -b fill/c1-nf @ANCESTOR@
  git rev-parse HEAD        # must print @ANCESTOR@
  git rev-parse HEAD:TCSlib/Complexity/ClassNP/NDNormalForm.lean
  # must print 5150734a89b935396dee9516911030497f2034d1
  ```

  Record the base hash in `REPORT.md`. Never rebase, merge or cherry-pick.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-c1-nf.zip`. It contains:
  - `REPORT.md` and the full modified source;
  - a `git format-patch` series against your base, and a git bundle whose only prerequisite is
    your base;
  - **the environment logs** (`evidence/logs/` at the clone's root: preflight, cache store, roots,
    cache fetch, manifest check), this item's bootstrap and final sweep logs with **each module's
    time and maximum memory**, and the axiom log;
  - the seal test's source, its controls and both outputs; both screen outputs; and
    `SHA256SUMS`.
- **Checkpoint zips.** After each checkpoint below, commit and write `fill-c1-nf-cp<N>.zip`
  (`N` the checkpoint's number, 1 to 8) with the same contents as of that commit (the final sweep
  may be your module's tail check only; every log in it is a finished run, or is marked partial).
  Deliver the latest if the session ends early.

## Base, line numbers and what lands around you

- **Your base's Lean content is the campaign's tree after PR #179**, which merged `main` into the
  campaign (@ANCESTOR@ adds records only). Lines in this brief are those of your base's tree, where
  `NDNormalForm.lean` is 88 lines (1 public declaration, no private).
- **The overlay is your first edit** (region (a)): add, after line 7, exactly
  `import TCSlib.Complexity.TuringMachine.Build.NDHost` and
  `import TCSlib.Complexity.TuringMachine.Build.StepBlock`
  (`campaign/fills/c1/inputs/c1-fill-nf/NDNormalFormOverlay.lean.txt` is the file after it). The
  pre-ship elaborated it: exactly the target's sorry warning, nothing else. After the overlay every
  line below line 7 moves down by two; this brief cites the base's numbers.
- **In flight, merging after your base and invisible to it:** E-Q cont1's landing (PR #176,
  `Diagonalization/NTimeDiagonalizer`, in your order list as an import of the downstream
  `NTimeHierarchy`; every public statement frozen; it proves `exists_queryTM`, so its sorry count
  drops from two to one) and `NP`'s closure under `≤ₚ` (PR #177, `ClassNP/Reductions`, in your order
  list as an import of the `ClassNP` facade; additive). Nothing cites your file but
  `NTimeHierarchy`, by statement. PR #175 (`SpaceComplexity`) is outside your order list.

## Parallel batches this round

None in `NDNormalForm.lean`. E-D (`exists_diagonalizer`, `NTimeDiagonalizer`) may run beside you;
it cites `guessRunTM`, the bounded instance of your host, and never your file.
`Complexity.ntime_hierarchy` (`NTimeHierarchy`) is proved from your target's statement, which is
frozen.

## What this is

**The linear-overhead coded normal form** ([AB09, §3.2]; [BGW70]-style guess-then-verify). For
every `N : FinNDTM Bool` there are `M : CodeNDTM` and `C` with
- **forward**, `N.AcceptsWithin x t → M.toFinNDTM.AcceptsWithin x (C * (t + 1))`;
- **backward**, `M.toFinNDTM.AcceptsWithin x t → ∃ t', N.AcceptsWithin x t'`.

`CodeNDTM` fixes **two** binary work tapes and the states `Fin (numStates + 1)`
(`TuringMachine/NDCodes.lean:99`). `AcceptsWithin x t` is a choice word of length **exactly** `t`
whose run halts with output **exactly** `[true]` (`ClassNP/NTIME.lean:96`; read it through
`Turing.FinNDTM.acceptsWithin_iff`). The backward direction is unbounded and claims no all-branch
halting: a runaway guess may run forever. `C` depends on `N` only.

**Where it stands.** Nothing of it is proved. The host it needs landed in PR #174 at the
maintainer's API gate (gate 85), proved, together with the controller's contract, so that this fill
writes the display, the verifier and the transfers, and composes nothing at the host level.

**Proved modulo, exactly:** none. **A complete delivery has no `sorryAx` in the target.**

**Read first:**
- the design note `campaign/items/c1/nf/NF-route-design.md` (the route, the rulings D1–D4);
- `Build/NDHost.lean` from `Turing.GuessRunPhase.CtlState` (line 571) to the end: the host, its
  case lemmas and the five lemmas of the controller-stopped instance (from line 1707);
- the target's docstring (lines 45–77), which this brief refines in one place: the display carries
  the choice bit, the claimed reads and an end flag; the state and the action are recomputed, never
  guessed (ruling D3);
- `Build/Catalog.lean`'s rows `scanTM` (from line 12835, with `scanTM_run_ofCfg`, `scanFold`,
  `scanResult_fold`), `skipTM`, `skipBackTM` and `clearTM`, and `Build/StepBlock.lean` lines
  136–198.

**Pre-ship check** (the maintainer, against the replay snapshot of your base's tree; its log is
`campaign/fills/c1/logs/c1-fill-nf-preship.log`):
- the overlay elaborates with exactly the target's sorry warning;
- the import probe: **149 checks, 0 errors** (the first round's 88 names and the brief review's
  61);
- the route probe (sealed, 9 definitions sealed and the 4 `@[simp]` TCSlib definitions erased; its
  9 controls close unsealed and fail sealed, each at its own goal) proves the packaging and the
  trivial setup's hypotheses (below), each on the standard axioms or fewer;
- the brief review's probes, sealed over 39 definitions: `rv_skeleton` (the target from three
  obligations on `V` through the packaging, the trivial setup and the two acceptance lemmas),
  `rv_entry` (the entry configuration is `streamStartCfg x 0 qentry s`), `rv_sweep0`,
  `rv_inputSymbol_congr`, `rv_moveInputPos_le`, and a one-sweep `V` (`rv_V_verdict`), each on the
  standard axioms or fewer; their 30 controls close unsealed and fail sealed;
- the order list: **112 modules, 39 Mathlib roots, 20 base sorries in 9 modules**;
- the screen base (20 files): 1,344 declarations, 862 pairs, 274,615 characters; your file in no
  pair;
- lint: `ClassNP` 0 FAIL, 17 WARN over 21 files; the policy linter 0 findings on your file.

## Owned regions and targets (modify these and nothing else)

`TCSlib/Complexity/ClassNP/NDNormalForm.lean`:
- **(a)** the imports, lines 6–7: add exactly the overlay's two;
- **(b)** new private declarations between `namespace FinNDTM` (line 43) and the target's
  docstring (line 45), or in a `namespace` or `section` of your own opened there and closed before
  it. Every new declaration has a docstring, and every proof over 20 lines a literal
  `**Proof sketch.**` paragraph (`policy.md` §3). Docstrings are public-facing library text: no
  campaign labels, dates or session narrative; provenance goes in `REPORT.md`. The replay leaf's
  docstring says which public rows it is not and what was missing (`policy.md` §1): `scanTM` reads
  one tape, and `StepBlock`'s `recordTM` reads records on `k + 2` tapes;
- **(c)** the target's body, line 84 (`sorry`);
- **(d)** the status text: the module docstring's lines 20–22 (the two sentences on where the
  statement lived and why it moved) and 30–31 (the "(sorried; phase P3.3)" status), and the target
  docstring's status phrase on line 46 ("spec, fill pending — phase P3.3") and its "(round-1 finding
  6)" on line 66. Rewrite them as public-facing text: no campaign labels (no phase, gate, round,
  finding or fill names, no `audits/` or `campaign/` paths, no dated rulings). Propose an
  `**Implementation.**` paragraph for the target's docstring in `REPORT.md`; the maintainer lands
  it.

**Target:** `Turing.FinNDTM.exists_codeNDTM_accepts_linear` (line 78), its statement frozen.

### Hosts (binding; the host-first rule, `policy.md` §1, `workflow.md` §2)

- **`M` is the controller-stopped instance of the host**, relabeled:
  `guessCtlRunTM P pexit 0 q₀ δ stop false V qentry acc rej` with `k = 2` (tape `0` is A, the
  display; tape `1` is B, the replay tape), packaged into a `CodeNDTM` by
  `Turing.NDTM.relabelState` along `Fintype.equivFin`. Never compose `phaseHostND` yourself, never
  write a second writer, and never re-prove a handoff, a stop or an acceptance lemma of the host.
- **The setup `P` is trivial**: a two-tape machine whose start state is its exit `pexit`, so
  `TP = 0`. The route probe's `nfr_setup` proves the host's five setup hypotheses for it at time
  `0` on every tape (`runFrom_zero`, `initCfg_eq` and `Cfg.init`'s field equations); copy it as the
  private `nf_setup`.
- **The packaging** is the route probe's `nfr_pack`: for any finite-state `H : NDTM 2 Bool S`, some
  `M : CodeNDTM` has `M.toFinNDTM.AcceptsWithin x t` iff some choice word of length `t` halts `H`
  from `H.initCfg x` with output `[true]`. Copy it as the private `nf_pack` (keep its proof: it
  reads `toFinNDTM` through `CodeNDTM.toFinNDTM_tm`, `_k`, `_State`, and the relabeling through
  `relabelState_q₀` and `relabelState_runWith`). The host's state type is finite and has decidable
  equality by the published instances (`GuessRunPhase.instFintypeCtlState`,
  `instDecidableEqCtlState`), given those of its fibers: `V`'s state type, and so the fold's and the
  leaf's, must be a `Fintype` with `DecidableEq` (hold a record as `Fin _ → Option Bool`, not a
  list).
- **The verifier `V`** is a deterministic two-tape machine composed by `Turing.phaseHostTM`
  (`Build/Seam`, with `phaseHostTM_run`, `_run_le`, `_q₀`, `_tr_of_red_none`, `_tr_of_red_some`)
  over the published rows `Turing.scanTM` (sweep 0: `scanTM_run_ofCfg`, `scanFold`, `scanKeep`,
  `scanResult_fold`), `Turing.skipTM` and `Turing.skipBackTM` (`skipTM_run_ofCfg`,
  `skipBackTM_run_ofCfg`: the returns of A and B), `Turing.clearTM` (B's clear,
  `clearTM_run_ofCfg`; not the R3 row `clearTM_run`) and your one replay leaf. Its entry
  configuration is the host's `Turing.guessRunCfg cP 0 s qentry`: the stream `s` on A from cell
  `0`, A's head at `0`, B blank with its head at `0`, the input head at `1`, the output empty
  (read through the `guessRunCfg_*` field equations and `nfr_setup`'s configuration).
- **`V` is silent**: no leaf of `V` emits output. The host's verdict leaf emits the one bit.

### The route (binding where it names a row; the rest is the recommended shape)

**The display.** One record per step of `N`'s run, of fixed width `W = 2k + 4` (`k = N.k`): the
choice bit `bᵣ`; the `k + 1` claimed reads `σᵣ` (the input's, then each work tape's), each an
`Option Bool` in a 2-bit block; the end flag `endᵣ`. **The per-step actions are recomputed, never
guessed**: `aᵣ := N.tm.tr bᵣ qᵣ σᵣ`, with `qᵣ` tracked in each sweep's finite control.

**The guess** (ruling D3: a guessed end flag per record). The controller is `Q := Fin W × Bool` (the
position in the record, and whether the last completed record carried the end flag), with
`q₀ := (0, false)`, `δ (p, f) b := if p = W − 1 then (0, b) else (p + 1, f)` and
`stop (p, f) := (p = 0 && f)` (the flag is the record's last bit); `stop` holds exactly at a record
boundary after an end-flagged record. So a stopped stream is a sequence of
complete records whose last, and only last, record is end-flagged. A branch that never sets the flag
never stops; the statement allows it.

**`V`'s phases** (A's head is back at cell `0` after each):
1. **Sweep 0**, the control check, is **the published scan fold** on A:
   `Turing.scanTM 2 0 (scanFold δ₀) scanKeep a₀`, with your fold step `δ₀` over the stream's bits.
   From the entry it reaches `done (s.foldl δ₀ a₀)` at exactly `2|s| + 2`, no `done` earlier, with
   every tape and head as at the entry, so A needs no rewind (`scanTM_run_ofCfg`,
   `scanResult_fold`). `δ₀`'s state (a `Fintype` with `DecidableEq`) holds: the position in the
   record and the record read so far; `qᵣ`, from `N.tm.q₀`; the output summary, from
   `outputSummary [] = none` and updated by `summaryEmit`; a failure flag. At each record's end it
   recomputes `aᵣ` and checks that `endᵣ` is set exactly when `aᵣ.state = none`. Its verdict passes
   iff no check failed and the final summary is `some true` (`outputSummary_true`: exactly
   `[true]`). **Write no machine for sweep 0.**
2. **Sweep 1**, the input claims: each record's recomputed action moves the native input head
   (the same `SignType` move, so the same `moveInputPos`), and the claimed input read must equal
   the cell under it. The input head is not returned: no later phase reads the input, and the
   acceptance lemmas constrain only `V`'s state and output.
3. **Sweeps 2 … k + 1**, one per work tape `j < k`: tape `j` is replayed on B as 2-bit blocks, a
   visited cell as two nonblank bits encoding its `Option Bool` content and an unvisited cell as two
   blanks, so the visited region is contiguous and nonblank. B's head follows tape `j`'s claimed
   head (a move of one cell is two cells on B); each claimed read is checked against B's block, and
   the recomputed write is applied. Then B's head goes to the visited region's first cell and B is
   cleared, by three published rows on B: `skipTM` (over the region from B's head,
   `skipTM_run_ofCfg`; it leaves the head one past the region's right blank); `skipBackTM`
   (`u :=` the whole region, `skipBackTM_run_ofCfg`); `clearTM` (`clearTM_run_ofCfg`), which leaves
   B blank with its head at the region's first cell. The region is never empty: every record writes
   its block.
4. **The verdict:** `acc` iff every sweep passed; `rej` at the first failure.

**A's return after a replay sweep.** A replay sweep ends with A's head on the blank after `s`
(cell `|s|`). `skipBackTM_run_ofCfg` needs the head **one cell past** that blank, so first step
right with `skipTM` on A (`skipTM_run_ofCfg` at `w := []`), then run `skipBackTM` on A at
`u := s`, as the host does after its writer. `Build/Rewind`'s `rewindTM`, which starts on the
blank, is outside your imports.

**One leaf for sweeps 1 to `k + 1`.** They share the record scan and the recomputation: write one
leaf parameterized by the tape it replays (the input, or work tape `j` on B), not `k + 1` copies.
It is a single own-file machine reading A one cell per step (A stationary while it works on B),
with its run lemma by induction over records through `MultiTapeTM.step_of_some` and the
`Action.apply_*` field equations; no private loop driver. The sweeps are own-file leaves by the
design note (its "Leaves and sizes" table; D2 moved only the guess-run host to `Build/NDHost`):
their contract is this file's display format, and no other consumer exists.

**Recommended shape.** State each leaf's run lemma as "after `r` records, a pure fold of the
stream" (as `scanTM_run_ofCfg` does), and `V`'s lemma as a characterization: its first verdict at a
time `T(s)`, `acc` iff every fold passes. That one lemma gives `hV`, the forward `hacc` and
`hfirst`, and the backward "accepted ⇒ every check passed"; the transfers then never touch a
machine.

**`hV`, the backward lemma's obligation (binding):** for **every** stream `s` that first stops the
controller at its end, well formed or not in content, `V` reaches a verdict, `acc` or `rej`, from
`guessRunCfg cP 0 s qentry`, and is at neither before. Each replay sweep ends at the blank after
`s` or rejects earlier; B's replay moves its head at most two cells per record; and B's clear
(`skipTM`, `skipBackTM`, `clearTM`) runs over the visited region, which is contiguous and nonblank
on every stream. So `V` is total; prove it as a lemma of its own, not inside the backward
transfer.

**The transfers.**
- **Forward** (`guessCtlRunTM_accepts_of`): from `N.AcceptsWithin x t`, take its word, the first
  time `t₀ ≤ t` its run halts, and the display `s` of those `t₀` steps (`|s| = W · t₀`); `s` first
  stops the controller at its end (`hslive`, `hsstop`); `V` is at `acc` at `TQ` (`hacc`), at
  neither `acc` nor `rej` before (`hfirst`), with an empty output (`hnil`); `TQ = O(k · W · t₀)`;
  and the lemma gives a word of length exactly `C · (t + 1)` once
  `0 + 2 |s| + TQ + 11 ≤ C · (t + 1)`. `t₀ ≥ 1`, since the start state is live.
- **Backward** (`guessCtlRunTM_stream_of_accepts`, with `hV`): an accepting word of `M` gives a
  stopped stream `s` that `V` accepts with an empty output. By induction on records, a passing
  display is a genuine run: if the claimed reads before record `r` are genuine, so are the
  recomputed actions, so each replayed tape at `r` is genuine, so sweeps 1 to `k + 1` make `σᵣ`
  genuine. The run halts at the flagged record with output `[true]`, so `N.AcceptsWithin x t'`
  with `t'` the record count and the record bits as the word.

**The ledger.** `C := C_N`, uniform in `x` and `t`: each sweep and rewind is `O(W · t₀)`, B's
replay and clear `O(W · t₀)`, `V` in all `O(k · W · t₀)`, and the `+ 1` covers `k = 0` and the
constants.

**Edge cases that must stay true:**
- `N.k = 0`: no tape sweep; `V` is sweep 0, sweep 1 and the verdict, and `W = 4`;
- a run halting at its first step (`t₀ = 1`): one record;
- a run whose input head moves left of the first cell, or right past the input: the claimed read is
  the blank there, and `moveInputPos` is the machine's own move;
- a write of a blank (`some none`) on a work tape: the block encodes `none`, and the cell stays
  visited;
- the output: a halting transition may emit (`summaryEmit` covers it); a run emitting twice is
  rejected (`some false` is irreversible);
- a stream whose claims are wrong: `V` rejects it, and still reaches its verdict (`hV`);
- a claimed-read block with the unused fourth code: sweep 0 rejects it (or it decodes to `none`;
  say which in `REPORT.md`).

## Gate guidance (binding)

- **The P3.3 statement gate and gate 38** froze the statement: the constant `C` is uniform, the
  forward budget is `C · (t + 1)` exactly, the backward direction unbounded.
- **Gate 85** (the host's API gate): the host's acceptance lemmas are the route; their hypotheses
  `hslive`, `hsstop`, `hacc`, `hfirst`, `hnil` and `hV` are your obligations, stated as they are.

## Cited infrastructure (public and proved at the issue commit; `NFImportProbe.lean.txt`)

The probe's names: the host, its state family, phases and redirects with their 19 case lemmas,
`guessRunCfg` and `streamStartCfg`, the five lemmas of the controller-stopped instance and the
writer's contract; `phaseHostND` and its run; `phaseHostTM` and its run, bound and transition
equations; `skipTM`, `skipBackTM` and their framed runs; `inputRewindTM` and its two lemmas; the
output summary and its laws; the relabeling with its run and field equations; the run algebra
(`runWith_nil`, `_cons`, `_append`, `runWith_of_halt`, `runWith_mapState_of_agreeOn`,
`MultiTapeTM.toNDTM_initCfg`, `toNDTM_runWith`); `FinNDTM.AcceptsWithin` and `acceptsWithin_iff`;
`CodeNDTM` and its field equations; `step_of_some`, `initCfg_eq` and the `Cfg.init_*` and
`Action.apply_*` field equations; `Fintype.equivFin`. Also: N's step through
`NDTM.stepWith_of_some` and `stepWith_of_halt`; `MultiTapeTM.step_of_halt`,
`runFrom_succ_eq_step'`, `runFrom_add`, `runFrom_zero`; the readings of the input head
(`Cfg.inputSymbol_of_zero`, `Cfg.inputSymbol_of_end`, `inputSymbolInner`) and of the work heads
(`Cfg.workTapeSymbols_eq`); `moveInputPos_*`; `FinTM.bufferTape_eq`, `_of_neg`, `_nat`, `_left`;
the field equations of `guessRunCfg`, `streamStartCfg`, `Cfg.mapState`, `Action.mapState`;
`scanTM`, `scanTM_run_ofCfg`, `scanFold`, `scanKeep`, `scanResult_fold`, `clearTM`,
`clearTM_run_ofCfg`; the two `CtlState` instances.

## Ground rules (binding)

1. **File ownership, by region.** Only regions (a)–(d) of `NDNormalForm.lean`. List every new
   declaration with its role.
2. **Statement freeze** over the target.
3. **No new public declaration.**
4. **Escalation, item by item:** on anything unprovable as stated, stop **on that item only**,
   record the obstruction mathematically, and **continue with every item that does not depend on
   it**. The forward transfer does not depend on `hV`; the packaging depends on nothing.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports.** Exactly the base's two and the overlay's two; add none.
7. **One proof per shared argument.** Never write a second host, writer, phase composition, handoff,
   scan, clear, step right, rewind, input rewind or run decomposition. Never re-walk
   `ClassNP/ExhaustiveReplay`'s `xr_` privates (replays of a fixed NDTM on a choice word),
   `ClassNP/Nondeterminism`'s private `choiceCore` replay, `Build/NDHost`'s private `wr_` and `gr_`
   helpers, `Build/StepBlock`'s `recordTM` family or `CodeSimulator`'s private `h1` record family:
   they are models to read, not to copy.
8. **Size.** No cap; file size alone is not a driver. Report the final line count and the public
   and private declaration counts (base: 88 lines; 1 public, 0 private).
9. **Continuation budget.** A partial zip states the checkpoints reached, the open declarations
   (each with a literal "Proof sketch") and the target's axiom walk. A partial is expected and
   fine; an unreported gap is not.
10. **The pinned base, and no unfolding (user, 2026-10-16).**
    - Cite only declarations public at your base, and your file's own definitions and privates.
    - **Never unfold a definition of another file**, and no definitional closure either.
      - The host and its families: through their case lemmas (`GuessRunPhase.ctlState_*`,
        `guessCtlRunPhases_*`, `guessCtlRunRed_*`) and the run and acceptance lemmas; never by
        unfolding `guessCtlRunTM`.
      - `guessRunCfg`, `streamStartCfg`, `Cfg.init`, `Cfg.mapState`: through their `simps` field
        equations (pointwise: `funext` before `rw`).
      - `FinNDTM.AcceptsWithin`: through `acceptsWithin_iff`. `CodeNDTM.toFinNDTM`: through
        `CodeNDTM.toFinNDTM_tm`, `_k`, `_State` (by `simp only`, as `nfr_pack`).
      - `NDTM.relabelState`: through `relabelState_q₀`, `_tr` and `relabelState_runWith`.
      - `phaseHostTM`: through `phaseHostTM_q₀`, `_tr_of_red_none`, `_tr_of_red_some` and its runs.
      - `outputSummary`, `summaryEmit`: through their laws.
    - **Scope (user, 2026-10-23):** this binds TCSlib's own definitions. Core and Mathlib
      definitions may reduce in a `rfl`, `decide` or `show` step, but are never passed to `simp`,
      `rw` or `unfold`; use their equation lemmas.
    - **The machine model's primitives** (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
      `NDTM.runWith`, `Cfg.mapState`) are read through their lemmas. Unfold `step` and
      `Action.apply` only for a leaf defined in your own file, and prefer `MultiTapeTM.step_of_some`
      and the `Action.apply_*` field equations there too; the inspection table lists each such
      unfolding as an own leaf's, not as a finding. An own leaf's unfolding is by `unfold`, `rw`
      or `simp only` with the definition (listed in the inspection table), never by `show`,
      `change` or `rfl` (the seal rejects those). **`N.tm.tr`** is `N`'s own table: apply it,
      never unfold it.
    - Your own file's definitions may be unfolded, but prefer their laws.
    - If a fact you need about another file's definition has no published lemma, **stop on that
      item and escalate** (ground rule 4), naming the lemma you need.
    - **Self-check by both methods** (neither alone is complete):
      - a **seal test**: a scratch copy of your module with `attribute [local irreducible]` on
        every other-file TCSlib definition your proofs mention, from your first private on. Start
        from the route probe's 9 (`CodeNDTM.toFinNDTM`, `NDTM.relabelState`, `NDTM.initCfg`,
        `Cfg.init`, `Cfg.mapState`, `NDTM.runWith`, `FinNDTM.AcceptsWithin`,
        `MultiTapeTM.runFrom`, `MultiTapeTM.initCfg`) and extend: at least `guessCtlRunTM`,
        `GuessRunPhase.CtlState`, `guessCtlRunPhases`, `guessCtlRunRed`, `guessRunCfg`,
        `ndWriterTM`, `NDTM.phaseHostND`, `phaseHostTM`, `skipTM`, `skipBackTM`, `inputRewindTM`,
        `StepBlock.outputSummary`, `StepBlock.summaryEmit`, `MultiTapeTM.step`,
        `MultiTapeTM.toNDTM`, `NDTM.stepWith`, `Action.apply`, `Action.mapState`,
        `FinTM.bufferTape`, `moveInputPos`, `Cfg.inputSymbol`, `Cfg.workTapeSymbols`,
        `streamStartCfg`, `scanTM`, `scanResult`, `scanFold`, `scanKeep`, `clearTM`, and any action
        builder your leaf uses (`FinTM.controlAction`, `tapeAction`, `inputMoveAction`). Add
        `attribute [-simp]` on the four `@[simp]` TCSlib
        definitions (`Action.apply`, `Cfg.init`, `MultiTapeTM.initCfg`, `NDTM.initCfg`). A
        reducible `abbrev` (`Cfg.Halted`) cannot be sealed: read it through its body
        (`policy.md`). The copy must still elaborate, **with controls**: for each sealed
        definition, a goal that closes by `rfl` with nothing sealed and fails under the seal
        (recursive definitions, as `NDTM.runWith`, get usage controls); with
        `GuessRunPhase.CtlState` sealed, a control whose statement needs `CtlState` to reduce
        (those of `guessCtlRunPhases`, `guessCtlRunRed`) fails at elaboration: run those two with
        `CtlState` unsealed too, where they must fail at their `rfl`. The inputs ship 30 such
        controls (`NFReviewSealControl.lean.txt`);
      - an **inspection table** of every `rw`/`simp`/`simpa`/`dsimp`/`unfold`/`show`/`change`
        argument in your diff, each other-file name classified (a theorem, or a definition: a
        finding).
      - **Ship the raw outputs** of the seal and its controls, with their commands and exit
        statuses. **A seal not run, or a seal without controls that fail sealed and close
        unsealed, is a checklist failure.**
    - List every declaration you cite outside your file. If you cite more than the probe's list,
      add them to a copy of the probe and run it.
11. **MIG-1 compatibility.** Cite none of the six R3 canonical rows (`copyTM_run`,
    `transferTM_run`, `clearTM_run`, `compareTM_run`, `incrementTM_run_succ`,
    `incrementTM_run_overflow`); use the framed `_ofCfg` forms. Cite no private declaration of
    another file. Keep your new privates under the `nf_` prefix (`Nf`/`nf` for types and
    definitions; the prefix is unused in the tree). A `private inductive` with
    `deriving DecidableEq` gets a public instance name: check that no file or open PR has it and
    report it (`workflow.md` §4, counting public names), or write the instance as a
    `private instance`.

### Checkpoints (for a partial; ground rule 9)

1. **The overlay and the display:** the record layout, the display of a run's first `t₀` steps,
   its length `W · t₀`, the controller, that a display first stops the controller at its end, and
   conversely that a stream which first stops it at its end is `n ≥ 1` complete records with only
   the last flagged; `nf_setup` and `nf_pack` copied.
2. **Sweep 0:** the fold `δ₀` and its laws (its run is `scanTM_run_ofCfg` with `scanResult_fold`).
3. **The replay sweep** for the input (sweep 1).
4. **The replay sweep** for a work tape on B (sweeps 2 … k + 1) and B's clear (`skipTM`,
   `skipBackTM`, `clearTM` on B).
5. **`V`**: the composition, its totality (`hV`) and its verdict on a display.
6. **The forward transfer** and the ledger.
7. **The backward transfer**: a passing display is a genuine accepting run.
8. **The target.**

Each may land alone. **Add no new admission:** a helper is inserted only once proved. The freeze
check for a partial is the axiom walk: `sorryAx` reaches the target only through its own open
body. **One checkpoint, one commit, one zip, delivered at once.**

## Duplication governance (binding)

Run the text-level screen **before and after**, **one run at a time, under `nice -n 10`**
(`campaign/standards/TEMPLATE.md` failure mode 5; `policy.md`, **Duplication**). Run the before
screen right after branching, beside the bootstrap: it must equal the screen base. Run the after
screen once, at the end, beside the final sweep; checkpoint zips carry the tail check, the seal
and the axiom prints, not a screen.
**Run each screen on a frozen copy of its commit** (`git worktree add <dir> HEAD`, the screen's
root `<dir>`).
- **Semantic duplication (required).** The text screen misses a private that re-derives a lemma
  already published (gate 69: six prefix arguments re-deriving `Turing.phaseHostTM_run_le`; gate
  72: a private `(workReadsK 2).length = 9`). For **every** private lemma you add, search for a
  published declaration that states it or a generalization of it: in the tree and on every open
  PR branch, by name and by statement (`git grep`), and by an `exact?` or `apply?` probe on the
  statement. **Cite proved material; never re-prove it.** `REPORT.md` lists, for each new private,
  the search made and its result. The pre-ship probe `NFDupProbe.lean.txt` poses the route probe's
  statements to `exact?`: none is published (one closes only by `rfl`, a reduction rule 10
  forbids).
- **The population** is 21 files
  (`campaign/fills/c1/inputs/c1-fill-nf/screen-population.txt`):
  - your file;
  - the files the route cites: `Build/NDHost`, `Build/Seam`, `Build/Catalog`, `Build/InputRewind`,
    `Build/StepBlock`, `Nondeterministic`, `StateRenaming`, `Configuration`, `Deterministic`,
    `NDCodes`, `ClassNP/NTIME`;
  - the known hazards: `ClassNP/ExhaustiveReplay` and `ClassNP/Nondeterminism` (replays of an NDTM
    on a choice word), `TuringMachine/ChoiceReplay` (an NDTM's run along a choice word read from a
    tape), `CodeSimulator` and `NDCodeSimulator` (record families and an interpreter core over a
    guessed stream), `Diagonalization/NTimeHierarchy`, `Simulation`, and `Build/Contract/Catalog`
    and `Build/Contract/Basic` (the contract forms of the rows; outside your imports).
- **The screen** is `scripts/copy-text-screen-v3.py`, on the repository paths.
- **The base** is `campaign/fills/c1/logs/c1-fill-nf-screen-base.txt`: **1,344 declarations, 862
  pairs, 274,615 characters** (MEASURED at your base's Lean; about 13 minutes under `nice -n 10` on
  the maintainer's host, peak memory 3.2 GB). Your file is in no pair.

```sh
P=campaign/fills/c1/inputs/c1-fill-nf
nice -n 10 python3 -I scripts/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-before.txt
# after your changes, again, only when the first run has finished
nice -n 10 python3 -I scripts/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-after.txt
```

- **A new cross-file pair** with an owned-file declaration on one side is listed in `REPORT.md`
  with its shared tiles and one disposition:
  - **idiom**: the shared text is a public row's invocation and the standard conversion around it
    (for example the `Cfg.mapState` field equations around a renamed run), and no lemma, public
    or private, is re-derived. Justify it in one line and go on;
  - **re-derivation of a published lemma**: cite the lemma instead, before the zip;
  - **re-derivation of another file's private**: keep yours, and list it as a promotion request.

  **None of these ends the item.** A pair at 90% or more is a copy.
- **Known hazards:**
  - the one-step identity `M.runFrom c 1 = M.step c` is re-derived inline across the catalog and
    is private in `CfgRecord` (`recordStep_runFrom_one`): if you need it, state it once and list
    it as a promotion request;
  - `ExhaustiveReplay`'s replays and `Nondeterminism`'s `choiceCore`: your sweeps replay claimed
    actions, not a fixed machine's run on a word; cite the run algebra, never a prelude copied
    from them;
  - `NDHost`'s `gr_` and `wr_` privates: the host's run and acceptance lemmas already state what
    they prove;
  - the record readers of `StepBlock` and `CodeSimulator`: a fixed-width reader on `k + 2` tapes;
    yours is on two, and is new;
  - the input read's congruence (equal input positions ⇒ equal `inputSymbol`, any tapes and
    states) is private in `ExhaustiveReplay` (`xr_inputSymbol_congr`) and `ZoneRebalance`
    (`zr_inputSymbol_congr`): state it once (from `Cfg.inputSymbol_of_zero`, `_of_end`,
    `inputSymbolInner`) and list it as a promotion request.
- List every new in-file pair with a one-line justification. Quote each screen's summary line and
  its new pairs in `REPORT.md`, which carries **"new copies: none"** (or lists each pair), and
  ship both full outputs as files (`screens/`).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; the cache **for your roots only** (addendum v2.6, Part 1,
  items 2–4; your order list's modules import 39 roots directly);
  **never `lake build`**, and never the unfiltered `lake exe cache get`. Use
  `scripts/lean_check_tree.sh` for every check, one Lean process at a time.
- **The cache tool's own compilation inside `lake exe cache get` is outside the one-Lean rule.**
  Do not stop, or open an escalation, for it or anything like it. Your own checks stay strictly
  one at a time: never two `lean_check_tree.sh` runs, probes or sweeps at once, and none while
  `lake exe cache get` runs. A screen may run beside one of them. **A process deviation never ends
  the item**: disclose it with its evidence and continue.
- **Budget, measured:** each screen about 13 minutes on the maintainer's host (peak 3.2 GB). The
  last 4-CPU fill host ran 2–3× slower than the maintainer's: expect about 30–40 minutes per
  screen and 25–40 minutes for the 112-module bootstrap. Reserve about an hour for the
  finishing sequence (the final sweep with the after screen beside it, then the REPORT and the
  zip), and use the rest for proofs.
- **Bootstrap** (addendum Part 1, item 5) from `campaign/fills/c1/orders/c1-fill-nf.txt`
  (**112 modules**), right after branching, logging each module's start and end time and maximum
  memory. **The base sorry-warning set has 20 entries in 9 modules**
  (`campaign/fills/c1/logs/c1-fill-nf-base-sorries.txt`). Yours is `NDNormalForm`'s one. Record
  the base list by name first, and report any difference.
- **Final checks:**
  1. `NDNormalForm`: zero errors, no sorry warning (for a partial, the target's only), and no other
     warning in anything you added.
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's.
  3. Re-run `NFImportProbe.lean.txt` (extended by your citations): 0 errors.
  4. **After every proof edit, the whole order list's tail from your module on**, not your
     module alone.
- **Axiom prints** (in a scratch copy of your module with `#print axioms` appended) for the target
  and every new private: within `[propext, Classical.choice, Quot.sound]`, no `sorryAx` for a
  complete delivery.
- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/ClassNP`, 0 FAIL (base:
  0 FAIL, 17 WARN over 21 files), and `python3 -I scripts/style_lint.py` on your file. No new line
  over 100 characters. Your file will pass 1000 lines: the size WARN that follows is expected, not
  a failure.

## Out-of-scope sorries you will see (leave every one untouched)

Everything in the base sorry set except your target: `exists_queryTM` and `exists_diagonalizer`
(`Diagonalization/NTimeDiagonalizer`), and the older function-level and space stubs of
`Simulation`, `Composition`, `Encoding`, `ClassP/TimeConstructible`, `Build/Wrappers`,
`Build/Loop` and `Build/Primitives` (the list in
`campaign/fills/c1/logs/c1-fill-nf-base-sorries.txt`). If a proof seems to *need* one of these
beyond a named citation, that is an escalation, not a license.

## REPORT.md checklist

- [ ] The preflight's numbers, the roots' count and the cache fetch's (quoted from the logs, the
      cache store's log included), **the logs copied into this zip**, the bootstrap with
      per-module time and memory, and the base blob check.
- [ ] The overlay only; nothing outside regions (a)–(d).
- [ ] The checkpoints reached (1–8), **one zip each**; the base hash and the ancestor check.
- [ ] Every new declaration with its role; the record layout and `W`; the controller; each leaf
      and its run; `V`'s phases and their order; each hand-built machine's docstring names the row
      it is not.
- [ ] `hV` as its own lemma; each edge case with the lemma that covers it.
- [ ] `C`, term by term: the guess, each sweep and rewind, B's replay and clear, the verdict, the
      host's `+ 11`.
- [ ] The base sorry list by name.
- [ ] Promotion candidates and escalations (each stated mathematically), or "none"; the proposed
      `**Implementation.**` paragraph for the maintainer.
- [ ] Rule 10: the declarations cited outside your file (from an elaborated-constant walk), the
      probe re-run as "N checks of M names", **the seal test with its controls and both raw
      outputs**, and the inspection table. Rule 11: a grep of your diff for the six R3 rows and for
      other files' private names.
- [ ] Duplication: both v3 screens, every new pair justified, the semantic search per private,
      "new copies: none".
- [ ] File size; the final sweep tail; the axiom prints; the lint line. The diff touches only your
      owned regions.

## Known pitfalls at this pin (hard-won)

- **The simps field equations are pointwise** (`Cfg.init_workTapes`, `guessRunCfg_workTapes`,
  `Cfg.mapState_workTapes` take the tape and the cell): `funext i p` before `rw`, or the step
  closes by unfolding and the seal rejects it.
- **`CodeNDTM.toFinNDTM`'s fields are dependent** (`k`, `State`, `tm`): read them together by
  `simp only [CodeNDTM.toFinNDTM_tm, CodeNDTM.toFinNDTM_k, CodeNDTM.toFinNDTM_State]` (as
  `nf_pack` and `NDCodeSimulator` do), not one by one with `rw`.
- **`AcceptsWithin` is exact length.** The forward lemma gives a word of length exactly `B`; choose
  `B := C * (t + 1)` and prove the lower bound `2 |s| + TQ + 11 ≤ B`.
- **The acceptance lemmas hide the word:** the forward one returns it, and the backward one returns
  the stream; never build or split a choice word yourself.
- **Under the seal, never write a host state yourself** (`⟨.pre, P.q₀⟩`, `Sigma.mk .run`): with
  `GuessRunPhase.CtlState` sealed, `CtlState SP SQ Q .run` does not reduce. Cite only
  `guessCtlRunTM_accepts_of` and `guessCtlRunTM_stream_of_accepts`, whose statements name none.
- **`guessCtlRunTM_stop_of_halted` is the backward lemma's first step**, already inside
  `guessCtlRunTM_stream_of_accepts`: cite the latter, not both.
- **No core or Mathlib definition is reduced outside `rfl`, `decide` or `show`**: write
  `congrArg (fun b => [b])`, not `congrArg List.singleton`. Recursive definitions get usage
  controls, not delta controls.
- `omega` with products as atoms (`ring` first). The linter needs a literal "Proof sketch" before
  every `sorry` (partial only).
