# External audit pack — H1-H: the H1 hosted-clock harvest (statement gate)

Campaign: the Arora-Barak chapters 3-4 plan, cluster C1 (`Diagonalization/NTimeHierarchy.lean`, [AB09,
Theorem 3.2] at linear overhead). The C1 host-contracts gate (`audits/c1-hosts-statements-findings.md`,
PASS 0/0/11, attached verbatim) ruled, in its answer to open question 5, that the private H1 hosted
clock of `TuringMachine/CodeSimulator.lean` be harvested into public contracts **before the brief of
the interpreter core `R`** (`Turing.exists_ndInterpreterCore`). **This gate audits the harvest: two
public machines and three public theorems in a proposed new module `Build/StepBlockLoop.lean`
(namespace `Turing.StepBlock`), their five private helpers, and the companion edit of
`CodeSimulator.lean` that deletes the harvested private declarations and re-points the three that
stay.** All ten declarations are proved (no `sorry`); nothing is landed. Record findings in
`audits/h1-harvest-statements-findings.md`.

| File (bundle path) | Content |
|---|---|
| `audits/evidence/h1harv/H1Harvest.lean.txt` (540 lines, MEASURED) | **the unit**: one part, the body of the new module, `-- @landing TCSlib.Complexity.TuringMachine.Build.StepBlockLoop`, `-- @imports` `Build.StepBlock`, `Build.CounterLoop`, `Build.VirtualInput`; 10 declarations (5 public), 0 sorried |
| `audits/evidence/h1harv/PostHarvest-CodeSimulator.diff` | **the companion edit**: `CodeSimulator.lean` at the tip against its landing form |
| `audits/evidence/h1harv/H1HarvestOverlay.lean.txt` (4,077 lines) | **the full-file overlay**: the tip's `CodeSimulator.lean`, byte for byte, then the unit's part, then §C (the corollary direction), §S (sanity) and §X (axiom prints) |

Supporting evidence: the design note `audits/evidence/h1harv/H1-harvest-design.md` ("design §n"
below); the probes `audits/evidence/h1harv/probes/` (`ConsumerProbe-tail`, `ReplayProbe`, the landed
module `StepBlockLoop`); the scripts `audits/evidence/h1harv/scripts/` (`runall.sh` regenerates every
log and **fails closed**: each check states its expected outcome, the last line counts failures,
the exit status is nonzero on any); the logs
`audits/logs/h1-harvest-statements-{elaboration,cutcheck,freeze,names,axioms}.log`.

**Bundle:** this pack first; the standards (`audits/TEMPLATE.md`, `policy.md`, `workflow.md`); the
design records (`machine-library-design.md`, `backlog.md`, `AroraBarakChapters3-4Plan.md`); the
design notes (this gate's, C1's, H2's round 2); the files under audit, the probes, the scripts and
the logs; the C1 and H2 gate records and MIG-0b's round-2 notes; and every library file the
statements and sketches cite (`BUNDLE-FILES.txt` lists them in order). `Build/Catalog.lean` (653 KB)
is not attached: the statements use only its `FlagPhase.run` (`Catalog.lean:163`:
`inductive FlagPhase | run | rewind (flag : Bool) | done (flag : Bool)`).

**Provenance (drafter).** A maintainer sub-agent wrote the files. **Base: the campaign tip
`e831b5b0`** (backlog-only; Lean content as at `6fbdefac` and `13a16a69`), exported read-only by
`git archive`; that is the brief's base `2c3c975a` plus **MIG-0b (PR #90, merged as `79c30a89`)**
and PR #91 (proof sketches in `Build/StepBlock.lean`, comments only). Lean ran only through
`tools/leanelab.sh`, against the olean snapshot `oleans-lm0b` (post-MIG-0b; its content checks are
the elaboration log's §0) with the packages of `wt-h1harv` (same `lake-manifest.json` and
`lean-toolchain` as the tip; Lean `v4.25.0`). Every check below was run there by `runall.sh`.
Every `file:line` is at the tip. History: the gate was first run at `2c3c975a` (snapshot
`oleans-lc1`, MIG-0b still pending) and passed 40 of 40 checks; that run's logs were lost when the
session stopped at about 16:22 UTC; the only change to the unit since is `loopOrbit_succ`'s proof,
which now cites MIG-0b's `roundOrbit_succ` (design §7). The open PRs #92 and #93 were read as text
only. The transcripts are the drafter's; the maintainer's re-run of `runall.sh` is the acceptance
replay.

**Maintainer note, after the pack was built (2026-10-14).** PRs #92 (the B6 hosts) and #93 (ARM
comments and imports) are now merged, and the campaign tip is
`1b6b972cf0ba0ffb8ccbac421ae1b894400783a1`. Neither PR changes `CodeSimulator.lean` or the new
module's imports (`Build/StepBlock`, `Build/CounterLoop`, `Build/VirtualInput`). #92 changes
`Encoding` and `StateRenaming`, which are upstream of them.

The maintainer re-elaborated the unit and the overlay at `1b6b972c`, read-only, against
`oleans-lb6` (#92's replay output, 270 of 270):
- the unit: 0 errors, 0 warnings;
- the overlay: 0 errors and exactly the two headline sorry warnings, at lines 2746 and 3278. Its 10
  axiom prints use only `propext`, `Classical.choice` and `Quot.sound`.

So this pack's "#92 first" case now holds. The landing runs at the merged base with
`SelfUniversal` in its replay set (9 modules), and it rebases the `TuringMachine` facade edit onto
#92's.

Three bundled files are at `1b6b972c`, not `e831b5b0`: `backlog.md`, `TuringMachine/Encoding.lean`
and the `TuringMachine` facade. Their differences are #92's additions and the maintainer's records.
This pack's `file:line` references to those three files are at `e831b5b0`. Every other bundled
library file is identical at both commits.

## What the gate covers

1. **The two machines**: `loopTM k`, the counter loop over the step block (formerly the private
   `h1ClockTM`), and `hostedLoopTM k`, the same under Z1 (formerly `h1HostedClockTM`).
2. **The three contracts**: `loopTM_run` and `hostedLoopTM_run` (generalizing `h1Clock_effect`
   and `h1HostedClock_effect`), and the reading lemma `hostedLoop_read`.
3. **Ruling 5's three generalizations**, and three free ones (design §3).
4. **The landing form**: the new module, the eight deletions and three re-pointings in
   `CodeSimulator.lean`, the status text, the facade, and the freeze.
5. **The consumer fit** for `R` (two probes), the **MIG-0b interaction**, and the **sequencing**
   with the open PRs #92 and #93.
6. **Homes, names, registry row, and the duplication ledger.**

Out of scope: tactic proofs (machine-checked); `R`'s own statement and its other phases (gated
and passed at C1); the step block's contract `roundTM_effect` (gated at H2-S); the counter loop's,
the round layer's and Z1's contracts (gated earlier); `CodeSimulator`'s headlines and canonizer.

## Decisions in force (verify that the files reflect them)

* **Ruling 5 of the C1 gate, verbatim** (`audits/c1-hosts-statements-findings.md:184`): "Register
  and complete the H1 hosted-clock harvest before R's consumer brief: arbitrary represented live
  start with the stream already installed, the early-escape time bound, and live exits usable by
  the caller. H2's open promotion findings do not disappear because this C1 gate passes. The
  required generalizations are credible from the visible represented-run invariant and exact
  escape theorem, but they are not yet supplied public contracts in this unit." Its note N3: "Do
  not fill R by copying H1 privately."
* **C1's user decisions (2026-10-13)**: guess first; nondeterministic codes interpreted through
  their replay machine with H2 unchanged at `k = 3`; `R` reads its input through a bounded window
  copy and input locality (decisions 1, 3, 5).
* **H2-S round 2 (CLOSED 0/0/8) and H2-M (PR #88)**: the step block is public in `Build/StepBlock`
  under its round-2 names; **H1's round-time function `h1RoundTime` stays private until MIG-0b's
  round adapter** (O7; `backlog.md:575`); CO-RF is a consumer obligation of unclocked emitting
  hosts; the `RoundContract` envelopes are work-head envelopes (R2-8).
* **Hosts come first** (`policy.md` §1): a private host is harvested into the shared construction
  layer before a second consumer is briefed. **File size is not a driver** (user). **No private
  copies** without human approval (`policy.md` §1, *Duplication*).

## Dependencies and sequencing

* **MIG-0b (PR #90) has landed** (`79c30a89`; the brief expected it pending). It made
  `counterLoopOrbit` (`CounterLoop.lean:651`) an `abbrev` of the core's `Turing.roundOrbit`
  (`Build/Contract/Basic.lean:708`) and added `roundOrbit` to the unfolding step of the private
  `h1Clock_orbit` (`CodeSimulator.lean:2892`). **No statement of the unit mentions
  `counterLoopOrbit`, `roundOrbit` or a round-time function, and no proof unfolds the orbit**: the
  successor step is `loopOrbit_succ := roundOrbit_succ …` (`Contract/Basic.lean:713`) through the
  abbreviation. The harvest deletes `h1Clock_orbit` together with #90's edit (design §7).
* **PR #92** (`lean/b6-hosts` `6158e48f`, open; B6 hosts) overlaps the harvest in four places
  (design §8; file lists in the log's §8):
  - **the `TuringMachine` facade** (both add imports beside `Build.StepBlock` and `## Contents`
    bullets: textual neighbours; the second to land rebases its hunks);
  - **`Encoding` and `StateRenaming`**, which lie in the new module's forward closure (whichever
    lands second re-elaborates `Build/StepBlockLoop` and `CodeSimulator` on the merged tree);
  - **`SelfUniversal`** (new, imports `CodeSimulator`): it joins the harvest's replay set if #92
    lands first; it cites the unclocked block only (`roundTM_effect`, `roundTM_iterate`);
  - **citations and names**: the probes cite `Encoding`'s `length_bits_le_self` and `unaryFin`,
    which #92 does not touch; #92 adds host H3's step clock (`Turing.exists_stepClockTMVia`,
    `Turing.clockCfg`); the name screen against #92's tree finds no clash.
  *Recommended order: #92 first, then the harvest on the merged base with `SelfUniversal` in its
  replay.*
* **PR #93** (`lean/arm-minor-fixes` `3fe6a2de`, open; comments and imports of 33 ARM files): no
  overlap with the harvest's files, its closure or its replay set. Independent.
* **C1's landed hosts (PR #87)**: `ChoiceReplay` (`replayTM`, `withChoiceTape`, `replayTM_runFrom`)
  and `runWith_initCfg_take` are used by the replay probe only.

## Homes and module names (proposed; the auditor rules on them)

| Part | Lands as | Namespace | Size (MEASURED) |
|---|---|---|---|
| A | new `TCSlib/Complexity/TuringMachine/Build/StepBlockLoop.lean`, imports `Build.StepBlock`, `Build.CounterLoop`, `Build.VirtualInput` | `Turing.StepBlock` | 504 lines |
| — | `TuringMachine/CodeSimulator.lean` gains its import and loses 8 private declarations | `Turing.MachineFormat` (unchanged) | 3,290 → 3,010 lines |
| — | the `TuringMachine` facade gains its import and a `## Contents` line | | |

**Why a new Build module** (design §5): it composes exactly three public hosts and imports exactly
them; its forward closure excludes `CodeSimulator`; with the landing edges the graph is acyclic; a
consumer of the loop does not import the canonizer or `CodeSimulator`'s two admitted headlines;
appending to `Build/StepBlock` instead would add `CounterLoop` (and, since MIG-0b,
`Build/Contract/Basic`) and `VirtualInput` to the closure of every unclocked consumer of the bare
block. `R`'s module imports `CodeSimulator` and so sees either home; the decision is made by
layering and the other consumers (B5a H1, U-1, EXPCOM). **Replay set at landing** (MEASURED from
header imports, the root `TCSlib.lean` not listed): the new module, `CodeSimulator`, `Codes2Tape`,
`NDCodeSimulator`, `Diagonalization/EXPCOM`, `Diagonalization/Relativization`, the `TuringMachine`
and `Diagonalization` facades: **8 modules**, plus `SelfUniversal` on PR #92's tree.

**Registry** (`machine-library-design.md` §14): the registry's H1 is the AND/OR evaluator; the
private `h1…` names come from brief B5a-H1. The harvested clock is registered as **H2-L, H2's
loop form**, a sub-row of H2 (proposed row: design §10), and renamed accordingly.

## What the files state (verify)

Write `B = 50·(|tableBitsK M.tr| + 1)` and `run₀ = counterLoopCfg (some (.dec .run)) d ct cp`
(the loop's start: control at its first decrement, body part `d`, counter tape `ct` with head
`cp`). All in namespace `Turing.StepBlock`; unit lines.

* **`loopTM k`** (def, `:133`): `counterLoopTM (roundTM k) (exit k true) (some (exit k false))` at
  type `MultiTapeTM (k + 2 + 1) Bool (CounterLoopState (Σ key, Ph k key))`.
* **`hostedLoopTM k`** (def, `:141`): `vhostEmitTM (loopTM k)` at type
  `MultiTapeTM (1 + (k + 2 + 1)) Bool (CounterLoopState (Σ key, Ph k key) × Bool)`.
* **`loopTM_run`** (proved, `:330`): for `M : MultiTapeTM k Bool (Fin (n + 1))`, a configuration
  `c` on `x` with `c.state ≠ none`, `d` with `d.state = some (exit k true)` and `Rep M.tr c d`, a
  word `w` with `ct (cp + p) = bufferTape w p` for `-1 ≤ p ≤ |w|`, and `t` with
  `Nat.ofDigits 2 (w.map Bool.toNat) = t`: there are `T`, `e`, `ct'` with (i) `T ≤ t·B + 4t + 2|w| +
  2`; (ii) `T ≤ t'·B + 4t' + 2|w|` for every `t' ≤ t` with `(M.runFrom c t').state = none`;
  (iii) `Rep M.tr (M.runFrom c t) e`; (iv) `e.output = d.output`; (v) `ct' q = ct q` for every `q`
  outside `[cp, cp + |w|)`; (vi) `(loopTM k).runFrom run₀ T = counterLoopCfg (some (if (M.runFrom
  c t).state.isSome then .done else .escape)) e ct' cp`; (vii) for every `u < T` the state at `u` is
  neither `some .done` nor `some .escape`.
* **`hostedLoopTM_run`** (proved, `:458`): the same hypotheses, plus a native input `z`, a frozen
  native head `p : Fin (z.length + 2)`, a tag `b` with `FinTM.VirtualTag c.inputPos b`, and a prior
  output `pre`: there are `T`, `e`, `ct'`, `b'` with (i)–(v) as above, `FinTM.VirtualTag e.inputPos
  b'`, `(hostedLoopTM k).runFrom (vhostCfg run₀ b p pre) T = vhostCfg (counterLoopCfg (some (if …
  then .done else .escape)) e ct' cp) b' p pre`, and for every `u < T` and every tag `tag` the state
  at `u` is neither `some (.done, tag)` nor `some (.escape, tag)`.
* **`hostedLoop_read`** (proved, `:522`): for any table `tr`, `Rep tr c' e`, control `q`, counter
  `ct` at `cp`, tag `b`, native head `p` and prefix `pre`, the configuration `vhostCfg
  (counterLoopCfg (some q) e ct cp) b p pre` has state `some (q, b)`, input position `p`, output
  `pre ++ e.output`, and `workTapeSymbols (vhostBank (summaryTape k).castSucc) = outputSummary
  c'.output`.
* **Private** (moved; `:150-290`): `loopRoundTime d` (the least positive `t` with the block at
  `exit k b` for some `b`, else `0`; body of `h1RoundTime`, unchanged); `loopOrbit_succ` (the
  orbit's successor equation, `roundOrbit_succ` through the abbreviation); `loopRoundTime_spec`
  (statement of `h1RoundTime_spec`, unchanged); `loopOrbit_rep`, `loopOrbit_round`
  (`h1Clock_orbit`, `h1Clock_round` from a live `c` instead of `M.initCfg x`; at `c := M.initCfg x`
  they are the private statements, checked by `decls.py movemap`).

**The companion edit** (`PostHarvest-CodeSimulator.diff`; freeze in `…-freeze.log`): `CodeSimulator`
gains the import; **deletes** `h1ClockTM`, `h1HostedClockTM`, `h1RoundTime`, `h1RoundTime_spec`,
`h1Clock_orbit` (with MIG-0b's `roundOrbit` token), `h1Clock_round`, `h1Clock_effect`,
`h1HostedClock_effect` (269 lines, with their docstrings); keeps `h1HostedVerdictTM` with
`hostedLoopTM` for `h1HostedClockTM` (code otherwise identical, checked), `h1HostedVerdict_effect`
with a new proof citing `hostedLoopTM_run` and `hostedLoop_read` (the declaration 61 → 46 lines;
statement unchanged), and `h1HostedVerdict_accepts` unchanged; changes status text only in comments
(the module's status bullet, `h1HostedVerdictTM`'s docstring, the headline's H1 continuation-2
appendix, a new "H1 harvest" paragraph). No other declaration's statement, code, docstring or
visibility changes; 105 → 97 declarations, 11 public before and after. **The planned private →
public promotions are exactly** `h1ClockTM` → `loopTM`, `h1HostedClockTM` → `hostedLoopTM` (bodies
identical after renaming; types now explicit), `h1Clock_effect` → `loopTM_run`,
`h1HostedClock_effect` → `hostedLoopTM_run` (generalized); `hostedLoop_read` is new.

## Changes from the private assembly (verify against `…-freeze.log` §2)

1. **(a) Any represented live start**: `M.initCfg x` becomes any `c` with `c.state ≠ none`. The
   only use of `initCfg` in the private proofs was the liveness of the orbit's base case and the
   positivity of the first halting time.
2. **(b) The early-escape bound (ii)**: new; the private statement weakened the escape branch's
   exact time `Σ_{j<u} τ_j + counterOverhead (bits t) u` (`CodeSimulator.lean:2969-2971`) to the
   full budget.
3. **(c) Live exits usable by the caller**: the machines and the hosted contract become public;
   the counter frame (v) is new; `hostedLoop_read` packages the reading step that was inline in
   `h1HostedVerdict_effect`'s proof.
4. **Free generalizations**: the counter `bufferTape (bits t)` at `0` becomes any delimited word of
   value `t` at any `cp` on any tape; the initial tag `true` any valid tag; the prefix `[]` any
   `pre`.
5. **Proof changes**: `loopRoundTime_spec`'s uniqueness step cites `roundTM_firstExit_unique`
   (`StepBlock.lean:3457`, H2-S's additive) instead of re-proving it (H2 design O7's disclosed
   duplication); the orbit's successor step cites `roundOrbit_succ` instead of `simp only
   [counterLoopOrbit, roundOrbit, …]`.

## Brief for the auditor

Restate every definition in your own words **before** reading its docstring and compare. The unit
has **no sorried theorem**: for each of the three theorems, argue in 2–5 sentences that the
statement says what its docstring and ruling 5 claim, that it is not vacuous, and that it suffices
for its consumers (or exhibit the gap). Attempt at least the adversarial instantiations of point 9
(failure modes 1–5 of `audits/TEMPLATE.md`). Points to rule on:

1. **Ruling 5, item by item.** (a) Is "any `c` with `c.state ≠ none` and `Rep M.tr c d`" the
   arbitrary represented live start with the stream installed? The replay probe instantiates it at
   `NDTM.withChoiceTape (N.initCfg (x.take t)) (bufferTape s) 0`. Is `live` necessary (it is the
   step block's own hypothesis), and is anything else about the start needed by `R`? (b) Is clause
   (ii) the early-escape bound `R`'s prefix clause needs, with the right quantifier (`∀ t' ≤ t`) and
   no hidden `+ 2`? (c) Are the exits "usable by the caller": live control, exact endpoint, cut for
   every tag, the frame, and the summary cell (`hostedLoop_read`)?
2. **`loopTM_run`.** The exit selection `if (M.runFrom c t).state.isSome then .done else .escape`,
   including a halt exactly at the deadline; the endpoint `Rep M.tr (M.runFrom c t) e` in the escape
   case (by absorption, the halted configuration); the counter frame (v), including the delimiter
   cells `cp - 1` and `cp + |w|`; the silence (iv); the cut at `u = 0`.
3. **`hostedLoopTM_run`.** The tag hypothesis `VirtualTag c.inputPos b` (Z1's), the arrival tag
   `b'`, the frozen native head, the prefix; the cut "for every tag".
4. **`hostedLoop_read`.** Is `vhostBank (summaryTape k).castSucc` the right host tape? Does
   `outputSummary c'.output = some true` mean exactly "output `[true]`" (`outputSummary_true`)?
5. **Consumer fit** (`ConsumerProbe-tail`, `ReplayProbe`): do the two probes derive the loop step
   that `R`'s sketch (`NDCodeSimulator.lean:112-127`) takes as given: one per-code constant, the
   verdict on the branch on `x` along `s.take t`, `T ≤ C·(t + 1)`, and `R`'s prefix clause
   `T ≤ C·(t' + |x| + |bits t| + 1)`? What remains for `R`'s fill (setup, window copy, seam frame,
   verdict states, ledger)?
6. **The landing form and the freeze.** Is the companion edit what the design says (no private
   copy kept; statements frozen; the only promotions those listed)? Is the rehearsal (one file) with
   the reference check an adequate substitute for cross-module privacy?
7. **MIG-0b and the open PRs.** Is it right that no statement depends on #90, and that no copied
   proof needs #90's kind of edit again? Is the sequencing with #92 and #93 complete (design §8)?
8. **Homes, names, registry.** The new module and its name; `Turing.StepBlock` as namespace; the
   names `loopTM`/`hostedLoopTM`/`loopTM_run`/`hostedLoopTM_run`/`hostedLoop_read`; the H2-L row.
9. **Adversarial instantiations** (at least these):
   - *(FM3, boundary)* `t = 0` with `w = []` and with the padded `w = [false, false]`: zero rounds,
     `done`, `T ≤ 2|w| + 2`, even when `c`'s first transition halts (overlay S1);
   - *(FM3)* a halt exactly at the deadline (`u = t`): `escape`, and (ii) at `t' = t` gives `T ≤
     t·B + 4t + 2|w|`, below the full budget; the escaping round index `u - 1 < t`;
   - *(FM3)* a start whose first transition halts, for every `t ≥ 1`: `escape` within `B + 4 + 2|w|`,
     independent of `t` (S2); and at `t = 1`, hosted, the live state `(escape, b')` (S4);
   - *(FM2, trivialization)* is `Rep` with `entry` satisfiable for every `c` (S0), so that no
     clause holds vacuously? Is the endpoint pinned (the run equation), so that `∃ e` is not free?
   - *(FM4, missing hypotheses)* drop `live`: `c` halted, `Rep` with an empty state word, the block
     run from `entry` unspecified; drop `hb`: Z1's clamped buffer move at a boundary with the wrong
     tag;
   - *(FM3)* `k = 0` work tapes, one state, empty simulated input, a counter `[true, false, true]`
     (S5, concrete: escape, verdict cell `some true`);
   - *(FM1, infidelity)* outputs `[]`, `[true]`, `[true, true]`, `[false]` and the summary cell
     (`none`, `some true`, `some false`, `some false`); a stream longer than `t`, with arbitrary bits
     after position `t` (the replay probe reads `s.take t` only);
   - *(FM5, debt)* the duplication ledger (design §11): nothing copied, eight declarations moved,
     three overlaps retired; the probes' local value lemma for `bits t` (evidence only; open
     question 6).
10. **Documentation and policy** (`policy.md`): the module header (`# Title`, `## Main definitions`,
    `## Main results`, `## References`), statement prose and `[AB09, …]` locations, a literal
    `**Proof sketch.**` on each nontrivial theorem (private helpers included), lines of at most 100
    characters, the status text of the companion edit.
11. Report anything else the files, this pack or the design note misstate.

## Repository-side attestations (verify or challenge)

Source facts (checkable in the bundle) are separated from the drafter's execution claims (the
logs). All MEASURED unless marked.

- **Base and snapshot** (`…-elaboration.log` §0): the seven cited sources exported from the tip
  equal its blobs; its `lake-manifest.json` and `lean-toolchain` equal `wt-h1harv`'s. Against
  `oleans-lm0b`, the tip's `CodeSimulator.lean` gives exactly its two headline sorries and the tip's
  `Build/StepBlock.lean` 0 errors and 0 warnings; controls: the tip's `CodeSimulator.lean` against
  the pre-MIG-0b `oleans-lc1` fails (1 error), and `2c3c975a`'s against `oleans-lm0b` fails exactly at
  the unedited `h1Clock_orbit` (1 error, line 2893, plus the unused-`simp`-argument warning at
  2892); the snapshot prints `counterLoopOrbit` as the reducible abbreviation of `roundOrbit`.
  Against `oleans-lc1`, exactly 23 oleans differ (the 16 modules #90 changed or added and 7
  downstream ones), none outside #90's reverse closure. **INFERRED**: that `oleans-lm0b` is a
  complete rebuild of the post-#90 tree (no build record names it); its `StepBlock.olean` predates
  #91's comment-only sketches.
- **The unit** (§1): in exactly its own three imports, exit 0, **0 errors, 0 warnings**. **Cut
  check** (`…-cutcheck.log`, the C1 gate's `cutcheck.py` verbatim): one part, its imports exactly
  the unit's three; the cut file and the landed module (equal up to blank lines) each elaborate
  with 0 errors and 0 warnings.
- **The overlay** (§2): its first 167,148 bytes are the tip's `CodeSimulator.lean` (`cmp`, SHA-256
  and a line `diff`, all equal), followed by a newline; each §C statement is its private
  declaration's text with the header replaced by `example`; **0 errors; exactly 2 warnings, both
  `declaration uses 'sorry'`, at lines 2746 and 3278: the tip's own headlines**
  (`exists_polyCanonizer`, `exists_uniformSimulator`); 0 other warnings.
- **Axioms** (`…-axioms.log`): ten prints, the five public and five private harvested
  declarations, each exactly `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.
- **Probes** (§3): `ConsumerProbe` 0 errors (the 2 inherited sorries); `ReplayProbe` 0 errors, 0
  warnings; the rehearsal `PostHarvest-CodeSimulator` **0 errors, the 2 headline sorries, 0 other
  warnings**. **Negative controls** (§4): `neg1` (a zero-round run claimed to escape), `neg2` (the
  early bound without `2|w|`), `neg3` (the verdict cell read at the table tape) each fail with
  exactly 1 error.
- **Freeze, move map, references** (`…-freeze.log`): as stated above; `decls.py` exits 0 on all
  three.
- **Names** (`…-names.log`): the ten full names clash with no declaration name (privates
  included) of the tip's `TCSlib/` tree or of PR #92's, nor with MIG-1's statement unit; no public
  short name is shared with another declaration. Positive control: seven planted clashes caught of
  seven. The parser is a text parser (comment-aware, namespace-resolving), not Lean's declaration
  inventory.
- **Style** (§5): `scripts/campaign_style_lint.py` over the two landing files: 0 FAIL, 1 WARN (the
  landed `CodeSimulator.lean`'s size, 3,010 lines; reported, not acted on). **Widths**: no line of
  the unit, the landed module, the tails or the probes exceeds 100 characters; the only one in the
  checked set is the tip's `CodeSimulator.lean:1134` (102 characters, in the canonizer, untouched)
  and its copy. **Admissions**: no `sorry` in the unit or the landed module, 2 in the landed
  `CodeSimulator` (the headlines), no `axiom` declaration anywhere. **Banned constructs** (`#eval`,
  `run_cmd`, `IO`, `unsafe`, `implemented_by`, `extern`, `native_decide`, `syntax`/`macro`/`elab`
  commands): none in any file.
- **Cited names** (§6): the backticked tokens of the unit's comments, `#check`ed in the overlay's
  context and in the replay probe's; those resolved in neither are bound variables and prose (`B`,
  `M`, `R`, `T`, `CodeSimulator`, `TCSlib.Complexity.TuringMachine`) and
  `Turing.exists_ndInterpreterCore` (checked separately, importing `NDCodeSimulator`: 0 errors).
  The screen is filtered by `cited.py`'s pattern (C1 finding M9).
- **Closure** (§7): from header imports; acyclic with the landing edges on the tip's tree and on
  PR #92's; the new module's forward closure without `CodeSimulator`; the replay sets as above.
- **Overlap with #92 and #93** (§8): the file lists, the harvest-edited files each PR also changes,
  and the modules of the new module's closure each PR changes, computed from `git diff`.
- **Nothing in a checkout changed** (§9): `wt-h1harv`'s cited files still equal their commit's
  blobs; git only read; no lake or elan; `lean` only through `tools/leanelab.sh`; Python only as
  `python3 -I`; every output under the gate's directory.
- **ESTIMATE / INFERRED**: the snapshot's completeness (above); that the replay passes beyond the
  rehearsal (`Codes2Tape`, `NDCodeSimulator`, `EXPCOM` and `Relativization` name no deleted
  declaration, which `decls.py refs` checks, none opens `Turing.StepBlock` or names `StepBlock`
  (grep), and the unit declares no instance, `simp` attribute or notation; but they were not
  re-elaborated against the new module, which would need oleans this gate may not write).

## Open questions for the user (recommendations in italics)

1. **Home.** *New `Build/StepBlockLoop.lean`, namespace `Turing.StepBlock` (layering; design §5).*
2. **Registry.** *A sub-row H2-L, "H2's loop form", directly after H2 (design §10).*
3. **Names.** *`loopTM`, `hostedLoopTM`, `loopTM_run`, `hostedLoopTM_run`, `hostedLoop_read`;
   no "clock" names, which `Complexity.TimeHierarchy.clockTM` and host H3's step clock (#92) use.*
4. **Order with PR #92.** *#92 first, then the harvest on the merged base, re-elaborated there,
   with `SelfUniversal` in its replay (design §8). #93 is independent.*
5. **Gate and fill.** *The statements are proved: no fill brief; one maintainer PR (module,
   companion edit, facade, records) with its replay once this gate closes; then `R`'s brief cites
   the public names.*
6. **The value of `bits t`.** *Add a public `Turing.counterValue_bits` beside MIG-0b's
   `counterValue` (`CounterLoop.lean:1939`) with the harvest's landing, so that `R`'s fill needs no
   private copy of `CodeSimulator`'s `canonBits_value` route (design §11, Q6).*
7. **`R`'s sketch text** (`NDCodeSimulator.lean:117-120`, "private in `CodeSimulator` since
   fills-8; harvested with H2's promotion"). *Re-point it to the public names in the harvest PR (the
   file is in the replay set anyway).*

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/h1-harvest-statements-findings.md`. The gate closes when a round reports zero blockers and
zero majors; the part then lands as cut, with the companion edit. This pack is immutable once sent.
