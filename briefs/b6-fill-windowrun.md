# Ch3–4 fill campaign — B6 fill, batch F2: the windowed runner (`Turing.exists_windowLoopTM`, `Turing.exists_windowRunnerTM`, `Build/WindowRun.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor 70b503b49760b65817a3bce4b876dc466c32235c HEAD`
  succeeds. That commit contains:
  - the B6 hosts (PR #92: the five host modules with their ten sorried contracts, among them
    your two targets and the step clock you cite), the ARM minor fixes (#93) and the H1 harvest
    (PR #94: `Build/StepBlockLoop`, and `counterValue_bits` with the public
    `foldr_bit_eq_ofDigits` in `Build/CounterLoop`), all merged;
  - the B6 fill plan (`audits/evidence/b6-fill/B6-fill-plan.md`);
  - this round's order list (`briefs/orders/b6-fill-windowrun.txt`), base sorry set, screen
    population and base, pre-ship log, and the pre-ship probes with their generators
    (`audits/evidence/b6-fill-windowrun/`).

  If the check fails, **stop**.
- **Branch at exactly that commit, not at the campaign tip:**

  ```sh
  git checkout -b fill/b6-windowrun 70b503b49760b65817a3bce4b876dc466c32235c
  git rev-parse HEAD        # must print 70b503b49760b65817a3bce4b876dc466c32235c
  ```

  Record that hash as your base in `REPORT.md`. Never rebase, merge or cherry-pick later campaign
  commits. More landings are queued in your import closure (next section). Pinning keeps your
  base, your base sorry set and your screen base exactly the ones this brief states. The
  maintainer re-checks your delivery at integration on the tip of that day. Ground rule 10 says
  what the pinned base means for your citations.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-b6-windowrun.zip`, containing
  `REPORT.md`, the full modified source, a `git format-patch` series against `70b503b49760b65817a3bce4b876dc466c32235c`, a git
  bundle whose only prerequisite is `70b503b49760b65817a3bce4b876dc466c32235c`, the bootstrap and final sweep logs, the axiom
  log, the sanity evidence file `B6F2Sanity.lean.txt` and its log, both screen outputs, and
  `SHA256SUMS`.

## Base, line numbers and what lands around you

- **Lines in this brief are those of campaign commit `c52663f1`** (the records commit after #94's
  merge). The inputs commit `70b503b49760b65817a3bce4b876dc466c32235c` adds no Lean change to it. `Build/WindowRun.lean` and
  `Build/StepClock.lean` have not changed since #92 (byte-identical at `1b6b972c` and at
  `c52663f1`, checked). Every probe and measurement below was run at `c52663f1`, against the
  olean snapshot of #94's replay.
- **#94 (the H1 harvest) is in your base.** It changed `Build/CounterLoop.lean`, which is in your
  import closure (through `Build/StepClock` and `Build/InputCall`): a new import of
  `TuringMachine/CodeParser` and two new public lemmas. Your closure has 27 modules, your file
  included. Your targets need neither new lemma.
- **Record-table row 18 is proved on PR #95** (branch `lean/rt5-row18`, open, not in your base):
  `Turing.exists_recordInitTM`, statement unchanged, in `Build/RecordTable.lean`, which is in your
  import closure. Your targets do not use it (its consumer is `Complexity.space_hierarchy`). At
  your base it is still sorried: your order list and base sorry set are those of the tip, and
  **#95 removes one sorry from the set when it lands** (`Build/RecordTable` 5 → 4).
- **MIG-1 stage S (built, not yet a PR) is not in your base.** It edits modules in your import
  closure: `Simulation`, `Composition`, `Build/Wrappers`, `Encoding`, `Build/Loop` and
  `Build/Catalog` (with `ClassP/TimeConstructible` and `Build/Primitives`, outside it). It makes
  private witnesses public under new names (`audits/evidence/mig1/gate/scripts/renames.json`:
  for example `loopHost` → `loopHostTM`, `emCallTM` → `callTM`, `catalogPrefixTM` → `prependTM`,
  `counterTM` → `FinTM.lengthBitsTM`) and moves `Turing.FinTM.rewind_heads` and
  `rewind_scan_heads` from `Build/Catalog` to `Simulation` (same names). It is invisible to your
  base; the maintainer rebases at integration. **Cite no private name of those files**, and keep
  your new privates under the `wl_` and `wr_` prefixes, so no name of yours meets one of S's.
  None of the publics this brief cites changes its name or statement at S.
- **Later, also outside your base:** the C1-A assembly gate (round 2) adds the public
  `Turing.embedSilentCfg_cap` to `Build/Embed.lean` (in your closure). Your route uses only the
  forwarding embedding.

## Parallel batches this round (disjoint files; never edit another batch's)

| Batch | Brief | Owns |
|---|---|---|
| B6-F1, the step clock | `briefs/b6-fill-stepclock.md` | `TuringMachine/Build/StepClock.lean` (upstream of yours) |
| B6-F2, the windowed runner | `briefs/b6-fill-windowrun.md` (this brief) | `TuringMachine/Build/WindowRun.lean`: the regions of ground rule 1 |

B6-F1 fills `Turing.exists_stepClockTMVia`, which your runner cites **by its frozen statement**;
nothing of B6-F1's work is visible to you. Other work in flight owns other files (MIG-1 stage S,
above). A parallel batch's work is invisible to your base and your screen.

## What this is

**Host H3, the windowed runner** (registry row H3, design §14; B6's window route, §16b item 3;
the B6 hosts gate, round 1, PASS, `audits/b6-hosts-statements-findings.md`, notes N4 and the
rulings on brief points 2 and 3). It is the second batch of the B6 fill plan
(`audits/evidence/b6-fill/B6-fill-plan.md`), on the chain to `Complexity.space_hierarchy`: the
configuration-count runner `Turing.exists_configWindowRunnerTM` (`SpaceComplexity/WindowClock.lean`,
batch B6-F3) runs your runner on a clock word it writes itself (Route A, the gate's ruling once
the shared clock is filled). Two targets:

1. **`Turing.exists_windowLoopTM`** (line 371): the unclocked round loop, a phase host over the
   two proved record rows; every `N` rounds of the semantic run `Turing.windowRun` are realized
   at a time `≤ C · N · (L + |x| + 1)`, with an all-times head envelope and silence.
2. **`Turing.exists_windowRunnerTM`** (line 428): the loop under the step clock
   `Turing.exists_stepClockTMVia`, with the clock word supplied by the consumer and one dispatch
   from every `timeout` to the exit `exhausted`.

**Proved-modulo set:** target 1 is proved modulo nothing (the record rows are proved). Target 2
is proved modulo **exactly `Turing.exists_stepClockTMVia`** (batch B6-F1, the campaign's
proved-modulo rule) and your own target 1. A complete delivery has `sorryAx` in target 2 only
through `exists_stepClockTMVia`, and none in target 1.

**Read first:** both targets' docstrings, whose proof sketches are binding (the loop's sketch
carries the gate's finding-3 repair: one stationary anchor step per round); the module docstring
and the specification section (lines 71–337: `Turing.windowRun` and its six proved lemmas);
`Turing.exists_recordTestTM` (`Build/CfgRecord.lean:4972`) and `Turing.exists_recordStepTM`
(`:4309`), their statements only; `Turing.exists_stepClockTMVia` (`Build/StepClock.lean:115`),
its statement only; `Turing.phaseHostTM` and `Turing.phaseHostTM_run` (`Build/Seam.lean:832`,
`:849`); the gate's findings, note N4 and finding 3; the design note
`audits/evidence/b6hosts/B6-hosts-design.md` §2.2; the pre-ship overlay below.

**Pre-ship check (maintainer, at `c52663f1`, against #94's replay snapshot;
`audits/logs/b6-fill-windowrun-preship.log`):**
- `audits/evidence/b6-fill-windowrun/B6F2ImportProbe.lean.txt`: every public declaration this
  brief cites, and every one its pitfalls and prohibitions name, resolves in your file's import
  context. 0 errors, 0 warnings. **Re-run it after your delivery.**
- `audits/evidence/b6-fill-windowrun/WindowRunOverlay.lean.txt`, generated by
  `tools/mkoverlay.py` from `tools/homeA.lean.txt`, `tools/loopbody.lean.txt`,
  `tools/homeB.lean.txt` and `tools/runnerbody.lean.txt`, every edit asserted and the reverse edit
  checked byte for byte. It is `WindowRun.lean` with the two home blocks inserted at their homes
  and both targets' bodies replaced by skeletons. Elaborated: **0 errors, 0 non-sorry warnings,
  2 sorry warnings**, exactly the two skeletons' remaining obligations. It shows the following:
  - the loop's phase index `wl_Phase`, its controls `wl_Ctrl` with their `Fintype` and
    `DecidableEq` instances, the phase machines `wl_rows`, the redirect table `wl_red` and the
    loop `wl_loopTM` elaborate, and the loop skeleton obtains both record rows, builds
    `wl_loopTM` and proves the two distinctness clauses;
  - the runner's controls `wr_Ctrl`, its machine `wr_runnerTM` (the clock with the timeout
    dispatch) and its exits `wr_exit` elaborate; the prescribed layout lemma `wr_clockCfg_eta` is
    **proved**; the runner skeleton obtains the loop and the clock at
    `e := RecSym.digitEmb`, builds `wr_runnerTM`, and proves the two distinctness clauses;
  - what remains is each target's contract (route steps 1–4 and 5–9).
- `tools/mkchecks.py` appends `tools/checks.lean.txt`: a fit check of the loop's entry and
  redirects, and the axiom prints. 0 errors; `sorryAx` appears exactly in the two targets.

## Owned regions and targets (modify these and nothing else)

| # | File:line | Target | Route | Uses |
|---|---|---|---|---|
| 1 | `TuringMachine/Build/WindowRun.lean:371` | `Turing.exists_windowLoopTM` | one phase host over the two record rows; the skeleton | `exists_recordTestTM`, `exists_recordStepTM`, `phaseHostTM_run`, R1, the specification lemmas |
| 2 | `TuringMachine/Build/WindowRun.lean:428` | `Turing.exists_windowRunnerTM` | the step clock over target 1, with the timeout dispatch; the skeleton | target 1, `exists_stepClockTMVia` (B6-F1, modulo), `phaseHostTM_run`, the specification lemmas |

- **(a) Home A:** the blank line **340**, between `/-! ### The machines -/` (line 339) and target
  1's docstring (line 341). Insert `tools/homeA.lean.txt` there first; your own privates for the
  loop go in the same home, each after what it uses and before its first consumer.
- **(b) Target 1's docstring,** lines 341–370: unchanged; append a flagged
  **"Fill appendix (B6-F2)"** paragraph before the closing ` -/` on line 370.
- **(c) Target 1's body,** the `sorry` on line 397 (the statement, lines 371–396, is frozen).
  Start from the skeleton (`tools/loopbody.lean.txt`).
- **(d) Home B:** the blank line **398**, between target 1's body and target 2's docstring
  (line 399). Insert `tools/homeB.lean.txt` there; your own privates for the runner go there.
- **(e) Target 2's docstring,** lines 399–427: unchanged; append a flagged Fill appendix before
  the closing ` -/` on line 427.
- **(f) Target 2's body,** the `sorry` on line 468 (the statement, lines 428–467, is frozen).
  Start from the skeleton (`tools/runnerbody.lean.txt`).
- **(g) Status text:** the module's "Status" paragraph (lines 24–26) and the "Main results"
  entry for the two contracts (lines 57–58, "(sorried)"), to "proved" (target 2: "proved modulo
  the step clock" until B6-F1 integrates), flagged.
- Add no `section`, `open` or `variable` that leaks past a home, and never put a declaration
  between a docstring and its declaration.
- **Frozen in your file:** the header and module docstring apart from (g) (lines 1–68); the
  whole specification section, lines 71–337 (`Turing.WindowExit`, `Turing.windowRun`,
  `windowRun_halted_of_run`, `windowRun_spec`, `windowRun_tag`, `windowRun_stop_unique`,
  `windowRun_exhausted_of_live`, `windowRun_halts_on_last_transition`): statements, proofs and
  docstrings byte-identical; both targets' statements; `end Turing`.
- **Not yours:** every other file, including `Build/StepClock.lean` (B6-F1's), `Build/CfgRecord.lean`,
  `Build/RecordTable.lean`, `Build/Seam.lean`, `Build/Embed.lean`, `Build/CounterLoop.lean`,
  `Build/Contract/*`, the downstream `SpaceComplexity/WindowClock.lean` and
  `SpaceComplexity/Hierarchy.lean`, and the facades.

### Prescribed home declarations (binding where marked; elaborated in the overlay)

Take the blocks from `tools/homeA.lean.txt` and `tools/homeB.lean.txt`. Replace their
"(Suggested.)" and "(Prescribed, proved.)" tags by ordinary docstring prose.

| Declaration | Home | Status in the overlay | Role |
|---|---|---|---|
| `wl_Phase` (`deriving DecidableEq, Fintype`) | A | suggested | the loop's phases: `anchor`, `test`, `step`, `stop` |
| `wl_Ctrl`, `wl_Ctrl_fintype`, `wl_Ctrl_decidableEq` | A | suggested | the phase controls: `Unit`, the test row's, the step row's, `WindowExit`. `WindowExit` has no public `Fintype`; its three values are listed locally, not as a new instance |
| `wl_recordTape` | A | suggested | tape `0` as a one-tape bank, for the test row's R1 embedding |
| `wl_rows` | A | suggested | the phase machines: a stationary anchor, the test row on tape `0` by R1, the step row on the whole bank, stationary stops |
| `wl_red` | A | suggested | the redirect table: anchor → test; test `yes` → `stop halted`, `no` → step; step `yes` → anchor, `no` → `stop left` |
| `wl_loopTM` | A | suggested | **the loop**: `phaseHostTM (wl_rows Rt Rs) ⟨.anchor, ()⟩ (wl_red …)` |
| `wr_Ctrl`, `wr_Ctrl_fintype`, `wr_Ctrl_decidableEq` | B | suggested | the runner's phases: the clock's control, the exhausted exit |
| `wr_runnerTM` | B | suggested | **the runner**: a phase host whose clock phase is `H` and whose every `timeout r` dispatches in one stationary step to the exhausted exit |
| `wr_exit` | B | suggested | the runner's exits: `halted`/`left` are the clock's `finish` at the loop's two stops, `exhausted` the dispatch target |
| `wr_clockCfg_eta` | B | **prescribed, proved** | a runner configuration at a clock state is the clock layout (`Turing.clockCfg`) of its loop part and last tape, tagged into the clock phase: how the runner's start meets the clock's precondition |

The two skeletons (take them, then prove their remaining obligations):
- **Loop:** `exists_recordTestTM` at `P := fun q _ => q.isNone` (the halted-state test, which the
  docstring's sketch names) and `exists_recordStepTM M.tm upd hupd`; the witness `wl_loopTM Rt Rs
  te ty tn se sy sn`, entry `⟨.anchor, ()⟩`, stops `fun e => ⟨.stop, e⟩`, constant
  `Ct + Cs + 3` (a suggestion; any constant depending only on the rows works); the distinctness
  clauses proved.
- **Runner:** target 1, then `exists_stepClockTMVia (RecSym.digitEmb M.State T) L (fun p =>
  decide (p = stop .halted ∨ p = stop .left))`; the witness `wr_runnerTM H timeout`, entry
  `⟨true, inj entry⟩`, exits `wr_exit finish stop`, constant `CL + 1`; the distinctness clauses
  proved (from the clock's `finish`/`inj` distinctness, `finish`'s and the loop's `stop`'s
  injectivity).

You may replace a suggested machine by your own, if you keep a phase host over the public rows
and the clock; say why in `REPORT.md`. If a prescribed statement turns out false or unusable,
that is an escalation (ground rule 4): record the obstruction and continue.

### Hosts (binding; the host-first rule, `policy.md` §1, `workflow.md` §2)

- **The loop is one phase host over two public rows** (the docstring's sketch): `Turing.phaseHostTM`
  with `Turing.phaseHostTM_run` for every phase; the halted-state test
  `Turing.exists_recordTestTM` (one tape, embedded on tape `0` by R1: `Turing.embedEmitTM`,
  `Turing.embedEmitTM_runFrom`, with the public reconstruction `Turing.Cfg.select`,
  `Turing.embedEmitCfg_select`, `Turing.embedEmitCfg_eq`); and the record step
  `Turing.exists_recordStepTM` on the whole bank (`K + 1` is the step row's own tape count). Cite
  the rows' contracts; never re-walk a row, never write a record test or a record step of your
  own, and write no hand controller.
- **The runner is the step clock over the loop** (`Turing.exists_stepClockTMVia`, by its frozen
  statement) plus one phase host for the timeout dispatch. Do not build a second clock, and do
  not use `Turing.counterLoopTMVia`: the round-counter route is B6-F3's Route B, not this
  contract's.
- **The specification lemmas are yours to cite** (proved, frozen): `Turing.windowRun_spec` (the
  characterization of the exits), `Turing.windowRun_stop_unique` (a stop does not depend on the
  budget), `Turing.windowRun_exhausted_of_live` and `Turing.windowRun_halted_of_run`. Prove every
  property of `windowRun` you need from them, not by a new induction on `windowRun`'s
  definition, except the loop's own every-`N` induction, which follows `windowRun`'s three
  branches.
- **Composition:** run concatenation by `Turing.MultiTapeTM.runFrom_add`, or MIG-0b's segment
  layer (`Turing.Segment`, `Segment.trans`). No private run-bookkeeping structure: `CfgRecord`'s
  private `RecordRun` is the pattern not to repeat.
- **Silence and space:** the output is append-only (`Turing.MultiTapeTM.output_prefix`), so a
  phase whose endpoint keeps the output was silent throughout (the gate's ruling on brief point
  2); space from the envelope by `Turing.MultiTapeTM.spaceUsedByTape_le_card_Icc`.

### The route (binding where it names a row)

**Target 1, the loop.**

1. **The round** (a private lemma; the gate's suggested "round-positivity fact" is part of it).
   From a configuration at the anchor with `RecordAt d 0 (cfgRecord s c τ)`, `c.InWindow s` and
   every other tape blank:
   - one dispatch step to the test's entry (`phaseHostTM_run` at the anchor phase, `T = 0`);
   - the test phase: present the configuration as the R1 embedding of its tape-0 selection
     (`embedEmitCfg_select`), apply the test row's contract to the selection (its `RecordAt` is
     `d`'s on tape `0`; its input is arbitrary), transport by `embedEmitTM_runFrom`, and dispatch
     by `phaseHostTM_run` at the verdict;
   - if `c.state = none`: `yes`, then `stop halted`. Otherwise `no`, then the step phase from
     the unchanged configuration: if `(M.tm.step c).InWindow s`, `yes` with the record of
     `(M.tm.step c, upd τ (M.tm.outputSymbol c))` and back to the anchor; otherwise `no`, then
     `stop left`, with the record unchanged.
   - Time: `1 + t₁ + 1` or `1 + t₁ + 1 + t₂ + 1`, with `t₁ ≤ Ct · (L + 1)` and
     `t₂ ≤ Cs · (L + |x| + 1)`, where `L = (joinFields (cfgRecord s c τ)).length =
     recordLength M.k |x| s` (`Turing.joinFields_cfgRecord_length`). At least `3` steps: the
     positivity the every-`N` clause's `N ≤ t` needs.
   - The heads stay within the rows' radii of their entry positions, and every head is back at
     entry at the round's end; the output is unchanged throughout (silence above).
2. **Every `N`.** Induct on `N` along `windowRun`'s three branches: halted (the round stops at
   `stop halted`), left (`stop left`, record unchanged, as `windowRun`'s `left` keeps the
   configuration and tag), or a step (the next round from the new record). After a stop the
   statement's `t` is the stop time, which does not grow with `N`; after `N` steps the loop is at
   the anchor at a time `≥ N`.
3. **The all-times clauses.** Every time `u` lies in some round (or after a stop, where the
   loop is stationary): the envelope `C · (L + 1)` and silence hold at every `u`.
4. **Package** in the skeleton.

**Target 2, the runner.**

5. **The start in the clock's layout.** `wr_clockCfg_eta` presents the runner's start `d` (at
   `⟨true, inj entry⟩`) as the clock layout of its loop part `d'` (at the loop's `entry`, with
   `d`'s first `K + 1` tapes) and its last tape, tagged by `Sigma.mk true`. `d'` meets the loop's
   precondition (`RecordAt d' 0`, the other loop tapes blank by the runner's blank hypothesis);
   the last tape carries the delimited word `w`, the clock's counter precondition.
6. **The clock phase.** `phaseHostTM_run` at phase `true`: until the clock's first exit no state
   is a `timeout` state (the clock's cut), so the host is `H`'s run tagged by `Sigma.mk true`.
   The loop never halts before its first stop (if it halted at `h`, its state at a later
   every-`N` time would be `none`), so the clock's "stopped" is "at `stop halted` or `stop
   left`".
7. **Finish or timeout.** If the loop first stops at `τ ≤ d := value w`: the clock's finish clause
   gives `finish (some (stop e))`, the exit `e`, within `5τ + 2|w| + 2`. Otherwise the clock's
   timeout clause, then one dispatch to `exhausted`: within `5d + 2|w| + 3`. No exit earlier, from
   the clock's cut.
8. **Certified and determined.**
   - If `N` rounds stop and `C · N · (L + |x| + 1) ≤ d`, then the loop's stop time for `N` is
     at most `CL · N · (…) ≤ d`, so the clock finishes there: `out` is the semantic exit.
   - If `out ≠ exhausted`, the clock finished at the loop's first stop `τ`. Take `N := τ + 1`: if
     `windowRun N` were exhausted, the loop's every-`N` time would be `≥ N > τ` with no stop
     before it, contradicting the stop at `τ`; so it stops, its stop time is `τ` (both are first
     stops), and the loop's endpoint there is the record of `windowRun N`. The runner's endpoint
     is the clock's: that record on tape `0`, `wordPatch` of a same-width word on the last tape,
     every other cell, every head and the input position restored (the gate's "the loop's
     cofinal exhausted endpoints exclude spurious stop states").
9. **Envelope, silence, space.** By the clock's frame clause the body heads are the loop's at some
   loop time (within `CL · (L + 1)`), the input head and the output are the loop's (silent), and
   the counter head is in `[cp - 1, cp + |w|]`; the dispatch moves nothing. So `C := CL + 1`
   covers `C · (L + |w| + 1)`, and the space bound follows tape by tape
   (`spaceUsedByTape_le_card_Icc`).

- **Degenerate cases:** `M.k = 0` (a record with no window fields), `s = 0`, `w = []` (`d = 0`:
  the runner times out unless the loop stops at time `0`, which it cannot, since every round takes
  a positive time; then `out = exhausted`), `N = 0` (the loop at its start, `t = 0`), and a
  halted `c` (the first round stops at `stop halted`).
- **Input convention:** the native input stays where it is; the record rows restore it, the
  clock never moves it.

### Phases (for a partial; ground rule 9)

Stop, if you must, at the end of a phase, and say which.
1. **The two home blocks and the skeletons landed** (each target's remaining obligation stays a
   `sorry` in its skeleton, each with a literal "Proof sketch").
2. **The round lemma** (route step 1), as a private lemma.
3. **Target 1 complete** (steps 2–4).
4. **Target 2 complete** (steps 5–9), proved modulo `exists_stepClockTMVia`.
5. **The sanity file.**

## Gate guidance (binding)

- **Finding 3 (round positivity):** the record rows bound their exit times only from above; the
  loop's anchor dispatch makes every round take at least one step. Do not claim a positive lower
  bound for a row.
- **The surplus round (check 4):** the loop realizes exactly `windowRun`; the strict surplus is
  the consumer's (B6-F3's `N ≤ configBound + 1`). Do not add a round.
- **Intercept every verdict:** each row's `yes`/`no` is redirected at once; never run a row past
  its verdict.
- **The every-`N` contract and the all-times envelope** are the gate's accepted form (ruling on
  brief point 2): exact round restoration prevents drift; append-only output plus equal endpoints
  gives silence.
- **`+ 3`** is the runner's one timeout dispatch; the clock keeps its `+ 2` (B6-F1).
- **Sanity cases at fill.** In an evidence file `B6F2Sanity.lean.txt` that imports
  `TCSlib.Complexity.TuringMachine.Build.WindowRun` (not in the module), prove as `example`s from
  the public targets: (a) the loop's `N = 0` clause gives `t = 0` and the start itself; (b) for a
  live `c` whose step stays in the window, the loop's `N = 1` time is at least `1`; (c) a run that
  halts on its final transition while emitting the deciding bit (the specification's
  `windowRun_halts_on_last_transition`) is reported `halted` by the loop at `N = t + 2`, with the
  tag of the output including that bit. No `#eval`, `native_decide` or `IO`. A partial says
  "pending".
- **Note 46:** file size is not a driver; report the file's size.

## Cited infrastructure (public and proved at `70b503b49760b65817a3bce4b876dc466c32235c`, unless marked; all in `B6F2ImportProbe.lean.txt`)

- **WindowRun (yours, frozen):** `WindowExit`, `windowRun`, `windowRun_halted_of_run`,
  `windowRun_spec`, `windowRun_tag`, `windowRun_stop_unique`, `windowRun_exhausted_of_live`,
  `windowRun_halts_on_last_transition`, `exists_windowLoopTM`, `exists_windowRunnerTM`.
- **StepClock (B6-F1's; sorried, cited by statement):** `exists_stepClockTMVia`, `clockCfg`,
  `wordPatch`, `Cfg.Stopped`.
- **CfgRecord:** `exists_recordTestTM`, `exists_recordStepTM`, `RecordAt`, `cfgRecord`,
  `cfgRecord_length`, `Cfg.InWindow`, `Cfg.inWindow_init`, `RecSym`, `RecSym.digitEmb`,
  `RecSym.digit`.
- **RecordTable and Catalog (layouts):** `recordLength`, `joinFields_cfgRecord_length`,
  `joinFields`, `joinFields_length`, `fieldsTape`.
- **Seam:** `phaseHostTM`, `phaseHostTM_run`.
- **R1 (Embed):** `embedEmitTM`, `embedEmitCfg`, `embedEmitTM_runFrom`, `embedEmitTM_frame`,
  `Cfg.select`, `embedEmitCfg_select`, `embedEmitCfg_eq`, `embedEmitCfg_unselected`,
  `embedEmitCfg_selected_tape`, `embedEmitCfg_selected_pos`.
- **State transport and segments:** `Cfg.mapState`, `Action.mapState`,
  `MultiTapeTM.runFrom_mapState_of_agreeOn`, `Segment`, `Segment.trans`, `Segment.take`,
  `Segment.drop`.
- **Runs, output and space:** `MultiTapeTM.runFrom`, `MultiTapeTM.runFrom_zero`,
  `MultiTapeTM.runFrom_add`, `MultiTapeTM.runFrom_succ_eq_step`, `MultiTapeTM.runFrom_of_halt`,
  `MultiTapeTM.step_of_halt`, `MultiTapeTM.step_output`, `MultiTapeTM.outputSymbol`,
  `MultiTapeTM.output_prefix`, `MultiTapeTM.workTapePos_runFrom_mem_Icc`,
  `MultiTapeTM.spaceUsedByTape_le_card_Icc`, `MultiTapeTM.spaceUsed`,
  `MultiTapeTM.spaceUsedByTape`, `MultiTapeTM.visitedByTapeHead`, `FinTM`, `FinTM.tm`,
  `FinTM.k`, `FinTM.State`, `FinTM.bufferTape`, `Cfg.ext`.
- **Do not cite** anything downstream (`SpaceComplexity/*`) or outside your import closure
  (`Build/Contract/{Seam,Embed,Catalog,Lift}`, `SpaceComplexity/ConfigCount` are not imported).
  Row 18 (`exists_recordInitTM`) is not yours to cite.

## Ground rules (binding)

1. **File ownership, by region.** Only the regions (a)–(g) of `Build/WindowRun.lean`. List every
   new declaration with its role. A lemma that belongs in a shared file is written privately,
   flagged in `REPORT.md` as a promotion candidate, and promoted by the maintainer (`workflow.md`
   §4, rule 1).
2. **Statement freeze** over both targets and every landed declaration: no renames,
   re-signatures, restatements or attribution edits. Docstrings stay; a flagged Fill appendix is
   expected wherever your proof refines a sketch.
3. **Status text:** only (g), flagged. **No new public declaration.** The named witnesses of B5's
   decision are your private `wl_loopTM` and `wr_runnerTM`; list them as promotion candidates.
4. **Escalation** on anything unprovable as stated, including a prescribed statement or a cited
   row that does not compose as the route says: stop on that item, record the obstruction, and
   continue with the rest.
5. **No touching other sorries.** `exists_stepClockTMVia` stays sorried in your base; cite its
   statement. Cite proved material; never re-prove it.
6. **Imports.** Unchanged (`Build/RecordTable`, `Build/StepClock`). No TCSlib import may be added.
   A Mathlib import is allowed only if a needed lemma requires it; flag it.
7. **One proof per shared argument.** Never write a second record test, record step, phase host,
   clock, R1 reconstruction or run-bookkeeping structure; never re-walk a row's trace.
8. **Size.** No cap; file size alone is not a driver. Report the file's final line count and its
   public and private declaration counts (base: 470 lines; 10 public, 0 private).
9. **Continuation budget.** If your budget runs out, deliver a partial zip whose `REPORT.md`
   states the phase reached, which `private` helpers remain `sorry` (each with a literal "Proof
   sketch"), and which proved declarations are proved modulo them. A partial is expected and
   fine; an unreported gap is not.
10. **The pinned base.** Cite only declarations that are public at `70b503b49760b65817a3bce4b876dc466c32235c`, and your file's
    own privates.
    - Do not rely on unfolding the body of any definition in `CfgRecord`, `RecordTable`, `Seam`,
      `Embed` or `StepClock`; use their public contracts (`phaseHostTM`'s two-line table is the
      exception your own redirect proofs need, as `phaseHostTM_run`'s proof shows).
    - Nothing that lands after your base is visible to you. In particular B6-F1's fill and its
      privates (`sc_*`) are not; the clock is its statement.
    - List every declaration you cite outside your file in `REPORT.md`. The import probe covers
      this brief's list; if you cite more, add them to a copy of the probe and run it.
11. **MIG-1 compatibility.** Cite none of the six R3 canonical rows (`copyTM_run`,
    `transferTM_run`, `clearTM_run`, `compareTM_run`, `incrementTM_run_succ`,
    `incrementTM_run_overflow`) and no private declaration of `Simulation`, `Composition`,
    `Build/Wrappers`, `Encoding`, `Build/Loop` or `Build/Catalog`.

## Duplication governance (binding)

Run the text-level screen **before and after** (`audits/TEMPLATE.md` failure mode 5; `policy.md`,
**Duplication**). The population is **21 files**
(`audits/evidence/b6-fill-windowrun/screen-population.txt`): your file; the files this brief
cites (`StepClock`, `CfgRecord`, `RecordTable`, `Catalog`, `Build/Seam`, `Build/Embed`,
`StateRenaming`, `Contract/Basic`, `CounterLoop`, `Simulation`, `Deterministic`,
`Configuration`, `Finite`); the known overlaps (`Contract/Seam`, `Contract/Embed`, `InputCall`);
and the consumers (`SpaceComplexity/WindowClock`, `Hierarchy`, `ConfigGraph`, `ConfigCount`).

**The screen labels files by basename**: `Build/Seam.lean` and `Build/Contract/Seam.lean`, and
`Build/Embed.lean` and `Build/Contract/Embed.lean`, would share labels. Run it, unchanged, on
byte-identical copies whose names encode the full path (`/` becomes `__`), before and after:

```sh
bash audits/evidence/b6-fill-windowrun/tools/flat-screen.sh . \
  audits/evidence/b6-fill-windowrun/screen-population.txt "$(mktemp -d)" > screen-before.txt
```

The base, at `c52663f1`, is `audits/logs/b6-fill-windowrun-screen-base.txt`:
**953 declarations, 488 pairs, 149,658 characters** (MEASURED; about 7 minutes). Your "before"
must reproduce it after its header line. The two base pairs touching your file are in-file, in
the frozen specification: `windowRun_spec` reproduces `windowRun_tag` (60%) and
`windowRun_exhausted_of_live` (58%), the shared induction along `windowRun`'s branches.

- **No new cross-file pair** with an owned-file declaration on one side, except the
  pre-disclosed ones below (measure each).
- **Pre-disclosed, measured on the pre-ship overlay** (the same population with the overlay as
  `WindowRun.lean`; `audits/logs/b6-fill-windowrun-screen-overlay.txt`): 11 more declarations,
  2 more pairs (964 / 490 / 149,803). Both are in-file instance boilerplate, the dependent-case
  `inferInstanceAs` dispatch: `wl_Ctrl_decidableEq` reproduces `wr_Ctrl_decidableEq` at 83%, and
  `wl_Ctrl_fintype` reproduces `wl_Ctrl_decidableEq` at 50%. There is no cross-file pair:
  nothing pairs with the record rows, `Build/Seam`'s phase host or the R1 family. If you take
  the blocks verbatim, report these two pairs as pre-disclosed; add nothing to them.
- **Known hazards:**
  - **the record rows' own proofs** (`exists_recordTestTM`'s and `exists_recordStepTM`'s
    bodies, and `CfgRecord`'s private `RecordRun` family): cite the contracts; a pair with them
    means a row was re-walked;
  - **the phase-host compositions elsewhere** (the record rows' and `RecordTable`'s phase-host
    proofs, `Build/Seam`'s `phaseHostTM_run`): follow the pattern, do not transcribe it;
  - the R1 reconstruction family (`embedEmitCfg_eq` and its corollaries; `RecordTable`'s private
    `rt_embed_matches`): cite the public lemma;
  - `Build/Contract/Seam`'s sequencing bookkeeping and `Contract/Basic`'s segments: cite them
    or concatenate runs directly; write no third form;
  - `ConfigGraph`'s remaining private S1b record helpers (`s1b_*`, dead, deleted by the payback
    PR) and the private helpers of `WindowClock`: never copy them;
  - `CounterLoop`'s counter loop (`counterLoopTMVia` and its contracts): not your host.
- List every new in-file pair with a one-line justification. At 90% or more it is a copy: factor
  it.
- Quote both outputs in `REPORT.md`, which carries **"new copies: none"** (or lists each pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/b6-fill-windowrun.txt` (**207 modules**: the upstream
  closure of your owned file and of every module downstream of it, at the issue tree,
  topologically ordered, without the root `TCSlib`; the same set as B6-F1's list). Your file is
  module 140; its import closure has 27 modules, your file included; 3 modules are downstream of
  it (`SpaceComplexity/WindowClock` and the two facades).

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/b6-fill-windowrun.txt )
  ```

  **Base sorry-warning set, 28** (`audits/logs/b6-fill-windowrun-base-sorries.txt`, one entry per
  declaration, 13 modules). Yours: `Build/WindowRun` 2 (both targets). Record the base list by
  name first, and report any difference. (When #95 lands, `Build/RecordTable` has 4; that is
  outside your base.)
- **Final checks:**
  1. `Build/WindowRun`: zero errors and no sorry warning (for a partial: exactly the open
     obligations'), and no other warning in anything you added.
  2. Every module of the order list after your file (67 modules), re-checked against your final
     source, and every other module: zero errors, and sorry warnings exactly the base's minus
     yours (**26** in all for a complete delivery).
  3. Re-run `audits/evidence/b6-fill-windowrun/B6F2ImportProbe.lean.txt`: 0 errors. Elaborate
     `B6F2Sanity.lean.txt`: 0 errors.
- **Axiom prints** (in a scratch copy of your module with `#print axioms` appended, as the
  overlay's checks variant does) for both targets and every new private: within
  `[propext, Classical.choice, Quot.sound]` and, for target 2 and what depends on the clock,
  `sorryAx` through `exists_stepClockTMVia` only: state the axiom walk (target 2's proof cites
  the clock, target 1 and proved material; nothing else of yours is sorried).
- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`,
  0 FAIL (base: 0 FAIL, 11 WARN over 33 files; the pre-ship overlay gives the same); no new line
  over 100 characters.

## Out-of-scope sorries you will see (leave every one untouched)

- `TuringMachine/Build/RecordTable`: exists_tableFindTM, exists_tableAppendTM, exists_recordInitTM, exists_recordValidTM, exists_recordNextTM
- `TuringMachine/CodeSimulator`: exists_polyCanonizer, exists_uniformSimulator
- `TuringMachine/Build/StepClock`: exists_stepClockTMVia
- `SpaceComplexity/WindowClock`: exists_configWindowRunnerTM
- `SpaceComplexity/Savitch`: spaceConstructible_poly, savitch
- `SpaceComplexity/Hierarchy`: space_universal, space_hierarchy, LOGSPACE_ssubset_PSPACE, SPACE_linear_ne_NP
- `TuringMachine/Build/NDHost`: ndWriterTM_run_block
- `TuringMachine/Build/Zone`: exists_zoneShiftInTM, exists_zoneShiftOutTM
- `TuringMachine/Build/InputWindow`: exists_inputWindowCopyTM
- `TuringMachine/Build/InputDevice`: exists_rulerTestTM, exists_rulerDeviceTM, exists_rulerHostTM
- `TuringMachine/SelfUniversal`: exists_selfStartupTM, exists_selfUniversal
- `TuringMachine/NDCodeSimulator`: exists_replayCanonizer, exists_ndInterpreterCore

If a proof seems to *need* one of these beyond a named citation, that is an escalation, not a
license.

## REPORT.md checklist

- [ ] 2/2, or the phase reached (rule 9); the base hash (`git rev-parse HEAD` at branch
      creation, equal to `70b503b49760b65817a3bce4b876dc466c32235c`) and the ancestor check.
- [ ] Every new declaration with its role; the prescribed blocks as taken (any deviation, with
      its reason); the machines as suggested or your own. Every flagged appendix and status
      update.
- [ ] Promotion candidates (`wl_loopTM`, `wr_runnerTM`, the round lemma) and escalations, or
      "none".
- [ ] Rule 10: the list of declarations cited outside your file, and the probe re-run. Rule 11:
      a grep of your diff for the six R3 rows and the S-renamed privates.
- [ ] Duplication: both flattened screens, every new pair justified, "new copies: none".
- [ ] File size; the final sweep tail; the axiom prints and the axiom walk; the lint line. The
      diff touches only your owned regions; the specification section is byte-identical.
- [ ] The sanity cases, executed (or "pending" for a partial).

## Known pitfalls at this pin (hard-won)

- From the pre-ship probe, each of which failed a first run:
  - `Turing.WindowExit` derives only `DecidableEq`: a `Fintype` for the stop phase is given by
    its three values inside `wl_Ctrl_fintype`, through `show Fintype WindowExit from ⟨…⟩` (a bare
    anonymous constructor does not see the expected type);
  - an anonymous-constructor `refine ⟨…, fun e h => by cases h, …⟩` mis-parses: give the
    distinctness clauses as `?_` and prove them in bullets;
  - `(Sigma.mk.inj h).2` is a `HEq`: use `eq_of_heq`, not `.eq`;
  - inside `wl_red`, a dotted constructor of the stop phase needs its type:
    `(WindowExit.halted : WindowExit)`.
- `phaseHostTM_run` gives the prefix up to `T` and the dispatch at `T + 1`; its `hguard` must hold
  strictly before `T`. A row whose entry equals its verdict has `T = 0`.
- `exists_recordTestTM` runs on any input word (`{y : List (RecSym Q T)}`), so the R1-embedded test
  on the record tape needs no input conversion; `exists_recordStepTM` needs the native input as
  digits, `x.map (RecSym.digitEmb Q T)`, which is your configuration's input.
- `Cfg.inputPos : Fin (|input| + 2)` starts at `1`; compare positions by `.val`.
- A halted source has `M.step c = c` and `M.outputSymbol c = none` (`step_of_halt`,
  `outputSymbol_of_halt`); `windowRun`'s first test catches it before any step.
- `K + 2` in target 2's statement and the clock's `K + 1 + 1` are the same tape count; if `rw`
  complains, `show` the goal at `K + 1 + 1`.
- `omega` with products and powers as atoms (`ring` first to expose them). The linter needs a
  literal "Proof sketch" before every `sorry` (partial only).
- MIG-0b moved `MultiTapeTM.runFrom_mapState_of_agreeOn` to `StateRenaming` and
  `MultiTapeTM.spaceUsedByTape_le_card_Icc` to `Finite`; the names are unchanged.
