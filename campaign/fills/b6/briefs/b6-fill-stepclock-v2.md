# Ch3–4 fill campaign — B6 fill, batch F1, brief v2: the step clock (`Turing.exists_stepClockTMVia`, `Build/StepClock.lean`, with promotions in `Build/CounterLoop.lean` and `SymbolLift.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- **If Lean cannot start, follow `briefs/fill-environment-addendum.md` exactly.**
- Before you start, confirm that `git merge-base --is-ancestor 15c404be6ba320bbf6e8be1788a1d4b8b43a0c4f HEAD`
  succeeds. That commit contains:
  - the B6 hosts (#92), the H1 harvest (#94), record-table row 18 proved (#95), the canonizer's
    continuation 3 (#96) and the C1-A assembly with the public `Turing.embedSilentCfg_cap` in
    `Build/Embed` (#97), all merged;
  - the fill-agent environment addendum (`briefs/fill-environment-addendum.md`) and the
    declaration-keyed copy-text screen v3 (`audits/evidence/retrofit/copy-text-screen-v3.py`);
  - brief v1 (`briefs/b6-fill-stepclock.md`, superseded by this brief) and the first delivery's
    report, which stopped on escalation E1 (`audits/b6-fill-agent-reports/stepclock-1-REPORT.md`);
  - this round's order list (`briefs/orders/b6-fill-stepclock-v2.txt`), base sorry set, screen
    population and base, pre-ship log, and the pre-ship probes with their generators
    (`audits/evidence/b6-fill-stepclock-v2/`).

  If the check fails, **stop**.
- **Branch at exactly that commit, not at the campaign tip:**

  ```sh
  git checkout -b fill/b6-stepclock-v2 15c404be6ba320bbf6e8be1788a1d4b8b43a0c4f
  git rev-parse HEAD        # must print 15c404be6ba320bbf6e8be1788a1d4b8b43a0c4f
  ```

  Record that hash as your base in `REPORT.md`. Never rebase, merge or cherry-pick later campaign
  commits. Pinning keeps your base, your base sorry set and your screen base exactly the ones this
  brief states. The maintainer re-checks your delivery at integration on the tip of that day.
  Ground rule 10 says what the pinned base means for your citations.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-b6-stepclock-v2.zip`,
  containing `REPORT.md`, the full modified sources (all three owned files), a `git format-patch`
  series against `15c404be6ba320bbf6e8be1788a1d4b8b43a0c4f`, a git bundle whose only prerequisite is `15c404be6ba320bbf6e8be1788a1d4b8b43a0c4f`, the bootstrap
  and final sweep logs, the axiom log, the sanity evidence file `B6F1Sanity.lean.txt` and its log,
  the route-probe re-run log, both screen outputs, and `SHA256SUMS`.

## Why there is a v2 (read this)

The first delivery under v1 stopped before phase 1, correctly (its report, escalation E1): v1's
binding route needed counter-arithmetic bridges that are **private** in `Build/CounterLoop.lean`,
cost and embedding equations that only an unfolding gives, and the field behaviour of the symbol
overlay (`Cfg.decodeSymbols`, `Cfg.liftOver`), while v1's rule 10 forbade private citations and
those unfoldings, and v1's own prescribed `sc_lastLayout` unfolded `Turing.lastEmb`. v1's import
probe checked that names resolve, not that the route can be completed.

**The user's decision (2026-10-14): authorize exactly the promotions the route needs.** This brief
therefore (1) adds two owned files for a fixed list of edits only (the promotion list below), (2)
prescribes the exact text of every edit, and (3) ships a **route probe** that discharges each route
step's interface with the library from public declarations only, with every promotion applied.
The target, its statement, the route and the C1 form are unchanged; `exists_stepClockTMVia`'s
statement is the one B6-F2 cites.

## Base, line numbers and what lands around you

- **Lines in this brief are those of campaign commit `ff4cab18`**, whose Lean content is the merge
  of #95–#97 (`c9cc485b`'s). No commit after `c9cc485b` up to and including the inputs commit
  `15c404be6ba320bbf6e8be1788a1d4b8b43a0c4f` touches a `.lean` file, so your base's Lean content is exactly `c9cc485b`'s. `Build/StepClock.lean`, `Build/CounterLoop.lean` and
  `SymbolLift.lean` are byte-identical to their `c52663f1` versions (checked); v1's line numbers in
  them stand. Every probe and measurement below was run at `ff4cab18`, against the olean snapshot
  of that tip's catch-up replay (`oleans-ltip3`).
- **#95–#97 are in your base.** Of their five Lean files, `Build/Embed.lean` (#97: the public
  `Turing.embedSilentCfg_cap`) is in your import closure; your route uses only the forwarding
  embedding. `Build/RecordTable` (row 18 now proved), `CodeSimulator`, `Build/NDHost` and
  `SpaceComplexity/Inclusions` are in your order list, downstream of your owned files.
- **MIG-1 stage S (not merged when this brief was issued) is not in your base.** It edits modules in your import
  closure: `Simulation`, `Composition`, `Build/Wrappers`, `Encoding`, `Build/Loop` and
  `Build/Catalog` (with `ClassP/TimeConstructible` and `Build/Primitives`, outside it); none of
  your owned files. It makes private witnesses public under new names
  (`audits/evidence/mig1/gate/scripts/renames.json`: for example `loopHost` → `loopHostTM`,
  `emCallTM` → `callTM`, `catalogPrefixTM` → `prependTM`, `counterTM` → `FinTM.lengthBitsTM`) and
  moves `Turing.FinTM.rewind_heads` and `rewind_scan_heads` from `Build/Catalog` to `Simulation`
  (same names). It is invisible to your base. **Cite no private name of those files**, and keep
  your new privates under the `sc_` prefix. None of the publics this brief cites or adds meets a
  name of S's (checked against `renames.json` and the tree: every new name has no occurrence).

## Parallel batches this round (disjoint files; never edit another batch's)

| Batch | Brief | Owns |
|---|---|---|
| B6-F1, the step clock (v2) | this brief | `TuringMachine/Build/StepClock.lean` (regions (a)–(d)); `TuringMachine/Build/CounterLoop.lean` and `TuringMachine/SymbolLift.lean`, **for the listed promotion edits only** |
| B6-F2, the windowed runner | `briefs/b6-fill-windowrun.md` (re-dispatched unchanged, with the addendum) | `TuringMachine/Build/WindowRun.lean` |

B6-F2 cites your target by its frozen statement only; your promotions are invisible to it, and it
cites none of them. Your owned `CounterLoop` and `SymbolLift` are upstream of 75 and 78 modules
of your order list (B6-F2's file among them): that is why the final sweep below re-checks them all.

## What this is

**H3's clock, the step-clocked runner, stated once for B6 and C1** (C1 decision 4; the B6 hosts
gate, round 1, PASS, `audits/b6-hosts-statements-findings.md`, note N3: "No findings in the formal
contract or the constants … Keep both `+2` bounds"). Your target is `Turing.exists_stepClockTMVia`
(`Build/StepClock.lean:115`): a host on one more tape that runs a body machine under a binary
countdown ticking once per **physical** body step, with exits `finish` and `timeout`, exact
endpoints, no earlier exit, the counter frame `Turing.wordPatch` and an all-times trajectory
clause. It heads the plan's chain to `Complexity.space_hierarchy`
(`audits/evidence/b6-fill/B6-fill-plan.md`). **It also serves C1**, whose consumers cite the
`Bool` form `Turing.exists_stepClockTM` (`:177`), proved in the file from your target and frozen.

**Proved-modulo set: empty.** A complete delivery has no `sorryAx` in `exists_stepClockTMVia`, and
therefore none in `exists_stepClockTM`.

**Read first:** the target's docstring (its sketch is binding); the gate's findings on the clock
(note N3, the ruling on brief point 1, the step-clock paragraph after the adversarial table, the
suggested sanity lemmas); the first delivery's report (escalation E1 and the additional conflict;
`audits/b6-fill-agent-reports/stepclock-1-REPORT.md`);
`Build/CounterLoop.lean` lines 1–124, 566–700 and 799–1232 (the counter loop's debit, body phase
and round induction: **the pattern you follow and must not copy**); `Build/Contract/Basic.lean`
lines 387–600 (segments); this brief's promotion blocks and the route probe.

**Pre-ship check (maintainer, at `ff4cab18`, against `oleans-ltip3`;
`audits/logs/b6-fill-stepclock-v2-preship.log`):**
- `audits/evidence/b6-fill-stepclock-v2/B6F1v2ImportProbe.lean.txt` (95 `#check`s, v1's list and
  the names this brief adds): every public declaration of the issue tree that the brief cites
  resolves in your file's import context. 0 errors, 0 warnings. **Re-run it after your delivery.**
- **The promotion list** (`tools/mkpromote.py`, every anchor asserted, the reverse edit checked byte
  for byte): `CounterLoopOverlay.lean.txt` and `SymbolLiftOverlay.lean.txt`, each elaborated on its
  own against the snapshot: **0 errors, 0 warnings, 0 sorries**.
- **The route probe** (`RouteProbe.lean.txt`, `tools/mkrouteprobe.py`; table below): **0 errors,
  0 non-sorry warnings, exactly 3 sorry warnings**, the three stubs `sc_debit`, `sc_finish` and
  `sc_timeout`. It elaborates the promotions, the v2 home block (`StepClockOverlay.lean.txt`, the
  overlay of `StepClock.lean` that cannot be elaborated alone before `CounterLoop` is rebuilt), the
  glue, and Part D's 14 route statements and 4 fit examples, all proved. The 19 promoted and new
  lemmas and the ten proved prescribed lemmas print the standard axioms or fewer; `sorryAx`
  appears exactly in the three stubs, the headline and `exists_stepClockTM`.
- **The static scan** (`tools/routescan.py`) on the home block, the glue and Part D: 0 findings
  (no private name of `CounterLoop` or `SymbolLift`, no `simp`/`rw`/`dsimp`/`unfold`/`delta`
  argument that is a definition of `CounterLoop`, `SymbolLift`, `Embed` or `Contract/Basic`). Its
  control flags v1's `simp [clockCfg, lastEmb]` and a planted private citation and two unfoldings.

## The promotion list (binding; apply it first, verbatim)

Every edit to `Build/CounterLoop.lean` and `SymbolLift.lean` is one of these; nothing else in
those two files changes. **Phase 0 of your delivery is applying them exactly**, by the generator,
which asserts every anchor and checks that removing the blocks (and restoring `private`) gives
back the issue-tree files byte for byte:

```sh
P=audits/evidence/b6-fill-stepclock-v2/tools
python3 -I $P/mkpromote.py . $P /tmp/CounterLoop.lean /tmp/SymbolLift.lean
cp /tmp/CounterLoop.lean TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean
cp /tmp/SymbolLift.lean TCSlib/Complexity/TuringMachine/SymbolLift.lean
```

The two results must have the SHA-256 that `audits/evidence/b6-fill-stepclock-v2/CounterLoopOverlay.lean.txt`
and `SymbolLiftOverlay.lean.txt` have (they are those files). Then never edit those two files again.

**(1) Existing private lemmas made public in place** — visibility only: `private lemma` becomes
`lemma`; name, statement, proof and docstring byte-identical. **The names are kept**: they are
`Turing.`-namespaced, in the file's `counter_` style (`counter_cfg_eq` is public already), and a
rename would edit the frozen proofs that use them (`counter_dec_zero`, `counter_word_decrement`,
`counter_potential`, `counter_word_exhausted`, `counter_debit`, `counter_rounds`).

| # | Line (issue tree → after) | Declaration | What the route needs it for |
|---|---|---|---|
| P1 | `CounterLoop.lean:393` → `:443` | `Turing.counter_dec_spec` | the debit: a predecessor keeps the width; underflow means all `false`, so the cost `2·|takeWhile not w| + 2` is `2|w| + 2` |
| P2 | `:421` → `:471` | `Turing.counter_dec_zero` | the timeout: value `0` iff underflow |
| P3 | `:479` → `:529` | `Turing.counter_word_decrement` | the rounds: before exhaustion the decrement of the `r`-th frozen word succeeds with the next one |

Not promoted, although the first report listed them: `counter_word_succ` and
`counter_word_exhausted`. The route probe discharges the rounds and the timeout without them
(`rp_round_word`, `rp_timeout_word` below), so they stay private (minimality).

**(2) New lemmas** — each with the exact statement, home, proof, and docstring with a proof sketch
in the named block file (`audits/evidence/b6-fill-stepclock-v2/tools/`):

| # | Home (blank line at the issue tree → the lemma's line after) | Declaration | Statement | Proof |
|---|---|---|---|---|
| N1 | `CounterLoop.lean:369`, after `decrementTM_run_underflow_ofCfg` → `:376` | `Turing.decrementTM_tr_input` | `(decrementTM k i).tr q inp work = (decrementTM k i).tr q inp' work` | `rfl` |
| N2 | same block → `:389` | `Turing.decrementTM_tr_action` | `((decrementTM k i).tr q inp work).inputTape = 0 ∧ ∀ j, (((decrementTM k i).tr q inp work).workTapes j).1 ≠ some none` | unfold the table, split on phase and cell |
| N3 | `:377`, after `counterWord` → `:408` | `Turing.counterWord_zero` | `counterWord w 0 = w` | `rfl` |
| N4 | `:388`, after `counterOverhead` → `:426` | `Turing.counterOverhead_zero` | `counterOverhead w 0 = 0` | `Finset.sum_range_zero` |
| N5 | same block → `:434` | `Turing.counterOverhead_succ` | `counterOverhead w (r + 1) = counterOverhead w r + (2 * ((counterWord w r).takeWhile not).length + 2)` | `Finset.sum_range_succ` |
| N6 | `:619`, after `lastEmb` → `:673` | `Turing.lastEmb_apply` | `lastEmb k i = Fin.last k` | `rfl` |
| N7–N11 | `SymbolLift.lean:379`, before `end Overlay` → `:388`–`:419` | `Turing.Cfg.decodeSymbols_state`, `_inputPos`, `_workTapes`, `_workTapePos`, `_output` | the shadow's fields: `D.state`; `D.inputPos` as a number; `(D.workTapes j p).bind (decodeBool e)`; `D.workTapePos`; `[]` | `rfl` each |
| N12–N16 | same block → `:426`–`:463` | `Turing.Cfg.liftOver_state`, `_inputPos`, `_workTapes`, `_workTapePos`, `_output` | the overlay's fields: `c.state`; `c.inputPos` as a number; `if c.workTapes j p = (D.workTapes j p).bind (decodeBool e) then D.workTapes j p else (c.workTapes j p).map e`; `c.workTapePos`; `D.output ++ c.output.map e` | `rfl` each |

Blocks: N1–N2 `cl-decrement.lean.txt`, N3 `cl-counterWord.lean.txt`, N4–N5
`cl-counterOverhead.lean.txt`, N6 `cl-lastEmb.lean.txt`, N7–N16 `sl-fields.lean.txt`. None carries
`@[simp]` (no downstream `simp` changes behaviour). N1–N2 replace v1's one exception to rule 10
(unfolding `decrementTM`'s table for the overlay transport's side conditions). N2's first half is
new to the route: the clock's frame clause needs the input head at **every** debit time, which no
public contract states; the run-level fact is the prescribed private `sc_dec_inputPos` in your
home (a pre-ship version of it as a `CounterLoop` lemma paired with three existing proofs on the
screen, so it was moved, and N2 merges the two table facts into one proof).

**Sizes after the promotions:** `CounterLoop.lean` 2,149 → 2,205 lines (44 → 53 public, 23 → 20
private, by the lint); `SymbolLift.lean` 382 → 470 lines (22 → 32 public) (MEASURED).

## Owned regions and target (modify these and nothing else)

| # | File:line | Target | Route | Uses |
|---|---|---|---|---|
| 1 | `TuringMachine/Build/StepClock.lean:115` | `Turing.exists_stepClockTMVia` | the docstring's sketch; concretely, the route below | the promotions, the C1 decrement, R1, the symbol lift, counter arithmetic, segments |

- **`Build/CounterLoop.lean` and `SymbolLift.lean`:** the promotion list only (P1–P3, N1–N16), at
  the lines above, by the generator. Every other declaration in them is frozen: statement, body,
  docstring and attributes.
- **(a) The home:** the blank line **81** of `StepClock.lean`, between `Turing.Cfg.Stopped` (line
  80) and the target's docstring (line 82). Insert `tools/home.lean.txt` there first, in its order;
  your own `private` declarations go in the same home, after what they use and before their first
  consumer. No `section`, `open` or `variable` that leaks past it.
- **(b) The target's docstring,** lines 82–114: unchanged; append a flagged
  **"Fill appendix (B6-F1)"** before the closing ` -/` on line 114.
- **(c) The target's body,** the `sorry` on line 167 (statement 115–166 frozen): the prescribed
  glue (`tools/headline.lean.txt`).
- **(d) Status text:** the module's "Status" paragraph (lines 23–26) and the "Main results" entry
  (line 51, "(sorried)"), to "proved", flagged, for a complete delivery only.
- **Frozen in `StepClock.lean`:** lines 1–61 apart from (d); `Turing.clockCfg` (68),
  `Turing.wordPatch` (74), `Turing.Cfg.Stopped` (78); the target's statement; and
  **`Turing.exists_stepClockTM` (lines 169–216), byte-identical**.
- **Not yours:** every other file, including `Build/Embed.lean`, `StateRenaming.lean`,
  `Build/Contract/*`, the downstream `Build/WindowRun.lean` (B6-F2's) and
  `SpaceComplexity/WindowClock.lean`, C1's modules, the colleague-owned
  `TimeHierarchy/ClockMachine.lean` and `ClockLoop.lean`, and the facades.

### Prescribed home declarations (binding where marked; elaborated in the route probe)

Take `tools/home.lean.txt` (v1's block, revised). Replace its tags by ordinary docstring prose.

| Declaration | Status | Role |
|---|---|---|
| `sc_State` (`deriving DecidableEq`), `sc_State_fintype` | suggested | the control: `dec s f`, `body s`, `finish r`, `timeout r` |
| `sc_decExit`, `sc_bodyAct`, `sc_clockTM` | suggested | the landings and **the fused machine** (v1's, unchanged) |
| `sc_decExit_injective`, `sc_agree`, `sc_layout` | **prescribed, proved** | as in v1 (`sc_layout` by the public `embedEmitCfg_eq`) |
| `sc_lastLayout` | **prescribed, proved, revised** | v1's statement; its proof now uses `Turing.lastEmb_apply` (N6) and unfolds no `CounterLoop` definition |
| `sc_dec_inputPos` | **prescribed, proved, new** (a promotion candidate) | the decrement never moves the input head, at every time of every run (from N2) |
| `sc_wordPatch_self` | **prescribed, proved, new** | `wordPatch ct cp u = ct` when `ct` already holds `u` delimited at `cp`: round 0's tape |
| `sc_wordPatch_twice` | **prescribed, proved, new** | a same-width patch over a patch is the second patch: the tape after each round |
| `sc_wordPatch_frame` | **prescribed, proved, new** | a same-width patch keeps the word delimited: the next round's precondition |
| `sc_debit` | **stub, recommended statement** (v1's; a promotion candidate) | the generic debit |
| `sc_stop_step`, `sc_body_step` | **prescribed, proved** | as in v1 |
| `sc_finish`, `sc_timeout` | **stubs, binding statements** | the target's two clauses for `sc_clockTM` |

The three `wordPatch` lemmas are about your file's own public `Turing.wordPatch`, so they are
proved by unfolding it; `CounterLoop`'s private `counter_patch_twice` and `counter_patch_frame`
prove the same for their private twin `counterPatch`, in different words (no screen pair). They
are listed with the dedup items for the maintainer (`BRIEF-NOTES.md`). **The target's body is the
prescribed glue** (`tools/headline.lean.txt`, v1's, verbatim).

You may replace the suggested machine (and with it the stubs' statements) by your own fused
controller, if you keep the glue's shape; say why in `REPORT.md`. `sc_debit`'s statement is a
recommendation (keep it generic in the host and the embedding). If a prescribed statement turns out
false or unusable, that is an escalation (ground rule 4).

### The route probe (what it establishes)

`audits/evidence/b6-fill-stepclock-v2/RouteProbe.lean.txt`, generated by `tools/mkrouteprobe.py`,
is one Lean file standing for the module stack with every promotion applied: `CounterLoop`'s
imports (the snapshot's), then Part A (the SymbolLift block, verbatim), Part B (`CounterLoop` with
the promotions, verbatim), Part C (`StepClock` with the v2 home block and the glue, verbatim) and
Part D (`tools/routechecks.lean.txt`: one statement per route seam, proved). Inlining is needed
because an edited module cannot be imported without an olean, and none is written. It also makes
`CounterLoop`'s privates visible to Parts C and D, which a module boundary would hide; the static
scan `tools/routescan.py` checks that the home block, the glue and Part D name none of them, and
that no `simp`, `rw`, `dsimp`, `unfold` or `delta` argument there is a definition of
`Build/CounterLoop`, `SymbolLift`, `Build/Embed` or `Build/Contract/Basic` (control: the scan
flags v1's `simp [clockCfg, lastEmb]` and a planted private citation and unfoldings,
`tools/routescan-control.lean.txt`).

| Route seam | Probe statement (Part D) | Discharged by (public only) |
|---|---|---|
| step 0: the start | `rp_start` | `counterWord_zero`, `counterOverhead_zero`, `sc_wordPatch_self` |
| step 1, debit, success | `rp_dec_success_width`, `rp_dec_patch_width` | `counter_dec_spec` |
| step 1, debit, underflow | `rp_dec_underflow_cost` | `counter_dec_spec` |
| step 1, the shadow meets both decrement contracts | `rp_shadow_pre` and two fit examples | `Cfg.decodeSymbols_state`, `_workTapes`, `_workTapePos`, `FinTM.bufferTape_map_decode`, `decrementTM_run_succ_ofCfg`, `decrementTM_run_underflow_ofCfg` |
| step 1, the lift transport | `rp_lift_run` | `liftSymbols_runFrom_over` with `decrementTM_tr_input`, `decrementTM_tr_action`, `Cfg.liftOver_decodeSymbols` |
| step 1, the frame during the debit | `rp_lift_frame`, a fit example into `sc_lastLayout` | `Cfg.liftOver_inputPos`, `_output`, `_workTapePos`, `sc_dec_inputPos` (from `decrementTM_tr_action`), `Cfg.decodeSymbols_inputPos`, `MultiTapeTM.output_prefix` |
| `sc_lastLayout` without unfolding `lastEmb` | Part C | `lastEmb_apply`, `embedEmitCfg_eq` |
| step 2, the round's counter word | `rp_round_word` | `counter_word_decrement` |
| step 2, the round's tape | `rp_round_tape` | `sc_wordPatch_twice`, `sc_wordPatch_frame`, `counterWord_length` |
| step 2–3, the round's time | `rp_round_time` | `counterOverhead_succ` |
| step 4, timeout's word and cost | `rp_timeout_word` | `counterWord_value`, `counter_dec_zero`, `counter_dec_spec` (through R1b), `counterWord_length` |
| step 4, accumulated time | `rp_finish_time`, `rp_timeout_time` | `counterOverhead_le_of_le`, `counterOverhead_le`, `counterOverhead_succ` |
| the machine | the v1 fit example (`sc_debit` at `sc_clockTM`) | `sc_agree`, `sc_decExit_injective` |

**No step is left undischarged** at its seam. What remains is the fill proper: `sc_debit` (the
transport composed), the round induction, and `sc_finish`, `sc_timeout`. Cite the `rp_` facts'
sources, or copy a probe statement into your home as a private lemma (they are yours to take; list
any you take).

### Hosts (binding; the host-first rule, `policy.md` §1, `workflow.md` §2)

As v1: the step clock is the host (registry row H3's clock); its phases are the one-tape decrement
with its framed contracts, the symbol lift with the overlay transport, R1 along `Turing.lastEmb` and
`Fin.castSuccEmb`, and the guarded state transport; counter arithmetic is cited, never re-proved
(now including P1–P3 and N3–N5); rounds compose as MIG-0b segments (`Turing.Segment`,
`Segment.trans`); layouts through `sc_layout` and `sc_lastLayout`. `Turing.Round.iterate` and
`Turing.Lockstep` do not fit (one fixed anchor; an encoding that is a function of the body
configuration). Write no other host.

### The route (binding where it names a row)

1. **The generic debit** (`sc_debit`). Follow the proof shape of the private `counter_debit`
   (`Build/CounterLoop.lean:799`, at the issue tree), with `H` and `ρ` in place of
   `counterLoopTMVia` and its redirection, but do not copy its text, and use only the seams of
   the route probe: the shadow (`rp_shadow_pre`), the two decrement contracts, the lift
   (`rp_lift_run`), the overlay's fields and frame (`rp_lift_frame`), R1 on the last tape
   (`Turing.embedEmitTM_runFrom`, `sc_lastLayout`), the transfer to `H`
   (`Turing.MultiTapeTM.runFrom_mapState_of_agreeOn` with `ρ` and the guard "not at a `done`
   phase"), the widths and costs (`rp_dec_success_width`, `rp_dec_underflow_cost`,
   `rp_dec_patch_width`).
2. **One round.** From `clockCfg (some (.dec s .run)) c ct cp` with `c` live at `s`, `stopAt s =
   false` and counter word `counterWord w r` of positive value: `sc_debit` at
   `ρ := ⟨sc_decExit s, sc_decExit_injective s⟩` (hypothesis `sc_agree … s hs`) reaches `body s`
   with the counter patched to `counterWord w (r + 1)` (`rp_round_word`); `sc_body_step` lands at
   `dec s' .run` with `M.step c` (or at `finish none` if it halts). The round costs
   `2·|takeWhile not (counterWord w r)| + 3`; a stop state costs one step (`sc_stop_step`).
3. **The rounds.** Induct on the body time: after `r` rounds (`r ≤ min τ d` for finish, `r ≤ d` for
   timeout) the host is at `clockCfg (some (.dec _ .run)) (M.runFrom c r) (wordPatch ct cp
   ((counterWord w r).map e)) cp` at time `counterOverhead w r + r` (`rp_start`, `rp_round_tape`,
   `rp_round_time`), with no exit before, the body part at some body time `≤ r` throughout, and the
   counter head in `[cp - 1, cp + |w|]`. Join rounds as segments.
4. **The two clauses.** *Finish:* at the first stop `τ ≤ d`, one more step if it is a live stop
   state, none if the `τ`-th transition halted; time `≤ 5τ + 2|w| + 2` (`rp_finish_time`).
   *Timeout:* at round `d` the word underflows (`rp_timeout_word`) to `timeout (some _)` with the
   counter all `true`; time `≤ 5d + 2|w| + 2` (`rp_timeout_time`). The trajectory clause: during
   round `r` the body part is `M.runFrom c r`, after its body transition `M.runFrom c (r + 1)`.
5. **Package:** the prescribed glue. Then the sanity file.

- **Degenerate cases:** `k = 0`, `w = []` (underflow at once, 2 steps), an initial stop state
  (`τ = 0`: one step, whatever `w`; the tape is `wordPatch ct cp (w.map e) = ct`, `sc_wordPatch_self`),
  a stop exactly at the budget (`τ = d`, by finish), and a zero-valued nonempty word
  (`w = [false, false]`: timeout within `6` steps, the counter left all `true`).
- **Input convention:** the input head is the body's at every time (`sc_dec_inputPos`
  during a debit; the stop dispatch never moves it).

### Phases (for a partial; ground rule 9)

0. **The promotion list applied** (generator; the two files' SHA-256 checked), and the full sweep
   green with the base sorry set unchanged.
1. **The prescribed block and the glue landed** (the headline's `sorryAx` only through
   `sc_finish`, `sc_timeout`, which may use `sc_debit`; the integration's freeze check is then an
   axiom walk naming exactly the open stubs).
2. **`sc_debit` proved.**
3. **The rounds** (step 3), as a private lemma.
4. **`sc_timeout`, then `sc_finish`:** the headline is complete.
5. **The sanity file.**

## Gate guidance (binding)

As v1: keep both `+ 2` bounds; intercept every verdict (`sc_decExit`); no termination hypothesis;
the frame clause at **every** host time up to the exit, including the debit's intermediate times;
note 46 (file size is not a driver). **Sanity cases at fill** (the gate's suggested sanity lemmas):
in an evidence file `B6F1Sanity.lean.txt` that imports `TCSlib.Complexity.TuringMachine.Build.StepClock`,
prove as `example`s from the public headline, for a concrete small body: (a) `w = []` times out
within `2` steps; (b) an initial designated stop finishes within `2 · |w| + 2` steps, for
`w = [true, false]`; (c) a body that first stops exactly at the budget (`τ = d = 1`, `w = [true]`)
finishes; (d) at timeout the returned counter word has the original width and the counter head is
back at `cp` (`w = [false, false]`). No `#eval`, `native_decide` or `IO`. A partial says "pending".

## Cited infrastructure (public at `15c404be6ba320bbf6e8be1788a1d4b8b43a0c4f` once the promotion list is applied; all in `B6F1v2ImportProbe.lean.txt` or the route probe)

- **Added by the promotion list:** P1–P3 and N1–N16 above. The import probe cannot import them (no
  olean of the edited modules); the route probe elaborates every one, and its Part D cites them.
- **StepClock (yours, frozen):** `clockCfg`, `wordPatch`, `Cfg.Stopped`, `exists_stepClockTMVia`,
  `exists_stepClockTM`.
- **CounterLoop:** `decrementTM`, `decrementTM_run_succ_ofCfg`, `decrementTM_run_underflow_ofCfg`,
  `decFixed`, `counterWord`, `counterWord_length`, `counterWord_value`, `counterOverhead`,
  `counterOverhead_le_of_le`, `counterOverhead_le`, `lastEmb`; for orientation only:
  `counterLoopTMVia`, `counterLoopCfg`, `counterLoopCfg_body`, `counterLoopTMVia_run_done`,
  `counterLoopTMVia_run_escape`, `CounterLoopState`.
- **Catalog:** `FlagPhase` (`run`, `rewind`, `done`), `incrementTM`.
- **SymbolLift:** `MultiTapeTM.liftSymbols`, `MultiTapeTM.liftSymbols_runFrom`,
  `MultiTapeTM.liftSymbols_runFrom_over`, `Cfg.liftSymbols`, `Cfg.liftSymbols_state`,
  `Cfg.liftSymbols_workTapePos`, `Cfg.liftOver`, `Cfg.decodeSymbols`, `Cfg.liftOver_decodeSymbols`,
  `decodeBool`, `decodeBool_apply`, `decodeBool_eq_some`, `FinTM.bufferTape_map`,
  `FinTM.bufferTape_map_decode`.
- **R1 (Embed):** `embedEmitTM`, `embedEmitCfg`, `embedEmitTM_tr`, `embedEmitTM_runFrom`,
  `embedEmitTM_frame`, `embedEmitCfg_eq`, `embedEmitCfg_selected_tape`, `embedEmitCfg_selected_pos`,
  `embedEmitCfg_unselected`.
- **State transport:** `Action.mapState`, `Cfg.mapState`, `Cfg.mapState_apply`,
  `MultiTapeTM.runFrom_mapState_of_agreeOn`.
- **Segments (Contract/Basic):** `Segment`, `Segment.zero`, `Segment.one`, `Segment.cons`,
  `Segment.trans`, `Segment.take`, `Segment.drop`, `Segment.mono`, `Segment.live`,
  `Segment.time_eq`, `HeadBox`; named in the hosts paragraph: `Round`, `Round.iterate`, `Lockstep`.
- **Runs and configurations:** `MultiTapeTM.step`, `MultiTapeTM.runFrom`, `runFrom_zero`,
  `runFrom_add`, `runFrom_succ_eq_step`, `runFrom_succ_eq_step'`, `step_of_halt`,
  `runFrom_of_halt`, `step_output`, `outputSymbol`, `outputSymbol_of_halt`, `output_prefix`,
  `workTapePos_runFrom_mem_Icc`, `spaceUsedByTape_le_card_Icc` (all `Turing.MultiTapeTM.`);
  `Action.apply`, `Cfg.ext`, `Cfg.inputSymbol`, `Cfg.workTapeSymbols`, `moveInputPos`,
  `moveInputPos_zero`, `FinTM.bufferTape`, `FinTM.bufferTape_left`, `FinTM.bufferTape_nat`.
- **Do not cite** anything downstream or outside your import closure (`Build/Seam`,
  `Build/Contract/{Seam,Embed,Catalog,Lift}`, `Build/StepBlock` are not imported).

## Ground rules (binding)

1. **File ownership.** `StepClock.lean`'s regions (a)–(d); in `CounterLoop.lean` and
   `SymbolLift.lean`, exactly the promotion list, applied by the generator. List every new
   declaration of yours (all in `StepClock`'s home) with its role. A lemma that belongs in a shared
   file is written privately in your home, flagged as a promotion candidate, and promoted by the
   maintainer.
2. **Statement freeze** over the target and every landed declaration, the promoted ones included
   (their statements are P1–P3's, byte-identical). Docstrings stay; a flagged Fill appendix is
   expected where your proof refines the sketch.
3. **Status text:** only (d), flagged. **No public declaration beyond the promotion list.** The named
   witness `sc_clockTM` and `sc_debit` are promotion candidates.
4. **Escalation** on anything unprovable as stated, including a prescribed statement, a promotion,
   or a cited row that does not compose as the route says: stop on that item, record it, continue.
5. **No touching other sorries.**
6. **Imports.** Unchanged in all three files. No TCSlib import may be added. A Mathlib import only
   if a needed lemma requires it; flag it.
7. **One proof per shared argument.** Never write a second decrement contract, lift transport, R1
   transport, layout lemma, counter-arithmetic lemma, field lemma or span structure.
8. **Size.** No cap. Report each owned file's final line count and its public and private
   declaration counts (base, by the lint: `StepClock` 218 lines; `CounterLoop` 2,149; `SymbolLift`
   382; after the promotions 218, 2,205, 470).
9. **Continuation budget.** A partial zip is expected and fine (phase reached, open `private`
   helpers each with a literal "Proof sketch", what is proved modulo them).
10. **The pinned base, revised.**
    - Cite only declarations public at `15c404be6ba320bbf6e8be1788a1d4b8b43a0c4f`, **the promotion list's P1–P3 and N1–N16**, and
      your file's own privates.
    - **The definitional projections of `Turing.lastEmb`, `Turing.counterWord` at `0`,
      `Turing.counterOverhead`, `Turing.decrementTM`'s table, `Turing.Cfg.decodeSymbols` and
      `Turing.Cfg.liftOver` are allowed only through N1–N16.** v1's exception (unfolding
      `decrementTM`'s table) is withdrawn; N1–N2 replace it.
    - Everything else stays as in v1: do not rely on unfolding the body of any definition in
      `CounterLoop`, `Embed`, `SymbolLift` or `Contract/Basic`; use their public contracts. Your own
      file's definitions (`clockCfg`, `wordPatch`, `Cfg.Stopped`, your privates) you may unfold.
    - Nothing that lands after your base is visible to you.
    - List every declaration you cite outside your file in `REPORT.md`; the import probe and the
      route probe cover this brief's list; if you cite more, add them to a copy and run it.
11. **MIG-1 compatibility.** Cite none of the six R3 canonical rows (`copyTM_run`,
    `transferTM_run`, `clearTM_run`, `compareTM_run`, `incrementTM_run_succ`,
    `incrementTM_run_overflow`) and no private declaration of `Simulation`, `Composition`,
    `Build/Wrappers`, `Encoding`, `Build/Loop` or `Build/Catalog`.

## Duplication governance (binding)

Run the text-level screen **before and after** (`audits/TEMPLATE.md` failure mode 5; `policy.md`,
**Duplication**) with the **declaration-keyed** screen `audits/evidence/retrofit/copy-text-screen-v3.py`
(the campaign's standard since the Diagonal Part 1 gate: labels are basenames where unique and
repository paths otherwise, and a short name repeated within one file gets its namespace-qualified
name; no flattening is needed). On this population its output is byte-identical to v2's, with which
the logs below were measured (maintainer re-check, `audits/logs/b6-fill-stepclock-v2-preship.log`,
last section). The
population is **22 files** (`audits/evidence/b6-fill-stepclock-v2/screen-population.txt`): v1's 21
(your three owned files among them) and `Build/StepBlock`, whose public
`Turing.MultiTapeTM.inputPos_runFrom_of_inputTape_eq_zero` is the overlap of `sc_dec_inputPos`.

```sh
python3 -I audits/evidence/retrofit/copy-text-screen-v3.py . \
  $(grep -v '^#' audits/evidence/b6-fill-stepclock-v2/screen-population.txt) > screen-before.txt
```

The base, at `ff4cab18`, is `audits/logs/b6-fill-stepclock-v2-screen-base.txt`: **1,000
declarations, 673 pairs, 192,769 characters** (MEASURED; about 4 minutes). Your "before" must
reproduce it after its header line. No base pair touches `StepClock`; the base pairs of
`CounterLoop` and `SymbolLift` are pre-existing and none involves a promoted lemma except the
in-file `counterWord_value` reproducing `counter_word_decrement` at 63%, which the promotion leaves
as it is.

- **The promotions copy nothing and remove nothing**: the population with
  `CounterLoopOverlay.lean.txt` and `SymbolLiftOverlay.lean.txt` in place
  (`audits/logs/b6-fill-stepclock-v2-screen-promotions.txt`) gives 1,001 / 673 / 192,769: the
  identical pair set and reproduced text (a first version, with a run-level input lemma in
  `CounterLoop`, added three pairs and was replaced before the final runs). Apply them verbatim,
  and your "after" screen must show no pair that involves a promoted or new lemma.
- **The prescribed home block, measured** (the population with all three overlays):
  `audits/logs/b6-fill-stepclock-v2-screen-overlay.txt`: 1,015 / 675 / 193,179, two new pairs
  against the promotions screen, both v1's pre-disclosed cross-file pair: `counterLoopTMVia`
  reproduces the suggested `sc_clockTM` at 56%, and the reverse at 66% (the shared phase
  structure, below 90%). The new prescribed lemmas (`sc_dec_inputPos`, the three `sc_wordPatch_*`)
  pair with nothing. If you take the machine verbatim, report these two pairs as pre-disclosed.
- **No new cross-file pair** with an owned-file declaration on one side, except the pre-disclosed
  ones. Known hazards, as v1: `counter_debit`, `counter_body`, `counter_rounds`
  (`CounterLoop.lean:799`, `:967`, `:1130`): write your debit and rounds generic and in your own
  words, and **`sc_debit` is the requested shared lemma** that would retire `counter_debit`'s proof;
  `counter_patch_twice` and `counter_patch_frame` against the prescribed `sc_wordPatch_*`; the R1
  layout family; `counter_dec_injective` against `sc_decExit_injective`; Hydroxyi's `clockTM` and
  `ClassNP/Nondeterminism`'s private `choiceCore`; `Build/StepBlock`'s input-position lemma against
  `sc_dec_inputPos`; the contract adapters `Build/Contract/{Lift,Embed}`.
- List every new in-file pair with a one-line justification; at 90% or more it is a copy: factor
  it. Quote both outputs in `REPORT.md`, which carries **"new copies: none"** (or lists each pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check. If Lean cannot start, follow
  `briefs/fill-environment-addendum.md` exactly.
- **Bootstrap once** from `briefs/orders/b6-fill-stepclock-v2.txt` (**292 modules**: the upstream
  closure of your three owned files and of every module downstream of any of them, at the issue
  tree, topologically ordered, without the root `TCSlib`). `SymbolLift` is module 148,
  `CounterLoop` 150, `StepClock` 224; 78, 75 and 4 modules are downstream of them.

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/b6-fill-stepclock-v2.txt )
  ```

  **Base sorry-warning set, 107** (`audits/logs/b6-fill-stepclock-v2-base-sorries.txt`, one entry
  per declaration, 21 modules). Yours: `Build/StepClock` 1. Record the base list by name first, and
  report any difference.
- **Final checks:**
  1. After phase 0 alone: every module of the order list from `SymbolLift` on (145 modules)
     re-checked: zero errors and the base sorry set exactly (the promotions add no sorry and break
     nothing downstream). Record it separately in `REPORT.md`.
  2. `Build/StepClock`: zero errors and no sorry warning (a partial: exactly the open stubs'), and
     no other warning in anything you added.
  3. Every module from `SymbolLift` on, against your final sources: zero errors, sorry warnings
     exactly the base's minus yours (**106** for a complete delivery).
  4. Re-run `B6F1v2ImportProbe.lean.txt` (0 errors), and re-run the route obligations against
     your real modules: append `tools/routechecks.lean.txt` to a scratch copy of your final
     `StepClock.lean` (which then imports your promoted `CounterLoop` and `SymbolLift` from your
     sweep's oleans; do not use the stitched `mkrouteprobe.py` there, whose Part A would declare the
     SymbolLift lemmas a second time) and elaborate it: 0 errors, and no sorry warning for a complete
     delivery. If you renamed or replaced a prescribed private, adapt only those names in your copy,
     and say so. Run `tools/routescan.py` on your home block: 0 findings. Elaborate
     `B6F1Sanity.lean.txt`: 0 errors.
- **Axiom prints** for the target, `exists_stepClockTM`, every promoted and new lemma and every new
  private: `[propext, Classical.choice, Quot.sound]` or a subset, for a complete delivery.
- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine` (it covers
  the three owned files), 0 FAIL; no new line over 100 characters. Base: 0 FAIL, 21 WARN over 74
  files; with the three overlays in place the same (only `CounterLoop`'s size WARN changes,
  2,149 → 2,205 lines).

## Out-of-scope sorries you will see (leave every one untouched)

- `TuringMachine/Build/RecordTable`: exists_tableFindTM, exists_tableAppendTM, exists_recordValidTM, exists_recordNextTM
- `FormulaKit/Gate`: template_eval, template_numVars_le, template_length_le, template_widthAtMost, numVars_le_of_forall_lt, exactlyOne_eval, cost_flatMap_le, serialize_length_le, gate_cost_le, exactlyOne_cost_le
- `FormulaKit/Emit`: polyTimeComputable_fragment_iff_serialize, polyTimeComputable_flatMap_range, polyTimeComputable_fragment_relabel, polyTimeComputable_fragment_gate_select, polyTimeComputable_unary_sub, polyTimeComputable_unary_mul, polyTimeComputable_unary_le, polyTimeComputable_unary_div, polyTimeComputable_unary_mod, polyTimeComputable_serialize_relabel_add
- `ClassPSPACE/TQBF`: width_le, code_length, code_getD_inputVar, code_getD_headVar, code_getD_stateVar, code_getD_workVar, code_getD_summaryVar, code_input_eq, code_eq_iff, validity_eval_iff, adjacency_eval_iff, adjacency_eval_of_ne, acceptance_eval_iff, validity_numVars_le, acceptance_numVars_le, adjacency_numVars_le, exists_serialize_length_le, polyTimeComputable_serialize_validity, polyTimeComputable_serialize_adjacency, polyTimeComputable_serialize_acceptance, polyTimeComputable_code_initCfg
- `TuringMachine/CodeSimulator`: exists_canonGrammarStage [private], exists_canonDecider [private], exists_uniformSimulator
- `Diagonalization/NTimeHierarchy`: exists_timed_universal_NDTM, exists_ndAcceptsWithin_decider, exists_codeNDTM_accepts_linear, ntime_hierarchy, ntime_hierarchy_of_pos, NTIME_linear_ssubset_square
- `RAMSimulation/WordSize`: WordSizeComputable.mono, wordSizeComputable_logSpace, wordSizeComputable_of_spaceConstructible
- `TCSlib/Programs/WordRAM/Extended`: XSteps.trans, xstep_map_base, XSteps.of_steps, XSteps.of_steps_proj, XInstr.card_touches_le, StepsIn.toSteps, Steps.exists_stepsIn, StepsIn.mono, StepsIn.trans, StepsIn.agreeOutside, stepsIn_straight, XStepsIn.toXSteps, XSteps.exists_xStepsIn, XStepsIn.of_stepsIn_proj, HaltsWithin.mono, HaltsWithin.touches_le, HaltsWithin.unique, HaltsWithin.coin_irrel
- `RAMSimulation/Simulation`: exists_simulation, exists_ndSimulation
- `RAMSimulation/Classes`: mem_DTIME_of_decides, mem_P_of_decides, mem_P_of_decides_logWord, mem_SPACE_of_decides, mem_LOGSPACE_of_decides, computesInSpace_of_computes, mem_SPACE_mul_of_decides, mem_NSPACE_of_accepts, mem_NL_of_accepts
- `TuringMachine/Build/WindowRun`: exists_windowLoopTM, exists_windowRunnerTM
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

- [ ] 1/1, or the phase reached (rule 9); the base hash (equal to `15c404be6ba320bbf6e8be1788a1d4b8b43a0c4f`) and the ancestor
      check; whether the environment addendum was needed.
- [ ] Phase 0: the generator's output, both files' SHA-256 against the overlays, the phase-0 sweep.
- [ ] Every new declaration with its role; the prescribed block as taken (any deviation, with its
      reason); `sc_debit` as stated or restated; which route-probe statements you took. Every
      flagged appendix and status update.
- [ ] Promotion candidates (`sc_debit`, `sc_clockTM`) and escalations, or "none".
- [ ] Rule 10: the declarations cited outside your file, the import probe and the route probe
      re-run, `routescan.py` on your home block. Rule 11: a grep of your diff for the six R3 rows
      and the S-renamed privates.
- [ ] Duplication: both screens, every new pair justified, "new copies: none".
- [ ] Sizes, the final sweep tail, the axiom prints, the lint line. The diff touches only your owned
      regions and the promotion list; `exists_stepClockTM` and the three layout definitions are
      byte-identical.
- [ ] The sanity cases, executed (or "pending").
- [ ] For a partial: the headline's axiom walk, naming exactly the open stubs.

## Known pitfalls at this pin (hard-won)

- From the pre-ship probes, each of which failed a first run:
  - a dotted constructor needs its expected type inside a `show … from rfl` or a `rw [show …]`:
    write `sc_State.body s`;
  - after `rw [sc_layout] at h`, `h` and the goal differ in their state field only: split by
    `Cfg.ext` and close each field by `have h := congrArg Cfg.inputPos hE; exact h`;
  - `simp only [MultiTapeTM.step]` unfolds the body's `M.step c` too: unfold the host's step alone,
    by `rw [show H.step d = (H.tr q …).apply d from rfl]`;
  - a membership `⟨0, rfl⟩ : Fin.last k ∈ Set.range (lastEmb k)` unfolds `lastEmb`: write
    `⟨0, lastEmb_apply k 0⟩`;
  - `counter_dec_spec`'s statement is a `match` on `decFixed w`: `rw [h] at hs` with
    `h : decFixed w = some v` (or `none`) reduces it (`rp_dec_success_width`);
  - in the decrement's table, `split` fails on the stationary `done` phase: `(try split)`.
- `Cfg.inputPos : Fin (|input| + 2)`; compare positions by `.val` (`Fin.ext`), as the field lemmas
  N8 and N13 state them.
- A halted source has `M.step c = c` and `M.outputSymbol c = none`; a halting body transition lands
  on `finish none` with `M.step c`'s tapes and output (R1 forwards the emission).
- `Turing.counterWord` freezes at value zero while the machine wraps: `counterOverhead` is the
  physical cost only for `r ≤ value + 1`.
- `Fin.lastCases` splits a host tape index (`Fin.lastCases_last`, `Fin.lastCases_castSucc`).
- `omega` with products and powers as atoms (`ring` first). The linter needs a literal "Proof
  sketch" before every `sorry` (partial only).
