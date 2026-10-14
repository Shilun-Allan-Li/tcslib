# Ch3–4 fill campaign — B6 fill, batch F1: the step clock (`Turing.exists_stepClockTMVia`, `Build/StepClock.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor 70b503b49760b65817a3bce4b876dc466c32235c HEAD`
  succeeds. That commit contains:
  - the B6 hosts (PR #92: the five host modules with their ten sorried contracts, among them
    your target), the ARM minor fixes (#93) and the H1 harvest (PR #94: `Build/StepBlockLoop`,
    and `counterValue_bits` with the public `foldr_bit_eq_ofDigits` in `Build/CounterLoop`), all
    merged;
  - the B6 fill plan (`audits/evidence/b6-fill/B6-fill-plan.md`);
  - this round's order list (`briefs/orders/b6-fill-stepclock.txt`), base sorry set, screen
    population and base, pre-ship log, and the pre-ship probes with their generators
    (`audits/evidence/b6-fill-stepclock/`).

  If the check fails, **stop**.
- **Branch at exactly that commit, not at the campaign tip:**

  ```sh
  git checkout -b fill/b6-stepclock 70b503b49760b65817a3bce4b876dc466c32235c
  git rev-parse HEAD        # must print 70b503b49760b65817a3bce4b876dc466c32235c
  ```

  Record that hash as your base in `REPORT.md`. Never rebase, merge or cherry-pick later campaign
  commits. More landings are queued in your import closure (next section). Pinning keeps your
  base, your base sorry set and your screen base exactly the ones this brief states. The
  maintainer re-checks your delivery at integration on the tip of that day. Ground rule 10 says
  what the pinned base means for your citations.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-b6-stepclock.zip`, containing
  `REPORT.md`, the full modified source, a `git format-patch` series against `70b503b49760b65817a3bce4b876dc466c32235c`, a git
  bundle whose only prerequisite is `70b503b49760b65817a3bce4b876dc466c32235c`, the bootstrap and final sweep logs, the axiom
  log, the sanity evidence file `B6F1Sanity.lean.txt` and its log, both screen outputs, and
  `SHA256SUMS`.

## Base, line numbers and what lands around you

- **Lines in this brief are those of campaign commit `c52663f1`** (the records commit after #94's
  merge). The inputs commit `70b503b49760b65817a3bce4b876dc466c32235c` adds no Lean change to it. `Build/StepClock.lean` has
  not changed since #92 (byte-identical at `1b6b972c` and at `c52663f1`, checked). Every probe
  and measurement below was run at `c52663f1`, against the olean snapshot of #94's replay.
- **#94 (the H1 harvest) is in your base.** It changed `Build/CounterLoop.lean`, which your file
  imports: a new import of `TuringMachine/CodeParser` (so your import closure has 21 modules,
  one more than at #92) and two new public lemmas, `Turing.foldr_bit_eq_ofDigits` and
  `Turing.counterValue_bits`. The lines of `CounterLoop` below are at the new base (by 1 after
  line 9, by 3 from the end of its module docstring on, against #92). Your target needs
  neither new lemma.
- **MIG-1 stage S (built, not yet a PR) is not in your base.** It edits modules in your import
  closure: `Simulation`, `Composition`, `Build/Wrappers`, `Encoding`, `Build/Loop` and
  `Build/Catalog` (with `ClassP/TimeConstructible` and `Build/Primitives`, outside it). It makes
  private witnesses public under new names (`audits/evidence/mig1/gate/scripts/renames.json`:
  for example `loopHost` → `loopHostTM`, `emCallTM` → `callTM`, `catalogPrefixTM` → `prependTM`,
  `counterTM` → `FinTM.lengthBitsTM`) and moves `Turing.FinTM.rewind_heads` and
  `rewind_scan_heads` from `Build/Catalog` to `Simulation` (same names). It is invisible to your
  base; the maintainer rebases at integration. **Cite no private name of those files**, and keep
  your new privates under the `sc_` prefix, so no name of yours meets one of S's. None of the
  publics this brief cites changes its name or statement at S.
- **Record-table row 18 is proved on PR #95** (branch `lean/rt5-row18`, open, not in your base):
  `Turing.exists_recordInitTM`, statement unchanged, in `Build/RecordTable.lean`. That file is not
  in your import closure, but it is in your order list (it is upstream of `Build/WindowRun`, which
  is downstream of you). At your base it is still sorried: your order list and base sorry set are
  those of the tip, and **#95 removes one sorry from the set when it lands**
  (`Build/RecordTable` 5 → 4).
- **Later, also outside your base:** the C1-A assembly gate (round 2) adds the public
  `Turing.embedSilentCfg_cap` to `Build/Embed.lean` (in your closure). Your route uses only the
  forwarding embedding, so nothing in it depends on that addition.

## Parallel batches this round (disjoint files; never edit another batch's)

| Batch | Brief | Owns |
|---|---|---|
| B6-F1, the step clock | `briefs/b6-fill-stepclock.md` (this brief) | `TuringMachine/Build/StepClock.lean`: the regions of ground rule 1 |
| B6-F2, the windowed runner | `briefs/b6-fill-windowrun.md` | `TuringMachine/Build/WindowRun.lean` (downstream of yours) |

Other work in flight owns other files: PR #95 (row 18, `Build/RecordTable.lean`, upstream of B6-F2,
not of you) and MIG-1 stage S, both above. B6-F2 cites your target by its frozen statement only. A parallel batch's work is invisible to your base and
your screen.

## What this is

**H3's clock, the step-clocked runner, stated once for B6 and C1** (C1 decision 4, "one step clock
shared with B6"; the B6 hosts gate, round 1, PASS, `audits/b6-hosts-statements-findings.md`, note
N3: "No findings in the formal contract or the constants … Keep both `+2` bounds"). Your target is
`Turing.exists_stepClockTMVia`: a host on one more tape that runs a body machine under a binary
countdown that ticks once per **physical** body step, with exit families `finish` (the body
stopped: halted, or reached a designated stop state) and `timeout` (the countdown ran out), exact
endpoints, no earlier exit, a counter frame (`Turing.wordPatch`) and an all-times trajectory
clause. It is the first batch of the B6 fill plan (`audits/evidence/b6-fill/B6-fill-plan.md`),
at the head of the chain to `Complexity.space_hierarchy`: the windowed runner
(`Turing.exists_windowRunnerTM`, batch B6-F2) is the loop under this clock, and the
configuration-count runner (`Turing.exists_configWindowRunnerTM`, batch B6-F3) uses that runner
by Route A, the route the gate's ruling assigns once the shared clock is filled.

**It also serves C1.** C1's diagonalizer caps and the exhaustive decider `E`'s replays cite
`Turing.exists_stepClockTM`, the `Bool` instance in C1's draft form, which the file already proves
from your target (`Build/StepClock.lean:177`, frozen); their modules name the clock in their
docstrings (`ClassNP/ExhaustiveReplay.lean:52`, `Diagonalization/NTimeHierarchy.lean:293`).

**Proved-modulo set: empty.** A complete delivery has no `sorryAx` in `exists_stepClockTMVia`,
and therefore none in `exists_stepClockTM`.

**Read first:** the target's docstring, whose proof sketch is binding; the module docstring;
the gate's findings on the clock (note N3, the ruling on brief point 1, the step-clock
paragraph after the adversarial table, and the suggested sanity lemmas in "Landing and fill
disposition"); the design note `audits/evidence/b6hosts/B6-hosts-design.md` §2.2 and §5;
`Build/CounterLoop.lean` lines 1–124 (the module docstring), 566–700 (the counter-loop host and
its layout) and 799–1232 (the private counter-loop debit, body phase and round induction, **the
pattern you follow and must not copy**); `Build/Contract/Basic.lean`'s segment layer (lines
387–600); the pre-ship overlay below.

**Pre-ship check (maintainer, at `c52663f1`, against #94's replay snapshot;
`audits/logs/b6-fill-stepclock-preship.log`):**
- `audits/evidence/b6-fill-stepclock/B6F1ImportProbe.lean.txt`: every public declaration this
  brief cites, and every one its pitfalls and prohibitions name, resolves in your file's import
  context. 0 errors, 0 warnings. **Re-run it after your delivery.**
- `audits/evidence/b6-fill-stepclock/StepClockOverlay.lean.txt`, generated by
  `tools/mkoverlay.py` from `tools/home.lean.txt` and `tools/headline.lean.txt`, every edit
  asserted and the reverse edit checked byte for byte. It is `StepClock.lean` with the home block
  inserted at the home and the headline's `sorry` replaced by the prescribed glue. Elaborated:
  **0 errors, 0 non-sorry warnings, 3 sorry warnings**, exactly the three stubs `sc_debit`,
  `sc_finish` and `sc_timeout`. It shows the following:
  - the suggested control `sc_State` (with its derived `DecidableEq` and its `Fintype`), the
    landing maps and the fused machine `sc_clockTM` elaborate;
  - six prescribed lemmas are **proved** there: `sc_decExit_injective`, `sc_agree`, `sc_layout`,
    `sc_lastLayout`, `sc_stop_step` and `sc_body_step` (standard axioms only);
  - the headline is proved from the two stubs `sc_finish` and `sc_timeout` by the glue, and the
    frozen `exists_stepClockTM` still follows from it.
- `tools/mkchecks.py` appends `tools/checks.lean.txt`: a **fit check** that `sc_debit`
  instantiates at the fused clock with `ρ := sc_decExit s` and the hypothesis `sc_agree`, a
  computation check of the redirection, and the axiom prints. 0 errors; `sorryAx` appears
  exactly in the three stubs, the headline and `exists_stepClockTM`.

## Owned region and target (modify these and nothing else)

| # | File:line | Target | Route | Uses |
|---|---|---|---|---|
| 1 | `TuringMachine/Build/StepClock.lean:115` | `Turing.exists_stepClockTMVia` | the docstring's sketch: one decrement fused with every body transition; concretely, the route below | the C1 decrement, R1, the symbol lift, counter arithmetic, the segment layer |

- **(a) The home:** the blank line **81**, between the end of `Turing.Cfg.Stopped` (line 80) and
  the target's docstring (line 82). Insert the prescribed block there first (`tools/home.lean.txt`,
  in its order); your own new `private` declarations go in the same home, each after what it uses
  and before its first consumer, never between a docstring and its declaration. Add no `section`,
  `open` or `variable` that leaks past it.
- **(b) The target's docstring,** lines 82–114. The text does not change. Append a flagged
  **"Fill appendix (B6-F1)"** paragraph before the closing ` -/` on line 114, recording where
  your proof refines the sketch (the generic debit, the segment composition, the constant
  ledger).
- **(c) The target's body,** the `sorry` on line 167. The statement, lines 115–166, is frozen.
- **(d) Status text:** the module docstring's "Status" paragraph (lines 23–26) and the
  "Main results" entry for your target (line 51, "(sorried)"), each to "proved", flagged, for a
  complete delivery only.
- **Frozen in your file:** the header and module docstring apart from (d) (lines 1–61); the
  layout definitions `Turing.clockCfg` (line 68), `Turing.wordPatch` (line 74) and
  `Turing.Cfg.Stopped` (line 78), statements, bodies and docstrings; the target's statement; and
  **`Turing.exists_stepClockTM` (lines 169–216, C1's form), byte-identical**: docstring,
  statement and proof.
- **Not yours:** every other file, including `Build/CounterLoop.lean`, `Build/Embed.lean`,
  `SymbolLift.lean`, `StateRenaming.lean`, `Build/Contract/*`, the downstream
  `Build/WindowRun.lean` and `SpaceComplexity/WindowClock.lean`, C1's
  `ClassNP/ExhaustiveReplay.lean` and `Diagonalization/NTimeHierarchy.lean`, the colleague-owned
  `TimeHierarchy/ClockMachine.lean` and `ClockLoop.lean`, and the facades.

### Prescribed home declarations (binding where marked; elaborated in the overlay)

Take the block from `tools/home.lean.txt`. Replace its "(Suggested.)", "(Prescribed, proved.)"
and "(Recommended shape; …)" tags by ordinary docstring prose.

| Declaration | Status in the overlay | Role |
|---|---|---|
| `sc_State` (inductive, `deriving DecidableEq`), `sc_State_fintype` | suggested | the control: `dec s f` (decrement phase `f`, body paused at `s`), `body s` (one pending body transition), `finish r`, `timeout r` |
| `sc_decExit` | suggested | the decrement's landing: `done true ↦ body s`, `done false ↦ timeout (some s)`, otherwise `dec s f` |
| `sc_decExit_injective` | **prescribed, proved** | the landing is an embedding |
| `sc_bodyAct` | suggested | a body action in the host: a live successor `s'` lands at `dec s' .run`, a halt at `finish none` |
| `sc_clockTM` | suggested | **the fused machine**: at `dec s .run` a stop state leaves at once for `finish (some s)`; otherwise the lifted, embedded decrement runs; `body s` makes one body transition |
| `sc_agree` | **prescribed, proved** | away from a stop state, the clock's decrement phases are the embedded lifted decrement renamed along `sc_decExit s` |
| `sc_layout` | **prescribed, proved** | `embedEmitCfg Fin.castSuccEmb (fun _ => ct) (fun _ => cp) [] c = clockCfg c.state c ct cp`, from the public `embedEmitCfg_eq` |
| `sc_lastLayout` | **prescribed, proved** | a one-tape configuration on the last tape by R1 along `lastEmb`, with the body as frame, is the clock layout |
| `sc_debit` | **stub, recommended statement** (a promotion candidate) | **the generic debit**: any host agreeing with the embedded lifted decrement along an embedding `ρ` runs one decrement on the last tape, with exact time `2·|takeWhile not w| + 2`, cut, counter patch, unchanged body part and counter-head interval |
| `sc_stop_step` | **prescribed, proved** | a stop state reaches `finish (some s)` in one step, nothing else changed |
| `sc_body_step` | **prescribed, proved** | one body transition from `body s`: the body's own step on the body tapes, landing at the successor's `dec _ .run` or at `finish none` |
| `sc_finish`, `sc_timeout` | **stubs, binding statements** | the target's two clauses for `sc_clockTM`, word for word |

**The target's body is the prescribed glue** (`tools/headline.lean.txt`; take it verbatim): the
witness `sc_State S`, `sc_clockTM e M stopAt`, `inj s := .dec s .run`, `finish := .finish`,
`timeout := .timeout`; the four distinctness clauses by constructor injectivity and
`noConfusion`; the two clauses from `sc_finish` and `sc_timeout`.

You may replace the suggested machine (and with it the stubs' statements, which mention it) by
your own fused controller, if you keep the glue's shape; say why in `REPORT.md`. The statement of
`sc_debit` is a recommendation: you may restate it (keep it generic in the host and the
embedding), but then give your statement in `REPORT.md`. If a prescribed statement turns out false
or unusable, that is an escalation (ground rule 4): record the obstruction and continue.

### Hosts (binding; the host-first rule, `policy.md` §1, `workflow.md` §2)

- **The step clock is the host** (registry row H3, its clock; design §14). Its machine is the
  fused controller above. It is not built from `Turing.counterLoopTMVia`: that host returns to one
  fixed anchor every round, so a body's state does not survive between rounds (C1 design §3.3,
  `audits/evidence/c1/C1-design.md`). Write **no other host**: no second loop, no runner, no
  private phase host.
- **Its phases are public rows and transformers only:** the one-tape decrement
  `Turing.decrementTM 1 0` with its framed contracts `Turing.decrementTM_run_succ_ofCfg` and
  `Turing.decrementTM_run_underflow_ofCfg`; the symbol lift `Turing.MultiTapeTM.liftSymbols`
  with its overlay transport `Turing.MultiTapeTM.liftSymbols_runFrom_over`; R1, the forwarding
  embedding `Turing.embedEmitTM`, along `Turing.lastEmb` for the counter and `Fin.castSuccEmb`
  for the body, with `Turing.embedEmitTM_runFrom`, `Turing.embedEmitTM_frame`; and the guarded
  state transport `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`. This is exactly the phase
  structure of `counterLoopTMVia` (`Build/CounterLoop.lean:624`), with the body state carried in
  the control.
- **Counter arithmetic is cited, never re-proved:** `Turing.counterWord`,
  `Turing.counterWord_length`, `Turing.counterWord_value`, `Turing.counterOverhead`,
  `Turing.counterOverhead_le_of_le` (the first `r ≤ value` decrements cost at most `4r + 2|w|`)
  and `Turing.counterOverhead_le` (counting down through the final underflow costs at most
  `4d + 2|w| + 2`), and `Turing.decFixed`.
- **Composition is MIG-0b's segment layer** (`Build/Contract/Basic.lean`): a round of the clock
  (one decrement and one body transition) is a `Turing.Segment` against the exit set; rounds join
  by `Turing.Segment.trans`, with `Segment.take`, `Segment.drop`, `Segment.live` and
  `Segment.time_eq` for the cut and the frame clause. The private `counterSpan` of `CounterLoop`
  is a segment by MIG-0b's own account; do not write a second span structure. The round layer
  (`Turing.Round`, `Turing.Round.iterate`) needs one fixed anchor and does not fit (the anchors
  `dec s .run` vary with `s`); MIG-0b's macro-step lockstep (`Turing.Lockstep`) needs an
  encoding that is a function of the body configuration, which the counter word is not. Say so
  in the Fill appendix if you use neither.
- **Layouts:** cite `Turing.embedEmitCfg_eq` (the R1 reconstruction lemma), through the
  prescribed `sc_layout` and `sc_lastLayout`; write no other layout lemma (`counter_layout` and
  the public `Turing.counterLoopCfg_body` are the family's seventh member, the prescribed two its
  eighth and ninth).

### The route (binding where it names a row)

1. **The generic debit** (`sc_debit`). Follow the proof shape of the private `counter_debit`
   (`Build/CounterLoop.lean:799`), with the host `H` and the embedding `ρ` in place of
   `counterLoopTMVia` and its decrement redirection, but do not copy its text: decode the
   one-tape start (`Turing.Cfg.decodeSymbols`, `Turing.Cfg.liftOver_decodeSymbols`), apply the
   decrement's success or underflow contract to the shadow, lift by
   `Turing.MultiTapeTM.liftSymbols_runFrom_over` (the decrement ignores its input and writes no
   blank), place on the last tape by `Turing.embedEmitTM_runFrom` along `Turing.lastEmb` and
   read the layout back by `sc_lastLayout`, and transfer to `H` by
   `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn` with `ρ` and the guard "not at a `done`
   phase". On underflow the cost is `2|w| + 2`, which is `2·|takeWhile not w| + 2` because `w`
   is all `false`.
2. **One round.** From `clockCfg (some (.dec s .run)) c ct cp` with `c` live at `s`, `stopAt s =
   false` and counter word `u = counterWord w r` of positive value: `sc_debit` at
   `ρ := ⟨sc_decExit s, sc_decExit_injective s⟩` (hypothesis `sc_agree … s hs`) reaches
   `body s` with the counter patched to `counterWord w (r + 1)`; then `sc_body_step` lands at
   `dec s' .run` with `M.step c` (or at `finish none` when `M.step c` halts). The round costs
   `2·|takeWhile not u| + 3`. A stop state costs one step (`sc_stop_step`).
3. **The rounds.** Induct on the body time: after `r` rounds, `r ≤ min τ d` (finish) or `r ≤ d`
   (timeout), the host is at `clockCfg (some (.dec (state of M.runFrom c r) .run)) (M.runFrom c
   r) (wordPatch ct cp ((counterWord w r).map e)) cp` at host time `counterOverhead w r + r`,
   with no exit before, the body part at some body time `≤ r` at every host time, and the
   counter head in `[cp - 1, cp + |w|]`. Use `counterWord_value` for the value and
   `counterWord_length` for the width; join rounds as segments.
4. **The two clauses.**
   - *Finish* (`sc_finish`). At the first stop `τ ≤ d`: either `M.runFrom c τ` is live at a stop
     state (one more step, `sc_stop_step`, to `finish (some _)`), or the `τ`-th body transition
     halted (it landed on `finish none` directly; `τ ≥ 1` since `c` is live). Time
     `counterOverhead w τ + τ (+ 1) ≤ 5τ + 2|w| + 1` by `counterOverhead_le_of_le` (as `τ ≤ d`).
     The counter word is `counterWord w τ`, of width `|w|`.
   - *Timeout* (`sc_timeout`). After `d` rounds the counter word is all `false`; `sc_debit`
     underflows to `timeout (some _)` with the counter all `true`. Time
     `counterOverhead w (d + 1) + d ≤ 5d + 2|w| + 2` by `counterOverhead_le`. Do not add a second
     `2|w|` to that whole bound (the gate's step-clock paragraph).
   - The trajectory clause: during round `r` the body part is `M.runFrom c r` (the debit changes
     no body cell, head, input head or output), and after its body transition `M.runFrom c (r +
     1)`; the counter head stays in the debit's interval and is untouched by a body transition.
5. **Package:** the prescribed glue. Then the sanity file (gate guidance).

- **Degenerate cases:** `k = 0` (no body tapes; `Fin.castSuccEmb : Fin 0 ↪ Fin 1`), `w = []`
  (value `0`, underflow at once in `2` steps, the patched word empty), an initial stop state
  (`τ = 0`, finish in one step, whatever `w`), a stop exactly at the budget (`τ = d`, by finish;
  the timeout premise includes time `d` and is false), and a zero-valued nonempty word
  (`w = [false, false]`: timeout within `6` steps, the counter left all `true`; the existential
  `w'` is essential).
- **Input convention:** the input head is the body's at every time; the decrement and the stop
  dispatch never move it.

### Phases (for a partial; ground rule 9)

Stop, if you must, at the end of a phase, and say which.
1. **The prescribed block and the glue landed** (the headline then has no `sorry` of its own; its
   `sorryAx` comes only through `sc_finish` and `sc_timeout`, which in turn may use `sc_debit`).
   For a partial the integration's freeze check is an **axiom walk**: `sorryAx` reaches the
   headline only through the named stubs.
2. **`sc_debit` proved.**
3. **The rounds** (step 3), as a private lemma.
4. **`sc_timeout` proved, then `sc_finish`:** the headline is complete.
5. **The sanity file.**

## Gate guidance (binding)

- **Keep both `+ 2` bounds** (the gate's ruling on brief point 1). The ledger above meets them
  with the stop check fused into the decrement's entry and a halting body transition landing on
  `finish none` directly; no extra dispatch step is needed for the clock.
- **Intercept every verdict:** a decrement's `done` anchors are redirected at once (`sc_decExit`),
  never run past.
- **No termination hypothesis:** the contract supplies the finite time in each clause.
- **The frame clause** holds at **every** host time up to the exit, including the debit's
  intermediate times (the gate strengthened it to carry the body tapes, the input position and the
  output; B6-F2's runner uses all of them for silence and restoration).
- **Sanity cases at fill** (the gate's suggested sanity lemmas). In an evidence file
  `B6F1Sanity.lean.txt` that imports `TCSlib.Complexity.TuringMachine.Build.StepClock` (not in the
  module), prove as `example`s from the public headline, for a concrete small body (for example a
  zero-tape machine on `Bool` with two states, one of them a stop state): (a) the empty word
  `w = []` times out within `2` steps; (b) an initial designated stop finishes within
  `2 · |w| + 2` steps, for `w = [true, false]`; (c) a body that first stops exactly at the
  budget (`τ = d = 1`, `w = [true]`) finishes; (d) at timeout the returned counter word has the
  original width and the counter head is back at `cp` (`w = [false, false]`). No `#eval`,
  `native_decide` or `IO`. Include the file and its elaboration log in the zip; a partial says
  "pending".
- **Note 46:** file size is not a driver; report the file's size.

## Cited infrastructure (public and proved at `70b503b49760b65817a3bce4b876dc466c32235c`; all in `B6F1ImportProbe.lean.txt`)

- **StepClock (yours, frozen):** `clockCfg`, `wordPatch`, `Cfg.Stopped`,
  `exists_stepClockTMVia`, `exists_stepClockTM`.
- **CounterLoop:** `decrementTM`, `decrementTM_run_succ_ofCfg`, `decrementTM_run_underflow_ofCfg`,
  `decFixed`, `counterWord`, `counterWord_length`, `counterWord_value`, `counterOverhead`,
  `counterOverhead_le_of_le`, `counterOverhead_le`, `lastEmb`; for orientation only (the pattern
  you follow, not to be cited in the proof): `counterLoopTMVia`, `counterLoopCfg`,
  `counterLoopCfg_body`, `counterLoopTMVia_run_done`, `counterLoopTMVia_run_escape`,
  `CounterLoopState`.
- **Catalog:** `FlagPhase` (`run`, `rewind`, `done`), `incrementTM`.
- **SymbolLift:** `MultiTapeTM.liftSymbols`, `MultiTapeTM.liftSymbols_runFrom`,
  `MultiTapeTM.liftSymbols_runFrom_over`, `Cfg.liftSymbols`, `Cfg.liftOver`, `Cfg.decodeSymbols`,
  `Cfg.liftOver_decodeSymbols`, `decodeBool`, `decodeBool_eq_some`, `FinTM.bufferTape_map`,
  `FinTM.bufferTape_map_decode`.
- **R1 (Embed):** `embedEmitTM`, `embedEmitCfg`, `embedEmitTM_tr`, `embedEmitTM_runFrom`,
  `embedEmitTM_frame`, `embedEmitCfg_eq`, `embedEmitCfg_selected_tape`,
  `embedEmitCfg_selected_pos`, `embedEmitCfg_unselected`.
- **State transport (StateRenaming):** `Action.mapState`, `Cfg.mapState`, `Cfg.mapState_apply`,
  `MultiTapeTM.runFrom_mapState_of_agreeOn`.
- **Segments (Contract/Basic):** `Segment`, `Segment.zero`, `Segment.one`, `Segment.cons`,
  `Segment.trans`, `Segment.take`, `Segment.drop`, `Segment.mono`, `Segment.live`,
  `Segment.time_eq`, `HeadBox`; named in the hosts paragraph: `Round`, `Round.iterate`,
  `Lockstep`.
- **Runs and configurations:** `MultiTapeTM.step`, `MultiTapeTM.runFrom`,
  `MultiTapeTM.runFrom_zero`, `MultiTapeTM.runFrom_add`, `MultiTapeTM.runFrom_succ_eq_step`,
  `MultiTapeTM.runFrom_succ_eq_step'`, `MultiTapeTM.step_of_halt`, `MultiTapeTM.runFrom_of_halt`,
  `MultiTapeTM.step_output`, `MultiTapeTM.outputSymbol`, `MultiTapeTM.outputSymbol_of_halt`,
  `MultiTapeTM.workTapePos_runFrom_mem_Icc`, `Action.apply`, `Cfg.ext`, `Cfg.inputSymbol`,
  `Cfg.workTapeSymbols`, `moveInputPos`, `FinTM.bufferTape`, `FinTM.bufferTape_left`,
  `FinTM.bufferTape_nat`.
- **Do not cite** anything downstream (`Build/WindowRun`, `SpaceComplexity`, C1's modules) or
  outside your import closure (`Build/Seam`, `Build/Contract/{Seam,Embed,Catalog,Lift}` are not
  imported; you need none of them).

## Ground rules (binding)

1. **File ownership, by region.** Only the four regions (a)–(d) of `Build/StepClock.lean`. List
   every new declaration with its role. A lemma that belongs in a shared file is written
   privately, flagged in `REPORT.md` as a promotion candidate, and promoted by the maintainer
   (`workflow.md` §4, rule 1).
2. **Statement freeze** over the target and every landed declaration: no renames,
   re-signatures, restatements or attribution edits. Docstrings stay; a flagged Fill appendix is
   expected wherever your proof refines the sketch.
3. **Status text:** only (d), flagged. **No new public declaration.** The named witness of B5's
   decision ("named machines at fill") is your private `sc_clockTM`; list it as a promotion
   candidate with the stub statements as its specification (the maintainer promotes it at
   integration, with its own gate if its statement goes public).
4. **Escalation** on anything unprovable as stated, including a prescribed statement or a cited
   row that does not compose as the route says: stop on that item, record the obstruction, and
   continue with the rest.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports.** Unchanged (`Build/CounterLoop` only). No TCSlib import may be added. A Mathlib
   import is allowed only if a needed lemma requires it; flag it.
7. **One proof per shared argument.** Never write a second decrement contract, lift transport,
   R1 transport, layout lemma, counter-arithmetic lemma or span structure. Never re-walk a
   decrement trace: the debit is the landed contracts transported.
8. **Size.** No cap; file size alone is not a driver. Report the file's final line count and its
   public and private declaration counts (base: 218 lines; 5 public, 0 private).
9. **Continuation budget.** If your budget runs out, deliver a partial zip whose `REPORT.md`
   states the phase reached, which `private` helpers remain `sorry` (each with a literal "Proof
   sketch"), and which proved declarations are proved modulo them. A partial is expected and
   fine; an unreported gap is not.
10. **The pinned base.** Cite only declarations that are public at `70b503b49760b65817a3bce4b876dc466c32235c`, and your file's
    own privates.
    - Do not rely on unfolding the body of any definition in `CounterLoop`, `Embed`, `SymbolLift`
      or `Contract/Basic`; use their public contracts. (Unfolding `Turing.decrementTM`'s table to
      show that it ignores its input and never writes a blank, as `liftSymbols_runFrom_over`
      requires, is the one exception; `counter_debit` does the same.)
    - Nothing that lands after your base is visible to you. If a lemma you want is "about to
      land", write it privately and flag it as a promotion candidate.
    - List every declaration you cite outside your file in `REPORT.md`. The import probe covers
      this brief's list; if you cite more, add them to a copy of the probe and run it.
11. **MIG-1 compatibility.** Cite none of the six R3 canonical rows (`copyTM_run`,
    `transferTM_run`, `clearTM_run`, `compareTM_run`, `incrementTM_run_succ`,
    `incrementTM_run_overflow`; MIG-1's last batch retires them) and no private declaration of
    `Simulation`, `Composition`, `Build/Wrappers`, `Encoding`, `Build/Loop` or `Build/Catalog`.

## Duplication governance (binding)

Run the text-level screen **before and after** (`audits/TEMPLATE.md` failure mode 5; `policy.md`,
**Duplication**). The population is **21 files**
(`audits/evidence/b6-fill-stepclock/screen-population.txt`): your file; the files this brief
cites (`CounterLoop`, `Catalog`, `SymbolLift`, `Build/Embed`, `StateRenaming`, `Contract/Basic`,
`Simulation`, `Deterministic`, `Configuration`, `Finite`); the known overlaps
(`Contract/Lift`, `Contract/Embed`, `InputCall`, `ClassNP/Nondeterminism`, and the
colleague-owned `TimeHierarchy/ClockMachine` and `ClockLoop`); and the consumers (`WindowRun`,
`WindowClock`, `ClassNP/ExhaustiveReplay`, `Diagonalization/NTimeHierarchy`).

**The screen labels files by basename**, so `Build/Embed.lean` and `Build/Contract/Embed.lean`
would share a label. Run it, unchanged, on byte-identical copies whose names encode the full path
(`/` becomes `__`), before and after:

```sh
bash audits/evidence/b6-fill-stepclock/tools/flat-screen.sh . \
  audits/evidence/b6-fill-stepclock/screen-population.txt "$(mktemp -d)" > screen-before.txt
```

The base, at `c52663f1`, is `audits/logs/b6-fill-stepclock-screen-base.txt`:
**907 declarations, 662 pairs, 187,245 characters** (MEASURED; about 3.5 minutes). Your
"before" must reproduce it after its header line. No base pair touches your file.

- **No new cross-file pair** with an owned-file declaration on one side, except the
  pre-disclosed ones below (measure each).
- **Pre-disclosed, measured on the pre-ship overlay** (the same population with the overlay as
  `StepClock.lean`; `audits/logs/b6-fill-stepclock-screen-overlay.txt`): 10 more declarations,
  2 more pairs (917 / 664 / 187,655). Both are cross-file, between the suggested machine
  `sc_clockTM` and `Turing.counterLoopTMVia` (`Build/CounterLoop.lean:624`):
  `counterLoopTMVia` reproduces `sc_clockTM` at 56%, and the reverse at 66%. They share the phase
  structure by design (the R1-embedded lifted decrement on the last tape, R1 along
  `Fin.castSuccEmb` for the body, the stationary exits), below 90%. No prescribed proof pairs
  with anything (a first version of `sc_layout` reproduced `counterLoopCfg_body`'s last-tape
  case split at 62% and was rewritten pre-ship). If you take the machine verbatim, report these
  two pairs as pre-disclosed; add nothing to them.
- **Known hazards:**
  - **the counter-loop debit, body phase and round induction** (`counter_debit`,
    `counter_body`, `counter_rounds`, `Build/CounterLoop.lean:799`, `:967`, `:1130`): your
    `sc_debit` and round lemma have their shape by design. Write them generic and in your own
    words; a pair with one of them is disclosed and measured, and at 90% or more it is a copy:
    factor it. **`sc_debit` is the requested shared lemma** that would retire `counter_debit`'s
    proof onto it (the maintainer's 12.2c window); flag it as such;
  - **the counter patch:** `Turing.wordPatch` (yours, frozen, public) has the same definition as
    `CounterLoop`'s private `counterPatch` (line 766); the screen does not pair them (the bodies
    differ in a variable name, below its tiling threshold), so this one is on you: add no
    third copy and no lemma about `wordPatch` that `counter_patch_twice` or `counter_patch_frame`
    already proves for its twin: if you need one, write it once, privately, as a promotion
    candidate;
  - the R1 layout family (`counter_layout`, `counterLoopCfg_body`, `embedEmitCfg_eq` and its
    corollaries in `Build/Embed`): cite the prescribed `sc_layout` and `sc_lastLayout`;
  - the redirection injectivity: `counter_dec_injective` (line 703) and the prescribed
    `sc_decExit_injective`;
  - the fused clocks elsewhere: Hydroxyi's `clockTM` (`TimeHierarchy/ClockMachine.lean:275`,
    colleague-owned, a `FinTM`-level fused runner from an initial configuration) and the private
    `choiceCore` replay of `ClassNP/Nondeterminism.lean:247`. Nothing is to be shared with
    either; never copy from them;
  - the lift and R1 contract adapters `Build/Contract/Lift` and `Build/Contract/Embed`: not in
    your closure; do not transcribe them.
- List every new in-file pair with a one-line justification. At 90% or more it is a copy: factor
  it.
- Quote both outputs in `REPORT.md`, which carries **"new copies: none"** (or lists each pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/b6-fill-stepclock.txt` (**207 modules**: the upstream
  closure of your owned file and of every module downstream of it, at the issue tree,
  topologically ordered, without the root `TCSlib`). Your file is module 139; its import closure
  has 21 modules (since #94 `CounterLoop` imports `CodeParser`); 4 modules are downstream of it
  (`Build/WindowRun`, `SpaceComplexity/WindowClock` and the two facades).

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/b6-fill-stepclock.txt )
  ```

  **Base sorry-warning set, 28** (`audits/logs/b6-fill-stepclock-base-sorries.txt`, one entry per
  declaration, 13 modules). Yours: `Build/StepClock` 1 (your target). Record the base list by name
  first, and report any difference. (When #95 lands, `Build/RecordTable` has 4; that is outside
  your base.)
- **Final checks:**
  1. `Build/StepClock`: zero errors and no sorry warning (for a partial: exactly the open stubs'),
     and no other warning in anything you added.
  2. Every module of the order list after your file (68 modules), re-checked against your final
     source, and every other module: zero errors, and sorry warnings exactly the base's minus
     yours (**27** in all for a complete delivery).
  3. Re-run `audits/evidence/b6-fill-stepclock/B6F1ImportProbe.lean.txt`: 0 errors. Elaborate
     `B6F1Sanity.lean.txt`: 0 errors.
- **Axiom prints** (in a scratch copy of your module with `#print axioms` appended, as the
  overlay's checks variant does) for the target, `exists_stepClockTM` and every new private:
  exactly `[propext, Classical.choice, Quot.sound]` or a subset, for a complete delivery.
- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`,
  0 FAIL (base: 0 FAIL, 11 WARN over 33 files; the pre-ship overlay gives the same); no new line
  over 100 characters.

## Out-of-scope sorries you will see (leave every one untouched)

- `TuringMachine/Build/RecordTable`: exists_tableFindTM, exists_tableAppendTM, exists_recordInitTM, exists_recordValidTM, exists_recordNextTM
- `TuringMachine/CodeSimulator`: exists_polyCanonizer, exists_uniformSimulator
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

- [ ] 1/1, or the phase reached (rule 9); the base hash (`git rev-parse HEAD` at branch
      creation, equal to `70b503b49760b65817a3bce4b876dc466c32235c`) and the ancestor check.
- [ ] Every new declaration with its role; the prescribed block as taken (any deviation, with
      its reason); the machine as suggested or your own; `sc_debit` as stated or restated. Every
      flagged appendix and status update.
- [ ] Promotion candidates (`sc_debit`, the generic debit; `sc_clockTM`, the named witness) and
      escalations, or "none".
- [ ] Rule 10: the list of declarations cited outside your file, and the probe re-run. Rule 11:
      a grep of your diff for the six R3 rows and the S-renamed privates.
- [ ] Duplication: both flattened screens, every new pair justified, "new copies: none".
- [ ] File size; the final sweep tail; the axiom prints; the lint line. The diff touches only
      your owned regions; `exists_stepClockTM` and the three layout definitions are
      byte-identical.
- [ ] The sanity cases, executed (or "pending" for a partial).
- [ ] For a partial: the headline's axiom walk, naming exactly the open stubs.

## Known pitfalls at this pin (hard-won)

- From the pre-ship probe, each of which failed a first run:
  - a dotted constructor needs its expected type: inside a `show … from rfl` or a `rw [show …]`,
    write `sc_State.body s`, not `.body s`;
  - after `rw [sc_layout] at h`, the two configurations in `h` and in the goal differ in their
    state field only, so `rw` of one into the other fails on `Cfg.inputSymbol` and
    `Cfg.workTapeSymbols`; split by `Cfg.ext` and close each field by
    `have h := congrArg Cfg.inputPos hE; exact h` (definitional, not syntactic, agreement);
  - `simp only [MultiTapeTM.step]` also unfolds the body's `M.step c` on the other side and
    then nothing matches: unfold the host's step alone, by `rw [show H.step d = (H.tr q …).apply d
    from rfl]`.
- `Cfg.inputPos : Fin (|input| + 2)` starts at `1`; compare positions by `.val`.
- A halted source has `M.step c = c` and `M.outputSymbol c = none` (`step_of_halt`,
  `outputSymbol_of_halt`). A live `c` with a halting transition has `(M.step c).state = none`;
  the clock then lands on `finish none` with `M.step c`'s tapes and output (the halting step's
  emission is forwarded by R1).
- `decrementTM` is `incrementTM` conjugated by complement; its phases are `FlagPhase.run`,
  `.rewind b` and `.done b`, and the `done` anchors are stationary in the source table but are
  redirected by `sc_decExit` in the host. `runFrom_mapState_of_agreeOn`'s guard must exclude the
  `done` phases before the last step.
- `Turing.counterWord` freezes at value zero while the machine wraps: `counterOverhead` is the
  physical cost only for `r ≤ value + 1` (its docstring).
- `Fin.castSuccEmb i = i.castSucc` (`Fin.coe_castSuccEmb`); `Fin.lastCases` splits a host tape
  index into the last tape and the body tapes (`Fin.lastCases_last`, `Fin.lastCases_castSucc`).
- `omega` with products and powers as atoms (`ring` first to expose them). The linter needs a
  literal "Proof sketch" before every `sorry` (partial only).
- MIG-0b moved `MultiTapeTM.runFrom_mapState_of_agreeOn` to `StateRenaming` and
  `MultiTapeTM.spaceUsedByTape_le_card_Icc` to `Finite`; the names are unchanged.
