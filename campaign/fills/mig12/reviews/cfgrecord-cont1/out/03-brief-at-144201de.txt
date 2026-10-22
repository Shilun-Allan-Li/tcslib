# Ch3–4 migration — MIG-12, continuation 1: `Build/CfgRecord` onto the contract layer (a swap: every public statement frozen)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If it
  fails, **stop**. That commit contains:
  - **the contract layer** (`Build/Contract/Basic`, MIG-0a and MIG-0b): `Contract` with its
    combinators, the segment layer (`Segment`, `Segment.zero`/`one`/`trans`/`mono`/`take`/`drop`)
    and the round layer;
  - **the row contracts** (`Build/Contract/Catalog`, and MIG-11a's PR #117): every framed row
    `CfgRecord` composes, as a contract — `scanTM_contract`, `skipTM_contract`,
    `skipBackTM_contract`, `clearTM_contract`, `copyTM_contract`, `compareTM_contract`, and
    `Build/Contract/Counter`'s `incrementTM_contract` and `decrementTM_contract`;
  - **the API PRs** (the user's "Everything" rule, 2026-10-16): the specification API (#112), the
    core API (#116), the brief-inventory API (#118: `segment_iff`, `headBox_iff`, `round_iff`,
    `Cfg.bindState`'s fields), and **MIG-12's API** (#118's round 2: `Cfg.liftSymbols`'s and
    `Action.liftSymbols`'s fields, `incFixed`'s cases, `incFixed_length`, `decFixed_length`);
  - **the design note** `campaign/items/mig12/DESIGN.md`;
  - **the first round's records:** the brief `campaign/fills/mig12/briefs/mig12-fill-cfgrecord.md`
    (its route, ledger and pitfalls stand, as repeated below), the worker's report
    `campaign/fills/mig12/reviews/round1/REPORT.md` (its row-by-row table of the remaining
    unfolding sites), and the maintainer's review `campaign/fills/mig12/reviews/round1/REVIEW.md`;
  - the fill-agent environment addendum `campaign/standards/fill-environment-addendum.md`
    (**v2**: Part 1, the resources and the cache, applies on every host), and the
    declaration-keyed copy-text screen v3 `scripts/copy-text-screen-v3.py`;
  - **this round's inputs** (`campaign/fills/mig12/inputs/mig12-fill-cfgrecord-cont1/`): **the
    first round's two commits as patches** (`patches/0001-…`, `patches/0002-…`), the import probe,
    the inventory of `RecordRun`'s former uses, the unfolding ledger, the frozen public list, and
    the screen population. Also the order list
    `campaign/fills/mig12/orders/mig12-fill-cfgrecord-cont1.txt`, the base sorry set, the screen
    base and the pre-ship log (`campaign/fills/mig12/logs/mig12-fill-cfgrecord-cont1-*`).
- **Before anything else, run Part 1 of `campaign/standards/fill-environment-addendum.md`**: the
  preflight, with its stop rule (E-RES). The first round was killed for memory (exit 137 under an
  8 GiB limit) while checks overlapped: run **one Lean process at a time** for this file, which
  takes about 2.4 GB alone.
- **Branch at exactly that commit, not at the campaign tip, and apply the first round's two
  commits first:**

  ```sh
  git checkout -b fill/mig12-cfgrecord-cont1 @ANCESTOR@
  git rev-parse HEAD        # must print @ANCESTOR@
  P=campaign/fills/mig12/inputs/mig12-fill-cfgrecord-cont1/patches
  git am $P/0001-*.patch $P/0002-*.patch
  git rev-parse HEAD:TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean
  #   must print 1c9d198f…, the first round's verified head file
  ```

  Record the ancestor as your base in `REPORT.md`; your format-patch series and bundle are against
  it and include these two commits. `git am` of exactly these two patches is the one authorized
  history operation; otherwise never rebase, merge or cherry-pick.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-mig12-cfgrecord-cont1.zip`. It
  contains:
  - `REPORT.md` and the full modified source;
  - a `git format-patch` series against your base, and a git bundle whose only prerequisite is
    your base;
  - the bootstrap and final sweep logs, the freeze log and the axiom log;
  - both screen outputs, and `SHA256SUMS`.
- **Checkpoint zips.** The file has no admission, so every whole lemma you finish leaves a
  complete, landable state. After each group of lemmas (at least after each phase), commit and
  write `fill-mig12-cfgrecord-cont1-cp<N>.zip` with the same contents as of that commit (the
  final sweep may be `CfgRecord`'s own check), so that a lost workspace loses at most one group.
  Deliver the latest checkpoint zip if the session ends early.

## Base, line numbers and what lands around you

- **Your base's Lean content is the campaign tip after #124** (`dac6b3b0`, #124's merge). The
  inputs commit adds no Lean change. `Build/CfgRecord.lean` there is the first round's base
  (5,302 lines, unchanged since); **after the two patches it has 5,310 lines** (21 public,
  98 private), **no admission**, and `RecordRun` is gone. Line numbers in this brief and in the
  ledger are the base's, before the patches; find each site by its declaration. Every probe and
  measurement below was run on the patched tree, against the olean snapshot of #124's replay
  (`oleans-lseam2`).
- **In flight, merging after your base and invisible to it:** #129
  (`Diagonalization/NTimeHierarchy`), #130 (`TuringMachine/UniversalK`), #131
  (`TuringMachine/CodeSimulator`), #132 (`Build/Primitives`, `Simulation`), the ruler device's
  landing (`Build/InputDevice`), the B6 F3 continuation (`SpaceComplexity/WindowClock`, which
  cites `CfgRecord`'s public statements only), and the fills of `Build/InputWindow`,
  `Build/ZoneRebalance` and `ClassNP/ExhaustiveReplay`. Cite nothing they add.

## What this is

**MIG-12 of the machine library's migration** (`machine-library-design.md` §16; `backlog.md` §2,
the MIG table): **rebase `Build/CfgRecord` onto the contract layer, keeping every public
statement.**
- **The first round completed phase 1** (the review: correct, admission-free, freeze-clean):
  `RecordRun` and its kit retired onto `Segment`, as one private
  `abbrev RecordSeg := Segment R {some yes, some no} (HeadBox (base − r) (base + r))`, two
  box/radius bridges (`record_headBox_iff`, `record_headBox_mono`), a scalar reader
  `recordSeg_iff`, and the renamed tagged helper `recordStep_tagged_segment`; every
  `recordRun_zero`/`_trans`/`_mono` use replaced by `Segment.zero`/`.trans`/`.mono`; 5 of the
  ledger's 173 rows re-pointed. **By the user's ruling (2026-10-18) it does not land alone**: it
  is folded into this continuation as its first two commits, and your delivery lands it.
- **This round: phases 2–4.** The phase lemmas become compositions of the row contracts, read
  through their field equations (never by destructuring a run theorem), the remaining 168
  unfolding sites are re-pointed, and the three rows are re-composed. The review's measure: 29
  phase lemmas still destructure `_run_ofCfg`.
- **Estimate** (design §16, ESTIMATED): −1.6k to −2.1k lines for the whole migration (phase 1:
  +8).
- **No public statement changes.** The gate is a **swap gate**: a freeze check, the replay of
  `CfgRecord`'s downstream closure (52 modules), and a fidelity gate.

**Read first:**
- the design note `campaign/items/mig12/DESIGN.md`, and the first round's review, (c) and (g);
- `Build/Contract/Basic.lean`: `Contract`, `Contract.segment`, `Contract.ofSegment`, the segment
  layer, `HeadBox`, and the combinators `seq`, `trans`, `inPhase`, `branch` with their field
  equations;
- the row contracts and their field equations (`Build/Contract/Catalog`, `Build/Contract/Counter`);
- `CfgRecord.lean` in full after the patches: `RecordSeg` and its kit, `recordStepMachine` (the
  phase host), the phase lemmas, and the three public rows.

**Pre-ship check** (maintainer, on the patched tree, against `oleans-lseam2`;
`campaign/fills/mig12/logs/mig12-fill-cfgrecord-cont1-preship.log`):
- **The two patches** apply at the base with `git am` and give the head file `1c9d198f` (5,310
  lines), the blob the first round's review verified.
- **Your file** (patched) elaborates: 0 errors, **0 warnings**.
- **The import probe** (`MIG12ImportProbe.lean.txt`, the first round's 227 `#check`s, unchanged):
  every public declaration this brief cites resolves. 0 errors, 0 warnings. **Re-run it after
  your delivery.**
- **The inventory** (`unfold-sites.tsv`, 173 rows, #118's round-3 review; the first round
  re-pointed rows 407, 441, 444, 465 and 1579): every row has a published lemma to re-point to.

## Owned region and targets

| # | What | Status |
|---|---|---|
| 1 | Every **private** declaration of `Build/CfgRecord.lean` (98 after the patches) | yours: restate, replace, merge or delete |
| 2 | The **bodies** of the 21 public declarations (the three rows and the layout facts) | yours; statements frozen |
| 3 | The phase lemmas (`recordStep_*`), 29 still on `_run_ofCfg` | **this round's main work** |

- **The statements and docstrings of all 21 public declarations are frozen**
  (`frozen-publics.txt`). Three docstring mentions of the retired `RecordRun`/`recordRun_trans`
  (in `exists_recordStepTM` and `exists_recordEqTM`; the review's M2) are reworded by the
  maintainer at integration: **do not add an appendix** to any docstring.
- **Docstrings of your new or rewritten private declarations** are public-facing library text:
  what the lemma says and how it is proved, with no campaign labels (brief, gate, finding or
  round names), dates or narrative. Provenance goes in `REPORT.md`.
- **Not yours:** the module header (the maintainer updates its status text), every other file,
  and every import (ground rule 6).
- `private` only for new declarations. No `section`, `open` or `variable` that leaks.

### The route (binding where it names a layer; otherwise recommended)

**Phase 1** is the two patches: done. Keep `RecordSeg` stated once, and its readers.

**Phase 2, the phases as contract compositions, smallest first** (`recordrun-uses.tsv` lists the
29 by size: `recordStep_halt_run`, `recordStep_state_run`, `recordStep_copyback_run`, …). Keep the
file elaborating after each lemma.
- **Read each row through its contract:** `C.segment` gives the row's run as a `Segment` in the
  `HeadBox` of its `lo`/`hi`; weaken it into `RecordSeg` by `Segment.mono` with
  `record_headBox_mono`. `C.post`'s field equations give the endpoint. Do not destructure
  `_run_ofCfg` for a row that has a contract.
- **Inside the host** (`recordStepMachine` is one `phaseHostTM`): either `Contract.inPhase`, whose
  endpoint is a `Cfg.bindState` (read it by `Cfg.bindState_*`), or `phaseHostTM_run` once per
  phase. Lift the row's segment into the host's states by `Cfg.mapState` (read through
  `Cfg.mapState_*`) and exclude the host's verdicts by their stage indices (`record_tag_ne`
  stays).
- **Sequences** by `Segment.trans` (same machine) or `Contract.seq`/`Contract.trans`.
- **The counter-loop phase** (`counterLoopTM_run_escape`: one direct use in `recordStep_save_run`;
  through it `recordStep_save_transport`, `recordStep_prepare_native`, `recordStep_live_native`
  and `exists_recordStepTM`) **stays on its run theorem**: its contract form is MIG-15. It is the
  one named exception.

**Phase 4, the remaining unfolding sites, alongside phase 2** (ground rule 10). **The ledger
`unfold-sites.tsv` is the binding list**: 173 rows, explicit and definitional, each with the lemma
to re-point to; the first round's report gives the remaining 168 row by row. By definition
(explicit / definitional rows at the base):

| Definition | Rows | Published lemmas |
|---|---|---|
| `Cfg.mapState` | 21 / 26 | `Cfg.mapState_state`/`_inputPos`/`_workTapes`/`_workTapePos`/`_output` (#118, round 2) |
| `Cfg.liftSymbols` | 7 / 20 | `Cfg.liftSymbols_inputPos`/`_workTapes`/`_output` (#118's MIG-12 commit), `Cfg.liftSymbols_state`, `_workTapePos`, `_inputSymbol` |
| `MultiTapeTM.runFrom` | 0 / 16 | `runFrom_zero`, `runFrom_succ_eq_step`, `runFrom_succ_eq_step'`, `runFrom_add` |
| `fieldOffset`, `fieldsTape` | 15 / 7 | `fieldOffset_zero`, `fieldOffset_succ`, `fieldOffset_cons_succ`, `fieldsTape_*`, `joinFields_*` (#112) |
| `embedEmitCfg` | 5 / 12 | `embedEmitCfg_eq`, `_selected_tape`/`_pos`, `_unselected`, `_state`/`_inputPos`/`_output` (#116) |
| `FinTM.bufferTape` | 10 / 1 | the `FinTM.bufferTape_*` lemmas (`bufferTape_nat`, `bufferTape_left`, …) |
| `Action.apply`, `MultiTapeTM.step`, `MultiTapeTM.outputSymbol` | 3 / 6 | `Action.apply_state`/`_inputPos`/`_workTapePos`/`_output`, `Action.apply_workTapes`, `MultiTapeTM.step_of_some`, `outputSymbol_of_some` (#118, round 3) |
| `decFixed`, `incFixed` | 5 / 1 | `decFixed_nil`/`_true_cons`/`_false_cons`, `incFixed_nil`/`_false_cons`/`_true_cons` (#118) |
| `roundOrbit`, `counterLoopOrbit` | 4 / 3 | `roundOrbit_zero`, `roundOrbit_succ`; through the abbreviation by `exact` or `simp only`, not `rw` |
| `counterWord`, `scanFold`/`scanKeep` | 0 / 3 | `counterWord_succ`, `scanResult_keep_keep` (#118, round 3), `scanResult_fold` |
| `Cfg.inputSymbol`, `Cfg.workTapeSymbols`, `moveInputPos`, `Cfg.init` | 6 / 2 | `Cfg.inputSymbol_of_zero`/`_of_end`, `inputSymbolInner`, `Cfg.workTapeSymbols_eq`, `Cfg.init_*` (#116), the `moveInputPos_*` lemmas |

The ledger's arithmetic (`record_digits_inj`, the counter values) may unfold your own file's
definitions.
- **`exists_recordStepTM` reaches two privates of `Build/Embed`** (`embedSlot`,
  `embedActionCore.match_3`) through the legacy definitional reading of `embedEmitCfg` (the
  ledger's 17 `embedEmitCfg` rows; identical at the base). Re-pointing those rows to
  `embedEmitCfg_*` removes it: the row's axiom walk must then reach no other file's private.

**Phase 3, the three public rows, last** (`exists_recordStepTM`, `exists_recordEqTM`,
`exists_recordTestTM`): re-compose them over the new phase lemmas. Their statements are frozen
byte for byte. Report the line delta against the estimate.

### Phases (for a partial; ground rule 9)

The file has no admission, so **every delivery is complete in itself:** it elaborates with no
`sorry`, and every public statement is unchanged. A partial stops after any whole lemma, and
lists what remains:
1. **Phase 1:** done (the two patches).
2. **Phase 2:** the phase lemmas re-proved over the contracts (report which, of the 29).
3. **Phase 4:** the unfolding sites re-pointed (report which rows, of the 168).
4. **Phase 3:** the three rows re-composed.

## Gate guidance (binding)

- **The MIG-0a gate's correction** (design §16, MIG-12's row): `Contract.seq` does not replace the
  segment bookkeeping, since it changes the machine and adds a dispatch step, and a segment's
  endpoint need not be a first exit. Use the segment layer for same-machine concatenation.
- **MIG-15 owns the counter loop's contract form.** Do not write one here.
- **The swap gate** checks: the freeze (every public statement byte-identical; `privstmt` over the
  publics), the replay of the 52-module closure with sorry counts equal to the base's, and the
  fidelity of the rewritten proofs to the design (contracts read through their fields, no hand
  trace, no unfolding).

## Cited infrastructure (public and proved at the issue commit; all in `MIG12ImportProbe.lean.txt`)

The probe's 227 names: the row contracts and their field equations; the combinators and their
field equations; the segment layer with `segment_iff`, `headBox_iff`; `phaseHostTM_run`,
`embedEmitTM_runFrom`, `embedEmitTM_frame`, `embedEmitCfg_*`; `MultiTapeTM.liftSymbols_runFrom`
and the lifts' fields; the counter loop's run theorems; the layout facts; and #118's round 3:
`Action.apply_state`/`_inputPos`/`_workTapePos`/`_output`, `MultiTapeTM.step_of_some`,
`outputSymbol_of_some`, `counterWord_succ`, `scanResult_keep_keep`.

## Ground rules (binding)

1. **File ownership.** Only `Build/CfgRecord.lean`, as in the region table. List every new, changed
   and deleted declaration with its role.
2. **Statement freeze** over the 21 public declarations: no renames, re-signatures, restatements
   or attribution edits; their docstrings are frozen too. Private declarations may change freely.
3. **No new public declaration.** A generic helper you would publish is a promotion candidate,
   in `REPORT.md`.
4. **Escalation, item by item**, on anything unprovable as routed, including a row contract that
   does not compose as the route says: stop on that item only, record the obstruction
   mathematically, keep the original proof for it, and continue with every item that does not
   depend on it.
5. **No touching other sorries.** None is in your file.
6. **Imports.** Unchanged after the patches (the first patch adds the one authorized import,
   `TCSlib.Complexity.TuringMachine.Build.Contract`). No other TCSlib import.
7. **One proof per shared argument.** Never write a second segment layer, phase host, seam,
   embedding transport or row trace. Compose the contracts.
8. **Size.** No cap; report the final line count and the public and private declaration counts
   (after the patches: 5,310 lines; 21 public, 98 private).
9. **Continuation budget.** A partial zip states what was done, what remains, and that the file is
   admission-free. A partial is expected and fine; an unreported gap is not.
10. **No unfolding (user, 2026-10-16).**
    - **Never unfold a definition of another file.** Read every definition through its published
      lemmas (the four API PRs and the landed lemmas the probe lists). **No definitional closure
      either:** a `rfl`, `exact`, `show`, `change`, `decide` or `simp` step that closes only because
      another file's definition reduces counts as unfolding (the ledger's definitional rows).
    - **The machine model's primitives** (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
      `Cfg.mapState`) are read through their published lemmas: `step_of_some`/`step_of_halt`,
      `outputSymbol_of_some`/`_of_halt`, the `runFrom` equations, `Action.apply_*` (with
      `Action.apply_workTapes`) and `Cfg.mapState_*`. This holds for an arbitrary action or
      machine as well. Unfold `step` and `Action.apply` only for a leaf defined in your own
      file. `phaseHostTM`'s table is read through `phaseHostTM_run`.
    - Your own file's definitions may be unfolded.
    - If a fact you need about another file's definition has no published lemma, **stop on that
      item and escalate**, naming the lemma you need.
    - **Self-check by the review's seal comparison** (its (c)): for each ledger definition, a
      scratch copy of your module with `attribute [local irreducible]` on that definition; the
      first error per tactic block, mapped to its declaration, is a remaining site. At a complete
      delivery each definition's site set is empty. At the base the counts are `Cfg.mapState` 27,
      `MultiTapeTM.runFrom` 15, `Cfg.liftSymbols` 20, `embedEmitCfg` 12, `fieldOffset` 7,
      `Action.apply` 6, `roundOrbit` 3, and 1 each for `FinTM.bufferTape`, `Cfg.inputSymbol`,
      `incFixed`, `scanKeep`, `scanFold`, `counterWord` and `Cfg.init` (after the patches).
      Report your counts, and the explicit-site count (73 after the patches).
11. **MIG-1 compatibility.** Cite none of the six R3 canonical rows (`copyTM_run`, `transferTM_run`,
    `clearTM_run`, `compareTM_run`, `incrementTM_run_succ`, `incrementTM_run_overflow`); cite no
    private declaration of `Build/Catalog`.

## Duplication governance (binding)

Run the text-level screen **before and after**, **one run at a time, under `nice -n 10`**
(`campaign/standards/TEMPLATE.md` failure mode 5; `policy.md`, **Duplication**).
- **The population** (`screen-population.txt`, 12 files): your file; the layers it composes
  (`Build/Contract/Basic`, `Build/Contract/Catalog`, `Build/Contract/Counter`,
  `Build/Contract/Seam`, `Build/Seam`, `Build/Catalog`, `Build/CounterLoop`, `Build/Embed`); and
  the siblings `Build/RecordTable` (MIG-13's) and `SpaceComplexity/WindowClock`.
- **The base** (on the patched tree) is
  `campaign/fills/mig12/logs/mig12-fill-cfgrecord-cont1-screen-base.txt`:
  **870 declarations, 435 pairs, 131,544 characters** (MEASURED; about 9 minutes).
- **A swap should remove pairs, not add them.** Every new pair with your file on one side is
  justified in `REPORT.md`; at 90% or more it is a copy, so factor it. Report the in-file pairs
  that the swap removed.

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check, **one at a time** for this file.
- **Bootstrap once** from `campaign/fills/mig12/orders/mig12-fill-cfgrecord-cont1.txt`
  (**280 modules**: the upstream closure of your file and of its 51 downstream modules, without
  the root `TCSlib`), after applying the patches.
  **The base sorry-warning set has 83 entries in 21 modules**
  (`campaign/fills/mig12/logs/mig12-fill-cfgrecord-cont1-base-sorries.txt`), none in your file.
- **Final checks:**
  1. `Build/CfgRecord`: zero errors, **no sorry warning**, no new warning.
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's
     (83).
  3. **The freeze:** a statement comparison of the 21 publics (`privstmt.py` or the repository's
     freeze script) against the base shows none changed.
  4. Re-run `MIG12ImportProbe.lean.txt`: 0 errors.
- **Axiom prints** for the 21 publics and every new private: within
  `[propext, Classical.choice, Quot.sound]`, and no other file's private reached from the three
  rows.
- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`,
  0 FAIL (base: 0 FAIL, 30 WARN over 38 files). No new line over 100 characters.

## REPORT.md checklist

- [ ] The preflight's numbers (addendum v2, Part 1).
- [ ] The base hash, the ancestor check, and the two patches applied (the head file's blob).
- [ ] What was done: the phase lemmas re-proved (each with the row contracts it composes, and how
      the host's verdicts are excluded), the ledger rows re-pointed (each with its lemma, or why
      the row no longer exists), the rows re-composed; what remains.
- [ ] The counter-loop exception: `recordStep_save_run`'s one direct use, unchanged in route.
- [ ] The seal comparison's per-definition counts and the explicit-site count, before and after.
- [ ] The freeze log (21 publics unchanged), the line count before and after.
- [ ] Rule 10 and 11 greps of your diff; the probe re-run; the axiom walks of the three rows.
- [ ] Duplication: both v3 screens, every new pair justified, the removed pairs.
- [ ] The final sweep tail; the axiom prints; the lint line; the checkpoint zips written.

## Known pitfalls at this pin (hard-won)

- **A `Contract`'s cut includes time `0`**, so a phase's entry is never one of its exits; a
  `Segment`'s cut is strict (`u < t`), so its endpoint may be anything.
- **`Contract.segment`'s relation is the contract's own box**; the phase lemma's box is the
  common radius about the phase's base. Weaken with `Segment.mono` and `record_headBox_mono`.
- **`phaseHostTM_run`** gives the prefix up to `T` and the dispatch at `T + 1`; its `hguard` must
  hold strictly before `T`.
- **The copy row has no endpoint frame claim beyond its post**: `copyTM_contract_frames` gives
  the cells outside the destination interval.
- **The compare row's time is exact**: `2 · compareStop u v + 2` (MIG-11a). The old existential
  `compareTM_run_ofCfg` is its corollary.
- **The counter rows are indexed by `(w, v)`** with `fix w = some v`; their endpoints write
  `bufferTape v` on the word's interval, which holds exactly `v` because `incFixed` and `decFixed`
  keep the width (`incFixed_length`, `decFixed_length`).
- **The scalar conversions** back to the frozen clauses failed as rewrites in the first round's
  first attempt (four errors, kept in its sweep log); its final version applies
  `(recordSeg_iff …).mp` instead. Follow that.
- **Memory:** this file takes about 2.4 GB to elaborate; never run two checks of it at once.
- `omega` with products and powers as atoms (`ring` first).
