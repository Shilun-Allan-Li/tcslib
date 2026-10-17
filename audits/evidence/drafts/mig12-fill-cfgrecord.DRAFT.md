# Ch3–4 migration — MIG-12: `Build/CfgRecord` onto the contract layer (a swap: every public statement frozen)

> **DRAFT (maintainer, 2026-10-16/17). Not issued.** Measured at MIG-12's API head `9872634e`,
> and its probe at #118's round-2 head `4624fc05` (which contains MIG-12's API). It issues with
> the five briefs after #118 merges (user, 2026-10-17); ⟨…⟩ are filled then.

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
  - **the API PRs** (the user's "Everything" rule, 2026-10-16): the specification API (#112: the
    contracts' and combinators' field equations, the layout facts), the core API (#116), the
    brief-inventory API (#118: `segment_iff`, `headBox_iff`, `round_iff`, `Cfg.bindState`'s
    fields), and **MIG-12's API** (#118's round 2: `Cfg.liftSymbols`'s and
    `Action.liftSymbols`'s fields, `incFixed`'s cases, `incFixed_length`, `decFixed_length`);
  - **the design note** `audits/evidence/mig12/DESIGN.md` (its Phase 1 is this brief);
  - the fill-agent environment addendum `briefs/fill-environment-addendum.md`, and the
    declaration-keyed copy-text screen v3 `audits/evidence/retrofit/copy-text-screen-v3.py`;
  - **this round's inputs** (`audits/evidence/mig12-fill/`): the import probe, the inventory of
    `RecordRun`'s uses, the unfolding sites, the frozen public list, and the screen population.
    Also the order list `briefs/orders/mig12-fill-cfgrecord.txt`, the base sorry set, the screen
    base and the pre-ship log (`audits/logs/mig12-fill-*`).
- If Lean cannot start, follow `briefs/fill-environment-addendum.md` exactly.
- **Branch at exactly that commit, not at the campaign tip:**

  ```sh
  git checkout -b fill/mig12-cfgrecord @ANCESTOR@
  git rev-parse HEAD        # must print @ANCESTOR@
  ```

  Record that hash as your base in `REPORT.md`. Never rebase, merge or cherry-pick.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-mig12-cfgrecord.zip`. It
  contains:
  - `REPORT.md` and the full modified source;
  - a `git format-patch` series against your base, and a git bundle whose only prerequisite is
    your base;
  - the bootstrap and final sweep logs, the freeze log and the axiom log;
  - both screen outputs, and `SHA256SUMS`.

## Base, line numbers and what lands around you

- **Your base's Lean content is the campaign tip after #118** (⟨BASE-LEAN⟩). The inputs
  commit adds no Lean change. Lines in this brief are those of that tree. `Build/CfgRecord.lean`
  has 5,302 lines and 119 declarations (21 public, 98 private), **and no admission**.
- **In flight, merging after your base and invisible to it:** U2-S (`UniversalK`), B6 F5
  (`Build/InputDevice`), the B6 F3 continuation (`SpaceComplexity/WindowClock`, which cites
  `CfgRecord`'s public statements only), the canonizer's continuation 6 (`CodeSimulator`), G4's
  continuation (`Build/ZoneRebalance`), and MIG-1's batches. Cite nothing they add.

## What this is

**MIG-12 of the machine library's migration** (`machine-library-design.md` §16; `backlog.md` §2,
the MIG table): **rebase `Build/CfgRecord` onto the contract layer, keeping every public
statement.** The user scheduled the MIG items between the fills, starting with MIG-12
(2026-10-16).
- `CfgRecord` composes its three public record rows (`exists_recordStepTM`, `exists_recordEqTM`,
  `exists_recordTestTM`) by hand: framed rows destructured from their `_run_ofCfg` theorems, the
  phase host's `phaseHostTM_run`, and a private run-segment bookkeeping, `RecordRun`.
- **`RecordRun` is exactly a `Segment`** (`Build/Contract/Basic`, design note): the run reaches
  `b` in `t` steps, no earlier state is either verdict anchor, and every head stays within a
  radius of a base vector. With `F := {some yes, some no}` and the head relation
  `HeadBox (base - radius) (base + radius)`, `RecordRun R yes no base radius a b t` is
  `Segment R F (HeadBox …) a b t` (`segment_iff`, `headBox_iff`, `abs_le`).
- **The swap:** `RecordRun` and its kit retire onto `Segment`, and each phase lemma becomes a
  composition of the row contracts. The rows are read through their field equations, never by
  destructuring a run theorem. Every other file's definition is read through its published
  lemmas (ground rule 10).
- **Estimate** (design §16, ESTIMATED): −1.6k to −2.1k lines.
- **No public statement changes.** The gate is a **swap gate**: a freeze check, the replay of
  `CfgRecord`'s downstream closure (52 modules), and a fidelity gate.

**Read first:**
- the design note `audits/evidence/mig12/DESIGN.md`;
- `Build/Contract/Basic.lean`: `Contract`, `Contract.segment`, `Contract.ofSegment`, the segment
  layer, `HeadBox`, and the combinators `seq`, `trans`, `inPhase`, `branch` with their field
  equations;
- the row contracts and their field equations (`Build/Contract/Catalog`, `Build/Contract/Counter`);
- `CfgRecord.lean` in full, in particular `RecordRun` (line 396) and its kit, `recordStepMachine`
  (the phase host), and the three public rows.

**Pre-ship check** (maintainer, at the base, against `oleans-lbapi3`, #118's round-2 replay;
`audits/logs/mig12-fill-preship.log`):
- **The inventory** (`audits/evidence/mig12-fill/`): every external definition `CfgRecord` uses
  (68), crossed with its 44 unfolding sites. With MIG-12's API every one has a published lemma, is
  a primitive of the machine model, or is a structure field.
- **The import overlay** (`audits/evidence/mig12-fill/CfgRecordOverlay.lean.txt`): your file with
  the authorized import. 0 errors, 0 warnings.
- **The import probe** (`MIG12ImportProbe.lean.txt`, 219 `#check`s): every public declaration
  this brief cites resolves from `CfgRecord`'s import context. 0 errors, 0 warnings. **Re-run it
  after your delivery.**

## Owned region and targets

| # | What | Status |
|---|---|---|
| 1 | Every **private** declaration of `Build/CfgRecord.lean` (98) | yours: restate, replace, merge or delete |
| 2 | The **bodies** of the 21 public declarations (the three rows and the layout facts) | yours; statements frozen |
| 3 | `RecordRun` and its kit (`recordRun_zero`, `recordRun_trans`, `recordRun_tagged`, …) | **retired**: none remains at a complete delivery |

- **The statements of all 21 public declarations are frozen** (`audits/evidence/mig12-fill/frozen-publics.txt`).
  Their docstrings are frozen too, except a flagged **"Migration appendix (MIG-12)"** paragraph
  you may append to each of the three rows' docstrings.
- **Not yours:** the module header (the maintainer updates its status text), every other file,
  and every import (ground rule 6).
- `private` only for new declarations. No `section`, `open` or `variable` that leaks.

### The route (binding where it names a layer; otherwise recommended)

**Phase 1, the segment layer (mechanical).**
- Replace each `RecordRun R yes no base radius a b t` by
  `Segment R {some yes, some no} (HeadBox (fun j => base j - radius) (fun j => base j + radius)) a b t`,
  or by a private abbreviation of exactly that, **stated once** (`private abbrev RecordSeg …`).
  The cut's conjunction is membership in the two-point set; the radius bound is the box by
  `abs_le`.
- `recordRun_zero` becomes `Segment.zero`; `recordRun_trans` becomes `Segment.trans`. A mono or
  weakening step is `Segment.mono`.
- `recordRun_tagged` (a phase-host prefix and dispatch as a segment) becomes the phase's contract
  in the host (Phase 2), or a statement over `Segment` proved from `phaseHostTM_run` once.
- Delete `RecordRun` and its kit when no use remains.

**Phase 2, the phases as contract compositions.** For each `recordStep_*` lemma (29 use
`RecordRun`; `audits/evidence/mig12-fill/recordrun-uses.tsv` lists them by size):
- **Read each row through its contract:** `C.segment` gives the row's run as a `Segment` in the
  `HeadBox` of its `lo`/`hi`, and `C.post`'s field equations give the endpoint. Do not
  destructure `_run_ofCfg` for a row that has a contract.
- **Inside the host** (`recordStepMachine` is one `phaseHostTM`): either `Contract.inPhase`, whose
  endpoint is a `Cfg.bindState` (read it by `Cfg.bindState_*`), or `phaseHostTM_run` once per
  phase. Lift the row's segment into the host's states by `Cfg.mapState` and exclude the host's
  verdicts by their stage indices (`record_tag_ne` stays).
- **Sequences** by `Segment.trans` (same machine) or `Contract.seq`/`Contract.trans`.
- **Weaken** each composed segment to the phase lemma's box by `Segment.mono` and `headBox_iff`.
- **The counter-loop phase** (`counterLoopTM_run_escape`, 3 uses: `recordStep_probe_run`,
  `recordStep_save_run`, `recordStep_apply_run`) **stays on its run theorem**: its contract form
  is MIG-15. It is the one named exception.
- Work smallest first (`recordStep_halt_run`, `recordStep_state_run`, `recordStep_copyback_run`,
  …), and keep the file elaborating after each lemma.

**Phase 3, the three public rows** (`exists_recordStepTM`, `exists_recordEqTM`,
`exists_recordTestTM`): re-compose them over the new phase lemmas. Their statements are frozen
byte for byte.

**Phase 4, the remaining unfolding sites** (ground rule 10). The base's 44 sites
(`audits/evidence/mig12-fill/unfold-sites.tsv`) re-point to:

| Definition | Sites | Published lemmas |
|---|---|---|
| `fieldOffset`, `fieldsTape` | 14 | `fieldOffset_zero`, `fieldOffset_succ`, `fieldOffset_cons_succ`, `fieldsTape_*`, `joinFields_*` (#112) |
| `Cfg.liftSymbols` | 7 | `Cfg.liftSymbols_inputPos`/`_workTapes`/`_output` (MIG-12's API), `Cfg.liftSymbols_state`, `_workTapePos`, `_inputSymbol` |
| `FinTM.bufferTape` | 7 | the `FinTM.bufferTape_*` lemmas |
| `embedEmitCfg` | 5 | `embedEmitCfg_eq`, `_selected_tape`/`_pos`, `_unselected`, `_state`/`_inputPos`/`_output` (#116) |
| `decFixed`, `incFixed` | 5 | `decFixed_nil`/`_true_cons`/`_false_cons` (#118), `incFixed_nil`/`_false_cons`/`_true_cons` (MIG-12's API) |
| `Cfg.inputSymbol`, `Cfg.workTapeSymbols`, `moveInputPos` | 6 | `Cfg.inputSymbol_of_zero`/`_of_end`, `inputSymbolInner`, `Cfg.workTapeSymbols_eq` (#116), the `moveInputPos_*` lemmas |

The ledger's arithmetic (`record_digits_inj`, the counter values) may unfold your own file's
definitions.

### Phases (for a partial; ground rule 9)

The file has no admission at the base, so **every delivery is complete in itself:** it
elaborates with no `sorry`, and every public statement is unchanged. A partial stops at a phase
boundary, or after any whole lemma within Phase 2, and lists what remains:
1. **Phase 1:** `RecordRun` retired onto `Segment`.
2. **Phase 2:** the phase lemmas re-proved over the contracts (report which).
3. **Phase 3:** the three rows re-composed.
4. **Phase 4:** the unfolding sites re-pointed.

## Gate guidance (binding)

- **The MIG-0a gate's correction** (design §16, MIG-12's row): `Contract.seq` does not replace
  `RecordRun`, since it changes the machine and adds a dispatch step, and a segment's endpoint need
  not be a first exit. Use the segment layer for same-machine concatenation.
- **MIG-15 owns the counter loop's contract form.** Do not write one here.
- **The swap gate** checks: the freeze (every public statement byte-identical; `privstmt` over the
  publics), the replay of the 52-module closure with sorry counts equal to the base's, and the
  fidelity of the rewritten proofs to the design (contracts read through their fields, no hand
  trace, no unfolding).

## Cited infrastructure (public and proved at the issue commit; all in `MIG12ImportProbe.lean.txt`)

The probe's 219 names: the row contracts and their field equations; the combinators and their
field equations; the segment layer with `segment_iff`, `headBox_iff`; `phaseHostTM_run`,
`embedEmitTM_runFrom`, `embedEmitTM_frame`, `embedEmitCfg_*`; `MultiTapeTM.liftSymbols_runFrom`
and the lifts' fields; the counter loop's run theorems; the layout facts.

## Ground rules (binding)

1. **File ownership.** Only `Build/CfgRecord.lean`, as in the region table. List every new, changed
   and deleted declaration with its role.
2. **Statement freeze** over the 21 public declarations: no renames, re-signatures, restatements
   or attribution edits. Private declarations may change freely.
3. **No new public declaration.** A generic helper you would publish is a promotion candidate,
   in `REPORT.md`.
4. **Escalation** on anything unprovable as routed, including a row contract that does not
   compose as the route says: stop on that item, record the obstruction, keep the original proof
   for it, and continue with the rest.
5. **No touching other sorries.** None is in your file.
6. **Imports.** Add exactly `import TCSlib.Complexity.TuringMachine.Build.Contract` (the contract
   facade, for the row contracts and the segment layer) as your first edit. The base does not
   reach the contract layer, and the facade makes no cycle: its upstream closure (26 modules) does
   not contain your file. The pre-ship overlay elaborates with it. No other TCSlib import.
7. **One proof per shared argument.** Never write a second segment layer, phase host, seam,
   embedding transport or row trace. Compose the contracts.
8. **Size.** No cap; report the final line count and the public and private declaration counts
   (base: 5,302 lines; 21 public, 98 private).
9. **Continuation budget.** A partial zip states the phase reached, what remains, and that the file
   is admission-free. A partial is expected and fine; an unreported gap is not.
10. **No unfolding (user, 2026-10-16).**
    - **Never unfold a definition of another file.** Read every definition through its published
      lemmas (the four API PRs and the landed lemmas the probe lists).
    - **The machine model's primitives** (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
      `Cfg.mapState`) are read through their existing lemmas. Unfold `step` and `Action.apply` only
      for a leaf defined in your own file. `phaseHostTM`'s table is read through `phaseHostTM_run`.
    - Your own file's definitions may be unfolded.
    - If a fact you need about another file's definition has no published lemma, **stop on that
      item and escalate**, naming the lemma you need.
11. **MIG-1 compatibility.** Cite none of the six R3 canonical rows (`copyTM_run`, `transferTM_run`,
    `clearTM_run`, `compareTM_run`, `incrementTM_run_succ`, `incrementTM_run_overflow`); cite no
    private declaration of `Build/Catalog`.

## Duplication governance (binding)

Run the text-level screen **before and after**, **one run at a time, under `nice -n 10`**.
- **The population** (`audits/evidence/mig12-fill/screen-population.txt`): your file; the layers it
  composes (`Build/Contract/Basic`, `Build/Contract/Catalog`, `Build/Contract/Counter`,
  `Build/Contract/Seam`, `Build/Seam`, `Build/Catalog`, `Build/CounterLoop`, `Build/Embed`); and
  the siblings `Build/RecordTable` (MIG-13's) and `SpaceComplexity/WindowClock`.
- **The base** is `audits/logs/mig12-fill-screen-base.txt`: ⟨BASE-COUNTS⟩ (MEASURED).
- **A swap should remove pairs, not add them.** Every new pair with your file on one side is
  justified in `REPORT.md`; at 90% or more it is a copy, so factor it. Report the in-file pairs
  that the swap removed.

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/mig12-fill-cfgrecord.txt` (**279 modules**: the upstream
  closure of your file and of its 52 downstream modules, without the root `TCSlib`).
  **The base sorry-warning set has 83 entries in 21 modules**, none in your file.
- **Final checks:**
  1. `Build/CfgRecord`: zero errors, **no sorry warning**, no new warning.
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's
     (83).
  3. **The freeze:** a statement comparison of the 21 publics (`privstmt.py` or the repository's
     freeze script) shows none changed.
  4. Re-run `MIG12ImportProbe.lean.txt`: 0 errors.
- **Axiom prints** for the 21 publics and every new private: within
  `[propext, Classical.choice, Quot.sound]`.
- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`, 0 FAIL
  (base: 0 FAIL, 32 WARN over 37 files). No new line over 100 characters.

## REPORT.md checklist

- [ ] The phase reached; the base hash and the ancestor check.
- [ ] `RecordRun`'s retirement: each former use and its replacement.
- [ ] Each phase lemma: the row contracts it composes, and how the host's verdicts are excluded.
- [ ] The counter-loop exception: the three lemmas, unchanged in route.
- [ ] Phase 4: each unfolding site and the lemma it now cites.
- [ ] The freeze log (21 publics unchanged), the line count before and after.
- [ ] Rule 10 and 11 greps of your diff; the probe re-run.
- [ ] Duplication: both v3 screens, every new pair justified, the removed pairs.
- [ ] The final sweep tail; the axiom prints; the lint line.

## Known pitfalls at this pin (hard-won)

- **A `Contract`'s cut includes time `0`**, so a phase's entry is never one of its exits; a
  `Segment`'s cut is strict (`u < t`), so its endpoint may be anything.
- **`Contract.segment`'s relation is the contract's own box**; the phase lemma's box is the
  common radius about the phase's base. Weaken with `Segment.mono`.
- **`phaseHostTM_run`** gives the prefix up to `T` and the dispatch at `T + 1`; its `hguard` must
  hold strictly before `T`.
- **The copy row has no endpoint frame claim beyond its post**: `copyTM_contract_frames` gives
  the cells outside the destination interval.
- **The compare row's time is exact**: `2 · compareStop u v + 2` (MIG-11a). The old existential
  `compareTM_run_ofCfg` is its corollary.
- **The counter rows are indexed by `(w, v)`** with `fix w = some v`; their endpoints write
  `bufferTape v` on the word's interval, which holds exactly `v` because `incFixed` and `decFixed`
  keep the width (`incFixed_length`, `decFixed_length`).
- `omega` with products and powers as atoms (`ring` first).
