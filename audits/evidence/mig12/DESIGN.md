# MIG-12 (`Build/CfgRecord` onto the contract layer), with its part of MIG-11: design note

Maintainer, 2026-10-16, measured at the tip `607eb7d6` (Lean content `c451e358`). This note
records the user's schedule (2026-10-16: interleave MIG items with the fills, starting with
MIG-12; MIG-4 closed as done) and the inventory behind it. It is a draft for the statement
phase, not yet issued.

## What `CfgRecord` does today

- 5,272 lines; 16 public and 99 private declarations. The public rows are `exists_recordStepTM`,
  `exists_recordEqTM` and `exists_recordTestTM`, plus the layout (`RecordAt`, `posWidth`, …).
- **The private `RecordRun`** (line 366) is a run segment: endpoint, a cut against the two verdict
  anchors `yes`/`no`, and a common head radius about a base vector. It is exactly the MIG-0b
  segment, `Segment R {some yes, some no} (fun p => ∀ j, |p j - base j| ≤ radius) a b t`
  (`Build/Contract/Basic`, line 393). Its kit `recordRun_zero`/`_trans`/`_mono` is
  `Segment.zero`/`.trans`/`.mono`.
- **28 declarations, 3,152 lines, use `RecordRun`.** The bulk is the `recordStep_*` run lemmas:
  - `recordStep_apply_run` (546 lines), `recordStep_read_fields` (280), `recordStep_read_prefix`
    (224), `recordStep_position_run` (153);
  - the three public rows: `exists_recordEqTM` (355), `exists_recordTestTM` (296),
    `exists_recordStepTM` (170).

  They compose phases by hand: `phaseHostTM_run` (14 uses), the R3 framed rows' `_run_ofCfg`
  lemmas, and `Segment`-style bookkeeping through `RecordRun`.
- **The rows it composes:**

  | Row | Uses | Contract today |
  |---|---|---|
  | `scanTM` | 8 | `scanTM_contract` |
  | `skipTM` | 5 | `skipTM_contract` |
  | `skipBackTM` | 4 | `skipBackTM_contract` |
  | `clearTM` | 2 | `clearTM_contract` |
  | `copyTM` | 2 | **none** |
  | `compareTM` | 2 | **none** |
  | `incrementTM` (success) | 1 | **none** |
  | `decrementTM` (success) | 1 | **none** |
  | `counterLoopTM` (escape) | 3 | segment forms `counterLoopTMVia_escape_segment` (MIG-15's area) |
  | `embedEmitTM` | 1 | `Contract.embed` |
  | `phaseHostTM` | 14 | `Contract.inPhase` |

## Phase 0: MIG-11a, the four missing row contracts (a maintainer PR with a statement gate)

Each is a thin wrapper over the row's existing `_run_ofCfg` lemma, as `clearTM_contract` is over
`clearTM_run_ofCfg`. They are in `Build/Contract/Catalog`, beside the nine row contracts, and land
with their `simps` field equations (`policy.md` §1, *Definitions land with their lemmas*):
- **`copyTM_contract src dst hne x`:** `sweepContract` at the touched heads `src`, `dst`, as
  `copyMapTM_contract` at the identity map. Index: the source word.
- **`incrementTM_contract i x`** and **`decrementTM_contract i x`:** the success case. Index: the
  word `w`, with `incFixed w = some v` (resp. `decFixed`) in the precondition. Time
  `2 · |takeWhile id w| + 2` (resp. `not`). Exits `{some (done true), some (done false)}`,
  since the run lemma's cut excludes both flags. The overflow/underflow cases are added when a
  consumer needs them.
- **`compareTM_contract fst snd hne x`:** the run lemma's time is existential (`∃ δ ≤ min |u| |v|`).
  A contract needs it as a function, so a public definition is needed, with its lemmas: the
  common-prefix stop `compareStop u v`, the first index at which the two words do not both hold
  the same symbol. The private `catalog_compare_stop` already proves it unique. Index: the pair
  `(u, v)`. Exits: both verdicts.

**Gate:** statement gate (MIG-11's "stmt"). The bodies are thin, so the PR proves them, and the gate
is a statement-and-fidelity gate in one round.

## Phase 1: MIG-12 proper (a fill brief; swap gate)

- **Statements frozen.** The three public rows and every public layout fact keep their exact
  statements. The freeze check, the replay of `CfgRecord`'s closure, and a fidelity gate apply.
- **The route:**
  - `RecordRun` retires onto `Segment` (mechanical);
  - each `recordStep_*` phase becomes a contract composition (`Contract.inPhase` in the phase
    host, `Contract.seq`/`trans` for the sequences) over the row contracts;
  - the hand-composed runs through `phaseHostTM_run` and `_run_ofCfg` give way to the
    contracts' fields, read through the field equations (#112, MIG-11a).
- **The counter-loop phase** (3 uses of `counterLoopTM_run_escape`) stays on its run theorem,
  since its contract form is MIG-15. It is the one named exception.
- **Estimate** (design §16, ESTIMATED): −1.6k to −2.1k lines.
- **Dependencies:** #112 (the field equations of the nine row contracts and the combinators) and
  MIG-11a. #116 is not needed.
- **Consumers:** `CfgRecord`'s downstream closure (B6's window runner and clock, the record table,
  …) is measured at issue, and it is the replay list.

## Order

1. #112 round 2, merged.
2. MIG-11a: the PR, its gate, merged.
3. The MIG-12 brief, measured at the tip after MIG-11a and dispatched. It runs in parallel with the
   fills that do not touch `CfgRecord`. The F3 continuation (`WindowClock`) cites `CfgRecord`'s
   public facts only, so it is unaffected by a swap that keeps statements.
