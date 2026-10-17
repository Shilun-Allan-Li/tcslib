# External audit pack — the brief-inventory API, round 2 (PR #118)

Campaign: the Arora-Barak chapters 3-4 plan; the user's "Everything" rule (2026-10-16: every
definition a brief's route reads gets a published equation before the brief is dispatched,
`policy.md` §1, *Definitions land with their lemmas*).
- **Round 1** (`audits/brief-api-findings.md`) was FAIL, 0 blockers, 2 majors, 1 minor. Both
  majors were gaps in the canonizer continuation 6's inventory.
- **The resolutions** are in `audits/brief-api-resolutions.md`.
- **This round's head** is `lean/brief-api` at `4624fc05`. It has three commits on round 1's
  `4ae686be`:

| Commit | What | Why |
|---|---|---|
| `9872634e` | **MIG-12's API** (new in this round): `Action.liftSymbols`'s four fields and `Cfg.liftSymbols`'s input position, cells and output (`SymbolLift`, `simps`); `incFixed_nil`, `_false_cons`, `_true_cons`, `incFixed_length` (`Build/Convention`); `decFixed_length` (`Build/CounterLoop`) | MIG-12's pre-ship inventory (the rebase of `Build/CfgRecord` onto the contract layer; draft `audits/evidence/drafts/mig12-fill-cfgrecord.DRAFT.md`), and #117's gate review (the two widths). It was held for this gate rather than gated alone. |
| `88fb25f3` | `codeSkipRepeat_zero`, `codeSkipRepeat_succ` (`CodeParser`); the five field equations of `RoundContract.counterLoopDone` and `counterLoopEscape` (`Build/CounterLoop`, `simps!`) | round 1's findings 1 and 2 |
| `4624fc05` | `Action.mapState`'s four and `Cfg.mapState`'s five field equations (`StateRenaming`, `simps`) | N1, found by the review's re-run of the inventory with the round-1 method fix |

Every addition is a declaration, without `@[simp]`, with a docstring stating its formula.
- **Evidence:** `audits/evidence/brief-api/r2/`:
  - the review `gate-review.md`;
  - the patches;
  - the logs, probes and screens;
  - the seed-inclusive inventory (`probes/DefInventorySeeds.lean.part.txt`, reports
    `review-out/seedinv*`);
  - MIG-12's API evidence (`mig12-api/`, with its replay log).
- **The bundle** also contains:
  - the five briefs' drafts and MIG-12's draft;
  - the touched files and their consumers: `CodeSimulator` (cont6), `Build/CfgRecord` (MIG-12),
    `Build/Contract/Seam` (the private `mapState_state` the drafts cited), `Build/Seam` and
    `Build/Embed`.

## Brief for the auditor

1. **Round 1's findings.** Are findings 1–3 closed?
   - Finding 1: the two cases are exactly the definition's two equations.
   - Finding 2: the ten field equations are exactly the two constructors' fields, as built by
     `Contract.ofSegment`.
   - Finding 3: the count in `NOTES.md`.
2. **N1.** Are the nine renaming equations faithful? Is `Cfg.mapState` really read by the routes
   the review says, and are the drafts' citations now right?
3. **MIG-12's API.** Check faithfulness, and the inventory behind it:
   - `CfgRecord`'s external definitions (`mig12-api/` and the draft's measurements);
   - its 44 unfolding sites, crossed with their lemmas.

   Is anything else `CfgRecord`'s rebase reads still unpublished? Note that `Cfg.liftSymbols`
   already had `@[simp]` lemmas for its state and heads, which the new `simps` does not
   duplicate.
4. **The method fix.**
   - Does the seed-inclusive elaborator now inventory the cited definitions themselves, and flag
     structure-valued definitions whose fields lack equations?
   - Challenge its reports' judgments for the five briefs (N2 and N3 are recorded, not fixed:
     say if either should be).
5. **No behaviour change.** Only declarations and `simps` attributes are added. One deletion is
   a docstring line in `CounterLoop`'s header. No existing statement or definition changes.
6. **Duplication and records:** the screens (no new pair), and the records against the evidence.

## Repository-side attestations (verify or challenge)

- **Elaboration**, of the five touched files against the MIG-12 API's snapshot `oleans-lm12api`
  (the review, then the maintainer): 0 errors, 0 warnings; the 21 round-2 names and 13 MIG-12 API
  names resolve, with standard axioms or none. **Freeze:** publics added only.
- **Lint:** 0 FAIL, 67 WARN over 79 files before and after; check 8 drops `codeSkipRepeat`.
- **Replays:**
  - MIG-12's API, `mig12-api/replay-lm12api.log`: 160 of 160 at `9872634e`, static-equal (80);
  - round 2, `replay-lbapi3.log`: the three repaired files' downstream closure, 274 modules, from
    `oleans-lm12api`.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/brief-api-r2-findings.md`. The gate closes when it has zero blockers and zero majors.
