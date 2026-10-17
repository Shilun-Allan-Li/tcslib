# External audit pack — the brief-inventory API, round 3 (PR #118)

Campaign: the Arora-Barak chapters 3-4 plan; the user's "Everything" rule (2026-10-16: every
definition a brief's route reads gets a published equation before the brief is dispatched,
`policy.md` §1).
- **Round 2** (`audits/brief-api-r2-findings.md`) was FAIL, 0 blockers, 1 major, 2 minors. The
  major was MIG-12's route reading the machine model's primitives for an arbitrary action or
  machine, with no published lemma.
- **The resolutions** are in `audits/brief-api-resolutions.md`, "Round 2 result" and "Round 3".
- **This round's head** is `lean/brief-api` at `531b98a2`, two commits on round 2's `4624fc05`:

| Commit | What | Why |
|---|---|---|
| `74765ef4` | `Action.apply_state`, `_inputPos`, `_workTapePos`, `_output` (`Configuration`, `simps`; the work tapes keep `Simulation`'s `Action.apply_workTapes`); `MultiTapeTM.step_of_some`, `outputSymbol_of_some` (`Deterministic`), beside the upstream halted cases; both vendoring headers updated | finding 1: MIG-12's `CfgRecord` helpers and F5's ruler host read an arbitrary action's fields, a live step and a live emission |
| `531b98a2` | `counterWord_succ` (`Build/CounterLoop`), `scanResult_keep_keep` (`Build/Catalog`) | the corrected unfolding ledger (finding 2) found these two laws only privately |

- **Evidence:** `audits/evidence/brief-api/r3/`:
  - the review `gate-review-r2.md`;
  - the patches;
  - the corrected ledger `unfold-sites-r3.tsv`, with its scanner `unfold_scan.py.txt`;
  - the single-definition irreducibility runs (`perdef/`);
  - the consumer and control probes (`review-out/consumer*-CfgRecord.out`,
    `control-CfgRecord.out`);
  - the logs, the screen, and the replay script.
- **The bundle** also contains:
  - the corrected MIG-12 and F5 drafts;
  - the four touched files and the consumers `Build/CfgRecord`, `Build/InputDevice` (F5) and
    `Simulation` (`Action.apply_workTapes`).

## Brief for the auditor

1. **Round 2's findings.** Are they closed?
   - Finding 1: the six primitive equations state exactly the definitions' behaviour at a live
     state. The applied action's fields are exactly its four non-tape fields.
   - Finding 2: is the ledger now complete? Check the explicit scan across line breaks, and
     whether the definitional rows found by the irreducibility method cover the uses the scan
     cannot see. Note its stated limits: a lower bound within a tactic block, and reducible
     abbreviations untestable.
   - Finding 3: the erratum.
2. **The rest of the primitives.**
   - Is any other primitive reading of an arbitrary machine left unpublished, on MIG-12's or a
     brief's route? Consider the step, the emission, the applied action, the initial
     configuration and the run.
   - The review judged `spaceUsed`/`spaceUsedByTape` as read only through run lemmas: challenge
     that if a route needs them.
3. **The two private-only laws:** faithful, and placed beside their definitions?
4. **No behaviour change.** Declarations, docstrings and `simps` attributes only. The three
   deleted lines are module-docstring text: one in each vendoring header (Configuration,
   Deterministic) and one in Catalog's results list. No existing statement or definition
   changes.
5. **Duplication and records:** the screen (no new pair), and the records against the evidence.

## Repository-side attestations (verify or challenge)

- **Elaboration** of the four files against round 2's snapshot `oleans-lbapi3` (the review,
  then the maintainer): 0 errors, warnings equal to the bases' (Configuration 3, Catalog 77,
  Deterministic and CounterLoop 0).
- **New names:** the 8 resolve, with `[propext]` or `[propext, Quot.sound]`.
- **Freeze:** publics added only.
- **Lint:** 0 FAIL, 67 WARN, unchanged.
- **Consumer probe:** `CfgRecord`'s two helpers re-proved through only the new lemmas, with the
  definitions irreducible. The original proof fails under the same irreducibility (the control).
- **Replay:** `replay-lbapi4.log`, Configuration's downstream closure (320 modules), from
  `oleans-lbapi3`: 320 of 320 at `531b98a2`, 0 failed, static-equal (94).
- **The drafts' probes** with the round-3 names (F5 58, MIG-12 227): 0 errors against the
  round-3 snapshot (`r3/draft-probes/`).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/brief-api-r3-findings.md`. The gate closes when it has zero blockers and zero majors.
