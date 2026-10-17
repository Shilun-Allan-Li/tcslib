# External audit pack — MIG-11a, the row contracts (PR #117)

Campaign: the Arora-Barak chapters 3-4 plan; the machine library's foundation migration
(`machine-library-design.md` §16; `backlog.md` §2, MIG/RS).
- **User (2026-10-16):** the MIG items are interleaved with the fills, starting with MIG-12, the
  rebase of `Build/CfgRecord` onto the contract layer. The plan is
  `audits/evidence/mig12/DESIGN.md`.
- MIG-12 composes four framed rows that had no contract. This PR is that part of MIG-11 ("contract
  instances of the framed rows"). It gets a **statement gate** (MIG-11's gate class) before it
  merges.
- **The rule it follows** (`policy.md` §1, *Definitions land with their lemmas*, adopted
  2026-10-16): every new public definition lands with its field equations or equation lemmas, and
  none is `@[simp]`.

| File | Additions |
|---|---|
| `Build/Catalog.lean` | `compareStop` with `compareStop_eq`, `_cons_cons`, `_spec`, `_unique`, `_le`; `compareTM_run_stop_ofCfg`; `compareTM_run_ofCfg` re-proved as its corollary (statement unchanged) |
| `Build/Contract/Catalog.lean` | `copyTM_contract`, `copyTM_contract_frames`, `compareTM_contract`; their field equations |
| `Build/Contract/Counter.lean` (new) | `counterRowContract`; `incrementTM_contract`, `decrementTM_contract`; field equations |
| `Build/Contract.lean` (facade) | the new module's import and Contents entry |

- **Evidence:** `audits/evidence/mig11a/` (`NOTES.md`, the patch, logs, probes, scripts).
- **The bundle** also contains:
  - the run lemmas the contracts wrap and their files (`Build/Catalog`, `Build/CounterLoop`);
  - the contract layer (`Build/Contract/Basic`);
  - MIG-12's design note;
  - `Build/CfgRecord.lean`, the consumer.

## Brief for the auditor

1. **Faithfulness.** Each contract's fields restate exactly its row's framed theorem:
   - precondition, time, endpoint, envelope;
   - the exit set and the cut.

   For `compareTM_contract`, the time is the new `compareStop`. Check that:
   - `compareStop` is the stop of the existing private trace (`compareStop_spec`,
     `compareStop_unique`);
   - `compareTM_run_stop_ofCfg` is the old theorem at that stop;
   - `compareTM_run_ofCfg`'s statement is byte-identical.
2. **Design.**
   - *Exits:* the compare and the counter rows exit at either verdict (a range, as
     `scanTM_contract` does), so that a `branch` can dispatch on them. Is this the right shape,
     against a singleton at the verdict actually reached?
   - *Counter index:* the counter rows are indexed by `(w, v)` with `fix w = some v`, rather
     than by `w` with an `Option`-valued endpoint.
   - *The factoring:* `counterRowContract` makes the increment and decrement instances of one
     constructor.
   - *Placement:* `Contract/Counter` sits beside `CounterLoop`, so that `Contract/Catalog` does
     not import the counter loop.
3. **Coverage for MIG-12.**
   - Against the inventory in `DESIGN.md`, are these the rows `CfgRecord` composes?
   - Does MIG-12 need anything more from them: frames for the compare and the counter rows,
     their overflow and underflow cases, or joint trajectories?

   Name any gap.
4. **The rule.**
   - Each new definition has its lemmas beside it.
   - The docstrings state their mathematics.
   - Lint check 8 lists none of them.
   - No `@[simp]`.
5. **No behaviour change.** No existing statement or definition changes. The one proof change
   (`compareTM_run_ofCfg`) is a swap onto the new theorem.
6. **Duplication** (failure mode 5): the screen before and after (`logs/screen-*.txt`).
7. **Records.** Check `NOTES.md` and this pack against the evidence.

## Repository-side attestations (verify or challenge)

- Built on the tip `c2ec34c5`, against `oleans-lapi2`, then stacked on #116's round 2 (`b131d239`).
- **Elaboration:** `Catalog` 0 errors, 77 warnings as at the base. `Contract/Catalog` through an
  overlay, 0 errors. `Contract/Counter` 0 errors, 0 warnings.
- **Axioms:** standard only. **Freeze:** publics added only, plus the one authorized body change.
- **Lint:** 0 FAIL; check 8 adds nothing.
- **Screen:** `logs/screen-delta.log`, no new copied proof.
- **Replay:** `replay-lm11a.log`, 86 of 86 at `b131d239`, 0 failed. The sorry counts equal a
  static count, 0 mismatches.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/mig11a-statements-findings.md`. The gate closes when it has zero blockers and zero majors.
