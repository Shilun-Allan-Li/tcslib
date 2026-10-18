# External audit pack — machine-routine layer (§12), round 3 (re-audit of the round-2 repair)

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md`), the §12
routine-layer statement gate, round 3. Round 2
(`audits/routine-infra-r2-findings.md`, attached verbatim, alongside round
1's `audits/routine-infra-findings.md`) returned **1 blocker, 0 majors,
0 minors, 1 note**: both new returning-run contracts were false at `T = 0`
for an initially halted configuration — the handover state projection would
demand `none = some (Sum.inr ())` — while the seven other new contracts and
all round-1 dispositions were accepted. This round audits the one repair.
The gate closes on zero blockers and zero majors.

Audited at commit `2b82cbb3` (branch `complexity/arora-barak-ch3-4`). The
complete repair is the attached diff
(`audits/evidence/routine-infra-r3-repairs.diff`, 38 lines): **one
hypothesis added to each of the two through-halt contracts** —
`(hc : c.state ≠ none)` on `embedSilentRetTM_run` and `embedEmitRetTM_run`,
your first proposed remedy — plus the suppressing flavor's docstring
recording the counterexample and the equivalence `hc ↔ 0 < T` under
`hhalt`. Nothing else changed; the inventory is unchanged (**56 sorried
statements**: Embed 13, Seam 11, Catalog 32).

## Brief for the auditor

You have both prior reports. Your deliverables:

1. **Replay your zero-time counterexample** against the amended contracts:
   with `c.state = none` the new `hc` fails, so no instance exists; with a
   live `c`, `hhalt` forces `T ≥ 1` and your own positive-time through-halt
   argument (round 2, "the induction has an essential last-step case")
   applies. Confirm nothing else is needed and that the added premise does
   not weaken any consumer: the §12 consumers always launch subroutines
   from live seams.
2. Confirm the repair does not disturb the seven other new contracts (the
   visited-set equalities were already true for initially halted starts
   and are unchanged) or any round-1 disposition.
3. Report anything newly misstated, same table and severity scale. One
   **round-2 pack erratum is acknowledged here** (your R2-2): that pack's
   brief misstated the new-contract subdivision as six run/first-return
   plus three visited-set contracts; the correct split is five and four.
   Shipped packs are never edited.

## Scope

| Item | Where |
|---|---|
| Under audit | the attached 38-line diff to `Build/Embed.lean` (two hypothesis insertions, one docstring paragraph) |
| Unchanged, re-attached | all three §12 modules and the frozen `Build/` context (byte-identity outside the diff checkable against round 2's attachments) |
| Declared, out of scope | the same commit range contains the P4.3/P3.2/P3.3 gate closures (their minors swept in `Diagonalization/` files and facade wiring in `TuringMachine.lean`/`Diagonalization.lean`/`TCSlib.lean` — closed gates, disjoint from the §12 statements); tactic proofs |

## Per-finding disposition (verify each)

| # | Round-2 finding | Repair |
|---|---|---|
| R2-1 | **blocker** — both through-halt contracts false at `T = 0` for an initially halted `c` | `(hc : c.state ≠ none)` added to both; the docstring records the counterexample and that `hc` is equivalent to `0 < T` under `hhalt`. Your positive-time proof sketch applies verbatim |
| R2-2 | note — the round-2 pack's 6+3 inventory subdivision | Pack erratum acknowledged above (5 run/first-return + 4 visited-set); no source change |

## Repository-side attestations (verify or challenge)

* Fresh elaboration (`audits/logs/routine-infra-r3-sweep.log`, revision
  recorded at start: `2b82cbb3`): the three modules, 0 `error:` lines,
  fresh `.olean`s, exactly **56** `declaration uses 'sorry'` warnings
  (Embed 13, Seam 11, Catalog 32).
* Style lint (`audits/logs/routine-infra-r3-stylelint.log`):
  `TuringMachine` tree 0 FAIL with the same 9 size WARNs as round 2
  (8 pre-existing plus the justified `Catalog.lean`).
* Statement-freeze baseline: commit `2b82cbb3`.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`; findings verbatim into
`audits/routine-infra-r3-findings.md`; the gate closes on zero blockers and
majors.
