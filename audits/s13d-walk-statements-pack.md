# External audit pack — §13d G4's ruler: the lockstep walk and the seek, walk and scan contracts (statement gate)

Campaign: the Arora-Barak chapters 3-4 plan, §2.1 (Thm 3.1 at `f log f`, through the
Hennie–Stearns simulation of [AB09] §1.7).
- The §13d zone layer's G2–G4 statements are landed (PR #106) and G2 is filled (PR #108).
- **Obligation 3** of the G2–G4 statement gate (`audits/s13d-g24-statements-resolutions.md`):
  identify, before G4's fill brief, the public host for the two-tape scratch and ruler layout,
  or gate a missing reusable host.
- The maintainer's survey (`audits/evidence/s13d/g4-hosts/G4-HOSTS-SURVEY.md`) found:
  - every host public;
  - **one leaf missing:** a two-tape lockstep walk that stays where it ends, the ruler for
    crossing to the mirror side and for slot offsets;
  - no Contract wrappers for the seek rows and the scan, which G4's rows (stated as `Contract`s)
    compose.
- **User (2026-10-15): public, gated first.**

**This gate audits that unit before it lands.** The unit is complete: its one new theorem is
proved, so the gate audits statements and proofs together. **Nothing is landed:** the landing PR
follows a clean gate (branch `lean/walk-row`, prepared at the tip; replay of the two modules'
downstream closure).

| File | Additions | Changes |
|---|---|---|
| `Build/Catalog.lean` (R8.3, after `Turing.skipTM`) | `Turing.walkTM`, `Turing.skipTM_eq_walkTM`, `Turing.walkTM_run_ofCfg` | `Turing.skipTM_run_ofCfg` re-proved as the walk's instance (statement byte-identical) |
| `Build/Contract/Catalog.lean` | `Turing.framedContract`; `Turing.seekPost`; `Turing.walkTM_contract`, `skipTM_contract`, `skipBackTM_contract`, `seekEndTM_contract`, `seekStartTM_contract`, `scanTM_contract` | `Turing.sweepContract` defined through `framedContract` (signature byte-identical) |

**Evidence:** `audits/evidence/s13d/walk/`. It holds the two unit files (`unit/*.lean.txt`, the
landed form), the generators and their blocks (`scripts/`), and the logs; its `NOTES.md` has the
design and the checks.

## Brief for the auditor

1. **The walk's statement.** `walkTM k src moved dir`: while tape `src` reads nonblank, every head
   in `moved` steps once along `dir`; at the first blank, once more, into `done`; nothing is
   written. `walkTM_run_ofCfg` states:
   - **hypotheses:** `src ∈ moved`, and the word `w` read along `dir` from `src`'s head, delimited
     `|w|` cells along;
   - **conclusion:** exit at exactly `|w| + 1`, never earlier; every moved head ends `|w| + 1`
     cells along, nothing else changed; the exact trajectory (each moved head `t` cells along at
     time `t`, every other head fixed).

   Check:
   - the boundary cases: `w = []`; `dir = 0`, where the hypothesis forces `w = []`; `moved` beyond
     `src`;
   - that the cells under the other moved heads are indeed unconstrained;
   - that the statement is what G4's ruler needs (the survey's §3: the mirror crossing and the
     slot and write-back offsets).
2. **The skip as an instance.**
   - `skipTM_eq_walkTM` (`rfl`) and the re-proof of `skipTM_run_ofCfg` through it.
   - `skipTM`'s definition is unchanged, so its consumers (`Build/CfgRecord`) are unaffected.
   - Confirm that the statement is byte-identical (`logs/freeze-catalog.log`).
3. **The constructor.** `framedContract` turns a framed one-exit row in the catalog's shape (touched
   heads in intervals, the others fixed) into a `Turing.Contract`, with one-point envelopes for
   the untouched heads.
   - `sweepContract` is now its two-pass instance: same signature, same fields definitionally.
   - Check that the instance proofs (`sweepContract_traj`, the frames lemmas, the clear, copy and
     transfer contracts) still elaborate and say the same thing.
4. **The six instances.** For each, check that `pre`, `time`, `post`, `lo` and `hi` are exactly the
   wrapped framed row's:
   - the seek and skip instances are one-line applications of the proved rows, with the shared
     endpoint `seekPost` (the head of tape `i` at a given position, state `done`);
   - the walk's interval is `[pos + min 0 (dir·(|w|+1)), pos + max 0 (dir·(|w|+1))]`;
   - the scan's exit set is every `done a`.
5. **Duplication** (failure mode 5). See the v3 screen below, with its population and both logs.
   The design was chosen to write each argument once:
   - the walk generalizes the skip's proof, and the skip becomes its instance;
   - the envelope conversion lives in `framedContract`, and the wrappers do not repeat it.
6. **Records.** Check the notes and this pack against the evidence. Report anything else in the
   standard table.

## Repository-side attestations (verify or challenge)

- Built at #108's head `a9ee4701` (the G2 fill), against `oleans-lcanon4`. #108 has since merged
  (`b6e0344c`). At the tip `2e79d0f7`, which is Lean-identical to that head, the generator
  reproduces both unit files byte for byte.
- **Elaboration.** The two overlays concatenated into one probe, because Contract/Catalog
  imports Catalog and no olean is written: 0 errors, 0 sorry warnings, Catalog's 78 warnings
  unchanged.
- **Axioms.** All 119 publics of the two files use standard axioms only; no `sorryAx`.
- **Freeze.**
  - Catalog: +3 publics; one authorized body change (`skipTM_run_ofCfg`).
  - Contract/Catalog: +8 publics; `sweepContract`'s body changed, its signature identical. The
    freeze tool's heuristic flags the `where` → `:=` change; the logged exact signature comparison
    resolves it.
- **Lint.** 0 FAIL; the WARN and finding sets are unchanged. No new line over 100 characters.
- **Screen** (v3; `logs/screen-{base,ov}.txt`, `logs/screen-delta.log`; population
  `logs/screen-population.txt`: the two files, `Contract/Basic`, `Contract/Seam`, `Simulation`,
  `ZoneRebalance`, `CfgRecord`).
  - Pairs go from 392 to 390, and reproduced text from 127,961 to 125,515 characters.
  - Gone: the three pairs against the skip's old proof (58–68%).
  - **New: one,** `seekStartTM_contract` ← `seekEndTM_contract` (207/390, 53%). These are mirror
    wrappers restating their rows' field-layout preconditions. **The user approved it on
    2026-10-15.** Verify the accounting.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/s13d-walk-statements-findings.md`. The gate closes when it has zero blockers and zero
majors.
