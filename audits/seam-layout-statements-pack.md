# External audit pack — the step block's seam layout, a statement gate (PR #124)

Campaign: the Arora-Barak chapters 3-4 plan. Three step-block simulators start the same way:
- the deterministic universal machine's startup U2-S (`UniversalK.exists_selfStartupTMK`);
- the record-table canonizer's H1 (`CodeSimulator`);
- C1's nondeterministic interpreter core R (`NDCodeSimulator.exists_ndInterpreterCore`).

Each captures a machine's canonical serialization
`serializeK M = pairEncode n.bits (unaryFin M.q₀ ++ tableBitsK M.tr)` on a scratch tape. The step
block's represented start (`Turing.StepBlock.Rep`) instead needs two exact auxiliary tapes:
- the bare table, `FinTM.bufferTape (tableBitsK tr)`, on the table tape, head `0`;
- the summary cells, `summaryCells (outputSummary c.output) (unaryFin q)`, on the summary tape,
  head `0`. For an empty output these are the unary initial state from cell `2`, with cells `0`
  and `1` blank.

**The gap (G2):** no public machine redistributes the first into the second. C1-R's partial
delivery was reviewed on 2026-10-17 (`audits/evidence/c1/fills/core-1/REVIEW.md`, (d) G2). R's
brief installed the whole serialization, which does not give `Rep`. U2-S's brief plans the split
as a private leaf.

**The user's ruling (2026-10-17):** one public contract, stated now in its own statement PR and
gate.
- R and UN cite it.
- U2-S's private leaf is promoted to prove it when U2-S delivers (U2-S's worker cannot add the
  import, so its delivery keeps its leaf private until integration).

**Stacked on #123** (C1-W's landing, itself on #122). Head `lean/seam-layout` at `0355da56`, one
commit on #123's `c567568f`.

| File | Change |
|---|---|
| `TuringMachine/Build/SeamLayout` (new) | `Turing.exists_seamLayoutTM`, sorried |
| `TuringMachine` (facade) | imports and lists the module |

## The statement

For distinct work tapes `src`, `tbl`, `sm` of a `k`-tape machine, there are a machine with an
entry state `entry`, a live exit `done` and a constant `C` such that the following holds. Let
`s = pairEncode a ((List.replicate q true ++ [false]) ++ v)`. Start at `entry` with:
- `src` holding exactly `FinTM.bufferTape s`, its head anywhere in `[0, |s|]`;
- `tbl` and `sm` blank, their heads at `0`.

Then the machine reaches `done` at some `T ≤ C·(|s| + 1)`, and not before, with:
- `tbl = bufferTape v`;
- `sm = fun p => bufferTape (List.replicate q true ++ [false]) (p - 2)`;
- `src` blank;
- the three heads at `0`;
- the input position unchanged, every other tape and head unchanged;
- the output equal to the start's at every time `u ≤ T`.

## Brief for the auditor

1. **True.** Is the contract achievable for a single `C`, uniformly in `a`, `v`, `q` and the
   frame? Check the sketch's phases:
   - rewind `src` from anywhere in `[0, |s|]`, including a start on the right blank `|s|`;
   - skip the doubled region of `pairEncode` over its separator `[false, true]`;
   - place the unary word on `sm` from cell `2`, which needs stopping at the first `false`, not
     at a blank;
   - copy `v` onto `tbl`;
   - rewind `tbl` and `sm`, and clear `src` and return its head to `0`.

   Check each against the catalog rows' `_run_ofCfg` contracts it names, or the leaves it
   declares. Watch for `v = []`, `q = 0`, `a = []`, and the head starting at `|s|`.
2. **Sufficient.**
   - **For R's route:** with `a = n.bits`, `q = M.q₀`, `v = tableBitsK M.tr`, and the source
     head where R1′ (`embedSilentRetTM_run`) leaves its capture tape (one past the word,
     `embedSilentCfg`), does the endpoint give `Rep`'s table and summary fields for the initial
     configuration? `audits/evidence/c1/seam-layout/SeamLayoutConsumer.lean.txt` derives both,
     reading the summary's cell `0` through #122's `FinTM.bufferTape_of_neg`.
   - **For U2-S's statement:** is the endpoint exactly U2-S's tapes `k` and `k + 1`
     (`UniversalK.lean`, `exists_selfStartupTMK`)?
3. **Not vacuous, and not too strong.**
   - The start hypotheses are satisfiable.
   - The exact-blank requirement on `tbl` and `sm` matches what the startups have.
   - Is requiring `src = bufferTape s` exactly (blank outside the word) right for a capture tape
     whose prefix `pre` is empty? Should the contract allow a nonempty `pre`?
4. **Placement:** is a new `Build/` module right? It imports `Build/Catalog` and `Build/Seam` (the
   rows and the phase host its fill needs), and nothing above the step block. Check for import
   cycles with its consumers: `NDCodeSimulator`, `UniversalK`, `CodeSimulator`.
5. **Records:** do this pack, the PR body and the review's G2 section agree?

## Repository-side attestations (verify or challenge)

- **Elaboration** (against `oleans-lndnf`): 0 errors; 1 warning, the contract's `sorry`.
- **Consumer probe:** 0 errors; the only warning is the inline contract's `sorry`.
- **Lint:** `TuringMachine/` 0 FAIL, 63 WARN, unchanged.
- **Replay:** `replay-lseam.sh`, 2 modules (the module and the `TuringMachine` facade), chained
  from `oleans-lc1w` (#123's replay). REPLAY-RESULT

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/seam-layout-statements-findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named
`seam-layout-statements-findings.md`** (the findings table and the verdict line, no other
wrapping), and also paste its content in your reply.
