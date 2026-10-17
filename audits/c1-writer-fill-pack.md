# External audit pack — C1-W fill gate: the bounded choice writer's contract (PR #123)

Campaign: the Arora-Barak chapters 3-4 plan, C1 (the nondeterministic time hierarchy, [AB09, Theorem
3.2]). The guess-first route has one nondeterministic leaf, the **choice writer** `ndWriterTM`
(`TuringMachine/Build/NDHost.lean`). C1 wave 1's brief W (`briefs/c1-fill-writer.md`) asked for
its bounded contract, which every guess-then-run assembly theorem of the module passes:

| Target | What it states |
|---|---|
| `Turing.ndWriterTM_run_block` | started at `run ()` over a nonblank block of `m` cells of tape `j` from its head, followed by a blank, every choice word `w` of length `m + 1` overwrites the block with `w.take m`, leaves the head of tape `j` just after the block, and reaches `done`, with every other field unchanged; no shorter word reaches `done` |

**How the proof arrived.**
- The fill worker's sandbox could not bootstrap Lean's dependencies, so its delivery was an
  environment-blocked partial (`audits/c1-fill-agent-reports/writer-1-REPORT.md`). It included
  an unchecked proof draft.
- The maintainer's review sub-agent (`audits/evidence/c1/fills/writer-1/REVIEW.md`) found 3 errors
  in the draft and fixed them with four one-line edits.
- The worker's two step lemmas formed a 91% screen pair, over the brief's copy line. The review
  merged them into one.
- **The user ruled on 2026-10-17** that the result lands by a maintainer PR and this fill gate.
  The worker's "Fill appendix" docstring is not landed.

**Stacked on #122**, whose replay closure it overlaps through the `TuringMachine` facade. Head
`lean/c1-writer` at `c567568f`, two commits on #122's `6a48b93e`:
- `7fdd7797`: the proof;
- `c567568f`: the facade's `Build/NDHost` entry.

## What changed (verify)

| Class | Declarations |
|---|---|
| **Target body, `sorry` → proof** | `ndWriterTM_run_block` |
| **Privates added** | `wr_cfg` (the configuration after writing a prefix), `wr_tape_append`, `wr_cfg_nil`, `wr_cfg_scan`, `wr_cfg_stepWith` (one step: the stationary exit at a blank, the extended prefix otherwise), `wr_prefix` (the induction) |
| **Other bodies** | `guessRunTM_runWith_handoff`'s docstring only (its sketch called the writer sorried) |
| **Docstrings** | the module's status texts and the facade's `Build/NDHost` entry: the writer is proved |
| **Imports, statements** | unchanged |

## Brief for the auditor

1. **Freeze.** Every public statement is unchanged; the only public body changes are the target's
   proof and one docstring; the privates added are exactly the six above
   (`audits/evidence/c1/fills/writer-1/land/freeze.txt`).
2. **The route is the brief's.** One induction over the written prefix. Check that the proof:
   - unfolds only `ndWriterTM` (this file's frozen definition, allowed by the brief) and its own
     private `wr_cfg`;
   - reads everything else through published lemmas: `NDTM.stepWith_of_some`, the `runWith`
     algebra, the `Action.apply_*` field equations, `FinTM.bufferTape_append`,
     `Cfg.workTapeSymbols_eq`;
   - uses no other file's private constant.
3. **The second clause** (no shorter word reaches `done`): check the argument that every proper
   prefix leaves the state at `run ()`.
4. **Edge cases:** `m = 0` (the first step reads the blank and stops; nothing is written);
   negative head positions; `k` work tapes with `j` arbitrary.
5. **Duplication** (the brief's 7-file population, `land/screen-*.txt`):
   - Two new within-file pairs, `wr_cfg` with `guessRunCfg` (56% and 50%). Both come from the
     tape-update expression that the frozen statement prescribes. Is that acceptable, or should
     `wr_cfg` be expressed through `guessRunCfg`?
   - The 91% pair of the worker's draft is gone.
6. **Records:** do the review, this pack and the PR body agree with the evidence? Is the credit to
   the worker's draft stated accurately?

## Repository-side attestations (verify or challenge)

- **Elaboration** against `oleans-lndnf`: 0 errors, 0 warnings. The module had one `sorry`, now
  none.
- **Axioms:** `ndWriterTM_run_block` and the seven assembly theorems that pass the writer print
  `propext`, `Classical.choice` and `Quot.sound`.
- **Lint:** 0 FAIL; `TuringMachine/` stays at 63 WARN.
- **Screen:** 780 → 787 declarations, 1,018 → 1,020 pairs, 380,649 → 380,919 characters. The two
  new pairs are `guessRunCfg`/`wr_cfg` (56%, 50%), within the file. The base equals the brief's
  measured base exactly.
- **Replay:** `replay-lc1w.sh`, `Build/NDHost`'s downstream closure (2 modules: it and the
  `TuringMachine` facade), chained from `oleans-lndapi2` (#122's replay). **Passed (user,
  2026-10-17):** 2 of 2 at `c567568f`, 0 failed (`land/replay-lc1w.log`); the sorry counts equal a
  static count (0 mismatches, 0). The snapshot `oleans-lc1w` is the tip plus #121's round 2, #122
  and #123.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/c1-writer-fill-findings.md`. The gate closes when it has zero blockers and zero majors.

**Deliver your findings as a downloadable Markdown file named `c1-writer-fill-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.
