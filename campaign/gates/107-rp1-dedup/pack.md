# External audit pack: dedup RP-1, definitional reads re-pointed to #196's equations (PR #216, a dedup gate)

## Why this PR

The dedup window (12.2c) started on 2026-11-06 (the user). It retires the ledger's families one PR
at a time. **RP-1** (`campaign/duplication-ledger.md`) is rule 10 debt rather than duplication.
#196 published `Iff.rfl` characterizations for seven definitions:

| Definition | Home | Equation(s) |
|---|---|---|
| `Complexity.WalkLe` | `Logspace/PathWalk` | `walkLe_zero_iff`, `walkLe_succ_iff_head` |
| `Complexity.Codec.StepRel` | `Codec/Bridge` | `stepRel_iff_mem` |
| `Complexity.ExpBFS.RCode` | `ExpBFS/Radius` | `rcode_iff_reflTransGen` |
| `Complexity.ExpBFS.WinRun` | `ExpBFS/Radius` | `winRun_iff` |
| `Complexity.LogProg.SavitchARM.Rel` | `SavitchARM/Recursion` | `rel_iff_orc` |
| `Complexity.LogProg.SavitchARM.InitO` | `SavitchARM/Search` | `initO_iff_orc` |
| `Complexity.LogProg.SavitchARM.AccO` | `SavitchARM/Search` | `accO_iff_orc` |

Proofs in other files, mostly Hydroxyi's (mechanical edits allowed with an FYI, the user,
2026-11-06), still read these definitions by unfolding them (`simp [WalkLe]`, `rw [RCode]`) or
through their definitional equality: `exact h` across the definition, anonymous constructors,
`rintro` patterns. The ledger recorded 10 sites. A scoping pass, and then an exhaustive
irreducibility probe, widened the family to **23 public proof bodies in 14 files**. All of them
now go through the equations.

**The PR:** #216 on `lean/dedup-rp1`, head `485cfbab` (full hash in the bundle header). The
commits are:
- the change `f200144b`;
- `cl_iff`'s proof sketch, `3d0f6ceb` (after the re-point it is a 21-line proof, which policy
  requires to have a sketch);
- merges of the campaign, the last at `485cfbab`, after #208, #212 and #213 merged.

The change touches 14 files, with 75 lines added and 57 removed at the merged head against the
campaign's Lean `a28b8c42` (`evidence/landing/rp1-merged.diff`).

## What changed (verify)

Every changed declaration keeps its statement. Only proof bodies change, plus `cl_iff`'s docstring
sketch (`evidence/freeze/`, 14 files):

| File | Public bodies changed |
|---|---|
| `ClassPSPACE/TQBFHardMachine` | `TQBFHard.reflTransGen_stepRel` |
| `Randomized/BPLInP` | `BPLInP.entryW_eq` |
| `Randomized/BPLInPCount` | `BPLInP.stepRel_iff` |
| `SpaceComplexity/ExpBFS/Main` | `ExpBFS.cl_iff` (and its sketch), `ExpBFS.stp_orcN` |
| `SpaceComplexity/ExpBFS/Radius` | `ExpBFS.rcode_iff` |
| `Logspace/ISCountGenRadius` | `ISGen.mem_ball_iff_rcode`, `ISGen.mem_of_exists_acc`, `ISGen.one_le_card_rset` |
| `Logspace/ISCountGenStage` | `ISGen.guloop`, `ISGen.gvloop` |
| `Logspace/ISCountGenWalk` | `ISGen.gwalk_loop`, `ISGen.gwalk_spec` |
| `Logspace/ISCountMath` | `ISCount.card_ball_zero`, `ISCount.walkLe_lt`, `ISCount.walkLe_succ_iff` |
| `Logspace/PathHard` | `PathHard.red_mem_iff` |
| `Logspace/PathHardRegs` | `PathHard.orc_step` |
| `Logspace/PathWalkMachine` | `LogProg.ps_walk` |
| `SavitchARM/Correct` | `SavitchARM.accO_orcN`, `initO_orcN`, `rel_orcN` |
| `SavitchARM/Reach` | `SavitchARM.mem_iff_reach` |

There are no new declarations, no removed declarations, no import changes and no private
changes. Public counts are equal before and after in every file.

`SavitchARM/Reach`'s `mem_iff_reach` is the one site found only by the probe. It passed a
`stepLang` membership where `StepRel` was expected, and is now
`fun j hj => stepRel_iff_mem.mpr (hstep j hj)`.

`ISCountMath`'s `walkLe_succ_iff` is itself a copy of `PathWalk`'s step equation, a separate
family (**WL-1**). The user ruled that it moves into `PathWalk` as `Complexity.walkLe_succ_iff`
after this PR merges. Here only its body is re-pointed.

## Brief for the auditor

1. **Completeness:** does any proof outside the seven home files still read one of the seven
   definitions other than through its equation? This covers `simp`/`rw`/`unfold` with the
   definition's name, `show`/`change` through it, `exact` across it, anonymous constructors and
   `rintro`/`cases` patterns on it.
2. **Scope:** does the change touch anything beyond those reads? In particular, is each new body
   the old argument with the read replaced, and is `cl_iff`'s sketch accurate?

## Repository-side attestations (verify or challenge)

- **Rule 10, exhaustively** (`evidence/rule10/README.md`). Each of the 52 modules that can see a
  home file was copied with `attribute [local irreducible]` on every one of the seven definitions it
  imports, then elaborated at `f200144b`. Explicit `simp [Def]`/`rw [Def]` unfolds still work under
  `irreducible`; they were found by grep, and none remains.
  - Result: **52 modules, 0 errors**. The only failure ever seen was `Reach` before its fix.
  - Since `f200144b`, two things changed:
    - `cl_iff`'s docstring;
    - the campaign merge, which brought #208's IL-1 re-points into `ExpBFS/Main`,
      `SavitchARM/Correct`, `PathHardRegs` and `PathWalkMachine`. These are other declarations,
      citing `indicator_inputLenLang`/`indicator_inputBitLang`, and none reads the seven
      definitions.

    The probes were not re-run on the merged head; the merged-tree replay below elaborates it.
- **Freeze** (`evidence/freeze/`, merged head against `a28b8c42`): 14 files, 23 authorized public
  body changes (the table above), 0 statement changes, 0 unauthorized, 0 private changes.
- **Lint** (`evidence/lint/`, `git archive`s of both trees):
  - The campaign lint is identical at base and head:
    - `SpaceComplexity` 0 FAIL, 81 WARN over 112 files;
    - `Randomized` 0 FAIL, 51 WARN over 65 files;
    - `ClassPSPACE` 0 FAIL, 10 WARN over 14 files.
  - The policy linter over the 14 files gives the same single pre-existing finding at both. The
    round-1 `cl_iff` finding is gone.
- **Replay** (`evidence/merged-tree/`): `replay-lrp3` at `485cfbab`, the downstream closure of the
  14 files (53 modules), chained from the campaign's new snapshot `oleans-lcamp2` (the combined
  replay after #208, #212 and #213; `campaign/status/2026-11-06-campaign-replay-2/`).
  **53 modules, 0 failed.** The static check finds 0 mismatches. Its 21 `sorry` warnings are all in
  `ClassPSPACE/TQBF`, the campaign's existing ones.
- **Screen:** not run. The change replaces reads with citations and adds no proof text that could
  pair.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/107-rp1-dedup/findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `rp1-dedup-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.
