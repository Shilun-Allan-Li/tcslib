# External audit pack — C1-E: the exponential decider as a hypothesis, a statement gate (PR #126)

Campaign: the Arora-Barak chapters 3-4 plan, C1 (the nondeterministic time hierarchy, [AB09, Theorem
3.2]). C1-E's statements (`Diagonalization/NTimeDiagonalizer`, PR #121) passed their statement
gate in round 2 (gate 40, `audits/ntime-diag-statements-r2-findings.md`, PASS 0/0/1/12).

**The import cycle.** The maintainer's review of gate 40 (`audits/evidence/c1/c1e/gate40-review.md`,
X2) found one:
- The fill E-D of `exists_diagonalizer` needs the exponential decider BF
  (`Turing.exists_ndAcceptsWithin_decider`) for the top rung's flip.
- BF is stated in `Diagonalization/NTimeHierarchy`, as UN's brief's target 2.
- That module's `ntime_hierarchy` must import `NTimeDiagonalizer`, so neither file can import the
  other.

**The user's ruling (2026-10-17):** `exists_diagonalizer` takes BF's conclusion as a hypothesis
`hBF`, and `ntime_hierarchy`'s proof supplies it. The alternatives not taken were re-homing UN's
and BF's statements upstream, and moving H, H′ and S downstream.

**Stacked on #125.** Head `lean/ntime-diag-bf` at `5333b29b`, one commit on `4ab012d9`. One file
changes.

| Change | What |
|---|---|
| `exists_diagonalizer`'s statement | a new hypothesis `hBF`, verbatim the conclusion of `exists_ndAcceptsWithin_decider c`: a deterministic `BF` such that for every code `α` there is a `C` with, for all `x` and `t`, `BF` computing `[true]` on `⟨⟨bits t, α⟩, x⟩` within `C·2^{C(t+1)}` when the coded machine accepts `x` within `t`, and `[false]` otherwise |
| its docstring | the hypothesis in the summary; a paragraph on why it is a hypothesis; the sketch's top rung reads `hBF` |
| two docstring lines (gate 40's X3) | the middle query word is no longer called R's input; `D` rewrites its budget field first |

Nothing else changes: the conclusion, the other declarations and the imports are as gated.

## Brief for the auditor

1. **Still sufficient.** With `hBF` supplied by `exists_ndAcceptsWithin_decider c`, does
   `ntime_hierarchy`'s chain still go through? `audits/evidence/c1/c1e/x2/Consumer.lean.txt`
   checks the application type-checks.
   - Is the hypothesis exactly BF's conclusion, at the same `c`?
   - Does nothing in the statement depend on BF's machine beyond that conclusion?
2. **Still true.** Gate 40 found the round-2 contract true with BF available by citation. Is it
   true with BF as a hypothesis? The sketch's top rung uses `BF` only through `hBF`'s two
   clauses, with `C_BF` from `hBF`.
3. **Not vacuous.** A statement with an unsatisfiable hypothesis would be vacuous. Is `hBF`
   satisfiable for every effective scheme `c`? BF's own statement is sorried
   (`NTimeHierarchy.lean`, UN's brief). Its derivation from UN is proved,
   `ndAcceptsWithin_decider_of_universal` (`ClassNP/ExhaustiveReplay.lean`).
4. **The cycle is gone.**
   - `NTimeDiagonalizer`'s imports are unchanged (`NDCodes`, `ClassNP/NTIME`,
     `ClassP/TimeConstructible`).
   - E-D's fill needs no import of `NTimeHierarchy`.
   - `ntime_hierarchy`'s fill can import `NTimeDiagonalizer`.
5. **The docstrings** describe the route correctly.
6. **Records:** do this pack, the PR body and the resolutions
   (`audits/ntime-diag-statements-resolutions.md`, round 2's X2) agree?

## Repository-side attestations (verify or challenge)

- **Elaboration** against `oleans-lndiag2`: 0 errors; 2 warnings, the two contracts' `sorry`s
  (`x2/elab.out`).
- **Consumer probe:** 0 errors; 1 warning, the inline statement's `sorry` (`x2/consumer.out`).
- **Freeze:** 22 → 22 publics. "STATEMENT CHANGED: exists_diagonalizer" is the intended change;
  `query`'s body change is its docstring (`x2/freeze.txt`).
- **Lint:** `Diagonalization/` 0 FAIL, 1 WARN (`EXPCOM`, unrelated), unchanged.
- **Screen** (gate 39's 7-file population): 49 → 49 declarations, 6 → 6 pairs, no new pair.
- **Replay:** `replay-lx2.sh`, 2 modules (`NTimeDiagonalizer` and the `Diagonalization` facade),
  chained from `oleans-lg4c1`. **Passed (user, 2026-10-17):** 2 of 2 at `5333b29b`, 0 failed
  (`x2/replay-lx2.log`); the sorry counts equal a static count (0 mismatches, 2). The snapshot
  `oleans-lx2` is the tip plus #121's round 2 and #122–#126.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/ntime-diag-bf-statements-findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named
`ntime-diag-bf-statements-findings.md`** (the findings table and the verdict line, no other
wrapping), and also paste its content in your reply.
