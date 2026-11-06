# Gate 04 (Pass–shelat ch. 5–8, S2b), round 5: closing audit pack (DRAFT)

**Draft, 2026-11-06.** Completed when the round 4 repair lands on #195: the head, the commits,
the counts and the evidence list are filled from the repair's report, and the evidence folder is
`evidence-r5/`.

**What is audited:** PR [Shilun-Allan-Li/tcslib#195](https://github.com/Shilun-Allan-Li/tcslib/pull/195)
at its head `@HEAD@`: the repair commits on round 4's `a588adfe` (`@COMMITS@`).

In the bundle:
- round 4's findings (`gate04-s2b-r4-findings.md`) and resolutions (`resolutions-r4.md`);
- the repair diff from `a588adfe` (`evidence-r5/repair.diff.txt`);
- **the reproducible seal package**:
  - the change classifier's source and output (`declchanges.tsv`, with elaborated signatures as
    well as declaration text);
  - the candidate tables and `unseal.json`;
  - the drivers (`declx.py`, `run_collect.sh`, the collector, the seal and the scanner);
  - the minimization logs;
  - the seal at the head, the plain seal, the `$BASE` control, and the source scan at the head
    and the base;
  - the regenerated exclusions (`exclusions.md`) and the worker's report (`REPORT.md`);
- replay, axioms, lint and the statement diff;
- every Lean file the repair changes, at the head.

**The source** is [PS10], 3rd ed., January 2010: `Pass–Shelat.pdf` at the root of
`cryptography/pass-shelat-ch2-4` (SHA-256
`7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`). Book page = PDF page − 12.

- **The deliverable:** **`gate04-s2b-r5-findings.md`**, committed as
  `inbox/gate04-s2b-r5-findings.md` on the exchange branch `exchange/pass-shelat-ch5-8` and
  pushed (the protocol is that branch's `README.md`: write only that file, `git pull --rebase`
  before pushing, never force-push, no PR).

## Brief for the auditor

1. **Verify round 4's resolutions:** for R4-01, R4-02 and F02, say fixed, recorded or not resolved
   (and why).
2. **Audit the changed surface:**
   - **The classifier.** Does it now detect a statement change that comes from an ambient
     `variable` binder or a universe change, as at `Pseudorandom/Functions/{Defs,GGM,SubHybrids}.lean`?
     Is every declaration it classes changed or added free of exclusions?
   - **The re-proofs.** The twelve declarations of R4-01 (and any others the new classifier found)
     must read no other file's definition and must keep their statements. Any new equation lemma
     (for example, for `randomFunction`) must sit beside its definition, be public, and not be
     `@[simp]`.
   - **The evidence's limits.** The report should describe the result as coverage of the
     collected candidates and the inspected syntax. Check that the scanner now reads `nth_rw`,
     `nth_rewrite` and multi-line `unfold`, that private names are collected, and what the report
     says about `def-aux` bodies. Check that the control is described literally.
   - **Reproducibility.** Can the classification, collection and seal be re-run from the bundled
     drivers and inputs?
3. **Look for regressions.** Do not give a blanket approval.

## Attestations (maintainer; `evidence-r5/`)

- **Change set, elaboration, axioms, lint, statements, seal:** `@FILLED FROM THE REPAIR@`.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Plus one line per item: `R4-01: fixed / recorded / not resolved — <reason>` (also R4-02, F02).
Severity guide as in rounds 1–4. The gate closes at **0 blockers and 0 majors**.
