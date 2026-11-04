# External audit pack, round 2: four space facts out of `Machines/ARMWidth` (PR #181, an API gate)

**Round 1** (`pack.md`, at `50adf098`; findings `findings.md`): **OPEN, 0 blockers, 1 major, 1
minor, 6 notes.** The resolutions are in `resolutions.md`.
- **Major 1:** LS-1 was not fully retired. Two inline copies of `logSpace n ≤ n + 1` survived
  outside the acknowledged scope:
  - `narm_decides` (`Machines/NARMProof`);
  - `narm_logspace_ptm` (`Machines/NARMLogspace`).
- **Minor 2:** the screen base's status file named a local commit (`2219912d`, on worktree
  `wt-edis`), not the pack's `711f5444`.

**The PR now:** #181 on `lean/logspace-move`, head `5de52d9aa76c22a4317b6ba83dcd4634c8ef36eb`. It
holds round 1's commits, the fix commit `1d1247a3` (`evidence/round2/patches/`) and a merge of the
campaign's later records commits, which changes no Lean. Against the campaign, #181 now changes six
files: round 1's four, plus `Machines/NARMProof` and `Machines/NARMLogspace`.

## What changed since round 1 (verify)

| File · declaration | Change |
|---|---|
| `Machines/NARMProof` · `Complexity.LogProg.narm_decides` | `have hLn : logSpace n ≤ n + 1 := by have := Nat.log_le_self 2 n; simp only [logSpace]; omega` becomes `have hLn : logSpace n ≤ n + 1 := logSpace_le_succ n` |
| `Machines/NARMLogspace` · `Complexity.LogProg.narm_logspace_ptm` | the same replacement |

Both files are Hydroxyi's. The edit is a mechanical deduplication edit to the ARM files, within the
standing exception (FYI to the author). The freeze (`evidence/round2/freeze/`) finds no public or
private declaration added or removed, and no statement changed. The only body changes are the two
named, which are authorized. The re-points also remove an unfolding of `logSpace`, `Basic`'s
definition, from each proof.

## Brief for the auditor

1. **Major 1, retired?**
   - Are the two re-points correct?
   - Does any copy of the fact remain anywhere in the tree? `evidence/round2/ls1-search/ls1-search.txt`
     greps the round-2 head for statements of a `logSpace` bound by a successor, for
     `Nat.log_le_self` beside `logSpace`, and for the citations of `logSpace_le_succ`. The fact is
     stated only in `Basic`. The other hits are different facts:
     - `Randomized/BPLInP`'s `logSpace n ≤ |bits n| + 1`;
     - `ImplicitPoly`'s and `Logspace/PreimageHost`'s polylogarithmic bounds.

     Are those classifications right?
   - Is the ledger's corrected LS-1 entry (`campaign/duplication-ledger.md`) accurate?
2. **Minor 2.** `evidence/round2/screen/round1-base-provenance.txt` lists the 14 population blobs at
   `2219912d` and at `711f5444`: all are equal. Round 2's base screen runs on a `git archive` export
   of `711f5444` itself (`screen-base.status`). Is that sufficient?
3. **The screen, round 2** (`evidence/round2/screen/`): 15 files, round 1's 14 and `NARMLogspace`.
   Base `711f5444`, head `5de52d9a`: SCREEN-R2. Is any pair new or gone?
4. **Unchanged from round 1:** the four moved declarations, their homes, imports, users, rule-10
   evidence and census. Confirm that the round-2 commit touches none of them.

## Repository-side attestations (verify or challenge)

- **Elaboration** (`evidence/round2/elab/`): `NARMProof` and `NARMLogspace` at the round-2 commit,
  against `oleans-lsm1` (the round-1 head's fresh snapshot; the two files' imports are unchanged):
  0 diagnostics each.
- **Replay:** `replay-lsm2.sh` (`evidence/round2/merged-tree/`), the six files' downstream closure,
  137 modules, fresh `.olean`s from `oleans-leqc3`, pinning the six blobs. Precheck passed;
  **not yet run.**
- **Overlap with #182** (gate 90, `replay-larm`): both closures contain `Machines/ARMWidth`'s users.
  Whichever of #181 and #182 merges second takes a merged-tree replay of the overlap.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/89-space-facts-api/findings-r2.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `space-facts-api-r2-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
