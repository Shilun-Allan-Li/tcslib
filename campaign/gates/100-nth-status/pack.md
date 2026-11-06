# External audit pack: NTimeHierarchy's Status paragraph (PR #209, a docstring gate)

## Why this PR

`TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean`'s module docstring said that
`Complexity.ntime_hierarchy` "is proved from two contracts that are still `sorry`". Both are now
proved and merged: E-D's `Turing.NTimeDiag.exists_diagonalizer` (#188, gate 93) and NF's
`Turing.FinNDTM.exists_codeNDTM_accepts_linear` (#191, gate 95). Gate 95's axiom prints on the
merged tree (`campaign/gates/95-nf-landing-fill/evidence/round5/axioms/NTHAx.out`) put the
hierarchy and its two corollaries on `[propext, Classical.choice, Quot.sound]`.

**The PR:** #209 on `lean/nth-status`, head `0b05cc3aaf2e48a8b8a676d8c6b7214a61848a06`:
`2029a1be` (`evidence/patches/`), then a records-only merge of the campaign. It changes the
Status paragraph and nothing else.

## Brief for the auditor

1. Is the new Status paragraph true at the campaign after #191, #202 and #207 (the hierarchy, its
   two corollaries and both contracts proved, on the standard axioms)?
2. Does the PR change anything but that paragraph?

## Repository-side attestations (verify or challenge)

- **Freeze** (`evidence/freeze/`): 5 → 5 public, 20 → 20 private, nothing added, removed or
  changed (comment text is not part of a declaration's body).
- **Lint** (`evidence/lint/`): the policy linter's output is identical at base and head.
- **Axioms:** gate 95's `NTHAx.out` (above), on the merged tree.
- **Replay** (`evidence/merged-tree/`): `replay-lnth` at `0b05cc3a`, `NTimeHierarchy` and the
  `Diagonalization` facade, chained from the campaign's snapshot `oleans-lcamp1`: **2 modules, 0
  failed, 0 `sorry`**; static 0 mismatches.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/100-nth-status/findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as `nth-status-findings.md`** (the findings table and the verdict line,
no other wrapping): push it to `arora-barak-ch3-4/inbox/` on the branch
`exchange/pass-shelat-ch5-8` (`git pull --rebase` first, add only that file, never force-push, no
PR), and also paste its content in your reply. If you cannot push, say so and paste it only.
