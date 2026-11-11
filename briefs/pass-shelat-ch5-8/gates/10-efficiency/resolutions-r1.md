# Gate 10 (efficiency proofs, PR #285): round 1 resolutions — CLOSED

- **Findings:** `findings/gate10-efficiency-findings.md`, the original local Markdown returned by the Codex
  auditor in chat (route recorded in `findings/provenance.md`), preserved verbatim. SHA-256
  `936561d873c26e8c56c9a52342ada419c32aedbb91633ad2e2e6517ee0cefc05`, re-verified on intake against `findings/SHA256SUMS`.
- **Verdict: CLEAR — 0 blockers, 0 majors, 0 minors, 0 notes.** Gate 10 closes at
  [PR #285](https://github.com/Shilun-Allan-Li/tcslib/pull/285) head `747cc18ddb53979919d107fefed450191eb31743`.

## Intake checks (cloud maintainer, 2026-11-11)

| Pin in the report | Check | Result |
|---|---|---|
| Lean head `747cc18ddb53979919d107fefed450191eb31743` | live head of `codex/pass-shelat-efficiency-proof` and of PR #285 | match |
| PR base `e226b470e25cb08a9fe8b10f9f5dd54fc55c1808` | `git merge-base` with the campaign; ancestor of the campaign head | match |
| No Lean or checker change on the campaign since the PR base | `git diff e226b470..campaign -- TCSlib audits scripts lakefile.lean lean-toolchain lake-manifest.json` | empty |
| Records `5bcf11aaf08963ab33ce608ea7509e7403e4351a` | ancestor of the campaign head | yes |
| Exchange `f5054f40b2df67c04f47354f5cfeccde704e3440` | the staged pack commit (`dispatch.md`); live exchange head at intake | match |
| Findings bytes | `sha256sum` against `findings/SHA256SUMS` | match |
| File overlap with the other open PRs (#284, #286) | `git diff --name-only` of each against its merge base | none |

## Disposition

- No findings to resolve. The report's **verification boundary** is accepted as stated: the auditor
  checked provenance, hashes, source arguments, seal/control/scan coverage and evidence consistency
  independently, and relied on the maintainer's archived native Lean results (`verification.md`,
  `verification.zip`) for elaboration.
- The approved **72 historical provider diagnostic/declaration pairs** stay deferred cleanup (the
  user's scoped approval, decision log 2026-11-10); this gate does not clear them.
- The source is unchanged since the audited head, so no further verification is owed before merge.
- Shared-helper consolidation requests disclosed by the worker remain follow-up work under the
  issued design.

**Clear to merge** — [#285](https://github.com/Shilun-Allan-Li/tcslib/pull/285) at `747cc18ddb53979919d107fefed450191eb31743`; the user merges.
