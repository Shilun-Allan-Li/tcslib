# Construction-core proof fill

All 31 audited obligations are proved at
`690217cc1aaefe411158808a8b0797fd887a8abc`, preserving the 62 source declarations
and every audited definition/signature from
`a1f1b2e0d9315dff2a8dc36e2a6f8339c0a5abdf`. Existing draft PR #237 targets
`cryptography/lwe-sis-constructions` and depends on audited PR #236.

[REPORT.md](REPORT.md) records the proof routes, reuse, exact inventories and
continuing obligations. `evidence/summary.json` reconciles a fresh serial 68-module
sweep (zero owned admissions, 17 inherited warnings), all 263 owned constants
without sorryAx, the 31-body source freeze, and 0 FAIL / 2 unchanged style WARNs.
The whole library root was not built. The statement evidence and issued reports
remain unchanged.

Only root edited and ran native jobs. Two internal agents supplied read-only
research. Iteration used the own `.lake/phase1-oleans`; final verification used a
new `.lake/core-fill-final-oleans` tree. Checks ran one module at a time through
`scripts/lean_check_tree.sh`, with existing own pinned packages and no cache fetch.

## Proof review

Current status: the user dispatched the proof audit. GitHub verifies the code
head/central target and gate metadata at exchange
`aaeb9b3764e7fa3c2d4f3e93905e8654ea1786f5`. See `dispatch-receipt.json`.
The frozen Lean/root and packet are unchanged. Do not redispatch this running job.

The vendor-neutral pack is `audits/lwe-sis-core-proofs-pack.md`. The prepared
GitHub input belongs under the owned orphan-exchange namespace
`lwe-sis-constructions/outbox/gates/03-construction-core-proofs-r1/`.
`build_review.py` assembles source/records-pinned inputs; it neither publishes
nor dispatches. The publication receipt distinguishes prepared local commits
from remotely published pins.

The user chooses **Codex or Claude** for this new proof audit and dispatches it.
Once chosen, run the client command with that explicit flag:

```sh
python3 -I /Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-lwe-sis-phase1/briefs/lwe-sis-constructions/fills/01-construction-core/publish_review.py --worker codex
```

Use `--worker claude` for Claude. `--check-only` verifies local preparation without
network access or mutation. The command pushes only our existing draft ref,
updates draft PR #237, rebases the private sparse publisher before pushing only
the owned namespace, and prints the exact GitHub kickoff. It never merges or
pushes to a central/campaign branch, and never uses the shared exchange checkout.
Auditors read GitHub directly and return `lwe-sis-core-proofs-findings.md` as
Markdown in chat. No ZIP is required. The command above documents the completed handoff, not a redispatch request.

**Not yet clear to merge — the proof audit, source-policy work, relevant landing
checks and user approval remain open.**
