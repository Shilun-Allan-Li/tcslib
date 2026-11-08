# Construction-core statement gate

Current status: the user dispatched Codex. PR #237 is published at
`1b148307150a0b0a08dd80d68c54ba2db95de13c`; both it and #236 target the central
LWE/SIS branch. The exact input is exchange
`90d652e19508262b3bd81234260d0585aaf8e0a0`. See `dispatch-receipt.json` for
verification. The source remains frozen; findings are pending. The publication
instructions below document the completed handoff and should not be taken as
a request to redispatch the running review.

The eight mathematical modules are frozen at
`a1f1b2e0d9315dff2a8dc36e2a6f8339c0a5abdf`, on top of audited dependency
`0769cba3e44c56700349f954190fc99d9e622270` (PR #236).
The draft branch is `cryptography/lwe-sis-phase1-statements`, targeting the user's
central branch **`cryptography/lwe-sis-constructions`**.

[REPORT.md](REPORT.md) records the scope, exact inventories, native evidence and
continuing obligations. The external pack is
`audits/lwe-sis-core-statements-pack.md`. There are 31 explicit admissions; no
nontrivial proof fill has begun. The prior foundation gates pass, but do not approve
this new statement surface.

The fresh sweep covers 68 modules, with zero errors, 31 new admission warnings and
17 inherited warnings. The final probe reconciles 62 source declarations and 90 new
constants, plus all 166 unchanged foundation constants. Forty-six new constants
depend transitively on the disclosed admissions. Style is 0 FAIL / 2 unchanged
acronym warnings over 18 files. Neither whole-root elaboration nor machine efficiency
is claimed.

Exact Pei16/Wu24 primary PDF bytes are acquired and hashed in the own local archive.
The provenance record provides source versions and page anchors. Reference ingestion
and approved matching remain open; the registry/dataset pipeline was not run.

## Publication and review

`build_review.py` assembles the source/records-pinned text bundle, revision-qualified
index and checksum files in the independent sparse exchange publisher. It does not
push or dispatch. `review-publication.json`, added after assembly, records the prepared
payload hashes and local exchange commit; a prepared commit is not a published pin.

The user selects **Codex or Claude** for each external job and dispatches it.
After selecting the reviewer, run the client-side command with the matching flag:

```sh
python3 -I /Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-lwe-sis-phase1/briefs/lwe-sis-constructions/gates/02-construction-core/publish_review.py --worker codex
```

Use `--worker claude` for Claude. The command verifies the clean source/records
and prepared exchange payload, retargets PR #236 to the central branch, pushes
only this draft branch, creates/updates its draft PR, rebases the independent
exchange publisher and pushes only its owned namespace. It never pushes to a
central/campaign ref, merges, forces, stashes, resets or operates on the shared
exchange checkout/index. Git or PR failures stop publication. `--check-only`
verifies the local prepared payload without network access or mutations.

The successful command prints the draft PR URL, exact exchange commit and complete
reviewer kickoff. Auditors read GitHub directly and return
`lwe-sis-core-statements-findings.md` in chat. No ZIP attachment is needed.
The external pack remains vendor-neutral and frozen; the selected reviewer is
recorded by the explicit client flag/kickoff, not inferred from an older job.

**Not yet clear to merge — the Codex statement audit is dispatched and findings
are pending. The audited Lean surface remains frozen.**
