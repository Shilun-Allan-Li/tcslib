# Encoding-adapter proof review: prepared, not dispatched

This is a new external job. The completed adapter statement audit's Codex choice
does not select a reviewer for this proof gate. The user freshly selects Codex
or Claude, publishes the inputs and dispatches the review. No new worker has
been selected or dispatched by this preparation.

| Item | Prepared identity |
|---|---|
| Statement freeze | `6eec97be8f54d9990340900a5595dab32fb477f5` |
| Filled Lean/root | `b9ce3521e7f5a15d80e71bf5e9be4c48bc73010e` |
| Bundled records | `223713ba5ea15ac98dc5efedaad5a7208854e3d1` |
| Bundle SHA-256 | `24de3637321750a0ad12ec46120e32d28db102fd4cd77f0b56621e5e4bd16225` |
| Bundle sections / bytes | 1009 / 5711128 |
| Source / records attachments | 101 / 908 |
| Prepared local exchange commit | `ba56e8611eabbdf1adfb43d68cd1cf9d2f42dd27` |
| Draft PR / branch | #238 / `cryptography/lwe-sis-adapter-statements` |
| Central target | `cryptography/lwe-sis-constructions` |
| Exchange gate | `lwe-sis-constructions/outbox/gates/05-encoding-adapter-proofs-r1/` |

All 1009 attachments were extracted, hashed and byte-compared with their exact
Git revision/path objects. Both ordered indexes and all five gate checksums pass.
The evidence checksum set has 146 entries. Three required blank unified-diff
context lines in the unapplied probability-reader proposal remain verbatim;
authored handoff files pass whitespace checking. `review-publication.json`
records these checks and the seven local payload hashes.

The prepared exchange commit is local. No proof-update publication, remote proof
audit input, draft PR title/body update, dispatch or merge is claimed yet.
Earlier exchange gate folders and other namespaces remain unchanged.

After the fresh reviewer choice, use `publish_review.py --worker codex` or
`--worker claude` as selected. The full client path is:

```sh
python3 -I /Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-lwe-sis-adapters/briefs/lwe-sis-constructions/fills/02-encoding-adapters/publish_review.py --check-only
```

`--check-only` verifies local readiness without network access or mutation.
Replace it with the explicitly selected `--worker` argument to publish. The
command pushes only this PR's draft branch, updates #238's title/body, rebases
the private sparse publisher before pushing only this namespace, and prints
the exact immutable GitHub kickoff. It never merges or pushes a central/campaign
ref, changes another checkout or uses the shared exchange checkout/index.

The auditor reads GitHub directly and returns
`lwe-sis-adapter-proofs-findings.md` as Markdown in chat. No ZIP is required.
Keep all Lean/root/pin bytes fixed while this proof gate is pending.

**Not yet clear to merge — proof audit selection/publication/dispatch,
source-policy work, applicable landing checks and user approval remain.**
