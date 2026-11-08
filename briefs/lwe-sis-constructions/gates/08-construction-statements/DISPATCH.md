# Client publication and morning Codex audit

The dyadic scalar proof report has been accepted: PASS, 0 blockers/majors/minors,
three continuing notes. Eight earlier scoped gates now pass. No merge is performed
or requested. The larger statement draft is ready for one combined Codex audit.

## Prepared identities

| Item | Identity |
|---|---|
| Own branch | `cryptography/lwe-sis-construction-statements` |
| Central target | `cryptography/lwe-sis-constructions` |
| Frozen Lean/root | `17b2a282b545c6ebca3fccc88d518d18ae78f485` |
| Bundled records | `03f13bc817f4d281801e2025d3722bcab513c6c0` |
| Bundle SHA-256 | `04b19eff425cc268426662a4352f2be4cfa96a97d965a559c1f82f2e51444d8d` |
| Sections / bytes | 2,395 / 18,418,400 |
| Source / record attachments | 153 / 2,242 |
| Owned gate path | `lwe-sis-constructions/outbox/gates/08-construction-statements-r1/` |
| Reviewer | Codex, preselected by the user for morning audits |

All five exchange checksums and both ordered indexes pass. The extractor recovers
every indexed byte; all 2,395 revision/path Git blobs match their attachment.
The private publisher's prepared commit is recorded in `review-publication.json`;
it is **not a remote publication identity** and may change when rebased. The helper
prints the actual pushed exchange commit and actual new draft PR number.

## Run on the client

Shell publication remains unavailable in the sandbox because GitHub DNS fails;
the connector's earlier write attempts returned HTTP 403. The user offered client
publication. This command uses the client's existing Git/gh credentials:

```sh
python3 -I ~/phd_experiments/tcslib_all_branches/tcslib-lwe-sis-construction-statements/briefs/lwe-sis-constructions/gates/08-construction-statements/publish_review.py --worker codex
```

It checks the clean own checkout, 153 frozen source hashes and seven exact owned
payload hashes, then pushes only the own feature branch and creates or updates a
**draft PR targeting `cryptography/lwe-sis-constructions`**. The existing dependency
PRs #236–#239 are not merged or edited by this helper. It rebases the separate
private publisher onto the remote exchange before pushing, refuses pending paths
outside `lwe-sis-constructions/`, and never uses the shared exchange checkout.
No force-push, stash, reset, central push, merge or worker dispatch is performed.

If a rebase conflicts or a remote operation fails, publication stops. Inspect
that failure and any completed feature-PR step; do not bypass its guards. The
helper can be rerun after the issue is resolved and discovers an existing draft
instead of creating a duplicate. Its local-only verification is available with
`--check-only`. Five in-memory scenarios exercise creation/update and rejection
of a non-draft PR or a foreign exchange path; they perform no remote action.

## Dispatch after publication

Paste the helper's printed kickoff into a fresh **Codex** auditor chat. The auditor
reads the pinned GitHub exchange inputs directly and returns
`lwe-sis-constructions-statements-findings.md` as Markdown in chat. No ZIP is needed.
Do not use the unpublished prepared exchange hash as an audit input.

The combined audit covers all 19 mathematical modules, 220 declarations, 101
admitted obligations/sketches, 62 closed source readers, 40 generated readers,
13 compiler auxiliaries, all 575 owned constants and 48 backing contracts. Ask
the auditor to assess the exact unapplied reader/catalogue proposals too.
Affected fills remain paused; the independent construction statements are ready
for review. Neither preparation nor publication dispatches the job.

After findings return, preserve the complete Markdown report verbatim, verify its
pins/checksums, record dispositions and repair/re-audit any blockers or majors.
Only then plan larger proof batches against the frozen statements. Do not treat
a statement PASS as proof completion, source-policy closure or merge approval.

**Ready to run — client publication prepares the remote draft and prints the
combined Codex kickoff. The user dispatches; nothing is clear to merge yet.**
