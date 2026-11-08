# Dyadic scalar proof audit: returned PASS

The user selected and dispatched Codex for this separate proof audit. Published
exchange `083448cef9229dc95b96ef45686ce7f3768992ab` and PR head
`d3c762d121b15fd0ca6a990a98c1f8d92d2e308f` are verified. The returned audit
passes 0/0/0/3; see the retained report and dispositions under audits/.
The preparation and command below are historical; no rerun is needed.

| Item | Prepared identity |
|---|---|
| Statement freeze | `dbacd91218c19f0df106d316ce4ff0e22b869e66` |
| Filled Lean/root | `ec72ed773a690c17ac253707350935cc9e0acb34` |
| Bundled records | `a9b97213c616ef7afe80dcaa57eb5a503cf6b110` |
| Bundle SHA-256 | `a252af465a90beab319c27c32b25edafe712f8f105d7969f71b2cbeb98b692d4` |
| Sections / bytes | 1301 / 6699026 |
| Source / records attachments | 102 / 1199 |
| Prepared local exchange commit | `083448cef9229dc95b96ef45686ce7f3768992ab` |
| PR / central target | #239 / cryptography/lwe-sis-constructions |

All 1301 sections are extracted, hashed and byte-compared with exact Git
revision/path blobs. Both ordered indexes and all five checksums pass; the
proof evidence has 130 checksum entries. Three required unified-diff context
lines remain verbatim. Authored handoff files pass whitespace checking.

The first unissued local preparation is preserved in Git history and marked
superseded: the client helper checked 102 files but printed a static 101. Its
status count is now dynamic. The Lean source and native evidence did not change.
This prepared local exchange pin is not a remote-publication attestation.

Publish the fixed inputs for the selected Codex reviewer:

```sh
python3 -I /Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-lwe-sis-dyadic-arithmetic/briefs/lwe-sis-constructions/fills/03-dyadic-arithmetic/publish_review.py --worker codex
```

--check-only verifies local readiness without network or mutation. Publication
updates only the own PR branch/title/body, rebases the private publisher before
pushing this namespace and prints the actual immutable GitHub kickoff. The user
dispatches it. No central ref is pushed, branch merged or shared exchange
checkout/index used. Read GitHub directly; return
lwe-sis-dyadic-arithmetic-proofs-findings.md as Markdown in chat. No ZIP needed.
Keep source/root/pin bytes fixed while proof review is pending.

**Not yet clear to merge — the proof audit passes; source-policy work,
applicable landing checks and user approval remain.**
