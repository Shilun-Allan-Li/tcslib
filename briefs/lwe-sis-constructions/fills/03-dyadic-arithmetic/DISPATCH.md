# Dyadic scalar proof audit: prepared, not dispatched

This is a separate job requiring a fresh Codex/Claude choice and user dispatch.
No new reviewer or remote proof-update publication is claimed yet.

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

After choosing the reviewer, run --worker codex or --worker claude as selected:

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

**Not yet clear to merge — proof-audit selection/publication/dispatch,
source-policy work, applicable landing checks and user approval remain.**
