# Encoding-adapter statement audit: Codex dispatched

The user reported dispatch. GitHub confirms draft PR
[#238](https://github.com/Shilun-Allan-Li/tcslib/pull/238), published head
`a3eb3627f3b26b78613a41367221788057ca4142`, targeting
`cryptography/lwe-sis-constructions`. The published exchange input is
`a0b0d03b5694a0e9ab3df3ff6dfdd88ed7326ef4`; the source, bundled records and
bundle identities below are unchanged. The returned statement report passes
0/0/0/3; see `audits/lwe-sis-adapter-statements-{findings,resolutions}.md`.

The separate `dispatch-receipt.json` records the checks. All 101 source hashes,
199 evidence checksums and seven local payload hashes pass. Remote PR/README/
checksum/index metadata were read; this intake did not rehash the entire remote
bundle or rerun Lean. The statement gate now permits only the subsequent audited
proof fill; the issued review packet stays fixed. This intake launches no
external job and performs no merge.

## Historical prepared handoff

The user selected **Codex** for this new statement audit. At preparation time,
dispatch and remote publication were pending. The completed construction-core proof audit is a
different, closed job.

| Item | Prepared identity |
|---|---|
| Lean/root | `6eec97be8f54d9990340900a5595dab32fb477f5` |
| Bundled records | `82f01285d688c09ddbce370a34f20944ba206fb6` |
| Bundle SHA-256 | `5b26dabb5fa78b2f79a778808e79f5483ff0d0b7beb1709af0aee4c86f705b76` |
| Sections / bytes | 844 / 5114602 |
| Prepared local exchange commit | `ac0298925f8408de3112c4a2971ae875fc084cc3` |
| Draft branch | `cryptography/lwe-sis-adapter-statements` |
| Central PR target | `cryptography/lwe-sis-constructions` |

All 844 sections were extracted, hashed and byte-compared with their exact Git
revision/path objects. Both ordered indexes and all five checksums pass. The
prepared local commit is not a published exchange pin. No new remote PR is
claimed until client publication succeeds. The bundle preserves three empty
unified-diff context lines in the unapplied reader proposal, including their
required leading spaces. Authored handoff files pass whitespace checking.

Use `publish_review.py --worker codex` for the selected reviewer, as documented
in README. `--check-only` verifies local
readiness without network access or mutation. The command publishes the records-only
proof-audit intake to #237's own draft branch if still open, pushes only this new
draft ref, creates/updates its draft PR against the central branch, rebases the
private sparse publisher, and pushes only our namespace. It prints the actual
exchange commit and exact kickoff. No central/campaign ref is pushed and no
branch merged; the shared exchange checkout/index is never used.

The user pastes that kickoff into the newly selected auditor chat. The auditor
reads GitHub directly and returns `lwe-sis-adapter-statements-findings.md` as
Markdown in chat. No ZIP attachment is needed. Four earlier scoped gates pass,
but they do not approve these new 14 admitted adapter obligations.

**Not yet clear to merge — the new statement gate and proof fill, retained
source-policy/landing checks and user approval remain outstanding.**
