# Codex representation-proof review

The user freshly selected Codex. Input is read directly from GitHub on the exchange;
output is `lwe-sis-encoding-proofs-findings.md` as Markdown in chat. The user dispatches
the job. No external proof-review execution, verdict or merge is claimed here.

| Item | Identity |
|---|---|
| Statement freeze | `4364d0e0fe9accd649b6acb4751e8684aa93ad1e` |
| Filled source | `893e921bf2afeca293be9da9d495613bb1486796` |
| Bundled records | `7a9dfa6bf05eebb9ea736067351be3cbb438857c` |
| New code PR branch | `cryptography/lwe-sis-encoding-proofs` |
| PR target | `cryptography/pass-shelat-ch2-4` |
| Gate | `lwe-sis-constructions/outbox/gates/01-encoding-proofs-r1/` |
| Bundle SHA-256 | `2f8308efa0f737d09cf9554c45407855b76756ee73a2d9fe28fa582962a49ff0` |
| Bundle Git blob | `3fd06f3dbc45afb56b67578752528cd9cd33bc6a` |
| Bundle size / sections | 3,033,293 bytes / 259 |

The seven publication paths are prepared in the independent sparse publisher clone.
Their hashes are in `review-publication.json`. Local exchange commit
`ebe777ba3bf904f6a6909aaf8b931fcb0c53f358` is a prepared commit, **not a published pin**;
rebasing before publication may change it. Use the successful command's printed pin.
All 259 original attachments were extracted and checked against the revision-qualified
index before this publication was prepared. No ZIP attachment is needed.

## Client publication

Shell GitHub access still fails DNS, and connector draft-PR creation returned HTTP 403.
Run from any directory with the client's ordinary Git/GitHub CLI credentials:

```sh
python3 -I /Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-crypto-parallel-kickoff/briefs/lwe-sis-constructions/fills/00-encodings/publish_review.py
```

The command verifies the clean own checkout, frozen source, intended branch/remotes and
payload hashes; pushes **only the new PR branch**; creates or updates its draft PR;
rebases **only the separate exchange clone**; verifies pending changes are confined to
`lwe-sis-constructions/`; and pushes the exchange input. It does not update the earlier
`cryptography/lwe-sis-constructions` ref or any campaign ref, merge, force, reset, stash
or operate on the shared exchange checkout/index. Git or PR errors stop publication.

After success it prints the draft PR URL, exact exchange commit, README permalink and
complete Codex kickoff. Paste that kickoff into a fresh Codex chat; the user dispatches
the audit. The source and records pins above remain unchanged by exchange rebasing.

## Scope and hold

The review covers 14 completed representation proofs, unchanged interfaces and the
verification evidence. It does not fill a primitive construction, close source archival,
certify the 17 inherited admission sites, or approve a merge. The earlier external
statement PASS 0/0/0/3 and its three notes remain verbatim in the packet.

**Ready to run — the PR and exchange publication are prepared; external proof review,
source archival and user-controlled integration remain outstanding.**
