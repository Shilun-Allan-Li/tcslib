# Construction-core proof audit: prepared for user selection

No reviewer has been selected and no job has been dispatched for this new gate.
The earlier Codex choice applied to the completed statement audit only.

| Item | Prepared identity |
|---|---|
| Frozen Lean/root | `690217cc1aaefe411158808a8b0797fd887a8abc` |
| Bundled records | `42a400a1b88eecf9172a91ba287894450c72f9b0` |
| Bundle SHA-256 | `aacf0fbca7b937172888910ac1eb7129a294cdcd3280661842042f2a940f658e` |
| Sections / bytes | 593 / 4108601 |
| Prepared local exchange commit | `aaeb9b3764e7fa3c2d4f3e93905e8654ea1786f5` |
| Central PR target | `cryptography/lwe-sis-constructions` |

All 593 sections were extracted, hashed and byte-compared with their exact Git
revision/path objects. Both ordered indexes and all five gate checksums pass.
The local exchange commit is not a remote publication pin. Code and inputs
still require client publication before a reviewer can read them on GitHub.

Select **Codex or Claude** for this proof audit. Run `publish_review.py` with the
matching `--worker codex` or `--worker claude` flag, using the command in README.
It checks the clean own checkout and all payload/source hashes, pushes only our
existing draft branch, updates draft PR #237, then rebases the private sparse
publisher and pushes its owned namespace to the orphan exchange. It prints the
exact resulting GitHub commit and complete reviewer kickoff. It never merges,
pushes to the central/campaign branch, or touches the shared exchange checkout.

The user pastes that printed kickoff into the freshly selected auditor chat.
The auditor reads GitHub directly and returns
`lwe-sis-core-proofs-findings.md` as Markdown in chat. No ZIP is required.

**Not yet clear to merge — publication, proof audit, source-policy work, relevant
landing checks and user approval remain outstanding.**
