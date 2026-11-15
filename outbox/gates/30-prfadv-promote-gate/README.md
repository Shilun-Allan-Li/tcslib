# Codex audit · Gate 30 prfadv-promote (#314)

Audit draft PR #314 at 5757bc0604527602d790a1a57e9703374ce02c7b using the scope in pack.md: a promotion audit of TCSlib.Cryptography.prfAdv_eq_expect (ruling F-01, DL-44) and the
proof-only re-derivation of ETTGame.prfAdv_eq_expect.
Campaign records are pinned at 7bd85992f8bd61df48f43092bc5c845d5fac1b27.

The bundle contains the pack, policy, the prf-mac review (F-01), the duplication ledger, the records PR draft
  pr-body.md and the opened description pr-description.md; pr.diff.txt; the two changed Lean files
  at the head (Pseudorandom/Functions/Defs, EncryptThenTag/Reduction) and, as context at the head,
  Games/Bridges/Experiments (the new import) and Encryption/PrivateKey/OracleFromPRF (the deferred
  private copy).

Also:
- pr.diff.txt: the full diff from the PR base 8aefdab4cdb372d0787a9be83bc65f1567ceb8b4 to the head;
- pr-description.md: the PR description as opened on GitHub;
- source-head.json: the head hashes, line counts and over-width counts of the changed files;
- sources.zip: the source closure at the head of every changed module (164 files);
- verification.zip: the maintainer's evidence promote-prfadv-evidence.zip with its manifest, the
  cited records and byte copies of the evidence entries the pack cites, as byte-identical originals;
  its entries are exactly its SHA256SUMS plus SHA256SUMS (38 entries).

landing/ holds the logs at the head.
Check SHA256SUMS before using the pack.

Return gate30-prfadv-promote-findings.md as Markdown in the chat. If you have several evidence files, return a ZIP
containing that Markdown and the evidence. The user dispatches and merges.
