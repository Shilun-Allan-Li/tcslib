# Codex audit · Gate 25 hash-sign (#308)

Audit draft PR #308 at 4f0280c85fae8730ca0dfad980b41749452980fa using the scope in pack.md. Campaign records are pinned at b01c150512fe6668ee6dddb1c6b429d1b9c822bf.

The bundle contains:
- the pack, the maintainer review, the worker report, policy, the issued brief and the duplication ledger;
- pr.diff.txt, the full diff from the PR base dee0de32ee33d7188afe97bdc3089fac68412057 to the head;
- all ten changed Lean files at the head: Authentication/Signatures/HashAndSign (owned), its eight new helpers
  under HashAndSign/ (CodecReaders, CollisionGame, CollisionHandler, FixedGame, ForwardGame, ForwardHandler,
  OneQuery, OneQuerySampling) and the facade Authentication.

The zips:
- sources.zip: the source closure at the head of every changed module (169 files);
- verification.zip: every file the maintainer review cites, as byte-identical originals: review-evidence.zip and
  ledoc-evidence.zip with their manifests, the landing/ and landing-ledoc/ extracts, the cited records and the
  worker's escalation and authorization records (worker/escalations/, worker/inputs/); its entries are exactly its
  SHA256SUMS plus SHA256SUMS itself.

landing/ holds the logs at the head. The worker's own evidence is on this branch under
inbox/fills/hash-sign/evidence/ (delivery commit 90e4b3c833e5e7fed134941e016724531ad64f1f). Check SHA256SUMS before
using the pack.

Return gate25-hash-sign-findings.md as Markdown in the chat. If you have several evidence files, return a ZIP
containing that Markdown and the evidence. The user dispatches and merges.
