# Codex audit · Gate 31 prf-long (#315)

Audit draft PR #315 at fbd37f447596d4207c8d08b7ef7602f57fe95198 using the scope in pack.md: a machinery audit of the PRF machinery at l(n)-bit outputs (D1-D4, ruling B3; no admitted
target), with the landing edits LE-doc (docstrings only) and LE-ws (whitespace only).
Campaign records are pinned at 9cc4db6204a9965da907471603993e9c24d105d2.

The bundle contains the pack, the maintainer review, the worker report, policy, the issued brief, the duplication
  ledger and Gate 27's resolutions (the hand-off); pr.diff.txt; the six changed Lean files at the head
  (Asymptotic/Defs, FromPRF/{Hybrid,ReductionMachine,MultiMsgOut}, the FromPRF and PrivateKey facades)
  and, as context at the head, FromPRF/HybridLemmas (owned, unchanged) and the consumer side:
  SecureComputation/SpecialEncryptionMulti (the merged B1 statement), SpecialEncryptionSecurity
  (PRFOut, spDecStr_wrongKey) and SpecialEncryption (spEncStr).

Also:
- pr.diff.txt: the full diff from the PR base dd98360d4886ac68fab34899b8bd0d12ae9a0aef to the head;
- pr-description.md: the PR description as opened on GitHub;
- source-head.json: the head hashes, line counts and over-width counts of the changed files;
- sources.zip: the source closure at the head of every changed module (180 files);
- verification.zip: every file the review cites, as byte-identical originals: review-evidence.zip
  with its manifest, the landing extracts, evidence extracts, the cited records, the worker extracts
  (worker/) and the pack's git-object re-checks (pack-checks/); its entries are exactly its
  SHA256SUMS plus SHA256SUMS (96 entries).

landing/ holds the logs at the head. The worker's own evidence is on this branch under
inbox/fills/prf-long/ (delivery commit 8d44fa5b5cdd408b9361364a246697dc294151fb).
Check SHA256SUMS before using the pack.

Return gate31-prf-long-findings.md as Markdown in the chat. If you have several evidence files, return a ZIP
containing that Markdown and the evidence. The user dispatches and merges.
