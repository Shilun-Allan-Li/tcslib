# Codex audit · Gate 36 sc-garble (#323)

Audit draft PR #323 at cd9a48438c2a6548fe9e246ce569be57c9df96b3 using the scope in pack.md: a proof audit of the seven sc-garble targets (spDecStr_wrongKey, specialScheme_wrongKey,
specialScheme_multiMessageSecure, nestedSpecial_wrongKeyBot, uprob_not_good_le, yaoSeed_good_whp,
sliceMultiMessageSecure_of_prfOut) and the garbling bound B2 [PS10, §6.2.2-6.2.3], under ruling SG-1,
with the one approved frozen-file reader DAGCircuit.isFaninTwo_iff and the landing edit LE-doc
(docstrings only).
Campaign records are pinned at fb18d199fdce1f8cd1ae94ea9e092c52b157ce86.

The bundle contains the pack, the maintainer review, the worker report, policy, the issued brief, ruling SG-1, the
  duplication ledger (DL-46, DL-47 with SG-F04), the review's PROVENANCE and Gate 27's resolutions
  (the hand-off obligations); pr-description.md and pr.diff.txt; the 13 changed SecureComputation
  files at the head (the DAGCircuit hunk is in pr.diff.txt and the file in sources.zip); and, as
  context at the head, SecureComputation/SpecialEncryption, SecureComputation/GarblingSpecial and
  Encryption/PrivateKey/FromPRF/MultiMsgOut (D4).

Also:
- pr.diff.txt: the full diff from the PR base 1321b9cb358867f5b51974b8c5d0781519a9cfdb to the head;
- pr-description.md: the PR description as opened on GitHub;
- source-head.json: the head hashes, line counts and over-width counts of the changed files;
- sources.zip: the source closure at the head of every changed module (166 files);
- verification.zip: every file the review cites and the pack uses, as byte-identical originals:
  review-evidence.zip with its manifest, the review's PROVENANCE, the cited records, evidence extracts,
  the worker extracts (worker/) and the pack's git-object re-checks (pack-checks/); its entries are
  exactly its SHA256SUMS plus SHA256SUMS (147 entries).

landing/ holds byte copies of review-evidence entries (the builds, the census, the frozen check, the tree check). The
worker's own evidence is on this branch under inbox/fills/sc-garble/ (delivery commit a73072f19787ee437f2201777711c7eb3154c714).

Check SHA256SUMS before using the pack.

Return gate36-sc-garble-findings.md as Markdown in the chat. If you have several evidence files, return a ZIP
containing that Markdown and the evidence. The user dispatches and merges.
