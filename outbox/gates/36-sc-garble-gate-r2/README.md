# Codex audit · Gate 36 round 2 · sc-garble (#323)

Re-audit draft PR #323 at 8c3f3e3fe2912784f680c10f8c478d2eeeeb7f6a using pack-r2.md. Campaign records are pinned at 298338e34bb6a4c1754d406244ceeed7e8be6338.

Round 1 was HOLD (0/1/0/0) at cd9a48438c2a6548fe9e246ce569be57c9df96b3. Its finding is in findings/, and
resolutions-r1.md answers it (G36-01 fixed by LE-gate36). The round-1 pack is outbox/gates/36-sc-garble-gate/ at
exchange ab34c528748af26491d896e0f504373b45e4ada1; pack.md here is its pack.

- landing-r1/: LE-gate36 (G36-01) and #323's integration build against the merged #313, done on a scratch replica of
  the branch rebased onto the tip with the same patch: the evidence ZIP with its manifest and PROVENANCE. The pushed
  head is that patch on the round-1 head, not rebased; merging it into the tip gives exactly the built tree
  (pack-r2.md, section 2).
- verification-r2.zip: byte-identical originals of the decision log, the duplication ledger, the sc-garble review and
  the int-313-323-324 PROVENANCE, plus checks generated from git objects (merge trees with the tip and every other
  open PR, downstream, source equality, names, the replica, the series, the edit, the duplication scan, decls2) with
  their scripts; its entries are exactly its SHA256SUMS plus SHA256SUMS itself.
- pr.diff-r2.txt, source-head-r2.json and sources-r2.zip: the diff, hashes and source closure (167 files) at the head.
- bundle.md: the round-2 pack, resolutions, findings, the PROVENANCE, the round-1 pack, the duplication ledger,
  policy, and at the head SpecialEncryptionMulti/SliceParser.lean and Asymptotic/BlockEncryptor.lean.

Check SHA256SUMS before using the pack. Return gate36-sc-garble-r2-findings.md as Markdown in the chat. If you have
several evidence files, return a ZIP containing that Markdown and the evidence. The user dispatches and merges.
