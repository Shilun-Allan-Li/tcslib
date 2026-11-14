# Codex audit · Gate 24 round 2 · dl-crh (#307)

Re-audit draft PR #307 at d356381aadc350860f9a0e97123e84d9aefa585b using pack-r2.md. Campaign records are pinned at a518558d26988753261c73b436c4493adbc16cb0.

Round 1 was HOLD (0/1/2/0). Its findings are in findings/, and resolutions-r1.md answers them. The round-1 pack is
outbox/gates/24-dl-crh-gate/ at exchange e7b9e53e4a41ffa84b52deb17d34d144877d31f3; pack.md here is its pack.

- landing-r1/: LE-reuse (G24-01). It holds the patch, PROVENANCE.txt, and the complete evidence ZIP with its
  manifest evidence-SHA256SUMS.
- trial-merge-r1/: the two trial-merge builds of #307 onto the merged tip (after #308 and #309, then after #306 as
  well), each a ZIP with its manifest and PROVENANCE.
- verification-r2.zip: byte-identical originals of the review with its errata (G24-02) and its pinned round-1 copy,
  the decision log, the duplication ledger and the combined-308-309 record the trial merges use as per-PR reference;
  its entries are exactly its SHA256SUMS plus SHA256SUMS itself.
- pr.diff-r2.txt, source-head-r2.json and sources-r2.zip: the diff, hashes and source closure (128 files) at the new
  head.
- bundle.md: the round-2 pack, resolutions, findings, the LE-reuse patch and PROVENANCE, both trial PROVENANCE
  files, the review with its errata, the combined-308-309 README, the round-1 pack, and Encoding.lean and
  ReductionSupport.lean at the head.

Check SHA256SUMS before using the pack. Return gate24-dl-crh-r2-findings.md as Markdown in the chat. If you have
several evidence files, return a ZIP containing that Markdown and the evidence. The user dispatches and merges.
