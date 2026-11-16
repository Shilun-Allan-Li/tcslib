# Codex audit · Gate 39 round 2 · seq-zk (#327)

Re-audit draft PR #327 at a94ba750b2f21ea5f2c3e58bc7959ad5ac9de871 using pack-r2.md. Campaign records are pinned at 2c42911bf538feb40d2f124a6cc8c21f0cbe3307.

Round 1 was HOLD (0/1/0/0) at bd19c433a4cf3d4027ffc891d7d3c06e927e9dfa. Its findings are in findings/, and
resolutions-r1.md answers them (G39-01: fixed by LE-gate39, proof only). The round-1 pack is
outbox/gates/39-seq-zk-gate/ at exchange da8f8f66e505a9e27034667ff68a3b104036e84e; pack.md here is its pack.

- le-gate39.diff.txt: git diff bd19c433 a94ba750, the whole of LE-gate39 (RealPrefixBounds.lean, +5/-5).
- landing-r1/: LE-gate39 (G39-01) with its rebuilds, #327 alone on the tip (679 modules) and the final combined tree
  with #324 (26 modules), its seals and axioms: the evidence ZIP with its manifest and PROVENANCE.
- integration/: round 1's combined integration build of all open PRs (records maintainer/int-all-open-2026-11-16/):
  the evidence ZIP with its manifest and PROVENANCE, the reference for the combined-tree rebuild.
- verification-r2.zip: byte-identical originals of the decision log, the duplication ledger, the deferred-work
  register and the seq-zk review, plus checks generated from git objects (the series, the edit, merge trees with the
  tip and the open PRs, downstream, names, the combined tree, source equality, the duplication scans, decls2, the
  evidence read-back) with their scripts; its entries are exactly its SHA256SUMS plus SHA256SUMS itself.
- pr.diff-r2.txt, source-head-r2.json and sources-r2.zip: the diff, hashes and source closure (185 files) at the head.
- bundle.md: the round-2 pack, resolutions, findings, both PROVENANCE files, the round-1 pack, the duplication ledger,
  policy, and at the head RealPrefixBounds.lean and ProofTransfers.lean.

Check SHA256SUMS before using the pack. Return gate39-seq-zk-r2-findings.md as Markdown in the chat. If you have
several evidence files, return a ZIP containing that Markdown and the evidence. The user dispatches and merges.
