# Codex audit · Gate 34 round 2 · sc-ot (#318)

Re-audit draft PR #318 at b0bad23ae611983e3323460bb8c564da90ad6e8c using pack-r2.md. Campaign records are pinned at 4c95a8437dec980209d12327e6208c5ae967e178.

Round 1 was HOLD (0/2/0/0) at f62a25b3eda099c9cf9371900664752e7b89007d. Its findings are in findings/, and
resolutions-r1.md answers them (G34-01 fixed by LE-gate34; G34-02 ledger debt, DL-48). The round-1 pack is
outbox/gates/34-sc-ot-gate/ at exchange a74d11833a0814bb686a4b961c5712957008d6a9; pack.md here is its pack.

- landing-r1/: LE-gate34 (G34-01), the rebase onto 05d26fe5 and #318's integration build against #314-#317: the
  evidence ZIP with its manifest and PROVENANCE.
- verification-r2.zip: byte-identical originals of the decision log, the duplication ledger and the sc-ot review,
  plus checks generated from git objects (merge trees with the tip and every other open PR, downstream, source
  equality, names, the rebase, the edit, the base move, DL-48, the duplication scan, decls2) with their scripts; its
  entries are exactly its SHA256SUMS plus SHA256SUMS itself.
- pr.diff-r2.txt, source-head-r2.json and sources-r2.zip: the diff, hashes and source closure (128 files) at the head.
- bundle.md: the round-2 pack, resolutions, findings, the PROVENANCE, the round-1 pack, the duplication ledger,
  policy, and at the head ObliviousTransfer/Efficiency.lean, Foundations/BitLists.lean,
  ObliviousTransfer/Simulators.lean and NonMalleability/Simulation/Rounds.lean.

Check SHA256SUMS before using the pack. Return gate34-sc-ot-r2-findings.md as Markdown in the chat. If you have
several evidence files, return a ZIP containing that Markdown and the evidence. The user dispatches and merges.
