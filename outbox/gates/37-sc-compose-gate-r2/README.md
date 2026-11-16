# Codex audit · Gate 37 round 2 · sc-compose (#324)

Re-audit draft PR #324 at 4bd2d80bfb58fab5243c66c9f1a697a30b533756 using pack-r2.md. Campaign records are pinned at 4de7ff85bfb4eaa53b4531218fca44fdf7cd64e2.

Round 1 was HOLD (0/2/1) at a6eaebd78c48e7fdfd06263edb84b70bc00ec593. Its findings are in findings/, and
resolutions-r1.md answers them (G37-01/02: re-point via import, Seyoon's ruling; G37-03: docstrings). The round-1
pack is outbox/gates/37-sc-compose-gate/ at exchange 5fab5874b1411ab7a4f8343e6dd4e1add234516b; pack.md here is its
pack.

- landing-r1/: LE-gate37 (G37-01/02/03) and its 21-module rebuild on the combined tree: the evidence ZIP with its
  manifest and PROVENANCE. LE-gate37 also qualifies three uses of splitCoins in Runs.lean (pack-r2.md, section 2).
- integration/: the combined integration build of all open PRs (records maintainer/int-all-open-2026-11-16/): the
  evidence ZIP with its manifest and PROVENANCE. Merging the open heads onto the current tip, in any order, gives
  exactly its TCSlib and audits trees (pack, merge interaction).
- verification-r2.zip: byte-identical originals of the decision log, the duplication ledger, the deferred-work
  register and the sc-compose review, plus checks generated from git objects (merge trees with the tip, the other
  open PRs and the merged heads, downstream, names, the integration build against the current tip, source equality,
  the series, the edit, the splitCoins qualification, the formulas, the duplication scans, decls2) with their
  scripts; its entries are exactly its SHA256SUMS plus SHA256SUMS itself.
- pr.diff-r2.txt, source-head-r2.json and sources-r2.zip: the diff, hashes and source closure (145 files) at the head.
- bundle.md: the round-2 pack, resolutions, findings, both PROVENANCE files, the round-1 pack, the duplication ledger,
  policy, and at the head the ten files LE-gate37 edits and ZeroKnowledge/CommitmentLemmas.lean.

Check SHA256SUMS before using the pack. Return gate37-sc-compose-r2-findings.md as Markdown in the chat. If you have
several evidence files, return a ZIP containing that Markdown and the evidence. The user dispatches and merges.
