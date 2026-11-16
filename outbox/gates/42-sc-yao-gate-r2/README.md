# Codex audit · Gate 42 round 2 · sc-yao (#341)

Re-audit draft PR #341 at 355a0288d56290e8c984228cbc1824187029e456 using pack-r2.md. Campaign records are pinned at
2da7e0f3cd65ec93ed71813b7828c3b66ba18942.

Round 1 was HOLD (0 blockers, 1 major, 2 minors) at e9b03c437aca251846430ff23b40ee5ff3d3347a, with no mathematical gap. Its
findings are in findings/, and resolutions-r1.md answers them with three landing edits on that head: LE-reuse-2
(G42-01, proof-only: RunWithHost.acc_poly from the public StateLoop.MajLoop.acc_poly through the readers acc_eq and
MajLoop.acc_eq), LE-refs (G42-02, the full AB09 and BMR90 entries) and LE-steps (G42-03, step comments in six proofs).
The round-1 pack is outbox/gates/42-sc-yao-gate/ at exchange 747b61e7d95d44461639c5884aed33aa4908fc00; pack.md here is its
pack. The earlier rulings (SY-F01 to SY-F05; DL-49, DL-51, DL-52) stand.

- pr-r2.diff.txt: git diff e9b03c43..355a0288, the three landing edits (9 files, +69/-3).
- pr.diff-r2.txt, source-head-r2.json and sources-r2.zip: the diff from the PR base
  f9fda8fe8d11fc68c233df2979a86d356ddfe1ab (70 paths, as in round 1), the hashes at the head, and the 9 files changed
  since round 1 (with round 1's sources.zip, the source closure at the head).
- verification-r2.zip: checks generated from git objects and the committed integration evidence, with their scripts
  (the landing edits, the declarations, the frozen check of Yao.lean, the step comments, the references, the
  integration evidence and its binding, the source closure, the merge-trees, the lint); a pointer to the integration
  evidence ZIP at the records pin and byte copies of the entries the pack cites; the round-1 findings, resolutions and
  dispatch, the plan and its decision-log extract; and the PR's REST fields. Its entries are exactly its SHA256SUMS
  plus SHA256SUMS itself.
- pr-description-r2.md: #341's description as it stands.
- bundle.md: the round-2 pack, resolutions, round-1 findings, the PR description, the integration README, the
  decision-log extract, the checks, the round-1 -> round-2 diff, the 9 changed Lean files and StringLoops.lean at the
  head, policy.md and the round-1 pack. Each section header names its path and source; BUNDLE-FILES.txt lists them.

Check SHA256SUMS before using the pack. Return gate42-sc-yao-r2-findings.md as Markdown in the chat. If you have
several evidence files, return a ZIP containing that Markdown and the evidence. The user dispatches and merges.
