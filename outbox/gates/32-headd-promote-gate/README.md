# Codex audit · Gate 32 headd-promote (#316)

Audit draft PR #316 at c18afbe66101381eed1617801d942dcf691506ea using the scope in pack.md: a promotion audit of TCSlib.Cryptography.headD_drop_ofFn (Gate 29 G29-02) and the
proof-only re-derivation of Authentication.LamportFill.headD_drop_ofFn.
Campaign records are pinned at 3433097294600c7cd1ce30f5a5cc005c4ff0e4a4.

The bundle contains the pack, policy, Codex's Gate 29 findings (G29-02) and Gate 29's round-1 resolutions (the
  ruling), the duplication ledger (DL-47), the records PR draft pr-body.md and the opened
  description pr-description.md; pr.diff.txt; the two changed Lean files at the head (Foundations/BitLists,
  Lamport/MachineSpec) and, as context, Pseudorandom/NextBit at the head (an inline chain) and
  #313's Randomness/Learning/{Random,Sample} at 94b31964 (the G29-02 consumer).

Also:
- pr.diff.txt: the full diff from the PR base dd98360d4886ac68fab34899b8bd0d12ae9a0aef to the head;
- pr-description.md: the PR description as opened on GitHub;
- source-head.json: the head hashes, line counts and over-width counts of the changed files;
- sources.zip: the source closure at the head of every changed module (149 files);
- verification.zip: the maintainer's evidence promote-headd-evidence.zip with its manifest, the
  cited records, byte copies of the evidence entries the pack cites and the pack's git-object
  re-checks (pack-checks/), as byte-identical originals; its entries are exactly its SHA256SUMS
  plus SHA256SUMS (62 entries).

landing/ holds the logs at the head.
Check SHA256SUMS before using the pack.

Return gate32-headd-promote-findings.md as Markdown in the chat. If you have several evidence files, return a ZIP
containing that Markdown and the evidence. The user dispatches and merges.
