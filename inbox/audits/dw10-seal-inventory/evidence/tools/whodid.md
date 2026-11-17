**Lead (Claude, cloud).**
- The setup: preflight, toolchain, cache, bootstrap and tree map.
- The collectors and owner check, item location, the scan, seal generation and every Lean run. That is the seal runs (one process,
  then the four-slot pool after the user's override and the ruling), the controls, and the reader index (attempts 1–4).
- The reconciliation, the classification review of the lead's owner set (`review/lead-review-log.md`, `review/overrides-lead.tsv`),
  the merge of the reviews, the tool corrections they prompted, this report and the delivery.
- Only the lead ran Lean or Lake, fetched the cache, wrote under the delivery path outside `subagents/`, or committed.

**Two sub-agents (Claude, in the same session).** They did analysis only: no Lean, no Lake, no git, no network, and they wrote
only under `evidence/subagents/<name>/`. Each worked from its own read-only worktree at the base (`/home/user/dw10/subA` and
`subB`, sparse `TCSlib/`) and a frozen snapshot of the evidence (`snap-r1`: open items, seal errors, scan, reader index; hashes
in `SNAPSHOT.sha256`). Each reviewed the tool's classification of its owner set's open items, item by item, under the
classification brief (`subagents/REVIEW_BRIEF.md`).
- **sub-A** (SecureComputation, ZeroKnowledge): 290 rows (`subagents/sub-A/overrides-A.tsv`, `review-log.md`).
  - 23 STATEMENT→STAGE2, with the error in the proof on the header's last line.
  - The fix changed in 199 rows: a different definition read, a completed partial fix, or a concrete reader statement.
  - The shadow-transfer design question (DW10-W6) and the two lexer false positives (DW10-W7).
- **sub-B** (Encryption, Authentication, Games, Hashing, Randomness, Implications, Pseudorandom): 120 rows
  (`subagents/sub-B/overrides-sub-B.tsv`, `review-log.md`).
  - 8 STATEMENT→STAGE2. sub-B found the line-only statement test, which the lead then corrected in the tool for every set.
  - The fix changed in 50 rows.
  - The duplicate generated-equation row, which the lead traced to the matcher.

Three corrections were sent to the sub-agents while they worked; their logs record them:
- the `agent` values are `sub-A` / `sub-B`;
- the harness rows are DW10-W5;
- use the attempt 4 reader index.

The lead copied their override files into `review/` unchanged. Rows the seals added after the snapshot were reviewed by the lead
(`review/overrides-lead-delta.tsv`).
