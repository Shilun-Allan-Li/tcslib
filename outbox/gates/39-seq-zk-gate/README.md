# Codex audit · Gate 39 seq-zk (#327)

Audit draft PR #327 at bd19c433a4cf3d4027ffc891d7d3c06e927e9dfa using the scope in pack.md: a proof audit of the five seqRep
theorems ZK.seqRep, StatZK.seqRep, InteractiveProof.seqRep, InteractiveProofErr.seqRep and
EfficientProverProofErr.seqRep [PS10, §7.2.1, Theorem 175.1; Gol01, §4.3.4], with the approved shared-file reader
StatZK_iff (S-01) and the landing edit LE-doc (S-02, 81 docstrings). Campaign records are pinned at d5a3e2d0c399b918d72e5a51732905625e500bd2.

The bundle contains the pack, the maintainer review, the worker report, policy, the issued brief, the duplication
ledger, the review's and LE-doc's PROVENANCE, pr-description.md and pr.diff.txt, and at the head
Composability/SequentialZK.lean, ZeroKnowledge/Defs.lean and SequentialZK/SimulatorMachine.lean.

Also:
- pr.diff.txt: the full diff from the PR base 05d26fe5b41fcb9426ec220d877d03264b9c8e8c to the head;
- pr-description.md: the PR description as fetched from GitHub on 2026-11-16 (it predates LE-doc);
- source-head.json: the head hashes, line counts and over-width counts of the changed files;
- sources.zip: the source closure at the head of every changed module (185 files);
- verification.zip: every file the review cites and the pack uses, as byte-identical originals: review-evidence.zip
  with its manifest, the review's PROVENANCE, the issue package and cited records, evidence extracts, the worker
  extracts (worker/) and the pack's git-object re-checks (pack-checks/); its entries are exactly its SHA256SUMS
  plus SHA256SUMS;
- landing-ledoc/: LE-doc (derand F-04 and seq-zk S-02): the evidence ZIP with its manifest and PROVENANCE;
- integration/: the combined integration build of all open PRs (records maintainer/int-all-open-2026-11-16/): the
  evidence ZIP with its manifest and PROVENANCE. Merging the open heads onto the current tip, in any order, gives
  exactly its TCSlib and audits trees (pack, merge interaction).

landing/ holds byte copies of review-evidence entries (the build, the census, the frozen check, the tree check). The
worker's own evidence is on this branch under inbox/fills/seq-zk/ (delivery commit
a6be22fa168fcd0a40971383d8ffb3f1adb9731d).

Check SHA256SUMS before using the pack.

Return gate39-seq-zk-findings.md as Markdown in the chat. If you have several evidence files, return a ZIP
containing that Markdown and the evidence. The user dispatches and merges.
