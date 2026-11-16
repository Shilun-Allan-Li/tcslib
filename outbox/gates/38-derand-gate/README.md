# Codex audit · Gate 38 derand (#326)

Audit draft PR #326 at c27005d67298f79c785a4e8ac1648da0a67d3614 using the scope in pack.md: a proof audit of
Complexity.exists_seedMajorityTM (host H17), Complexity.seedMajority_mem_DTIME and
TCSlib.Cryptography.Randomness.bpp_subset_dtime_subexp [PS10, §8.2, Theorem 180.1], with the pre-approved
shared-file additions E1-E3 and SR-01, the ruled Rule-10 debt F-01 (DW-5), and the landing edit LE-doc (F-04, one
docstring). Campaign records are pinned at 24f4405205542f810157cbaf29a36ab99a52cbe8.

The bundle contains the pack, the maintainer review, the worker report, policy, the issued brief (issued-r2), the
duplication ledger, the deferred-work register, the review's and LE-doc's PROVENANCE, Gate 28's round-2 resolutions,
pr-description.md and pr.diff.txt, and at the head the five pre-existing files (ClassP/DTIME, Build/IterateFind,
Randomized/Classes, Randomized/SeedMajority, Randomness/Derandomization).

Also:
- pr.diff.txt: the full diff from the PR base 6ce4658db08a1dc2a03a149987197660db078011 to the head;
- pr-description.md: the PR description as fetched from GitHub on 2026-11-16 (it predates LE-doc);
- source-head.json: the head hashes, line counts and over-width counts of the changed files;
- sources.zip: the source closure at the head of every changed module (207 files);
- verification.zip: every file the review cites and the pack uses, as byte-identical originals: review-evidence.zip
  with its manifest, the review's PROVENANCE, the issue package and cited records, evidence extracts, the worker
  extracts (worker/) and the pack's git-object re-checks (pack-checks/); its entries are exactly its SHA256SUMS
  plus SHA256SUMS;
- landing-ledoc/: LE-doc (derand F-04 and seq-zk S-02): the evidence ZIP with its manifest and PROVENANCE;
- integration/: the combined integration build of all open PRs (records maintainer/int-all-open-2026-11-16/): the
  evidence ZIP with its manifest and PROVENANCE. Merging the open heads onto the current tip, in any order, gives
  exactly its TCSlib and audits trees (pack, merge interaction).

landing/ holds byte copies of review-evidence entries (the build, the census, the frozen check, the tree check). The
worker's own evidence is on this branch under inbox/fills/derand/ (delivery commit
186ffb99ae6e1034185ee2cdffc318db2c955a58).

Check SHA256SUMS before using the pack.

Return gate38-derand-findings.md as Markdown in the chat. If you have several evidence files, return a ZIP
containing that Markdown and the evidence. The user dispatches and merges.
