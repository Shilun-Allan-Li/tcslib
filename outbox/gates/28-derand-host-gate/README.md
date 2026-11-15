# Codex audit · Gate 28 derand-host (#312, statement)

Audit draft PR #312 at 8972fb4ef15fa3d4e3df37d6aa8674408835593d using the scope in pack.md: a statement audit of the seed-majority enumeration host seedMajority_mem_DTIME, the contract that
derand (PS10 Theorem 180.1) consumes, and its reader half_lt_randProb_iff.
Campaign records are pinned at 1ea6503c82b12fd7e49c2e621fcae4cd29d9d08c.

The bundle contains:
- the pack, policy, the PR description pr-body.md (with the paper proof of Theorem 180.1), the
  issued derand brief and the duplication ledger;
- the new module Complexity/Randomized/SeedMajority and the facade Randomized at the head, and the context
  at the head: Cryptography/Randomness/Derandomization (the consumer), ClassP/DTIME,
  Randomized/QuasiPolyHierarchy and Randomized/Build/IterateFind.

Also:
- pr.diff.txt: the full diff from the PR base 013119f006af40d03b88b0fc2d9b453cf0a9b348 to the head;
- source-head.json: the head hashes, line counts and over-width counts of the changed files;
- sources.zip: the source closure at the head of every changed module (308 files);
- verification.zip: the maintainer's evidence stmt-derand-evidence.zip with its manifest, the cited records and byte copies of the
  evidence entries the pack cites, as byte-identical originals (45 entries); its entries are exactly its
  SHA256SUMS plus SHA256SUMS itself.

Check SHA256SUMS before using the pack.

Return gate28-derand-host-findings.md as Markdown in the chat. If you have several evidence files, return a ZIP
containing that Markdown and the evidence. The user dispatches and merges.
