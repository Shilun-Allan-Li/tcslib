# Codex audit · Gate 41 GSW statements (#332 and #333, audited together)

Audit draft PR #332 (DAGCircuit depth readers and runWith_rel) at 94eae71b779c4ca0f76c138d699f4d737dbd6cee and
draft PR #333 (GSW leveled homomorphic encryption from LWE, phase 5 of the lattice campaign; stacked on #332) at
48d796a8a68cd50897047f01825a8132dd19e8d8, using the scope in pack.md: a **statement audit** of the 35 sorried GSW targets (gadget, noise algebra,
public-key scheme, circuit evaluation and leveled correctness, IND-CPA, the optional secret-key unit, the column
leftover-hash lemma), under rulings Q1-Q16 (Q9 changed) and QS1-QS2, and an audit as proofs of #332's two proved
results (DAGGate.getD_lt_depth, runWith_rel). Campaign records are pinned at 86d19094aafecc1e19d208c6629b179cfdd14009.

The bundle contains the pack, policy, the rulings, questions and plan section, the statement-phase EVIDENCE.md, text
excerpts of the passages of [GSW13], [AP14], [Pei16] and [BV14] that the statements use (the PDFs are not committed),
DAGCircuit.lean at #332's head and the GSW and Columns modules and facades at #333's head.

Also:
- pr.diff.txt: the full diff from the common base 523d80d2d4dd8e4ed6799358831e5b3806c6187b to #333's head (it
  contains #332's single commit; its DAGCircuit.lean part is exactly #332's diff);
- pr-description.md: the two PR descriptions as fetched from GitHub on 2026-11-16;
- source-head.json: the head hashes, line counts and over-width counts of the changed files;
- sources.zip: the source closure at #333's head of every changed module (118 files; the library root TCSlib.lean is
  included as a file, not as a closure root);
- source-excerpts/: the four excerpt files (also in bundle.md);
- verification.zip: the statement evidence stmt-gsw.zip with its manifest and PROVENANCE, byte copies of the entries
  the pack cites, the cited records, context files for the reuse and duplication questions and the pack's git-object
  re-checks (pack-checks/); its entries are exactly its SHA256SUMS plus SHA256SUMS.

Check SHA256SUMS before using the pack.

Return gate41-gsw-statements-findings.md as Markdown in the chat. If you have several evidence files, return a ZIP containing
that Markdown and the evidence. The user dispatches and merges.
