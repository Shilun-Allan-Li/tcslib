# Codex audit · Gate 37 sc-compose (#324)

Audit draft PR #324 at a6eaebd78c48e7fdfd06263edb84b70bc00ec593 using the scope in pack.md: a proof audit of HybridProtocol.composeP_efficient, composeV_efficient and hbcSecure_compose
[Gol04, §7.3.1, Theorem 7.3.3], with the landing edits LE-doc (docstrings only) and LE-prose (one
sentence of frozen prose, SC-F03; checked doc-only, not rebuilt).
Campaign records are pinned at c44557596ee5c714e1277891591cc8b5d51a0ab0.

The bundle contains the pack, the maintainer review, the worker report, policy, the issued brief, the duplication
  ledger (DL-49) and the review's PROVENANCE; pr-description.md and pr.diff.txt; the 16 changed
  files at the head (ComposeSecurity.lean and its 15 helpers); and, as context at the head,
  SecureComputation/Hybrid, SecureComputation/Compose and SecureComputation/ComposePhases.

Also:
- pr.diff.txt: the full diff from the PR base 6ce4658db08a1dc2a03a149987197660db078011 to the head;
- pr-description.md: the PR description as opened on GitHub;
- source-head.json: the head hashes, line counts and over-width counts of the changed files;
- sources.zip: the source closure at the head of every changed module (98 files);
- verification.zip: every file the review cites and the pack uses, as byte-identical originals:
  review-evidence.zip with its manifest, the review's PROVENANCE, the cited records, evidence extracts,
  the worker extracts (worker/) and the pack's git-object re-checks (pack-checks/); its entries are
  exactly its SHA256SUMS plus SHA256SUMS (121 entries).

landing/ holds byte copies of review-evidence entries (the builds, the census, the frozen check, the tree check). The
worker's own evidence is on this branch under inbox/fills/sc-compose/ (delivery commit bdfdcb76d0d78bedd61025b33cb7382b26ee7c70).

Check SHA256SUMS before using the pack.

Return gate37-sc-compose-findings.md as Markdown in the chat. If you have several evidence files, return a ZIP
containing that Markdown and the evidence. The user dispatches and merges.
