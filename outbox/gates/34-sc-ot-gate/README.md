# Codex audit · Gate 34 sc-ot (#318)

Audit draft PR #318 at f62a25b3eda099c9cf9371900664752e7b89007d using the scope in pack.md: a proof audit of SecureComputation.otProtocol_polyTime and otProtocol_simulators [PS10, Protocol
160.4 and Proposition 161.5], with the landing edits LE-doc (docstrings only) and LE-reuse (proof
only, review finding F-01).
Campaign records are pinned at 5d719839503c1f29f65f5ffa200410349a782276.

The bundle contains the pack, the maintainer review, the worker report, policy, the issued brief, the duplication
  ledger (DL-48) and the review's PROVENANCE; pr-description.md and pr.diff.txt; the seven changed
  Lean files at the head (SecureComputation/ObliviousTransfer and its helpers ObliviousTransfer/
  {Shape,Efficiency,Simulators,ViewA,Predictor,ViewB}) and, as context at the head,
  SecureComputation/Defs (the functionality and its samplers), Encryption/PublicKey/TrapdoorPredictor
  (tdpPredictor) and Encryption/PublicKey/Trapdoor (exists_pkPredictor).

Also:
- pr.diff.txt: the full diff from the PR base a334ec2e1d87dbde7eac40812286ba60e85c9078 to the head;
- pr-description.md: the PR description as opened on GitHub;
- source-head.json: the head hashes, line counts and over-width counts of the changed files;
- sources.zip: the source closure at the head of every changed module (128 files);
- verification.zip: every file the review cites and the pack uses, as byte-identical originals:
  review-evidence.zip with its manifest, the review's landing extracts, the cited records, evidence
  extracts, the worker extracts (worker/) and the pack's git-object re-checks (pack-checks/); its
  entries are exactly its SHA256SUMS plus SHA256SUMS (113 entries).

landing/ holds byte copies of review-evidence entries at the head. The worker's own evidence is on this
branch under inbox/fills/sc-ot/ (delivery commit a8972fa063a58ad2ffbfd221d625653d34a53ee8).
Check SHA256SUMS before using the pack.

Return gate34-sc-ot-findings.md as Markdown in the chat. If you have several evidence files, return a ZIP
containing that Markdown and the evidence. The user dispatches and merges.
