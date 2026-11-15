# Codex audit · Gate 35 canonizer (#319)

Audit draft PR #319 at 6421ac1631ef08feed297c810f0839b178d2a2bb using the scope in pack.md: a proof audit of TCSlib.Cryptography.exists_canonizerExp [PS10, §2.13; run-3 audit P3-4], with the
two pre-approved rfl readers in the frozen CodeFormat and CodeSimulator and the landing edit LE-doc
(docstrings only).
Campaign records are pinned at 034da63a3408d0112fa45df00abb3de3080246d2.

The bundle contains the pack, the maintainer review, the worker report, policy, the issued brief, the readers ruling
  of 2026-11-14 and the review's PROVENANCE; pr-description.md and pr.diff.txt; the changed Lean
  files at the head except CodeSimulator (474 KB; its one hunk is in pr.diff.txt and the file in
  sources.zip): Asymptotic/Universal, its helper Universal/Canonizer and TuringMachine/CodeFormat;
  and, as context at the head, TuringMachine/Encoding (EffectiveMachineCode) and
  Diagonalization/EXPCOM (exists_uniformMachineCode).

Also:
- pr.diff.txt: the full diff from the PR base a334ec2e1d87dbde7eac40812286ba60e85c9078 to the head;
- pr-description.md: the PR description as opened on GitHub;
- source-head.json: the head hashes, line counts and over-width counts of the changed files;
- sources.zip: the source closure at the head of every changed module (110 files);
- verification.zip: every file the review cites and the pack uses, as byte-identical originals:
  review-evidence.zip with its manifest, the review's landing extracts, the cited records, evidence
  extracts, the worker extracts (worker/) and the pack's git-object re-checks (pack-checks/); its
  entries are exactly its SHA256SUMS plus SHA256SUMS (125 entries).

landing/ holds byte copies of review-evidence entries at the head. The worker's own evidence is on this
branch under inbox/fills/canonizer/ (delivery commit 27ae588db3952fb508f02184f9ea2adbb726cf6c).
Check SHA256SUMS before using the pack.

Return gate35-canonizer-findings.md as Markdown in the chat. If you have several evidence files, return a ZIP
containing that Markdown and the evidence. The user dispatches and merges.
