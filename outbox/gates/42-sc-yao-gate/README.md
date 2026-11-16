# Codex audit · Gate 42 sc-yao (#341)

Audit draft PR #341 at e9b03c437aca251846430ff23b40ee5ff3d3347a using the scope in pack.md: a **proof audit** of the two frozen
Yao targets `yaoHybrid_polyTime` and `yaoHybrid_simulators` (and the derived `yaoHybrid_hbcSecure`), Yao's
garbled-circuit protocol in the bit-transfer (OT) hybrid model [PS10, Protocol 162.6, Theorem 163.7], with the frozen
`Yao.lean` regions, the seven SY-3 readers in `Uniform.lean`, the landing edits LE-bullet, LE-reuse, LE-title and LE-doc,
duplication (SY-F01 to SY-F12), Rule 10, and the docstring, sketch, sources and evidence rules.
Campaign records are pinned at f22e0f6798815b9263893e61928b4f16452f74ee; Seyoon's rulings on SY-F01 to SY-F03 (ledger rows DL-51 and the
DL-49 extension) are recorded after the pin, at 67423db6c9d6448ae531b04f42c315585d00d502.

The bundle contains the pack, policy, the maintainer's final review, its post-merge addendum and landing PROVENANCE,
the interim (Phase 1) review it supersedes, the worker report, the issued package's README, brief and rulings SY-1 to
SY-6, Seyoon's rulings on SY-F01 to SY-F03 with the duplication ledger and deferred-work register as they stand after
them (records commit 67423db6c9d6448ae531b04f42c315585d00d502, after the pin), Gate 27's resolutions (the hand-off obligations), the PR
description, the frozen files' diff and the pack's main re-checks, the PS10 §6.2 excerpt (text), `Yao.lean` and
`Uniform.lean` at the head, the hub and its 67 helpers at the head, and as context six frozen
SecureComputation files at the head (Defs, Hybrid, Garbling, GarblingSpecial, SpecialEncryptionMulti, YaoReal) and the
two #327/#324 files the duplication findings compare against, at 201bf57a.

Also:
- pr.diff.txt: the full diff from the PR's merge base f9fda8fe8d11fc68c233df2979a86d356ddfe1ab to the head (70 paths);
- pr-description.md: the PR description as read on GitHub;
- source-head.json: the head hashes, line counts and over-width counts of the changed files;
- sources.zip: the source closure at the head of every changed module (TCSlib/), and PS10/: [PS10] §6.2 (book pages
  154-164) from the PDF at the records pin, as PDF pages and as text, with a README;
- verification.zip: the review's manifest and a pointer to its 19 MB evidence ZIP at its committed path at the records
  pin, byte copies of every evidence entry the pack cites, the cited records, the worker extracts (worker/), context
  files, the PR data, and the pack's git-object re-checks with their scripts (pack-checks/); its entries are exactly
  its SHA256SUMS plus SHA256SUMS;
- review.md, post-merge-addendum.md: the maintainer's final review and addendum (records pin); rulings.md: Seyoon's
  rulings on SY-F01 to SY-F03 (records commit 67423db6);
- worker-report.md: the worker's REPORT.md at the final delivery 47c38c479e4be52654cd2c055141dfb64be975c4.

landing/ holds byte copies of review-evidence entries (the build summary and results, the whole-order state check, the
axioms census and summary, the Yao.lean and Uniform.lean scope checks against the tip). The worker's own evidence is
on this branch under inbox/fills/sc-yao/ (final delivery commit 47c38c479e4be52654cd2c055141dfb64be975c4).

Check SHA256SUMS before using the pack.

Return gate42-sc-yao-findings.md as Markdown in the chat. If you have several evidence files, return a ZIP
containing that Markdown and the evidence. The user dispatches and merges.
