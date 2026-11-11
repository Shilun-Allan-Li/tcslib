# Levin production checkpoint

Draft [PR #286](https://github.com/Shilun-Allan-Li/tcslib/pull/286) at 9ada398e06c00656f96207f5254a826c74130c15
contains the integrated proof of PadQuad.exists_linearTime_gStr. The original
header is preserved. Six supporting modules separate parameter recovery,
binary search, padding assembly, quantitative concatenation, unary polynomial
evaluation and binary-to-unary emission. The existing facades export them.

All sixteen native module checks pass at the checkpoint source, including
the thirteen changed files, asymptotic facade, library root and campaign
Checks. All 174 selected new or changed stored declarations use standard
Lean axioms. The actual padding theorem, lemma_64_3 and the conditional
theorem_63_1 also print only standard axioms.

The raw comparison and probe failures are retained. Generalizing the core
proofs changes 26 generated proof-helper identities. The retained-reference
probe needs actual Lean Name values for numeric private components before
that dependency check can finish. The production seal review, controls,
final reader scan and Codex audit also remain. The provider reuse ruling
is approved. The canonizer proof is a separate task.

Resume in the managed worktree at
/Users/seyoonr/.codex/worktrees/ps-levin-padding/tcslib-pass-shelat-ch2-4.
The local native tree and tools are under
/private/tmp/tcslib-levin-proofs.g9J5YEGr/production. The two archives below
preserve the source and evidence if the temporary tree is lost. Every
maintainer native check has finished.

[Checked source](production-source.zip) has SHA-256 `830c79b0f09ebaa45b12b30334b2758be6f40a81fcc86a2f40d96a6e1154ccf2`.
[Native logs and remaining checks](production-checkpoint.zip) have SHA-256 `3c92610aca6865ef182a4b933ebcf34629e1718856b2115d78ecc5a269f594fd`.

The completed Claude efficiency fill is in draft PR #285. Codex Gate 10
is [ready to dispatch](../../gates/10-efficiency/dispatch.md).
PR #284 remains clear for Seyoon to merge at its audited source.

**Not yet clear to merge — Levin production seals, dependency verification and external audit are pending.**
