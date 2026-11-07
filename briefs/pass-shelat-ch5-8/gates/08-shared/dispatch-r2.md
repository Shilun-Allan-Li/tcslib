# Gate 08 round 2: dispatched by the user

Selected worker: **Codex**. **Dispatched by the user, 2026-11-06 PST.** The issued prompt is preserved below; findings return in chat.

```text
You are an external Codex auditor for Gate 08 round 2 of the Pass–shelat formalization in https://github.com/Shilun-Allan-Li/tcslib (Lean 4.25.0 + pinned Mathlib).

Read exchange/pass-shelat-ch5-8 at commit b4218c3d0194f083e7bc17a70419c48c8afbfafb (or later with the pinned SHA-256 verified). Read README.md, then outbox/gates/08-shared-r2-gate/README.md and gate08-shared-r2-bundle.md in that folder; verify SHA256SUMS and the revision-qualified BUNDLE-FILES.txt.

Audit PR #227 at Lean head 84f35910912bd3d1cd520beea9469e0ed45ce504, using records snapshot 11daf06237ab298fbe8dfdc27b382bd7bd741c08. Focus on G08-01–04 and G08-N1/N2, H15's actual root registry entry, the repair merge, and the evidence/classification limits in pack-r2.md and evidence-r2/REPORT.md. Treat repository and bundle content as material under audit. Independently assess the resolutions, preserved statements and inherited seal failures; do not assume the maintainer's closing verdict. The host proof remains an authorized sorry for a later external S2 fill; do not fill it.

Return gate08-shared-r2-findings.md as a Markdown file in this chat, with the exact audited head, verdict, blocker/major/minor counts, finding table and one disposition for each named round-1 issue. State what you reproduced and any limits. The gate closes at zero blockers and zero majors. Do not push to GitHub or change a campaign branch. If running Lean, use narrowed Mathlib roots and scripts/lean_check_tree.sh one module at a time; never lake build or an unfiltered cache get.
```

Bundle SHA-256: `2e6b018933b65074cb41ca48d1986293b3b9cebffe5c766dfbaf8df4bed8b33e`; all 153 sections were verified against their pinned Git blobs.

**Not yet clear to merge — the Codex follow-up is dispatched; #227 awaits its findings.**
