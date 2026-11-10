Adds finite-noise decisional LWE and integer SIS problems, canonical binary representations, configurable parameter families, and `DLWEAssumption` / `SISAssumption` against the existing nonuniform PPT machines.

All 14 representation lemmas are proved: vector/matrix and challenge lengths/injectivity, signed SIS decoding completeness, and polynomial input/output bounds. The 61 public declarations retain their audited signatures and all definition/instance bodies. No helper, new hardness axiom, sampler machine or primitive security claim is added.

Both external Codex gates passed with 0 blockers, 0 majors, 0 minors and 3 continuing notes: the foundation statement gate and the representation-proof gate. Reports are retained verbatim under `audits/lwe-sis-phase0-findings.md` and `audits/lwe-sis-encoding-proofs-findings.md`, with separate resolutions. The proof auditor performed static source/evidence checks and did not independently run Lean.

Validation: a fresh 55-module dependency sweep passes with zero new admissions and the same 17 inherited warnings. All 166 owned-module elaborated constants use only standard axioms. Style has zero FAIL and two accepted acronym-reader warnings. The whole library root was not checked. Records-only audit intake reverified all 63 frozen source files, 86 current evidence checksums, 82 historical evidence checksums and 5 exchange-gate checksums; Lean and pin bytes are unchanged.

Source commit: `893e921bf2afeca293be9da9d495613bb1486796`; audited statement freeze: `4364d0e0fe9accd649b6acb4751e8684aa93ad1e`. Proof-review exchange input: `ebe777ba3bf904f6a6909aaf8b931fcb0c53f358`; bundle SHA-256: `2f8308efa0f737d09cf9554c45407855b76756ee73a2d9fe28fa582962a49ff0`.

Primary PDF archival/ingestion and relevant integration checks remain open. Honest sampler efficiency, useful parameter profiles, machine adapters and primitive security belong to later consumer gates. Keep this PR in draft pending source-policy work and user-controlled integration.

Shared-file overlap: the three imports in `TCSlib.lean` remain isolated in export commit `4364d0e0fe9accd649b6acb4751e8684aa93ad1e`. The proof fill and audit intake add no root-export edit. Existing cryptography owner APIs, pins and other campaigns' records are unchanged. Maintainers should reconcile parallel root-import overlap before merge.
