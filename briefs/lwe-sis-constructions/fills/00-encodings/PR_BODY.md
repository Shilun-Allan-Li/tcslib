Adds finite-noise decisional LWE and integer SIS problems, canonical binary representations, configurable parameter families, and `DLWEAssumption` / `SISAssumption` against the existing nonuniform PPT machines.

All 14 representation lemmas are proved: vector/matrix and challenge lengths/injectivity, signed SIS decoding completeness, and polynomial input/output bounds. The 61 public declarations retain their audited signatures and all definition/instance bodies. No helper, new hardness axiom, sampler machine or primitive security claim is added.

Validation: the external statement gate passed 0 blockers / 0 majors / 0 minors / 3 notes. A fresh 55-module dependency sweep passes with zero new admissions and the same 17 inherited warnings. All 166 elaborated constants use only standard axioms. Style has zero FAIL and two acronym-reader warnings accepted by the statement audit. The whole library root was not checked.

Source commit: `893e921bf2afeca293be9da9d495613bb1486796`; audited statement freeze: `4364d0e0fe9accd649b6acb4751e8684aa93ad1e`. Codex is selected for the separate proof review. Primary PDF archival/ingestion remains open. Keep this PR in draft pending proof review, source-policy work and user approval.

Shared-file overlap: the three imports in `TCSlib.lean` remain isolated in export commit `4364d0e0fe9accd649b6acb4751e8684aa93ad1e`. The proof fill adds no root-export edit. Existing cryptography owner APIs, pins and other campaigns' records are unchanged. Maintainers should reconcile any parallel root-import overlap before merge.
