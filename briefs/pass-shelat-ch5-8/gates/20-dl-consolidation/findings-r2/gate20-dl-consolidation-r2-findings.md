# Pass–shelat Gate 20, round 2 — external Codex audit

**Verdict: CLEAR. Open counts: 0 blockers, 0 majors, 0 minors, 0 notes.**

Both round-1 findings are closed. No new finding arose from LE-gate20.

## Pins and scope

- Repository / draft PR: [Shilun-Allan-Li/tcslib #298](https://github.com/Shilun-Allan-Li/tcslib/pull/298).
- Audited Lean head: `c2839c41ca6b3a9c34db1595a1ad287768316630`; tree: `5eb486b8c2f1901e3c4db08b610840a12d13fe0f`.
- Round-1 head / direct parent: `6f853adc61d5d175ee83c69f6c07ab2da112cabc`.
- PR base: `2ea4df08d009a4bbdb8042795ff062d7f22db325`.
- Campaign records: `1ca834544fa2c866b5e370f97ecd338cad9f1b12`.
- Exchange: `ed63370ed1a9edaa412871a5529aa188928bc366`; pack: `outbox/gates/20-dl-consolidation-gate-r2/`.
- Scope: the round-1 evidence omissions, both missed folds, and the complete two-file LE-gate20 change. The round-1 source-review conclusions stand, with the previously unverified raw evidence checked below.

## Round-1 findings

| ID | Original severity | File · declaration | Claim / disposition | Evidence | Proposed fix |
|---|---|---|---|---|---|
| G20-01 | major | `verification.zip`, `landing.zip` | **CLOSED.** The omitted originals are supplied, complete and hash-identical; their raw runs support the census, seal comparisons and controls. | Main plus supplement matches **2441/2441** and **188/188** original manifest entries, with no overlap, missing entries, mismatches or supplement extras. All 184 formerly missing active seal logs are present. | None remaining. |
| G20-02 | minor | `UniversalPadding.lean`: `PadQuad.ofFn_arrowCongr`; `OneWayLemmas.lean`: `OneWay.ofFn_block_eq_take_drop` | **CLOSED.** The private copy is deleted and both uses call `ofFn_arrowCongr_finCongr`. The public block-window theorem retains its exact statement and derives its proof through `FunFamily.blocks_apply` and `FunFamily.ofFn_blocks`, without unfolding either block definition. | The patch matches the pinned parent-to-head Git diff. Two-file decls2 independently reproduces **0 rows**; builds, axiom checks, seals and controls support the change. | None remaining. |

## Independently checked

1. **Integrity and source identity.** Both outer manifests pass: **17/17** round-1 and **26/26** round-2 entries. LE-gate20's archive contains exactly its **252/252** manifest paths, all hashes matching. The additional round-1 `statements-r2` manifest also passes. All **52** final source hashes and the deleted path match Git; the complete PR diff matches byte-for-byte: **53 paths, 1480 insertions, 1486 deletions**. All **240** earlier source-closure files match the round-1 head, and all **14** bundle sections match their pinned records/source blobs.
2. **Restored census.** Raw baseline/head logs give **2112 → 2099** stored constants: **101 removed, 88 added, 11 moved**. The sole changed common type hash is the disclosed R3 promotion, `expect_simulate_indImpl_cpa`. The same four inherited Yao constants have nonstandard axioms at both ends.
3. **Seals.** Checked **198** probe sources and their records, reconstructed original source bytes by removing the recorded insertions, checked probe/log hashes, recomputed request coverage from the collector catalogs, and checked every chunk's installation and EOF counts. Effective results are:

   | Variant | Base passes | Head passes | New failing declarations |
   |---|---:|---:|---:|
   | A | 33/40 | 34/41 | 0 |
   | B | 28/40 | 30/41 | 0 |

   The nm-sim seals pass **22/22**. For LE-gate20, `OneWayLemmas` passes both variants before and after; `UniversalPadding` retains the same **4** failing declarations in A and **5** in B. Those declarations are untouched, and both files were unchanged between the PR base and round-1 head.
4. **Final-landing coverage.** The carry-forward argument is sound. After applying the three replacement seal pairs, every effective consolidation probe's reconstructed owner source matches the round-1 Git head. Independently computing imports confirms that none of the **41** sealed owners or their source closures contains any of the **11** nm-sim modules. Those modules have their own later seals. LE-gate20 changes theorem proofs and deletes a private theorem; retained statements and definitions are unchanged. Its two owners are re-sealed at the final head, and these theorem-proof changes do not invalidate dependent seals.
5. **Controls and raw records.** All **50** paired-control probes satisfy their expected outcomes: **90** consolidation, **38** nm-sim and **10** LE-gate20 sealed negatives each fail exactly once; positives and unsealed controls are clean. Checked **1848** latest-per-run-directory result/log hash pairs across the three evidence collections.
6. **Statements, builds and axioms.** Whole-PR decls2 independently reproduces **68 added / 42 removed / 2 moved / 0 changed**, byte-identical to the supplied output. All **16** endpoint headers, both named `castImpl` headers, and the block-window header remain byte-identical. All **114** downstream rebuild records have zero errors and final-source hashes, including root `TCSlib` and both audit `Checks` modules. The final-tree records cover **1198/1198** modules at matching head-source hashes, with **219** admission warnings. The two-file census has **164** standard-axiom constants; all **33** explicit axiom prints, including the 16 endpoints, are standard. Lint FAIL/WARN entries are unchanged, and no changed file increases its count of lines over 100 characters.

## Verification boundary

**No fresh Lean elaboration was performed.** Build, census, axiom and seal conclusions concern the supplied raw records, independently checked against their manifests, probe sources and pinned Git sources. This closes the evidence gap identified in round 1; it does not claim that inherited admissions or inherited seal failures have been eliminated.

The accompanying ZIP contains this Markdown, verification scripts and machine-readable evidence. No source edit, push, GitHub review submission or merge was made. The user dispatches and merges.
