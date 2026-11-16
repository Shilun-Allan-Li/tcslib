# gsw-security · maintainer delivery review (r1)

**Verdict: ACCEPT, no landing edit.** All six targets (F5 `hashColumns_eq_mul`, `distAdv_hashColumns_uniform_le`; F6
`real_uniformKey_advantage`, `uniformKey_uniform_advantage_le`, `distAdv_encrypt_le`, `distAdv_encrypt_le_of_width`) are
proved exactly as frozen.
- On the merge of the current records tip with the delivered head, all 650 rebuilt modules pass, through root `TCSlib` and
  both `audits/*/Checks`.
- The targets use only the standard three axioms, and no target reaches a sorried constant.
- Rule 10 holds: the canonical coe seal A finds 0 failing declarations.

There are 0 blockers and 0 majors. There are two minors: GS-02, a disclosure erratum, and GS-03, an evidence file that was not
delivered and that I reconstructed. There are four info findings. **GS-01, the disclosed duplication of the hybrid pattern,
awaits Seyoon's ruling** on the debt and its payback (promotion request P-1).

## Delivery and landing
- **Delivery:** a single-agent Claude fill.
  - The final is exchange `5857e850e7f7daf264d2860caf27341e3052f8c5`; the checkpoint is
    `b08456186ebfa194f8445f1f78ba7c0743e4991b` (F5).
  - Both commits touch only `inbox/fills/gsw-security/`, and the history is linear.
  - The issue base is `486f44f8414c20a2d21e452c44de8b8c8d8513a0`, #333's head, with #332 as an ancestor. Both have since
    merged, so the base is an ancestor of the tip.
- **Head:** `a9f97eddb42c7dfc0422fa8c9ce998c658bfa4f8`. It has two commits: `58a97f52` (F5, the checkpoint's) and `a9f97edd`
  (F6). Neither is signed; `COMMITS.tsv` reads `none`.
- **Files:** only the two owned files, +219/−26:
  - `Hashing/SIS/Columns.lean`: 89 → 194 lines;
  - `AdvancedEncryption/Homomorphic/GSW/Security.lean`: 217 → 305 lines.

  Nothing else changed: there is no new declaration (public or private), no helper module, no facade, no frozen-file edit and
  no scope request. The one new import, in both files, is `TCSlib.Cryptography.Pseudorandom.Indistinguishability`, which the
  brief authorizes; its closure is 4 modules. `Columns` imports nothing under `AdvancedEncryption/`.
- **Landing:**
  - `git merge-tree` of the records tip `e2f5850fcd1b38738f7ad2f2cd413c840803ef90` and `a9f97edd` is clean, giving tree
    `ac512a9b`. I recorded it as the scratch commit `a51294c5`, which is unsigned and never pushed.
  - The merge differs from the tip only in the two files, and each equals the delivered file. The tip's code paths are equal to
    those of `4b46c488`, which Phase 1 merged (tree `710f1fcd`).
  - The three-way merge with gsw-core's head `d4ebb0be` is also clean. The two fills own disjoint files, and gsw-core changes
    no import and keeps `encrypt_eq`, `lift_apply` and `gadget`.
  - Between the base and the tip, one module in the owned closure changed: `Randomized/Classes` gained `inBPP_iff`, an addition.
- **Evidence:** `$SP/dl-review/gsw-security-r1/`. The ZIP `gsw-security-r1-evidence.zip` has SHA-256
  `447f651d4f5e5aed92642d31e3529475d1455a489a620a7d46b9f631d210d7fb`. It has 1023 entries: the 1022 manifest paths plus
  `SHA256SUMS` (SHA-256 `d2482963…`).

## Checks (Phase 1, static)
- **Integrity.**
  - **Manifests.** The top-level `SHA256SUMS` lists 779 files, of which 778 are present: `evidence/probes/CacheProbe.lean` is
    missing (GS-03). `evidence/SHA256SUMS` lists 772, of which 771 are present (the same file). There are 0 hash mismatches,
    no extra file and no `./`.
  - **Patches.** `git am` at the base, with the recorded identities and dates and `commit.gpgsign=false`, reproduces both
    hashes unsigned (`%G?` N), giving tree `6dd1a771`. `src/` equals the two changed paths byte for byte.
  - **Pack and sources.** The issue pack verifies 7/7, and its exchange copy is blob-identical. `SOURCE-SHA256SUMS` verifies
    147/147 at the base.
- **Statements, by my own script** (independent of the delivery's):
  - `Columns` 4/4 and `Security` 13/13 base declarations reappear in order, with 0 differences.
  - The six target headers are byte-identical, and so is their prose up to `**Proof sketch.**`.
  - Every non-target is byte-identical, body included: `hashColumns`, `view`, `realView`, `uniformKeyView`, `reduction`,
    `columnHashParameters`, the five readers and the `attribute [simps …]` line. So is every `open`, `set_option` and module
    docstring.
  - The only addition is the import.
  - Ten controls per file each give the expected count: one-character header 1, deleted reader 1 removal, definition body 1,
    target prose 1, sketch-only edit 0, removed option 1, added option 1, order swap 1, one-character command 2, identity 0.
  - `decls2.py`: 0 ADDED, 0 CHANGED, 0 REMOVED. The delivered header check and its two controls agree.
- **Style.**
  - Widths are at most 100 (`Columns` 100, `Security` 99), and the files have 194 and 305 lines.
  - There is no `µ`, tab, trailing space, `@[simp]` or new attribute.
  - Every target has a sketch that describes the delivered proof. The two long proofs (`distAdv_hashColumns_uniform_le`, 98
    lines; `uniformKey_uniform_advantage_le`, 42) and `distAdv_encrypt_le` carry step comments.
- **Sources.** The source-tag multisets of both files are identical at base and final, and the sketches carry no tag. No
  excerpt or location is fabricated. The Gate 41 excerpts were not needed.
- **Names.** There are no new names, so there is nothing that could clash with the base or the tip.
- **Lint.** My rerun at base and final gives 92 FAIL / 101 WARN over 364 files at both. The FAIL and WARN line sets are
  identical; only the two owned files' INFO size lines change. The results equal the delivered logs. At the merge it is
  92/101 over 385 files, with FAIL/WARN line sets identical to final's.
- **Rule 10, by reading the source.**
  - My explicit-unfold scan covers 90 rule heads (65 lemmas, 25 local `let`/`have` names) and finds 0 foreign definitions.
  - `Security` reads `hashColumns` only through `hashColumns_eq_mul`, `encrypt` through `encrypt_eq`, `lift` through
    `lift_apply`, `LWE.decisionAdvantage`, `Regev.extractionError` and `distAdv`/`acceptProb` through their readers, and its
    own `columnHashParameters` through its `simps` readers.
  - `Regev.augmented` appears only as a term inside `Equiv.ofBijective … (Regev.augmented_bijective …)`. Its declared codomain
    is `Fin (n+1)`-indexed, so the `AugKey` type is reached without a type-level unfold. `Regev.hashParameters` is not used.
  - Mathlib definitions (`Matrix.mulVec`, `Matrix.of`, `Equiv` coercions) reduce only in `rfl` or term steps.
- **Delivered seal, control, axiom and admission evidence** (re-parsed from the raw logs):
  - **Seals.** Each of the 24 seal probes reproduces its source exactly (contiguous line map, hoisted imports), with one install
    and one EOF record and 0 errors in both forms.
  - **Controls.** There are 35 at the checkpoint and 55 at final. Every sealed negative fails exactly once; the coercion fails
    only under strict.
  - **Errors.** Across 454 logs there are 38 `error:` and 5 `error(`. All are expected control negatives or the disclosed
    development iterations.
  - **Admissions,** recounted from the raw sweeps: 51 in 14 modules at checkpoint 1, and 47 in 13 at final.

## Checks (Phase 2, Lean, on `$SP/dl-oleans-2`)
- **Build.** The source is an export of the merge `a51294c5`: only `TCSlib/`, `audits/`, `scripts/` and the lake files, with
  the shared `.lake/packages` linked.
  - The tree starts at snapshot `457ba704…` (1230 files), which is the oleans at `eff2dcd0`.
  - The incremental plan by import-closure keys gives 650 builds and 638 reuses. Those 650 are exactly the downstream of the
    changes since `eff2dcd0`, including root `TCSlib` and both `audits/*/Checks`.
  - The 561 snapshot oleans to be overwritten were backed up and hash-verified. The Mathlib overlay and `NthRootLemmas`
    (built through `lean_check_tree.sh`, olean `c0a9cff0…` as before) were added.
- **Results.** 650/650 modules give rc 0, with 0 `error:`, 0 `error(` and 0 occurrences of the substring "error". The build
  took 5856 s of module time (10:50–12:28 UTC), with a maximum RSS of 4.51 GB.
  - `Columns` (2.8 s) and `Security` (3.0 s) show 0 sorry and 0 warnings. So do the `Hashing/SIS`, `Hashing`, `GSW`,
    `Homomorphic` and `AdvancedEncryption` facades, root `TCSlib` and both `Checks`.
  - **References.** 648 of the 650 modules are byte-identical, in both olean and log, to a same-source reference record from
    earlier builds of the tip's code. The other two, `Columns` and `Security`, have new sources.
  - **State check:** 1288 modules OK. **Whole-tree check:** every module is rc 0 at the merge's source and every olean equals
    its record; no olean is missing, stray or zero-byte, and no directory is empty.
- **Admissions.** The tip has 237; the merge has 231. The difference is exactly `Columns` 2 → 0 and `Security` 4 → 0, and no
  other module changes. The gsw-core files keep their 29 tip admissions.
- **Axioms**, from my own probe: all six targets and all 32 stored constants of the two modules use only `propext`,
  `Classical.choice` and `Quot.sound`.
  - My dependency trace walks types and values, theorem bodies included, and reaches no sorried constant from any target. The
    closure sizes are 2444, 19103, 9349, 19199, 19214 and 19231, the same as the delivery's.
  - The only gsw-core theorems reached are the `rfl` readers `encrypt_eq` and `lift_apply`. The tip still admits every
    gsw-core target, so this confirms that no gsw-core target is cited.
- **Rule 10, my own canonical seals.**
  - Method: the collector reads the elaborated terms and the closures, and the archived Gate 06/10 instrumenter seals every
    ordinary TCSlib definition of each file's import closure. Each probe runs with `lean -DmaxErrors=0` and without `-o`.
  - **Seals:** 8/8 probes (`Columns` and `Security` × A/B × strict/coe) give rc 0, with 0 `error:` and 0 `error(`. Each
    has its install and EOF records, with every request verified.
    - Requests: strict 32 and 115; coe 31 and 114. Strict differs from coe only by the projection coercion
      `FinDist.instCoeFunForallReal`.
    - A = B, because `PolyExpr.eval` is in neither closure.
    - The **canonical coe seal A** fails on 0 declarations in either file. The request counts equal the delivery's.
    - Coverage includes the SIS `hash`, `hashColumns`, `Regev.augmented`, `Regev.hashParameters`,
      `Regev.extractionError`, `LWE.sample`, `LWE.decisionAdvantage`, `BitEncoding.codepoint`, both `gadget`s, `encrypt`,
      `lift`, `acceptProb` and `distAdv`, which covers plan §G8's type-level list.
    - Every foreign definition that the stored constants reference is either sealed or an abbreviation, which is notation:
      `Ciphertext`, `Parameters.columns`/`lwe`, `Noise.Coins` and the `Parameters` fields.
  - **Controls, written by me:** 11 paired rows for `Security` and 3 for `Columns`, plus the coercion row under strict.
    - Each negative is the bare `rfl` unfolding, and each positive is the published reader: `hash_eq`,
      `hashColumns_apply`, `augmented_eq`, `hashParameters_dimension`, `extractionError_eq`, `sample_fst`,
      `decisionAdvantage_eq`, `encrypt_eq`, `lift_apply`, `acceptProb_def`, `distAdv_def`, `FinDist.coe_mk`.
    - In the coe variants (A and B), 8 probes are **ALL_OK**: unsealed, all pass; sealed, each negative fails exactly once
      (14 failures), the positives pass, there is no stray error, and the install and EOF records are present.
    - In the strict variants, the only deviation is `ctlCoeReader` (`FinDist.coe_mk` at an anonymous-constructor
      `FinDist`), which also fails once in each sealed probe. This is the known strict artifact from the seq-zk review;
      the coe seal is canonical.
    - Error counts in both forms: probes 0/0, seals 0/0, coe controls 14/0 per variant, strict controls 18/0 per variant.
      All are expected.
- **Restore.** All 561 backups were restored, each hash-checked, with 0 failures. The 89 new oleans and the Mathlib overlay
  (3346 symlinks plus `NthRootLemmas`) were deleted, and 18 emptied directories were removed.
  - `restoreplan` reports extra 0, changed 0 and missing 0.
  - `snapshot-post` has 1230 files and SHA-256 `457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f`, and is
    byte-equal to `snapshot-pre` (**SNAPSHOT EQUAL**). A fresh recheck snapshot is also equal.
  - The probes wrote nothing to the tree. The backup, the export and the delivery extract have been removed.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| GS-01 | info, disclosed | **Duplicated proof pattern, disclosed and within the brief.** (1) F5's 98-line inline column hybrid re-derives the shared-parameter planting hybrid. Its `hleft`/`hright` steps re-derive the planting identity from public lemmas (`acceptProb_bind`, `acceptProb_comp_equiv`, `acceptProb_update`); `hzero`/`hfull` are the end hybrids. (2) F6's proofs mirror `Regev/Experiments.lean` almost line for line: the 3×`abs_sub_le` triangle chain of `distAdv_encrypt_le` and the `hreal`/`hideal` relabel-into-test steps of `uniformKey_uniform_advantage_le`. Gate 41 and the brief sanction both routes (the generic column hybrid belongs in `Columns`; F6 restates the Regev hybrids for GSW's ciphertext space), and no generic `distAdv` triangle lemma exists. The REPORT discloses each step and proposes P-1, a generic shared-parameter hybrid in the probability layer. Policy §1 requires every duplicated proved material to be human-approved. | **Awaiting Seyoon's ruling.** Recommended: accept as disclosed debt. Add a duplication-ledger row naming the copies (`Columns.lean:95–192`; `Security.lean:197–238` and `256–279` against `Regev/Experiments.lean:254–292` and `309–327`). Payback is P-1 as restated in GS-02, in the cleanup queue. No landing edit. |
| GS-02 | minor | **Overlap disclosure is incomplete, and P-1 misstates the gap.** The `## Overlap and reuse` table omits three public relatives: (a) the generic coordinatewise hybrid with **different seed types** in `ZeroKnowledge/Commitment.lean:148–239` (`pairTuple`, `pairHybrid`, `pairRed`, `acceptProb_pairHybrid_zero/_self`, `acceptProb_pairRed_left/_right`, `exists_pairRed_ge`), which is the nearest relative of `hleft`/`hright`/`hzero`/`hfull` and appears in the worker's own `evidence/overlap/searches-tcslib.txt`; (b) `distAdv_multi_le_sum` (`Encryption/PublicKey/EnsembleSecurity.lean:134`), the public form of the disclosed `distAdv_tuple_le_sum`, which `Security`'s own module docstring cites; (c) `distAdv_comp` (`Pseudorandom/Indistinguishability.lean:141`, in the authorized import), which states the `hreal`/`hideal` relabel-into-test step. P-1 asks for a hybrid "for two samplers with *different* seed types"; `pairHybrid` already provides that. What is missing is only the **shared public parameter**, which `pairHybrid`'s independent coordinates cannot express. Neither reuse was available without an import outside the brief's list or a new shared lemma, so no code change follows. | **Erratum, recorded here.** P-1 is restated: generalize `pairHybrid`/`pairRed` with a shared parameter `κ`, then re-derive `distAdv_tuple_le_sum` and `Columns`' hybrid from it. Ledger row with GS-01. No landing edit. |
| GS-03 | minor | **Evidence completeness: one delivered-manifest file is missing.** `evidence/probes/CacheProbe.lean` is listed in both manifests at the checkpoint and at final but was never committed, so the REPORT's "listed paths equal the delivered files exactly" is false, as is its mention of `evidence/probes/`. The file is the environment's cache probe; its log `evidence/logs/cache-probe.log` is delivered, and no proof claim depends on it. **Reconstructed:** the one line `import Mathlib.Algebra.BigOperators.Field` plus a newline has exactly the manifest's SHA-256 `f8388ee61e1b1b5ba7d6786f99b895008e3278cb1f06a0063fe1434571d444a1` (evidence `out/reconstructed/`). | **Accepted with the reconstruction.** No re-delivery needed. Recorded for the intake: the exchange path set is 778 files against a 779-path manifest. |
| GS-04 | info | `evidence/headers/__pycache__/frozen_headers.cpython-313.pyc`, a compiled tool artifact, is delivered and listed in the manifests. It is harmless. | None. |
| GS-05 | info | The delivered "base" seals of `Security` ran after the final sweep, against the final `Columns` olean. Their closure therefore includes `Pseudorandom/Indistinguishability` (115/114 requests, the same as final; the true base would have 7 fewer: `copies`, `mixDist`, `multicopyAvgRed`, `multicopyHybrid`, `multicopyRed`, `pushSampler`, `sunglassRed`). The REPORT's "at base" label is imprecise. There are 0 failures either way, so no attribution depends on it. | None. |
| GS-06 | info | **Cross-fill note.** The same two inline relabellings appear at three sites: the key equivalence `Equiv.ofBijective _ (Regev.augmented_bijective _)` and the translation by `μG`/the codepoint (`Equiv.addRight`). The sites are `Regev/Experiments.lean:260`, `GSW/Security.lean:202–206` and gsw-core's `GSW/Symmetric.lean:116,136`. | None now. A published `Regev.augmentedEquiv` (with its `_apply` reader) is a candidate for the DW-4 deduplication queue. |

## Proposed landing edits
None. The delivery lands as is, after #332 and #333, which have merged; it rebases onto the tip with no conflict. The
REPORT errata (GS-02, GS-03) are recorded here and need no change to the delivery.

## Evidence (`$SP/dl-review/gsw-security-r1/`, ZIP `gsw-security-r1-evidence.zip`)
- `PROVENANCE.txt` (method, hashes, every step), `PHASE2-PLAN.txt`, `SHA256SUMS`.
- **Phase 1:**
  - `out/`: manifests, patch reproduction, package and source verification, frozen check and controls (`out/headers/`),
    `decls2`, widths, source tags, lint (`out/lint/`, base, final, merge), unfold scan, duplication searches at the tip,
    merge-tree, the delivered-evidence re-checks (seal probes against source, error counts, sweep admissions), the
    reconstructed `CacheProbe.lean`, and copies of the delivered `REPORT.md` and `COMMITS.tsv`. The delivery extract itself
    was removed; it is reproducible from exchange `5857e850e`.
  - `tools/`: `manifest_check.py`, `frozen_check.py`, `frozen_controls.py`, `widths.py`, `closure.py`, `downstream.py`,
    `unfold_scan.py`, `sealprobe_check.py`, `logcount.py`, and the maintainer's `decls2.py`.
- **Phase 2:**
  - `order/`, `plan/`, `state/` (keys at `eff2dcd0` and after the build).
  - `tree/`: `snapshot-pre.txt`, `backed-up.txt`, `new-oleans.txt`, `snapshot-post.txt`.
  - `build/`: `results.jsonl`, 650 logs, `per-module.tsv`, `buildsum.txt`, `statecheck.txt`, `refunion*`, `logcheck.txt`.
  - `build-mathlib-extra/`, `records/`, `tree-final/`, `admissions/`, `refs/` (the reference records).
  - Probes: `probe-runs-1/` (axioms and trace, collector), `p2/probes/`.
  - Seals: `seals{,-coe}/{A,B}/` (records and probe sources) and `seal-runs/`.
  - Controls: `controls-{coe,strict}-{A,B}/` and `control-runs-*/`, with `probes/` holding orders, error counts and probe
    sources.
  - Restore: `restore/`.
  - `tools-used/` (unmodified copies of the int-x tools, plus `fullorder.py` and `restore_gsws.sh`) and `rule10-tools/` (the
    seal and control harness, plus `mkctl_gsws.py`, `mkseals_*_gsws.py`, `sealtab.py`).
  - The finish scripts: `run-build.sh`, `finish-post-build.sh`, `finish-probes.sh`, `finish-restore.sh`.

**Not yet clear to merge — GS-01 awaits Seyoon's ruling; then a landing branch and PR for his approval.**
