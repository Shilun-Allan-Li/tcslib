# Pass–shelat Gate 34, round 2 — sc-ot findings

**Verdict: CLEAR. Current findings: 0 blockers, 0 majors, 0 minors, 0 notes.**

Both round-1 findings are closed for this gate. **G34-01 is fixed by reuse; G34-02 is discharged by the explicit DL-48 debt ruling, with its code cleanup still outstanding.** No new audit finding or new undisclosed duplicate was found.

| Pin | Audited revision |
|---|---|
| Repository / PR | `Shilun-Allan-Li/tcslib`, draft [#318](https://github.com/Shilun-Allan-Li/tcslib/pull/318) |
| Lean head | `b0bad23ae611983e3323460bb8c564da90ad6e8c` |
| Recorded audit base | `05d26fe5b41fcb9426ec220d877d03264b9c8e8c` |
| Campaign records | `4c95a8437dec980209d12327e6208c5ae967e178` |
| Exchange | `7add7297c4021ea4c68d3b890814e02f71c1f9b8` |
| Round-1 Lean head | `f62a25b3eda099c9cf9371900664752e7b89007d` |
| Audit date | 2026-11-15 (America/Los_Angeles) |

## Round-1 finding closure

Lean paths below are relative to `TCSlib/Cryptography/`. The severities in this table are the **historical round-1 severities**, not current open findings.

| ID | Round-1 severity | File · declaration | Assessment | Evidence | Disposition |
|---|---|---|---|---|---|
| G34-01 | major | `SecureComputation/ObliviousTransfer/Efficiency.lean:199,206` · `OT.getD_zero_eq`, `OT.getD_one_eq'` | Both now derive from public `TCSlib.Cryptography.headD_drop`. The first reverses its index-zero instance and simplifies `List.drop_zero`; the second reverses its index-one instance. | Independent Git comparison of `e0ecdf22..b0bad23a`; `Foundations/BitLists.lean:52`; refreshed landing evidence. | **Closed — fixed by LE-gate34.** Headers and imports are unchanged. Only these two proofs and their provenance docstrings change. |
| G34-02 | major | `SecureComputation/ObliviousTransfer/Simulators.lean:210–212` · `OT.length_ofFn_coins` | The identical public `Composability.NMSim.length_ofFn_coins` remains, and the duplication is now explicitly disclosed and accepted. | DL-48 at the campaign pin; decision-log ruling “fix 01, ledger 02”; `resolutions-r1.md`; `landing-gate34/NOTE.txt`. Both source copies are unchanged. | **Closed — accepted ledger debt.** Cleanup must promote `length_ofFn_coins` to the `NUPPT` layer and re-point both copies. This is not a claim that the duplication has been removed. |

DL-48 names both declarations and their locations, records the import-cost reason for deferral, specifies the shared-layer promotion, and distinguishes G34-01 as fixed rather than debt. This satisfies the requested disposition check.

## What is new since round 1

The five original commits were rebased onto `05d26fe5`, ending at `e0ecdf22`; the independently regenerated range-diff is **5/5 identical**. All seven unit files are byte-identical before and after that rebase. LE-gate34 is the sole subsequent unit change: one file, **+8/−5**, exactly the two reader repairs above and two pure docstring insertions.

All **193 declaration headers**, their order, and every definition body are unchanged from round 1. There are no added or removed unit declarations. Against the new base, the count remains **141 added, 0 changed, 0 removed statement headers**. The frozen targets, their substantive proofs, and `EnhancedHardCore` are unchanged from round 1.

The base delta is **#316 and #317**, across eight Lean files. **#314 and #315 were already in round 1’s base.** Only `Foundations/BitLists.lean` from this delta belongs to the unit’s import closure; its addition is `headD_drop_ofFn`, and the public `headD_drop` used by LE-gate34 is unchanged. The closure remains **128 files**, with only `BitLists.lean` and `Efficiency.lean` differing from round 1’s source archive.

The remaining changes are the refreshed verification evidence and the explicit finding dispositions. The live PR metadata also identifies the requested Lean head.

## Verification

All checks below were independently recomputed from Git objects or checked against the supplied raw evidence; pack summaries were not treated as proof of their claims.

| Check | Result |
|---|---|
| Pack integrity | **16/16** top-level SHA-256 entries pass. All 17 pack files match the pinned exchange objects. The landing ZIP verifies **459/459** hashes and exactly 460 manifest-covered entries; the verification ZIP verifies **22/22** hashes and exactly 23 entries. No duplicate or unlisted archive entries. |
| Bundle and sources | All **11 bundle sections** match their declared pinned sources. All **128 source files** match the Lean tree and equal the independently computed import closure. The seven-file PR diff matches `pr.diff-r2.txt` byte-for-byte. |
| Records provenance | The three verification records match their declared `b0ebd475` provenance. At the requested campaign pin, the ledger and review remain identical; the plan only appends the round-2 registration row. Round-1 pack and findings content are preserved. |
| Frozen checks | LE-gate34’s parent comparison is empty for statements. Its frozen evidence has 38 → 38 declarations, zero HEADER/BODY differences, and only two PROSE insertions. The header control adds exactly one HEADER difference. Independent source comparisons confirm the permitted change. |
| Integration build | **270/270** unique module records have return code zero. Every source hash matches `b0bad23a`; every raw log hash matches its record. Both diagnostic forms and the `error` substring count are zero. The build set equals the independently recomputed downstream of **76 changed modules** since `eff2dcd0`, covering the integration with #314–#317. All seven unit modules have zero warnings. |
| Rule 10 | All four refreshed Efficiency probes reconstruct the pinned source exactly after removing their recorded insertions. Probe and log hashes match. Strict A/B verify **1110/1111** requests; canonical-coercion A/B verify **1109/1110**, at both installation and EOF, with return code zero and no errors. The supplied runner invokes `lean -DmaxErrors=0`. |
| Paired controls | Canonical controls: **4 probes, 9 sealed negatives**, all correct. Strict controls: **4 probes, 11 sealed negatives**, each negative fails exactly once. Their only two discrepancies are the already disclosed `ctlCoeReader` failures; unsealed controls pass. No new Rule-10 defect is exposed. |
| Axioms and admissions | All **234 census constants** use only `propext`, `Classical.choice`, and `Quot.sound`; the two repaired readers use only `propext`. Both targets and `otProtocol_hbcSecure` print the standard three. The full-order admission count is **214**, versus **216** at the base, exactly the two removed target admissions. Yao’s disclosed `sorryAx` is unchanged from the base. |
| Whole-tree records and restore | All **1255 module records** match the head source hashes and recorded object hashes. The raw head checker says `RESULT FAIL` solely because the two disclosed probe oleans remain outside its module order: zero bad module records, object mismatches, or missing modules. The post-restore check is **RESULT OK**, with the original snapshot restored. |
| Lint | FAIL/WARN diagnostic sets are unchanged: Cryptography **92/101**, Complexity **25/391**. Cryptography’s informational inventory changes to include the six helper files. |

## Duplication and merge scope

No copied proof or declaration was added by the round-2 patch: the complete unit delta removes the two case-split proofs and replaces them with public-lemma calls. I also reviewed the newly available history/list, coin-length, probability, closeness, and negligible-function statements against the existing OT helpers and the recorded disclosures. No further undisclosed public-lemma duplicate was found.

As a mechanical cross-check, the **107 new OT theorems** have no identical normalized binder-and-type statement among the **1000 candidate theorems** in the tip delta and the recorded #319/#323/#324/#326/#327 changed files. This exact-statement scan is an aid, not an assertion that syntactic matching decides semantic duplication. Existing DL-47/DL-48 dispositions remain respected.

The six recorded trial merges are clean when independently regenerated; their tree hashes match the pack. I found no concrete new name or instance interaction requiring a finding.

**Audit limit:** Lean was not rerun locally. This is an independent source and supplied-evidence re-audit. The merged-tip rebuilds involving merged #313 and #319/#323/#324/#326/#327, and the concurrent combined build of all open PRs, remain the maintainer’s pending merge conditions, as instructed. They are not audit deficiencies, and this CLEAR verdict does not certify those pending builds. The user dispatches and merges.
