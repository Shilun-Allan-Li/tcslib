# Pass–shelat Gate 36, round 2 — sc-garble

**Verdict: CLEAR. 0 blockers, 0 majors, 1 minor, 0 notes.** Round-1 finding **G36-01 is closed**. No new undisclosed duplicate was found. The new finding, G36-02, corrects the reported control counts; the underlying controls behave as required.

| Pin | Audited revision |
|---|---|
| Repository / draft PR | `Shilun-Allan-Li/tcslib` / [#323](https://github.com/Shilun-Allan-Li/tcslib/pull/323) |
| Lean head | `8c3f3e3fe2912784f680c10f8c478d2eeeeb7f6a` |
| Lean tree | `41e3febe1241c7af505bc208b72092cfd2e5f513` |
| Round-1 head / direct parent | `cd9a48438c2a6548fe9e246ce569be57c9df96b3` |
| Unchanged branch base | `1321b9cb358867f5b51974b8c5d0781519a9cfdb` |
| Campaign records | `298338e34bb6a4c1754d406244ceeed7e8be6338` |
| Exchange | `0bdffba74f2798b9f8aba4df3234e4dea58e9369` |
| Build base, including merged #313 | `654323f27fbbed3a1b3664908b6c14cf563e52a2` |
| Built replica tree | `5662520d23695e1451bb3aa849ace82f71685393` |

I read the pinned README, `pack-r2.md`, bundle, resolutions, round-1 pack and findings, and the relevant source and evidence. I independently replayed hashes, source and declaration comparisons, import closures, merge trees, and checks of the supplied build, seal, axiom and admission records. **I did not execute Lean:** compilation and kernel outcomes below are verified supplied evidence, not an independent compilation.

**Round-1 finding**

| # | Original severity | Status | Closure evidence |
|---|---|---|---|
| G36-01 | major | **CLOSED** | LE-gate36 deletes `SliceReduction.length_le_encodeList` and its docstring, replaces its sole use with `TCSlib.Cryptography.length_le_length_encodeList`, and adds the acyclic provider import. Declaration, frozen, build and seal checks support the repair. |

The complete change since round 1 is one commit on `cd9a4843`, affecting only `TCSlib/Cryptography/SecureComputation/SpecialEncryptionMulti/SliceParser.lean`: **+2/−11**, in exactly three hunks. At the head, line 5 imports `Asymptotic.BlockEncryptor`; line 161 uses the public lemma in `slicePost_encode`. The deleted name has zero occurrences in `TCSlib/` and `audits/`, versus the declaration and one use at round 1. There is no replacement re-proof.

The public provider, `TCSlib/Cryptography/Asymptotic/BlockEncryptor.lean:70`, is unchanged at the branch base, build base and head. `SliceParser`'s closure grows **147 → 149**, including itself, by exactly `BlockEncryptor` and `Encryption/PrivateKey/FromPRG`. `BlockEncryptor` does not import `SliceParser`, directly or transitively. The whole unit's closure grows **166 → 167** because `FromPRG` was already present elsewhere in it.

**New finding**

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| G36-02 | **minor** | `pack-r2.md:104–106`; `landing-r1/PROVENANCE.txt:80–83`, including the archived copy | Paired-control summaries overstate the number of sealed negatives: coe **7** and strict **9** are reported, but the actual counts are **5** and **7**. | Both `controls-plan.json` files, `mkctl-{coe,strict}.log`, `ctlcheck-{coe,strict}.log`, and raw diagnostics agree. See `evidence/G36-02-control-counts.txt`. | Correct the summaries and their bundled copies to coe **5**, strict **7**. State separately that strict has **2** disclosed positive-reader failures, giving **9 total strict diagnostics**. Preserve the raw evidence. |

Paths in this finding are relative to `outbox/gates/36-sc-garble-gate-r2/`; raw control files are inside `landing-r1/gate36-le-evidence.zip`, under `rule10/`.

| Variant | Sealed A negatives | Sealed B negatives | Total negatives | Positive-reader failures |
|---|---:|---:|---:|---:|
| Coe | 2 | 3 | **5** | 0 |
| Strict | 3 | 4 | **7** | 2, both `ctlCoeReader` |

Each variant has four probes: two sealed and two unsealed. Every actual sealed negative fails exactly once, every unsealed control passes, and there are no unattributed errors. The new `encodeList` negative fails and its published-reader positive passes in both variants and both A/B runs. Thus G36-02 is a reporting defect, with no missing control needed to close G36-01.

**Replica and evidence verification**

| Check | Result |
|---|---|
| Pack hashes | Round 2: **16/16** manifest entries verify. Round 1 at `ab34c528…`: **20/20** verify; its pack is preserved verbatim. |
| Nested archives | `verification-r2.zip`: exactly 22 manifest paths plus its manifest, all hashes valid. Landing ZIP: exactly 628 manifest paths plus its manifest, all hashes valid; external and internal manifests agree. |
| Bundle / records | All nine bundle sections equal their pinned source or campaign-record blobs. All four archived verification records equal their stated `b0ebd475…` originals. |
| Sources / diff | All **167** source-archive files equal head blobs. Relative to round 1, only `BlockEncryptor` is added and only `SliceParser` changes. All 14 source-head hashes, line counts and width counts verify. The full PR diff equals the pinned base-to-head diff. |
| Declarations | Replayed decls2: round 1 → head is **exactly 1 REMOVED**, the duplicate; base → head is **54 ADDED, 0 CHANGED, 0 REMOVED**. All **259** surviving unit declarations retain their headers and docstrings. |
| Frozen check | Replayed against the issue base: **0 unexpected differences**, with exactly the six SG-1 removals. Round 1 → head across all 14 files: **0 unexpected differences**, with only the duplicate's removal allowed. |
| Built-tree identity | Independently computed `merge-tree(654323f2, 8c3f3e3f)` = **`5662520d23695e1451bb3aa849ace82f71685393`**, exactly the built tree. The corresponding round-1 merge equals replica parent tree `63ce05ff…`; its edit diff is byte-identical to the pushed patch and the landing evidence diff. |
| Later pack tip | Merging the head with `b0ebd475…` gives `f9041e78…`, whose `TCSlib` and `audits` subtrees equal the built tree's. |
| Integration build | **392/392 rc 0**, zero errors in both diagnostic forms and zero `error` substrings. Every raw log hash and diagnostic count verifies; every recorded source hash equals its built-tree blob. All 14 unit modules, their 277-module downstream, root `TCSlib` and both audit `Checks` are covered, in import order. |
| Object records | All 392 object-digest records agree with the supplied head snapshot. **390/392** source/object pairs match a supplied reference build; the two exceptions are the disclosed `SliceParser` and `SliceReduction`. The latter's rerun reproduces its digest. This checks recorded hashes, not unavailable object-file bytes. |
| Rule 10 | All four new `SliceParser` seals pass: strict A/B **2102/2103**, coe A/B **2101/2102** requests. Rechecked exact eligible closure coverage, all seven foreign-definition references, source reconstruction, source/probe hashes, complete installation and EOF verification, and `maxErrors = 0`. Controls have the corrected counts above. |
| Axioms | Supplied output gives exactly `[propext, Classical.choice, Quot.sound]` for the seven targets, B2 and `slicePost_encode`; the public length lemma uses `[propext, Quot.sound]`. The disclosed Yao downstream admissions remain outside these endpoints. Probe hashes and raw output agree. |
| Admissions | Independently recomputed **215 → 208** from source-matched rc-0 records: 1253 modules at the build base, 1261 at the built head. Only the seven target admissions disappear. The same 34 modules lack matching records at both revisions; all 34 sources are unchanged. These totals describe the source-matched census. |
| Trial with #324 | Reconstructed trial tree **`a025d7ab…`** in both merge orders. Its **19/19 rc-0** records have zero errors/admissions, matching raw logs and trial-tree source hashes; all 19 source/object pairs match the supplied combined-build reference. |

Building the replica loses no source coverage for the specified merge into `654323f2`: the entire merge tree is identical. This is an integration build for that tree, rather than a claim that the unmerged pushed tree itself was compiled.

**Duplication and changes since round 1**

No declaration is added since round 1, and the only changed surviving proof line invokes the existing public lemma. The seven target proofs, B2, the direct-D4 route and the other source audited in round 1 remain unchanged. Their round-1 correctness and integrity conclusions therefore stand, supported by the new integration evidence.

As an additional search, I compared all 46 theorem statements newly introduced by the PR against 20,735 theorem/lemma statements at the branch base, the newly imported provider, the five merged Learning files, and the changed files of pinned #318, #319, #324, #326 and #327. Exact normalized-signature matches were only the two SG-1 private readers already replaced by public ones; no new overlap was found. This mechanical search supplements the complete delta comparison and round-1 audit; it is not a semantic completeness claim. DL-46 and DL-47, including SG-F04, retain their accepted dispositions.

The maintainer's integration rebuilds on the merged tip with #318, #319, #324, #326 or #327, whichever merges second, and the concurrent combined build of all open PRs remain **pending merge conditions, not audit items**. They do not reopen G36-01. Dispatch and merging remain with the user.

The accompanying ZIP contains this Markdown, the auditor's replay scripts and results, declaration/frozen reports, and the control-count excerpts.
