# Pass–shelat Gate 20 — external Codex audit

**Verdict: HOLD.** Counts: **0 blockers, 1 major, 1 minor, 0 notes**.

The source review found no audited statement drift or demonstrated mathematical defect. The gate remains open because required raw verification evidence is missing. Two small, eligible duplication folds also remain.

## Pins and scope

- Repository / draft PR: [Shilun-Allan-Li/tcslib #298](https://github.com/Shilun-Allan-Li/tcslib/pull/298).
- Audited Lean head: `6f853adc61d5d175ee83c69f6c07ab2da112cabc`.
- PR base: `2ea4df08d009a4bbdb8042795ff062d7f22db325`.
- Campaign records: `3015c622434a0321e784a3da1d83c125b426bf7e`.
- Exchange / pack: `1350b6083bb08760ab32ada31da63a860377c7f9`, `outbox/gates/20-dl-consolidation-gate/`.
- Scope: DL-30–DL-34 promotions, deletions and uses; all five landing edits, including the #297 re-points. Deferred DL-36/DL-37 work is excluded, apart from the explicitly landed deletion.

## Findings

| ID | Severity | File / declaration | Claim and evidence | Proposed fix |
|---|---|---|---|---|
| G20-01 | **major** | `verification.zip`, `landing.zip`: baseline census, whole-file seals and paired-control evidence | The archives omit necessary raw evidence, beyond the documented omission of generated seal sources. `verification.zip` omits **80 baseline and 82 initial-head seal logs**, their run records, the baseline census/collector logs, and the review control plan/sources. `landing.zip` omits **all 22 nm-sim seal logs**, their run records, and the seal request records/manifests. These files are named and hashed in the inner manifests but absent from the ZIP entries. No loose counterparts occur in the pinned final-delivery paths. Consequently the reported whole-file coverage, baseline comparison and 22/22 nm-sim seal result cannot be checked from their raw runs. The three final re-sealed modules and the separately supplied nm-sim paired controls do not supply those missing runs. | Supply the missing baseline/head census and seal request records, instrumented sources or reproducible generation inputs, raw logs and `results.jsonl`, plus the review control plan/sources. Include both seal variants and update the pack manifests. Existing originals matching the recorded hashes suffice; rerun only evidence that cannot be recovered. |
| G20-02 | **minor** | `Asymptotic/UniversalPadding.lean:180`, `PadQuad.ofFn_arrowCongr`; `Asymptotic/OneWayLemmas.lean:75`, `OneWay.ofFn_block_eq_take_drop` | Two disclosed copies have straightforward folds that the delivery review’s “Debt now foldable” list misses. The private `ofFn_arrowCongr` has the same statement as promoted `ofFn_arrowCongr_finCongr`, and retains two uses at lines 190 and 199. The public block-window theorem still re-proves the new `FunFamily.ofFn_blocks` result. Worker §11 says that relating the functions would require unfolding; the published `FunFamily.blocks_apply` reader supplies that relation. Both files already depend on `Adversary`; neither fold needs an import cycle or an audited statement change. | Delete the private width-cast copy and re-point its two uses. Preserve the public block-window statement and derive its proof from `FunFamily.ofFn_blocks` through `FunFamily.blocks_apply`. Rebuild the affected consumers. |

Concrete missing-file examples for G20-01:

```text
verification.zip:
  base-census-run/mods/DlProbe_CensusBase.log
  base-probe-runs/mods/DlProbe_CollectBase.log
  base-seal-runs/results.jsonl
  base-seal-runs/mods/DlProbe_BaseSeals_BaseSealA_Cryptography_Asymptotic_Adversary.log
  seal-runs/results.jsonl
  controls/out/controls-plan.json
landing.zip:
  seal-runs/results.jsonl
  seals/A/manifest.json
  seals/B/manifest.json
```

The omissions inventory and all 184 missing active seal-log paths are in the accompanying evidence. The old worker seal corpus predates the landing edits and #297 rebase; it does not certify the final landing.

## Independently checked

1. **Integrity.** All **17/17** outer SHA-256 entries match, including all three ZIPs. Included inner-manifest files also match: **1413** in `verification.zip`, **96** in `landing.zip`, and **4/4** in `statements-r2/`. The respective main inner manifests additionally name **1028** and **92** omitted files. Both evidence ZIPs are the same Git blobs as their pinned campaign-record counterparts.
2. **Source identity.** All **240** source-closure files match Git blobs at the audited head. All **50** `source-head.json` hashes match. A freshly generated Git diff is byte-identical to `pr.diff.txt` with `--abbrev=9`: **51 paths**, **1471 insertions**, **1469 deletions**.
3. **Statement freeze.** Re-running the supplied textual declaration comparison gives **68 added, 42 removed, 2 moved, 0 changed** public headers. A separate byte comparison passes for **all 16 named endpoints**, including `padded_cpa` across its file move, and for `castImpl_snmImpl` and `castImpl_indImpl_abs`. Context and name-resolution changes were also reviewed. This does not replace the missing elaborated baseline census.
4. **Landing edits.** LE-split moves `section PaddedCPA` byte-for-byte at its commit. LE-review changes only comments/whitespace in six files. LE-rule10 replaces the exposed OracleSecurity body reads with published readers; the six available final seal probes for PaddedCPA, BitwiseCPA and TrapdoorCPA have source/probe hashes matching the supplied files and final sources. The #294/#297 changes reviewed are consistent with their name re-points, removed selective opens, wrapping, and the one DL-37 deletion.
5. **Promotions.** Reviewed the probability, simulation, codec, block, list and handler APIs against their deleted forms. The two S1 forms have different hypotheses and appropriately remain separate. P2 is a corollary proved through `Bridge.expect_sample_pair`. R3 retains arbitrary initial state through explicit casts and specializes to the deleted BitwiseCPA form at `none`. R5 retains the constant-answer theorem as a specialization. R7’s statement-freeze escalation is justified.
6. **Build/axiom evidence.** All **15** supplied final rebuild records have `rc = 0`, zero errors and source hashes matching Git. The aggregated build records have **1229** latest module records with no failed latest run; all **240** source-closure hashes match their latest build records. The available head censuses contain **2099** consolidation constants and **572** nm-sim constants; only the four identified Yao constants use `sorryAx`, and nm-sim’s census has none. The 16 endpoint axiom prints list only `propext`, `Classical.choice`, `Quot.sound`.
7. **Controls and policy.** Rechecking the supplied nm-sim control plan against its raw logs gives **8/8** expected probe outcomes, including **38** sealed negative controls. **1297** available latest result/log hash pairs match. The 240-module TCSlib source import closure is complete and acyclic. No new `@[simp]` appears; line/width counts match the manifest, with no per-file increase in over-width lines. ElGamal remains the inherited size exception. The recorded lint delta and deferred DL-36/DL-37 items are not additional findings.

## Verification boundary

This audit independently checked source, Git objects, hashes, declaration text and available raw evidence. **No fresh Lean elaboration was performed.** Build and axiom results above describe the supplied, checked records. Full Rule-10 closure and elaborated baseline-census claims remain unverified for the precise omissions in G20-01.

The user dispatches and merges. No repository changes, review submission, push or merge was made.
