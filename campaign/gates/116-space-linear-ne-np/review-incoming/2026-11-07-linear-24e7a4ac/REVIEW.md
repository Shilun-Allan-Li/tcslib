# Gate 116 incoming audit — independent maintainer crosscheck

**No blocking issue, source fix or new design decision found.** The received verdict
is consistent with the pinned evidence: **PASS — 0 blockers, 0 majors, 0 minors,
12 notes**. The root maintainer can adopt the report and record the gate disposition.
This review itself does not close the gate or authorize a merge; the replay/current
base conditions remain the maintainer's responsibility.

The original findings remain untouched: **8,968 bytes**, SHA-256
`24e7a4acf34bdd0bc103144d93c2d94b37a4a4d0265f9ab309ac44f0ddd5830c`.
All twelve numbered rows are notes, and the verdict count agrees. The preserved
report's source-citation rendering artifact has no bearing on the findings and was
not edited.

## Immutable dispatch and primary evidence

The actual exchange bundle is **3,217,942 bytes**, SHA-256
`ed39955fc328b4d49eb21677237d564edf0eb1c02efffcd8a2477b6511907b9e`.
All **217** section names exactly match the published index, in order. Dispatch pins:

- Lean: `74494d669ad9f8f926844f9280812449f57263d6`.
- Records: `63a41dcdc5f13b64b8f70e3e3265217aa9cea4ad`.
- Exchange publication: `bc19751769ad912465fcaa54c803f5bf82f6ecee`.
- Current-context source base: `3555163f40d9c101a2ef4e81407c1bda58fe5ca4`.

The **current-after-natbits** evidence is primary. All **22** archived source files
(eleven base and eleven head) match both their SHA-256 pins and Git blob hashes
computed directly from their bytes, and match their exact immutable bundle sections.
Only Hierarchy differs between those two populations. Moving worktree records were
not substituted for the frozen packet. No Git/archive operation was rerun here.

## Note-by-note disposition

| Note | Independent disposition |
|---|---|
| 1 | **Supported.** Bundle identity, byte length, index order and source-content pins reconcile. The auditor reports its own Git-archive comparison; this review independently checks the archived bytes and their recorded blob hashes without Git. |
| 2 | **Supported.** `SPACE` quantifies a finite binary decider and natural multiplier, including zero. The model sums visited work cells, including each head's initial cell. Literal bound `n` therefore forces zero tapes at the empty word; the inherited positive normalization `n+1` is disclosed and unchanged. |
| 3 | **Supported.** `NP` uses an exactly specified polynomial certificate length and concatenated verifier input, with coefficient zero permitted. The padding/preimage proof uses the bounded paired characterization and published preimage closure, rather than treating arbitrary concatenation as injective. |
| 4 | **Supported.** Pairing doubles the first word, appends `[false,true]`, then the second word. The unchanged helper applies the public first-projection left inverse to padded-image equality. No new pairing implementation is introduced. |
| 5 | **Supported.** `padLang` is exactly the image of members under unary padding, with its public membership iff. Malformed encodings and incorrect pad contents/length cannot enter that image. At empty original input the pad length is one, so `pairEncode [] []` is excluded. |
| 6 | **Supported.** At `S(n)=n²+1`, `T(m)=m+1`, padding coefficient one and degree two, `m=n²+4n+3`; hence `S(n)≤T(m)`. The second bound is reflexive. This padding coefficient is independent of the source decider's arbitrary space multiplier. The local set equality supplies precisely the frozen helper's padded language. |
| 7 | **Supported, with the stated execution bounds.** Empty input gives pad/paired lengths 1/3 and bounds 1≤4; either one-bit input gives 4/8 and 2≤9. Empty-language/zero-tape rejection permits multiplier zero and requires no division or positivity assumption. The auditor's Python counts are supplementary finite checks, not Lean or machine-simulator evidence. |
| 8 | **Supported.** Under class equality, padding a quadratic-space language places its image in linear space and NP; polynomial preimage closure pulls back to NP and linear space. Pairing's left inverse proves the preimage identity. Constructibility and eventual domination contradict the existing strict hierarchy. The theorem asserts inequality, without choosing a direction of noninclusion. The official-source indexed-text/403 limitation is explicit. |
| 9 | **Supported.** Independent raw-source comparison preserves all 47 headers, visibility and order (4 public/43 private); only the approved Padding import and target body differ. Raw compiled censuses independently parse as 4→5 non-private and 137→138 total, with 133 private each. Sole addition: internal theorem `Complexity.SPACE_linear_ne_NP._proof_1_1`; no removal or kind/owner change. |
| 10 | **Supported within screen scope.** Both supplied screen output hashes match their receipts. Independent parsing reproduces 247→248 eligible bodies, 31→31 directional pairs and 5,917 reproduced characters; every pair and measurement agrees, and the target occurs in no pair. The new 13-line body is interface glue using the unchanged helper and published padding facts, not a machine/host or copied validator. No new debt acknowledgment follows. |
| 11 | **Supported.** The inventory covers target plus its sole auxiliary, with exactly four direct foreign definitions (`SPACE`, `NP`, `padLang`, `pairEncode`) and no exclusions. The strong seal restores the pinned source after removing its declared wrappers and their two added blank separators. Four default-simp unfoldings are removed. Input hashes match; seal records exit 0, positive controls exit 0, and the sealed controls exit 1 with exactly one failure at each of lines 10,12,14,16,21,23,25,27. No extra failure is present. This certifies the new section's supplied check, not legacy proofs. |
| 12 | **Supported.** The target inventory lists only the standard three axioms; its auxiliary omits choice. The unchanged admitted `space_universal` is absent from this dependency chain. All five replay artifact hashes and sizes reconcile; raw replay/static logs report two modules, zero failures and zero mismatches, with one remaining F6 admission. The replayed modules are Hierarchy and its facade. The auditor explicitly disclaims rerunning Lean/replay. |

## Additional independent checks and execution limits

`crosschecks.json` records the actual receipt, source/blob checks, source freeze,
raw census parsing, control-line multiplicities, screen-pair equality and replay
artifact verification. The complete source bytes outside the target body and approved
import are unchanged; this is stronger than merely comparing normalized headers.
The source dependency candidate check finds the facade as Hierarchy's only direct
importer in the current local tree; the supplied pinned replay list contains exactly
those two modules.

An independently authored finite Python model checked 1,953 pair round trips
(`|x|≤4`, `|y|≤5`) and all 8,191 binary words through length twelve against unary-pad
shape membership. There are exactly three valid padded images within that latter
length bound. These checks corroborate the boundary arithmetic and image convention;
they do not identify or authenticate the auditor's unspecified Python test domain,
simulate the padding validator, or prove the general theorem.

The auditor reports an independent head-screen rerun and source/archive checks.
No separate auditor raw execution logs accompanied the findings, so those activities
remain attributed claims. This review reconciles the supplied raw screen/receipt data
and the mathematical claims; it does not turn them into a fresh execution by this
reviewer. The official Princeton exercise reference is an indexed-text receipt with
direct PDF retrieval failure disclosed; no fresh PDF download/visual inspection is
claimed here. Neither auditor nor this reviewer reran Lean or the merged-tree replay.

All twelve notes can be accepted without code changes. Canonical findings,
resolutions, gate status and merge clearance are for the root maintainer to publish.
This task wrote only this independent review and crosschecks in the incoming-review
folder. No canonical record/source change, Git, Lean, cache, screen, push or gate
closure was performed.
