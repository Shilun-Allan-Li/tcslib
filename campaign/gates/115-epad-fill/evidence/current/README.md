# Gate 115 executed evidence

Lean head: `b6c2f5e4b8ce3bc18c385a09a3bf5dc26b75c205`. Baseline: `680760723d72826469d0fc294e4d7ee2ecac3e6c` (the complete native `oleans-mac0` snapshot, 894 modules, zero failures). These are actual maintainer runs. The delivery's original logs are historical agent evidence, clearly separated in its verbatim receipt.

| Check | Executed result |
|---|---|
| Source freeze | 3 public source declarations preserved, 49 new private; no surviving statement/visibility/order changes; only the authorized public proof body changes |
| Module plus three boundary probes | Passed; target uses only `propext`, `Classical.choice`, `Quot.sound`; padLang and its defining iff have no axioms |
| Independent merged-tree replay | 2 modules, 0 failed, 0 static mismatches; the one admitted declaration becomes proved (1 → 0) |
| Complete axiom walk | All **506** compiled module constants, including private/generated ones, use only the standard three axioms |
| Unfiltered non-private census | **3 → 6**: three preserved source declarations plus three new internal proof auxiliaries, listed below |
| Foreign-definition inventory | **46** direct foreign definitions = **36** effectively sealed + **10** explicit exclusions; every listed seal appears in the fresh walk |
| Full sealed source | Passed with the three reachable default-simp definition unfoldings removed |
| Controls | 36 pointwise + 36 parameter-abstracted equations close unsealed; all 72 fail sealed, with exactly the expected 72 errors and no successful reflexivity attempt |
| Exclusion checks | Four expected reducibility-validation errors for ARM/AConf/BankS/Ins.casesOn; matcher control closes both before and after its attribute, documenting the limitation |
| Citation inventory | **122** foreign constants from **20** source modules; all are in the complete **23-file** screen/bundle population |
| Copy-text screen | 335 → 335 pairs, zero new or removed; see the raw outputs and semantic classification |
| Lint and blueprint | Both blueprint checks pass. Policy head has only the 1,769-line size finding, governed by the standing no-size-driver ruling; raw base/head campaign lint remains supplied |

The three new non-private compiler constants are:

- `Complexity.mem_SPACE_padLang._proof_1_1` (theorem, internal=true).
- `Complexity.mem_SPACE_padLang._proof_1_2` (theorem, internal=true).
- `Complexity.mem_SPACE_padLang._proof_1_3` (theorem, internal=true).

They are compiler proof auxiliaries, not new public source declarations. `PublicConstants.out` and both changed-module censuses are unfiltered. This independently confirms the count discrepancy in the original REPORT; that report remains unedited.

`checks.json` records the cross-checks. Exact inputs, output/exit lines and per-run input checksums are retained. The source census, replay/static results, every control, the inventory partition and citation coverage were reconciled before staging. Full baseline sources and both source versions needed for the comparisons are provided; unchanged population files have identical baseline/head blobs.

The initial failed preflight and control-design attempts remain labeled separately. The corrected preflight and full seal used completed baseline import closures while bootstrap continued; the later two-module replay is the merged-tree check. Imported metadata and boundary probes use that passed PR snapshot. The matcher exclusion remains an explicit limitation for the auditor to challenge.

The user raised this Mac's global cap to five during these runs. The two long replays were suspended during the earlier cross-campaign overlap and resumed; this campaign now budgets three slots, leaving two for Pass–Shelat. No external process was signaled.

**Ready to dispatch** once the verified bundle is staged. **Not yet clear to merge:** gate 115 has not closed. After another Lean merge, reassess/replay the combined tree before clearing a PR.
