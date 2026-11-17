<!-- Filed by the maintainer on 2026-11-17 from the auditor's reply, uploaded by Seyoon. Verbatim below. -->

**Gate 44 pairing fills — round 2 findings**

**Verdict: CLEAR. Open findings: 0 blockers, 0 majors, 0 minors, 0 notes.**

All three round-1 findings are closed. DL-55 and DL-56 remain accepted debt scheduled for cleanup Stage 2; closing G44-01 does not mean that repayment has already occurred.

| Audited item | Pin |
|---|---|
| Exchange | `2e0152540aae5bb1ce7f8061572aedc5a4fc5437` |
| Campaign records | `4f4a7592a54cf82fa04f96b83645d7936672614c` |
| PR #340, T1 | `916afc25c21f5e52b4b01958186ad55d2f615fd1` — unchanged |
| PR #346, T4 | `98cb0e521a94e94c304c78348fb5d3033435a3ed` |
| Joint tree T44′ | `bee027f0903d531b3a43511cea16bfa123210291` |
| Round-1 joint tree T44 | `33681cb8ed893a897ca2028d5ada70ca29237978` |

| Finding | Previous severity | Disposition and evidence |
|---|---|---|
| **G44-01** | Major | **Closed by explicit acceptance and scheduled repayment.** At the records pin, the plan's ruling, ledger rows DL-55/DL-56 and Stage 2 scope agree. DL-55 identifies the published verdict identity, its promotion to a shared low-level home importable by both layers, and the subsequent re-points of `TrapdoorPredictor` and pairing T1. DL-56 identifies the four projection facts in `Games/Efficiency` as the shared home and schedules the four re-points, with a reader there if required. Both identify Seyoon's acceptance and cleanup Stage 2 as the repayment point. This satisfies policy §1. Both reports retain their original disposition with an accurate dated correction; the bb1-machine review carries the matching correction. These copies bind to staging records commit `bb0199d6dc6753996e674b6a5dcdcb49b092f5f9`, after the records pin, as disclosed. |
| **G44-02** | Minor | **Closed by LE-g44.** Its sole parent is round 1's #346 head. Only `BonehBoyenMachine/Draws.lean`, `Words.lean` and `Handler.lean` change, by +22/−7 lines. Each is byte-identical to its parent after removing comments, including nested block comments and docstrings while preserving strings. The sampler attribution is correct: `Candidates.sampleBelowL` supplies the construction, and `Candidates.statClose_sampleBelowL` supplies precisely the stated fixed-coin, fallback-zero statistical bound. The unchanged `statClose_draw` applies that theorem. PS10 §2.8/Theorem 52.3 is consistently marked as context for easy domain sampling; all three References entries are corrected. |
| **G44-03** | Note | **Closed by the corrected figures.** Raw logs and control records confirm, per strict/coe variant, **2 sealed and 2 unsealed probes**, with **25 negatives: 12 in A and 13 in B**. Across both variants: **4 sealed, 4 unsealed, 50 negatives**. Every negative fails exactly once, every reader passes, and both unsealed probes have zero errors in each variant. Both control checks report `ALL_OK True`. |

The T44′ evidence binds to the audited heads and shows no regression:

| Check | Result |
|---|---|
| **Integrity and bundle** | **Pass.** All **14/14** outer checksums and **132/132** inner verification checksums pass, with exact file sets. All **30** bundle sections match their separate pack, archive or pinned repository sources. All seven Lean copies in `sources-r2.zip` bind to pinned git blobs. The round-1 material used for comparisons matches its specified exchange pin. |
| **Merges and delta** | **Pass.** Independently reconstructed T44 and all **six** permutations of the records pin and two PR heads. Each merge is clean and yields T44′. Its nine changed paths relative to the records pin equal their respective PR-head blobs. The entire code diff from T44 to T44′ equals `le-g44.diff.txt` byte for byte. The records advance adds no code change. |
| **Replay and state** | **Pass on supplied replay evidence.** Independently recovered the **10-module** downstream subset; the build queue covers it exactly. All ten source/log/output hashes bind, all return rc 0, and no build log contains an error. The only warnings are the two inherited T2/T3 admissions. The copied state hash matches round 1's final state. The plan builds 10 and reuses 1417; the unchanged full root/audit order contains **1427 modules**, all reported OK by the final state check. The nine replay-tool hashes match round 1's supplied tool bytes. |
| **Objects and preservation** | **Pass.** All ten rebuilt oleans have link count 1, different inodes from the base output, and no `.ilean`. Seven are byte-identical to T44's; only the three documentation-edited modules differ. The 1458-entry output maps independently compare as **1455 equal, 3 changed**, with no additions or removals. The new map hashes to `fca1b6a308ac1585fb5897fae95e8294b54be55e160119e4eca1702692b41ef9`. Snapshot #4's before/after/final rehashes report **0 extra / 0 changed / 0 missing**. The old-output rechecks and subsequent deletion record are consistent with preservation of the new output. |
| **Admissions and axioms** | **Pass.** The recorded per-module admission counts are identical: **196 → 196**, with zero in the three edited owners. The axioms probe hashes to both rounds' run records; its log is byte-identical to round 1's. T1 and T4 use only `propext`, `Classical.choice` and `Quot.sound`. The nine-owner census reports **604 constants, 0 nonstandard axioms**. `bb1_sidSecure` still reaches `sorryAx` exactly through the two out-of-scope T2/T3 statements. |
| **Canonical coe-A seals** | **Pass.** Draws **1644**, Words **2242**, Handler **2275**, and BonehBoyenMachine **2311** requests. All four runs have rc 0 and zero errors. Independently checked source/probe/log hashes, exact source recovery after removing harness insertions, identical request rows/readers/exclusions and insertion payloads, and complete install/EOF coverage. Comparisons use round 1's `rel/` request-set record for Draws, as disclosed. |
| **Lint** | **Pass: no regression.** Non-INFO campaign output is byte-identical: **92 FAIL / 104 WARN over 524 files**. INFO differences are only the three line counts. The supplied three-file style check reports zero findings, and `sk15` has zero hits. |

**The remaining round-1 seals can be carried forward; a rerun is unnecessary for this delta.** Every other code source is blob-identical, the three edited owners have identical code after comment removal, and both the collector probe and its complete log are byte-identical to round 1's. The four new canonical seals additionally confirm unchanged requests and harness behavior against the new output. Together these justify carrying the strict/coercion A/B variants, paired controls, supplement seals and explicit-unfold results within this round's stated scope.

**Round 1's passes still hold and were not re-audited.** No change reopens the proof or edge-case conclusions, frozen statements and statement prose, seven readers, LE-bb1m, declaration inventory, name-clash result, or the prior grading of BM-F01–BM-F09 and #340's disclosures. Item 5 and the four projection re-derivations now have the acceptance records required by G44-01.

**No new undisclosed change or finding was identified.** The three corrections' post-pin provenance is accurate. Live PR checks confirm #346 is pushed to `98cb0e52`, #340 remains at `916afc25`, and both descriptions now disclose the resolutions. The other known slips remain compatible with the audited material.

I did **not** run a fresh Lean compilation. Compilation, axiom and filesystem-preservation conclusions rely on the supplied hash-bound replay/probe records, independently recounted and checked against pinned sources. Git reconstruction, checksum verification, source binding, comment removal, map comparisons and seal-record comparisons were performed locally.

Gate 40, the T2/T3 fill and #351/#352 remain outside scope. Merge order and snapshot adoption remain maintainer conditions. The user dispatches and merges.
