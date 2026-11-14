# Pass–shelat Gate 24, round 2 — dl-crh findings

**Verdict: CLEAR.** G24-01, G24-02 and G24-03 are closed. No new finding arose from LE-reuse or the merged-tip integration.

| Blocker | Major | Minor | Note |
|---:|---:|---:|---:|
| 0 | 0 | 0 | 0 |

Audited [draft PR #307](https://github.com/Shilun-Allan-Li/tcslib/pull/307):

- Lean head: `d356381aadc350860f9a0e97123e84d9aefa585b`.
- PR base: `a757b6a18785377c158312ed051b1789cf45badf`.
- Campaign records: `a518558d26988753261c73b436c4493adbc16cb0`.
- Exchange: `9bdc6e341003529631f2b5b2d61c5399deba0969`, `outbox/gates/24-dl-crh-gate-r2/`.

The round-1 pack at the same exchange commit was checked alongside the round-2 README, pack, bundle and evidence. Severities below identify the **closed historical findings**, not outstanding findings.

| # | Severity | File · declaration | Claim / status | Evidence | Proposed fix |
|---|---|---|---|---|---|
| G24-01 | major, closed | `Hashing/FromDiscreteLog/Encoding.lean` · `inputWord_take` | **Closed by LE-reuse.** The public proof is now reused. | The body directly applies `take_ofFn_castLE`, with only finite-index extensionality and congruence afterward. `inputWord_split` additionally reads `ofFn_eq_init_append`. Both statements and docstrings are unchanged; the new import is acyclic. Expanded seals and controls pass in the archived runs. | None remaining for this finding. |
| G24-02 | minor, closed | `fills/dl-crh/final-r1/review.md` · Content, step 2 | **Closed by the explicit erratum.** Equal selectors are now correctly ruled out; different selectors invoke extraction. | The revised and pinned reviews differ in exactly three disclosed hunks. The pinned round-1 copy is byte-identical to the round-1 outbox copy. | None. The example requires challenge exponent zero, as disclosed in the round-2 pack. |
| G24-03 | minor, closed | Round-1 `pack.md` · ruling 3 | **Closed by the erratum in `resolutions-r1.md`.** | Raw lint records confirm identical FAIL lines and exactly two changed `DiscreteLog` WARN lines: size 1192 → 1212; missing readers 6 → 5. Both trial merges reproduce these same changes against their tips. | None. |

Paths abbreviated in the table are under `TCSlib/Cryptography/` or `briefs/pass-shelat-ch5-8/`, as applicable.

**What is new since round 1.** Exactly one Lean commit changes one file: 6 insertions and 4 deletions. Independently applying its patch to authenticated round-1 bytes reproduces the new file exactly. The entire change is one import and the two replacement proof bodies. All 197 unique declaration headers remain identical; no other declaration, attribute or docstring changes. The 128-file source closure matches the pinned Git blobs. Its only additions are `ReductionSupport.lean` and `Pseudorandom/Generators.lean`; among shared entries, only `Encoding.lean` changes. Both reused public lemmas are unchanged from the PR base.

**Rule 10.** The new import expands Encoding’s project closure from 65 to 69 modules without a cycle. Independently reconstructed strict A/B request sets contain 948/949 entries; coercion A/B contain 947/948. Every prior row remains identical; each set gains exactly 24 rows from the four added modules. Probe sources, run hashes, installation and EOF records agree. All eight paired-control probes behave correctly: ten sealed negatives fail exactly once, and reader and unsealed controls pass.

Retaining the other eight files’ round-1 seal results is justified here: their source and rebuilt olean hashes are unchanged, their build logs are identical, and the seven unchanged declaration-owning modules retain identical collected elaborated references. The expanded closure therefore introduces no new reads into their unchanged proof terms. The changed Encoding module receives all four expanded seals.

**Build and integration evidence.**

| Archived build | Independently reconstructed merge tree | Rebuilt modules | Whole-tree snapshot |
|---|---|---:|---:|
| LE-reuse | PR head | 22 | 1207 |
| Onto `996d7cc2` after #308/#309 | `c60af4c22099ad1d595a3d8f763770c79cc25202` | 48 | 1231 |
| Onto `fb674b96` after #306 too | `84a1cbd822d41ffe01ac4c4a6a7cabaa04e77e0d` | 61 | 1241 |

All rebuilt rows have exit status zero, zero errors and zero admission warnings; source and raw-log hashes were checked. Only Encoding’s olean changes in the LE-reuse build. Trial objects and logs match the available per-PR references. Their 22 compiler warnings are inherited. Snapshots agree with the latest successful archived object records, and all three restores reproduce the base snapshot exactly.

The merged branch’s 38 changed Lean files are disjoint from #307’s nine files. The first trial excludes #306; the second includes it. The merge onto records tip `47e6cf47` reconstructs tree `b8b1308afa0db9083b735b1f78505e88a86aed5e`, with identical Lean content to the second trial. Records commit `a518558d` also makes no further Lean change. Thus the second build covers the requested combination with #303, #306, #308 and #309.

No ambiguity or redeclaration diagnostics occur. The supplementary name probes report zero user-level overlaps; their 12/28 short-name overlap pairs are generated `congr_simp` lemmas. The reported dependencies of `dlHash_crh` and the four integrated security endpoints contain only `propext`, `Classical.choice` and `Quot.sound`. Lint remains 92 FAIL / 102 WARN at the PR head and 92 FAIL / 101 WARN at both trial tips and merges, with no added FAIL line.

**Integrity and limits.** All 23 top-level payload hashes verify. Nested manifests verify 209 LE-reuse, 142 first-trial, 152 second-trial, 9 verification and 128 combined-reference payloads, with exact archive member sets. No fresh Lean compilation was performed: this environment has no Lean executable. Compilation conclusions rely on the pinned archived runs, supplemented by independent source, patch, import, seal, control, Git-tree, log and snapshot checks. Snapshot checks establish recorded consistency; the oleans were not re-executed locally.

The remaining DL-41 debt and disclosed record slips remain as previously dispositioned. **No blocker or major remains.** The user dispatches and merges; no repository mutation or GitHub message was made.
