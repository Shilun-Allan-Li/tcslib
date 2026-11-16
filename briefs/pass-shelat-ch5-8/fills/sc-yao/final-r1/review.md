# sc-yao · maintainer delivery review (r1)

**Verdict: ACCEPT WITH LANDING EDITS.** The landing edits are LE-bullet, LE-reuse, LE-title (optional) and LE-doc
(the separate job, which closes SY-F04). Phase 2 is complete: the landing head builds with 0 errors through root `TCSlib`
and both `Checks`. `yaoHybrid_polyTime`, `yaoHybrid_simulators` and `yaoHybrid_hbcSecure` use only the standard three
axioms on the tip. Still open: Seyoon's confirmation of SY-F01, and his rulings on SY-F02 and SY-F03 (ledger
recommended). No PR has been opened yet.

## Delivery and landing
- **Delivery:** Codex on Seyoon's Mac, a lead and 3 sub-agents (SY-6). The final is exchange `47c38c47`; the checkpoints are
  `f0a9a616`, `816971fc`, `acc86827` and `171a341a`, and all touch only `inbox/fills/sc-yao/`. The issue base is `6ce4658d`;
  the worker tip is `6e7ef601`, with 8 unsigned commits.
- **Landing:** `land/pass-shelat-sc-yao` (local, not pushed), on the tip `f9fda8fe`.
  - **Head:** `e9b03c437aca251846430ff23b40ee5ff3d3347a`.
  - **Tip check:** origin has since moved to `15d8f01a` with records only. Between `f9fda8fe` and `15d8f01a`, `TCSlib`,
    `TCSlib.lean`, `audits`, `scripts` and the lake files are byte-identical. #324 and #327 are not merged.
  - **Commits:** the worker's 8, cherry-picked with author kept and committer Claude, SSH-signed: `b288691f`, `16ac8d64`,
    `65158baa`, `13403ddf`, `d9c2f53e`, `bb1a1bf6`, `fe88a3b0`, `e737096b`. Then LE-bullet `13690d2e`, LE-reuse `81d526d8`,
    LE-title `bd7832d7` and LE-doc `e9b03c43` (the LE-doc job's, fast-forwarded).
  - **Range-diff:** 5/8 identical. Commit 1 lost the `isFaninTwo_iff` hunk, which the merge absorbed because it is
    byte-identical to #323's; commits 4 and 7 differ only in the bullet resolution.
- **Files:** 70 changed against the tip:
  - `Yao.lean`, 1179 lines (970 after #323; at most 1,200 under SY-2);
  - `Uniform.lean`, with the seven SY-3 encoding readers;
  - the hub `Yao/HybridProof.lean` and 67 helpers.
  - `DAGCircuit.lean` is unchanged against the tip.
- **Evidence:** `review-evidence.zip`, SHA-256 `d3f7c3da0d081acd9275e798514fffd7b538c83787a109c11c59bab4e2c3b5a8`, 1511 entries; `evidence-SHA256SUMS` beside it. The working
  directory was `$SP/dl-review/sc-yao-r1/`, where `$SP` is this session's scratchpad.

## Checks
- **Integrity:**
  - The manifests verify 7597/7597 and 7515/7515, streamed from git, with exact path sets.
  - `git am` at the base reproduces all 8 hashes, with `COMMITS.tsv` signing "none".
  - `src/` equals the 71 changed paths byte for byte.
  - The issue package verifies 8/8, and its sources 184/184.
- **Scope:** own masking script `frozen_sy.py`, with controls.
  - In `Yao.lean`, everything outside the six approved regions is byte-identical to the base. The regions are the hub import
    after line 9, the bullet at 96–98, the sketches at 826–840 and 860–906, and the bodies at 843 and 918. These match the
    brief.
  - The bodies contain no column-0 line and no `sorry`. The sketches drop "not yet stated".
  - Six controls behave as expected.
  - The circuit files are pure insertions of exactly the eight SY-3 readers. Each is a formula docstring with an
    `rfl`/`Iff.rfl` proof, no attribute, and sits directly after its `def`. Removing them restores the base.
  - On the landing head against the tip, only the six regions and LE-title's title line differ.
- **LE-doc (`e9b03c43`):**
  - It touches 64 helper files. After stripping comments and doc comments, the code is identical in all 64.
  - The widest line has 100 characters; the largest helper has 649 lines. `Yao.lean` is untouched.
  - The job's one assumption holds: `#check @…FakeSimulator.Data.make` gives exactly the argument order of the new
    docstring: `E₁ E₂ E₁_poly E₂_poly bound inputs inA inB outLen gen gen_poly circuit output shape input_range output_lt
    fanin seed key nonce₀ nonce₁ permutation`.
- **Build** (`dl-oleans-2`, one Lean process, `scripts/lean_check_tree.sh` only):
  - Incremental from the tree's snapshot base `eff2dcd0`, by import-closure keys (`stateplan.py`). That covers 718 modules,
    the whole downstream of `eff2dcd0..e9b03c43`, including the 145 downstream of sc-yao itself, root `TCSlib`,
    `audits/pass-shelat/Checks` and `audits/garg-ch1-3/Checks`. The other 638 modules of the 1356-module order are reused
    from the snapshot with equal keys.
  - Result: 718/718 rc 0; 0 `error:` and 0 `error(`; no log contains "error". It took 6181 s; the peak RSS was 4.32 GB.
  - The whole-order state check gives 1356/1356 OK.
  - NthRootLemmas came from the Mathlib overlay, as for derand.
  - sc-yao's modules (`Yao.lean`, `YaoReal`, the hub and helpers, `Uniform`, `DAGCircuit`, root and both `Checks`) give no
    `sorry` and one linter warning (`BobIO:211`, unnecessary `simpa`).
- **Axioms** (probe `AxiomsLand`, `import …YaoReal`; trace `#admitted`):
  - `yaoHybrid_polyTime`, `yaoHybrid_simulators`, `yaoHybrid_hbcSecure` and `yaoSeed_good_whp` use only the standard three.
    Their closures (9168, 20202, 20475 and 17757 constants) contain no direct `sorryAx` user.
  - `yaoProtocol_hbcSecure` keeps `sorryAx` only through `HybridProtocol.hbcSecure_compose` (sc-compose #324, not merged).
    `otProtocol_*` (#318) are standard.
  - The 1492 stored constants of the 71 owners are all standard. They add no user `@[simp]`; the only new simp-tagged
    constants are the auto-generated `FakeSimulator.Data.mk.sizeOf_spec`/`injEq`.
  - The SY-4 hosts, the LE-reuse lemmas and the SY-3 readers are standard; the readers use no axioms at all.
- **Rule 10** (own seals; collector `CollectLand`; archived Gate 06/10 harness; whole-file seals over the full TCSlib import
  closure; `-DmaxErrors=0`; both error forms):
  - **Variants:** strict and coe. The coe variant treats `FinDist.instCoeFunForallReal` as notation; it is the only
    projection-coercion instance in the environment (collector `COEINST`). The coe variant is canonical.
  - **Frozen files**, all four variants:
    - `Yao.lean`: A 0/0. B 24/24 in 9 declarations, against 15 in 8 at the tip (the sc-garble review's tip seal). The 9 new
      errors are `yaoHybrid_polyTime` 2 and `yaoHybrid_simulators` 7. I read every error in the raw logs: all are
      `PolyExpr.eval` index or type conversions, or cascades from them (`yao-B-attribution.txt`). This matches the worker's
      attribution.
    - `Uniform.lean`: 4 in every variant, in `length_encode_le_of_isFaninTwo` and `IsPUniform.isPolySize`. The tip's
      `Uniform.lean`, sealed with the same 135 requests, gives the same 4 in the same 2 declarations, so they are
      inherited. The 7 new readers pass.
    - `DAGCircuit.lean`: 0 requests (no TCSlib definition in its closure), 0 errors.
  - **Helpers:** coe-A on all 68 helpers (68/68 pass). The other three variants on five helpers (`CoinSeedRelabel` after
    LE-reuse, `Lengths` with its `nestedSpecial` match reduction, `Decryption`, `SliceReduction`, `GarbledRun`): 15/15
    pass. Every helper seal gives 0 errors, with install and EOF records present. The worker's own 272 helper seals had
    0 errors (recount in Phase 1).
  - **Paired controls** (`mkctl_sy.py`). Rows: `PolyExpr.eval`, `DAGCircuit.IsFaninTwo`, the four SY-3 encodings,
    `spEncStr`, `Good`, the `FinDist` coercion, and the helper definitions `ChunkScanner.scan`, `RunWithHost.acc`,
    `CoinRelabel.keyRelabel` and `SelectedRows.offset`. Each negative is the `rfl`/`Iff.rfl` unfolding; each positive is
    the published reader.
    - coe: 30 probes, ALL_OK; 83 sealed negatives each fail exactly once, and 15 unsealed probes pass.
    - strict: 34 probes; 100/100 sealed negatives fail exactly once, and 17/17 unsealed probes pass. The only other
      failures are `ctlCoeReader` in the 17 sealed probes: the harness effect also seen in sc-ot F-09 and sc-garble.
  - **Explicit-unfold scan** (Phase 1): 0 foreign definitions.
- **Admissions:**
  - Source level: 32 at the base → 30 at the worker's final; 23 at the tip → 21 at the landing head. `Yao.lean` has none.
  - Build: 0 `sorry` in every sc-yao module. `ComposeSecurity` keeps its 3 (#324).
- **Lint** (line sets, landing head against the tip):
  - Cryptography goes from 92/101 to 92/102. The only new line is the `Yao.lean` size WARN (1179 lines, SY-2).
  - Complexity stays at 25/390. `Uniform.lean`'s check-8 WARN loses `encodeList`.
  - There is no new FAIL.
- **Restore:** `dl-oleans-2` is back to snapshot `457ba704…` (`snapshot-post` is byte-equal to `snapshot-pre`; restoreplan: extra 0, changed 0, missing 0; 37
  restored, 524 rebuilt byte-identical, 157 new oleans and the Mathlib overlay deleted).
- Phase 1 also covered layout, docstrings, duplication, the delivered seal recount, the delivered axiom trace and the host
  log; those checks are unchanged from the interim review.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| SY-F01 | minor | Four helper imports outside the issued order: `ZeroKnowledge/ThreeColoring/Machines`, `PrivateKey/FromPRF/ReductionMachine`, `PrivateKey/FromPRF/HybridLemmas` and `Asymptotic/BlockEncryptor`. Seyoon approved each in the worker's session, but the approval is recorded only in the delivery (`evidence/scope-request/`). `HybridLemmas` was a brief defect: its lemma was listed as an interface, but the module was missing from the order. | **Pending:** Seyoon to confirm, as for SG-F01, S-01 and F-02. |
| SY-F02 | minor, undisclosed | `StatisticalSwitch.statClose_of_eq_off` (and `distAdv_le_of_eq_off`) is a corollary of the public `statClose_of_uprob_ne` (`Candidates/DDH.lean:145`) with `StatClose.mono` and `uprob_mono`. It was re-derived through `MultiMsg.abs_uexp_sub_le_uprob`, and the nearest relative was not disclosed. Re-pointing would pull `Candidates/DDH` into the closure. | **Ruling needed.** Recommended: ledger, then promote `statClose_of_uprob_ne` to `Asymptotic/Sampling` and re-point both. |
| SY-F03 | minor, undisclosed | `Lengths.encodeMsgs_eq_encWords` (by induction) restates the public `ColMachines.encodeMsgs_eq_flatMap` (`ThreeColoring/Machines.lean:912`; copy in `SimulatorNumeric.lean:503`) with `BinArith.encWords_def`. This is the DL-49 class. `Lengths` does not import `ThreeColoring/Machines`. | **Ruling needed.** Recommended: ledger (extend DL-49). |
| SY-F04 | minor | Formula docstrings: in the delivery, 239 public theorems, 56 defs, 7 abbrevs and the structure had none. | **Fixed** by LE-doc `e9b03c43` (separate job, verified docstring-only). |
| SY-F05 | info, disclosed | SY-5 copies after #323. `CoinSeedRelabel.assignmentFold_lt_four` and `assignmentFold_injective` are exactly the conjuncts of `GarblingProbability.assignmentFold_small`. The other disclosed relatives are not copies. `OTAnswerWords.length_answersB`/`answersA_nil` against sc-compose `HybridProtocol.length_answersA/B` wait for #324. | **Fixed** by LE-reuse `81d526d8`: proof only, no import change, standard axioms. Ledger row for the `OTAnswerWords` pair until #324 lands. |
| SY-F06 | info | Undisclosed near-relatives that are not restatements. `ChunkScanner.scan` generalizes `Complexity.transduce` (`ClassNP/Transducer.lean`). `RunWithHost.acc` equals `StateLoop.MajLoop.acc`, the loop-predicate idiom. `SliceReduction.distAdv_fibers_le` is close to `OT.statClose_prod_of_forall`. `distAdv_chain_le` is a two-line corollary of `abs_sub_le_sum_hybrids`. | Ledger note. |
| SY-F07 | info | Yao seal B has 24 errors against 15 at the tip; the 9 new ones are `PolyExpr.eval` conversions or cascades, verified by my own seals. `Uniform.lean`'s 4 inherited canonical-A failures can now read `isFaninTwo_iff`. | None (as SG-F07). `Uniform` goes to the cleanup. |
| SY-F08 | info | 14 inline `List.getD_eq_getElem`/`List.getElem_ofFn` rewrites in 10 helpers, which the brief allowed. There is no new DL-47 lemma. | The DL-47 cleanup may re-point them. |
| SY-F09 | info | Six proofs of 40 lines or more have no step comments, among them the 128-line `yaoHybrid_polyTime` body. There is also one unnecessary-`simpa` linter warning (`BobIO:211`). | Cleanup. |
| SY-F10 | info | SY-4 host and promotion requests: H-SY-decoder and H-SY-eval, with draft registry rows in REPORT. | Maintainer decision at the gate. |
| SY-F11 | info | `S_A` and `S_B` are uniform, though the frozen statement does not expose it. | Note for DW-1; nothing demanded. |
| SY-F12 | info | The size exception: `Yao.lean` has 1179 lines, within the SY-2 waiver of 1,200. | Record the size exception. |

## Landing edits
- **Rebase resolutions:**
  - (i) The identical `isFaninTwo_iff` hunk was absorbed, and `DAGCircuit.lean` equals the tip.
  - (ii) The bullets: kept sc-garble's `yaoSeed_good_whp` bullet and the worker's two bullets.
- **LE-bullet `13690d2e`:** "(proved modulo sc-garble)" → "(proved)".
- **LE-reuse `81d526d8`:** SY-F05.
- **LE-title `bd7832d7`:** drops "(statement phase)". It is optional.
- **LE-doc `e9b03c43`:** SY-F04.
- **(iii) #332:** no clash.
- Every landing edit is an SSH-signed commit with the Co-Authored-By and Claude-Session trailers.

**Not yet clear to merge — SY-F01 needs Seyoon's confirmation and SY-F02/SY-F03 need his rulings (ledger recommended); then the PR and gate**
