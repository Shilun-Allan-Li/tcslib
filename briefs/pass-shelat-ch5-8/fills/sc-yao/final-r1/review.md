# sc-yao · maintainer delivery review (r1)

**Status: INTERIM (Phase 1 and landing preparation complete; the Lean checks of Phase 2 are pending an olean tree).**
**Provisional verdict: ACCEPT WITH LANDING EDITS**, subject to Phase 2. Landing edits made: LE-bullet, LE-reuse, LE-title
(optional). Pending: Seyoon's confirmation of SY-F01, rulings on SY-F02 and SY-F03 (ledger recommended), and LE-doc (SY-F04).

## Delivery and landing
- **Delivery:** Codex on Seyoon's Mac, a lead and 3 sub-agents (SY-6). The final is exchange `47c38c47`; the checkpoints are
  `f0a9a616`, `816971fc`, `acc86827` and `171a341a`. All five commits touch only `inbox/fills/sc-yao/`. The issue base is
  `6ce4658d`; the worker tip is `6e7ef601` (8 unsigned commits).
- **Landing:** `land/pass-shelat-sc-yao` (local, not pushed), on the tip `f9fda8fe`.
  - **Head:** `bd7832d7fbac20b04db75bc858086b143ba4735b`, tree `327f4f64`.
  - **Commits:** the worker's 8, cherry-picked with author kept and committer Claude, SSH-signed: `b288691f`, `16ac8d64`,
    `65158baa`, `13403ddf`, `d9c2f53e`, `bb1a1bf6`, `fe88a3b0`, `e737096b`. Then LE-bullet `13690d2e`, LE-reuse `81d526d8`
    and LE-title `bd7832d7`.
  - **Range-diff:** 5/8 identical. Commit 1 lost the `isFaninTwo_iff` hunk, which the merge absorbed because it is
    byte-identical to #323's. Commits 4 and 7 differ only in the bullet resolution.
- **Files:** 70 changed against the tip, +14571/−67:
  - `Yao.lean`, 1179 lines (970 after #323; at most 1,200 under SY-2);
  - `Uniform.lean`, with the seven SY-3 encoding readers;
  - the hub `Yao/HybridProof.lean` and 67 helpers under `Yao/HybridProof/`.
  - `DAGCircuit.lean` is unchanged against the tip.
- **Evidence:** `$SP/dl-review/sc-yao-r1/` (`$SP` is this session's scratchpad). The zip and `SHA256SUMS` are written at the
  end of Phase 2.

## Checks (Phase 1)
- **Integrity:**
  - The manifests verify 7597/7597 and 7515/7515, streamed from git. The path sets are exact: nothing missing, nothing
    extra, no `./`.
  - `git am` at the base reproduces all 8 hashes, with `COMMITS.tsv` signing "none".
  - `src/` equals the 71 changed paths byte for byte: 68 added, 3 modified.
  - The issue package verifies 8/8, and its sources 184/184 at the base.
- **Scope** (own masking script `frozen_sy.py`, with controls):
  - In `Yao.lean`, everything outside the six approved regions is byte-identical to the base. The regions are the hub import
    after line 9, the bullet at 96–98, the sketches at 826–840 and 860–906, and the bodies at 843 and 918. These line numbers
    match the brief.
  - The bodies contain no column-0 line and no `sorry`. The sketches drop "not yet stated". There is one new import line.
  - Six controls: the one-character header control, the extra-frozen-line control, the second-import control and the
    frozen-prose control each give exactly 1 violation. A declaration smuggled into a body gives 1 rule break, and an edit
    inside a sketch passes.
  - `DAGCircuit.lean` and `Uniform.lean` are pure insertions of exactly the eight SY-3 readers. Each is a formula docstring
    with an `rfl`/`Iff.rfl` proof, no attribute, and sits directly after its `def`. Removing them restores the base exactly.
  - `isFaninTwo_iff` is byte-identical to the tip's (#323). Two circuit controls (an added attribute, a one-character edit to
    a `def`) fail as expected.
- **Layout:**
  - There are 68 files under the hub and 14306 lines; the largest is `RowFromCoins` with 577. The widest line is 100
    characters.
  - The hub imports exactly the 67 children and has a `## Contents` list. Nothing else sits directly under `Yao/`.
  - Helper imports outside the issued order are exactly the four approved ones (SY-F01). Every Mathlib import is in
    `roots.txt`.
  - There is no `@[simp]`, no `sorry`, no `native_decide` and no `unsafe`. The SY-4 hosts are public; only the decoder's
    internal transition tables and lemmas are private.
- **Docstrings and sketches:**
  - Of the 71 theorems with at least 15 proof lines, 67 carry `**Proof sketch.**`. The other 4 are `rfl` readers with long
    statements, which are false positives.
  - Formulas: SY-F04.
- **Duplication:**
  - The namespace-resolved name scan checks all 764 new names (private included) against the tip, which has #313, #318,
    #319, #323, #326, #332 and #333. It finds one full-name match, the absorbed `isFaninTwo_iff`. Nothing clashes with
    #332's readers.
  - A normalized-statement match against 21,045 tip theorem headers gives 0 exact matches. The loose variant's 5 hits are
    generic `PolyTimeComputable` shapes on local definitions.
  - The targeted searches covered the probability, hybrid, list, encoding and machine families, the sc-garble, sc-ot,
    prf-long and DL-46/DL-47 publications, and the SY-5 relatives now merged. Results: SY-F02, SY-F03, SY-F05, SY-F06 and
    SY-F08.
- **Rule 10, by source and delivered evidence:**
  - The delivered seal is broad: it seals every TCSlib `defnInfo` in the import closure, matchers included. It treats
    `PolyExpr.eval` as Q1 notation in A only, and projection coercions as notation in the coe variant only. It records
    `SEAL_COUNTS`.
  - I recounted both error forms in all 284 raw logs from git: no mismatch with the summaries.
    - The 272 helper logs (68 files × A/B × strict/coe) have 0 errors.
    - Frozen files: `Yao.lean` A 0/0 and B 24/24; `DAGCircuit.lean` 0; `Uniform.lean` 4 in every variant (inherited).
  - The 9 new Yao B errors are all `PolyExpr.eval` index conversions or their cascades: 2 efficiency, 7 in the simulator
    body. I read them in the raw logs (SY-F07).
  - SY-3 controls, recounted from the logs: 8 unsealed `rfl` pass, 8 sealed `rfl` fail exactly once, 8 sealed readers pass.
  - Own explicit-unfold scan: 1512 tactic references, 28 short-name candidates, all local `let`/`have` names on inspection.
    0 foreign definitions.
- **Admissions:** source-level, outside comments, over the issued order plus helpers.
  - 32 at the base → 30 at the worker's final; exactly the two targets go.
  - 23 at the tip → 21 at the landing head. `Yao.lean` has none left. The 3 in `ComposeSecurity` (#324) and 18 in the
    complexity layer remain.
- **Axioms (delivered trace):**
  - 1490 stored constants; the 1098 helper constants are standard-only.
  - `yaoHybrid_polyTime` uses only the standard three.
  - `yaoHybrid_simulators` and `yaoHybrid_hbcSecure` keep `sorryAx` only through `yaoSeed_good_whp` and
    `sliceMultiMessageSecure_of_prfOut`.
  - `yaoProtocol_hbcSecure` adds `otProtocol_*` and `hbcSecure_compose`.
- **Lint** (line sets):
  - Base → final: Cryptography 92/101 → 92/102. The only new line is the `Yao.lean` size WARN (SY-2); `Yao.lean`'s INFO size
    line goes. Circuits stay 0/79, with two check-8 WARN texts improved.
  - Tip → landing: the same, with `Yao.lean` at 1179 lines.
- **Host (`slots.log`):**
  - Over the matched intervals, never more than 3 slots are held. The tags are `sc-yao` and `-a`/`-b`/`-c`.
  - The 4 ACQUIRE lines without a RELEASE are the disclosed interrupted runs.
  - Every cache get names its modules (77, 2, 2). There is no `lake build`.

## Checks (Phase 2, pending a tree)
- Per-module native checks of every changed or new module and their downstream, through root `TCSlib` and both
  `audits/*/Checks`.
- Axioms of the four Yao theorems on the landing head, with the dependency trace. On the tip, no `sorryAx` should come from
  sc-garble.
- My own seals: strict/coe A/B, coe-A canonical, `-DmaxErrors=0`, both error forms, paired controls. They cover the frozen
  files and the helpers, including `Lengths`' `nestedSpecial` match reduction.
- Restore the tree to `457ba704…`.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| SY-F01 | minor | Four helper imports outside the issued order: `ZeroKnowledge/ThreeColoring/Machines`, `PrivateKey/FromPRF/ReductionMachine`, `PrivateKey/FromPRF/HybridLemmas` and `Asymptotic/BlockEncryptor`. Seyoon approved each in the worker's session, but the approval is recorded only in the delivery (`evidence/scope-request/`). `HybridLemmas` was a brief defect: its `MultiMsg.abs_uexp_sub_le_uprob` was listed as an interface, but the module was missing from the order. | **Pending:** Seyoon to confirm, as for SG-F01, S-01 and F-02. |
| SY-F02 | minor, undisclosed | `StatisticalSwitch.statClose_of_eq_off`, and its corollary `distAdv_le_of_eq_off`, is a corollary of the public `statClose_of_uprob_ne` (`Candidates/DDH.lean:145`) with `StatClose.mono` and `uprob_mono`. It was re-derived through `MultiMsg.abs_uexp_sub_le_uprob`, and the nearest relative was not disclosed. Re-pointing would pull `Candidates/DDH` (DiscreteLog, QuadraticResidues) into the closure. | **Ruling needed.** Recommended: ledger, then promote `statClose_of_uprob_ne` to `Asymptotic/Sampling` and re-point both. |
| SY-F03 | minor, undisclosed | `Lengths.encodeMsgs_eq_encWords` (`Strategy.encodeMsgs L = BinArith.encWords L`, by induction) restates the public `ColMachines.encodeMsgs_eq_flatMap` (`ThreeColoring/Machines.lean:912`; copy in `SimulatorNumeric.lean:503`) with `BinArith.encWords_def`. Only Yao's local `henc` was disclosed. This is the DL-49 class. `Lengths` does not import `ThreeColoring/Machines`. | **Ruling needed.** Recommended: ledger (extend DL-49). Re-pointing needs an import or a promotion. |
| SY-F04 | minor | Formula docstrings, which the brief said to "do these yourself". Of the new public declarations, 239 theorems, 56 defs, 7 abbrevs and the structure have no backticked formula; 224 more theorems give only a prose relation with backticked terms. All have docstrings: the three NO-DOC hits are attribute-placement false positives. | **LE-doc pending, before the gate** (as seq-zk S-02 and sc-ot F-03). |
| SY-F05 | info, disclosed | SY-5 copies after #323. `CoinSeedRelabel.assignmentFold_lt_four` and `assignmentFold_injective` are exactly the conjuncts of `GarblingProbability.assignmentFold_small`. The other disclosed relatives are not copies: `CoinRelabel` against the `CoinBlocks` `pushesUniform_*`; the `Lengths` bounds against `NestedBounds.length_nestedInner`; `RowFromCoins.assignmentFold_eq_two`; `TwoMoveViews` against OT `exec_five` and `realA_realCoins`. `OTAnswerWords.length_answersB`/`answersA_nil` against sc-compose `HybridProtocol.length_answersA/B` wait for #324. | **Fixed** by LE-reuse `81d526d8`: proof only, no import change. Ledger row for the `OTAnswerWords` pair until #324 lands. |
| SY-F06 | info | Undisclosed near-relatives that are not restatements. `ChunkScanner.scan` generalizes `Complexity.transduce` (`ClassNP/Transducer.lean`) to word-valued emission. `RunWithHost.acc` equals `StateLoop.MajLoop.acc`, the common one-line loop predicate. `SliceReduction.distAdv_fibers_le` is close to `OT.statClose_prod_of_forall`. `distAdv_chain_le` is a two-line corollary of `abs_sub_le_sum_hybrids`. | Ledger note. |
| SY-F07 | info | Yao seal B has 24 errors against 15 at the base. The 9 new ones are `PolyExpr.eval` conversions or cascades; canonical A passes. | None (as SG-F07). Phase 2 re-checks. |
| SY-F08 | info | 14 inline `List.getD_eq_getElem`/`List.getElem_ofFn` rewrites in 10 helpers, which the brief allowed. There is no new DL-47 lemma. | The DL-47 cleanup may re-point them. |
| SY-F09 | info | Six proofs of 40 lines or more have no step comments, among them the 128-line `yaoHybrid_polyTime` body. | Optional, with LE-doc. |
| SY-F10 | info | SY-4 host and promotion requests: H-SY-decoder (`DescriptionDecoder`) and H-SY-eval (`RunWithHost.exists_machine`), with draft registry rows in REPORT. | Maintainer decision at the gate. |
| SY-F11 | info | `S_A` and `S_B` are uniform (`AliceSimulator.simulator_uniform`, `FakeSimulatorFactory`), though the frozen statement does not expose it. | Note for DW-1; nothing demanded. |
| SY-F12 | info | The size exception: `Yao.lean` has 1179 lines on the landing head, within the SY-2 waiver of 1,200. It gives the lint's only new WARN. | Record the size exception. |

## Landing edits
- **Rebase resolutions** (inside the cherry-picked commits):
  - (i) `isFaninTwo_iff`: the identical hunk was absorbed, and `DAGCircuit.lean` equals the tip.
  - (ii) The bullets: kept sc-garble's `yaoSeed_good_whp` (proved) bullet and the worker's two bullets. The worker's
    superseded `yaoSeed_good_whp` (stated) bullet was dropped.
- **LE-bullet `13690d2e`:** "(proved modulo sc-garble)" → "(proved)".
- **LE-reuse `81d526d8`:** see SY-F05.
- **LE-title `bd7832d7`:** drops "(statement phase)", as the brief anticipated. It is optional.
- **(iii) #332:** no clash, and nothing to edit.

## Evidence (in `$SP/dl-review/sc-yao-r1/`)
`integrity/` (manifests, git am, src equality, issue package), `scope/` (files, checks, controls), `layout/`, `docs/`
(touched, doc and sketch audits), `dup/` (tip name clash, statement matches), `rule10/` (unfold scan, seal and control
recounts, axiom-trace parse), `admissions/`, `lint/`, `host/`, `landing/` (PROVENANCE, series, commits, range-diff, scope
against the tip), `tools/`.

**Not yet clear to merge — Phase 2 Lean checks pending; SY-F01 confirmation, SY-F02/SY-F03 rulings and LE-doc (SY-F04) open**
