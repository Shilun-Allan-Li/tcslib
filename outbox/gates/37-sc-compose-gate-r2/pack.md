# Gate 37 · The semi-honest composition theorem (`sc-compose`, [Gol04, §7.3.1, Theorem 7.3.3])

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews).

- **PR:** draft [PR #324](https://github.com/Shilun-Allan-Li/tcslib/pull/324) at
  `a6eaebd78c48e7fdfd06263edb84b70bc00ec593` (branch `land/pass-shelat-sc-compose`, tree
  `0758162eb040b2de2513719910edaa4ab37e7b73`).
- **Target and base:** the PR targets `cryptography/pass-shelat-ch2-4` on base
  `6ce4658db08a1dc2a03a149987197660db078011` (the merge base; the records tip after #311, #312 and #314–#317).
  - The fill was issued on `107f1e8c218733eac12d6b9bee6fece441271317`. The 16 PR paths are byte-identical at the issue
    base and at `6ce4658d` (`pack-checks/rebase.txt`); in particular the owned file's blob is `3041d93f` at `eff2dcd0`,
    `107f1e8c` and the base. The Lean delta between them is #307, #311, #312 and #314–#317 (29 files; the only
    `SecureComputation` file is `SpecialEncryptionMulti`), and the review's build covers it.
  - The records tip is now `540bac18ce13cb8ef37b7dc41d97de5d2deaf661`; it is records only since `6ce4658d`.
  - `pr.diff.txt` is `git diff origin/cryptography/pass-shelat-ch2-4...a6eaebd7`, which equals `6ce4658d..a6eaebd7`
    byte for byte (16 paths, 4580 insertions, 60 deletions).
  - **Open PRs and the tip.** `git merge-tree --write-tree` of the head with the tip, #313, #318, #319 and #323 is
    clean in each case, and no path is shared (`pack-checks/mergetrees.txt`). **Pending merge condition** (not an audit
    item): #324's own integration rebuild at the head (below, *The build and LE-prose*), and, for whichever of #324 and
    each open PR with a shared downstream merges second, an integration rebuild on the merged tip; the maintainer runs
    these builds (question 7).
- **Commits:** 14, all authored and committed by Claude and SSH-signed (`pack-checks/rebase.txt`).
  - The Claude worker's 12 commits (job `sc-compose`), applied with `git am` with the delivered committer data. The 12
    worker hashes (`a3cb219d` … `d3f405d4`) reproduce only with the environment's signing on (SC-F05; `COMMITS.tsv` has
    no signing column, which this brief did not ask for). They were rebased onto `6ce4658d` without conflict, author
    kept: `git range-diff 107f1e8c..d3f405d4 6ce4658d..f3036c69` is 12/12 `=`. At `f3036c69` the 16 files are
    byte-identical to the worker's `src/` (exchange `bdfdcb76`).
  - Landing edit **LE-doc** `f61ce08fa74401660345f1f50c36dffb37588391`: formulas for 70 new public declarations,
    docstrings only.
  - Landing edit **LE-prose** `a6eaebd78c48e7fdfd06263edb84b70bc00ec593` (the head; SC-F03): one sentence of the frozen
    prose of `polyTime_compose`, under Seyoon's prose-only exception.
- **Scope:** a **proof audit**. The job proves the admitted `HybridProtocol.composeP_efficient`,
  `HybridProtocol.composeV_efficient` and `HybridProtocol.hbcSecure_compose` [Gol04, §7.3.1, Theorem 7.3.3] (used
  unstated by [PS10, Theorem 163.7]). The statements passed the prong B statement phase and Gate 06B and are frozen.
  Their consumer `polyTime_compose` (unchanged, proved at the base from the three) now uses only the standard axioms.
- **Brief:** `fills/sc-compose/issued-r1/brief.md` on the records branch. Three checkpoints (the efficiency pair;
  `hbcSecure_compose` steps 1–2; steps 3–5). The owned file plus `SecureComputation/ComposeSecurity/` only, with two
  named extra imports for helpers; every other file frozen. The binding duplication rule with an `## Overlap and
  reuse` section; Rule 10 with the projection-coercion ruling and seals with `PolyExpr.eval` both excluded and sealed;
  the docstring and sketch rules; the G26-N1 error count; the evidence-completeness rule.

## What changed

Paths are under `TCSlib/Cryptography/SecureComputation/`; `CS/` is `ComposeSecurity/`. The PR touches 16 Lean files:
the owned file (382 → 449 lines) and 15 new helpers (`source-head.json`; every line at most 100 characters, every
file at most 632 lines):

| Helpers (lines) | Role |
|---|---|
| `CS/Machines` (260), `CS/Efficiency` (596) | checkpoint 1: polynomial-time machines on encoded histories; the composed parties as functions of the layout |
| `CS/Probability` (126), `CS/Reductions` (106), `CS/Accept` (198) | the statistical switch, fixing coordinates, negligible × polynomial; advice-dependent pre/post-processing; coin splittings and acceptance |
| `CS/Assembly` (292), `CS/Runs` (632), `CS/Bounds` (96), `CS/Sim` (257), `CS/Correct` (208) | the assembled view; the coins run by run and `GoodRuns`; lengths; `Φ` and the simulator; correctness and the union bound |
| `CS/Chain` (263), `CS/Template` (191), `CS/Lengths` (303), `CS/SideA` (470), `CS/SideB` (455) | the hybrid argument over the runs; the worst-case template as advice; polynomial bounds on the template words; the two sides |

The owned file imports the 15 helpers and gets a `## Contents` list; after #305 no facade edit is needed, and none was
made.

**The proof** (REPORT § *The proof of `hbcSecure_compose`*; review § *Content*; the targets' sketches were rewritten
to describe the delivered proof, the statement prose is unchanged apart from LE-prose):
- **`composeP_efficient`, `composeV_efficient`** (checkpoint 1): `composePW`/`composeVW` on the raw layout are
  polynomial-time (`polyTimeComputable_composePW/VW` from `runW`, `ansW`, `mainW` and
  `polyTimeComputable_flatMap_range`: the indices from `|hist|`, the call inputs from `H.PolyTime`, the run tapes cut
  from `r`, one `ρ` activation or `L(n)` of them for the answers, one `main` activation); the strategy equals it
  (`composeP_next_eq_composePW`); `GI.efficient_of_polyTime`.
- **`hbcSecure_compose`**: `hbcSecure_iff` with `polyTime_compose`; simulators `exists_simA`/`exists_simB`; and **for
  each `D`, `ε = ε_A + ε_B`**, the sum of the two sides' negligible bounds (each nonnegative, since it bounds a
  `distAdv`). Each side follows the five-step sketch:
  1. **Simulator** (`ComposeSim.exists_simulator`): `S_A^H` post-processed by `Φ = phiV`, which recomputes the call
     inputs from the simulated `main`-view, runs `S_A^ρ` on each with its answer block and a fresh coin block, and
     assembles the view (`asmView`).
  2. **Output clause and switch** (`exists_correct`, `uprob_not_goodRuns_le`, `distAdv_le_uprob_of_eq`,
     `realA_compose_sampleA`): with the worst-case inputs as advice of a test machine, each `ρ`-output is wrong with
     probability `≤ ε_c(n)`; off `¬GoodRuns` (probability `≤ L(n) ε_c(n)`) the real sample is
     `sampleA m (real run views)`.
  3. **Hybrids over the runs** (`ComposeProb.abs_chain_le`, `exists_hyb_step`, `exists_gapA`, `exists_gap_le`): hybrid
     `i` has the runs `< i` simulated; one step reduces to one `ρ`-sample by `D ∘ hybW` with the worst instance's
     template as advice (polynomial by `exists_tmplA_bound`); each step `≤ ε₂(n)`, the chain `≤ L(n) ε₂(n)`.
  4. **The hybrid model** (`acceptProb_realA_dPhi`, `ComposeProb.acceptProb_post_pre`, `exists_dPhi`): with all runs
     simulated the sample is `D ∘ Φ` on `H.realA F n x y`, and `D` on `S_A` is `D ∘ Φ` on `F.idealA S_A^H`;
     `H.HBCSecure F` gives `ε₃(n)`.
  5. **Total** `L(n)(ε_c(n) + ε₂(n)) + ε₃(n)` (the brief's `L(n)(2ε₁(n) + ε₂(n)) + ε₃(n)`, with `ε_c` the correctness
     bound), negligible by `negligible_polyExpr_mul` and `Negligible.add`.
- `hM` is used in `realA_compose_eq`/`realB_compose_eq`. Bob's side (`CS/SideB`) is symmetric, with `ρ.V`'s coins and
  the leading fillers.

The brief's edge cases: `L(n) = 0` (no hybrid step; the instance type of `exists_gap_le` is empty there, the advice
`[]`, the union bound `0`); `ρ.rounds(n) = 0` (empty run chunks); `hM`; the fillers and leading fillers (`segW`,
`asmView`); the tape cut lengths (exact on real views: `padTo_of_length`); `padFin` readback
(`answersRealA_eq_answersA`); Bob's side.

**Statements.** decls2 from the issue base (and from `6ce4658d`) to the head gives **185 ADDED, 0 CHANGED, 0 REMOVED**
(review `statements/head-le/decls2-vs-base.tsv`; re-checked, `pack-checks/decls2-*.tsv`; 0 rows for LE-doc
`f3036c69..f61ce08f` and for LE-prose `f61ce08f..a6eaebd7`).
- The frozen check (`frozencheck.py`, at LE-doc) compares the owned file's **11** base declarations: kind, name,
  order, header bytes and statement prose. It finds **0 differences** (`landing/frozen-check.txt`). Its controls (the
  headers of `hbcSecure_compose` and `composeP_efficient`, the prose of `composeV_efficient`, the removal of the private
  `exists_ofFn_eq`) each report exactly one difference; the `polyTime_compose` prose control is a harness artifact (its
  docstring has no sketch, so the changed character was the closing `-/`; noted in `statements/frozen/controls-summary.txt`).
- `touched`: 3 CHANGED (the targets: proofs and sketches only), 8 UNCHANGED, 186 in new files.
- Re-checked for this pack from git objects (`pack-checks/headers.txt`): the 11 base headers byte-identical at the
  head, in order; docstrings changed only for the three targets (their sketches) and `polyTime_compose` (LE-prose).

## Rulings and records in force

1. **DL-49 (Seyoon, 2026-11-15): "ledger" — SC-F01.** Helpers under `CS/` restate public lemmas because the worker read
   the brief's two extra imports as exhaustive (disclosed in the checkpoint REPORTs): a third `negligible_polyExpr_mul`
   (`EnsemblesLemmas.lean:377`); `appendCoins` (= `coinsEquiv`); `ofFn_blocks_symm` (= `FunFamily.ofFn_blocks_symm`);
   and `polyTimeComputable_flatMap_range`, `flatMap_range_ite`, `iterSnd_poly`, `encodeMsgs_eq_flatMap`,
   `msgAt_encodeMsgs` and the `padTo` family (from `ZeroKnowledge/ThreeColoring/Machines.lean`). Re-pointed in the
   cleanup. **Not a finding:** any item DL-49 lists.
2. **SC-F03 (Seyoon, 2026-11-15): a prose-only exception.** The frozen prose of `polyTime_compose` still called the
   efficiency theorems `sorry`s. LE-prose changes exactly that sentence:

   ```text
   - The two strategies are PPT (`composeP_efficient`, `composeV_efficient`; `sorry`s under their
   - sketches), and the messages are bounded by `B_main + B_ρ` (`compose_msg_bound`, proved). The
   + The two strategies are PPT (`composeP_efficient`, `composeV_efficient`, proved), and the
   + messages are bounded by `B_main + B_ρ` (`compose_msg_bound`, proved). The
   ```

   Re-checked (`pack-checks/leprose.txt`): one file, +2/−2; identical with doc comments deleted; one docstring
   (`polyTime_compose`) changed and no header; the prose at LE-doc equals the issue base's.
3. **Rule 10: a `CoeFun`/`Coe` instance whose body is a structure projection is notation (Seyoon, 2026-11-14).** This is
   `FinDist`'s `⟨FinDist.prob⟩`. The coe-variant seals are canonical; the strict variant is run and its differences
   attributed.
4. **`PolyExpr.eval` is notation (Q1, the user, 2026-11-07).** Seal **A** is canonical; seal B is run and reported.
   So **coe-A is the canonical variant**.
5. **The facade-completeness lint fix, #305.** The baseline is **92 FAIL / 101 WARN** (Cryptography).
6. **LE-doc (the maintainer's landing edit): docstrings only** (SC-F04). For the 70 new public declarations the
   review's docaudit flagged NO-FORMULA, the declaration's own Lean conclusion (for a `def` whose type is no relation,
   its `_eq`/`_iff` reader's) is added as a backticked formula at the end of the statement prose; 15 long conclusions
   are cut at 240 characters with " …" (`landing/le-doc-plan.tsv` in the review ZIP). Re-checked (`pack-checks/lecheck.txt`):
   `f3036c69..f61ce08f` touches 13 files, each identical with doc comments deleted, 70 docstrings changed, every line
   within 100 characters.
7. **The landing edits are the maintainer's** (the ext-nosrc … sc-ot, sc-garble precedents).

## What is frozen

- **The three targets' statements** (quoted in the brief), the 8 other pre-existing declarations of
  `ComposeSecurity.lean` and their statement prose (`polyTime_compose`'s apart from the SC-F03 sentence), in particular
  `exists_runExec_eq_transcript`, `exists_mainExec_eq_transcript`, `compose_msg_bound` and `polyTime_compose`.
- **Every file outside** `ComposeSecurity.lean` and `ComposeSecurity/`, in particular `SecureComputation/Defs.lean`,
  `Hybrid.lean`, `Compose.lean`, `ComposePhases.lean`, `YaoReal.lean`, `Yao.lean`, `Garbling*.lean`, the `FromPRF*`
  files, `Pseudorandom/*` and `Games/*`.
- **The landing edits:** LE-doc 70 docstrings; LE-prose one sentence.

## Questions for the audit

**1. Correctness against [Gol04, §7.3.1, Theorem 7.3.3]**
- **The efficiency pair:** do `composePW`/`composeVW` compute the composed parties' next-message functions on every
  history (the indices from `|hist|`, the call inputs, the run tapes cut from `r`, the answer activations, the `main`
  activation; `composeP_next_eq_composePW`)? Are they polynomial-time from `H.PolyTime F` and `G.PolyTime ρ`, with
  `GI.efficient_of_polyTime` the right extraction?
- **`hbcSecure_compose`:** does the proof follow the **five-step sketch** above, with `ε = ε_A + ε_B` for every `D`?
  - Is `Φ` right (call inputs recomputed from the simulated `main`-view, `S_A^ρ` per call on its answer block and a
    fresh coin block, `asmView`)?
  - Is the switch "agree off `¬GoodRuns`" sound, with `Pr[¬GoodRuns] ≤ L(n) ε_c(n)` from the worst-case-input test
    machine?
  - Is the hybrid chain over the runs right (`abs_chain_le`, `exists_hyb_step`; the coordinate fixing
    `exists_abs_sub_le_sections`; the worst instance's template as advice, polynomially long by `exists_tmplA_bound`),
    each step at most `ε₂(n)`?
  - Is the step to the hybrid model right (`acceptProb_realA_dPhi`, `exists_dPhi`, `H.HBCSecure F` giving `ε₃`)?
  - Is the total `L(n)(ε_c + ε₂) + ε₃` negligible, and is Bob's side really symmetric (`ρ.V`'s coins, the leading
    fillers)?
- Are the brief's edge cases covered (`L(n) = 0`, `ρ.rounds(n) = 0`, `hM` and its counterexample, the fillers, the cut
  lengths, `padFin` readback, Bob's side)? Do the rewritten sketches describe the delivered proof?

**2. Frozen-statement integrity**
- Are the three targets' headers and the other 8 pre-existing declarations byte-identical (`landing/frozen-check.txt`,
  `statements/frozen/`, `pack-checks/headers.txt`)? Is decls2 **185 ADDED / 0 CHANGED / 0 REMOVED**?
- In the owned file, did only the imports, the title, `## Contents`, `## Main results`, the three proofs and their
  sketches change, plus the LE-prose sentence (`statements/frozen/owned.diff`)?

**3. Duplication (recent gates graded undisclosed re-proofs of public lemmas as majors)**
- Does any new declaration, or any part of a proof, duplicate a public TCSlib or Mathlib lemma, or copy a private one,
  beyond the worker's tables (the final REPORT's `## Overlap and reuse` and the two checkpoint REPORTs it says stand,
  `worker/cp1/REPORT.md` and `worker/cp2/REPORT.md`) and **DL-49**? SC-F01 is ruled ledger debt (DL-49). **Anything
  further is a major.** The recent majors of this class are G23-01, G24-01, prf-mac F-01, learning (`uprob_eq_point`),
  G29-01, G29-02, sc-ot F-01 and G34-01.
- Search in particular:
  - the hybrid argument (`multicopyHybrid`, `multicopyRed`, `exists_multicopyRed_ge`, `abs_sub_le_sum_hybrids`,
    `exists_hybrid_gap`) against `hybV`, `plugV`, `exists_hyb_step`, `abs_chain_le`;
  - argmax advice (`Finset.exists_max_image` patterns in `PublicKey/Hybrid.lean:295`, `NextBit.lean:411`,
    `Commitment.lean:317`) against `tmplW`, `hybW`, `exists_gap_le`;
  - probability and acceptance (`uprob_*`, `uexp_*`, `acceptProb_*`, `distAdv_*`, `StatClose`,
    `distAdv_le_of_statClose`, `pushesUniform_*`);
  - coin splittings and blocks (`coinsEquiv`, `splitCoins`, `blocks`, `coinBlock_flatten`, `FunFamily.ofFn_blocks_symm`);
  - history machinery (`Strategy.encodeMsgs`, `pairFstD`/`pairSndD`, `GI.iterate_pairSndD_encodeMsgs`, the
    `ThreeColoring/Machines` and `GI` layout helpers, `padFin`, `padTo`);
  - list readings (`getD`, `getElem?_ofFn`, `headD_drop_ofFn`; `pack-checks/dupscan.txt` lists the 9 added lines that
    use a getD/`getElem_ofFn` reading lemma: `msgAt_encodeMsgs` and the `padTo` family are DL-49 items; the others,
    `coinBlock_blocksCoins`, `runTape_ofFn_splitCoins`, `getD_filter_map_mover`, `getD_plug` and the two side lemmas,
    read coin blocks and word lists, not `(List.ofFn f).getD i d = f i`. Is that reading right?);
  - lengths (`length_answersA/B` against the owned file's `length_answersRealA/B`; the private `exists_ofFn_eq` of
    `CS/Lengths`, restated from the owned file's private one and disclosed).
- Are the disclosed relations accurate and their "why not reused" reasons valid (in particular "not importable" for
  `getD_plug` and the hybrid-chain lemmas)?

**4. Rule 10**
- Do the seals cover every touched declaration of the 16 files over the full closure, at the base and the head, in all
  four variants, run with `-DmaxErrors=0` (`tools/runner_full.py`) and install/EOF records? Requests 561–1192 per file
  (`logs/mkseals-*.log`); the base phase rebuilt the base owned file in its own closure.
- With **coe-A canonical**, does every file pass? The review has **64/64 head probes rc 0** (A and B, strict and coe, all
  16 files) and **4/4 at the base** (670/671/669/670 requests = the worker's); 0 new failing declarations; strict =
  coe (`logs/seal-table-seals{,-coe}.txt`).
- Do the paired controls bite? Rows: `PolyExpr.eval` (B), the `FinDist` CoeFun instance, `HybridProtocol.answersA`
  (frozen `Hybrid.lean`), `ComposeMachines.padTo`, `ComposeSim.tmplW`. Coe (canonical): 14 probes, 16 sealed
  negatives, `logs/ctlcheck.log` ALL_OK. Strict: 16 probes, 24 sealed negatives; every sealed negative fails exactly
  once, and only `ctlCoeReader` fails in the 8 strict sealed probes (the harness effect of sc-ot F-09;
  `logs/controls-strict-attribution.txt`).
- Explicit-unfold scan at the head (LE-doc): 1189 items, 1036 theorems, 2 owned definitions, 151 local or unresolved,
  **0 foreign** (`logs/scan2-head.log`). Does any proof read a foreign definition other than through a published
  reader (`Compose`, `ComposePhases`, `Hybrid`, `Defs`: `composeP`/`composeV`, `slotMsgs`, `runTape`, `answersA/B`,
  `realA/B`, `idealA/B`, `Protocol.transcript`, `acceptProb`, `distAdv`; the `NUPPT` layer; one helper's definitions
  read from another)?

**5. The landing edits, and the build**
- **LE-doc (ruling 6):** does each of the 70 new formulas state what its declaration says, in Lean argument order
  (`landing/le-doc.diff`, `landing/le-doc-doconly.txt`)? Are the 15 cut conclusions acceptable? Is it docstrings only?
- **LE-prose (ruling 2):** is it exactly the SC-F03 sentence, docstring only, with the header and code identical?
- **The build ran at LE-doc `f61ce08f`, not at the head.** The review built 279/279 modules and then the 18 modules
  LE-doc touches and their dependants, all at `f61ce08f`; its seals, controls, scan and census ran at `f61ce08f` too.
  **LE-prose `a6eaebd7` was checked doc-only, by stripping doc comments; it was not rebuilt.** Of the 279 built
  sources, 278 equal their blobs at the head; the one that differs is `ComposeSecurity.lean`, by the LE-prose docstring
  (`pack-checks/srcequality.txt`). The rebuild at the head is part of #324's integration build, which the maintainer
  runs before #324 merges (question 7). Is the doc-only check sufficient for this audit?

**6. The docstring and sketch rules**
- Does every new public declaration's docstring state its formula, with arguments in the Lean order and a source tag
  where it comes from the source? The review's docaudit after LE-doc (`statements/head-le/docaudit.tsv`) has 145 OK,
  29 LABEL (all state their equation) and 14 NO-FORMULA: the frozen prose of `composeP_efficient` and
  `composeV_efficient`, and 12 `PolyTimeComputable …` Prop formulas without a relation symbol, which the tool does not
  accept. Are those 12 acceptable?
- Does every proof of 15 lines or more carry a `**Proof sketch.**`? `statements/head-le/sketchaudit.txt` has 37
  theorems and 3 flagged: `runW_eq`, `composePW_eq`, `composeVW_eq`, `:= rfl` readers under long statements (a tool
  artifact). Do the long proofs (`exists_gapA`/`B`, `exists_simA`/`B`, `abs_chain_le`, the efficiency proofs) have
  step comments? A misstated formula or sketch is a minor.
- Does every new public `def` land with its `_eq` reader (lint check 8)? Is nothing new `@[simp]`, an instance or an
  abbreviation? The census has none; its 3 "abbrev" rows are compiler match auxiliaries (`…match_1_1`).

**7. The merge interaction**
- `git merge-tree --write-tree a6eaebd7 <x>` is clean, and no path is shared (`pack-checks/mergetrees.txt`):

  | `<x>` | head | merged tree | downstream of both (`pack-checks/downstream.txt`) |
  |---|---|---|---|
  | the tip | `540bac18` | `a5944f88` | none (records only since the base) |
  | #313 (learning) | `2b6c2981` | `828d6685` | root `TCSlib` |
  | #318 (sc-ot) | `f62a25b3` | `8da059d7` | `YaoReal`, `SecureComputation`, root `TCSlib` |
  | #319 (canonizer) | `6421ac16` | `6ceb6246` | root `TCSlib` |
  | #323 (sc-garble) | `cd9a4843` | `e6911ef7` | `YaoReal`, `SecureComputation`, root `TCSlib` |

- No open PR changes a module of the unit's closure (98 modules). None of the 185 new short names is declared in a file
  another PR changes (`pack-checks/namecheck.txt`); the review's name-clash scan has 0 exact clashes (the private
  `exists_ofFn_eq` of `CS/Lengths` shares its short name with the owned file's private one, disclosed).
- **Pending merge conditions (not audit items).** The combined trees are **not** built.
  - **#324's integration rebuild at the head:** the review build is at LE-doc `f61ce08f`; the maintainer rebuilds
    `ComposeSecurity` and its downstream (`YaoReal`, `SecureComputation`, root `TCSlib`) at `a6eaebd7`, on the merged
    tip, before #324 merges.
  - Whichever of #324 and #313, #318, #319 or #323 merges second needs an integration rebuild of the shared downstream
    on the merged tip before it merges; the maintainer runs that build.
  - Treat these as conditions on the merge, not as something for this audit to establish. What you can raise: a
    concrete reason a merged tree cannot build, or a name or instance interaction.

## Known dispositions (not findings)

- **SC-F02** (info): the final REPORT's overlap section relies on the checkpoint tables; copies are in the evidence
  (`worker/cp1/`, `worker/cp2/`). **SC-F04** (info): the 70 missing formulas, fixed by LE-doc. **SC-F05** (info):
  `COMMITS.tsv` has no signing column; the hashes reproduce only with the environment's deterministic SSH signing
  (`logs/git-am-integrity*.log`), as sc-ot F-05.
- **The PR description** reports the build (279/279) without saying that it ran at LE-doc; this pack states it.
- **`yaoProtocol_hbcSecure` keeps `sorryAx`**, now only through `otProtocol_*` (#318) and `yaoHybrid_*` (sc-yao);
  `hbcSecure_compose` is no longer among its admissions (review DepTrace).
- **Admissions:** 31 in 14 modules → 28 in 13; only `ComposeSecurity` changes (3 → 0). Outside the issued order only
  `SeedMajority` (#312) and `SpecialEncryptionMulti` (#311) differ, both base delta (`logs/sorry-census.txt`).
- **The worker's promotion requests** (the FP/history toolkit of `CS/Machines`, `Efficient.exists_polyTime`,
  `polyTimeComputable_slots`, `negligible_polyExpr_mul`, the coin splittings, the acceptance lemmas, `abs_chain_le`/
  `exists_hyb_step` beside the multicopy lemma, the argmax-advice pattern) are for the deferred cleanup.

## Also check

**Axioms**
- At LE-doc, `composeP_efficient`, `composeV_efficient`, `hbcSecure_compose`, `polyTime_compose`, `exists_simA/B` and
  the helper endpoints each print `[propext, Classical.choice, Quot.sound]` (`landing/census-head.log`). At the base
  the three targets and `polyTime_compose` had `sorryAx`.
- The census has **258** stored constants (= the worker's); the axiom union is the standard three, with no `sorryAx`,
  `@[simp]` or instance. Against the base: removed 0, type-changed 0, axioms-changed 4 (the targets and
  `polyTime_compose`, `sorryAx` dropped; `logs/census-base-vs-head.tsv`).

**Sizes and widths:** the owned file 449 lines, the largest helper 632 (`CS/Runs`), every line at most 100 characters
(`source-head.json`).

**Build:** at LE-doc `f61ce08f`, **279/279 modules rc 0, 0 errors in both diagnostic forms** (G26-N1; substring
"error" 0): the downstream of every module changed since `eff2dcd0` (85 = 69 base delta + 16 unit) through root
`TCSlib` and `audits/pass-shelat/Checks` (`landing/root-checks.jsonl`, at the pre-edit head `f3036c69`), then 18/18
for LE-doc (`landing/edit-build-results.jsonl`). The 16 unit modules have 0 warnings and 0 sorries. Whole-tree check
at `f61ce08f`: 1264 modules, RESULT OK (`landing/tree-check-head.txt`). Restore: `dl-oleans` back at `457ba704…`.
**Not rebuilt at the head** (question 5).

**Lint:** 92 FAIL / 101 WARN at the tip and at the landing head before LE-doc, with identical line sets; LE-doc and
LE-prose only edit docstrings.

## Evidence

- **`review.md`:** the maintainer's delivery review, verdict ACCEPT WITH LANDING EDITS (SC-F01–SC-F05).
- **`verification.zip`** (121 entries): every file the review cites and the pack uses, as byte-identical originals.
  Its `SHA256SUMS` lists every other entry, and `PROVENANCE.txt` gives each entry's source. It holds:
  - `review-evidence.zip` (`fills/sc-compose/final-r1/`, SHA-256 `c11ce8bb…`) and `review-evidence-SHA256SUMS`, its
    manifest: 917 entries, 66 directories and 851 files, exactly the 850 manifest paths plus `SHA256SUMS`
    (byte-identical to the manifest; no top folder); every hash verifies;
  - `landing/PROVENANCE.txt`: the review's PROVENANCE (= the ZIP's);
  - `records/` (12): the issue package `fills/sc-compose/issued-r1/`, the duplication ledger (DL-49), the decision log
    (the SC-F01 and SC-F03 rulings) and the secure-computation plan (§ 2.11–2.12), at records
    `540bac18ce13cb8ef37b7dc41d97de5d2deaf661`;
  - `evidence/` (70): byte copies of the ZIP entries this pack cites;
  - `worker/` (13): byte copies from exchange (`inbox/fills/sc-compose/`): at the final
    `bdfdcb76d0d78bedd61025b33cb7382b26ee7c70`, `COMMITS.tsv`, the census and sorry diffs, the lint diff, the axioms,
    `git am` check, header check and control, sketch and width checks and the control results; and the two checkpoint
    REPORTs at `419c4ceb` and `f1ba0b1a` (`worker/cp1/REPORT.md`, `worker/cp2/REPORT.md`; 10 of the 13 also
    byte-identical to the review's `logs/delivery-extracts/`);
  - `pack-checks/` (21): the re-checks for this pack, from git objects only (no Lean), with their scripts.
- **The worker's own evidence:** on the exchange at `bdfdcb76`, under `inbox/fills/sc-compose/`. Its top `SHA256SUMS`
  lists 1062 files and `evidence/SHA256SUMS` 1031, all delivered.
- **`landing/`:** byte copies of evidence-ZIP entries: `root-checks.jsonl` (= `build/results.jsonl`), `build-summary.txt`,
  `edit-build-results.jsonl`, `edit-build-summary.txt`, `census-head.log` (= `probe-runs/mods/PlProbe_H_CensusHead.log`),
  `frozen-check.txt` (= `statements/head-le/frozen-check.txt`) and `tree-check-head.txt`.
- **`worker-report.md`:** the worker's final `REPORT.md`, at exchange `bdfdcb76`.
- **`pr-description.md`:** the PR #324 description as fetched from the GitHub REST API on 2026-11-15 (`.body`, raw).
- **`pr.diff.txt`:** `git diff` from the base to the head (16 paths, 4580 insertions, 60 deletions).
- **`source-head.json`:** the head hashes, line counts and over-width counts of the 16 changed files.
- **`sources.zip`:** the source closure at the head of every changed module, 98 files.
- **The bundle** adds, as context at the head: `SecureComputation/Hybrid.lean` (`HybridProtocol`, `PolyTime`,
  `HBCSecure` and readers), `SecureComputation/Compose.lean` and `SecureComputation/ComposePhases.lean` (the composed
  protocol and its phase lemmas).

## Findings delivery

Return `gate37-sc-compose-findings.md` as a Markdown file in this chat. If you have several evidence files, return a
ZIP. The user dispatches and merges.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

**Severities**
- **blocker:** a false or unusable statement, a proof that does not establish the frozen statement, or a scope
  violation.
- **major:** a changed frozen statement, a forbidden read in a touched declaration not covered by the rulings, an
  undisclosed copied private lemma or undisclosed re-proof of a public one outside DL-49, or necessary evidence that
  cannot be verified.
- **minor:** documentation or API defects, including an inaccurate formula docstring or proof sketch.
- **note:** anything else.

Report the audited head and the counts by severity. The gate closes at zero blockers and zero majors.
