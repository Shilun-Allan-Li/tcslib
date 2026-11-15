## ===== briefs/pass-shelat-ch5-8/gates/37-sc-compose/pack.md =====

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

## ===== briefs/pass-shelat-ch5-8/gates/37-sc-compose/review.md =====

# sc-compose · maintainer delivery review (r1)

**Verdict: ACCEPT WITH LANDING EDITS.** The landing edits are LE-doc and LE-prose. Draft [PR #324](https://github.com/Shilun-Allan-Li/tcslib/pull/324).

## Delivery and landing
- **Delivery:** a Claude worker. The final is at exchange `bdfdcb76`; the checkpoints are `419c4ceb` and `f1ba0b1a`. The issue base is `107f1e8c`.
- **Landing:** `land/pass-shelat-sc-compose`, on `6ce4658d`. The range-diff is 12/12 identical.
  - **Head:** `a6eaebd78c48e7fdfd06263edb84b70bc00ec593`.
  - **Commits:** the worker's twelve (`7c31136e` … `f3036c69`), then two landing edits:
    - LE-doc `f61ce08f`, tree `f7432799`: formulas for 70 new public declarations.
    - LE-prose `a6eaebd7` (SC-F03).
- **Files:** 16 files, +4580/−60: the owned `ComposeSecurity.lean` and 15 helpers under `ComposeSecurity/`.
- **Evidence:** `review-evidence.zip`, SHA-256 `c11ce8bb81d2ab7bf19259740f78c1dd2006d08e14e6672f9b257a131445a24b`, 851 entries.

## Checks
- **Integrity:**
  - The manifests verify 1062/1062 and 1031/1031.
  - The 12 hashes reproduce only with signing on (SC-F05).
  - `src/` equals the 16 files. The package verifies 7/7 and its sources 152/152.
- **Build:**
  - 279/279 modules give rc 0, with 0 errors in both forms, and 0 warnings in the unit's modules. The whole-tree check covers 1264 modules: OK.
  - The build ran at LE-doc `f61ce08f`. LE-prose changes only a docstring: the code is identical with doc comments stripped (maintainer check). It is rebuilt in #324's integration build.
- **Statements:** the owned file's 11 declarations show 0 differences, and each control reports exactly 1. Exactly the 3 targets change. decls2 gives 185 ADDED, 0 CHANGED, 0 REMOVED. There are 0 name clashes.
- **Axioms:** the targets and `polyTime_compose` use only the standard three. None of the 258 stored constants uses `sorryAx`.
- **Rule 10:** the seals pass 64/64 at the head and 4/4 at the base. The coe controls are ALL_OK; strict fails only on `ctlCoeReader`. The scan finds 0 foreign definitions.
- **Admissions:** 31 → 28, by exactly the three targets.
- **Lint:** 92/101, with identical line sets.
- **Content:** the proof follows the five-step sketch, with ε = ε_A + ε_B.
- **Overlap:** the trial merges with #313, #318, #319 and sc-garble are clean.
- **Restore:** `dl-oleans` is exactly `457ba704…`.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| SC-F01 | minor | Public lemmas are restated instead of imported, because the worker read the brief's two allowed imports as exhaustive. The restatements are disclosed in the checkpoint REPORTs: a third `negligible_polyExpr_mul` (`EnsemblesLemmas.lean:377`); `appendCoins` = `coinsEquiv`; `ofFn_blocks_symm` = `FunFamily.ofFn_blocks_symm`; and `polyTimeComputable_flatMap_range`, `flatMap_range_ite`, `iterSnd_poly`, `encodeMsgs_eq_flatMap`, `msgAt_encodeMsgs` and the `padTo` family from `ThreeColoring/Machines.lean`. | **Ruling (Seyoon, 2026-11-15): ledger.** DL-49; re-point in the cleanup. |
| SC-F02 | info | The final REPORT's overlap section relies on the checkpoint tables. | Copies are in the evidence. |
| SC-F03 | minor | The frozen prose of `polyTime_compose` still called the efficiency theorems `sorry`s. | **Ruling (Seyoon): a prose-only exception.** Fixed by LE-prose `a6eaebd7`; the header and code are identical. |
| SC-F04 | info | 70 public declarations had no formula. | **Fixed** by LE-doc. |
| SC-F05 | info | `COMMITS.tsv` has no signing column. | Note. |

## ===== briefs/pass-shelat-ch5-8/gates/37-sc-compose/worker-report.md =====

# Fill `sc-compose` · final · `composeP_efficient`, `composeV_efficient`, `hbcSecure_compose`

**Worker** Claude. **Unit** `sc-compose` ([Gol04, §7.3.1, Theorem 7.3.3], the semi-honest composition
theorem). **Issue base** `107f1e8c218733eac12d6b9bee6fece441271317` (`cryptography/pass-shelat-ch2-4`), read from the
exchange at `2b9270ad095e993b020cb5e447d5a0043496802a` (pack 7/7 and SOURCE 152/152 verified:
`evidence/logs/inputs-check.log`). **Proof branch** `fill/sc-compose` (local), twelve commits over the base;
head `d3f405d4671a3ad0ffd3930ef182a43cb12ed134`. Checkpoints 1 and 2 were delivered at exchange `419c4ceb9` and
`f1ba0b1ac`.

| commit | content |
|---|---|
| `a3cb219da` … `32f837d9e` | checkpoint 1 (four commits): `composeP_efficient`, `composeV_efficient` |
| `2d99291eb` … `392a95ecb` | checkpoint 2 (four commits): the simulators, the output clause, the statistical switch |
| `756cb2c88eb2c99ce7b1b01f2502ba9480a36048` | five helpers (steps 3–5) and the proof of `hbcSecure_compose`; module title, `## Main results`, the theorem's sketch |
| `93afd4f35306371e201ea11ac8dd376efc3312ec` | Rule-10: read `Protocol.transcript`, `acceptProb`, `distAdv` through their published readers (found by the seals) |
| `034f90a97d75d2f2fa012438b7b0ffc70b13f5c2` | Rule-10: `exists_viewP_le`, `exists_viewV_le` with explicit length facts (found by the seals) |
| `d3f405d4671a3ad0ffd3930ef182a43cb12ed134` | proof-sketch paragraphs of those two lemmas (docstrings only) |

## Status of the targets

| target | status |
|---|---|
| `composeP_efficient` | **proved** (axioms `propext`, `Classical.choice`, `Quot.sound`) |
| `composeV_efficient` | **proved** (same axioms) |
| `hbcSecure_compose` | **proved** (same axioms) |

`polyTime_compose` (proved at the base from the three) uses only the standard axioms. No statement was
changed; no ℓ-output PRF is built or needed. The sorry census changes from the base exactly by the removal of
the three targets (31 → 28 declarations, 14 → 13 modules).

## Changed files

| file | base | final | content |
|---|---|---|---|
| `SecureComputation/ComposeSecurity.lean` (owned) | 382 | 449 | imports the 15 helpers; `## Contents`; title without "(statement phase)"; `## Main results` status; the three proofs; their `**Proof sketch.**` paragraphs rewritten to describe the delivered proofs (statement prose unchanged) |
| `ComposeSecurity/Machines.lean` | — | 257 | polynomial-time machines on encoded histories (checkpoint 1) |
| `ComposeSecurity/Efficiency.lean` | — | 575 | the composed parties as polynomial-time functions of the layout (checkpoint 1) |
| `ComposeSecurity/Probability.lean` | — | 124 | the statistical switch, fixing coordinates, negligible × polynomial |
| `ComposeSecurity/Reductions.lean` | — | 106 | advice-dependent pre-/post-processing with extra coins |
| `ComposeSecurity/Assembly.lean` | — | 284 | the assembled view `asmView` and its word form |
| `ComposeSecurity/Runs.lean` | — | 604 | the coins run by run, `GoodRuns`, the real samples under `GoodRuns` |
| `ComposeSecurity/Bounds.lean` | — | 96 | lengths of encodings, transcripts, machine outputs |
| `ComposeSecurity/Sim.lean` | — | 249 | `Φ` (`phiV`, `phiD`), the simulator, the reduction to the hybrid model |
| `ComposeSecurity/Accept.lean` | — | 192 | coin splittings, acceptance with pre-/post-processing, test machines |
| `ComposeSecurity/Correct.lean` | — | 204 | correctness of a secure protocol, the union bound over the runs |
| `ComposeSecurity/Chain.lean` | — | 260 | the hybrid argument over the runs (generic) |
| `ComposeSecurity/Template.lean` | — | 183 | the reduction of one hybrid step with the worst-case template as advice |
| `ComposeSecurity/Lengths.lean` | — | 286 | polynomial bounds on the words of the templates |
| `ComposeSecurity/SideA.lean` | — | 453 | Alice's side (`exists_simA`) |
| `ComposeSecurity/SideB.lean` | — | 438 | Bob's side (`exists_simB`) |

Sketch edits: `composeP_efficient`, `composeV_efficient` (checkpoint 1) and `hbcSecure_compose` (final) have
sketches describing the delivered proofs. The docstring of `polyTime_compose` still says "`sorry`s under their
sketches" about the efficiency theorems: it is another declaration's statement prose, which the brief freezes, so
I left it and flag it for the landing edit.

## The proof of `hbcSecure_compose`

Polynomial time is `polyTime_compose`. For each side there is one simulator, and for a distinguisher `D` the sum of
the two sides' negligible bounds bounds both advantages (each bound dominates a distinguishing advantage, so it
is nonnegative). Alice's side (`exists_simA`; Bob's, `exists_simB`, is symmetric, with `ρ.V`'s coins, Alice's moves
read and the leading fillers):

1. **Simulator** (`ComposeSim.exists_simulator`): `S_A^H` post-processed by `Φ = phiV`, which recomputes the call
   inputs from the `main`-tape of the simulated `main`-view, runs `S_A^ρ` on each with its answer block and a fresh
   coin block, and assembles the view (`asmView`). Coins `S_A^H.coins + calls · S_A^ρ.coins`.
2. **Output clause and switch** (`exists_correct`, `uprob_not_goodRuns_le`, `distAdv_le_uprob_of_eq`,
   `realA_compose_sampleA`): with the worst-case inputs of each length as advice of a test machine, every party's
   `ρ`-output is wrong with probability `≤ ε_c(n)`; off `¬GoodRuns` (probability `≤ L(n) ε_c(n)`) the real sample is
   `sampleA m (real run views)` on the coins `composeCoins (m, t)`.
3. **Hybrids over the runs** (`ComposeProb.abs_chain_le`, `exists_hyb_step`, `exists_gapA`, `exists_gap_le`): hybrid
   `i` has runs `< i` simulated. Overwriting run `i`'s seeds (`acceptProb_update`) and fixing the other
   coordinates at their worst value (`exists_abs_sub_le_sections`) reduces a step to one `ρ`-sample: the reduction
   `D ∘ hybW` holds as advice the template of the worst instance `(x, y, i, coordinates)` of length `n` (header,
   the other runs' words, Bob's output; polynomially long by `exists_tmplA_bound`), inserts the sample's view and
   assembles. Each step is `≤ ε₂(n)`, the chain `≤ L(n) ε₂(n)`.
4. **Hybrid model** (`acceptProb_realA_dPhi`, `ComposeProb.acceptProb_post_pre`, `exists_dPhi`): with all runs
   simulated the sample is `D ∘ Φ` on `H.realA F n x y` (the extra coins read as blocks, `blocksCoins`), and `D` on
   `S_A` is `D ∘ Φ` on `F.idealA S_A^H`; `H.HBCSecure F` gives `ε₃(n)`.
5. **Total** `L(n)(ε_c(n) + ε₂(n)) + ε₃(n)` (the brief's `L(n)(2ε₁(n) + ε₂(n)) + ε₃(n)` with
   `ε_c = ε_A + ε_B`), negligible by `negligible_polyExpr_mul` and `Negligible.add`.

Edge cases: `L(n) = 0` (no hybrid step; the instance type of `exists_gap_le` is empty at such `n`, where the advice
is `[]`; the union bound is `0`); `ρ.rounds(n) = 0` (empty run chunks); `hM` (in `realA_compose_eq`,
`realB_compose_eq`); the fillers and the leading fillers (`segW`, `asmView`); the tape cut lengths (exact on real
views: `padTo_of_length`); `padFin` readback (`answersRealA_eq_answersA`); Bob's side (`SideB.lean`, symmetric).

## New declarations

Checkpoints 1 and 2: as listed in their reports (unchanged since, except the reuse commit `5b90f0dac`, which
removed `acceptProb_seed_fst`, `uprob_fst_eq`, `uexp_le_of_le`, `uprob_coord`, `distAdv_triangle`). Final:

- `Chain.lean` (`ComposeProb`): `hybV` (+`hybV_eq`), `plugV` (+`plugV_eq`), `hybV_update`, `hybV_succ_update`,
  `exists_hyb_step`, `acceptProb_hyb_zero`, `acceptProb_hyb_last`, `abs_chain_le`, `getD_plug`.
- `Template.lean` (`ComposeSim`): `tmplW` (+`tmplW_eq`), `hybW` (+`hybW_eq`), `hybW_tmplW`, `polyTimeComputable_hybW`,
  `exists_gap_le`.
- `Lengths.lean`: `HybridProtocol.length_answersA`, `length_answersB`, `exists_main_msgs_le`,
  `exists_main_outV_le`, `exists_main_outP_le`; `ComposeBound.exists_viewP_le`, `exists_viewV_le`,
  `exists_runAt_le`; one private `exists_ofFn_eq` (see Overlap).
- `SideA.lean` (`HybridProtocol`): `viewRunA` (+`_eq`), `simRunA` (+`_eq`), `sampleA` (+`_eq`),
  `realA_compose_sampleA`, `exists_tmplA_bound`, `exists_gapA`, `acceptProb_realA_dPhi`, `exists_simA`.
- `SideB.lean` (`HybridProtocol`): the same with `B`.

Every new public `def` has its `_eq` reader; every new declaration has a docstring with its formula; every proof of
15 lines or more has a `**Proof sketch.**` paragraph; no `@[simp]`.

## Overlap and reuse

Searches: `evidence/overlap/dupsearch-base.log` (checkpoint 1), `dupsearch-base-cp2.log` (every new name and
statement shape, on a checkout of the base), `dupsearch-final.log` (the same patterns on the final tree), and a
scan of the published lemma lists of the modules in the permitted import closure. The checkpoint-2 overlap table
(in its report, repeated here in short) and the checkpoint-1 table stand; additions for the final helpers:

Reused (final): `acceptProb_fst`, `acceptProb_snd`, `acceptProb_update` (`Pseudorandom/Indistinguishability.lean:73,83,103`),
`abs_sub_le_sum_hybrids` (`Foundations/Probability.lean:218`), `acceptProb_comp_equiv`, `Finset.exists_max_image`,
`NUPPT.runAtL_eq_output_layout`, `coinBlock_flatten`, `Protocol.transcript_eq_transcriptWith`, `View.encode_mk`,
`length_pairEncode`, `PolyExpr.eval_*`.

| new declaration | nearest relative | relation, and why not reused |
|---|---|---|
| `hybV`, `plugV`, `exists_hyb_step`, `acceptProb_hyb_zero/last`, `abs_chain_le` | `Pseudorandom/Indistinguishability.lean:198–330` `multicopyHybrid`, `multicopyRed`, `acceptProb_multicopyRed_left/right`, `exists_multicopyRed_ge` | the same hybrid argument for `t` i.i.d. copies of one sampler; here the runs share the seed `m` and run `j`'s samplers depend on `m` and `j`, so the multicopy statements do not apply. The resampling step reuses `acceptProb_update` (as `acceptProb_multicopyRed_left` does). New. |
| `getD_plug` | `ZeroKnowledge/CommitmentLemmas.lean:189` (`ofFn (update W k z)` split at `k`) | the list form of plugging one entry; not importable. New. |
| `tmplW`, `hybW`, `exists_gap_le` | the worst-case-advice reductions written inline with `Finset.exists_max_image` (`Encryption/PublicKey/Hybrid.lean:295`, `Pseudorandom/NextBit.lean:411`, `ZeroKnowledge/Commitment.lean:317`) | no published lemma packages "argmax instance as advice"; new, generic in the samplers and the instance family. |
| `length_answersA`, `length_answersB` | owned file `length_answersRealA`, `length_answersRealB` (`ComposeSecurity.lean:128,135` final; 88, 95 at the base) | the same computation for `answersA`/`answersB` (Hybrid.lean) instead of the honest answers; the owned file's are about other definitions. New. |
| private `exists_ofFn_eq` (`Lengths.lean`) | owned file's private `exists_ofFn_eq` (`ComposeSecurity.lean:122` final; 82 at the base) | **restated** (two lines from `List.ofFn_getElem`): the owned file's declarations are foreign to the helpers and it is private there. Disclosed here. |
| `exists_main_msgs_le`, `exists_main_outV_le`, `exists_main_outP_le`, `exists_viewP_le`, `exists_viewV_le`, `exists_runAt_le` | owned `compose_msg_bound` (the message half); `InteractiveProofs.lean:133` (`ProverBounded` clauses) | the polynomial bounds the advice needs, built from `H.PolyTime`, `G.PolyTime ρ`, `Efficient.length_next_le`, `length_runAt_le`. New. |
| `viewRunA/B`, `simRunA/B`, `sampleA/B` and the side lemmas | `realViewA/B` (`Runs.lean`), `phiV_view` (`Sim.lean`) | the per-run words and the sample as functions of the coordinates. New. |

## Scope requests

None.

## Promotion requests

As in the checkpoint reports (the FP/history toolkit of `Machines.lean`, `Efficient.exists_polyTime`,
`polyTimeComputable_slots`, `negligible_polyExpr_mul`, the coin splittings, the acceptance lemmas). In addition:
`abs_chain_le`/`exists_hyb_step` (a hybrid argument over non-identical, seed-sharing coordinates) beside the
multicopy lemma in `Pseudorandom/Indistinguishability.lean`, and `exists_gap_le`'s argmax-advice pattern as a
generic lemma for the asymptotic layer.

## Checks

- **Order** (`evidence/final/order-final.txt`, `reorder.log`): `order.txt` with the 15 helpers inserted before their
  consumers (167 modules).
- **Sweep** (`evidence/final/`): **167/167 exit 0, 0 error diagnostics** (`sweep-errors.txt`, counted with
  `^\S+\.lean:\d+:\d+: error[:(]`; `sweep.tsv`, logs `sweep/`). History in `sweep-run.log`: full sweep at
  `756cb2c88`; after the seal fixes the rows from `Probability` (position 140) to the end were moved to
  `sweep-superseded.tsv` (logs `sweep-superseded/`) and re-checked at `034f90a97`; after the docstring commit the rows
  from `Lengths` (position 160) on were moved again (logs `sweep-superseded2/`) and re-checked at `d3f405d46`. Rows
  1–139 are modules none of the later commits touch; every row's module is identical at `d3f405d46`.
- **Sorry census** (`evidence/final/sorry-census-final.txt`, `census-diff.txt`): 28 declarations in 13 modules; the
  only change from the base census (31 in 14) is the removal of `composeP_efficient`, `composeV_efficient` and
  `hbcSecure_compose`.
- **Axioms** (`evidence/axioms/axioms-final.log`): all **258** stored constants of the owned file and the 15 helpers
  use only `propext`, `Classical.choice`, `Quot.sound`; the three targets and `polyTime_compose`:
  `[Classical.choice, Quot.sound, propext]`.
- **Rule 10 — seals** (`evidence/seals/`, tool `seals.py`, sources `evidence/scratch-src/seal/`): whole-file seals of
  the owned file at the base (ROOT = base checkout) and of the owned file and the 15 helpers at the final tree,
  each over its full TCSlib import closure (every module of the closure foreign), in the four variants strict-A,
  strict-B, coe-A, coe-B (A: `PolyExpr.eval` exempt as notation; B: sealed; strict: projection coercions sealed;
  coe: the `FinDist` coercion exempt). Errors counted with `^\S+\.lean:\d+:\d+: error[:(]`, raw logs kept.
  - base: 4/4 exit 0, **0 errors** (670/671/669/670 requests).
  - final: **64/64 exit 0, 0 errors** (`final/results.jsonl`; e.g. the owned file 1192/1193/1191/1192 requests).
    The first final run found failures, all fixed by the two Rule-10 commits and re-sealed; the superseded results
    are kept (`final/results-superseded.jsonl`, logs `final/superseded*/`): `Lengths` `exists_main_msgs_le`,
    `exists_viewP_le`, `exists_viewV_le` (transcript read as `transcriptWith`; then simp normal forms that differ
    under the seals), `Probability` `acceptProb_eq_uexp_sections` (`acceptProb` by `rfl`), `SideA` `exists_simA`,
    `SideB` `exists_simB` (`distAdv` by defeq); each failed in all four variants alike.
  - strict vs coe: the variants differ by one request (the `FinDist` coercion instance, which is in the closure);
    no result differs between them.
- **Paired controls** (`evidence/controls/`, source `evidence/scratch-src/controls/Controls.lean`, tool
  `controls2.py`): seven pairs (`segW`, `tmplW`, `inA`, `hybV`, `viewRunA` of my helpers; `answersA` of the frozen
  `Hybrid.lean`; `PolyExpr.eval`). Unsealed every example closes; in each sealed variant each `CONTROL` fails exactly
  once and each `READER` closes; the `PolyExpr.eval` control fails exactly in the B variants (`results.json`).
- **Explicit-unfold scan** (`evidence/rwids/`, tools `rwids.py`, `rwids_run.py`): every identifier given to
  `rw`/`simp`/`unfold`/… in the 16 files resolves to a theorem, a local hypothesis, or one of the file's own
  definitions (`phiD`, `simV` in `Sim.lean`); no foreign definition is unfolded by name.
- **Statement check** (`evidence/headers/headers-final.txt`): 11 → 11 base declarations, headers, `omit … in` lines
  and statement prose byte-identical: **0 differences**; control (`control-final.txt`): one altered character →
  exactly one difference.
- **Width and size** (`evidence/checks/widths-final.txt`): no line over 100 characters; every file ≤ 1000 lines.
- **Sketches** (`evidence/checks/sketches-final.txt`): every proof of 15 lines or more has a `**Proof sketch.**`
  paragraph; the one flag is the definition `runW` (a body, not a proof).
- **Lint** (`evidence/lint/lint-final.txt`, `lintdiff-final.txt`): 92 FAIL / 101 WARN, line sets equal to the base's
  (`lint-base.txt`): **no new FAIL, no new WARN, none gone**.
- **Environment.** As at checkpoint 1 (`evidence/logs/`): packages symlinked at the manifest's pins (11 match, 0
  mismatch, 4 absent), narrowed cache get (74 roots), bootstrap 152/152. One Lean process at a time against the
  olean tree; no `lake build`. The host restarted several times during the work (uptime resets); the resumable
  runners re-checked any module or probe that had started without finishing, as recorded in the run logs.
  Development checks of single files used a scratch copy compiled with `lean` and a heartbeat limit (not evidence).
  The repository's `AGENTS.md` asks agents to read goals from the VS Code infoview rather than run Lean from a
  shell; this environment has no editor, and the brief prescribes `scripts/lean_check_tree.sh`, so every check went
  through that script (one module per call) or the scratch copies above; `lake build` was never run.

## Patches and reproduction

`patches/0001…0012-*.patch` and `patches/COMMITS.tsv`; a scratch clone at the issue base applies the series with
`git am`, the committer of each row set from `COMMITS.tsv`, and reproduces every hash and the final tree
(`evidence/amcheck/amcheck-final.log`).

## Evidence

`evidence/SHA256SUMS` covers every evidence file (inputs, raw logs, `results.jsonl`, seal/control/scan/axiom sources,
tools); the top-level `SHA256SUMS` covers every delivered file except itself; both checked against the delivered
paths.

## ===== policy.md =====

# TCSlib Contribution Policy

Standards for all Lean contributions to this repository, whether written by humans or by
agents. This document covers three things: **modularity** (how code is organized),
**attribution** (how every result is traced to a source), and **proof sketches** (how every
formal proof is accompanied by readable mathematics).

It complements, and does not replace:

- `workflow.md` — the campaign formalization process (phases, audit gates, fill epochs)
  that produces code meeting these standards.
- `.github/copilot-instructions.md` — build workflows, import rules, CI integration points.
- `AGENTS.md` / `.claude/CLAUDE.md` — the sorry-ladder proof workflow and agent roster.
- `blueprint/BLUEPRINT_PIPELINE.md` — how blueprint entries are generated and validated.

Where this document names an existing mechanism (blueprint macros, hygiene scripts), the
policy is to *use that mechanism*, not to invent a parallel one.

## 1. Modularity

**Layout.** Content lives at `TCSlib/<Area>/<Topic>/<Piece>.lean`, one coherent concept or
lemma cluster per file, with a facade file `TCSlib/<Area>/<Topic>.lean` that imports every
child and carries a `/-! -/` module docstring with a `## Contents` list (one line per child).
See `TCSlib/Complexity/NPReductions.lean` for the reference example.

**File size.** Target 150–600 lines per math file. A file approaching 1000 lines should be
split unless there is a positive reason not to (e.g. a single long proof that cannot be
usefully decomposed).

**Exports.** Every new topic facade must be imported from `TCSlib.lean`. CI only builds what
is reachable from `TCSlib.lean`; an unexported file is invisible to CI, docs, and the
blueprint.

**Imports.** Precise module imports only. A bare `import Mathlib` fails CI. Import only what
the file uses.

**Namespaces.** Namespaces are area-local: pick one namespace root per topic and use it
consistently within that topic. Do not leak auxiliary definitions into the root namespace;
mark internal helpers `private` or put them in a dedicated inner namespace.
*Model registry exception*: a model-defining **type** (a machine, circuit, formula, or
decision-tree model) may live at the root namespace, Mathlib-style, provided it is
registered in the catalog facade `TCSlib/ComputationalModels.lean`; its operations and
lemmas still live in the type's own namespace. Anything else at root is a leak.

**Layering.** Keep definition files separate from heavyweight theorem files, so that
downstream work can import a model or a class definition without pulling in every proof about
it. When a development has both a "raw/general" layer and a "bundled" layer (e.g. a machine
model that is parametric in its types, plus a bundled version carrying finiteness instances),
headline definitions and theorems are stated against the bundled layer; the raw layer is
internal plumbing.

**Helpers.** Foundational helper lemmas that serve a whole area belong in that area's
`Basic.lean`, not in the file that first needed them.

**Definitions land with their lemmas** (user, 2026-10-16). Every new public `def` is published,
in the same PR and beside the definition, with the lemmas that let a consumer read it without
unfolding:
- a structure-valued definition (a contract, a configuration, zone contents): its field
  equations, generated by `simps` with `(config := { isSimp := false })` and explicit
  projections (`simps!` where the body is another constructor's result);
- any other definition: an equation lemma `<name>_eq` (by `rfl` where that holds), or case
  lemmas that together cover every input (`_of_lt`/`_of_le`, `_true`/`_false`, one per
  constructor);
- a predicate: an `_iff` characterization;
- a machine: its run or contract lemma, the only way consumers read a machine.

None carries `@[simp]` unless a gate approves it, and each docstring states its formula. Consumers
never unfold another file's definition (the no-unfolding rule of the briefs, user 2026-10-16). The
rule binds TCSlib's own definitions: core and Mathlib definitions may reduce in a `rfl`, `decide`
or `show` step, but are never passed to `simp`, `rw` or `unfold`; use their equation lemmas
(`Bool.toNat_true`, not `simp [Bool.toNat]`) (user, 2026-10-23).
**Reducible abbreviations are notation** (user, 2026-10-26). Lean unfolds a TCSlib `abbrev` (such
as `Turing.Cfg.Halted`, `cfg.state = none`) at every step, and the standard seal cannot cover it:
under Lean's default reducibility validation, `attribute [local irreducible]` fails on a reducible
declaration (only the unsafe override `set_option allowUnsafeReducibility true`, which the
campaign's seals do not use, lifts the check). So reading an abbreviation through its body,
for example `¬ c.Halted` as `c.state ≠ none`, is allowed and is not a definitional closure. A
consumer names it in `simp`, `rw` or `unfold` only through a published lemma where one exists, and
a new public `abbrev` still lands with its `_iff` or `_eq` lemma.
They read the machine model's primitives (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
`Cfg.mapState`) through the existing lemmas. The style lint's check 8 reports, per file, every
public `def` with no lemma named after it and no `simps` attribute, so a head-against-base diff
of the lint shows any new definition that lacks one. Definitions that predate the rule are listed
by the same check and covered as consumers need them.

**Construction reuse.** Machines are built from the verified construction layers, not from
scratch: the combinators and routine catalog of `TCSlib/Complexity/TuringMachine/Build/`
(conventions, wrappers, loops, primitives, embeddings, seams, and the catalog rows —
`machine-library-design.md` is the registry), the registered hosts (**Hosts come first**,
below), and the program layers (`LogProg.ARM`, `CounterProg`, and the general programming
layer of `machine-library-design.md` §15 once it lands) where a program-level description
suffices. Before writing a transition
table by hand, check the registry; a routine that exists is cited, not re-derived. A routine
that *almost* exists is the interesting case: do not write a third private variant — either
consume the general form, or commission the missing form into the shared layer (during a
fill batch: a `private` local copy plus a "requested shared lemma" in the report, promoted
at the next shared-file window). A hand-built machine is acceptable only when no layer
covers the need, and its docstring must say so and name what was missing — that sentence is
what turns the gap into the next catalog row. The chapter-1/2 files that predate this layer
re-derived the same bank/relocation/dispatch/frame families four times over (`emitterBank*`,
`clBank*`, `clSlot*`, …); the retrofit paying that debt back is the standing cautionary
tale. The same discipline applies to circuit construction once `CircuitComplexity`'s gadget
layer exists: gadgets, wiring combinators, and size/depth ledgers get one shared home and a
registry, and new circuits are assembled from it.

**Hosts come first.** A *host* is a control structure that drives other routines rather than
computing one value: a search or traversal (BFS, DFS, backtracking, an odometer over
assignments), a recursion or evaluation scheme (AND/OR evaluation, Savitch's midpoint
recursion), an interpreter or simulation step block, a clocked or windowed runner, a dispatcher
over a data structure (tables, records), or an input device. Any routine whose natural contract
does not depend on its first consumer counts as a host; leaf rows (copy, compare, seek,
arithmetic) do not. **A host is never built `private` inside the proof that first needs it.**
Its public contract is designed, statement-gated and placed in the shared construction layer
first, generic in the parts its consumers vary (the leaf test, the step relation, the data
domain), with time and space (head-envelope) clauses. Consumers cite it, under the campaign's
proved-modulo rule while its own fill is still running. The host registry is
`machine-library-design.md` §14. A private host already in the tree is harvested into the
shared layer before a second consumer is briefed against it. The rule exists because private
hosts were the main way the library overfitted to single proofs: four configuration encodings,
three reachability notions and a private search host per theorem, each to be re-derived by the
next consumer (assessment of 2026-10-12, recorded in the design document). (User, binding,
2026-10-12.)

**Duplication.** Some duplication is mechanically forced by the campaign discipline —
exclusive file ownership, the statement freeze, and `private` visibility leave a fill batch
no other legal way to use another file's unexported machinery — and occasionally it is the
right engineering call. It is never silently acceptable: **every instance of duplicated
proved material must be human-approved.** A fill batch discloses each copy in its report;
the maintainer's integration ledger totals copied material per file (`workflow.md` §4); and
the audit template treats accumulated duplication as a major finding that a gate cannot
close over without the human maintainer explicitly accepting the debt and naming where and
when it is paid back (the registry's dedup/refactor queue). Duplication that was never
disclosed is a freeze violation, not debt.

**File header.** Every math file begins with the Mathlib-style copyright block, its imports,
the repo-standard options

```
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
```

then a module docstring containing `# Title`, `## Main definitions`, `## Main results`, and
`## References` (see §2).

## 2. Attribution

Every mathematical statement in the library must be traceable to a source, at the level of
precision of a textbook theorem number or a paper section.

**File-level.** Every math file's module docstring contains a `## References` section giving
full citations with short tags, e.g.

```
## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
```

**Declaration-level.** Every definition, theorem, and lemma that corresponds to a result in
a source carries the tag with a precise location in its docstring: `[AB09, Claim 1.6]`,
`[AB09, §1.7]`, `[GRS25, Thm 4.2.1]`. Purely technical glue lemmas with no textbook
counterpart may omit the tag; anything a reader would recognize as "a result" may not.

**Deviations.** If the formal statement deviates from the source — different constants,
strengthened or weakened hypotheses, a reformulation — the docstring must say so and briefly
say why (e.g. "stated with explicit constant 5k rather than O(·), following the proof").

**Statement prose.** Every public declaration's docstring begins with a natural-language
statement of what it asserts (for a definition: what it is), precise enough that a reader
could judge the formalization's fidelity without parsing the Lean. The `[Tag, location]`
citation and any deviation note attach to that statement; the proof sketch (§3) follows it.
A bare label ("Unfolding lemma", "Helper for X") is not a statement. Instances are exempt,
as are vendored files (which follow upstream style). `private` declarations should carry
docstrings too, but at reviewer discretion rather than as a hard requirement. The blueprint
remains the cross-referenced informal layer for dependency structure (see **Blueprint**);
the docstring statement is what external audits compare blind restatements against, so it
is part of the trusted surface.

**Blueprint.** When an ingested reference exists under `blueprint/src/references/`, blueprint
entries use `\statementsource{<ref>}{<anchor>}` and `\proofsource{<ref>}{<anchor>}` to cite
it, subject to the existing rule that these are written only after an approved proofmatch
run. When starting a new chapter or paper, ingest it as a reference pair
(`<name>.raw.md` + `<name>.md`) so these citations are possible: put the PDF under
`blueprint/src/references/` in the change that formalizes it and run
`python3 scripts/dataset_pipeline.py --yes`, which ingests it, matches every text the
blueprint does not cite yet, and carries the new statements into the dataset
(`python3 scripts/sources.py add TAG=<pdf or md>` does the ingest and match alone, with
the docstring tag above; `python3 scripts/sources.py` shows which texts are attached and
which are still missing; see `dataset/INSTRUCTIONS.md`). The dataset builder does not
search outside that directory for sources; an unattached text leaves the theorems with
informalized proof notes instead of citations.

**Vendored code.** Lean code adapted from another project keeps the original copyright
header and license notice, and its file docstring names the source project, the commit it
was taken from, and a summary of local modifications.

**Design adaptation.** When a construction, proof architecture, or module design is
adapted from — or materially inspired by — another project's code, the debt is cited even
when no code is transcribed. The module docstring's `## References` section names the
source project, author, module or archive entry, the commit or version consulted, and its
license, with a short tag usable at declaration level; the precedent is
`TuringMachine/Composition.lean`'s `[Balbach22]` for the Isabelle AFP `Cook_Levin`
composition-combinator architecture. Design documents and blueprint entries built on the
adapted design carry the same citation. Examining external code purely for comparison,
with nothing taken, creates no citation duty, but on a campaign it belongs in the
campaign's records (plan decision log or backlog) so the provenance question is answerable
later. (Maintainer guideline, binding, 2026-10-06.)

## 3. Proof sketches

Every nontrivial formal proof is accompanied by a human-readable English proof sketch, kept
next to the Lean it describes.

**What counts as nontrivial.** Rule of thumb: any proof longer than ~20 lines of tactics, or
that would rate difficulty ≥ 3 on the blueprint scale. One-line `simp`/`omega`/`exact`
proofs need no sketch.

**Where sketches live.** In the Lean file itself:

- For most theorems: a `**Proof sketch.**` paragraph at the end of the theorem's docstring,
  written in mathematical English (not Lean identifiers), naming the key intermediate steps.
- For long proofs: additionally, short comments at the major `have`/section boundaries tying
  the tactics back to the sketch's steps.

The named intermediate steps of a sketch should be visible in the formalization as `have`s
or standalone lemmas — if the sketch says "first reduce to the one-tape case", there should
be a lemma that is that reduction.

**Where sketches do not live.** Not in the blueprint. Blueprint statement entries state
claims only; `scripts/dataset_hygiene.py --strict` hard-fails on proof content there. The
blueprint records *what* is true and its dependency structure; the Lean docstrings record
*why* it is true.

**Sketches and the sorry ladder.** When landing a sorry-skeleton, write the sketch at
skeleton time — the sketch *is* the plan, and each `sorry` should correspond to a named step
of it. A skeleton whose sketch cannot be written is not ready to land.

**Synchronization.** When a proof strategy changes, the sketch changes in the same commit.
A sketch that describes a proof the code no longer performs is worse than no sketch.

## Review checklist

Before merging new Lean content, check:

1. Files follow the Area/Topic layout with a facade, and `TCSlib.lean` exports are updated.
2. Imports are precise; no bare `import Mathlib`.
3. Every file has a `## References` section; every source-derived declaration has a
   `[Tag, location]` in its docstring; deviations from sources are noted.
4. Every nontrivial proof (or sorry-stub standing in for one) has a proof sketch.
5. Every public declaration (instances and vendored files excepted) has a docstring
   opening with a natural-language statement of what it asserts
   (`python3 scripts/style_lint.py` checks presence mechanically; statement quality is
   review judgment).
6. `zsh scripts/lean_check.sh <file>` reports zero errors for each touched file.
7. If blueprint content was touched: `python3 scripts/blueprint_validate.py --strict` and
   `python3 scripts/dataset_hygiene.py --strict` pass.
8. No new private host: every search, recursion, interpreter, runner or input device the
   change introduces is a registered public host, or cites one (§1, **Hosts come first**).

## ===== briefs/pass-shelat-ch5-8/fills/sc-compose/issued-r1/brief.md =====

# Claude fill · the semi-honest composition theorem (`composeP_efficient`, `composeV_efficient` and `hbcSecure_compose`, [Gol04, Theorem 7.3.3])

**Issue base** `107f1e8c218733eac12d6b9bee6fece441271317` on `cryptography/pass-shelat-ch2-4` (the records tip after #303, #305, #306,
#308 and #309; records-only commits since `58a061c9`). **Unit** `sc-compose`. **Worker** Claude (standing ruling, 2026-11-11). **Lean** 4.25.0 and the
Mathlib revision in that commit's `lake-manifest.json`.

Prove the admitted theorems `composeP_efficient`, `composeV_efficient` and `hbcSecure_compose` of [Gol04, §7.3.1, Theorem 7.3.3] (used unstated by [PS10, Theorem 163.7]) in
`TCSlib/Cryptography/SecureComputation/ComposeSecurity.lean`. The statements passed the prong B statement phase and Gate 06B (closed PASS),
and are frozen. Each docstring holds the maintainer's proof sketch.

## Feasibility (maintainer's assessment)

Feasible as stated (plan §2.11–2.12: well posed, no false statement found). The phase lemmas exist. The missing pieces are the interleaved-slot map lemma, the efficiency extraction, a simulator-repeating NUPPT, the bad-event switch and the run-`i` coin equivalence. No dependency on an admitted target: Yao and OT meet only in `YaoReal.lean`.

**Estimated size:** 3,000–5,300 lines (plan: the efficiency pair 1,000–1,800, `hbcSecure_compose` 2,000–3,500), in 6–10 helper modules. `ComposeSecurity.lean` is at 382 lines.

## Checkout and delivery

- Fetch `cryptography/pass-shelat-ch2-4`. Start a local branch `fill/sc-compose` at the exact issue base, and
  record the base in `REPORT.md`. Keep the proof branch local.
- Read `policy.md`, the attached environment addendum and `README.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/sc-compose/` on `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `patches/COMMITS.tsv`: one row per commit, giving its hash, the author's name, email and date, and the
    committer's name, email and date, so that `git am` at the base reproduces every hash. Before you push,
    check the reproduction in a scratch clone and say so in `REPORT.md`. The last batch's worker hashes
    could not be reproduced, because no committer metadata was delivered;
  - `src/`: the changed and new files;
  - `evidence/`, with an `evidence/SHA256SUMS` manifest (see *Evidence completeness*);
  - a top-level `SHA256SUMS` listing every delivered file under `inbox/fills/sc-compose/` except itself. The
    delivered paths must equal the manifest's paths exactly, with nothing missing and nothing extra.
    Check this before each push.
- Commit as `fill sc-compose: checkpoint N` and `fill sc-compose: final`.
- Pull with rebase before pushing, push only your delivery path, and never force-push. Campaign changes land
  by a maintainer PR for Seyoon's approval.

## Base and parallel work

- **#307 (dl-crh) is not merged.** It changes `Candidates/DiscreteLog.lean`, the `Hashing.lean` facade and `Hashing/FromDiscreteLog*`. This unit edits none of them, and its closure contains none of them.
- The other fills of this batch (`prf-mac`, `learning`, `derand`, `seq-zk`, `canonizer`, `sc-ot`) start from the same base.
  Each edits only its own owned file and helper directory.

## Targets (frozen; quoted from the issue base)

```lean
theorem composeP_efficient {F : Functionality} (hH : H.PolyTime F) (hρ : G.PolyTime ρ) :
    (H.composeP ρ).Efficient := by
  sorry
```

```lean
theorem composeV_efficient {F : Functionality} (hH : H.PolyTime F) (hρ : G.PolyTime ρ) :
    (H.composeV ρ).Efficient := by
  sorry
```

```lean
theorem hbcSecure_compose {G F : Functionality} (H : HybridProtocol G) (ρ : Protocol)
    (hM : ∀ n, 0 < H.main.rounds.eval n) (hH : H.HBCSecure F)
    (hρ : SecureComputation.HBCSecure ρ G) : SecureComputation.HBCSecure (H.compose ρ) F := by
  sorry
```

They live in namespace `TCSlib.Cryptography.SecureComputation.HybridProtocol`. In the section `Efficiency` the variables are `{G : Functionality} (H : HybridProtocol G) (ρ : Protocol)`;
the two efficiency theorems take `{F}`, `hH : H.PolyTime F` and `hρ : G.PolyTime ρ`. `hbcSecure_compose` takes
`hM : ∀ n, 0 < H.main.rounds.eval n`, `H.HBCSecure F` and `HBCSecure ρ G`. Read the module docstring's
deviations (calls first, `hM` with its counterexample, uniform bounds) and the theorem's five-step sketch.

**Consumers:** `polyTime_compose` (proved from the two efficiency theorems and `compose_msg_bound`) and
`YaoReal.yaoProtocol_hbcSecure`. The proof needs neither Yao nor OT (plan §1).

**Analysis.** `briefs/pass-shelat-ch5-8/maintainer/securecomp-plan-2026-11-14/plan.md`, §2.11 and §2.12. Both
statements were checked and found well posed.

## Published interfaces

| Interface | Provider |
|---|---|
| `exists_runExec_eq_transcript`, `exists_mainExec_eq_transcript`, `compose_msg_bound`, `polyTime_compose` | owned file |
| `compose_P`, `compose_V`, `composeP`, `composeV` and the `slotMsgs`/`runTape` readers | `SecureComputation/Compose.lean` (frozen) |
| `slotFromA_eq`, `slotFromB_eq`, `compose_transcript`, `compose_exec_runs`, `compose_exec_main`, `compose_viewP`, `compose_outV` | `SecureComputation/ComposePhases.lean` (frozen) |
| `HybridProtocol.PolyTime` (the `callA`/`callB` clauses), `HybridProtocol.HBCSecure`, `polyTime_iff`, `hbcSecure_iff`, `realA_eq`, `realB_eq`, `answersA_eq`, `answersB_eq`, `coins_eq` | `SecureComputation/Hybrid.lean` (frozen) |
| `HBCSecure`, `PolyTime`, `polyTime_iff`, `hbcSecure_iff`, `realA_eq` … `idealB_eq` | `SecureComputation/Defs.lean` (frozen) |
| `exists_hybrid_gap`, `abs_sub_le_sum_hybrids`, `uprob_exists_le`, `uprob_prod`, `uprob_comp_equiv`; `StatClose`, `distAdv_le_of_statClose` | `Foundations/Probability.lean`, `Asymptotic/Sampling.lean` |
| `polyTimeComputable_blockMap` (fixed block size), `polyTimeComputable_iterate(Find)`, `polyTimeComputable_stateFind`; `countW` | `Complexity/Randomized/Repetition.lean`, `ZeroKnowledge/EncodingMachines.lean`, `Complexity/ClassP/BinaryArith/Words.lean` |
| `Strategy.Efficient` readers (`efficient_iff`, `ofNUPPT_efficient`); `NUPPT.exists_comp`, `exists_seq`, `exists_withAdvice`, `ofPolyTimeUniform`, `Computes.polyTimeComputable`; `padFin_ofFn` | `ZeroKnowledge/Interaction.lean`, `Complexity/Randomized/Closure.lean`, `Asymptotic/Adversary.lean` |
| `Negligible.add`, `mul_pow`, `const_mul`, `mono` | `Foundations/Negligible.lean` |
| `simulate` and `OracleComp` laws, `buildComp_*`, `CostBoundedBy`, `bitCodec_*`, `ProbComp.expect_*`, `advantage_eq`, `accept_eq` | `Games/*` |

## Proof route and checkpoints

1. **Checkpoint 1 · `composeP_efficient` and `composeV_efficient` (plan §2.11).** The interleaved-slot map lemma; the extraction of a polynomial-time next-message function from `Strategy.Efficient` (`Computes.polyTimeComputable` covers uniform NUPPTs); `composeP.next` as a polynomial-time function on the raw layout: the indices from `|hist|`, the call inputs from `H.PolyTime`, the run tapes cut from `r`, one `ρ` activation or `L(n)` of them for the answers, and one `main` activation. Share the helpers between Alice and Bob. Plan estimate: 1,000–1,800 lines. Send this checkpoint.
2. **Checkpoint 2 · `hbcSecure_compose`, sketch steps 1–2.** The simulator `S_A` (and `S_B`) as a non-uniform PPT that runs `S_A^H` and then `L(n)` runs of `S_A^ρ` on blocks and assembles the view; the output clause with the worst-case inputs as advice; the statistical switch "agree off a bad event" of probability at most `2L(n)ε₁(n)`. Send this checkpoint.
3. **Final · `hbcSecure_compose`, sketch steps 3–5.** The hybrid over the runs (advice: worst `i`, inputs, `main` tapes and ideal answers; the coin-space equivalence for run `i`), the post-processing `Φ` to the hybrid model (`H.HBCSecure F`), and the total `L(n)(2ε₁(n) + ε₂(n)) + ε₃(n)`.

Check the edge cases: `L(n) = 0` calls; `ρ.rounds(n) = 0`; `hM` (the statement is false without it, see the docstring); the fillers; the tape cut lengths (exact on real views, so `Φ` is the identity there); `padFin` readback; Bob's side, symmetric to Alice's.

If the sketch is wrong, or a target is false as stated, stop and escalate with the exact obligation: a
checkpoint with the counterexample or the missing fact. Do not weaken any statement.

**Partial delivery.** If you cannot finish every target, your final payload may prove a subset. Each proved
declaration must use only the standard axioms. The others keep their `sorry` and their statements,
and `REPORT.md` says which are proved and what remains for each of the others.

## Scope and proof discipline

- **Owned file.** You own `TCSlib/Cryptography/SecureComputation/ComposeSecurity.lean` (382 lines at the issue base):
  - replace the targets' proof bodies and edit their sketches to describe the delivered proof;
  - update the module title (drop "(statement phase)" where present) and the `## Main results` status.
- **Helper modules.**
  - They are permitted under `TCSlib/Cryptography/SecureComputation/ComposeSecurity/`. The owned file imports them precisely and gets a
    `## Contents` list.
  - **Facades.** After the facade-lint fix (#305), a new helper under `X/` is covered as long as `X.lean`
    imports it, so no parent facade needs an edit.
  - A helper may import `ZeroKnowledge/GraphIsomorphism/EfficiencyRep` and `ZeroKnowledge/EncodingMachines`. Neither depends on the owned file (checked at the issue base). `SecureComputation/Defs.lean`, `Hybrid.lean`, `Compose.lean`, `ComposePhases.lean`, `SpecialEncryption.lean`, `GarblingSpecial.lean`, `YaoReal.lean`, `Yao.lean`, `Garbling*.lean`, the `FromPRF*` files and `Pseudorandom/*` are named frozen for this unit (with every other file).
- **Size and width.** Every line has at most 100 characters (Python `len`), and every file at most 1000 lines.
  Check both with a short `python3 -I` script before each push and include its output in `evidence/`.
- **Frozen files.** Do not edit any other file.
  - `Games/Efficiency.lean` is at 982 lines. Do not add to it.
  - **Scope requests.** If the route needs a change to a frozen file (a reader beside a foreign definition, an
    import, a promotion), stop that line of work. Ask Seyoon in your session, giving the exact file, the diff
    and the reason, and go ahead only on his approval. Record the request and his answer verbatim under
    `evidence/scope-request/` and in `REPORT.md` § *Scope requests*. The Codex fills obtained their facade
    imports, and dl-crh its two `DiscreteLog` readers, this way. Seyoon prefers a route with no frozen-file edit
    where one exists.
  - A lemma that belongs in an existing file goes in your helper module, with a promotion request.
- **Parallel fills.** The seven fills `prf-mac`, `learning`, `derand`, `seq-zk`, `canonizer`, `sc-ot` and
  `sc-compose` are issued from the same base. Edit only your owned file and helper directory.
- **No ℓ-output PRF.** This unit does not need the ℓ₂-output PRF machinery. Seyoon ruled that the PRF layer is generalized in a separate job, `prf-long`; do not build or copy any of it. If you find you need it, stop and escalate with the exact obligation.
- **Duplication (binding).**
  - **Search first.** Before writing any lemma, search `TCSlib/` and Mathlib for its statement shape and key
    names. Reuse published lemmas by importing them.
  - **Private lemmas.** Never copy a private lemma silently. If you need one, re-derive it from published
    readers, keep its statement general, and disclose it.
  - **Disclose every overlap.** `REPORT.md` has a section **`## Overlap and reuse`**. For every new declaration
    that restates, specializes or re-proves existing material (public or private, TCSlib or Mathlib), give its
    nearest relative (`path:line`), the relation, and why it is not reused. List the searches you ran.
  - **Why.** Undisclosed duplication is a freeze violation, not debt. The majors that held Gates 23 and 24
    were undisclosed duplicates: G23-01, a private copy of `length_le_length_encodeLog`; G24-01,
    `inputWord_take`, which re-proves the public `take_ofFn_castLE`.
  - **Nearest relatives here:** the history machines of the graph-isomorphism and 3-colouring efficiency proofs (`ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean`, `ZeroKnowledge/ThreeColoring/Machines.lean`), `polyTimeComputable_blockMap`, the hybrid lemmas of `Foundations/Probability.lean`, and the ZK simulators that run a machine on coin blocks (`ZeroKnowledge/Defs.lean`, `retry`). **Expected new API:** the plan finds no lemma for mapping a polynomial-time function over the `L(n)` interleaved run slots of a history (`blockMap` needs fixed-size blocks). Write it once, generic, as a public helper shared by both efficiency theorems; search for a near relative first, disclose it, and propose it for promotion.
- **Statements.** Preserve the target statements, every other declaration, the statement prose and the global
  simp attributes.
- **Docstrings and sketches.** The last batch's landing edits were mostly LE-doc (cca2-ett: 94 formulas and
  15 sketches; dl-crh: 59 formulas; lamport: 188 formulas and 7 sketches) and LE-width. Do these yourself:
  - every new public declaration has a docstring that states its formula: the equation or inequality, with its
    arguments in the Lean order, and a `[PS10, …]` tag where it comes from the source;
  - every proof of 15 lines or more carries a `**Proof sketch.**` paragraph, and long proofs get step comments
    (policy §3);
  - a new public `def` lands with its `_eq`, `_iff` or `simps` readers (lint check 8), and a new public
    `abbrev` with an `_eq` or `_iff` lemma;
  - add no `@[simp]`.
- **Rule 10.**
  - Use only published readers for other files' definitions, including generated matchers and projections.
  - Your helper modules count as foreign to each other and to the owned file. The owned file's definitions
    are foreign to your helpers.
  - **Notation, never sealed:**
    - `PolyExpr.eval` (Q1);
    - reducible abbreviations (2026-10-26; for example `QueryImpl`, `OracleSpec.add`, `glNeed`);
    - **projection coercions:** a `CoeFun`/`Coe` instance whose body is a structure projection, such as
      `FinDist`'s `⟨FinDist.prob⟩` (Seyoon's ruling, 2026-11-14).

    The coe-variant seals are canonical. Run the strict variant as well, and attribute each difference.

## Checks and report

- **Bootstrap.**
  - Bootstrap from `order.txt` (152 modules) and the narrow `roots.txt` (74), following the addendum.
  - Check one module per `scripts/lean_check_tree.sh` call, with one Lean process per olean tree.
  - Never run `lake build` or an unfiltered cache get. Run Python as `python3 -I`.
  - Insert helper modules before their consumers.
- **Sweep.**
  - Recheck the owned module, then sweep the supplied order with 0 errors.
  - Compare the `sorry` warnings with `base-sorries.txt` (31 declarations in 14 modules). The only change
    must be the removal of `composeP_efficient`, `composeV_efficient` and `hbcSecure_compose`.
- **Axioms.**
  - Print the axioms of `composeP_efficient`, `composeV_efficient` and `hbcSecure_compose`. Expect only `propext`, `Classical.choice` and `Quot.sound`.
  - Print them for every stored constant of the changed and new files.
- **Rule 10 evidence.**
  - Run whole-file seals A and B of every changed or new file over its full TCSlib import closure, at base and
    final.
  - Run both the **strict** and the **coe** variant (projection coercions sealed, or treated as notation).
    Report every failing declaration in each.
  - Add paired controls that pass unsealed and fail sealed, each sealed negative failing exactly once.
  - Run the explicit-unfold scan.
  - Report the seals with `PolyExpr.eval` both excluded as notation and sealed.
  - **Error counts (G26-N1).** Your runner must count both diagnostic forms, `error:` and `error(…)`, for
    example with `^\S+\.lean:\d+:\d+: error[:(]`. Keep every raw log.
- **Lint.**
  - Run `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b` at base and at final.
  - The baseline at the issue base is **92 FAIL / 101 WARN** (after #305).
  - Diff the line sets, not only the counts. There must be no new FAIL line, and no new WARN line except one you
    disclose and justify.
- **Report.** `REPORT.md` gives:
  - the base and the status of each target;
  - the changed files and the sketch edits;
  - the new declarations;
  - **Overlap and reuse**;
  - **Scope requests** (none, or each with Seyoon's answer);
  - the promotion and reader requests;
  - the evidence, with its manifest.

### Evidence completeness

Gate 20 held a delivery for omitted raw evidence (G20-01).
- Every file that `evidence/SHA256SUMS` names must be delivered. That includes:
  - seal and control sources, manifests and request records;
  - every raw log and `results.jsonl`;
  - the probe sources and the tools used.
- If the evidence is too large for one commit, deliver it in several commits, or as numbered ZIP parts, each part
  with an entry list. Do not leave anything out for size.
- Check before delivery that the delivered paths are exactly the manifest's.

The maintainer checks `TCSlib` and `audits/pass-shelat/Checks` on the full-library tree at landing.

**Ready to dispatch**

## ===== briefs/pass-shelat-ch5-8/duplication-ledger.md =====

# Duplication ledger: Pass–shelat ch. 5–8

Accepted debt, each entry acknowledged by the user, with its scheduled resolution.

| ID | New declaration (where) | Existing copy (where) | Status | Resolution |
|---|---|---|---|---|
| DL-1 | `TCSlib.InformationTheory.abs_probTrue_sub_le_statDist` (#183, `InformationTheory/Extractors.lean`, for `main`) | `TCSlib.Cryptography.abs_sum_sub_le_statDist` (`Foundations/Experiments.lean`, Garg's concrete layer, on `cryptography/pass-shelat-ch2-4` and `cryptography/garg-ch1-3`; not on `main`) | accepted 2026-11-04 (user) | No copy on `main` today. When the concrete layer lands on `main`, its lemma becomes a one-line corollary of #183's (a `Finset` test is the `Bool` test `(· ∈ T)`) or is removed. Gate 01 pack erratum E1. |

## Inherited with ch. 2–4 (found 2026-11-05; acknowledged 2026-11-05 by the user: clean up now)

This campaign owns ch. 2–4 since 2026-11-05 (plan, decision log). These duplicates predate it.

| ID | Copies (where) | Status | Proposed resolution |
|---|---|---|---|
| DL-2 | XOR of encodings is the encoding of the Boolean sum, `zipWith xor (ofFn a) (ofFn b) = ofFn (a + b)`, stated three times: `TCSlib.Cryptography.zipWith_xor_ofFn_add` (`Asymptotic/HardCoreLoops.lean`; it was `zipWith_xor_ofFn`, renamed by the base repair to end the name clash with `Encryption.lean`'s different lemma); `TCSlib.Cryptography.zipWith_xor_ofFn_eq_add` (`Asymptotic/MultiMessage.lean`); `TCSlib.Cryptography.MultiMsg.zipWith_xor_ofFn_eq_add` (`Asymptotic/MultiMessageLemmas.lean`) | accepted; scheduled now | Keep the most upstream copy (`HardCoreLoops`) and point the other two at it, in a ch. 2–4 cleanup PR. |
| DL-3 | `pairEncode a b ≠ []`, stated four times: `GGMRed.pairEncode_ne_nil` (`Asymptotic/GGMReduction.lean`), `GI.pairEncode_ne_nil` (`ZeroKnowledge/GraphIsomorphism/Proofs.lean`), `ColMachines.pairEncode_ne_nil` (`ZeroKnowledge/ThreeColoring/Machines.lean`); and, on `main`, `Complexity.pairEncode_ne_nil` (`Complexity/SpaceComplexity/Logspace/InputAccess.lean`), the copy that made the merge's ambiguity | accepted; scheduled now | `main` is merged (#186). Remove the three local copies in favour of `Complexity.pairEncode_ne_nil`, in the same cleanup PR. |
| DL-4 | Not a copy (different carriers): the sampler-based `StatClose` (`Asymptotic/Sampling.lean`) and `main`'s `EpsClose` on `FinDist` (`InformationTheory/Extractors.lean`, #183) | accepted; scheduled now | A bridge lemma, in the same cleanup PR (user, 2026-11-05). |
| DL-5 | Not a copy (different carriers; found by the gate 02 round 2 review): `Games.guessAdv_eq_half_advantage` and `Games.accept_guessGame` (games) and the concrete layer's `predict_eq` (`Asymptotic/Ensembles.lean`, on `uprob` over seed spaces), both the identity behind [PS10, Lemma 73.8] | disclosed in the docstring (gate 02 closing commit) | Derive one from the other through bridge B2 when ch. 2–4 lands on `main`. |

## Found in the ch. 5–8 statement phase (2026-11-05)

| # | Statement | Copies | Status | Resolution |
|---|---|---|---|---|
| DL-6 | Coin-tape slices `(r.drop (j * c)).take c` in global/GI-shadow graph isomorphism, Lamport and sequential ZK, alongside the former BlockEncryptor home | historical duplicates found by the Lamport worker/maintainer | **Implemented at `e9d64158461bfe24ddc88ab885bc4017899b4c16`; final source `3f6db40e1688c4a0bb922c9575dd3bd2157a650b` is checked in draft PR #232. Native and layered Rule10 reconciliation identify zero new/touched reads; all older failures remain recorded. External gates and landing pending.** | One `TCSlib.Cryptography.coinBlock`, `coinBlock_eq` and `length_coinBlock` live in `Asymptotic/Adversary.lean`. The BlockEncryptor definition moved upstream; global/shadow `coinSlice` and sequential ZK's `phaseSlice`/unused length lemma are retired. Lamport already used the public BlockEncryptor `coinBlock`; its length lemma moved upstream. Consumers use the shared name and published reader. |
| DL-7 | Equal-length padding: Lamport's `ofFn_padFin_of_length`, and the inline step in `Composability.length_eval_of_length` (`CCA2Scheme.lean`) | General equation `Collection.ofFn_padFin_of_le` in **`Asymptotic/CollectionsHelpers.lean`**, not `Collections.lean` | **Implemented at `e9d64158461bfe24ddc88ab885bc4017899b4c16`; final source `3f6db40e1688c4a0bb922c9575dd3bd2157a650b` is checked in draft PR #232. Native and layered Rule10 reconciliation identify zero new/touched reads; all older failures remain recorded. External gates and landing pending.** | Lamport's duplicate theorem is deleted. Its uses and CCA2's two padding steps use the general equation, whose conclusion is `List.ofFn (padFin ℓ w) = w ++ List.replicate (ℓ - w.length) false`; at `w.length = ℓ`, simplify `Nat.sub_self`, `List.replicate_zero` and `List.append_nil`. |
| DL-8 | `SecureComputation.PRFOut ℓ₂` (prong B, `SpecialEncryptionSecurity.lean`): ch. 2–4's `PRF` with `ℓ₂(n)`-bit outputs; `PRF` is its case `ℓ₂ = n` | resolved 2026-11-05 | `prfOut_var_iff : PRFOut .var F ↔ PRF F` proved beside `PRFOut` (prong B). The ch. 2–4 layer is unchanged. |


## Found by gate 03 (2026-11-05; rulings G3-5 and R-03l-1: clean up in the gate 03 clean-up PR, after #195)

Most copies trace to helpers that are `private` in pack 03a's and 03l's files. The clean-up makes
one copy public in the most upstream file and re-points the rest.

| Id | Copies | Status | Payback |
|---|---|---|---|
| DL-9 | The coin-block bijection `blocks` (`Fin (m · c) → Bool ≃ Fin m → Fin c → Bool`) and its lemmas, copies and an inverse: `FunFamily.blocks`, `OneWayYao.blocksE`, `blocksEquiv`, `blocksEquivX`, `EnsembleLemmas.blocks`, `SoundnessRep.blocksEquiv`, and `Ensemble.blocks` (private, `Asymptotic/Ensembles.lean`, which calls itself a copy of `FunFamily.blocks`; added on gate 03a round 2, R2-4); with S2b's public duplicate `take_drop_ofFn_blocks` of `EnsembleLemmas.take_drop_ofFn_blocks` (gate 04 N4) | accepted; scheduled (G3-5) | One `FunFamily.blocks` in a low file; re-point 03h, 03i, 03k's statements, `Ensembles.lean` (03a) and S2b's copy. |
| DL-10 | `ptc_comp` (composition of polynomial-time functions in a convenient form), six private or public copies (`Closure`/`Repetition` helpers, `Universal*`, `ThreeColoring/Machines`, …) | accepted; scheduled (G3-5) | Public once in 03a's `Closure.lean`; delete the copies. |
| DL-11 | The state loop `stateFind` (private in `Repetition.lean`) and its copies `GI.stateFind`, `EncodingMachines.polyTimeComputable_stateFind`, `GGMRed.stateLoopFun`, and the variant `stateIterate` | accepted; **half done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (`polyTimeComputable_stateFind` public, prose fixed); the copies are re-pointed in clean-up part 2 | `polyTimeComputable_stateFind` public in `Repetition.lean`; re-point; update the prose that calls it private (`StringLoops.lean:36–38`, `HardCoreLoops.lean:68`). |
| DL-12 | `abs_uexp_sub_le`, two copies (`PublicKeyLemmas` and a private one) | accepted; scheduled (G3-5) | One public copy. |
| DL-13 | `negligible_zero` (`Foundations/Negligible.lean` since G3-7a) and `negligible_const_zero` (`ZeroKnowledge/Defs.lean`) | accepted; scheduled (G3-5) | Delete `negligible_const_zero` (2 uses). |
| DL-14 | `forall_of_uprob_eq_one`, two copies | accepted; scheduled (G3-5) | One public copy. |
| DL-15 | `decodeFin_eq_some_iff`, a private copy in `Collections.lean` and a public one in `GGMReductionEval.lean` (`GGMRed.decodeFin_eq_some_iff`; making the `Collections.lean` copy public must avoid the namespace clash, gate 03b review #12c), and the new forward lemma `ofFn_of_decodeFin_eq_some` (`CollectionsHelpers.lean`, #198); S2b's private `eq_ofFn_of_decodeFin` | accepted; scheduled (G3-5) | One public `decodeFin_eq_some_iff` in `Asymptotic/Adversary.lean`; the forward lemma derived from it. |
| DL-16 | `IterateFindHost` (03l) copies 26 declarations of `main`'s private module layer in `Complexity/ClassNP/SAT.lean` (ten now public); the new host is missing from the policy's host registry (§14) | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)**: one public host `Turing.ModuleHost` (`TuringMachine/Build/ModuleHost.lean`), consumed by `SAT.lean` and `IterateFindHost.lean`; registry row H14 | Make `SAT.lean`'s layer public on the ch. 2–4 branch and re-point `IterateFindHost`; register the host. |
| DL-17 | `StateLoop` (03l) restates five `main` lemmas, plus `tail_poly` and `xor_poly` (arrived with the `main` merge, #186) | accepted; scheduled (R-03l-1) | Use `main`'s lemmas. |
| DL-18 | `UnaryMul` (03l) privately copies `PairSplit`'s parser | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (`Turing.PairParse` in `PairSplit.lean`) | Use `PairSplit`'s. |
| DL-19 | Not a copy yet: a latent name clash between `StateLoop.BlockLoop` and `main`'s `Complexity.BlockLoop` (nothing uses it) | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (renamed `StateLoop.BlockMapLoop`) | Rename or merge in the same PR. |
| DL-20 | `main`'s `TuringMachine/Build/Loop.lean` keeps a private `loop_first_halt`, the same lemma as the new public `Turing.ModuleHost.first_halt` (found by #203's worker). `Loop.lean` is upstream of the host, so it cannot consume it | noted | Move `first_halt` and `live_prefix` down into `Loop.lean` (or the machine core) at the `main` landing, and have `Loop.lean` use them. |
| DL-21 | Elementary number theory that Mathlib already has (audit `mathlib-overlap-nt.md`, 2026-11-06, Mathlib pin `029db123`): 6 DUP (`QR` = `(powMonoidHom 2).range`, `crtUnits` (keep as alias, `rfl`), `coprime_of_ne` = `(Nat.coprime_primes hp hq).2`, `powOneSubgroup` = `(powMonoidHom m).ker`, `rsaPerm` ≈ `powCoprime` (optional), `IsGenerator` ≈ `∀ x, x ∈ zpowers g`) and 9 WRAP (shorter proofs from Mathlib: `units_val_mem`, `pow_mod_totient_modEq`, `units_pow_eq_one_iff`, `two_mul_card_le_of_ne_top`, `card_units_eq_mul_card_QR`, `card_QR_prime`, `sq_pow_div_four_succ`, `fmultNat_eq_mul_prime`; and the core of the sorried `elGamal_correct`) | accepted; scheduled (user direction 2026-11-06: Mathlib first) | Replace by Mathlib's (alias where a name is load-bearing), clean-up part 2 item M; rows in fill-owned files (`Candidates/*`) after those fills land, as landing edits. The fill briefs cite the report's Mathlib names. |
| DL-22 | TCSlib's Chebyshev lower bound (`NumberTheory/Chebyshev.lean`) and Korselt-type facts are in newer Mathlib (`Chebyshev.pi_ge`, `theta_ge`, `psi_ge`; `Nat.isCarmichael_iff_korselt`; master `94f43000`, Lean v4.36.0-rc2), not at our pin | noted | Replace at the next Mathlib bump (repository-wide, `main`'s pin). At the same bump, the hypothesis `BlumDensity` (`Rabin.lean`) can be discharged in its eventual form (`n ≥ n₀`): apply `WienerIkehara.tendsto_sum_range_div` (master only) to `vonMangoldt.residueClass 3` mod 4, with the continuation `vonMangoldt.continuousOn_LFunctionResidueClassAux` (already at our pin) and Chebyshev's `ψ(x) ≪ x` (master), to get `ψ(x; 4, 3) ~ x/2`; then `θ ≥ ψ − (ψ − θ)` (`Chebyshev.psi_sub_theta_le_mul_sqrt`) and `π(x; 4, 3) ≥ θ(x; 4, 3)/log x`. This changes the Rabin statements that take `BlumDensity` (they would take nothing, or `n ≥ n₀`); a statement gate then. |
| DL-23 | fac fill (`Candidates/Factoring.lean`, delivery review 2026-11-07): private near-copies of public lemmas: `fac_chunkEquiv` = `FunFamily.blocks`; `fac_arrowCongr` = `finCastEquiv`; `fac_ofFn_halves` repeats a private `OneWay` lemma (half is `ofFn_block_eq_take_drop`); `fac_listToNat_inj` repeats a private `Sampling` lemma; plus the REPORT's three near-duplicates and small numeral facts re-proved across the fac, rsa and dl-a fills | noted | Clean-up part 2: re-point to the public lemmas; publish the two private ones beside their files and share the numeral facts. |
| DL-24 | col-b fill (delivery review 2026-11-07): `ColZK.acceptProb_seed_to_coins` = `acceptProb_bind` reversed and `ColZK.findSome?_map_option` = core `List.map_findSome?` (removed by landing edits E3–E4); a third copy of `pushesUniform_restrict` across fill units (dl-a has one); `table_index_*` vs `finProdFinEquiv`; `polyTimeComputable_next` repeats `reply_poly`'s proof (review finding 6 has the full list) | E3–E4 at landing; rest noted | Clean-up part 2: publish one `pushesUniform_restrict`, re-point the rest. |
| DL-25 | dl-b fill (`DiscreteLogHardcore.lean`, delivery review 2026-11-07): `dlb_statClose_pi` copies the public `OneWay.statClose_pi` (removed by landing edit E1); `dlb_stateIterate_poly` (from `HardCoreLoops`), `dlb_count_ofFn` (from `HardCoreGL`; relative of `List.count_ofFn`), the `listToNat` fold lemmas, `two_pow_size_le` (dl-a and 3-col have inline `2^size m ≤ 2m` bounds), `pushesUniform_castLE` copies (review D1) | E1 at landing; rest noted | Clean-up part 2: publish one copy of each beside its source; missing equations `HardcoreBit.majority_eq` (`PairwiseIndependence.lean`) and `expSampler_coins` (`DiscreteLog.lean`) at the next shared-file window. |
| DL-26 | col-a fill (delivery review 2026-11-07): `colRep_xor_poly` = `StateLoop.xor_poly`, `eq_of_xor_eq_false` = core `bne_eq_false_iff_eq`, `pushesUniform_blockRead` rebuilds `FunFamily.blocks` (removed by landing edits E2–E4); `ColRep.exec_four_mul`'s step repeats `GI.exec_repViews`'s proof (promote `exec_four_mul`, request R-3); cross-unit near-copies with col-b's `ColZK.pushesUniform_offsetTable`, `ColZK.ofFn_drop_take` | E2–E4 at landing; rest noted | Clean-up part 2: promote `exec_four_mul`, share the col-a/col-b helpers; requests R-2 (`(decGraph x).1` equation), R-5 endorsed. Base reading for #210's next round: `R3COL_witnessRelation`'s `bounded` clause destructures `R3COL` instead of using `R3COL_iff`. |
| DL-27 | rsa fill (delivery review 2026-11-07): 151 lines copied verbatim from dl-a's private helpers (`dla_findSome?_ite`, `dla_find?_range_lt`, `dla_listToNat_append`, `dla_drop_natToList_zero_append`, `dla_ss*`); `rsa_appendEquiv` = Mathlib `Fin.appendEquiv` (landing edit E1); `rsa_comp`/`ptc_congr` copies of the private `ptc_comp` family; loop lemmas descend from Primality's private `spStep`; near-copies of `findSome?_eq_bind_find?`, `find?_range_eq_map_find?_finRange`; parallels with fac (`fac_natToList_mod`, `fac_pairDec`) | E1 at landing; shared-lemma PR planned | **Landing order:** (1) dl-a lands; (2) a shared-lemma PR publishes `PolyTimeComputable.comp'`/`.congr` (`PolyTime.lean`), `IterateFind.find?_range_and_lt` (`IterateFind.lean`), nine `listToNat`/`natToList` lemmas (`Arithmetic.lean`), `rejectBlocksL_eq_find?` (`Concrete.lean`), removing dl-a's copies; (3) rsa lands with E1–E3 and E4 (cites them; checked against stubs); (4) a statement-gated `polyTimeComputable_rejectBlocksL` retires the copied loops in dl-a, rsa, rabin (and dl-c, pending its review). |
| DL-28 | dl-c fill (delivery review 2026-11-07): near-verbatim copies of the trial loop and numeral helpers shared with dl-a and rsa (and dl-b's own modular-numeral layer); `dlc_abs_uexp_sub_le` duplicates `Sampling.lean`'s private lemma and its public copy in `PublicKeyLemmas.lean` (review D1) | noted | Folds into DL-27's shared-lemma PR. The review's D2 homes: generic `polyTimeComputable_rejectBlocksL` (`Concrete.lean`), `listToNat` lemmas, width lemmas (`Arithmetic.lean`), `find?_range` (`Repetition.lean`), `PolyTimeComputable.congr` (`PolyTime.lean`), `abs_uexp_sub_le` public in `Sampling.lean`, `finCastEquiv` to `CollectionsHelpers.lean`. Reconcile with DL-27's homes when that PR is drafted. |
| DL-29 | rabin fill (delivery review 2026-11-07): `rabin_appendEquiv` = Mathlib `Fin.appendEquiv` and `rabin_pushesUniform_prod` (re-proved from `PushesUniform.prodMap`) handled by landing edits E1–E2; undisclosed copies: `rabin_statClose_one` = dl-a's `dla_statClose_one`; `rabin_listToNat_mulStr`, `rabin_prime_poly` copy rsa helpers; `rabin_rS`/`_rQ`/`_rTest` ≈ rsa's `rsa_fS`/`_fQ`/`_fTest`; the block loop is a fourth copy (with dl-a, rsa, dl-c `dlc_ss*`); `rabin_drop_zeros_append`'s step = fac's `fac_natToList_mod` | E1–E2 at landing; rest noted | Folds into DL-27/DL-28's shared-lemma PR and the `polyTimeComputable_rejectBlocksL` host PR. Base reads `rabinCollection_index`, `rabinBlumTrapdoor_index` (through `show`; re-point via `Collection.index_eq`) go to clean-up part 2's (b) list. |
| DL-30 | padded-cpa fill (delivery review 2026-11-11): generic `ProbComp` facts published in a public-key helper as `Composability.ChallengeSim.expect_sample_equiv`, `expect_sample_comm`, `expect_sample_unique`, `expect_sub` (`PublicKey/OracleSecurity/ChallengeSim.lean`); `expect_sample_prod` repeated `Bridge.expect_sample_pair`'s proof. | `ChallengeSim.lean` only | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | Landing edit re-proved `expect_sample_prod` from `Bridge.expect_sample_pair`. Promote the four lemmas to `ProbComp` in `Games/Probability.lean` and re-point their uses. |
| DL-31 | `ofFn_padFin_of_length` (`List.ofFn (padFin d w) = w` when `w.length = d`): `GGMRed.ofFn_padFin_of_length` (`GGM/Run.lean`), copy in `Asymptotic/HardCoreGLColl.lean`, private copy in `ElGamal.lean`; padded-cpa's `RecordHandler.lean` uses the GGM one through a transitive import. | 3 | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | Promote one public lemma beside `padFin` in `Asymptotic/Adversary.lean`; re-point all uses and delete the copies. |
| DL-32 | `List.ofFn (cast h f) = List.ofFn f` for a width equality: public `Composability.AdaptiveCPA.ofFn_cast` (`PublicKey/AdaptiveCPA/Games.lean`) and private `cca2OfFn_cast` (`PrivateKey/OracleFromPRF.lean`, #289). adaptive-cpa review also lists for promotion: `expect_sample_update` (→ `Games/Probability.lean`, with DL-30), `simulate_eq_of_abs` and the `castImpl` family (→ `Games/Simulate.lean`), `padFin_ofFn_zeroBits`, `headD_ofFn_one`, `ofFn_splitHalf_fst/_snd`; reader request `indCodec_eq_bitCodec`; new uses of `GGMRed.ofFn_padFin_of_length` join DL-31. | 2 (+ candidates) | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | Promote one generic `ofFn_cast` beside `padFin`/`BitCodec`; re-point both; promote the listed generic lemmas. |
| DL-33 | bitwise-cpa fill (delivery review 2026-11-11): `BitwiseSim.expect_sample_update` vs `AdaptiveCPA.expect_sample_update` (two forms, same name); generic `BitwiseSim.expect_simulate_eager` and public near-copy `BitwiseSim.expect_simulate_indImpl_cpa` of the private lemma in `PublicKey/OracleSecurity.lean`; `chRun_toCompOn_transport_list` generalizes `ChallengeSim.chRun_toCompOn_transport`; `BitwiseSim.headD_drop` = public `CommitmentLemmas.headD_drop` (and private `headD_drop_ofFn` in `Pseudorandom/NextBit.lean`); `flatten_ofFn_singleton` = private `flatten_ofFn_one` (`Yao.lean`); `decodeFin_nil_getD` (→ `Games/BitCodec`); `padded_enc_runAt/_coins` (→ beside the padded readers); `qDin/qDout` third copy of the two-oracle length vector (`recDin/recDout`, `acDin/acDout`); private `ofFn_half`, `bitwise_runAtL` re-prove published facts; reader request `HybridMachine.hybridPre_eq`. | several | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | One consolidation PR with DL-30–DL-32: promote to `Games/Probability`, `Games/Simulate`, `ChallengeSim`, `BitCodec`, a shared list module; re-point and delete copies. |
| DL-34 | pk-cpa-cca1 fill (delivery review 2026-11-12): `OracleFromPRF/Handler.lean` copies private AdaptiveCPA handler pieces (`ofFn_padFin_eq_padL`, round-input readers `rU`…`rCnt`, `impl_of_ret`, `replicate_one`); public `ofFn_pkTapes` re-proves `AdaptiveCPA.ofFn_acTapes` (a generic `⟦blocks q ℓ ω j⟧ = (⟦ω⟧.drop (j·ℓ)).take ℓ` belongs beside `FunFamily.blocks`, input-layout readers beside `InteractiveHandler.input`); private-key `indCodec_eq_bitCodec` (DL-32 reader request); `mem_keys_of_lookup_isSome` (core `List.lookup_isSome_iff`); promotion candidates `simulate_eq_of_abs_bounded` (generalizes `AdaptiveCPA.simulate_eq_of_abs`), `expect_simulate_congr` (→ `Games/Simulate`), `abs_expect_sub_le` (→ `Games/Probability`), `prob_bad_le`, `expect_sample_mem_le` (→ `Games/Hopping`), `padFin_nil`, `padFin_replicate_false`, `ofFn_arrowCongr_finCongr` (→ beside `padFin`), `zipWith_xor_cancel_left`, `xorPerm` (shared list/vector module); owned-file private overlaps with the `cca2*` helpers. | several | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | Fold into the DL-30–DL-34 consolidation PR. |
| DL-35 | Found while staging the consolidation (2026-11-12): public `blocks` in `Asymptotic/EnsemblesLemmas.lean` and private `blocks` in `Asymptotic/Ensembles.lean`, both the equivalence `(Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool)` of `FunFamily.blocks` (`Asymptotic/Adversary.lean`). | 2 | Open (ch. 2–4 inherited) | Re-point to `FunFamily.blocks` in a later ch. 2–4 cleanup; out of scope for `dl-consolidation`. |
| DL-36 | nm-cca2 fill (delivery review 2026-11-12): `NMCCA2.logEmit` (`PublicKey/NonMalleability/Indistinguishability/Forward.lean`) generalizes `Games.EffFill.relabelN`/`relabel` (`Games/Efficiency/OracleBridge.lean`), and its log facts `logEmit_encodeLog`, `iterate_pairSndD_encodeLog`, `flatMap_range_drop`, `length_le_length_encodeLog`, `length_iterate_pairSndD_le`, `polyTimeComputable_logEmit` mirror `relabelN_encodeHist`, `length_le_length_encodeHist` and the orbit bound of `bridgePre_poly` (undisclosed); public `finU`, `finZ`, `finW`, `finA`, `finL`, `fields_finInput` are the DL-34 round-input readers (`rU`…`rL`) again; `ofFn_nthCt` (owned file) is DL-34's generic block fact (`ofFn_acTapes`, `ofFn_pkTapes`); the private readers `rState`…`rAns` (disclosed). Promotion requests: `fwdHandler`/`fwdHandler_impl`, `exists_withAdviceOn` (→ `Games/Efficiency`), `cntRead`/`ansRead` (→ `BitCodec`), `indImpl_eq_of_msgLen_eq_zero` (→ `PublicKey/OracleSecurity`, after that file is split: it is at 999 lines). | several | **Paid** ([#299](https://github.com/Shilun-Allan-Li/tcslib/pull/299), merge `eff2dcd0`, 2026-11-14; Gate 21) | After the DL-30–DL-34 consolidation lands: put `logEmit` beside `relabelN` with `relabel x = logEmit relabelEmit x`; re-point `dCnt`/`dCt`/`dIn`/`dFin`/`eBit`/`eMsg`/`eTape`/`eCt` to R6's readers and delete `finU`…`fields_finInput`; derive `ofFn_nthCt` from the generic block lemma; promote the accepted requests. |
| DL-37 | nm-sim fill (delivery review 2026-11-13; **undisclosed**, accepted as debt by Seyoon 2026-11-13): `NMSim.chunkAt`/`chunkAt_eq`/`length_chunkAt` (`PublicKey/NonMalleability/Simulation/Hybrid.lean`) and the block lemmas `ofFn_block`, `chunkAt_flatten_append`, `map_chunkAt_flatten`; private `padFin_replicate_false` (`Simulation/Challenge.lean`); `Rounds.impl_of_ret`, `rdU`…`rdLog`/`rdState`, `rdAns`, `Simulator.finSt` (`Simulation/Rounds.lean`, `Simulator.lean`); also generic neighbours `expect_eq_until_bad`, `NMSim.expect_simulate_eager`, `expect_congr_of_allOutputs`, `chunkMap`; disclosed: `flatMap_range_drop`, `ofFn_padFin_eq_padL`, `polyTimeComputable_guessBit`, `ofFn_eq_map_range` | `coinBlock`/`coinBlock_eq`/`length_coinBlock` (`Asymptotic/Adversary.lean`), `OneWayLemmas.ofFn_block_eq_take_drop`, `NMCCA2.ofFn_nthCt`, Lamport `coinBlock_flatten`; `PRFGame.padFin_replicate_false` (`OracleFromPRF/Transfer.lean`; → `Games.padFin_replicate_false` in the consolidation); DL-34 private `impl_of_ret` (`AdaptiveCPA/Handler.lean`, `PRFGame`) and readers `rU`…`rL`/`rS`; `Games.prob_eq_until_bad`, `BitwiseSim.expect_simulate_eager`, `ProbComp.expect_mono_of_allOutputs`, `relabelN`/`logEmit` (DL-36); ZK `ofFn_eq_map_range` ×2; A4 `EnsembleLemmas.ofFn_padFin_eq_padL`; `rFwd`/`rY`/Forward `rAns` | **Paid** ([#299](https://github.com/Shilun-Allan-Li/tcslib/pull/299), merge `eff2dcd0`, 2026-11-14; Gate 21) | Landing of the consolidation (after nm-sim): delete the private `padFin_replicate_false` and use `Games.padFin_replicate_false`; re-point the nm-sim files to the moved names. Post-consolidation fold window, with DL-36: fold `chunkAt` onto `coinBlock` (58 uses) and place the block lemmas beside it; re-point `rdU`…`rdLog`, `rdState`, `finSt` to `InteractiveHandler.rU`…`rS` and `impl_of_ret` to `InteractiveHandler.impl_of_ret`; derive `prob_eq_until_bad` and `ChallengeSim.expect_simulate_eager` from the general nm-sim forms; one iterate-and-emit definition for `relabelN`/`logEmit`/`chunkMap`; merge the three `ofFn_eq_map_range` into `Foundations/BitLists`; make `NMSim.ofFn_padFin_eq_padL` the A4 lemma; fold `rdAns` with the `rFwd`/`rY`/`rAns` readers; promote the accepted requests (review r1 table). |
| DL-38 | dl-folds fill (worker REPORT §0.6, disclosed; delivery review 2026-11-14): inline re-proofs of `impl_of_query` (`acHandler_impl_forward`) and of a returning finalization (`pkHandler_finish`, `acHandler_finish`); a local `have` equal to `polyTimeComputable_ansRead` (`OracleFromPRF.lean`); further block-window restatements (`Primality.ofFn_chunk`, `ColRep.drop_take_ofFn_blockRead`, `Factoring.fac_ofFn_halves`, already corollaries); other iterate-and-emit loops (`BlockEncryptor`, `EnsembleLemmas.CopiesLoop`, `StretchMachine`, `CommitmentLemmas.ComLoop`, ZK `EncodingMachines`); the ZK pair `GI.iterate_pairSndD_encodeMsgs` / `ColMachines.iterate_pairSndD_encodeMsgs`; and the B3 `blocks` aliases (`EnsembleLemmas.blocks` and its lemmas, private `Ensembles.blocks`), escalated. | `InteractiveHandler.impl_of_query`, `finish_of_ret`; `Games.polyTimeComputable_ansRead`; `FunFamily.ofFn_blocks`; `Games.iterEmit`; `FunFamily.blocks` | Open (deferred) | Opportunistic: fold each when its file is next touched. The B3 aliases need a gate-approved restatement of `exists_copiesRed`, `ofFn_blocks_symm`, `take_drop_ofFn_blocks`, `ComLoop.emit_init_of_lt` and of the bodies of `PRFGame.pkTapes`, `Ensemble.copies` (all definitionally equal). Complexity copies of `ofFn_eq_map_range` and `flatMap_range_drop` are another campaign's. |
| DL-39 | ext-nosrc fill (worker request and delivery review 2026-11-14, disclosed): `Randomness.Rejection.tupleEquiv` restates Mathlib's `(Fin.consEquiv _).symm`; generic `FinDist` facts local to `Randomness/Extraction/Rejection.lean` (`sum_map`, `expect_map`, `probTrue_map`, `probTrue_le_one`, `probTrue_nonneg`, `map_map`, `map_prod_snd`, `uniform_prod`, `map_uniform_equiv`, `mixture`, `mixture_isSource`, `uniform_probTrue`); no exact duplicate in TCSlib (nearest: `SamplingFinDist.uprob_comp_eq_probTrue_map`, `Experiments.uprob_comp_eq_sum_map`, `ProbComp.expect_map`). | Mathlib `Fin.consEquiv`; `InformationTheory/FinDist` (to be added) | Open (deferred) | Promote the `FinDist` facts to `InformationTheory/FinDist` and use `Fin.consEquiv` in a later job (`FinDist` was frozen for the fill). The authoritative full promotion list (also `map_apply_expect`, `branch_apply`, the uniform-machine family, `take_poly`) is the delivery's `evidence/promotion-requests.md`, `rejection-review.md`, `sampler-review.md` (exchange `a5da5cc3`, `inbox/fills/ext-nosrc/`; Gate 22 observation). |
| DL-40 | cca2-ett fill (delivery review 2026-11-14): undisclosed `ETTGame.eval_toOracleAdversary_len` (`EncryptThenTag/Machines.lean`) generalizes public `PRFGame.eval_toOracleAdversary_width` (`OracleFromPRF/Reduction.lean`, its `ℓ = n` case); disclosed `ETTGame.zipWith_xor_cancel` = four private `zipWith_xor_xor_self` copies (`FromPRF`, `FromPRG`, `SpecialEncryption`, owned `zipWith_xor_xor_self'`; public relative `zipWith_xor_cancel_left`, other orientation); Gate 23 (G23-01, Seyoon 2026-11-14: debt now, fold in cleanup): private `length_le_length_encodeLog` (`EncryptThenTag/Machines.lean`) = the private copy in `NonMalleability/Indistinguishability/Forward.lean:108`; `ETTGame.prfAdv_eq_expect` re-derives private `prfAdv_prfReduction` (public relative `prfAdv_eq`, uprob form); generic forms `ETTGame.tapeImpl`/`simulate_tapeImpl_congr`/`expect_simulate_tapeImpl` (AdaptiveCPA), `recBits` family and `ovr` (PRFGame), `expect_simulate_abs` (`Games.simulate_eq_of_abs_bounded`), private `abs_expect_sub_le_expect` (`ProbComp.abs_expect_sub_le`). | `Foundations/BitLists`, `Pseudorandom/Functions`, `Games/*`, the general ETT forms | Open (deferred) | Promote the general forms (worker requested most) and re-derive the specialised copies from them; fold the private XOR copies; publish `length_le_length_encodeLog` in `Games/Efficiency/Strings.lean` beside `length_encodeLog_le` and delete both private copies (cleanup job). |
| DL-41 | dl-crh fill (delivery review 2026-11-14): **undisclosed** `FromDiscreteLog.inputWord_split` restates `ofFn_eq_init_append` (`Asymptotic/ReductionSupport.lean`, up to `Fin.init`); `ofFn_splitBits_fst/_snd` restate `ofFn_splitCoins_fst/_snd` (`CollectionsHelpers.lean`; `Authentication.splitBits` = `splitCoins`); disclosed re-derivations from public readers of private `dlb_expo_val`, `fac_listToNat_inj`, `ofFn_splitCoins_symm_cast`, `dla_statClose_expDec`; near relatives `residueFinEquiv` (Mathlib `ZMod.finEquiv`), `boundedInputEquiv` (`Fin.snocEquiv`), `expect_sample_eq_uexp` (`Games.Bridge.prob_sample_eq_uprob`). | `ofFn_eq_init_append`, `ofFn_splitCoins_*`, a `splitBits = splitCoins` bridge; worker promotion list `evidence/PROMOTION.md` (exchange `9ad236d1`) | Open (deferred) | `inputWord_take` (Gate 24 G24-01) and `inputWord_split` re-pointed to `take_ofFn_castLE` / `ofFn_eq_init_append` by LE-reuse `d356381a` (#307); the rest: re-point and promote in a later job. |
| DL-42 | hash-sign fill (delivery review 2026-11-14): `HashSignForward.roundWord`/`handler` repeats the `Games/Forwarding` `fwdRun`/`fwdHandler` pattern with a hashed query and different widths (disclosed); `splitBits_pad_concat` is a corollary of `Games.padFin_append_split`; `expect_simulate_sample_once` near `Games.expect_simulate_eager`; `MachineCodec.ext_of_fields`, `forgerCodec_eq_bitCodec`, `eq_pure_of_cost_zero` overlap the parallel lamport delivery's `lamport_codec_ext`, `lamport_forgerCodec`, `exists_pure_of_cost_zero`. | `Games/Forwarding` (a query-map `fwdHandler`), `Games/BitCodec`, `Games/Hopping`, `Games/Machines` | Open (deferred) | Generalize `fwdHandler`; promote the codec/cost facts to `Games/Machines` (no attribute) and fold the lamport copies once both units have landed. |
| DL-43 | lamport fill (delivery review 2026-11-14): **undisclosed** `LamportFill.signatureBlock σ i` = `FunFamily.blocks n n σ i` (via `blocks_apply`; DL-9 class); near relatives `Blocks.flatten_ofFn_update` (`CommitmentLemmas.ofFn_update_eq`), `Averaging.expect_favourable_of_success` (`ProbComp` counterpart of `HardcoreBit.uprob_mul_le_uexp`). Overlaps with hash-sign are DL-42. Also the follow-up (Seyoon, 2026-11-14): restate the frozen `lamport_oneTimeSecure` hypothesis `f` over `Fin (var.eval n)` with a published reader, clearing its 16 seal-B failures. | `FunFamily.blocks`; `CommitmentLemmas`; `HardcoreBit` | Open (deferred) | Re-point `signatureBlock`; promote the averaging lemma; the frozen-statement restatement needs its own gate. |
| DL-44 | prf-mac fill (delivery review 2026-11-15): F-01 local `hadv` in `MAC/FromPRF/Bound.lean` re-proves public `ETTGame.prfAdv_eq_expect` (**ruling Seyoon 2026-11-15: promote now** to the PRF layer beside `prfAdv`, re-derive the ETT copy proof-only, re-point prf-mac); F-02 `decide_fnForge`'s `hw`/`htake`/`hdrop` restate list readings of `splitBits` (`take_ofFn_castLE`, `CollectionsHelpers.ofFn_drop_take`, `FromDiscreteLog.ofFn_splitBits_fst/_snd`); F-03 `PRFMAC.blocks`/`macState`/`hits_nil_iff` near `GGMRed.tblEnc`/`lookup` (cca2-ett `tblW`). The private `prfAdv_prfReduction` (`OracleFromPRF.lean`) is the same identity specialised (DL-40). | `TCSlib.Cryptography.prfAdv_eq_expect` (published in #314, merge `59c2c1fb`); the list readers above; `GGMRed.tblEnc` | Open (F-01 paid) | F-01 **paid**: promoted in #314 (ETT re-derived, LE-gate30), prf-mac re-pointed by LE-reuse `590d1a56` (#317, Gate 33). F-02/F-03 and the private `prfAdv_prfReduction` in the deferred cleanup. |
| DL-45 | learning fill (delivery review 2026-11-15): undisclosed `LearnPRF.uprob_eq_point` = `OneWay.uprob_eq_one_div_card` (reversed); inline re-proof of `MultiMsg.abs_uexp_sub_le_uprob` in `abs_gameProb_random_sub_half_le` (both re-pointed by maintainer LE-reuse `8befc589`, #313); private `length_blk` re-proves `MultiMsg.length_histBlock` for the disclosed private copy `blk` of `histBlock`; `flip0`/`flip0_flip0` = `flipBit`/`flipBit_flipBit` (BooleanAnalysis) and `flipAt` (DeterministicCC); `foldr_pairEncode_nil` reads `Strategy.encodeMsgs`; short-name clashes `relabel`/`relabel_eq` (DL-36 family) and `flipAt`. | `OneWay.uprob_eq_one_div_card`; `MultiMsg.abs_uexp_sub_le_uprob`, `length_histBlock`; `BooleanAnalysis.flipBit` | Open | Items 1–2 by LE-reuse at landing; the rest in the deferred cleanup. |
| DL-46 | prf-long fill (delivery review 2026-11-15, disclosed): `MultiMsg.encodeList_eq_flatMap` (`FromPRF/MultiMsgOut.lean`) is a third copy of public `encodeList_eq_flatMap` (`Asymptotic/BlockEncryptor.lean`) beside the frozen private copy in `FromPRF.lean` (now unused); reuse blocked by a private/public name clash. `histBlockLen` kept beside `histBlockLenOut` (different `PolyExpr` terms); `adviceBound` now unused. Near relatives: GGM `encodeHist_eq_histEnc`/`histEnc_append_single`/`length_histEnc`, `UniformTableauEmitter.encodeList_eq_flatMap`. | `encodeList_eq_flatMap` (to move to `EnsembleSecurity`, worker's promotion request) | Open (deferred) | Promote and delete the copies; remove the unused frozen items under a frozen-file exception in the cleanup. |
| DL-47 | Gate 32 staging (2026-11-15), pre-existing: copies of `((List.ofFn f).drop i).headD d = f i` and of its getD form `(List.ofFn f).getD i d = f i`, at the tip `e9998722`. Inline chain: `Pseudorandom/NextBit.lean:454` (`headD_drop, List.getD_eq_getElem?_getD, List.getElem?_ofFn`, the remnant of NextBit's private `headD_drop_ofFn` that dl-consolidation L1 deleted). Index-0 cases: `headD_ofFn_one` (`Foundations/BitLists.lean:75`), `GIZK.headD_ofFn_block` (`ZeroKnowledge/GraphIsomorphismZK/Closeness.lean:280`), private `eq_const_headD` (`Encryption/PublicKey/NonMalleability/Simulation/SimIND.lean:88`). getD forms: `GI.getD_ofFn_lt'` (`ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean:61`), `GI.getD_ofFn_lt` (`ZeroKnowledge/GraphIsomorphism/Proofs.lean:818`), `GIZK.getD_ofFn_lt` (`ZeroKnowledge/GraphIsomorphismZK/Closeness.lean:110`), `ColProofs.ofFn_getD_lt` (`ZeroKnowledge/ThreeColoring/ProtocolProofs.lean:391`), Yao's private `getD_ofFn'` (`SecureComputation/Yao.lean:611`). Inline getD chains (`List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos …`): `ZeroKnowledge/ThreeColoring/Simulator.lean:861`, `ZeroKnowledge/ThreeColoring/Language.lean:429` (in private `ofFn_getD_tape`), `ZeroKnowledge/Encoding.lean:359`; the same getD chain also inline outside the cryptography files, in `TCSlib/Complexity/ClassNP/SAT.lean:149`, `TCSlib/Complexity/ClassNP/Tautology.lean:142` and `TCSlib/Complexity/SpaceComplexity/Codec/Word.lean:135` (`getD_encChunk`). **Extended by Gate 32 G32-01 (ruling Seyoon 2026-11-15: extend DL-47 and close), at the #316 head `c18afbe6`:** exact copy of the promoted statement: GGM `Pseudorandom/Functions/Asymptotic/GGM/Run.lean:449–450` (`step_eq`, local `hbit`, replacement `TCSlib.Cryptography.headD_drop_ofFn x ⟨d.i, hi⟩ false`); headD chain `Asymptotic/HardCoreLoops.lean:278–280` (`orbit_eq`); getD/ofFn computations: `SecureComputation/Garbling.lean:193–198` (private `map_range_getD_ofFn`) and `:375–380` (`garbledValues_getD`), `SecureComputation/Yao.lean:626–627` (`yaoBobTables_yaoMsg`), `Encryption/PublicKey/BitwiseCPA.lean:107–113` (private `ofFn_half`), `Encryption/PublicKey/OracleSecurity/PaddedCPA.lean:72–78` (private `ofFn_splitHalf_bit`), `Complexity/CircuitComplexity/CircuitEvalNP.lean:68–69` (`dagCktSatLang_mem_NP`), `PSubsetPPolyGadget.lean:188–190` (`runWith_embedGates_getD`), `PSubsetPPolyProgram.lean:383–387` (`progGates_values`), `PSubsetPPolyTableau.lean:127–132` (`snapEncode_injective`), `UniformTableauCircuit.lean:427–431` (private `tabSrc_eval`), `Complexity/Randomized/RandomWalk.lean:256–259` (`decodeIdx_succ_append`), `Complexity/ClassPSPACE/TQBF.lean:857–859` (private `codecRow_realize`), optional-access form `Cryptography/Encoding/BooleanVector.lean:168–171` (`expandPoly_encode`) and `Hashing/SIS/CollisionOutput.lean:237–243` (`collisionOutputPoly_pairEncode`). **sc-garble SG-F04 (ruling Seyoon 2026-11-15, ledger):** new inline getD/`List.ofFn` chain in `SecureComputation/Garbling/CoinBlocks.lean:73–74` (`getD_eq_getElem`, `getElem_ofFn`), same as Yao's private `getD_ofFn'`. | `TCSlib.Cryptography.headD_drop_ofFn` (#316) | Open (deferred) | Ruling Seyoon 2026-11-15: pre-existing (merged before the promotion), recorded as debt and not re-pointed in #316. Re-point NextBit:454 and the index-0 cases onto `headD_drop_ofFn`, and the getD forms onto one shared getD reader, in the deferred cleanup. Yao's `getD_ofFn'` waits for sc-garble and sc-yao to land (`Yao.lean` is shared). **Cleanup plan (G32-01):** add one generic reader `(List.ofFn f).getD i d = f ⟨i, h⟩` (any type) derived from `headD_drop_ofFn` and `List.headD_drop`, then re-point every DL-47 copy onto it or onto `headD_drop_ofFn`, proof only, headers preserved, starting with the exact GGM copy; the `Garbling.lean`/`Yao.lean` copies wait for sc-garble and sc-yao to land. |
| DL-48 | sc-ot fill (delivery review 2026-11-15): F-02 `OT.splitLen` / `splitLen_symm_ofFn` (`SecureComputation/ObliviousTransfer/Simulators.lean`) restate public `coinsEquiv` (inverted) and `ofFn_coinsEquiv` (`Asymptotic/EnsemblesLemmas.lean:141,145`), body as private ElGamal `dlc_splitEquiv`; F-04 `OT.uprob_signedPredictor_false/_true` adapt `exists_pkPredictor` (`pkPredictor` has no public reader); F-07 near-relatives `GI.pairSndD_encodeMsgs` (for `getD_one_eq`), `predict_eq`, and promotion requests `negligible_finset_sum`, `statClose_prod_of_forall`, `exec_five`, `length_runAtL_le`. **Gate 34 G34-02 (ruling Seyoon 2026-11-15, ledger):** `OT.length_ofFn_coins` (`ObliviousTransfer/Simulators.lean:210–212`) is a verbatim copy of public `Composability.NMSim.length_ofFn_coins` (`Encryption/PublicKey/NonMalleability/Simulation/Rounds.lean:41–43`); direct reuse would add 69 NM modules to the OT closure. (G34-01, `OT.getD_zero_eq`/`OT.getD_one_eq'` re-proving `headD_drop`, is fixed by LE-gate34, not debt.) | `coinsEquiv`, `ofFn_coinsEquiv`; `exists_pkPredictor` | Open (deferred) | Ruling Seyoon 2026-11-15: ledger debt, disclosed (not fixed in the landing: reuse needs a new import and a definition change). Cleanup: replace `splitLen` by `(coinsEquiv h).symm`; publish `pkPredictor_apply` and re-derive the signed predictor from `exists_pkPredictor`; decide the promotion requests. G34-02 cleanup: promote `length_ofFn_coins` to the `NUPPT` layer (`Asymptotic/Adversary` or `Randomized/NonUniform`) and re-point both copies. |
| DL-49 | sc-compose fill (delivery review 2026-11-15, SC-F01; disclosed in the checkpoint REPORTs): helpers under `SecureComputation/ComposeSecurity/` restate public lemmas because the brief's two extra imports were read as exhaustive: a third `negligible_polyExpr_mul`; `appendCoins` (= `coinsEquiv`); `ofFn_blocks_symm` (= `FunFamily.ofFn_blocks_symm`); `polyTimeComputable_flatMap_range`, `flatMap_range_ite`, `iterSnd_poly`, `encodeMsgs_eq_flatMap`, `msgAt_encodeMsgs` and the `padTo` family (from `Composability/ZeroKnowledge/ThreeColoring/Machines.lean`). | `EnsembleLemmas.negligible_polyExpr_mul` (`Asymptotic/EnsemblesLemmas.lean:377`), `coinsEquiv`, `FunFamily.ofFn_blocks_symm`, the `ThreeColoring/Machines` helpers | Open (deferred) | Ruling Seyoon 2026-11-15: ledger debt. Cleanup: import the public lemmas (or promote the ThreeColoring helpers to a shared machine layer) and re-point the sc-compose copies proof-only. |

## ===== briefs/pass-shelat-ch5-8/fills/sc-compose/final-r1/landing/PROVENANCE.txt =====

sc-compose ([Gol04, §7.3.1, Theorem 7.3.3]: composeP_efficient, composeV_efficient, hbcSecure_compose) maintainer delivery review r1, 2026-11-15 UTC
$SP = /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad. Paths below are relative to this directory.
Method: as the sc-garble review ($SP/dl-review/sc-garble-r1/, the common brief with Updates 1-3, the sc-ot template, C-F02 full-file
  seals); run after it and after LE-gate29b, whose restores left the tree at the base snapshot. Nothing pushed, no PR opened, the
  records checkout only read (git fetch, git worktree). No lake build, no cache get. python3 -I. One Lean process at a time, only on
  $SP/dl-oleans (dl-oleans-2 never touched).

issue package: briefs/pass-shelat-ch5-8/fills/sc-compose/issued-r1/ (brief.md in logs/): SHA256SUMS 7/7 OK (logs/issue-package-check.txt);
  SOURCE-SHA256SUMS 152/152 OK at the issue base 107f1e8c218733eac12d6b9bee6fece441271317 (logs/source-sums-check.txt); base-sorries 31 in
  14 modules. ComposeSecurity.lean is byte-identical (blob 3041d93f) at eff2dcd0, 107f1e8c and the tip (statements/owned-file-blobs.txt).
delivery: exchange/pass-shelat-ch5-8 bdfdcb76d0d78bedd61025b33cb7382b26ee7c70 ("Claude fill sc-compose: final"; checkpoints 419c4ceb, f1ba0b1a);
  the three commits touch only inbox/fills/sc-compose/, no later commit touches it (logs/exchange-commits.txt). git archive into a fresh
  directory (removed after use); inventory logs/payload-inventory.sha256 (1063 files); cited extracts logs/delivery-extracts/ (11 files
  byte-equal, logs/delivery-extract-hashes.txt) and the two checkpoint REPORTs from the exchange (checkpoint-reports/; the final REPORT's
  Overlap section says their tables "stand"). Worker REPORT: logs/worker-REPORT.md.
integrity (logs/payload-check.txt): top SHA256SUMS 1062/1062 OK; evidence/SHA256SUMS 1031/1031 OK; exact path sets, no "./".
  git am of the 12 patches at 107f1e8c with committer data from patches/COMMITS.tsv: with commit.gpgsign=false no hash reproduces
  (logs/git-am-integrity-unsigned.log); with the environment's default SSH signing all 12 reproduce (a3cb219d … d3f405d4671a3ad0ffd3930ef182a43cb12ed134,
  each with a gpgsig; logs/git-am-integrity.log); the tree is 25be113b either way. COMMITS.tsv has no signing column (this brief did not
  ask for one; as sc-ot F-05). The 16 changed paths (M ComposeSecurity.lean; A 15 helpers under ComposeSecurity/) are byte-identical to
  src/, which holds exactly these (logs/src-equality.txt): scope as briefed.
olean tree: tree/snapshot-pre.txt 1230 files, SHA-256 457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f (required value).
landing: branch land/pass-shelat-sc-compose (local), worktree $SP/wt-land-sc-compose (sparse, briefs/ excluded). Worker head d3f405d4
  rebased onto origin/cryptography/pass-shelat-ch2-4 6ce4658db08a1dc2a03a149987197660db078011 (landing/landing.log): rc 0, range-diff
  12/12 identical, the 16 paths equal the worker head. Origin Lean delta since 107f1e8c: 29 files (#307, #311, #312, #314-#317; the only
  SecureComputation file is SpecialEncryptionMulti; landing/origin-delta-since-issue-base.txt). LE-doc on top.
  FINAL head f61ce08fa74401660345f1f50c36dffb37588391, tree f7432799ee26f287a4e3055a1b5f6eba97305972 (landing/commits.txt, series
  landing/series/0001-0013); 16 files +4578/-58 vs origin. 13 commits, all SSH-signed by the environment default; the 12 worker commits
  keep author Claude <noreply@anthropic.com>; LE-doc f61ce08f authored Claude <noreply@anthropic.com>.
LE-doc (f61ce08f; tools/ledoc_sc.py, plan landing/le-doc-plan.tsv, diff landing/le-doc.diff, message landing/commit-msg-le-doc.txt):
  for the 70 new public declarations docaudit flagged NO-FORMULA (all but the two frozen targets and 2 whose docstring already states
  the formula), the declaration's own Lean conclusion (for a def whose type is no relation, its _eq/_iff reader's) is added as a
  backticked formula at the end of the statement prose; 15 long conclusions cut at 240 characters with " …". tools/ledoc_list_sc.py
  lists the candidates (statements/head/ledoc-candidates.tsv). landing/le-doc-doconly.txt (tools/doconly_sg.py): code-identical True in
  all 13 edited files, docstring counts unchanged, max width 100: RESULT OK. statements/head-le/decls2-vs-worker.tsv empty.
build (order/ from downorder.py against eff2dcd0 at the pre-edit head f3036c69: changed 85 = 69 base delta + 16 unit; down 279):
  - build/: 279/279 rc 0, 0 errors (G26-N1, both forms), substring "error" 0, 1558 s; the 16 unit modules 0 warnings, 0 sorry; sorry
    warnings only in admitted modules. Unit downstream: ComposeSecurity, YaoReal, the SecureComputation facade, root TCSlib.
  - edit-build/ (order/le-build-queue.txt, 18 modules: the 13 edited helpers, their dependants, ComposeSecurity, YaoReal, SecureComputation,
    TCSlib): 18/18 rc 0, 0 errors, 0 warnings.
  - tree/backed-up.txt (214 base oleans, hashes = snapshot-pre), tree/new-oleans.txt (65). tree/tree-check-head.txt (1264 modules;
    logs/records-head.jsonl = base records + build + edit-build): RESULT OK.
statements (base 107f1e8c):
  - statements/frozen/frozen-check.txt and statements/head-le/frozen-check.txt (tools/frozencheck.py): the 11 base declarations of the
    owned file present, same kind, name and order; headers and statement prose identical: 0 differences. Controls
    (statements/frozen/controls-summary.txt): headers of hbcSecure_compose and composeP_efficient, prose of composeV_efficient, removal of
    the private exists_ofFn_eq: each exactly 1 difference; the polyTime_compose prose control is a harness artifact (its docstring has no
    sketch, so the changed character was the closing `-/`), noted there. statements/frozen/owned.diff: imports, title, ## Contents,
    ## Main results, the three proofs and their sketches only.
  - statements/head-le/touched.tsv: 3 CHANGED (the targets), 8 UNCHANGED, 186 in new files; decls2-vs-base.tsv 185 ADDED, 0 CHANGED,
    0 REMOVED; no @[simp], no instance. docaudit (head-le): 145 OK, 29 LABEL (all state their equation), 14 NO-FORMULA = the two frozen
    targets + 12 `PolyTimeComputable …` Prop formulas (no relation symbol; tool artifact). sketchaudit: 37 theorems with >= 15 proof lines,
    3 without a sketch: runW_eq, composePW_eq, composeVW_eq, `:= rfl` readers under long statements (tool artifact). Sizes: max 604 lines
    (Runs), owned file 449, max width 100, 0 over 100. Name clash (clash/nameclash-head.txt): 0 exact clashes; the private exists_ofFn_eq
    of Lengths.lean has the same short name as the owned file's private one (disclosed by the worker).
axioms: probe-sources/head/CensusHead.lean (tools/mkcensus_sc.py) -> probe-runs/: composeP_efficient, composeV_efficient,
  hbcSecure_compose, polyTime_compose, exists_simA/B and the helper endpoints [propext, Classical.choice, Quot.sound]; yaoProtocol_hbcSecure
  keeps sorryAx. DepTrace.lean (copy of the sc-garble probe): the admitted declarations under yaoProtocol_hbcSecure are now only
  otProtocol_polyTime, otProtocol_simulators (sc-ot, #318) and yaoHybrid_polyTime, yaoHybrid_simulators (sc-yao); hbcSecure_compose is
  gone. logs/census-summary.txt: 258 stored constants (= the worker's), axiom union the standard three, no sorryAx, simp or instance;
  the 3 "abbrev" rows are compiler match auxiliaries (`…match_1_1`). Base (CensusBase on the base-phase tree): the 3 targets and
  polyTime_compose had sorryAx. logs/census-base-vs-head.tsv: removed 0, type-changed 0, axioms-changed 4 (those, sorryAx dropped).
admissions: logs/sorry-census.txt (issued base-sorries, issue base 107f1e8c, records-head.jsonl): 31 in 14 modules -> 28 in 13; the only
  issued module differing is ComposeSecurity (3 -> 0). Outside the issued order only SeedMajority (#312) and SpecialEncryptionMulti (#311)
  differ, both base delta with changed sources.
Rule 10 (final head f61ce08f):
  - Collector CollectHead -> probe-runs/; seals mkseals_ab.py (strict) seals/{A,B}, mkseals_coe.py (canonical) seals-coe/{A,B}
    (logs/mkseals-*.log; 561-1192 requests); 64 probes seal-runs/ (lean -DmaxErrors=0, tools/runner_full.py): logs/seal-head-*.tsv:
    64/64 rc 0, 0 errors, install and EOF records present: A and B, strict and coe, all 16 files pass.
  - Base: ComposeSecurity's closure contains base-delta modules, so the tip version (= 107f1e8c) was rebuilt from a sparse worktree
    $SP/wt-sc-base at 6ce4658d (base-build/, 1 module, rc 0; worktree removed), then CensusBase, CollectBase (base-probe-runs/) and 4 base
    seals (base-seals{,-coe}/, base-seal-runs/): 4/4 pass (670/671/669/670 requests = the worker's). logs/seal-table-seals.txt,
    seal-table-seals-coe.txt: head A 16/16, B 16/16; new failing declarations 0; strict = coe.
  - Paired controls tools/mkctl_sc.py (rows PolyExpr.eval, the FinDist CoeFun instance, HybridProtocol.answersA (frozen Hybrid.lean),
    ComposeMachines.padTo, ComposeSim.tmplW) -> controls/ (coe, 14 probes, 16 sealed negatives), controls-strict/ (16, 24), runs
    control-runs/: logs/ctlcheck.log ALL_OK True; logs/ctlcheck-strict.log: every sealed negative fails exactly once, every unsealed probe
    passes, only ctlCoeReader fails under the strict seal (harness effect; logs/controls-strict-attribution.txt).
  - Explicit-unfold scan (scan/items-head.json, explicit-head.json, logs/scan2-head.log; at the final head): 1189 items, 1036 THEOREM,
    2 OWNED_DEFINITION, 151 LOCAL_OR_UNRESOLVED, 0 foreign.
lint (#305 script): tip 6ce4658d 92 FAIL / 101 WARN (lint/lint-records-tip-6ce4658d.txt, from the LE-gate29b job's export) and the
  landing head before LE-doc 92/101 (lint-landing-head-preLE.txt); identical line sets (linediff-preLE.txt empty). LE-doc only edits
  docstrings.
content: the three targets read. composeP/V_efficient: composePW/composeVW on the layout are polynomial-time
  (polyTimeComputable_composePW/VW from runW/ansW/mainW and polyTimeComputable_flatMap_range), the strategy equals it
  (composeP_next_eq_composePW), GI.efficient_of_polyTime. hbcSecure_compose: hbcSecure_iff with polyTime_compose, simulators
  exists_simA/exists_simB and, per D, ε = ε_A + ε_B (each nonnegative as it bounds a distAdv); the two sides follow the five-step sketch
  (simulator Φ ∘ S_A^H, correct answers off GoodRuns with L·ε_c, the hybrid chain over the runs with the worst-case template as advice
  at ε₂ per step, the hybrid model via H.HBCSecure F, total L(ε_c + ε₂) + ε₃). hM is used in realA/realB_compose_eq. Edge cases listed in
  the brief are covered as the REPORT says (L = 0, rounds = 0, fillers, cut lengths, padFin readback, Bob's side).
duplication: checkpoint REPORTs (logs/delivery-extracts/checkpoint-reports/) disclose restatements of public lemmas the worker judged
  "not importable" under the brief's helper-import sentence (finding SC-F01); the final REPORT relies on those tables.
open PRs (logs/open-pr-overlap.txt): merge-tree of the landing head (pre-edit f3036c69) with #313 94b31964 (and the local LE-gate29b head
  2b6c2981), #318 f62a25b3, #319 6421ac16 and the local sc-garble landing cd9a4843: all clean; no shared file; shared downstream #313:
  TCSlib; #318 and sc-garble: YaoReal, SecureComputation, TCSlib; #319: TCSlib.
restore (restore/restore-log.txt): 214 backups back (0 hash failures), 65 new oleans deleted, emptied dirs pruned; SNAPSHOT EQUAL;
  tree/snapshot-post.txt 1230 files SHA-256 457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f = snapshot-pre;
  tree/tree-check-post.txt: 1199 base modules, snapshot equal: RESULT OK.
tools/: the sc-garble review's tools plus mkcensus_sc.py, mkctl_sc.py, ledoc_sc.py, ledoc_list_sc.py.
cleanup: payload extraction, backups bk-sc, the integrity worktree wt-sc-int and the base worktree (git worktree remove --force), the
  LE-doc trial copy and PlProbe/ removed; the landing worktree is clean at f61ce08f.
SHA256SUMS: every file here except itself (paths without "./"); ../sc-compose-r1-evidence.zip holds exactly these paths plus SHA256SUMS.

## ===== briefs/pass-shelat-ch5-8/gates/37-sc-compose/pr-description.md =====

This is the landing PR for the Pass–shelat `sc-compose` fill. It proves the three admitted theorems in `SecureComputation/ComposeSecurity.lean`:
- `composeP_efficient` and `composeV_efficient`, the composed strategies are PPT;
- the composition theorem for the semi-honest model ([Gol04, §7.3.1, Theorem 7.3.3]).

**Head:** `a6eaebd78c48e7fdfd06263edb84b70bc00ec593`.
**Base:** `cryptography/pass-shelat-ch2-4` at `6ce4658d`.

## Changes
16 Lean files, +4580/−60: the owned `ComposeSecurity.lean` and 15 helpers under `ComposeSecurity/`. The proof follows the five-step sketch with ε = ε_A + ε_B.

**Commits:**
- Twelve Claude worker commits.
- **LE-doc** `f61ce08f`: formulas for 70 new public declarations.
- **LE-prose** `a6eaebd7`, for SC-F03, under Seyoon's frozen-prose exception (2026-11-15). The docstring of `polyTime_compose` no longer calls the efficiency theorems `sorry`s. This is docstring-only: the code is identical once doc comments are removed.

## Review
The record is `briefs/pass-shelat-ch5-8/fills/sc-compose/final-r1/review.md`. Verdict: **ACCEPT WITH LANDING EDITS**.
- **Statements:** 0 differences on the owned file's 11 declarations, and exactly 3 targets changed. decls2 gives 185 ADDED, 0 CHANGED, 0 REMOVED. There are no name clashes.
- **Axioms:** the targets and `polyTime_compose` use only the standard three, as do all 258 stored constants.
- **Build:** 279/279 rc 0, with 0 errors. The whole-tree check covers 1264 modules: OK.
- **Rule 10:** seals 64/64 at the head and 4/4 at the base. The controls are ALL_OK. The strict `ctlCoeReader` failure is the known harness effect.
- **Admissions:** 31 → 28.
- **Lint:** unchanged.
- **Ledger:** SC-F01 is recorded as DL-49, by Seyoon's ruling. About ten public lemmas were restated instead of imported, because the worker read the brief's import list as exhaustive. Examples are a third `negligible_polyExpr_mul`, `appendCoins` = `coinsEquiv`, and the `ThreeColoring/Machines` list helpers. They will be re-pointed in the cleanup.

A Codex gate follows. Seyoon merges.

---
_Generated by [Claude Code](https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA)_

## ===== briefs/pass-shelat-ch5-8/gates/37-sc-compose/pr.diff.txt =====

diff --git a/TCSlib/Cryptography/SecureComputation/ComposeSecurity.lean b/TCSlib/Cryptography/SecureComputation/ComposeSecurity.lean
index 3041d93f2..931d14291 100644
--- a/TCSlib/Cryptography/SecureComputation/ComposeSecurity.lean
+++ b/TCSlib/Cryptography/SecureComputation/ComposeSecurity.lean
@@ -3,13 +3,28 @@ Copyright (c) 2026 TCSlib contributors. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 -/
 import TCSlib.Cryptography.SecureComputation.ComposePhases
+import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Machines
+import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Efficiency
+import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Probability
+import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Reductions
+import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Assembly
+import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Runs
+import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Bounds
+import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Sim
+import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Chain
+import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Accept
+import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Correct
+import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Template
+import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Lengths
+import TCSlib.Cryptography.SecureComputation.ComposeSecurity.SideA
+import TCSlib.Cryptography.SecureComputation.ComposeSecurity.SideB
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
 set_option autoImplicit false
 
 /-!
-# The composition theorem for the semi-honest model (statement phase)
+# The composition theorem for the semi-honest model
 
 [Gol04, §7.3.1, Theorem 7.3.3]: if a protocol `H` privately computes `F` in the `G`-hybrid model
 and a protocol `ρ` privately computes `G`, then `H` with every ideal call replaced by a run of `ρ`
@@ -25,8 +40,10 @@ follows from this theorem with Protocol 160.4 for `ρ`.
 **Polynomial time** (ruling of 2026-11-05: security includes polynomial-time parties). The
 messages of `H.compose ρ` are bounded by the sum of `main`'s and `ρ`'s bounds
 (`compose_msg_bound`, proved). This uses that `H.PolyTime` bounds `main`'s messages for **any**
-answers of the right lengths, since in `H.compose ρ` `main` runs on `ρ`'s outputs. That the
-composed strategies are PPT is stated, with `sorry`s under their sketches.
+answers of the right lengths, since in `H.compose ρ` `main` runs on `ρ`'s outputs. The composed
+strategies are PPT (`composeP_efficient`, `composeV_efficient`): each is a polynomial-time
+function of the machine layout built from `main`'s and `ρ`'s machines and the call-input
+functions (`ComposeSecurity/Efficiency.lean`).
 
 **Deviations from [Gol04, Theorem 7.3.3].**
 - **Calls first only**, and the layout with fillers (`Compose.lean`).
@@ -46,15 +63,38 @@ composed strategies are PPT is stated, with `sorry`s under their sketches.
 * None: the composed protocol is defined in `Compose.lean` and its phases in
   `ComposePhases.lean`.
 
+## Contents
+
+* `ComposeSecurity/Machines.lean`: polynomial-time machines on encoded histories (loops over a
+  data-dependent range, the interleaved-slot map, strategies as functions of the layout).
+* `ComposeSecurity/Efficiency.lean`: the composed parties as polynomial-time functions of the
+  machine layout.
+* `ComposeSecurity/Probability.lean`: distinguishing-advantage tools (the statistical switch,
+  fixing coordinates, a negligible function times a polynomial).
+* `ComposeSecurity/Reductions.lean`: machines with advice-dependent pre- and post-processing.
+* `ComposeSecurity/Assembly.lean`: a view of the composed protocol assembled from run views.
+* `ComposeSecurity/Runs.lean`: the coins of the composed protocol run by run, and the real
+  samples when every run gives the ideal answers.
+* `ComposeSecurity/Bounds.lean`: lengths of encodings, transcripts and machine outputs.
+* `ComposeSecurity/Sim.lean`: the post-processing `Φ`, the simulators and the reduction to the
+  hybrid model.
+* `ComposeSecurity/Chain.lean`: the hybrid argument over the runs.
+* `ComposeSecurity/Accept.lean`: acceptance of machines with split coins; test machines.
+* `ComposeSecurity/Correct.lean`: a secure protocol is correct; the union bound over the runs.
+* `ComposeSecurity/Template.lean`: the reduction of one hybrid step to the sub-protocol.
+* `ComposeSecurity/Lengths.lean`: polynomial bounds on the words of the templates.
+* `ComposeSecurity/SideA.lean`, `ComposeSecurity/SideB.lean`: Alice's and Bob's sides of the
+  composition theorem.
+
 ## Main results
 
 * `HybridProtocol.exists_runExec_eq_transcript`, `exists_mainExec_eq_transcript`: the runs and
   the main phase are transcripts of `ρ` and `main` on inputs and coins of the right types.
 * `HybridProtocol.compose_msg_bound`: the messages of `H.compose ρ` are polynomially bounded.
-* `HybridProtocol.composeP_efficient`, `composeV_efficient` (stated; `sorry`s under their
-  sketches), and `polyTime_compose` (proved from the three).
-* `HybridProtocol.hbcSecure_compose` ([Gol04, Theorem 7.3.3], stated; a `sorry` under its
-  sketch).
+* `HybridProtocol.composeP_efficient`, `composeV_efficient`: the composed strategies are PPT;
+  `polyTime_compose` (proved from the three).
+* `HybridProtocol.hbcSecure_compose` ([Gol04, Theorem 7.3.3]): from Alice's and Bob's sides
+  (`exists_simA`, `exists_simB`).
 
 ## References
 
@@ -280,35 +320,52 @@ theorem compose_msg_bound {F : Functionality} (hH : H.PolyTime F) (hρ : G.PolyT
 /-- **Alice's strategy in `H.compose ρ` is PPT** (`Strategy.Efficient`), when `main`'s and `ρ`'s
 are and the call inputs are polynomial-time.
 
-**Proof sketch.** A uniform machine with the coin polynomial `main.P.coins + calls · ρ.P.coins`
-computes `composeP.next` on `⟨⟨x, z⟩, hist⟩` and the tape `r`:
-1. it computes `n = |x|`, `L`, `R`, `|hist|` and the pair, run and position indices;
-2. it recomputes the run inputs with the polynomial-time function of `H.PolyTime` on
-   `⟨1^n, ⟨z, ⟨r_main, 1^j⟩⟩⟩`, cuts the run tapes out of `r`, and reads the run histories from
-   `hist` (`slotMsgs`);
-3. it runs the uniform machine of `ρ.P` once (a run move) or `L(n)` times (the answers), and that
-   of `main.P` once, each on an input of length polynomial in its own.
-
-Each piece is polynomial-time on the raw layout, and `L` is a polynomial, so the composition is
-(`NUPPT.ofPolyTimeUniform`). -/
+**Proof sketch.** Take polynomial-time functions of the machine layout for the efficient
+strategies `ρ.P` and `main.P` (`ComposeMachines.Efficient.exists_polyTime`) and Alice's
+call-input function from `H.PolyTime`. Alice's next message is `composePW` on the layout
+`⟨⟨⟨1^n, ⟨⟨x, z⟩, hist⟩⟩, []⟩, r⟩` (`composeP_next_eq_composePW`):
+1. the number `k = |hist|` of messages received, `L`, `R`, `k / R`, `k % R` and the mover test
+   are unary computations (`GI.msgCount_poly`, `divNum_poly`, `modNum_poly`);
+2. a run move is one activation of `ρ.P`'s machine on the call input (recomputed from the
+   `main`-tape), the run tape cut from `r` and the run's messages read at the interleaved
+   pairs (`ComposeMachines.runW`, `ComposeMachines.polyTimeComputable_slots`);
+3. the main move is one activation of `main.P`'s machine on `⟨z, answers⟩` and the messages
+   after the runs, the answers being `L(n)` such activations of `ρ.P`'s machine, padded and
+   concatenated (`ComposeMachines.ansW`, `ComposeMachines.polyTimeComputable_flatMap_range`).
+So `composePW` is polynomial-time (`polyTimeComputable_composePW`), and its uniform machine with
+the coin polynomial `main.P.coins + calls · ρ.P.coins` computes `composeP`
+(`GI.efficient_of_polyTime`). -/
 theorem composeP_efficient {F : Functionality} (hH : H.PolyTime F) (hρ : G.PolyTime ρ) :
     (H.composeP ρ).Efficient := by
-  sorry
+  obtain ⟨hmain, -, ⟨fA, hfA, hcallA⟩, -, -⟩ := (HybridProtocol.polyTime_iff H F).mp hH
+  obtain ⟨hρP, -, -⟩ := (Functionality.polyTime_iff G ρ).mp hρ
+  obtain ⟨Fρ, hFρ, hρeq⟩ := ComposeMachines.Efficient.exists_polyTime hρP
+  obtain ⟨Fm, hFm, hmeq⟩ := ComposeMachines.Efficient.exists_polyTime hmain
+  exact GI.efficient_of_polyTime _ (H.polyTimeComputable_composePW ρ hFρ hFm hfA)
+    (H.composeP_next_eq_composePW ρ hρeq hmeq hcallA)
 
 /-- **Bob's strategy in `H.compose ρ` is PPT** (`Strategy.Efficient`), when `main`'s and `ρ`'s
 are and the call inputs are polynomial-time.
 
-**Proof sketch.** As for Alice (`composeP_efficient`), with `ρ.V`, `main.V`, the call-input
-function for Bob, and the coin polynomial `main.V.coins + calls · ρ.V.coins`. -/
+**Proof sketch.** As for Alice (`composeP_efficient`): Bob's next message is `composeVW` on the
+layout (`composeV_next_eq_composeVW`), with `ρ.V`'s and `main.V`'s machines, Bob's call-input
+function, the count `k = |hist| − 1`, the selector of Alice's moves, the drop count
+`L·R + lead` before the main phase, and the coin polynomial `main.V.coins + calls · ρ.V.coins`;
+`composeVW` is polynomial-time (`polyTimeComputable_composeVW`). -/
 theorem composeV_efficient {F : Functionality} (hH : H.PolyTime F) (hρ : G.PolyTime ρ) :
     (H.composeV ρ).Efficient := by
-  sorry
+  obtain ⟨-, hmain, -, ⟨fB, hfB, hcallB⟩, -⟩ := (HybridProtocol.polyTime_iff H F).mp hH
+  obtain ⟨-, hρV, -⟩ := (Functionality.polyTime_iff G ρ).mp hρ
+  obtain ⟨Fρ, hFρ, hρeq⟩ := ComposeMachines.Efficient.exists_polyTime hρV
+  obtain ⟨Fm, hFm, hmeq⟩ := ComposeMachines.Efficient.exists_polyTime hmain
+  exact GI.efficient_of_polyTime _ (H.polyTimeComputable_composeVW ρ hFρ hFm hfB)
+    (H.composeV_next_eq_composeVW ρ hρeq hmeq hcallB)
 
 /-- **The composed parties run in polynomial time** [Gol04, §7.3.1, the efficiency of the
 protocol of Theorem 7.3.3]: if `H` runs in polynomial time on `F`'s inputs (`H.PolyTime F`) and
 `ρ` on `G`'s (`G.PolyTime ρ`), then `H.compose ρ` runs in polynomial time on `F`'s inputs.
-The two strategies are PPT (`composeP_efficient`, `composeV_efficient`; `sorry`s under their
-sketches), and the messages are bounded by `B_main + B_ρ` (`compose_msg_bound`, proved). The
+The two strategies are PPT (`composeP_efficient`, `composeV_efficient`, proved), and the
+messages are bounded by `B_main + B_ρ` (`compose_msg_bound`, proved). The
 message bound uses that `H.PolyTime` bounds `main`'s messages for **any** answers of the right
 lengths, since `main` runs on `ρ`'s outputs. -/
 theorem polyTime_compose {F : Functionality} (hH : H.PolyTime F) (hρ : G.PolyTime ρ) :
@@ -337,45 +394,55 @@ D8's output convention (the module docstring gives an example): if `main.rounds(
 last move of `H.compose ρ` is a run move or the leading filler, and its sender outputs that
 message instead of its output in `main`.
 
-**Proof sketch.** Write `L = calls(n)`. Efficiency is `polyTime_compose`. Fix a non-uniform
-PPT distinguisher `D`. Alice's side follows; Bob's is symmetric.
-1. *The simulator* `S_A`, on `⟨1^n, ⟨x, f_A(x, y)⟩⟩`: run the hybrid simulator `S_A^H` on the
-   same input and read its output as a view of `main` with private input `⟨x, a⟩` and tape
-   `r_main`. For each `j < L`, recompute Alice's input to call `j`, `callA(n, x, r_main, j)`
-   (polynomial time by `H.PolyTime`), and run `ρ`'s simulator `S_A^ρ` on it and the `j`-th
-   `G.outA(n)`-bit block of `a`, with fresh coins; read its output as a view of `ρ` (tape `r_j`,
-   messages `m_j`). Output Alice's view of `H.compose ρ`: input `x`, tape
-   `r_main r_0 ⋯ r_{L−1}` (each cut to its length), and the messages `m_j` at Bob's pairs, with
-   fillers, followed by the hybrid view's messages (the layout of `compose_viewP`). `S_A` makes
-   `L(n) + 1` simulator calls and polynomial-time work: a non-uniform PPT.
-2. *Correct answers.* By the output clause of `HBCSecure ρ G`, applied to the distinguisher that
-   compares the second component of Bob's `ρ`-sample with a string given as advice (Alice's
-   ideal output on the worst-case inputs of length `n`, so one non-uniform machine serves every
-   `n`), Alice's `ρ`-output differs from her ideal output with probability at most `ε₁(n)`,
-   uniformly over the inputs (`ε` before the inputs in `HBCSecure`); likewise Bob's. By the
-   union bound, except with probability `2L(n)ε₁(n)` over the coins, every run's outputs are
-   the ideal answers, read back exactly by `padFin` (`padFin_ofFn`). Then `answersRealA`,
-   `answersRealB` are the hybrid answers `answersA`, `answersB`, and the main phase and both
-   outputs are those of the hybrid execution (`compose_exec_main`, `compose_outV`, using `hM`).
-   So the real sample is within statistical distance `2L(n)ε₁(n)` of the sample in which `main`
-   runs on the ideal answers.
-3. *Hybrid argument over the runs.* In `H_i` the first `i` runs of Alice's view are replaced by
-   `S_A^ρ` on the call inputs and the ideal answers, the others are real, and `main` runs on the
-   ideal answers. `H_i` and `H_{i+1}` differ in run `i` only (`compose_exec_runs`: run `i` is an
-   honest execution of `ρ` on the call inputs and the run tapes, independent of the other
-   runs given the `main`-tapes). A distinguisher between them gives one for `ρ`'s Alice side,
-   holding as advice the worst-case `i`, inputs, `main`-tapes and ideal answers for length `n`;
-   it simulates the other runs, runs `main` on the ideal answers, and assembles the sample in
-   polynomial time. So `|Pr[H_i] − Pr[H_{i+1}]| ≤ ε₂(n)`, and `H_0`, `H_L` are within `L(n)ε₂(n)`.
-4. *The hybrid model.* `H_L` is the post-processing `Φ` of step 1 applied to the hybrid real
-   sample `H.realA F n x y` (Bob's output there is `main`'s, as in `H_L`), and `idealA S_A` is
-   `Φ` applied to `F.idealA S_A^H`. `D ∘ Φ` is a non-uniform PPT, so `H.HBCSecure F` bounds the
-   remaining distance by `ε₃(n)`.
-5. In total `L(n)(2ε₁(n) + ε₂(n)) + ε₃(n)`, negligible since `L` is a polynomial. -/
+**Proof sketch.** Write `L = calls(n)`. Efficiency is `polyTime_compose`. Alice's side is
+`exists_simA` (`ComposeSecurity/SideA.lean`), Bob's is symmetric (`exists_simB`); for a
+distinguisher `D` the sum of the two negligible bounds bounds both advantages. On Alice's side:
+1. *The simulator* `S_A` (`ComposeSim.exists_simulator`), on `⟨1^n, ⟨x, f_A(x, y)⟩⟩`: run the
+   hybrid simulator `S_A^H` on the same input and read its output as a view of `main` with
+   private input `⟨x, a⟩` and tape `r_main`. For each `j < L`, recompute Alice's input to call
+   `j`, `callA(n, x, r_main, j)` (polynomial time by `H.PolyTime`), and run `ρ`'s simulator
+   `S_A^ρ` on it and the `j`-th `G.outA(n)`-bit block of `a`, with the `j`-th block of fresh
+   coins. Output Alice's view of `H.compose ρ` (`ComposeSim.asmView`): input `x`, tape
+   `r_main r_0 ⋯ r_{L−1}` (each cut or padded to its length), and the run messages at Bob's
+   pairs, with fillers, followed by the hybrid view's messages (the layout of `compose_viewP`).
+2. *Correct answers* (`ComposeProb.exists_correct`). The output clause of `HBCSecure ρ G`,
+   applied to the machine that compares the second component of a sample with an advice string
+   (each party's ideal output on the worst-case inputs of length `n`), bounds the probability
+   that a party's `ρ`-output is not its ideal output by `ε_c(n)`, uniformly over the inputs. By
+   the union bound, every run gives the ideal answers except with probability `L(n)ε_c(n)`
+   (`uprob_not_goodRuns_le`), and then the real sample is the assembled view of the real run
+   views with the hybrid main phase and Bob's output in `main` (`realA_compose_eq`, using `hM`;
+   the statistical switch `ComposeProb.distAdv_le_uprob_of_eq`).
+3. *Hybrid argument over the runs* (`ComposeProb.abs_chain_le`). In hybrid `i` the first `i`
+   run views are `S_A^ρ`'s outputs on the call inputs and the ideal answers. Resampling run `i`
+   at fixed other coordinates (`exists_hyb_step`), neighbouring hybrids give a distinguisher for
+   `ρ`'s Alice side that holds as advice the template of the worst-case inputs, run index and
+   coordinates at length `n`: the header of the view, the other runs' words and Bob's output,
+   of polynomial length (`exists_tmplA_bound`). It inserts the `ρ`-view and assembles the
+   sample in polynomial time (`ComposeSim.exists_gap_le`), so each step is within `ε₂(n)`.
+4. *The hybrid model.* With every run simulated the sample is `Φ` applied to the hybrid real
+   sample `H.realA F n x y` (`acceptProb_realA_dPhi`), and `idealA S_A` is `Φ` applied to
+   `F.idealA S_A^H` (`ComposeProb.acceptProb_post_pre`). `D ∘ Φ` is a non-uniform PPT
+   (`ComposeSim.exists_dPhi`), so `H.HBCSecure F` bounds the remaining distance by `ε₃(n)`.
+5. In total `L(n)(ε_c(n) + ε₂(n)) + ε₃(n)`, negligible since `L` is a polynomial
+   (`ComposeProb.negligible_polyExpr_mul`). -/
 theorem hbcSecure_compose {G F : Functionality} (H : HybridProtocol G) (ρ : Protocol)
     (hM : ∀ n, 0 < H.main.rounds.eval n) (hH : H.HBCSecure F)
     (hρ : SecureComputation.HBCSecure ρ G) : SecureComputation.HBCSecure (H.compose ρ) F := by
-  sorry
+  have hHpt := ((HybridProtocol.hbcSecure_iff H F).mp hH).1
+  have hρpt := ((SecureComputation.hbcSecure_iff ρ G).mp hρ).1
+  obtain ⟨SA, hSA⟩ := H.exists_simA ρ hM hH hρ
+  obtain ⟨SB, hSB⟩ := H.exists_simB ρ hM hH hρ
+  refine (SecureComputation.hbcSecure_iff (H.compose ρ) F).mpr
+    ⟨H.polyTime_compose ρ hHpt hρpt, SA, SB, fun D => ?_⟩
+  obtain ⟨εA, hεA, hA⟩ := hSA D
+  obtain ⟨εB, hεB, hB⟩ := hSB D
+  refine ⟨fun n => εA n + εB n, hεA.add hεB, fun n x y => ⟨?_, ?_⟩⟩
+  · -- `εB n` bounds a distinguishing advantage, so it is nonnegative
+    have h0 : 0 ≤ εB n := (abs_nonneg _).trans ((distAdv_def _ _ _).symm.le.trans (hB n x y))
+    exact (hA n x y).trans (le_add_of_nonneg_right h0)
+  · have h0 : 0 ≤ εA n := (abs_nonneg _).trans ((distAdv_def _ _ _).symm.le.trans (hA n x y))
+    exact (hB n x y).trans (le_add_of_nonneg_left h0)
 
 end HybridProtocol
 
diff --git a/TCSlib/Cryptography/SecureComputation/ComposeSecurity/Accept.lean b/TCSlib/Cryptography/SecureComputation/ComposeSecurity/Accept.lean
new file mode 100644
index 000000000..25386fe8c
--- /dev/null
+++ b/TCSlib/Cryptography/SecureComputation/ComposeSecurity/Accept.lean
@@ -0,0 +1,198 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Runs
+import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Probability
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Acceptance of machines with split coins
+
+The bookkeeping between the distinguishers and simulators of the composition theorem
+[Gol04, §7.3.1, proof of Theorem 7.3.3] and the samplers they act on:
+* coins as two strings (`appendCoins`) or as blocks (`blocksCoins`), read back by `take`, `drop`
+  and `coinBlock`;
+* a distinguisher `B` that pre-processes its sample with `p(n)` of its coins and hands the rest
+  to `D` accepts a sampler `X` as often as `D` accepts the pre-processed sampler on the seed
+  extended by those coins (`acceptProb_pre`);
+* a simulator that post-processes another machine's output, against a distinguisher that
+  pre-processes with the same map, is accepted as the other machine against the distinguisher
+  (`acceptProb_post_pre`);
+* a test machine with output `[P w]` accepts with the probability of `P` (`acceptProb_test`);
+  the comparison of the second component of a sample with an advice string is such a machine
+  (`exists_test`).
+
+## Main definitions
+
+* `ComposeProb.appendCoins`, `ComposeProb.blocksCoins`.
+
+## Main results
+
+* `ComposeProb.acceptProb_pre`, `ComposeProb.acceptProb_post_pre`, `ComposeProb.acceptProb_test`,
+  `ComposeProb.exists_test`.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §2.1 (non-uniform PPT machines, Definition 26.8) and §6.2 (Definition 155.1).
+-/
+
+namespace TCSlib.Cryptography.SecureComputation.ComposeProb
+
+open Complexity Turing TCSlib.Cryptography
+
+/-! ### Coins as strings -/
+
+/-- **Two coin strings as one**: `{0,1}^a × {0,1}^b ≃ {0,1}^c` for `c = a + b`, the first string
+followed by the second (`Fin.appendEquiv`). -/
+def appendCoins {a b c : ℕ} (h : c = a + b) : (Fin a → Bool) × (Fin b → Bool) ≃ (Fin c → Bool) :=
+  (Fin.appendEquiv a b).trans (Equiv.arrowCongr (finCongr h.symm) (Equiv.refl Bool))
+
+/-- The defining equation of `appendCoins` (see `appendCoins`).
+`appendCoins h = (Fin.appendEquiv a b).trans (Equiv.arrowCongr (finCongr h.symm) (Equiv.refl
+Bool))`. -/
+theorem appendCoins_eq {a b c : ℕ} (h : c = a + b) :
+    appendCoins h =
+      (Fin.appendEquiv a b).trans (Equiv.arrowCongr (finCongr h.symm) (Equiv.refl Bool)) := rfl
+
+/-- `⟦appendCoins h (u, v)⟧ = ⟦u⟧ ++ ⟦v⟧`. -/
+theorem ofFn_appendCoins {a b c : ℕ} (h : c = a + b) (u : Fin a → Bool) (v : Fin b → Bool) :
+    List.ofFn (appendCoins h (u, v)) = List.ofFn u ++ List.ofFn v := by
+  rw [appendCoins_eq, Equiv.trans_apply, ofFn_arrowCongr_finCongr]
+  exact List.ofFn_fin_append u v
+
+/-- The first `a` bits of `appendCoins h (u, v)` are `u`.
+`(List.ofFn (appendCoins h (u, v))).take a = List.ofFn u`. -/
+theorem take_ofFn_appendCoins {a b c : ℕ} (h : c = a + b) (u : Fin a → Bool) (v : Fin b → Bool) :
+    (List.ofFn (appendCoins h (u, v))).take a = List.ofFn u := by
+  rw [ofFn_appendCoins, List.take_left' List.length_ofFn]
+
+/-- The bits of `appendCoins h (u, v)` after the first `a` are `v`.
+`(List.ofFn (appendCoins h (u, v))).drop a = List.ofFn v`. -/
+theorem drop_ofFn_appendCoins {a b c : ℕ} (h : c = a + b) (u : Fin a → Bool) (v : Fin b → Bool) :
+    (List.ofFn (appendCoins h (u, v))).drop a = List.ofFn v := by
+  rw [ofFn_appendCoins, List.drop_left' List.length_ofFn]
+
+/-- **Blocks of coins as one string**: `({0,1}^b)^q ≃ {0,1}^m` for `m = q·b`, the blocks in order
+(`FunFamily.blocks`). -/
+def blocksCoins {m q b : ℕ} (h : m = q * b) : (Fin q → Fin b → Bool) ≃ (Fin m → Bool) :=
+  (FunFamily.blocks q b).symm.trans (Equiv.arrowCongr (finCongr h.symm) (Equiv.refl Bool))
+
+/-- The defining equation of `blocksCoins` (see `blocksCoins`).
+`blocksCoins h = (FunFamily.blocks q b).symm.trans (Equiv.arrowCongr (finCongr h.symm) (Equiv.refl
+Bool))`. -/
+theorem blocksCoins_eq {m q b : ℕ} (h : m = q * b) :
+    blocksCoins h =
+      (FunFamily.blocks q b).symm.trans (Equiv.arrowCongr (finCongr h.symm) (Equiv.refl Bool)) :=
+  rfl
+
+/-- `⟦blocksCoins h t⟧ = ⟦t 0⟧ ++ ⋯ ++ ⟦t (q − 1)⟧` (`ComposeSim.ofFn_blocks_symm`). -/
+theorem ofFn_blocksCoins {m q b : ℕ} (h : m = q * b) (t : Fin q → Fin b → Bool) :
+    List.ofFn (blocksCoins h t) = (List.ofFn fun j => List.ofFn (t j)).flatten := by
+  rw [blocksCoins_eq, Equiv.trans_apply, ofFn_arrowCongr_finCongr, ComposeSim.ofFn_blocks_symm]
+
+/-- Block `j` of `blocksCoins h t` is `t j`: `coinBlock b j ⟦blocksCoins h t⟧ = ⟦t j⟧`
+(`coinBlock_flatten`). -/
+theorem coinBlock_blocksCoins {m q b : ℕ} (h : m = q * b) (t : Fin q → Fin b → Bool) (j : Fin q) :
+    coinBlock b j (List.ofFn (blocksCoins h t)) = List.ofFn (t j) := by
+  rw [ofFn_blocksCoins, coinBlock_flatten (List.ofFn fun j => List.ofFn (t j))
+    (fun c hc => by
+      obtain ⟨i, -, rfl⟩ := List.mem_ofFn.1 hc
+      exact List.length_ofFn) j (by rw [List.length_ofFn]; exact j.2), List.getElem_ofFn]
+
+/-! ### Acceptance -/
+
+/-- **A distinguisher with pre-processing and extra coins**: if `B` has coins `p + D.coins` and
+`B(1^n, w; r) = D(1^n, Ψ w r_{<p(n)}; r_{≥p(n)})`, then
+`acceptProb X (B.distinguisherL n) = acceptProb (fun (s, e) => Ψ (X s) ⟦e⟧) (D.distinguisherL n)`
+over `e ∈ {0,1}^{p(n)}`.
+
+**Proof sketch.** Split `B`'s coins as `{0,1}^{p(n)} × D.Coins n` (`appendCoins`,
+`uprob_comp_equiv`); the cut coins are the two halves (`take_ofFn_appendCoins`,
+`drop_ofFn_appendCoins`); reassociate the seed (`Equiv.prodAssoc`). -/
+theorem acceptProb_pre {σ : Type*} [Fintype σ] (X : σ → List Bool) (B D : NUPPT) (p : PolyExpr)
+    (n : ℕ) (Ψ : List Bool → List Bool → List Bool) (hc : B.coins = .add p D.coins)
+    (hB : ∀ w r, B.runAtL n w r = D.runAtL n (Ψ w (r.take (p.eval n))) (r.drop (p.eval n))) :
+    acceptProb X (B.distinguisherL n) =
+      acceptProb (fun z : σ × (Fin (p.eval n) → Bool) => Ψ (X z.1) (List.ofFn z.2))
+        (D.distinguisherL n) := by
+  have hlen : B.coinLen n = p.eval n + D.coinLen n := by
+    rw [NUPPT.coinLen_eq, NUPPT.coinLen_eq, hc, PolyExpr.eval_add]
+  let e : (Fin (p.eval n) → Bool) × D.Coins n ≃ B.Coins n := appendCoins hlen
+  rw [acceptProb_def, acceptProb_def]
+  calc uprob (fun z : σ × B.Coins n => B.distinguisherL n (X z.1) z.2 = true)
+      = uprob (fun z : σ × ((Fin (p.eval n) → Bool) × D.Coins n) =>
+          B.distinguisherL n (X z.1) (e z.2) = true) :=
+        (uprob_comp_equiv ((Equiv.refl σ).prodCongr e)
+          (fun z : σ × B.Coins n => B.distinguisherL n (X z.1) z.2 = true)).symm
+    _ = uprob (fun z : σ × ((Fin (p.eval n) → Bool) × D.Coins n) =>
+          D.distinguisherL n (Ψ (X z.1) (List.ofFn z.2.1)) z.2.2 = true) := by
+        congr 1
+        funext z
+        rw [NUPPT.distinguisherL_eq, NUPPT.distinguisherL_eq, NUPPT.runAt_eq, NUPPT.runAt_eq, hB,
+          take_ofFn_appendCoins, drop_ofFn_appendCoins]
+    _ = uprob (fun z : (σ × (Fin (p.eval n) → Bool)) × D.Coins n =>
+          D.distinguisherL n (Ψ (X z.1.1) (List.ofFn z.1.2)) z.2 = true) :=
+        (uprob_comp_equiv (Equiv.prodAssoc σ (Fin (p.eval n) → Bool) (D.Coins n))
+          (fun z : σ × ((Fin (p.eval n) → Bool) × D.Coins n) =>
+            D.distinguisherL n (Ψ (X z.1) (List.ofFn z.2.1)) z.2.2 = true)).symm
+
+/-- **A simulator with post-processing against a distinguisher with pre-processing**: let
+`S(1^n, w; r) = Ψ (S'(1^n, w; r_{<S'.coins(n)})) r_{≥S'.coins(n)}` with coins `S'.coins + p`, and
+`B(1^n, v; r) = D(1^n, Ψd v r_{<p(n)}; r_{≥p(n)})` with coins `p + D.coins`, where
+`Ψd ⟨hv, o⟩ e = ⟨Ψ hv e, o⟩`. Then `D` accepts `⟨S(1^n, w), o⟩` as often as `B` accepts
+`⟨S'(1^n, w), o⟩`.
+
+**Proof sketch.** Split `S`'s coins as `S'.Coins n × {0,1}^{p(n)}` (`appendCoins`,
+`acceptProb_comp_equiv`; `take_ofFn_appendCoins`, `drop_ofFn_appendCoins`), and unfold `B` by
+`acceptProb_pre`; the two samplers on `S'.Coins n × {0,1}^{p(n)}` agree by `hΨ`. -/
+theorem acceptProb_post_pre (S S' B D : NUPPT) (p : PolyExpr) (n : ℕ)
+    (Ψ Ψd : List Bool → List Bool → List Bool) (w o : List Bool)
+    (hSc : S.coins = .add S'.coins p)
+    (hS : ∀ r, S.runAtL n w r =
+      Ψ (S'.runAtL n w (r.take (S'.coinLen n))) (r.drop (S'.coinLen n)))
+    (hBc : B.coins = .add p D.coins)
+    (hB : ∀ v r, B.runAtL n v r = D.runAtL n (Ψd v (r.take (p.eval n))) (r.drop (p.eval n)))
+    (hΨ : ∀ hv e, Ψd (pairEncode hv o) e = pairEncode (Ψ hv e) o) :
+    acceptProb (fun s : S.Coins n => pairEncode (S.runAt n w s) o) (D.distinguisherL n) =
+      acceptProb (fun s : S'.Coins n => pairEncode (S'.runAt n w s) o) (B.distinguisherL n) := by
+  have hlen : S.coinLen n = S'.coinLen n + p.eval n := by
+    rw [NUPPT.coinLen_eq, NUPPT.coinLen_eq, hSc, PolyExpr.eval_add]
+  rw [acceptProb_pre _ B D p n Ψd hBc hB]
+  refine (acceptProb_comp_equiv (appendCoins hlen)
+    (fun s : S.Coins n => pairEncode (S.runAt n w s) o) (D.distinguisherL n)).symm.trans ?_
+  refine congrArg (fun f => acceptProb f (D.distinguisherL n)) (funext fun z => ?_)
+  rw [hΨ, NUPPT.runAt_eq, NUPPT.runAt_eq, hS, take_ofFn_appendCoins, drop_ofFn_appendCoins]
+
+/-- **A test machine**: if `B(1^n, w; r) = [P w]` for all `w`, `r`, then `B` accepts the sampler
+`X` with probability `Pr_s[P (X s)]`:
+`acceptProb X (B.distinguisherL n) = uprob (fun s => P (X s) = true)` (`uprob_fst`). -/
+theorem acceptProb_test {σ : Type*} [Fintype σ] (X : σ → List Bool) (B : NUPPT) (n : ℕ)
+    (P : List Bool → Bool) (hB : ∀ w r, B.runAtL n w r = [P w]) :
+    acceptProb X (B.distinguisherL n) = uprob fun s => P (X s) = true := by
+  have h : (fun z : σ × B.Coins n => B.distinguisherL n (X z.1) z.2 = true) =
+      fun z => P (X z.1) = true := by
+    funext z
+    rw [NUPPT.distinguisherL_eq, NUPPT.runAt_eq, hB]
+    simp
+  rw [acceptProb_def, h]
+  exact uprob_fst fun s => P (X s) = true
+
+/-- **The comparison with an advice string**: for a polynomially bounded advice family `α` there
+is an `NUPPT` `B` with `B(1^n, w; r) = [eqW ⟨pairSndD w, α n⟩]`, which accepts exactly when the
+second component of the sample is `α n` (`BinArith.eqW_pairEncode`). -/
+theorem exists_test (α : ℕ → List Bool) (a : PolyExpr) (hα : ∀ n, (α n).length ≤ a.eval n) :
+    ∃ B : NUPPT, ∀ n w r, B.runAtL n w r = [BinArith.eqW (pairEncode (pairSndD w) (α n))] := by
+  have hf : PolyTimeComputable fun z =>
+      [BinArith.eqW (pairEncode (pairSndD (NUPPT.inArg z)) (NUPPT.inAdvice z))] :=
+    BinArith.polyTimeComputable_eqW.comp' ((polyTimeComputable_pairSndD.comp'
+      NUPPT.polyTimeComputable_inArg).pairEncode NUPPT.polyTimeComputable_inAdvice)
+  refine ⟨NUPPT.ofPolyTime hf (.const 0) a α hα, fun n w r => ?_⟩
+  rw [NUPPT.runAtL_ofPolyTime]
+  simp only [NUPPT.advInput_eq, ← NUPPT.layout_eq, NUPPT.inArg_layout, NUPPT.inAdvice_layout]
+
+end TCSlib.Cryptography.SecureComputation.ComposeProb
diff --git a/TCSlib/Cryptography/SecureComputation/ComposeSecurity/Assembly.lean b/TCSlib/Cryptography/SecureComputation/ComposeSecurity/Assembly.lean
new file mode 100644
index 000000000..8b8f7cb97
--- /dev/null
+++ b/TCSlib/Cryptography/SecureComputation/ComposeSecurity/Assembly.lean
@@ -0,0 +1,292 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Efficiency
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Assembling a view of the composed protocol from views of the runs
+
+The post-processing of the simulators and reductions of the composition theorem
+[Gol04, §7.3.1, proof of Theorem 7.3.3]: a party's view of `H.compose ρ` is its common input, its
+input, its tape (the `main`-tape followed by one `ρ`-tape per run) and its received messages
+(the other party's run messages at the pairs, with fillers, the leading fillers and the main
+phase). Given a word `V j` per run that reads as an encoded view of `ρ`
+(`⟨⟨x, z⟩, ⟨r, encodeMsgs received⟩⟩`, `View.encode`), `asmView` assembles such a view: the run
+tapes are cut or padded to `ρ`'s coin length, and the received run messages are placed at the
+pairs where the other party moves (the `k`-th message received at the `k`-th such pair, `p / 2`).
+
+## Main definitions
+
+* `ComposeSim.segW`: the pair chunks of one run, from the run's encoded received messages.
+* `ComposeSim.asmView`: the assembled encoded view; `ComposeSim.asmW` its word form.
+
+## Main results
+
+* `ComposeSim.moverIsV_beq_iff`, `length_filter_mover`, `getD_filter_map_mover`: the parity of
+  the pairs at which a party moves, and the position of a run message among them.
+* `ComposeSim.polyTimeComputable_asmW`: the assembly is polynomial-time.
+
+## References
+
+* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
+  University Press, 2004, §7.3.1 (the proof of Theorem 7.3.3).
+-/
+
+namespace TCSlib.Cryptography.SecureComputation.ComposeSim
+
+open Complexity Turing Complexity.StateLoop TCSlib.Cryptography.EncodingMachines ComposeMachines
+
+/-! ### The pairs at which a party moves -/
+
+/-- **The mover test is a parity**: `moverIsV vF q == b` iff `q % 2 = (if vF == b then 0 else 1)`
+(`moverIsV_def`). -/
+theorem moverIsV_beq_iff (vF b : Bool) (q : ℕ) :
+    (moverIsV vF q == b) = true ↔ q % 2 = (if vF == b then 0 else 1) := by
+  rw [moverIsV_def]
+  rcases Nat.mod_two_eq_zero_or_one q with h | h <;> cases vF <;> cases b <;> simp [h]
+
+/-- The number of `q < p` with `q % 2 = d` (for `d ≤ 1`) is `(p + 1 − d) / 2`. -/
+theorem length_filter_mod_two {d : ℕ} (hd : d ≤ 1) :
+    ∀ p, ((List.range p).filter fun q => q % 2 == d).length = (p + 1 - d) / 2
+  | 0 => by
+    rw [List.range_zero, List.filter_nil, List.length_nil]
+    omega
+  | p + 1 => by
+    rw [List.range_succ, List.filter_append, List.length_append, length_filter_mod_two hd p,
+      List.filter_singleton]
+    by_cases h : p % 2 = d
+    · rw [show (p % 2 == d) = true from beq_iff_eq.2 h, cond_true, List.length_singleton]
+      omega
+    · rw [show (p % 2 == d) = false from beq_eq_false_iff_ne.2 h, cond_false, List.length_nil]
+      omega
+
+/-- **The number of moves of a party before its move `p`** is `p / 2`: if
+`moverIsV vF p == b`, then `|{q < p : moverIsV vF q == b}| = p / 2` (`moverIsV_beq_iff`,
+`length_filter_mod_two`). -/
+theorem length_filter_mover (vF b : Bool) {p : ℕ} (hp : (moverIsV vF p == b) = true) :
+    ((List.range p).filter fun q => moverIsV vF q == b).length = p / 2 := by
+  have hd : (if vF == b then 0 else 1) ≤ 1 := by split_ifs <;> omega
+  have hpar := (moverIsV_beq_iff vF b p).1 hp
+  have hfilt : ((List.range p).filter fun q => moverIsV vF q == b) =
+      (List.range p).filter fun q => q % 2 == (if vF == b then 0 else 1) := by
+    refine List.filter_congr fun q _ => ?_
+    rw [Bool.eq_iff_iff, moverIsV_beq_iff]
+    exact beq_iff_eq.symm
+  rw [hfilt, length_filter_mod_two hd]
+  split_ifs at hpar ⊢ <;> omega
+
+/-- **A run message at its position**: for `p < R` with `moverIsV vF p == b`, entry `p / 2` of
+the messages `f q` at the `q < R` with `moverIsV vF q == b` is `f p`
+(`length_filter_mover`). -/
+theorem getD_filter_map_mover (vF b : Bool) (f : ℕ → List Bool) {R p : ℕ} (hpR : p < R)
+    (hp : (moverIsV vF p == b) = true) :
+    (((List.range R).filter fun q => moverIsV vF q == b).map f).getD (p / 2) [] = f p := by
+  obtain ⟨d, rfl⟩ : ∃ d, R = p + 1 + d := ⟨R - (p + 1), by omega⟩
+  rw [List.range_add, List.range_succ, List.filter_append, List.filter_append,
+    List.filter_singleton, hp, cond_true, List.map_append, List.map_append, List.map_singleton,
+    List.append_assoc, List.getD_eq_getElem?_getD, List.getElem?_append_right (by
+      rw [List.length_map, length_filter_mover vF b hp]), List.length_map,
+    length_filter_mover vF b hp, Nat.sub_self, List.singleton_append, List.getElem?_cons_zero,
+    Option.getD_some]
+
+/-- Padding a word of the right length is the identity: `|w| = L → padTo L w = w`. -/
+theorem padTo_of_length {L : ℕ} {w : List Bool} (h : w.length = L) : padTo L w = w := by
+  rw [padTo_eq, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
+
+/-- A concatenation over `range a` is one over `range b` when `a = b` (no rewriting inside the
+chunks): `a = b → (range a).flatMap f = (range b).flatMap f`. -/
+theorem flatMap_range_congr {a b : ℕ} (h : a = b) (f : ℕ → List Bool) :
+    (List.range a).flatMap f = (List.range b).flatMap f := by
+  subst h
+  rfl
+
+/-! ### One run's chunks -/
+
+/-- **The pair chunks of one run**, from the encoded received messages `e` of the run's view:
+for `p < R`, the chunk `⟨m_p, []⟩` with `m_p` the message received at the `p / 2`-th of the pairs
+where the other party moves (`moverIsV vF p == b`) and `[]` (a filler) at the others:
+`segW vF b R e = (range R).flatMap fun p =>
+⟨if moverIsV vF p == b then pairFstD (pairSndD^[p / 2] e) else [], []⟩`. -/
+def segW (vF b : Bool) (R : ℕ) (e : List Bool) : List Bool :=
+  (List.range R).flatMap fun p =>
+    pairEncode (if moverIsV vF p == b then pairFstD (pairSndD^[p / 2] e) else []) []
+
+/-- The defining equation of `segW` (see `segW`).
+`segW vF b R e = (List.range R).flatMap fun p => pairEncode (if moverIsV vF p == b then pairFstD
+(pairSndD^[p / 2] e) else []) []`. -/
+theorem segW_eq (vF b : Bool) (R : ℕ) (e : List Bool) :
+    segW vF b R e = (List.range R).flatMap fun p =>
+      pairEncode (if moverIsV vF p == b then pairFstD (pairSndD^[p / 2] e) else []) [] := rfl
+
+/-- **`segW` on a real run**: if the run's received messages are the messages `f q` at the
+`q < R` with `moverIsV vF q == b`, the chunks are `⟨f p, []⟩` at those pairs and `⟨[], []⟩` at
+the others:
+`segW vF b R (encodeMsgs (filter … (range R)).map f) =
+(range R).flatMap fun p => ⟨if moverIsV vF p == b then f p else [], []⟩`
+(`msgAt_encodeMsgs`, `getD_filter_map_mover`). -/
+theorem segW_encodeMsgs (vF b : Bool) (R : ℕ) (f : ℕ → List Bool) :
+    segW vF b R (Strategy.encodeMsgs (((List.range R).filter fun q => moverIsV vF q == b).map f)) =
+      (List.range R).flatMap fun p =>
+        pairEncode (if moverIsV vF p == b then f p else []) [] := by
+  rw [segW_eq]
+  refine List.flatMap_congr fun p hp => ?_
+  by_cases h : (moverIsV vF p == b) = true
+  · rw [if_pos h, if_pos h, msgAt_encodeMsgs, getD_filter_map_mover vF b f (List.mem_range.1 hp) h]
+  · rw [if_neg h, if_neg h]
+
+/-! ### The assembled view -/
+
+/-- **The assembled encoded view** of a party of `H.compose ρ` (`n = |x₁|`, `L = calls(n)`,
+`R = rounds(n)`, `c = cρ(n)`), from its common input `x₁`, input `xin`, `main`-tape `mt`, encoded
+main-phase messages `me`, the number `lead` of leading fillers it receives, and one word `V j`
+per run read as an encoded `ρ`-view: the view `⟨⟨x₁, xin⟩, ⟨mt ++ τ, E⟩⟩` with the tape
+`τ = (range L).flatMap fun j => padTo c (tape of V j)` and the messages
+`E = (range L).flatMap (fun j => segW vF b R (messages of V j)) ++ encodeMsgs [[]]^lead ++ me`. -/
+def asmView (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ) (x₁ xin mt me : List Bool)
+    (V : ℕ → List Bool) : List Bool :=
+  pairEncode (pairEncode x₁ xin)
+    (pairEncode (mt ++ (List.range (calls.eval x₁.length)).flatMap fun j =>
+        padTo (cρ.eval x₁.length) (pairFstD (pairSndD (V j))))
+      ((List.range (calls.eval x₁.length)).flatMap (fun j =>
+          segW vF b (rounds.eval x₁.length) (pairSndD (pairSndD (V j)))) ++
+        Strategy.encodeMsgs (List.replicate lead []) ++ me))
+
+/-- The defining equation of `asmView` (see `asmView`).
+`asmView calls rounds cρ vF b lead x₁ xin mt me V = pairEncode (pairEncode x₁ xin) (pairEncode (mt
+++ (List.range (calls.eval x₁.length)).flatMap fun j => padTo (cρ.eval x₁.length) (pairFstD
+(pairSndD (V j)))) ((List.range (calls.eval …`. -/
+theorem asmView_eq (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ)
+    (x₁ xin mt me : List Bool) (V : ℕ → List Bool) :
+    asmView calls rounds cρ vF b lead x₁ xin mt me V =
+      pairEncode (pairEncode x₁ xin)
+        (pairEncode (mt ++ (List.range (calls.eval x₁.length)).flatMap fun j =>
+            padTo (cρ.eval x₁.length) (pairFstD (pairSndD (V j))))
+          ((List.range (calls.eval x₁.length)).flatMap (fun j =>
+              segW vF b (rounds.eval x₁.length) (pairSndD (pairSndD (V j)))) ++
+            Strategy.encodeMsgs (List.replicate lead []) ++ me)) := rfl
+
+/-- `asmView` depends on the run words only below `L`: if `V j = V' j` for `j < calls(|x₁|)`, the
+assembled views agree. -/
+theorem asmView_congr (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ)
+    (x₁ xin mt me : List Bool) {V V' : ℕ → List Bool}
+    (h : ∀ j < calls.eval x₁.length, V j = V' j) :
+    asmView calls rounds cρ vF b lead x₁ xin mt me V =
+      asmView calls rounds cρ vF b lead x₁ xin mt me V' := by
+  have h₁ : ((List.range (calls.eval x₁.length)).flatMap fun j =>
+      padTo (cρ.eval x₁.length) (pairFstD (pairSndD (V j)))) =
+      (List.range (calls.eval x₁.length)).flatMap fun j =>
+        padTo (cρ.eval x₁.length) (pairFstD (pairSndD (V' j))) :=
+    List.flatMap_congr fun j hj => by rw [h j (List.mem_range.1 hj)]
+  have h₂ : ((List.range (calls.eval x₁.length)).flatMap fun j =>
+      segW vF b (rounds.eval x₁.length) (pairSndD (pairSndD (V j)))) =
+      (List.range (calls.eval x₁.length)).flatMap fun j =>
+        segW vF b (rounds.eval x₁.length) (pairSndD (pairSndD (V' j))) :=
+    List.flatMap_congr fun j hj => by rw [h j (List.mem_range.1 hj)]
+  rw [asmView_eq, asmView_eq, h₁, h₂]
+
+/-- **The assembly in word form**: on `w = ⟨⟨⟨x₁, xin⟩, ⟨mt, me⟩⟩, VL⟩`, `asmView` with the run
+words `V j = pairFstD (pairSndD^[j] VL)` (the entries of an encoded list,
+`msgAt_encodeMsgs`). -/
+def asmW (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ) (w : List Bool) : List Bool :=
+  asmView calls rounds cρ vF b lead (pairFstD (pairFstD (pairFstD w)))
+    (pairSndD (pairFstD (pairFstD w))) (pairFstD (pairSndD (pairFstD w)))
+    (pairSndD (pairSndD (pairFstD w))) fun j => pairFstD (pairSndD^[j] (pairSndD w))
+
+/-- The defining equation of `asmW` (see `asmW`).
+`asmW calls rounds cρ vF b lead w = asmView calls rounds cρ vF b lead (pairFstD (pairFstD (pairFstD
+w))) (pairSndD (pairFstD (pairFstD w))) (pairFstD (pairSndD (pairFstD w))) (pairSndD (pairSndD
+(pairFstD w))) fun j => pairFstD …`. -/
+theorem asmW_eq (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ) (w : List Bool) :
+    asmW calls rounds cρ vF b lead w =
+      asmView calls rounds cρ vF b lead (pairFstD (pairFstD (pairFstD w)))
+        (pairSndD (pairFstD (pairFstD w))) (pairFstD (pairSndD (pairFstD w)))
+        (pairSndD (pairSndD (pairFstD w))) fun j => pairFstD (pairSndD^[j] (pairSndD w)) := rfl
+
+/-- `asmW` on its word: `asmW … ⟨⟨⟨x₁, xin⟩, ⟨mt, me⟩⟩, VL⟩ =
+asmView … x₁ xin mt me (fun j => pairFstD (pairSndD^[j] VL))`. -/
+theorem asmW_pairEncode (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ)
+    (x₁ xin mt me VL : List Bool) :
+    asmW calls rounds cρ vF b lead
+        (pairEncode (pairEncode (pairEncode x₁ xin) (pairEncode mt me)) VL) =
+      asmView calls rounds cρ vF b lead x₁ xin mt me fun j => pairFstD (pairSndD^[j] VL) := by
+  rw [asmW_eq]
+  simp only [pairFstD_pairEncode, pairSndD_pairEncode]
+
+/-- **`segW` is polynomial-time** on `⟨1^R, e⟩` words given by polynomial-time maps
+(`polyTimeComputable_flatMap_range` over `p < R`, the mover test `polyTimeComputable_moverW`,
+`p / 2` by `divNum_poly`, the message by `iterSnd_poly`). -/
+theorem polyTimeComputable_segW (vF b : Bool) {R : List Bool → ℕ} {e : List Bool → List Bool}
+    (hR : PolyTimeComputable fun z => List.replicate (R z) true) (he : PolyTimeComputable e) :
+    PolyTimeComputable fun z => segW vF b (R z) (e z) := by
+  have hhalf : PolyTimeComputable fun v => List.replicate ((pairFstD v).length / 2) true :=
+    (divNum_poly (unaryLength_poly polyTimeComputable_pairFstD) (unaryConst_poly 2)).congr
+      fun v => by rw [divNum_eq]
+  have hmsg := polyTimeComputable_pairFstD.comp'
+    (iterSnd_poly (he.comp' polyTimeComputable_pairSndD) hhalf)
+  have hchunk : PolyTimeComputable fun v =>
+      pairEncode (if moverIsV vF (pairFstD v).length == b then
+        pairFstD (pairSndD^[(pairFstD v).length / 2] (e (pairSndD v))) else []) [] :=
+    (polyTimeComputable_ite ((polyTimeComputable_moverW vF b).congr fun v => moverW_eq vF b v)
+      hmsg (polyTimeComputable_const [])).pairEncode (polyTimeComputable_const [])
+  exact (polyTimeComputable_flatMap_range hchunk hR).congr fun z => (segW_eq vF b (R z) (e z)).symm
+
+/-- **The assembly is polynomial-time**: `PolyTimeComputable (asmW calls rounds cρ vF b lead)`.
+
+**Proof sketch.** The components `x₁`, `xin`, `mt`, `me` are projections. The tape part and the
+message part are concatenations over the unary count `calls(|x₁|)`
+(`polyTimeComputable_flatMap_range`) of a padded tape (`padTo_poly`) and of `segW`
+(`polyTimeComputable_segW`) of the run word `pairFstD (pairSndD^[j] VL)` (`iterSnd_poly`),
+followed by constant fillers and `me`; the word is `asmView` of these (`asmW_eq`,
+`asmView_eq`). -/
+theorem polyTimeComputable_asmW (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ) :
+    PolyTimeComputable (asmW calls rounds cρ vF b lead) := by
+  have hx₁ : PolyTimeComputable fun w => pairFstD (pairFstD (pairFstD w)) :=
+    polyTimeComputable_pairFstD.comp'
+      (polyTimeComputable_pairFstD.comp' polyTimeComputable_pairFstD)
+  have hxin : PolyTimeComputable fun w => pairSndD (pairFstD (pairFstD w)) :=
+    polyTimeComputable_pairSndD.comp'
+      (polyTimeComputable_pairFstD.comp' polyTimeComputable_pairFstD)
+  have hmt : PolyTimeComputable fun w => pairFstD (pairSndD (pairFstD w)) :=
+    polyTimeComputable_pairFstD.comp'
+      (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairFstD)
+  have hme : PolyTimeComputable fun w => pairSndD (pairSndD (pairFstD w)) :=
+    polyTimeComputable_pairSndD.comp'
+      (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairFstD)
+  -- the run word `V j` from `v = ⟨1^j, w⟩`
+  have hV : PolyTimeComputable fun v =>
+      pairFstD (pairSndD^[(pairFstD v).length] (pairSndD (pairSndD v))) :=
+    polyTimeComputable_pairFstD.comp' (iterSnd_poly
+      (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD)
+      (unaryLength_poly polyTimeComputable_pairFstD))
+  have hn : PolyTimeComputable fun v =>
+      List.replicate (pairFstD (pairFstD (pairFstD (pairSndD v)))).length true :=
+    unaryLength_poly (hx₁.comp' polyTimeComputable_pairSndD)
+  have htape : PolyTimeComputable fun v =>
+      padTo (cρ.eval (pairFstD (pairFstD (pairFstD (pairSndD v)))).length)
+        (pairFstD (pairSndD (pairFstD (pairSndD^[(pairFstD v).length]
+          (pairSndD (pairSndD v)))))) :=
+    padTo_poly ((polyTimeComputable_pairFstD.comp' polyTimeComputable_pairSndD).comp' hV)
+      (unaryPolyOf_poly cρ hn)
+  have hseg : PolyTimeComputable fun v =>
+      segW vF b (rounds.eval (pairFstD (pairFstD (pairFstD (pairSndD v)))).length)
+        (pairSndD (pairSndD (pairFstD (pairSndD^[(pairFstD v).length]
+          (pairSndD (pairSndD v)))))) :=
+    polyTimeComputable_segW vF b (unaryPolyOf_poly rounds hn)
+      ((polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD).comp' hV)
+  have hL := unaryPolyOf_poly calls (unaryLength_poly hx₁)
+  have hT := polyTimeComputable_flatMap_range (E := fun w j =>
+    padTo (cρ.eval (pairFstD (pairFstD (pairFstD w))).length)
+      (pairFstD (pairSndD (pairFstD (pairSndD^[j] (pairSndD w)))))) htape hL
+  have hS := polyTimeComputable_flatMap_range (E := fun w j =>
+    segW vF b (rounds.eval (pairFstD (pairFstD (pairFstD w))).length)
+      (pairSndD (pairSndD (pairFstD (pairSndD^[j] (pairSndD w)))))) hseg hL
+  exact (((hx₁.pairEncode hxin).pairEncode ((hmt.append hT).pairEncode
+    ((hS.append (polyTimeComputable_const _)).append hme)))).congr fun w => by
+      rw [asmW_eq, asmView_eq]
+
+end TCSlib.Cryptography.SecureComputation.ComposeSim
diff --git a/TCSlib/Cryptography/SecureComputation/ComposeSecurity/Bounds.lean b/TCSlib/Cryptography/SecureComputation/ComposeSecurity/Bounds.lean
new file mode 100644
index 000000000..2456794be
--- /dev/null
+++ b/TCSlib/Cryptography/SecureComputation/ComposeSecurity/Bounds.lean
@@ -0,0 +1,96 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Machines
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Polynomial length bounds
+
+The advice of a non-uniform reduction has polynomially bounded length (`NUPPT.advice_length`). The
+reductions of the composition theorem [Gol04, §7.3.1, proof of Theorem 7.3.3] hard-wire views and
+outputs of executions, so their lengths must be bounded by a polynomial in `n`. This file collects
+the lengths of the encodings (`encodeMsgs`, the machine layouts), of the transcripts, and of the
+outputs of machines and efficient strategies.
+
+## Main results
+
+* `ComposeBound.length_encodeMsgs_le`, `length_transcriptWith_fst_le`, `_snd_le`.
+* `ComposeBound.length_runAt_le`, `Efficient.length_next_le`, `length_ilayout`.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §2.1 (non-uniform PPT machines, Definition 26.8) and §4.4 (time complexity of interactive
+  machines).
+-/
+
+namespace TCSlib.Cryptography.SecureComputation.ComposeBound
+
+open Complexity Turing
+
+/-! ### Lengths of encodings and outputs -/
+
+/-- **A transcript has at most `rounds` messages per party**:
+`|(π.transcriptWith P' x y z r).1| ≤ π.rounds(|x|)` (`Compose.exec_eq_map`). -/
+theorem length_transcriptWith_fst_le (π : Protocol) (P' : Strategy) (x y z : List Bool)
+    (r : π.ExecCoins P' x) : (π.transcriptWith P' x y z r).1.length ≤ π.rounds.eval x.length := by
+  rw [Protocol.transcriptWith_eq, Compose.exec_eq_map, List.length_map]
+  exact (List.length_filter_le _ _).trans (List.length_range).le
+
+/-- The verifier's half: `|(π.transcriptWith P' x y z r).2| ≤ π.rounds(|x|)`. -/
+theorem length_transcriptWith_snd_le (π : Protocol) (P' : Strategy) (x y z : List Bool)
+    (r : π.ExecCoins P' x) : (π.transcriptWith P' x y z r).2.length ≤ π.rounds.eval x.length := by
+  rw [Protocol.transcriptWith_eq, Compose.exec_eq_map, List.length_map]
+  exact (List.length_filter_le _ _).trans (List.length_range).le
+
+/-- **The length of an encoded history**: if every message has at most `c` bits,
+`|encodeMsgs l| ≤ |l| (2c + 2)` (`encodeMsgs_eq_flatMap`, `BinArith.length_encWords_le`). -/
+theorem length_encodeMsgs_le (l : List (List Bool)) (c : ℕ) (h : ∀ w ∈ l, w.length ≤ c) :
+    (Strategy.encodeMsgs l).length ≤ l.length * (2 * c + 2) := by
+  rw [ComposeMachines.encodeMsgs_eq_flatMap, ← BinArith.encWords_def]
+  exact BinArith.length_encWords_le l c h
+
+/-- **The length of a machine layout**:
+`|layout u y α r| = 2(2(2|u| + 2 + |y|) + 2 + |α|) + 2 + |r|`
+(`NUPPT.layout_eq`, `length_pairEncode`). -/
+theorem length_layout (u y α r : List Bool) :
+    (NUPPT.layout u y α r).length = 2 * (2 * (2 * u.length + 2 + y.length) + 2 + α.length) + 2 +
+      r.length := by
+  rw [NUPPT.layout_eq, length_pairEncode, length_pairEncode, length_pairEncode]
+
+/-- **The output of a machine is polynomially long**:
+`|A.runAt n y r| ≤ A.Ct (|layout 1^n y (A.advice n) ⟦r⟧| + 1)^A.ct`
+(`NUPPT.output_length_le`, `NUPPT.runAtL_eq_output_layout`). -/
+theorem length_runAt_le (A : NUPPT) (n : ℕ) (y : List Bool) (r : A.Coins n) :
+    (A.runAt n y r).length ≤ A.Ct * (2 * (2 * (2 * n + 2 + y.length) + 2 +
+      (A.advice n).length) + 2 + A.coinLen n + 1) ^ A.ct := by
+  have h := A.output_length_le (NUPPT.layout (List.replicate n true) y (A.advice n) (List.ofFn r))
+  rw [NUPPT.timeBound_def, length_layout, List.length_replicate, List.length_ofFn] at h
+  rw [NUPPT.runAt_eq, NUPPT.runAtL_eq_output_layout]
+  exact h
+
+/-- **The next message of an efficient strategy is polynomially long** in the length of its
+activation's layout: for some `C, c`, `|S.next x z r hist| ≤ C (|GI.ilayout x z hist r| + 1)^c`
+(`ComposeMachines.Efficient.exists_polyTime`, `PolyTimeComputable.output_length_le`). -/
+theorem Efficient.length_next_le {S : Strategy} (h : S.Efficient) :
+    ∃ C c : ℕ, ∀ x z r hist, (S.next x z r hist).length ≤
+      C * ((GI.ilayout x z hist r).length + 1) ^ c := by
+  obtain ⟨F, hF, hnext⟩ := ComposeMachines.Efficient.exists_polyTime h
+  obtain ⟨C, c, hC⟩ := hF.output_length_le
+  exact ⟨C, c, fun x z r hist => by rw [hnext]; exact hC _⟩
+
+/-- **The length of a strategy layout**: `|GI.ilayout x z hist r| =
+2(2(2|x| + 2 + (2(2|x| + 2 + |z|) + 2 + |encodeMsgs hist|)) + 2) + 2 + |r|`. -/
+theorem length_ilayout (x z : List Bool) (hist : List (List Bool)) (r : List Bool) :
+    (GI.ilayout x z hist r).length =
+      2 * (2 * (2 * x.length + 2 + (2 * (2 * x.length + 2 + z.length) + 2 +
+        (Strategy.encodeMsgs hist).length)) + 2) + 2 + r.length := by
+  rw [GI.ilayout_def, length_layout, List.length_replicate, length_pairEncode, length_pairEncode,
+    List.length_nil, Nat.add_zero]
+
+end TCSlib.Cryptography.SecureComputation.ComposeBound
diff --git a/TCSlib/Cryptography/SecureComputation/ComposeSecurity/Chain.lean b/TCSlib/Cryptography/SecureComputation/ComposeSecurity/Chain.lean
new file mode 100644
index 000000000..e9f647eaa
--- /dev/null
+++ b/TCSlib/Cryptography/SecureComputation/ComposeSecurity/Chain.lean
@@ -0,0 +1,263 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Probability
+import TCSlib.Cryptography.Pseudorandom.Indistinguishability
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The hybrid argument over the runs
+
+Step 3 of the proof of the composition theorem [Gol04, §7.3.1, proof of Theorem 7.3.3], in a
+generic form. A sample is `Φ m V`, built from a seed `m : M` and one word `V j` per run `j < L`.
+In the real sample run `j` is `real m j x_j` for an independent seed `x_j : X`; in the simulated
+sample it is `sim m j s_j` for an independent `s_j : S`. The hybrid `i` (`hybV`) takes the first
+`i` runs simulated and the others real, on the joint seed `(m, (x_j, s_j)_j)`. Neighbouring
+hybrids differ in run `i` only, and resampling that run's seeds (`exists_hyb_step`, with the
+published `acceptProb_update`) bounds their gap by the gap at fixed other coordinates (`plugV`:
+run `i` replaced by a given word). Summing (`abs_sub_le_sum_hybrids`) gives `abs_chain_le`.
+
+## Main definitions
+
+* `ComposeProb.hybV`: the run words of hybrid `i`; `ComposeProb.plugV`: with run `i` replaced.
+
+## Main results
+
+* `ComposeProb.exists_hyb_step`: one step of the hybrid argument.
+* `ComposeProb.abs_chain_le`: the real and the simulated samples are within `L · g` when every
+  step at fixed other coordinates is within `g`.
+* `ComposeProb.getD_plug`: the word list of the reduction's template.
+
+## References
+
+* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
+  University Press, 2004, §7.3.1 (the proof of Theorem 7.3.3).
+* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley, draft of
+  22 January 2026, §3.2 (hybrid arguments).
+-/
+
+namespace TCSlib.Cryptography.SecureComputation.ComposeProb
+
+open Finset
+
+section Chain
+
+variable {M X S γ ρ : Type*} {L : ℕ}
+
+/-- **The run words of hybrid `i`** on the seed `ω = (m, (x_j, s_j)_j)`: run `j < L` is
+`sim m j s_j` for `j < i` and `real m j x_j` otherwise; `[]` for `j ≥ L`. -/
+def hybV (real : M → Fin L → X → List Bool) (sim : M → Fin L → S → List Bool) (i : ℕ)
+    (ω : M × (Fin L → X × S)) (j : ℕ) : List Bool :=
+  if h : j < L then
+    (if j < i then sim ω.1 ⟨j, h⟩ (ω.2 ⟨j, h⟩).2 else real ω.1 ⟨j, h⟩ (ω.2 ⟨j, h⟩).1)
+  else []
+
+/-- The defining equation of `hybV` (see `hybV`).
+`hybV real sim i ω j = if h : j < L then (if j < i then sim ω.1 ⟨j, h⟩ (ω.2 ⟨j, h⟩).2 else real ω.1
+⟨j, h⟩ (ω.2 ⟨j, h⟩).1) else []`. -/
+theorem hybV_eq (real : M → Fin L → X → List Bool) (sim : M → Fin L → S → List Bool) (i : ℕ)
+    (ω : M × (Fin L → X × S)) (j : ℕ) :
+    hybV real sim i ω j =
+      if h : j < L then
+        (if j < i then sim ω.1 ⟨j, h⟩ (ω.2 ⟨j, h⟩).2 else real ω.1 ⟨j, h⟩ (ω.2 ⟨j, h⟩).1)
+      else [] := rfl
+
+/-- **Hybrid `i` with run `i` replaced by the word `v`**: `plugV real sim i a v j = v` for
+`j = i` and `hybV real sim i a j` otherwise. -/
+def plugV (real : M → Fin L → X → List Bool) (sim : M → Fin L → S → List Bool) (i : ℕ)
+    (a : M × (Fin L → X × S)) (v : List Bool) (j : ℕ) : List Bool :=
+  if j = i then v else hybV real sim i a j
+
+/-- The defining equation of `plugV` (see `plugV`).
+`plugV real sim i a v j = if j = i then v else hybV real sim i a j`. -/
+theorem plugV_eq (real : M → Fin L → X → List Bool) (sim : M → Fin L → S → List Bool) (i : ℕ)
+    (a : M × (Fin L → X × S)) (v : List Bool) (j : ℕ) :
+    plugV real sim i a v j = if j = i then v else hybV real sim i a j := rfl
+
+/-- Hybrid `i` with run `i` reseeded by `(x, s)` has the real run `i` on `x`:
+`hybV i (m, update u i (x, s)) = plugV i (m, u) (real m i x)`. -/
+theorem hybV_update (real : M → Fin L → X → List Bool) (sim : M → Fin L → S → List Bool)
+    (i : Fin L) (m : M) (u : Fin L → X × S) (y : X × S) :
+    hybV real sim i (m, Function.update u i y) = plugV real sim i (m, u) (real m i y.1) := by
+  funext j
+  rw [hybV_eq, plugV_eq, hybV_eq]
+  by_cases hji : j = i
+  · subst hji
+    rw [dif_pos i.2, if_neg (lt_irrefl _), if_pos rfl]
+    simp only [Fin.eta, Function.update_self]
+  · rw [if_neg hji]
+    by_cases hj : j < L
+    · have hne : (⟨j, hj⟩ : Fin L) ≠ i := fun h => hji (congrArg Fin.val h)
+      rw [dif_pos hj, dif_pos hj]
+      simp only [Function.update_of_ne hne]
+    · rw [dif_neg hj, dif_neg hj]
+
+/-- Hybrid `i + 1` with run `i` reseeded by `(x, s)` has the simulated run `i` on `s`:
+`hybV (i + 1) (m, update u i (x, s)) = plugV i (m, u) (sim m i s)`. -/
+theorem hybV_succ_update (real : M → Fin L → X → List Bool) (sim : M → Fin L → S → List Bool)
+    (i : Fin L) (m : M) (u : Fin L → X × S) (y : X × S) :
+    hybV real sim ((i : ℕ) + 1) (m, Function.update u i y) =
+      plugV real sim i (m, u) (sim m i y.2) := by
+  funext j
+  rw [hybV_eq, plugV_eq, hybV_eq]
+  by_cases hji : j = i
+  · subst hji
+    rw [dif_pos i.2, if_pos (Nat.lt_succ_self _), if_pos rfl]
+    simp only [Fin.eta, Function.update_self]
+  · rw [if_neg hji]
+    by_cases hj : j < L
+    · have hne : (⟨j, hj⟩ : Fin L) ≠ i := fun h => hji (congrArg Fin.val h)
+      have hlt : j < (i : ℕ) + 1 ↔ j < i := by omega
+      rw [dif_pos hj, dif_pos hj]
+      simp only [Function.update_of_ne hne, hlt]
+    · rw [dif_neg hj, dif_neg hj]
+
+variable [Fintype M] [Fintype X] [Fintype S] [Fintype ρ]
+
+variable [Nonempty M] [Nonempty X] [Nonempty S]
+
+/-- **One step of the hybrid argument**: for `i < L` there are fixed other coordinates `a` such
+that the gap between hybrids `i` and `i + 1` is at most the gap between run `i` real and run `i`
+simulated, the others as in `a`:
+`|Pr[D(Φ(hyb i))] − Pr[D(Φ(hyb (i+1)))]| ≤
+|Pr_x[D(Φ a.1 (plugV i a (real a.1 i x)))] − Pr_s[D(Φ a.1 (plugV i a (sim a.1 i s)))]|`.
+
+**Proof sketch.** Overwrite run `i`'s seeds with a fresh `y : X × S` (`acceptProb_update`, after
+moving `m` last and the fresh seed last, `acceptProb_comp_equiv`): hybrid `k` becomes
+`hyb k (m, update u i y)`, which for `k = i` is the plugged real run on `y.1` and for `k = i + 1`
+the plugged simulated run on `y.2` (`hybV_update`, `hybV_succ_update`). Fix the coordinates
+`(u, m)` at the worst value (`exists_abs_sub_le_sections`) and drop the unused half of `y`
+(`acceptProb_fst`, `acceptProb_snd`). -/
+theorem exists_hyb_step (real : M → Fin L → X → List Bool) (sim : M → Fin L → S → List Bool)
+    (Φ : M → (ℕ → List Bool) → γ) (D : γ → ρ → Bool) (i : Fin L) :
+    ∃ a : M × (Fin L → X × S),
+      |acceptProb (fun ω => Φ ω.1 (hybV real sim i ω)) D -
+          acceptProb (fun ω => Φ ω.1 (hybV real sim ((i : ℕ) + 1) ω)) D| ≤
+        |acceptProb (fun x => Φ a.1 (plugV real sim i a (real a.1 i x))) D -
+          acceptProb (fun s => Φ a.1 (plugV real sim i a (sim a.1 i s))) D| := by
+  classical
+  -- overwrite run `i`'s seeds with a fresh seed; the fixed coordinates `(u, m)` come first
+  have hk : ∀ k : ℕ, acceptProb (fun ω => Φ ω.1 (hybV real sim k ω)) D =
+      acceptProb (fun w : ((Fin L → X × S) × M) × (X × S) =>
+        Φ w.1.2 (hybV real sim k (w.1.2, Function.update w.1.1 i w.2))) D := by
+    intro k
+    refine (acceptProb_comp_equiv (Equiv.prodComm (Fin L → X × S) M)
+      (fun ω : M × (Fin L → X × S) => Φ ω.1 (hybV real sim k ω)) D).symm.trans ?_
+    refine (acceptProb_update i (fun u m => Φ m (hybV real sim k (m, u))) D).symm.trans ?_
+    exact (acceptProb_comp_equiv (Equiv.prodComm ((Fin L → X × S) × M) (X × S)) _ D).symm
+  rw [hk i, hk ((i : ℕ) + 1)]
+  obtain ⟨a, ha⟩ := exists_abs_sub_le_sections
+    (fun w : ((Fin L → X × S) × M) × (X × S) =>
+      Φ w.1.2 (hybV real sim i (w.1.2, Function.update w.1.1 i w.2)))
+    (fun w : ((Fin L → X × S) × M) × (X × S) =>
+      Φ w.1.2 (hybV real sim ((i : ℕ) + 1) (w.1.2, Function.update w.1.1 i w.2))) D
+  refine ⟨(a.2, a.1), ha.trans (le_of_eq ?_)⟩
+  simp only [hybV_update, hybV_succ_update]
+  rw [acceptProb_fst (fun x => Φ a.2 (plugV real sim i (a.2, a.1) (real a.2 i x))) D,
+    acceptProb_snd (fun s => Φ a.2 (plugV real sim i (a.2, a.1) (sim a.2 i s))) D]
+
+omit [Nonempty M] [Nonempty X] in
+/-- Hybrid `0` is the real sample, the simulator seeds unused:
+`Pr[D(Φ(hyb 0))] = Pr_{(m, x)}[D(Φ m (real runs on x))]`. -/
+theorem acceptProb_hyb_zero (real : M → Fin L → X → List Bool) (sim : M → Fin L → S → List Bool)
+    (Φ : M → (ℕ → List Bool) → γ) (D : γ → ρ → Bool) :
+    acceptProb (fun ω => Φ ω.1 (hybV real sim 0 ω)) D =
+      acceptProb (fun z : M × (Fin L → X) =>
+        Φ z.1 fun j => if h : j < L then real z.1 ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) D := by
+  let e : M × (Fin L → X × S) ≃ (M × (Fin L → X)) × (Fin L → S) :=
+    { toFun := fun ω => ((ω.1, fun j => (ω.2 j).1), fun j => (ω.2 j).2)
+      invFun := fun z => (z.1.1, fun j => (z.1.2 j, z.2 j))
+      left_inv := fun _ => rfl
+      right_inv := fun _ => rfl }
+  rw [← acceptProb_fst (τ := Fin L → S) (fun z : M × (Fin L → X) =>
+      Φ z.1 fun j => if h : j < L then real z.1 ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) D,
+    ← acceptProb_comp_equiv e]
+  congr 1
+
+omit [Nonempty M] [Nonempty S] in
+/-- Hybrid `L` is the simulated sample, the real seeds unused:
+`Pr[D(Φ(hyb L))] = Pr_{(m, s)}[D(Φ m (simulated runs on s))]`.
+
+**Proof sketch.** Relabel the seed `(m, (x_j, s_j)_j)` as `((m, s), x)` (an equivalence,
+`acceptProb_comp_equiv`) and drop the unused `x` (`acceptProb_fst`); in hybrid `L` every
+run `j < L` is simulated (`hybV_eq`). -/
+theorem acceptProb_hyb_last (real : M → Fin L → X → List Bool) (sim : M → Fin L → S → List Bool)
+    (Φ : M → (ℕ → List Bool) → γ) (D : γ → ρ → Bool) :
+    acceptProb (fun ω => Φ ω.1 (hybV real sim L ω)) D =
+      acceptProb (fun z : M × (Fin L → S) =>
+        Φ z.1 fun j => if h : j < L then sim z.1 ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) D := by
+  let e : M × (Fin L → X × S) ≃ (M × (Fin L → S)) × (Fin L → X) :=
+    { toFun := fun ω => ((ω.1, fun j => (ω.2 j).2), fun j => (ω.2 j).1)
+      invFun := fun z => (z.1.1, fun j => (z.2 j, z.1.2 j))
+      left_inv := fun _ => rfl
+      right_inv := fun _ => rfl }
+  rw [← acceptProb_fst (τ := Fin L → X) (fun z : M × (Fin L → S) =>
+      Φ z.1 fun j => if h : j < L then sim z.1 ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) D,
+    ← acceptProb_comp_equiv e]
+  congr 1
+  funext ω
+  congr 1
+  funext j
+  rw [hybV_eq]
+  by_cases h : j < L
+  · rw [dif_pos h, dif_pos h, if_pos h]
+    rfl
+  · rw [dif_neg h, dif_neg h]
+
+/-- **The hybrid argument over the runs**: if for every run `i < L` and all fixed other
+coordinates `a` the plugged real and simulated runs are within `g`, then the real sample and the
+simulated sample are within `L · g`:
+`|Pr_{(m, x)}[D(Φ m (real runs))] − Pr_{(m, s)}[D(Φ m (simulated runs))]| ≤ L · g`.
+
+**Proof sketch.** The two samples are hybrids `0` and `L` (`acceptProb_hyb_zero`,
+`acceptProb_hyb_last`); telescope (`abs_sub_le_sum_hybrids`) and bound each of the `L` steps by
+`g` (`exists_hyb_step`). -/
+theorem abs_chain_le (real : M → Fin L → X → List Bool) (sim : M → Fin L → S → List Bool)
+    (Φ : M → (ℕ → List Bool) → γ) (D : γ → ρ → Bool) (g : ℝ)
+    (hg : ∀ (i : Fin L) (a : M × (Fin L → X × S)),
+      |acceptProb (fun x => Φ a.1 (plugV real sim i a (real a.1 i x))) D -
+        acceptProb (fun s => Φ a.1 (plugV real sim i a (sim a.1 i s))) D| ≤ g) :
+    |acceptProb (fun z : M × (Fin L → X) =>
+        Φ z.1 fun j => if h : j < L then real z.1 ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) D -
+      acceptProb (fun z : M × (Fin L → S) =>
+        Φ z.1 fun j => if h : j < L then sim z.1 ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) D| ≤ L * g := by
+  have h0 := acceptProb_hyb_zero real sim Φ D
+  have hL := acceptProb_hyb_last real sim Φ D
+  rw [← h0, ← hL]
+  have htel := abs_sub_le_sum_hybrids
+    (fun k => acceptProb (fun ω => Φ ω.1 (hybV real sim k ω)) D) L
+  have hsum : ∑ k ∈ range L, |acceptProb (fun ω => Φ ω.1 (hybV real sim k ω)) D -
+      acceptProb (fun ω => Φ ω.1 (hybV real sim (k + 1) ω)) D| ≤ ∑ _k ∈ range L, g :=
+    sum_le_sum fun k hk => by
+      obtain ⟨a, ha⟩ := exists_hyb_step real sim Φ D ⟨k, mem_range.1 hk⟩
+      exact ha.trans (hg _ a)
+  refine htel.trans (hsum.trans (le_of_eq ?_))
+  rw [sum_const, card_range, nsmul_eq_mul]
+
+end Chain
+
+/-- **The template's word list**: for `i < L` and `j < L`, entry `j` of
+`[f 0, …, f (i−1), v, f (i+1), …, f (L−1)]` is `v` for `j = i` and `f j` otherwise. -/
+theorem getD_plug (f : ℕ → List Bool) (v : List Bool) {i L j : ℕ} (hi : i < L) (hj : j < L) :
+    ((List.range i).map f ++ v :: (List.range (L - (i + 1))).map fun k => f (i + 1 + k)).getD j
+        [] = if j = i then v else f j := by
+  rw [List.getD_eq_getElem?_getD]
+  rcases lt_trichotomy j i with h | h | h
+  · rw [List.getElem?_append_left (by rw [List.length_map, List.length_range]; exact h),
+      List.getElem?_map, List.getElem?_range h, Option.map_some, Option.getD_some,
+      if_neg (Nat.ne_of_lt h)]
+  · subst h
+    rw [List.getElem?_append_right (by rw [List.length_map, List.length_range]),
+      List.length_map, List.length_range, Nat.sub_self, List.getElem?_cons_zero,
+      Option.getD_some, if_pos rfl]
+  · obtain ⟨k, rfl⟩ : ∃ k, j = i + 1 + k := ⟨j - (i + 1), by omega⟩
+    rw [List.getElem?_append_right (by rw [List.length_map, List.length_range]; omega),
+      List.length_map, List.length_range, show i + 1 + k - i = k + 1 by omega,
+      List.getElem?_cons_succ, List.getElem?_map, List.getElem?_range (by omega),
+      Option.map_some, Option.getD_some, if_neg (by omega)]
+
+end TCSlib.Cryptography.SecureComputation.ComposeProb
diff --git a/TCSlib/Cryptography/SecureComputation/ComposeSecurity/Correct.lean b/TCSlib/Cryptography/SecureComputation/ComposeSecurity/Correct.lean
new file mode 100644
index 000000000..bb03a3e5b
--- /dev/null
+++ b/TCSlib/Cryptography/SecureComputation/ComposeSecurity/Correct.lean
@@ -0,0 +1,208 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Accept
+import TCSlib.Cryptography.HardcoreBit.Basic
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Correct answers of the runs
+
+Step 2 of the proof of the composition theorem [Gol04, §7.3.1, proof of Theorem 7.3.3]. The
+output clause of honest-but-curious security makes a secure protocol correct: a distinguisher
+that compares the other party's output in the sample with the ideal output on the worst-case
+inputs of length `n`, given as advice, shows that each party's output differs from its ideal
+output with negligible probability, uniformly over the inputs (`ComposeProb.exists_correct`).
+By the union bound over the calls, every run of the composed protocol gives the ideal answers
+except with probability `L(n)` times that bound (`HybridProtocol.uprob_not_goodRuns_le`).
+
+## Main results
+
+* `ComposeProb.exists_correct`: a secure protocol computes its functionality except with
+  negligible probability.
+* `HybridProtocol.inA_val`, `inB_val`: the call inputs at a call index.
+* `HybridProtocol.uprob_not_goodRuns_le`: the bad event of the statistical switch.
+
+## References
+
+* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
+  University Press, 2004, §7.3.1 (the proof of Theorem 7.3.3).
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §6.2, Definition 155.1.
+-/
+
+namespace TCSlib.Cryptography.SecureComputation
+
+open Finset Complexity Turing TCSlib.Cryptography
+
+namespace ComposeProb
+
+/-- **A secure protocol computes its functionality** (the output clause of [PS10,
+Definition 155.1]): if `ρ` has simulators `S_A`, `S_B` against every non-uniform PPT
+distinguisher, there is a negligible `ε_c` with, for all `n` and all inputs `x`, `y` of `G`'s
+lengths, `Pr_t[ρ.outP ≠ ⟦f_A(x, y)⟧ ∨ ρ.outV ≠ ⟦f_B(x, y)⟧] ≤ ε_c(n)` on common input `1^n`.
+
+**Proof sketch.** For Alice's output take the inputs `w_n` maximizing
+`Pr_t[outP ≠ ⟦f_A⟧]` at each `n`, and the test machine accepting when the second component of
+its sample is `⟦f_A(w_n)⟧` (`exists_test`; advice of `G.outA(n)` bits). On Bob's ideal sample
+at `w_n` it accepts with probability `1` (the second component is `⟦f_A(w_n)⟧`); on the real one
+with `Pr_t[outP = ⟦f_A(w_n)⟧]` (`acceptProb_test`). So `Pr_t[outP ≠ ⟦f_A⟧] ≤
+Pr_t[outP(w_n) ≠ ⟦f_A(w_n)⟧] = 1 − Pr_t[outP(w_n) = ⟦f_A(w_n)⟧] ≤ ε_A(n)` (`uprob_not`).
+Likewise for Bob's output on Alice's side; take `ε_c = ε_A + ε_B` (`uprob_or_le`). -/
+theorem exists_correct {G : Functionality} {ρ : Protocol} (SA SB : NUPPT)
+    (hS : ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
+      ∀ n (x : Fin (G.inA.eval n) → Bool) (y : Fin (G.inB.eval n) → Bool),
+        distAdv (G.realA ρ n x y) (G.idealA SA n x y) (D.distinguisherL n) ≤ ε n ∧
+          distAdv (G.realB ρ n x y) (G.idealB SB n x y) (D.distinguisherL n) ≤ ε n) :
+    ∃ εc : ℕ → ℝ, Negligible εc ∧
+      ∀ n (x : Fin (G.inA.eval n) → Bool) (y : Fin (G.inB.eval n) → Bool),
+        uprob (fun t : ρ.ExecCoins ρ.P (List.replicate n true) =>
+          ρ.outP (List.replicate n true) (List.ofFn x) (List.ofFn y) t ≠
+              List.ofFn (G.f n x y).1 ∨
+            ρ.outV ρ.P (List.replicate n true) (List.ofFn x) (List.ofFn y) t ≠
+              List.ofFn (G.f n x y).2) ≤ εc n := by
+  -- the worst-case inputs for each output
+  have hmax : ∀ (n : ℕ) (q : (Fin (G.inA.eval n) → Bool) × (Fin (G.inB.eval n) → Bool) → ℝ),
+      ∃ w, ∀ w', q w' ≤ q w := fun n q => by
+    obtain ⟨w, -, hw⟩ := exists_max_image univ q univ_nonempty
+    exact ⟨w, fun w' => hw w' (mem_univ w')⟩
+  choose wA hwA using fun n => hmax n fun w => uprob fun t : ρ.ExecCoins ρ.P
+    (List.replicate n true) => ρ.outP (List.replicate n true) (List.ofFn w.1) (List.ofFn w.2) t ≠
+      List.ofFn (G.f n w.1 w.2).1
+  choose wB hwB using fun n => hmax n fun w => uprob fun t : ρ.ExecCoins ρ.P
+    (List.replicate n true) => ρ.outV ρ.P (List.replicate n true) (List.ofFn w.1)
+      (List.ofFn w.2) t ≠ List.ofFn (G.f n w.1 w.2).2
+  obtain ⟨BA, hBA⟩ := exists_test (fun n => List.ofFn (G.f n (wA n).1 (wA n).2).1) G.outA
+    fun n => by rw [List.length_ofFn]
+  obtain ⟨BB, hBB⟩ := exists_test (fun n => List.ofFn (G.f n (wB n).1 (wB n).2).2) G.outB
+    fun n => by rw [List.length_ofFn]
+  obtain ⟨εA, hεA, hA⟩ := hS BA
+  obtain ⟨εB, hεB, hB⟩ := hS BB
+  refine ⟨fun n => εA n + εB n, hεA.add hεB, fun n x y => (uprob_or_le _ _).trans
+    (add_le_add ((hwA n (x, y)).trans ?_) ((hwB n (x, y)).trans ?_))⟩
+  · -- Alice's output, through Bob's samples
+    have h1 : acceptProb (G.realB ρ n (wA n).1 (wA n).2) (BA.distinguisherL n) =
+        uprob fun t : ρ.ExecCoins ρ.P (List.replicate n true) =>
+          ρ.outP (List.replicate n true) (List.ofFn (wA n).1) (List.ofFn (wA n).2) t =
+            List.ofFn (G.f n (wA n).1 (wA n).2).1 := by
+      rw [acceptProb_test _ BA n _ (hBA n)]
+      simp only [Functionality.realB_eq, pairSndD_pairEncode, BinArith.eqW_pairEncode,
+        decide_eq_true_iff]
+    have h2 : acceptProb (G.idealB SB n (wA n).1 (wA n).2) (BA.distinguisherL n) = 1 := by
+      rw [acceptProb_test _ BA n _ (hBA n)]
+      simp only [Functionality.idealB_eq, pairSndD_pairEncode, BinArith.eqW_pairEncode,
+        decide_true]
+      exact uprob_true
+    have h3 := (hA n (wA n).1 (wA n).2).2
+    rw [distAdv_def, h1, h2, abs_le] at h3
+    have h4 := uprob_not fun t : ρ.ExecCoins ρ.P (List.replicate n true) =>
+      ρ.outP (List.replicate n true) (List.ofFn (wA n).1) (List.ofFn (wA n).2) t =
+        List.ofFn (G.f n (wA n).1 (wA n).2).1
+    exact (le_of_eq h4).trans (by linarith [h3.1])
+  · -- Bob's output, through Alice's samples
+    have h1 : acceptProb (G.realA ρ n (wB n).1 (wB n).2) (BB.distinguisherL n) =
+        uprob fun t : ρ.ExecCoins ρ.P (List.replicate n true) =>
+          ρ.outV ρ.P (List.replicate n true) (List.ofFn (wB n).1) (List.ofFn (wB n).2) t =
+            List.ofFn (G.f n (wB n).1 (wB n).2).2 := by
+      rw [acceptProb_test _ BB n _ (hBB n)]
+      simp only [Functionality.realA_eq, pairSndD_pairEncode, BinArith.eqW_pairEncode,
+        decide_eq_true_iff]
+    have h2 : acceptProb (G.idealA SA n (wB n).1 (wB n).2) (BB.distinguisherL n) = 1 := by
+      rw [acceptProb_test _ BB n _ (hBB n)]
+      simp only [Functionality.idealA_eq, pairSndD_pairEncode, BinArith.eqW_pairEncode,
+        decide_true]
+      exact uprob_true
+    have h3 := (hB n (wB n).1 (wB n).2).1
+    rw [distAdv_def, h1, h2, abs_le] at h3
+    have h4 := uprob_not fun t : ρ.ExecCoins ρ.P (List.replicate n true) =>
+      ρ.outV ρ.P (List.replicate n true) (List.ofFn (wB n).1) (List.ofFn (wB n).2) t =
+        List.ofFn (G.f n (wB n).1 (wB n).2).2
+    exact (le_of_eq h4).trans (by linarith [h3.1])
+
+end ComposeProb
+
+namespace HybridProtocol
+
+variable {G : Functionality} (H : HybridProtocol G) (ρ : Protocol)
+
+/-- Alice's input to a call `j : Fin calls(n)` is `⟦callA(n, zA, rA, j)⟧` (`inA_eq`).
+`H.inA n zA rA j = List.ofFn (H.callA n zA rA j)`. -/
+theorem inA_val (n : ℕ) (zA rA : List Bool) (j : Fin (H.calls.eval n)) :
+    H.inA n zA rA j = List.ofFn (H.callA n zA rA j) := by
+  rw [inA_eq, dif_pos j.2]
+
+/-- Bob's input to a call `j : Fin calls(n)` is `⟦callB(n, zB, rB, j)⟧` (`inB_eq`).
+`H.inB n zB rB j = List.ofFn (H.callB n zB rB j)`. -/
+theorem inB_val (n : ℕ) (zB rB : List Bool) (j : Fin (H.calls.eval n)) :
+    H.inB n zB rB j = List.ofFn (H.callB n zB rB j) := by
+  rw [inB_eq, dif_pos j.2]
+
+/-- **The bad event of the statistical switch**: if on common input `1^n` every pair of inputs of
+`G`'s lengths makes a party's `ρ`-output wrong with probability at most `ε_c`, then over the
+`main`-tapes and the run tapes some run gives a wrong answer with probability at most
+`calls(n) · ε_c`.
+`uprob (fun z : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) => ¬
+H.GoodRuns ρ n zA zB z.1 z.2) ≤ H.calls.eval n * εc`.
+
+**Proof sketch.** `¬ GoodRuns` is the union over the calls `j` of the event that run `j`'s
+outputs are wrong (`goodRuns_iff`; `uprob_exists_le`). For fixed `main`-tapes `m` that event
+concerns the run tapes `t j` only, on the call inputs of `m`, which have `G`'s lengths
+(`inA_val`, `inB_val`): its probability is at most `ε_c` (`HardcoreBit.pushesUniform_eval`),
+hence so is its average over `m` (`uprob_prod`, `HardcoreBit.uexp_mono`,
+`HardcoreBit.uexp_const`). -/
+theorem uprob_not_goodRuns_le (n : ℕ) (zA zB : List Bool) (εc : ℝ)
+    (hc : ∀ (xA : Fin (G.inA.eval n) → Bool) (yB : Fin (G.inB.eval n) → Bool),
+      uprob (fun t : ρ.ExecCoins ρ.P (List.replicate n true) =>
+        ρ.outP (List.replicate n true) (List.ofFn xA) (List.ofFn yB) t ≠
+            List.ofFn (G.f n xA yB).1 ∨
+          ρ.outV ρ.P (List.replicate n true) (List.ofFn xA) (List.ofFn yB) t ≠
+            List.ofFn (G.f n xA yB).2) ≤ εc) :
+    uprob (fun z : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) =>
+      ¬ H.GoodRuns ρ n zA zB z.1 z.2) ≤ H.calls.eval n * εc := by
+  -- the event that run `j` is wrong, on the run tape `t'`
+  let bad : H.Coins n → Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) → Prop :=
+    fun m j t' =>
+      ρ.outP (List.replicate n true) (List.ofFn (H.callA n zA (List.ofFn m.1) j))
+          (List.ofFn (H.callB n zB (List.ofFn m.2) j)) t' ≠
+        List.ofFn (G.f n (H.callA n zA (List.ofFn m.1) j) (H.callB n zB (List.ofFn m.2) j)).1 ∨
+      ρ.outV ρ.P (List.replicate n true) (List.ofFn (H.callA n zA (List.ofFn m.1) j))
+          (List.ofFn (H.callB n zB (List.ofFn m.2) j)) t' ≠
+        List.ofFn (G.f n (H.callA n zA (List.ofFn m.1) j) (H.callB n zB (List.ofFn m.2) j)).2
+  have hsub : ∀ z : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)),
+      ¬ H.GoodRuns ρ n zA zB z.1 z.2 → ∃ j ∈ (univ : Finset (Fin (H.calls.eval n))),
+        bad z.1 j (z.2 j) := by
+    intro z hz
+    rw [goodRuns_iff] at hz
+    push_neg at hz
+    obtain ⟨j, hj⟩ := hz
+    refine ⟨j, mem_univ j, ?_⟩
+    show _ ∨ _
+    rw [← H.inA_val n zA (List.ofFn z.1.1) j, ← H.inB_val n zB (List.ofFn z.1.2) j]
+    by_cases h : ρ.outP (List.replicate n true) (H.inA n zA (List.ofFn z.1.1) j)
+        (H.inB n zB (List.ofFn z.1.2) j) (z.2 j) =
+      List.ofFn (G.f n (H.callA n zA (List.ofFn z.1.1) j) (H.callB n zB (List.ofFn z.1.2) j)).1
+    · exact Or.inr (hj h)
+    · exact Or.inl h
+  calc uprob (fun z : H.Coins n × (Fin (H.calls.eval n) →
+        ρ.ExecCoins ρ.P (List.replicate n true)) => ¬ H.GoodRuns ρ n zA zB z.1 z.2)
+      ≤ uprob (fun z : H.Coins n × (Fin (H.calls.eval n) →
+          ρ.ExecCoins ρ.P (List.replicate n true)) => ∃ j ∈ univ, bad z.1 j (z.2 j)) :=
+        uprob_mono hsub
+    _ ≤ ∑ j ∈ (univ : Finset (Fin (H.calls.eval n))),
+          uprob (fun z : H.Coins n × (Fin (H.calls.eval n) →
+            ρ.ExecCoins ρ.P (List.replicate n true)) => bad z.1 j (z.2 j)) :=
+        uprob_exists_le _ _
+    _ ≤ ∑ _j ∈ (univ : Finset (Fin (H.calls.eval n))), εc := sum_le_sum fun j _ => by
+        rw [uprob_prod]
+        refine (HardcoreBit.uexp_mono fun m => ?_).trans_eq (HardcoreBit.uexp_const (εc))
+        rw [(HardcoreBit.pushesUniform_eval j).uprob_eq (bad m j)]
+        exact hc _ _
+    _ = H.calls.eval n * εc := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
+
+end HybridProtocol
+
+end TCSlib.Cryptography.SecureComputation
diff --git a/TCSlib/Cryptography/SecureComputation/ComposeSecurity/Efficiency.lean b/TCSlib/Cryptography/SecureComputation/ComposeSecurity/Efficiency.lean
new file mode 100644
index 000000000..def3258ef
--- /dev/null
+++ b/TCSlib/Cryptography/SecureComputation/ComposeSecurity/Efficiency.lean
@@ -0,0 +1,596 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Machines
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The composed parties as polynomial-time functions of the machine layout
+
+The efficiency half of the composition theorem [Gol04, §7.3.1, the protocol of Theorem 7.3.3]:
+Alice's and Bob's next-message functions in `H.compose ρ` (`HybridProtocol.composeP`,
+`composeV`) are polynomial-time functions of the machine layout
+`GI.ilayout x z hist r = ⟨⟨⟨1^{|x|}, ⟨⟨x, z⟩, encodeMsgs hist⟩⟩, []⟩, r⟩`, when `main`'s and `ρ`'s
+strategies are efficient and the call inputs are polynomial-time (`HybridProtocol.PolyTime`,
+`Functionality.PolyTime`).
+
+The pieces are shared by the two parties and generic in the strategies:
+* `ComposeMachines.runW`: one activation of a `ρ`-party in run `j` after `p` pairs of the run,
+  on the call input (recomputed from the `main`-tape), the run tape cut from the coins and the
+  run's messages read from the history at the interleaved pairs (`polyTimeComputable_slots`);
+* `ComposeMachines.ansW`: the `L(n)` run outputs, each padded to the answer length, concatenated;
+* `ComposeMachines.mainW`: one activation of a `main`-party on its input paired with the answers,
+  its `main`-tape and the messages after the runs.
+
+## Main definitions
+
+* `ComposeMachines.runW`, `ansW`, `mainW`, `moverW`: the shared pieces.
+* `HybridProtocol.composePW`, `composeVW`: the two parties on the layout.
+
+## Main results
+
+* `ComposeMachines.runW_ilayout`, `ansW_ilayout`, `mainW_ilayout`: the pieces on a layout.
+* `ComposeMachines.polyTimeComputable_runW`, `polyTimeComputable_ansW`,
+  `polyTimeComputable_mainW`: the pieces are polynomial-time.
+* `HybridProtocol.composeP_next_eq_composePW`, `composeV_next_eq_composeVW`: the composed
+  parties are the layout functions.
+* `HybridProtocol.polyTimeComputable_composePW`, `polyTimeComputable_composeVW`: and these are
+  polynomial-time.
+
+## References
+
+* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
+  University Press, 2004, §7.3.1 (the composed protocol of Theorem 7.3.3).
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §4.4 (interactive machines and their time complexity, pp. 114–116).
+-/
+
+namespace TCSlib.Cryptography.SecureComputation
+
+open Complexity Turing Complexity.StateLoop TCSlib.Cryptography.EncodingMachines
+
+namespace ComposeMachines
+
+/-! ### The mover test -/
+
+/-- **The mover test in unary**: `moverW vF b w = [moverIsV vF |fst w| = b]` (whether the
+party moving at position `|fst w|` of `ρ` is the verifier, compared with `b`). -/
+def moverW (vF b : Bool) (w : List Bool) : List Bool :=
+  [moverIsV vF (pairFstD w).length == b]
+
+/-- The defining equation of `moverW`: `moverW vF b w = [moverIsV vF |fst w| == b]`. -/
+theorem moverW_eq (vF b : Bool) (w : List Bool) :
+    moverW vF b w = [moverIsV vF (pairFstD w).length == b] := rfl
+
+/-- The mover test is polynomial-time: the parity of the unary length `|fst w|`
+(`EncodingMachines.modNum_poly`, `eqTest_poly`), compared with constants
+(`Complexity.polyTimeComputable_ite`).
+`PolyTimeComputable (moverW vF b)`. -/
+theorem polyTimeComputable_moverW (vF b : Bool) : PolyTimeComputable (moverW vF b) := by
+  have hpar : PolyTimeComputable fun w =>
+      [decide (modNum (pairFstD w).length 2 = (if vF then 0 else 1))] :=
+    eqTest_poly (modNum_poly (unaryLength_poly polyTimeComputable_pairFstD) (unaryConst_poly 2))
+      (unaryConst_poly _)
+  have h := polyTimeComputable_ite hpar (polyTimeComputable_const [b])
+    (polyTimeComputable_const [!b])
+  refine h.congr fun w => ?_
+  rw [moverW_eq, moverIsV_def, modNum_eq]
+  rcases Nat.mod_two_eq_zero_or_one (pairFstD w).length with hp | hp <;>
+    cases vF <;> cases b <;> simp [hp]
+
+/-! ### One activation of a `ρ`-party in a run -/
+
+/-- **One `ρ`-activation in run `j` after `p` pairs of the run**, on the word
+`u = ⟨1^j, ⟨1^p, w⟩⟩` with `w` a layout (common input `x`, input `z`, messages `M`, coins `r`,
+`n = |x|`): the `ρ`-party's machine `Fρ` on the layout with common input `x`, input
+`fcall ⟨1^n, ⟨z, ⟨r_{<c₀(n)}, 1^j⟩⟩⟩` (the call input from the `main`-tape), the messages
+of the run read at the pairs `R(n)·j + q`, `q < p`, selected by `moverIsV vF q = b`, and the run
+tape `r[c₀(n) + j·c(n), c₀(n) + (j + 1)·c(n))`. -/
+def runW (Fρ fcall : List Bool → List Bool) (c₀ c R : PolyExpr) (vF b : Bool)
+    (u : List Bool) : List Bool :=
+  Fρ (NUPPT.layout (List.replicate (GI.argX (pairSndD (pairSndD u))).length true)
+    (pairEncode (pairEncode (GI.argX (pairSndD (pairSndD u)))
+        (fcall (pairEncode (List.replicate (GI.argX (pairSndD (pairSndD u))).length true)
+          (pairEncode (GI.argZ (pairSndD (pairSndD u)))
+            (pairEncode ((NUPPT.inCoins (pairSndD (pairSndD u))).take
+                (c₀.eval (GI.argX (pairSndD (pairSndD u))).length))
+              (List.replicate (pairFstD u).length true))))))
+      ((List.range (pairFstD (pairSndD u)).length).flatMap fun q =>
+        if moverIsV vF q == b then
+          pairEncode (pairFstD (pairSndD^[R.eval (GI.argX (pairSndD (pairSndD u))).length *
+            (pairFstD u).length + q] (GI.argM (pairSndD (pairSndD u))))) []
+        else []))
+    []
+    (((NUPPT.inCoins (pairSndD (pairSndD u))).drop
+        (c₀.eval (GI.argX (pairSndD (pairSndD u))).length +
+          (pairFstD u).length * c.eval (GI.argX (pairSndD (pairSndD u))).length)).take
+      (c.eval (GI.argX (pairSndD (pairSndD u))).length)))
+
+/-- The defining equation of `runW` (see `runW`).
+`runW Fρ fcall c₀ c R vF b u = Fρ (NUPPT.layout (List.replicate (GI.argX (pairSndD (pairSndD
+u))).length true) (pairEncode (pairEncode (GI.argX (pairSndD (pairSndD u))) (fcall (pairEncode
+(List.replicate (GI.argX (pairSndD (pairSndD …`. -/
+theorem runW_eq (Fρ fcall : List Bool → List Bool) (c₀ c R : PolyExpr) (vF b : Bool)
+    (u : List Bool) :
+    runW Fρ fcall c₀ c R vF b u =
+      Fρ (NUPPT.layout (List.replicate (GI.argX (pairSndD (pairSndD u))).length true)
+        (pairEncode (pairEncode (GI.argX (pairSndD (pairSndD u)))
+            (fcall (pairEncode (List.replicate (GI.argX (pairSndD (pairSndD u))).length true)
+              (pairEncode (GI.argZ (pairSndD (pairSndD u)))
+                (pairEncode ((NUPPT.inCoins (pairSndD (pairSndD u))).take
+                    (c₀.eval (GI.argX (pairSndD (pairSndD u))).length))
+                  (List.replicate (pairFstD u).length true))))))
+          ((List.range (pairFstD (pairSndD u)).length).flatMap fun q =>
+            if moverIsV vF q == b then
+              pairEncode (pairFstD (pairSndD^[R.eval (GI.argX (pairSndD (pairSndD u))).length *
+                (pairFstD u).length + q] (GI.argM (pairSndD (pairSndD u))))) []
+            else []))
+        []
+        (((NUPPT.inCoins (pairSndD (pairSndD u))).drop
+            (c₀.eval (GI.argX (pairSndD (pairSndD u))).length +
+              (pairFstD u).length * c.eval (GI.argX (pairSndD (pairSndD u))).length)).take
+          (c.eval (GI.argX (pairSndD (pairSndD u))).length))) := rfl
+
+/-- **`runW` on a layout**: on `⟨1^j, ⟨1^p, GI.ilayout x z hist r⟩⟩` it is `Fρ` on the layout of
+the run activation: `runW … ⟨1^j, ⟨1^p, GI.ilayout x z hist r⟩⟩ =
+Fρ (GI.ilayout x (fcall ⟨1^{|x|}, ⟨z, ⟨r_{<c₀}, 1^j⟩⟩⟩) (slotMsgs sel (R·j) p hist)
+(runTape c₀ c j r))` with `sel q = (moverIsV vF q == b)` (`encodeMsgs_slotMsgs`). -/
+theorem runW_ilayout (Fρ fcall : List Bool → List Bool) (c₀ c R : PolyExpr) (vF b : Bool)
+    (x z : List Bool) (hist : List (List Bool)) (r : List Bool) (j p : ℕ) :
+    runW Fρ fcall c₀ c R vF b (pairEncode (List.replicate j true)
+        (pairEncode (List.replicate p true) (GI.ilayout x z hist r))) =
+      Fρ (GI.ilayout x (fcall (pairEncode (List.replicate x.length true)
+          (pairEncode z (pairEncode (r.take (c₀.eval x.length)) (List.replicate j true)))))
+        (Compose.slotMsgs (fun q => moverIsV vF q == b) (R.eval x.length * j) p hist)
+        (Compose.runTape (c₀.eval x.length) (c.eval x.length) j r)) := by
+  rw [runW_eq, pairSndD_pairEncode, pairSndD_pairEncode, pairFstD_pairEncode,
+    pairFstD_pairEncode, List.length_replicate, List.length_replicate, GI.argX_ilayout,
+    GI.argZ_ilayout, GI.argM_ilayout, GI.inCoins_ilayout, GI.ilayout_def, encodeMsgs_slotMsgs,
+    Compose.runTape_eq]
+
+/-- **`runW` is polynomial-time** when `Fρ` and `fcall` are.
+`PolyTimeComputable (runW Fρ fcall c₀ c R vF b)`.
+
+**Proof sketch.** The layout is assembled (`NUPPT.polyTimeComputable_layout`) from the slot
+projections, the unary polynomials `c₀(n)`, `c(n)`, `R(n)` (`unaryPoly_comp`), the call input
+(`fcall` after `pairEncode`), the typed cuts of the coins (`EncodingMachines.truncate_poly`,
+`Complexity.polyTimeComputable_pairDropPoly` at the unary count `c₀(n) + j·c(n)`) and the
+interleaved-slot map at the offset `R(n)·j` (`polyTimeComputable_slots`). -/
+theorem polyTimeComputable_runW {Fρ fcall : List Bool → List Bool} (hFρ : PolyTimeComputable Fρ)
+    (hcall : PolyTimeComputable fcall) (c₀ c R : PolyExpr) (vF b : Bool) :
+    PolyTimeComputable (runW Fρ fcall c₀ c R vF b) := by
+  have hw : PolyTimeComputable fun u => pairSndD (pairSndD u) :=
+    polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD
+  have hx := GI.argX_poly.comp' hw
+  have hn : PolyTimeComputable fun u =>
+      List.replicate (GI.argX (pairSndD (pairSndD u))).length true := unaryLength_poly hx
+  have hj : PolyTimeComputable fun u => List.replicate (pairFstD u).length true :=
+    unaryLength_poly polyTimeComputable_pairFstD
+  have hp : PolyTimeComputable fun u => List.replicate (pairFstD (pairSndD u)).length true :=
+    unaryLength_poly (polyTimeComputable_pairFstD.comp' polyTimeComputable_pairSndD)
+  have hr := NUPPT.polyTimeComputable_inCoins.comp' hw
+  have hc₀ := unaryPoly_comp c₀ hx
+  have hc := unaryPoly_comp c hx
+  have hR := unaryPoly_comp R hx
+  have hinp : PolyTimeComputable fun u => fcall (pairEncode
+      (List.replicate (GI.argX (pairSndD (pairSndD u))).length true)
+      (pairEncode (GI.argZ (pairSndD (pairSndD u)))
+        (pairEncode ((NUPPT.inCoins (pairSndD (pairSndD u))).take
+            (c₀.eval (GI.argX (pairSndD (pairSndD u))).length))
+          (List.replicate (pairFstD u).length true)))) :=
+    hcall.comp' (hn.pairEncode ((GI.argZ_poly.comp' hw).pairEncode
+      ((truncate_poly hr hc₀).pairEncode hj)))
+  have hsel : PolyTimeComputable fun w' => [moverIsV vF (pairFstD w').length == b] :=
+    (polyTimeComputable_moverW vF b).congr fun w' => moverW_eq vF b w'
+  have hslots := polyTimeComputable_slots (sel := fun _ q => moverIsV vF q == b)
+    (off := fun u => R.eval (GI.argX (pairSndD (pairSndD u))).length * (pairFstD u).length)
+    (p := fun u => (pairFstD (pairSndD u)).length)
+    hsel
+    (unaryMul_poly hR hj) hp (GI.argM_poly.comp' hw)
+  have hdrop : PolyTimeComputable fun u => (NUPPT.inCoins (pairSndD (pairSndD u))).drop
+      (c₀.eval (GI.argX (pairSndD (pairSndD u))).length +
+        (pairFstD u).length * c.eval (GI.argX (pairSndD (pairSndD u))).length) :=
+    ((polyTimeComputable_pairDropPoly .var).comp'
+      ((unaryAdd_poly hc₀ (unaryMul_poly hj hc)).pairEncode hr)).congr fun u => by
+        rw [pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var,
+          List.length_replicate]
+  exact (hFρ.comp' (NUPPT.polyTimeComputable_layout hn ((hx.pairEncode hinp).pairEncode hslots)
+    (polyTimeComputable_const []) (truncate_poly hdrop hc))).congr fun u => by
+      rw [runW_eq]
+
+/-! ### The answers -/
+
+/-- **The answers on the layout**: the `L(n)` run outputs of the `ρ`-party (`runW` with
+`p = R(n)`), each padded to `out(n)` bits, concatenated:
+`ansW … w = (range L(n)).flatMap fun j => padTo out(n) (runW … ⟨1^j, ⟨1^{R(n)}, w⟩⟩)`. -/
+def ansW (Fρ fcall : List Bool → List Bool) (c₀ c R L out : PolyExpr) (vF b : Bool)
+    (w : List Bool) : List Bool :=
+  (List.range (L.eval (GI.argX w).length)).flatMap fun j =>
+    padTo (out.eval (GI.argX w).length) (runW Fρ fcall c₀ c R vF b
+      (pairEncode (List.replicate j true)
+        (pairEncode (List.replicate (R.eval (GI.argX w).length) true) w)))
+
+/-- The defining equation of `ansW` (see `ansW`).
+`ansW Fρ fcall c₀ c R L out vF b w = (List.range (L.eval (GI.argX w).length)).flatMap fun j => padTo
+(out.eval (GI.argX w).length) (runW Fρ fcall c₀ c R vF b (pairEncode (List.replicate j true)
+(pairEncode (List.replicate (R.eval (GI.argX …`. -/
+theorem ansW_eq (Fρ fcall : List Bool → List Bool) (c₀ c R L out : PolyExpr) (vF b : Bool)
+    (w : List Bool) :
+    ansW Fρ fcall c₀ c R L out vF b w =
+      (List.range (L.eval (GI.argX w).length)).flatMap fun j =>
+        padTo (out.eval (GI.argX w).length) (runW Fρ fcall c₀ c R vF b
+          (pairEncode (List.replicate j true)
+            (pairEncode (List.replicate (R.eval (GI.argX w).length) true) w))) := rfl
+
+/-- **The answers are polynomial-time** (`polyTimeComputable_flatMap_range` over the unary count
+`L(n)`, with the chunk `padTo_poly` of `polyTimeComputable_runW`).
+`PolyTimeComputable (ansW Fρ fcall c₀ c R L out vF b)`. -/
+theorem polyTimeComputable_ansW {Fρ fcall : List Bool → List Bool} (hFρ : PolyTimeComputable Fρ)
+    (hcall : PolyTimeComputable fcall) (c₀ c R L out : PolyExpr) (vF b : Bool) :
+    PolyTimeComputable (ansW Fρ fcall c₀ c R L out vF b) := by
+  have hw := polyTimeComputable_pairSndD
+  have hx := GI.argX_poly.comp' hw
+  have hchunk : PolyTimeComputable fun v =>
+      padTo (out.eval (GI.argX (pairSndD v)).length) (runW Fρ fcall c₀ c R vF b
+        (pairEncode (List.replicate (pairFstD v).length true)
+          (pairEncode (List.replicate (R.eval (GI.argX (pairSndD v)).length) true)
+            (pairSndD v)))) :=
+    padTo_poly ((polyTimeComputable_runW hFρ hcall c₀ c R vF b).comp
+      ((unaryLength_poly polyTimeComputable_pairFstD).pairEncode
+        ((unaryPoly_comp R hx).pairEncode hw))) (unaryPoly_comp out hx)
+  exact (polyTimeComputable_flatMap_range hchunk (unaryPoly_comp L GI.argX_poly)).congr
+    fun w => rfl
+
+/-! ### One activation of a `main`-party -/
+
+/-- **One `main`-activation on the layout**: the `main`-party's machine `Fm` on the layout with
+common input `x`, input `⟨z, ans w⟩`, the messages after the first `d w` (`pairSndD^[d w] M`)
+and the `main`-tape `r_{<c₀(n)}`. -/
+def mainW (Fm ans : List Bool → List Bool) (d : List Bool → ℕ) (c₀ : PolyExpr) (w : List Bool) :
+    List Bool :=
+  Fm (NUPPT.layout (List.replicate (GI.argX w).length true)
+    (pairEncode (pairEncode (GI.argX w) (pairEncode (GI.argZ w) (ans w)))
+      (pairSndD^[d w] (GI.argM w)))
+    [] ((NUPPT.inCoins w).take (c₀.eval (GI.argX w).length)))
+
+/-- The defining equation of `mainW` (see `mainW`).
+`mainW Fm ans d c₀ w = Fm (NUPPT.layout (List.replicate (GI.argX w).length true) (pairEncode
+(pairEncode (GI.argX w) (pairEncode (GI.argZ w) (ans w))) (pairSndD^[d w] (GI.argM w))) []
+((NUPPT.inCoins w).take (c₀.eval (GI.argX w).length)))`. -/
+theorem mainW_eq (Fm ans : List Bool → List Bool) (d : List Bool → ℕ) (c₀ : PolyExpr)
+    (w : List Bool) :
+    mainW Fm ans d c₀ w =
+      Fm (NUPPT.layout (List.replicate (GI.argX w).length true)
+        (pairEncode (pairEncode (GI.argX w) (pairEncode (GI.argZ w) (ans w)))
+          (pairSndD^[d w] (GI.argM w)))
+        [] ((NUPPT.inCoins w).take (c₀.eval (GI.argX w).length))) := rfl
+
+/-- **`mainW` on a layout**: `mainW Fm ans d c₀ (GI.ilayout x z hist r) =
+Fm (GI.ilayout x ⟨z, ans (GI.ilayout x z hist r)⟩ (hist.drop (d …)) r_{<c₀})`
+(`GI.iterate_pairSndD_encodeMsgs`). -/
+theorem mainW_ilayout (Fm ans : List Bool → List Bool) (d : List Bool → ℕ) (c₀ : PolyExpr)
+    (x z : List Bool) (hist : List (List Bool)) (r : List Bool) :
+    mainW Fm ans d c₀ (GI.ilayout x z hist r) =
+      Fm (GI.ilayout x (pairEncode z (ans (GI.ilayout x z hist r)))
+        (hist.drop (d (GI.ilayout x z hist r))) (r.take (c₀.eval x.length))) := by
+  rw [mainW_eq, GI.argX_ilayout, GI.argZ_ilayout, GI.argM_ilayout, GI.inCoins_ilayout,
+    GI.iterate_pairSndD_encodeMsgs, GI.ilayout_def, GI.ilayout_def]
+
+/-- **`mainW` is polynomial-time** when `Fm`, the answers and the unary drop count are
+(`iterSnd_poly`, `EncodingMachines.truncate_poly`).
+`PolyTimeComputable (mainW Fm ans d c₀)`. -/
+theorem polyTimeComputable_mainW {Fm ans : List Bool → List Bool} (hFm : PolyTimeComputable Fm)
+    (hans : PolyTimeComputable ans) {d : List Bool → ℕ}
+    (hd : PolyTimeComputable fun w => List.replicate (d w) true) (c₀ : PolyExpr) :
+    PolyTimeComputable (mainW Fm ans d c₀) :=
+  (hFm.comp' (NUPPT.polyTimeComputable_layout (unaryLength_poly GI.argX_poly)
+    ((GI.argX_poly.pairEncode (GI.argZ_poly.pairEncode hans)).pairEncode
+      (iterSnd_poly GI.argM_poly hd))
+    (polyTimeComputable_const [])
+    (truncate_poly NUPPT.polyTimeComputable_inCoins (unaryPoly_comp c₀ GI.argX_poly)))).congr
+    fun w => by rw [mainW_eq]
+
+
+/-- **`ansW` on a layout**: the concatenation over `j < L(|x|)` of the padded run outputs
+`padTo out(|x|) (Fρ (GI.ilayout x (fcall ⟨1^{|x|}, ⟨z, ⟨r_{<c₀}, 1^j⟩⟩⟩)
+(slotMsgs sel (R·j) R hist) (runTape c₀ c j r)))` (`runW_ilayout`). -/
+theorem ansW_ilayout (Fρ fcall : List Bool → List Bool) (c₀ c R L out : PolyExpr) (vF b : Bool)
+    (x z : List Bool) (hist : List (List Bool)) (r : List Bool) :
+    ansW Fρ fcall c₀ c R L out vF b (GI.ilayout x z hist r) =
+      (List.range (L.eval x.length)).flatMap fun j =>
+        padTo (out.eval x.length) (Fρ (GI.ilayout x
+          (fcall (pairEncode (List.replicate x.length true)
+            (pairEncode z (pairEncode (r.take (c₀.eval x.length)) (List.replicate j true)))))
+          (Compose.slotMsgs (fun q => moverIsV vF q == b) (R.eval x.length * j)
+            (R.eval x.length) hist)
+          (Compose.runTape (c₀.eval x.length) (c.eval x.length) j r))) := by
+  rw [ansW_eq, GI.argX_ilayout]
+  refine List.flatMap_congr fun j _ => ?_
+  rw [runW_ilayout]
+
+/-- **A concatenation over `Fin L` as a concatenation over `range L`**:
+`(List.ofFn fun j : Fin L => E j).flatten = (List.range L).flatMap E`. -/
+theorem flatten_ofFn_eq_flatMap_range (E : ℕ → List Bool) (L : ℕ) :
+    (List.ofFn fun j : Fin L => E j).flatten = (List.range L).flatMap E := by
+  rw [List.ofFn_eq_map, ← List.map_coe_finRange, List.flatMap_map, List.flatMap_def]
+
+end ComposeMachines
+
+/-! ### The composed parties on the layout -/
+
+namespace HybridProtocol
+
+open ComposeMachines
+
+section Parties
+
+variable {G : Functionality} (H : HybridProtocol G) (ρ : Protocol)
+
+/-- **Alice of `H.compose ρ` on the layout** [Gol04, §7.3.1], given machines `Fρ` for `ρ.P`,
+`Fm` for `main.P` and `fcall` for her call inputs: with `k` the number of messages received
+(`GI.msgCount`), `n = |x|`, `L = calls(n)`, `R = ρ.rounds(n)`:
+- if `k < L·R`: `[]` if `ρ`'s mover `k % R` is Bob, else her `ρ`-move in run `k / R` after
+  `k % R` pairs (`runW`, reading Bob's moves);
+- else, if `main`'s verifier moves first and `k = L·R`: the leading filler `[]`;
+- else her `main`-move on `⟨z, her answers⟩` (`ansW`) and the messages after the first `L·R`
+  (`mainW`). -/
+def composePW (Fρ Fm fcall : List Bool → List Bool) (w : List Bool) : List Bool :=
+  if decide (GI.msgCount (GI.argM w) <
+      H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length) then
+    if moverIsV ρ.verifierFirst (GI.msgCount (GI.argM w) % ρ.rounds.eval (GI.argX w).length) then []
+    else runW Fρ fcall H.main.P.coins ρ.P.coins ρ.rounds ρ.verifierFirst true
+      (pairEncode
+        (List.replicate (GI.msgCount (GI.argM w) / ρ.rounds.eval (GI.argX w).length) true)
+        (pairEncode
+          (List.replicate (GI.msgCount (GI.argM w) % ρ.rounds.eval (GI.argX w).length) true) w))
+  else if (H.main.verifierFirst && decide (GI.msgCount (GI.argM w) =
+      H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length)) then []
+  else mainW Fm (ansW Fρ fcall H.main.P.coins ρ.P.coins ρ.rounds H.calls G.outA
+      ρ.verifierFirst true)
+    (fun w => H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length) H.main.P.coins w
+
+/-- The defining equation of `composePW` (see `composePW`).
+`H.composePW ρ Fρ Fm fcall w = if decide (GI.msgCount (GI.argM w) < H.calls.eval (GI.argX w).length
+* ρ.rounds.eval (GI.argX w).length) then if moverIsV ρ.verifierFirst (GI.msgCount (GI.argM w) %
+ρ.rounds.eval (GI.argX w).length) then [] …`. -/
+theorem composePW_eq (Fρ Fm fcall : List Bool → List Bool) (w : List Bool) :
+    H.composePW ρ Fρ Fm fcall w =
+      if decide (GI.msgCount (GI.argM w) <
+          H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length) then
+        if moverIsV ρ.verifierFirst (GI.msgCount (GI.argM w) % ρ.rounds.eval (GI.argX w).length)
+        then []
+        else runW Fρ fcall H.main.P.coins ρ.P.coins ρ.rounds ρ.verifierFirst true
+          (pairEncode
+            (List.replicate (GI.msgCount (GI.argM w) / ρ.rounds.eval (GI.argX w).length) true)
+            (pairEncode
+              (List.replicate (GI.msgCount (GI.argM w) % ρ.rounds.eval (GI.argX w).length) true) w))
+      else if (H.main.verifierFirst && decide (GI.msgCount (GI.argM w) =
+          H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length)) then []
+      else mainW Fm (ansW Fρ fcall H.main.P.coins ρ.P.coins ρ.rounds H.calls G.outA
+          ρ.verifierFirst true)
+        (fun w => H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length)
+        H.main.P.coins w := rfl
+
+/-- **Bob of `H.compose ρ` on the layout**, given machines `Fρ` for `ρ.V`, `Fm` for `main.V` and
+`fcall` for his call inputs: with `c` the number of messages received and `k = c − 1`:
+- if `k < L·R`: his `ρ`-move in run `k / R` after `k % R` pairs if `ρ`'s mover `k % R` is Bob
+  (`runW`, reading Alice's moves), else `[]`;
+- else his `main`-move on `⟨z, his answers⟩` and the messages after the first `L·R + lead`. -/
+def composeVW (Fρ Fm fcall : List Bool → List Bool) (w : List Bool) : List Bool :=
+  if decide (GI.msgCount (GI.argM w) - 1 <
+      H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length) then
+    if moverIsV ρ.verifierFirst ((GI.msgCount (GI.argM w) - 1) % ρ.rounds.eval (GI.argX w).length)
+    then runW Fρ fcall H.main.V.coins ρ.V.coins ρ.rounds ρ.verifierFirst false
+      (pairEncode
+        (List.replicate ((GI.msgCount (GI.argM w) - 1) / ρ.rounds.eval (GI.argX w).length) true)
+        (pairEncode
+          (List.replicate ((GI.msgCount (GI.argM w) - 1) % ρ.rounds.eval (GI.argX w).length)
+            true) w))
+    else []
+  else mainW Fm (ansW Fρ fcall H.main.V.coins ρ.V.coins ρ.rounds H.calls G.outB
+      ρ.verifierFirst false)
+    (fun w => H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length + H.lead)
+    H.main.V.coins w
+
+/-- The defining equation of `composeVW` (see `composeVW`).
+`H.composeVW ρ Fρ Fm fcall w = if decide (GI.msgCount (GI.argM w) - 1 < H.calls.eval (GI.argX
+w).length * ρ.rounds.eval (GI.argX w).length) then if moverIsV ρ.verifierFirst ((GI.msgCount
+(GI.argM w) - 1) % ρ.rounds.eval (GI.argX w).length) …`. -/
+theorem composeVW_eq (Fρ Fm fcall : List Bool → List Bool) (w : List Bool) :
+    H.composeVW ρ Fρ Fm fcall w =
+      if decide (GI.msgCount (GI.argM w) - 1 <
+          H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length) then
+        if moverIsV ρ.verifierFirst
+          ((GI.msgCount (GI.argM w) - 1) % ρ.rounds.eval (GI.argX w).length)
+        then runW Fρ fcall H.main.V.coins ρ.V.coins ρ.rounds ρ.verifierFirst false
+          (pairEncode
+            (List.replicate ((GI.msgCount (GI.argM w) - 1) / ρ.rounds.eval (GI.argX w).length) true)
+            (pairEncode
+              (List.replicate ((GI.msgCount (GI.argM w) - 1) % ρ.rounds.eval (GI.argX w).length)
+                true) w))
+        else []
+      else mainW Fm (ansW Fρ fcall H.main.V.coins ρ.V.coins ρ.rounds H.calls G.outB
+          ρ.verifierFirst false)
+        (fun w => H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length + H.lead)
+        H.main.V.coins w := rfl
+
+/-- **Alice of `H.compose ρ` is `composePW`**: if `Fρ`, `Fm` compute `ρ.P` and `main.P` on the
+layout and `fcall` computes Alice's call inputs (the `callA` clause of `HybridProtocol.PolyTime`),
+then `(H.composeP ρ).next x z r hist = H.composePW ρ Fρ Fm fcall (GI.ilayout x z hist r)`.
+
+**Proof sketch.** Unfold both sides (`composeP_next`, `composePW_eq`); the number of messages
+read from the layout is `|hist|` (`GI.msgCount_encodeMsgs`). In a run branch `j = k / R < L`, so
+the call input is `runInputA` (`runInputA_of_lt`) and `runW` is `runNextA` (`runW_ilayout`,
+`runNextA_eq`). In the main branch `mainW` is `main.P.next` on the answers read by `ansW`, which
+are `answersFromA` (`ansW_ilayout`, `answersFromA_eq`, `ofFn_padFin`). -/
+theorem composeP_next_eq_composePW {Fρ Fm fcall : List Bool → List Bool}
+    (hFρ : ∀ x z r hist, ρ.P.next x z r hist = Fρ (GI.ilayout x z hist r))
+    (hFm : ∀ x z r hist, H.main.P.next x z r hist = Fm (GI.ilayout x z hist r))
+    (hcall : ∀ n (x r : List Bool) (j : Fin (H.calls.eval n)),
+      fcall (pairEncode (List.replicate n true) (pairEncode x (pairEncode r
+        (List.replicate j true)))) = List.ofFn (H.callA n x r j))
+    (x z r : List Bool) (hist : List (List Bool)) :
+    (H.composeP ρ).next x z r hist = H.composePW ρ Fρ Fm fcall (GI.ilayout x z hist r) := by
+  have hrun : ∀ j p, j < H.calls.eval x.length →
+      H.runNextA ρ x z r hist j p =
+        runW Fρ fcall H.main.P.coins ρ.P.coins ρ.rounds ρ.verifierFirst true
+          (pairEncode (List.replicate j true)
+            (pairEncode (List.replicate p true) (GI.ilayout x z hist r))) := by
+    intro j p hj
+    rw [runW_ilayout, hcall x.length z _ ⟨j, hj⟩, ← H.runInputA_of_lt x z r hj, ← hFρ,
+      runNextA_eq]
+    congr 2
+    funext q
+    rw [beq_true]
+  rw [composeP_next, composePW_eq, GI.argM_ilayout, GI.argX_ilayout, GI.msgCount_encodeMsgs]
+  simp only [decide_eq_true_eq, Bool.and_eq_true]
+  by_cases hk : hist.length < H.calls.eval x.length * ρ.rounds.eval x.length
+  · have hR : 0 < ρ.rounds.eval x.length := Nat.pos_of_ne_zero fun h => by
+      rw [h, Nat.mul_zero] at hk
+      omega
+    have hj : hist.length / ρ.rounds.eval x.length < H.calls.eval x.length :=
+      (Nat.div_lt_iff_lt_mul hR).2 hk
+    rw [if_pos hk, if_pos hk]
+    by_cases hm : moverIsV ρ.verifierFirst (hist.length % ρ.rounds.eval x.length) = true
+    · rw [if_pos hm, if_pos hm]
+    · rw [if_neg hm, if_neg hm, hrun _ _ hj]
+  · rw [if_neg hk, if_neg hk]
+    by_cases hl : H.main.verifierFirst = true ∧
+        hist.length = H.calls.eval x.length * ρ.rounds.eval x.length
+    · rw [if_pos hl, if_pos hl]
+    · rw [if_neg hl, if_neg hl, mainW_ilayout, GI.argX_ilayout, ← hFm, answersFromA_eq,
+        ansW_ilayout,
+        flatten_ofFn_eq_flatMap_range
+          (fun j => List.ofFn (padFin (G.outA.eval x.length)
+            (H.runNextA ρ x z r hist j (ρ.rounds.eval x.length))))]
+      congr 2
+      refine List.flatMap_congr fun j hj => ?_
+      rw [ofFn_padFin, hrun _ _ (List.mem_range.1 hj), runW_ilayout]
+
+/-- **Bob of `H.compose ρ` is `composeVW`**: if `Fρ`, `Fm` compute `ρ.V` and `main.V` on the
+layout and `fcall` computes Bob's call inputs, then
+`(H.composeV ρ).next x z r hist = H.composeVW ρ Fρ Fm fcall (GI.ilayout x z hist r)`.
+
+**Proof sketch.** As `composeP_next_eq_composePW`, with `k = |hist| − 1`, `runNextB`,
+`runInputB_of_lt`, the selector `!moverIsV` (`beq_false`), `answersFromB` and the drop count
+`L·R + lead`. -/
+theorem composeV_next_eq_composeVW {Fρ Fm fcall : List Bool → List Bool}
+    (hFρ : ∀ x z r hist, ρ.V.next x z r hist = Fρ (GI.ilayout x z hist r))
+    (hFm : ∀ x z r hist, H.main.V.next x z r hist = Fm (GI.ilayout x z hist r))
+    (hcall : ∀ n (y r : List Bool) (j : Fin (H.calls.eval n)),
+      fcall (pairEncode (List.replicate n true) (pairEncode y (pairEncode r
+        (List.replicate j true)))) = List.ofFn (H.callB n y r j))
+    (x z r : List Bool) (hist : List (List Bool)) :
+    (H.composeV ρ).next x z r hist = H.composeVW ρ Fρ Fm fcall (GI.ilayout x z hist r) := by
+  have hrun : ∀ j p, j < H.calls.eval x.length →
+      H.runNextB ρ x z r hist j p =
+        runW Fρ fcall H.main.V.coins ρ.V.coins ρ.rounds ρ.verifierFirst false
+          (pairEncode (List.replicate j true)
+            (pairEncode (List.replicate p true) (GI.ilayout x z hist r))) := by
+    intro j p hj
+    rw [runW_ilayout, hcall x.length z _ ⟨j, hj⟩, ← H.runInputB_of_lt x z r hj, ← hFρ,
+      runNextB_eq]
+    congr 2
+    funext q
+    rw [beq_false]
+  rw [composeV_next, composeVW_eq, GI.argM_ilayout, GI.argX_ilayout, GI.msgCount_encodeMsgs]
+  simp only [decide_eq_true_eq]
+  by_cases hk : hist.length - 1 < H.calls.eval x.length * ρ.rounds.eval x.length
+  · have hR : 0 < ρ.rounds.eval x.length := Nat.pos_of_ne_zero fun h => by
+      rw [h, Nat.mul_zero] at hk
+      omega
+    have hj : (hist.length - 1) / ρ.rounds.eval x.length < H.calls.eval x.length :=
+      (Nat.div_lt_iff_lt_mul hR).2 hk
+    rw [if_pos hk, if_pos hk]
+    by_cases hm : moverIsV ρ.verifierFirst ((hist.length - 1) % ρ.rounds.eval x.length) = true
+    · rw [if_pos hm, if_pos hm, hrun _ _ hj]
+    · rw [if_neg hm, if_neg hm]
+  · rw [if_neg hk, if_neg hk, mainW_ilayout, GI.argX_ilayout, ← hFm, answersFromB_eq, ansW_ilayout,
+      flatten_ofFn_eq_flatMap_range
+        (fun j => List.ofFn (padFin (G.outB.eval x.length)
+          (H.runNextB ρ x z r hist j (ρ.rounds.eval x.length))))]
+    congr 2
+    refine List.flatMap_congr fun j hj => ?_
+    rw [ofFn_padFin, hrun _ _ (List.mem_range.1 hj), runW_ilayout]
+
+/-- **`composePW` is polynomial-time** when `Fρ`, `Fm` and `fcall` are.
+`PolyTimeComputable (H.composePW ρ Fρ Fm fcall)`.
+
+**Proof sketch.** Three branches (`Complexity.polyTimeComputable_ite`) on unary tests of the
+message count (`GI.msgCount_poly`) against `L(n)·R(n)` (`ltTest_poly`, `eqTest_poly`), the
+mover test at `k % R` (`polyTimeComputable_moverW`, `modNum_poly`), and the pieces
+`polyTimeComputable_runW` (at `k / R`, `divNum_poly`), `polyTimeComputable_ansW` and
+`polyTimeComputable_mainW`. -/
+theorem polyTimeComputable_composePW {Fρ Fm fcall : List Bool → List Bool}
+    (hFρ : PolyTimeComputable Fρ) (hFm : PolyTimeComputable Fm)
+    (hcall : PolyTimeComputable fcall) : PolyTimeComputable (H.composePW ρ Fρ Fm fcall) := by
+  have hk : PolyTimeComputable fun w => List.replicate (GI.msgCount (GI.argM w)) true :=
+    GI.msgCount_poly.comp' GI.argM_poly
+  have hR := unaryPoly_comp ρ.rounds GI.argX_poly
+  have hLR := unaryMul_poly (unaryPoly_comp H.calls GI.argX_poly) hR
+  have hdiv : PolyTimeComputable fun w =>
+      List.replicate (GI.msgCount (GI.argM w) / ρ.rounds.eval (GI.argX w).length) true :=
+    (divNum_poly hk hR).congr fun w => by rw [divNum_eq]
+  have hmod : PolyTimeComputable fun w =>
+      List.replicate (GI.msgCount (GI.argM w) % ρ.rounds.eval (GI.argX w).length) true :=
+    (modNum_poly hk hR).congr fun w => by rw [modNum_eq]
+  have hmv : PolyTimeComputable fun w =>
+      [moverIsV ρ.verifierFirst (GI.msgCount (GI.argM w) % ρ.rounds.eval (GI.argX w).length)] :=
+    ((polyTimeComputable_moverW ρ.verifierFirst true).comp'
+      (hmod.pairEncode polyTimeComputable_id)).congr fun w => by
+        rw [moverW_eq, pairFstD_pairEncode, List.length_replicate, beq_true]
+  have hrun := (polyTimeComputable_runW hFρ hcall H.main.P.coins ρ.P.coins ρ.rounds
+    ρ.verifierFirst true).comp' (hdiv.pairEncode (hmod.pairEncode polyTimeComputable_id))
+  have hmain := polyTimeComputable_mainW hFm (polyTimeComputable_ansW hFρ hcall H.main.P.coins
+    ρ.P.coins ρ.rounds H.calls G.outA ρ.verifierFirst true) hLR H.main.P.coins
+  have hlead : PolyTimeComputable fun w =>
+      [H.main.verifierFirst && decide (GI.msgCount (GI.argM w) =
+      H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length)] :=
+    polyTimeComputable_and (polyTimeComputable_const [H.main.verifierFirst]) (eqTest_poly hk hLR)
+  exact (polyTimeComputable_ite (ltTest_poly hk hLR)
+    (polyTimeComputable_ite hmv (polyTimeComputable_const []) hrun)
+    (polyTimeComputable_ite hlead (polyTimeComputable_const []) hmain)).congr
+    fun w => (H.composePW_eq ρ Fρ Fm fcall w).symm
+
+/-- **`composeVW` is polynomial-time** when `Fρ`, `Fm` and `fcall` are.
+`PolyTimeComputable (H.composeVW ρ Fρ Fm fcall)`.
+
+**Proof sketch.** As `polyTimeComputable_composePW`, with the count `k − 1` (`unarySub_poly`),
+two branches in the run phase and the drop count `L(n)·R(n) + lead` (`unaryAdd_poly`). -/
+theorem polyTimeComputable_composeVW {Fρ Fm fcall : List Bool → List Bool}
+    (hFρ : PolyTimeComputable Fρ) (hFm : PolyTimeComputable Fm)
+    (hcall : PolyTimeComputable fcall) : PolyTimeComputable (H.composeVW ρ Fρ Fm fcall) := by
+  have hk : PolyTimeComputable fun w => List.replicate (GI.msgCount (GI.argM w) - 1) true :=
+    unarySub_poly (GI.msgCount_poly.comp' GI.argM_poly) (unaryConst_poly 1)
+  have hR := unaryPoly_comp ρ.rounds GI.argX_poly
+  have hLR := unaryMul_poly (unaryPoly_comp H.calls GI.argX_poly) hR
+  have hdiv : PolyTimeComputable fun w =>
+      List.replicate ((GI.msgCount (GI.argM w) - 1) / ρ.rounds.eval (GI.argX w).length) true :=
+    (divNum_poly hk hR).congr fun w => by rw [divNum_eq]
+  have hmod : PolyTimeComputable fun w =>
+      List.replicate ((GI.msgCount (GI.argM w) - 1) % ρ.rounds.eval (GI.argX w).length) true :=
+    (modNum_poly hk hR).congr fun w => by rw [modNum_eq]
+  have hmv : PolyTimeComputable fun w =>
+      [moverIsV ρ.verifierFirst
+        ((GI.msgCount (GI.argM w) - 1) % ρ.rounds.eval (GI.argX w).length)] :=
+    ((polyTimeComputable_moverW ρ.verifierFirst true).comp'
+      (hmod.pairEncode polyTimeComputable_id)).congr fun w => by
+        rw [moverW_eq, pairFstD_pairEncode, List.length_replicate, beq_true]
+  have hrun := (polyTimeComputable_runW hFρ hcall H.main.V.coins ρ.V.coins ρ.rounds
+    ρ.verifierFirst false).comp' (hdiv.pairEncode (hmod.pairEncode polyTimeComputable_id))
+  have hmain := polyTimeComputable_mainW hFm (polyTimeComputable_ansW hFρ hcall H.main.V.coins
+    ρ.V.coins ρ.rounds H.calls G.outB ρ.verifierFirst false)
+    (unaryAdd_poly hLR (unaryConst_poly H.lead)) H.main.V.coins
+  exact (polyTimeComputable_ite (ltTest_poly hk hLR)
+    (polyTimeComputable_ite hmv hrun (polyTimeComputable_const [])) hmain).congr
+    fun w => (H.composeVW_eq ρ Fρ Fm fcall w).symm
+
+end Parties
+
+end HybridProtocol
+
+end TCSlib.Cryptography.SecureComputation
diff --git a/TCSlib/Cryptography/SecureComputation/ComposeSecurity/Lengths.lean b/TCSlib/Cryptography/SecureComputation/ComposeSecurity/Lengths.lean
new file mode 100644
index 000000000..2978459f2
--- /dev/null
+++ b/TCSlib/Cryptography/SecureComputation/ComposeSecurity/Lengths.lean
@@ -0,0 +1,303 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Runs
+import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Bounds
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Polynomial bounds on the words of the hybrid-step templates
+
+The templates of the reductions of the composition theorem [Gol04, §7.3.1, proof of
+Theorem 7.3.3] hold the hybrid main phase, the other party's output in `main`, real views of
+`ρ` and simulator outputs. Each has a length bounded by a polynomial in `n`, uniformly over the
+inputs and coins:
+* the encoded messages of the main phase on the ideal answers (`H.PolyTime` bounds `main`'s
+  messages for any answers of the hybrid lengths) and the parties' outputs in `main` (efficient
+  strategies on a polynomially long layout);
+* the encoded views of `ρ` on inputs of `G`'s lengths (`G.PolyTime ρ`);
+* the outputs of a machine on polynomially long arguments.
+
+## Main results
+
+* `HybridProtocol.exists_main_msgs_le`, `exists_main_outV_le`, `exists_main_outP_le`.
+* `ComposeBound.exists_viewP_le`, `exists_viewV_le`, `exists_runAt_le`.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §2.1 (Definition 26.8) and §4.4 (time complexity of interactive machines).
+-/
+
+namespace TCSlib.Cryptography.SecureComputation
+
+open Complexity Turing TCSlib.Cryptography ComposeBound
+
+/-- A list of length `c` is the encoding of a `c`-bit string. -/
+private theorem exists_ofFn_eq {c : ℕ} {l : List Bool} (h : l.length = c) :
+    ∃ t : Fin c → Bool, List.ofFn t = l := by
+  subst h
+  exact ⟨fun i => l[i.1], List.ofFn_getElem l⟩
+
+namespace HybridProtocol
+
+variable {G : Functionality} (H : HybridProtocol G)
+
+/-- Alice's ideal answers have `calls(n) · G.outA(n)` bits.
+`(H.answersA n x y rA rB).length = H.calls.eval n * G.outA.eval n`. -/
+theorem length_answersA (n : ℕ) (x y rA rB : List Bool) :
+    (H.answersA n x y rA rB).length = H.calls.eval n * G.outA.eval n := by
+  rw [answersA_eq, List.length_flatten, List.map_ofFn]
+  simp only [Function.comp_def, List.length_ofFn, List.ofFn_const, List.sum_replicate,
+    smul_eq_mul]
+
+/-- Bob's ideal answers have `calls(n) · G.outB(n)` bits.
+`(H.answersB n x y rA rB).length = H.calls.eval n * G.outB.eval n`. -/
+theorem length_answersB (n : ℕ) (x y rA rB : List Bool) :
+    (H.answersB n x y rA rB).length = H.calls.eval n * G.outB.eval n := by
+  rw [answersB_eq, List.length_flatten, List.map_ofFn]
+  simp only [Function.comp_def, List.length_ofFn, List.ofFn_const, List.sum_replicate,
+    smul_eq_mul]
+
+/-- **The encoded main phase is polynomially long**: for some polynomial `E`, on common input
+`1^n`, inputs of `F`'s lengths and any `main`-tapes, both halves of the encoded transcript of
+`main` on the ideal answers have at most `E(n)` bits.
+`∃ E : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (m : H.Coins
+n), (Strategy.encodeMsgs (H.main.transcript (List.replicate n true) (H.privA n (List.ofFn x)
+(List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) …`.
+
+**Proof sketch.** The ideal answers are strings of the hybrid lengths (`length_answersA`,
+`length_answersB`), so `H.PolyTime` bounds every message by `B(n)`; each half of the transcript
+has at most `rounds(n)` messages (`length_transcriptWith_fst_le`), so its encoding has at most
+`E(n) = rounds(n) (2B(n) + 2)` bits (`length_encodeMsgs_le`). -/
+theorem exists_main_msgs_le {F : Functionality} (hH : H.PolyTime F) :
+    ∃ E : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool)
+      (m : H.Coins n),
+      (Strategy.encodeMsgs (H.main.transcript (List.replicate n true)
+          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
+          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m).1).length ≤
+          E.eval n ∧
+        (Strategy.encodeMsgs (H.main.transcript (List.replicate n true)
+          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
+          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m).2).length ≤
+          E.eval n := by
+  obtain ⟨-, -, -, -, B, hB⟩ := (HybridProtocol.polyTime_iff H F).mp hH
+  refine ⟨.mul H.main.rounds (.add (.mul (.const 2) B) (.const 2)), fun n x y m => ?_⟩
+  obtain ⟨aA, haA⟩ := exists_ofFn_eq (c := H.calls.eval n * G.outA.eval n)
+    (l := H.answersA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
+    (H.length_answersA n _ _ _ _)
+  obtain ⟨aB, haB⟩ := exists_ofFn_eq (c := H.calls.eval n * G.outB.eval n)
+    (l := H.answersB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
+    (H.length_answersB n _ _ _ _)
+  have hmsg := hB n x y aA aB m
+  rw [haA, haB, ← privA_eq, ← privB_eq, Protocol.transcript_eq_transcriptWith] at hmsg
+  rw [Protocol.transcript_eq_transcriptWith]
+  have h₁ := length_transcriptWith_fst_le H.main H.main.P (List.replicate n true)
+    (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
+    (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m
+  have h₂ := length_transcriptWith_snd_le H.main H.main.P (List.replicate n true)
+    (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
+    (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m
+  have hR : H.main.rounds.eval (List.replicate n true).length = H.main.rounds.eval n := by
+    rw [List.length_replicate]
+  simp only [PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const]
+  exact ⟨(length_encodeMsgs_le _ (B.eval n) fun w hw => hmsg w (List.mem_append_left _ hw)).trans
+      (Nat.mul_le_mul_right _ (h₁.trans hR.le)),
+    (length_encodeMsgs_le _ (B.eval n) fun w hw => hmsg w (List.mem_append_right _ hw)).trans
+      (Nat.mul_le_mul_right _ (h₂.trans hR.le))⟩
+
+/-- **Bob's output in `main` is polynomially long**: for some polynomial `O`, on common input
+`1^n`, inputs of `F`'s lengths and any `main`-tapes, Bob's output in the hybrid execution has at
+most `O(n)` bits.
+`∃ O : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (m : H.Coins
+n), (H.main.outV H.main.P (List.replicate n true) (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn
+m.1) (List.ofFn m.2)) (H.privB n …`.
+
+**Proof sketch.** The output is `main.V.next` on `1^n`, Bob's private input, the messages he
+received and his `main`-tape (`Protocol.outV_eq`), at most `C (|layout| + 1)^c` bits
+(`Efficient.length_next_le`). The layout's length (`length_ilayout`) is linear in `n`, in his
+private input's `2 F.inB(n) + 2 + calls(n) G.outB(n)` bits (`length_answersB`), in the encoded
+messages (`exists_main_msgs_le`) and in his coin length; take `O = C (I + 1)^c` for that linear
+bound `I`. -/
+theorem exists_main_outV_le {F : Functionality} (hH : H.PolyTime F) :
+    ∃ O : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool)
+      (m : H.Coins n),
+      (H.main.outV H.main.P (List.replicate n true)
+        (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
+        (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m).length ≤
+        O.eval n := by
+  obtain ⟨-, hV, -, -, -⟩ := (HybridProtocol.polyTime_iff H F).mp hH
+  obtain ⟨C, c, hC⟩ := Efficient.length_next_le hV
+  obtain ⟨E, hE⟩ := H.exists_main_msgs_le hH
+  -- the layout: `1^n`, Bob's private input, the main phase and his `main`-tape
+  let I : PolyExpr := .add (.add (.mul (.const 2) (.add (.mul (.const 2)
+      (.add (.add (.mul (.const 2) .var) (.const 2))
+        (.add (.add (.mul (.const 2) (.add (.add (.mul (.const 2) .var) (.const 2))
+          (.add (.add (.mul (.const 2) F.inB) (.const 2)) (.mul H.calls G.outB)))) (.const 2)) E)))
+      (.const 2))) (.const 2)) H.main.V.coins
+  refine ⟨.mul (.const C) (.pow (.add I (.const 1)) c), fun n x y m => ?_⟩
+  have hI : (GI.ilayout (List.replicate n true)
+      (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
+      (H.main.transcriptWith H.main.P (List.replicate n true)
+        (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
+        (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m).2
+      (List.ofFn m.2)).length ≤ I.eval n := by
+    have h₁ := (hE n x y m).2
+    rw [Protocol.transcript_eq_transcriptWith] at h₁
+    have hpB : (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)).length =
+        2 * F.inB.eval n + 2 + H.calls.eval n * G.outB.eval n := by
+      rw [privB_eq, length_pairEncode, H.length_answersB, List.length_ofFn]
+    have hc : (List.ofFn m.2).length = H.main.V.coins.eval n := by
+      rw [List.length_ofFn, Strategy.coinLen_eq, List.length_replicate]
+    have hu : (List.replicate n true).length = n := List.length_replicate
+    rw [length_ilayout, hpB, hc]
+    simp only [I, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
+    omega
+  rw [Protocol.outV_eq]
+  refine (hC _ _ _ _).trans ?_
+  simp only [PolyExpr.eval_mul, PolyExpr.eval_pow, PolyExpr.eval_add, PolyExpr.eval_const]
+  gcongr
+
+/-- **Alice's output in `main` is polynomially long**: for some polynomial `O`, on common input
+`1^n`, inputs of `F`'s lengths and any `main`-tapes, Alice's output in the hybrid execution has
+at most `O(n)` bits.
+`∃ O : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (m : H.Coins
+n), (H.main.outP (List.replicate n true) (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1)
+(List.ofFn m.2)) (H.privB n (List.ofFn x) …`.
+
+**Proof sketch.** As `exists_main_outV_le`, with `main.P.next` on her private input
+(`length_answersA`), the messages she received and her `main`-tape (`Protocol.outP_eq`). -/
+theorem exists_main_outP_le {F : Functionality} (hH : H.PolyTime F) :
+    ∃ O : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool)
+      (m : H.Coins n),
+      (H.main.outP (List.replicate n true)
+        (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
+        (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m).length ≤
+        O.eval n := by
+  obtain ⟨hP, -, -, -, -⟩ := (HybridProtocol.polyTime_iff H F).mp hH
+  obtain ⟨C, c, hC⟩ := Efficient.length_next_le hP
+  obtain ⟨E, hE⟩ := H.exists_main_msgs_le hH
+  let I : PolyExpr := .add (.add (.mul (.const 2) (.add (.mul (.const 2)
+      (.add (.add (.mul (.const 2) .var) (.const 2))
+        (.add (.add (.mul (.const 2) (.add (.add (.mul (.const 2) .var) (.const 2))
+          (.add (.add (.mul (.const 2) F.inA) (.const 2)) (.mul H.calls G.outA)))) (.const 2)) E)))
+      (.const 2))) (.const 2)) H.main.P.coins
+  refine ⟨.mul (.const C) (.pow (.add I (.const 1)) c), fun n x y m => ?_⟩
+  have hI : (GI.ilayout (List.replicate n true)
+      (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
+      (H.main.transcriptWith H.main.P (List.replicate n true)
+        (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
+        (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m).1
+      (List.ofFn m.1)).length ≤ I.eval n := by
+    have h₁ := (hE n x y m).1
+    rw [Protocol.transcript_eq_transcriptWith] at h₁
+    have hpA : (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)).length =
+        2 * F.inA.eval n + 2 + H.calls.eval n * G.outA.eval n := by
+      rw [privA_eq, length_pairEncode, H.length_answersA, List.length_ofFn]
+    have hc : (List.ofFn m.1).length = H.main.P.coins.eval n := by
+      rw [List.length_ofFn, Strategy.coinLen_eq, List.length_replicate]
+    have hu : (List.replicate n true).length = n := List.length_replicate
+    rw [length_ilayout, hpA, hc]
+    simp only [I, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
+    omega
+  rw [Protocol.outP_eq]
+  refine (hC _ _ _ _).trans ?_
+  simp only [PolyExpr.eval_mul, PolyExpr.eval_pow, PolyExpr.eval_add, PolyExpr.eval_const]
+  gcongr
+
+end HybridProtocol
+
+namespace ComposeBound
+
+/-- **Alice's encoded `ρ`-views are polynomially long**: for some polynomial `V`, on common input
+`1^n` and inputs of `G`'s lengths, `|encode (viewP)| ≤ V(n)`.
+
+**Proof sketch.** The encoded view is `⟨⟨1^n, x⟩, ⟨tape, encodeMsgs received⟩⟩` (`View.encode_mk`,
+`length_pairEncode`): her tape has `ρ.P.coins(n)` bits, and she receives at most `rounds(n)`
+messages (`length_transcriptWith_fst_le`) of at most `B(n)` bits each, `B` the bound of
+`G.PolyTime ρ` (`length_encodeMsgs_le`); the sum is linear in these. -/
+theorem exists_viewP_le {G : Functionality} {ρ : Protocol} (hρ : G.PolyTime ρ) :
+    ∃ V : PolyExpr, ∀ n (x : Fin (G.inA.eval n) → Bool) (y : Fin (G.inB.eval n) → Bool)
+      (t : ρ.ExecCoins ρ.P (List.replicate n true)),
+      (ρ.viewP (List.replicate n true) (List.ofFn x) (List.ofFn y) t).encode.length ≤
+        V.eval n := by
+  obtain ⟨-, -, B, hB⟩ := (Functionality.polyTime_iff G ρ).mp hρ
+  refine ⟨.add (.add (.mul (.const 2) (.add (.add (.mul (.const 2) .var) (.const 2)) G.inA))
+      (.const 2)) (.add (.add (.mul (.const 2) ρ.P.coins) (.const 2))
+        (.mul ρ.rounds (.add (.mul (.const 2) B) (.const 2)))), fun n x y t => ?_⟩
+  have h₁ := length_transcriptWith_fst_le ρ ρ.P (List.replicate n true) (List.ofFn x)
+    (List.ofFn y) t
+  have hb := hB n x y t
+  rw [Protocol.transcript_eq_transcriptWith] at hb
+  have h₂ := (length_encodeMsgs_le _ (B.eval n) fun w hw =>
+    hb w (List.mem_append_left _ hw)).trans (Nat.mul_le_mul_right _ h₁)
+  have hR : ρ.rounds.eval (List.replicate n true).length = ρ.rounds.eval n := by
+    rw [List.length_replicate]
+  rw [hR] at h₂
+  have hu : (List.replicate n true).length = n := List.length_replicate
+  have hz : (List.ofFn x).length = G.inA.eval n := List.length_ofFn
+  have ht : (List.ofFn t.1).length = ρ.P.coins.eval n := by
+    rw [List.length_ofFn, Strategy.coinLen_eq, List.length_replicate]
+  rw [Protocol.viewP_eq, View.encode_mk, length_pairEncode, length_pairEncode, length_pairEncode,
+    ht]
+  simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
+  omega
+
+/-- **Bob's encoded `ρ`-views are polynomially long**: for some polynomial `V`, on common input
+`1^n` and inputs of `G`'s lengths, `|encode (viewV)| ≤ V(n)`.
+
+**Proof sketch.** As `exists_viewP_le`, with `ρ.V`'s tape and the messages he receives
+(`length_transcriptWith_snd_le`). -/
+theorem exists_viewV_le {G : Functionality} {ρ : Protocol} (hρ : G.PolyTime ρ) :
+    ∃ V : PolyExpr, ∀ n (x : Fin (G.inA.eval n) → Bool) (y : Fin (G.inB.eval n) → Bool)
+      (t : ρ.ExecCoins ρ.P (List.replicate n true)),
+      (ρ.viewV (List.replicate n true) (List.ofFn x) (List.ofFn y) t).encode.length ≤
+        V.eval n := by
+  obtain ⟨-, -, B, hB⟩ := (Functionality.polyTime_iff G ρ).mp hρ
+  refine ⟨.add (.add (.mul (.const 2) (.add (.add (.mul (.const 2) .var) (.const 2)) G.inB))
+      (.const 2)) (.add (.add (.mul (.const 2) ρ.V.coins) (.const 2))
+        (.mul ρ.rounds (.add (.mul (.const 2) B) (.const 2)))), fun n x y t => ?_⟩
+  have h₁ := length_transcriptWith_snd_le ρ ρ.P (List.replicate n true) (List.ofFn x)
+    (List.ofFn y) t
+  have hb := hB n x y t
+  rw [Protocol.transcript_eq_transcriptWith] at hb
+  have h₂ := (length_encodeMsgs_le _ (B.eval n) fun w hw =>
+    hb w (List.mem_append_right _ hw)).trans (Nat.mul_le_mul_right _ h₁)
+  have hR : ρ.rounds.eval (List.replicate n true).length = ρ.rounds.eval n := by
+    rw [List.length_replicate]
+  rw [hR] at h₂
+  have hu : (List.replicate n true).length = n := List.length_replicate
+  have hz : (List.ofFn y).length = G.inB.eval n := List.length_ofFn
+  have ht : (List.ofFn t.2).length = ρ.V.coins.eval n := by
+    rw [List.length_ofFn, Strategy.coinLen_eq, List.length_replicate]
+  rw [Protocol.viewV_eq, View.encode_mk, length_pairEncode, length_pairEncode, length_pairEncode,
+    ht]
+  simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
+  omega
+
+/-- **A machine's outputs on polynomially long arguments are polynomially long**: for an `NUPPT`
+`S` and a polynomial `k` there is a polynomial `O` with `|S.runAt n w s| ≤ O(n)` whenever
+`|w| ≤ k(n)` (`length_runAt_le`, `NUPPT.advice_length`). -/
+theorem exists_runAt_le (S : NUPPT) (k : PolyExpr) :
+    ∃ O : PolyExpr, ∀ n (w : List Bool) (s : S.Coins n), w.length ≤ k.eval n →
+      (S.runAt n w s).length ≤ O.eval n := by
+  let I : PolyExpr := .add (.add (.mul (.const 2) (.add (.add (.mul (.const 2)
+    (.add (.add (.mul (.const 2) .var) (.const 2)) k)) (.const 2)) S.adv)) (.const 2)) S.coins
+  refine ⟨.mul (.const S.Ct) (.pow (.add I (.const 1)) S.ct), fun n w s hw => ?_⟩
+  refine (length_runAt_le S n w s).trans ?_
+  have ha := S.advice_length n
+  have hI : 2 * (2 * (2 * n + 2 + w.length) + 2 + (S.advice n).length) + 2 + S.coinLen n ≤
+      I.eval n := by
+    simp only [I, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var,
+      NUPPT.coinLen_eq]
+    omega
+  simp only [PolyExpr.eval_mul, PolyExpr.eval_pow, PolyExpr.eval_add, PolyExpr.eval_const]
+  gcongr
+
+end ComposeBound
+
+end TCSlib.Cryptography.SecureComputation
diff --git a/TCSlib/Cryptography/SecureComputation/ComposeSecurity/Machines.lean b/TCSlib/Cryptography/SecureComputation/ComposeSecurity/Machines.lean
new file mode 100644
index 000000000..45cbde2cf
--- /dev/null
+++ b/TCSlib/Cryptography/SecureComputation/ComposeSecurity/Machines.lean
@@ -0,0 +1,260 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.EfficiencyRep
+import TCSlib.Cryptography.ZeroKnowledge.EncodingMachines
+import TCSlib.Cryptography.SecureComputation.Compose
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Polynomial-time machines on encoded histories
+
+The machine infrastructure behind the efficiency of the composed parties
+(`HybridProtocol.composeP_efficient`, `composeV_efficient`) [Gol04, §7.3.1, the protocol of
+Theorem 7.3.3]: a party of `H.compose ρ` reads its history `encodeMsgs hist` at interleaved
+positions (the messages of one run of `ρ` sit at every other pair, `Compose.slotMsgs`), and maps
+`ρ`'s next-message function over the `L(n)` runs. Both are loops over a data-dependent range of
+the unary FP toolkit (`ZeroKnowledge/EncodingMachines.lean`) and the peeling loops of
+`GraphIsomorphism/EfficiencyRep.lean`.
+
+## Main definitions
+
+* `ComposeMachines.padTo`: zero padding, the string form of `padFin`.
+
+## Main results
+
+* `ComposeMachines.polyTimeComputable_flatMap_range`: concatenating a polynomial-time chunk over
+  a data-dependent range is polynomial-time.
+* `ComposeMachines.iterSnd_poly`, `msgAt_encodeMsgs`: the `i`-th message of an encoded history.
+* `ComposeMachines.encodeMsgs_append`, `encodeMsgs_eq_flatMap`, `encodeMsgs_slotMsgs`: the
+  history encoding as a concatenation of chunks, and the interleaved slots of a history.
+* `ComposeMachines.polyTimeComputable_slots`: **the interleaved-slot map**: the encoded messages
+  `slotMsgs sel off p hist` are a polynomial-time function of the encoded history, for a
+  polynomial-time selector and unary offset and count.
+* `ComposeMachines.Efficient.exists_polyTime`: an efficient strategy's next-message function is
+  a polynomial-time function of the machine layout `GI.ilayout` (the converse of
+  `GI.efficient_of_polyTime`).
+* `ComposeMachines.ofFn_padFin`, `padTo_poly`: `padFin` as a polynomial-time string map.
+
+## References
+
+* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
+  University Press, 2004, §7.3.1 (the composed protocol of Theorem 7.3.3).
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §4.4 (interactive machines and their time complexity, pp. 114–116).
+-/
+
+namespace TCSlib.Cryptography.SecureComputation.ComposeMachines
+
+open Complexity Turing Complexity.StateLoop TCSlib.Cryptography.EncodingMachines
+
+/-! ### Loops over a data-dependent range -/
+
+/-- Emitting `E i` at the indices `i < L` of `List.range N` gives the concatenation of the
+`E i` over `i < min N L`:
+`(range N).flatMap (fun i => if i < L then E i else []) = (range (min N L)).flatMap E`. -/
+theorem flatMap_range_ite (E : ℕ → List Bool) (L : ℕ) :
+    ∀ N, (List.range N).flatMap (fun i => if i < L then E i else []) =
+      (List.range (min N L)).flatMap E
+  | 0 => by simp
+  | N + 1 => by
+    rw [List.range_succ, List.flatMap_append, flatMap_range_ite E L N, List.flatMap_singleton]
+    by_cases h : N < L
+    · rw [if_pos h, show min (N + 1) L = N + 1 by omega, show min N L = N by omega,
+        List.range_succ, List.flatMap_append, List.flatMap_singleton]
+    · rw [if_neg h, List.append_nil, show min (N + 1) L = min N L by omega]
+
+/-- **Concatenating a chunk over a data-dependent range**: if the chunk `E z i` is a
+polynomial-time function of `⟨1^i, z⟩` and the count `n z` is a unary function, then
+`z ↦ E z 0 ++ ⋯ ++ E z (n z − 1)` is polynomial-time.
+`PolyTimeComputable fun z => (List.range (n z)).flatMap (E z)`.
+
+**Proof sketch.** An instance of `Complexity.polyTimeComputable_iterateEmit` on the counter step
+`EncodingMachines.cstep` from `⟨[], z⟩`, whose `i`-th iterate is `⟨1^i, z⟩` (`cstep_iterate`),
+emitting `E z i` while `i < n z` (`flatMap_range_ite`); the number of rounds is the polynomial
+bound of the unary count (`PolyTimeComputable.output_length_le`). -/
+theorem polyTimeComputable_flatMap_range {E : List Bool → ℕ → List Bool}
+    (hE : PolyTimeComputable fun w => E (pairSndD w) (pairFstD w).length)
+    {n : List Bool → ℕ} (hn : PolyTimeComputable fun z => List.replicate (n z) true) :
+    PolyTimeComputable fun z => (List.range (n z)).flatMap (E z) := by
+  obtain ⟨C, c, hC⟩ := hn.output_length_le
+  have hnP : ∀ z, n z ≤ (PolyExpr.normal C c).eval z.length := fun z => by
+    have := hC z
+    simpa [PolyExpr.eval_normal] using this
+  have htest : PolyTimeComputable fun w => [decide ((pairFstD w).length < n (pairSndD w))] :=
+    ltTest_poly (unaryLength_poly polyTimeComputable_pairFstD)
+      (hn.comp polyTimeComputable_pairSndD)
+  have hemit := polyTimeComputable_ite htest hE (polyTimeComputable_const [])
+  have hL := polyTimeComputable_iterateEmit cstep_poly hemit (PolyExpr.normal C c)
+    (cbound (PolyExpr.normal C c)) (cstep_horbit _)
+  have hpre : PolyTimeComputable fun z => pairEncode [] z :=
+    (polyTimeComputable_const []).pairEncode polyTimeComputable_id
+  refine (hL.comp hpre).congr fun z => ?_
+  simp only [Function.comp_apply]
+  have horb : ∀ i, cstep^[i] (pairEncode [] z) = pairEncode (List.replicate i true) z :=
+    fun i => by rw [cstep_iterate, List.append_nil]
+  have hN : n z ≤ (PolyExpr.normal C c).eval (pairEncode [] z).length + 1 :=
+    ((hnP z).trans ((PolyExpr.normal C c).eval_mono
+      (by rw [length_pairEncode]; omega))).trans (Nat.le_succ _)
+  simp only [horb, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
+    decide_eq_true_eq]
+  rw [flatMap_range_ite, min_eq_right hN]
+
+/-! ### Reading an encoded history -/
+
+/-- **The iterated second projection** `pairSndD^[i z] (s z)` is polynomial-time for a
+polynomial-time `s` and a unary count `i`.
+`PolyTimeComputable fun z => pairSndD^[i z] (s z)`.
+
+**Proof sketch.** `GI.iterUnary_poly` with the step `⟨x₀, s⟩ ↦ pairSndD s` on
+`⟨1^{i z}, s z⟩`; peeling never lengthens a word (`GI.length_iterate_le`,
+`GI.length_pairSndD_le`), so the orbit is bounded by the input length. -/
+theorem iterSnd_poly {s : List Bool → List Bool} (hs : PolyTimeComputable s)
+    {i : List Bool → ℕ} (hi : PolyTimeComputable fun z => List.replicate (i z) true) :
+    PolyTimeComputable fun z => pairSndD^[i z] (s z) := by
+  have hstep : PolyTimeComputable fun w => pairSndD (pairSndD w) :=
+    polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
+  have hclosed : ∀ x₀ k, (fun t => pairSndD (pairSndD (pairEncode x₀ t)))^[k] (pairSndD x₀) =
+      pairSndD^[k] (pairSndD x₀) := by
+    intro x₀ k
+    congr 1
+    funext t
+    rw [pairSndD_pairEncode]
+  have hit := GI.iterUnary_poly hstep .var fun x₀ k _ => by
+    rw [hclosed, PolyExpr.eval_var]
+    exact (GI.length_iterate_le GI.length_pairSndD_le _ k).trans (GI.length_pairSndD_le x₀)
+  refine (hit.comp (hi.pairEncode hs)).congr fun z => ?_
+  simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
+    List.length_replicate]
+
+/-- **The `i`-th message of an encoded history**: `pairFstD (pairSndD^[i] (encodeMsgs hist)) =
+hist.getD i []` (`GI.iterate_pairSndD_encodeMsgs`, `Strategy.pairFstD_encodeMsgs`). -/
+theorem msgAt_encodeMsgs (hist : List (List Bool)) (i : ℕ) :
+    pairFstD (pairSndD^[i] (Strategy.encodeMsgs hist)) = hist.getD i [] := by
+  rw [GI.iterate_pairSndD_encodeMsgs, Strategy.pairFstD_encodeMsgs, List.headD_eq_head?_getD,
+    List.head?_drop, List.getD_eq_getElem?_getD]
+
+/-- **The history encoding is a concatenation**:
+`encodeMsgs (a ++ b) = encodeMsgs a ++ encodeMsgs b` (`pairEncode_nil_append`). -/
+theorem encodeMsgs_append (a b : List (List Bool)) :
+    Strategy.encodeMsgs (a ++ b) = Strategy.encodeMsgs a ++ Strategy.encodeMsgs b := by
+  induction a with
+  | nil => rw [List.nil_append, Strategy.encodeMsgs_nil, List.nil_append]
+  | cons m a ih =>
+    rw [List.cons_append, Strategy.encodeMsgs_cons, Strategy.encodeMsgs_cons, ih,
+      ← BinArith.pairEncode_nil_append,
+      ← BinArith.pairEncode_nil_append (b := Strategy.encodeMsgs a), List.append_assoc]
+
+/-- **The history encoding chunk by chunk**: `encodeMsgs l = l.flatMap fun m => ⟨m, []⟩`. -/
+theorem encodeMsgs_eq_flatMap (l : List (List Bool)) :
+    Strategy.encodeMsgs l = l.flatMap fun m => pairEncode m [] := by
+  induction l with
+  | nil => rw [Strategy.encodeMsgs_nil, List.flatMap_nil]
+  | cons m l ih =>
+    rw [Strategy.encodeMsgs_cons, List.flatMap_cons, ← ih, BinArith.pairEncode_nil_append]
+
+/-- **The encoded slots of a history**: the encoding of `slotMsgs sel off p hist` is the
+concatenation over `q < p` of the chunk `⟨hist[off + q], []⟩` when `sel q`, read from the
+encoded history (`msgAt_encodeMsgs`):
+`encodeMsgs (slotMsgs sel off p hist) = (range p).flatMap fun q =>
+if sel q then ⟨pairFstD (pairSndD^[off + q] (encodeMsgs hist)), []⟩ else []`. -/
+theorem encodeMsgs_slotMsgs (sel : ℕ → Bool) (off p : ℕ) (hist : List (List Bool)) :
+    Strategy.encodeMsgs (Compose.slotMsgs sel off p hist) =
+      (List.range p).flatMap fun q =>
+        if sel q then pairEncode (pairFstD (pairSndD^[off + q] (Strategy.encodeMsgs hist))) []
+        else [] := by
+  rw [Compose.slotMsgs_eq, encodeMsgs_eq_flatMap, List.flatMap_map]
+  induction p with
+  | zero => simp only [List.range_zero, List.filter_nil, List.flatMap_nil]
+  | succ p ih =>
+    rw [List.range_succ, List.filter_append, List.flatMap_append, List.flatMap_append, ih,
+      List.flatMap_singleton]
+    congr 1
+    cases h : sel p
+    · rw [List.filter_singleton, h, cond_false, List.flatMap_nil, if_neg Bool.false_ne_true]
+    · rw [List.filter_singleton, h, cond_true, List.flatMap_singleton, if_pos rfl,
+        msgAt_encodeMsgs]
+
+/-- **The interleaved-slot map**: for a selector `sel z q` that is a polynomial-time test of
+`⟨1^q, z⟩`, unary offset `off z` and count `p z`, and a polynomial-time word `M z`, the word
+`(range (p z)).flatMap fun q => if sel z q then ⟨pairFstD (pairSndD^[off z + q] (M z)), []⟩
+else []` is polynomial-time; on `M z = encodeMsgs hist` it is
+`encodeMsgs (slotMsgs (sel z) (off z) (p z) hist)` (`encodeMsgs_slotMsgs`).
+
+**Proof sketch.** `polyTimeComputable_flatMap_range` with the chunk built from the test, the
+iterated projection at the unary count `off z + q` (`iterSnd_poly`, `unaryAdd_poly`) and
+`pairEncode`. -/
+theorem polyTimeComputable_slots {sel : List Bool → ℕ → Bool}
+    (hsel : PolyTimeComputable fun w => [sel (pairSndD w) (pairFstD w).length])
+    {off p : List Bool → ℕ} (hoff : PolyTimeComputable fun z => List.replicate (off z) true)
+    (hp : PolyTimeComputable fun z => List.replicate (p z) true)
+    {M : List Bool → List Bool} (hM : PolyTimeComputable M) :
+    PolyTimeComputable fun z => (List.range (p z)).flatMap fun q =>
+      if sel z q then pairEncode (pairFstD (pairSndD^[off z + q] (M z))) [] else [] := by
+  have hcnt : PolyTimeComputable fun w =>
+      List.replicate (off (pairSndD w) + (pairFstD w).length) true :=
+    unaryAdd_poly (hoff.comp polyTimeComputable_pairSndD)
+      (unaryLength_poly polyTimeComputable_pairFstD)
+  have hmsg := polyTimeComputable_pairFstD.comp
+    (iterSnd_poly (hM.comp polyTimeComputable_pairSndD) hcnt)
+  exact polyTimeComputable_flatMap_range
+    (polyTimeComputable_ite hsel (hmsg.pairEncode (polyTimeComputable_const []))
+      (polyTimeComputable_const [])) hp
+
+/-! ### Strategies as functions of the machine layout -/
+
+/-- **An efficient strategy is a polynomial-time function of the layout** (the converse of
+`GI.efficient_of_polyTime`): if `S.Efficient`, there is a polynomial-time `F` with
+`S.next x z r hist = F (GI.ilayout x z hist r)` (the output
+function of the uniform machine, `NUPPT.polyTimeComputable_output`; its advice is empty). -/
+theorem Efficient.exists_polyTime {S : Strategy} (h : S.Efficient) :
+    ∃ F : List Bool → List Bool, PolyTimeComputable F ∧
+      ∀ x z r hist, S.next x z r hist = F (GI.ilayout x z hist r) := by
+  obtain ⟨A, hA, -, hnext⟩ := (Strategy.efficient_iff S).1 h
+  refine ⟨A.output, A.polyTimeComputable_output, fun x z r hist => ?_⟩
+  rw [hnext, Strategy.ofNUPPT_next, NUPPT.runAtL_eq_output_layout, NUPPT.Uniform.advice_eq hA,
+    GI.ilayout_def]
+
+/-! ### Zero padding -/
+
+/-- **Zero padding** to length `L` (and truncation to `L`): `padTo L w = (w ++ 0^L).take L`, the
+string form of `padFin L w` (`ofFn_padFin`). -/
+def padTo (L : ℕ) (w : List Bool) : List Bool := (w ++ List.replicate L false).take L
+
+/-- The defining equation of `padTo`: `padTo L w = (w ++ 0^L).take L`. -/
+theorem padTo_eq (L : ℕ) (w : List Bool) : padTo L w = (w ++ List.replicate L false).take L :=
+  rfl
+
+/-- Padding to a unary length is polynomial-time (`EncodingMachines.truncate_poly`, the zeros
+`GI.zeros_poly` of the unary string).
+`PolyTimeComputable fun x => padTo (L x) (s x)`. -/
+theorem padTo_poly {s : List Bool → List Bool} (hs : PolyTimeComputable s)
+    {L : List Bool → ℕ} (hL : PolyTimeComputable fun x => List.replicate (L x) true) :
+    PolyTimeComputable fun x => padTo (L x) (s x) :=
+  truncate_poly (hs.append ((GI.zeros_poly.comp' hL).congr fun x => by
+    rw [List.length_replicate])) hL
+
+/-- The padded word has length `L`: `|padTo L w| = L`. -/
+theorem length_padTo (L : ℕ) (w : List Bool) : (padTo L w).length = L := by
+  rw [padTo_eq, List.length_take, List.length_append, List.length_replicate]
+  omega
+
+/-- **`padFin` as a string**: `List.ofFn (padFin L w) = padTo L w`. -/
+theorem ofFn_padFin (L : ℕ) (w : List Bool) : List.ofFn (padFin L w) = padTo L w := by
+  apply List.ext_getElem?
+  intro i
+  rw [List.getElem?_ofFn, padTo_eq, List.getElem?_take]
+  by_cases hi : i < L
+  · rw [dif_pos hi, if_pos hi, padFin_apply, Fin.val_mk, List.getD_eq_getElem?_getD,
+      List.getElem?_append]
+    split_ifs with h
+    · rw [List.getElem?_eq_getElem h, Option.getD_some]
+    · rw [List.getElem?_eq_none_iff.2 (by omega), Option.getD_none,
+        List.getElem?_replicate, if_pos (by omega)]
+  · rw [dif_neg hi, if_neg hi]
+
+end TCSlib.Cryptography.SecureComputation.ComposeMachines
diff --git a/TCSlib/Cryptography/SecureComputation/ComposeSecurity/Probability.lean b/TCSlib/Cryptography/SecureComputation/ComposeSecurity/Probability.lean
new file mode 100644
index 000000000..feff8ed56
--- /dev/null
+++ b/TCSlib/Cryptography/SecureComputation/ComposeSecurity/Probability.lean
@@ -0,0 +1,126 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Foundations.Experiments
+import TCSlib.Cryptography.Foundations.Negligible
+import TCSlib.Complexity.Randomized.PolyExpr
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Probability tools for the composition theorem
+
+The distinguishing-advantage manipulations of the proof of [Gol04, §7.3.1, Theorem 7.3.3]
+(`HybridProtocol.hbcSecure_compose`), on uniform seeds and coins (`acceptProb`, `distAdv`):
+* the statistical switch: two samplers on one seed space that agree off a bad event are within
+  the bad event's probability;
+* fixing coordinates: the advantage between two samplers on `σ × τ` is at most the advantage of
+  their sections at the worst `a : σ` (the advice of a non-uniform reduction);
+* a negligible function times a polynomial is negligible.
+
+Unused seed coordinates are dropped by the published `acceptProb_fst`, `acceptProb_snd`
+(`Pseudorandom/Indistinguishability.lean`).
+
+## Main results
+
+* `ComposeProb.abs_uprob_sub_le`, `ComposeProb.distAdv_le_uprob_of_eq`,
+  `ComposeProb.exists_abs_sub_le_sections`, `ComposeProb.negligible_polyExpr_mul`.
+
+## References
+
+* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
+  University Press, 2004, §7.3.1 (the proof of Theorem 7.3.3).
+* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley, draft of
+  22 January 2026, §1.2 (negligible functions) and §3.2 (hybrid arguments).
+-/
+
+namespace TCSlib.Cryptography.SecureComputation.ComposeProb
+
+open Finset Complexity
+
+variable {σ τ υ γ ρ : Type*} [Fintype σ] [Fintype τ] [Fintype υ] [Fintype ρ]
+
+/-- Two events that agree off a third: `|Pr[A] − Pr[B]| ≤ Pr[C]` when `A ↔ B` outside `C`. -/
+theorem abs_uprob_sub_le {A B C : υ → Prop} (h : ∀ u, ¬ C u → (A u ↔ B u)) :
+    |uprob A - uprob B| ≤ uprob C := by
+  have h1 : uprob A ≤ uprob B + uprob C :=
+    (uprob_mono fun u ha => by
+      by_cases hc : C u
+      · exact Or.inr hc
+      · exact Or.inl ((h u hc).1 ha)).trans (uprob_or_le B C)
+  have h2 : uprob B ≤ uprob A + uprob C :=
+    (uprob_mono fun u hb => by
+      by_cases hc : C u
+      · exact Or.inr hc
+      · exact Or.inl ((h u hc).2 hb)).trans (uprob_or_le A C)
+  rw [abs_le]
+  constructor <;> linarith
+
+/-- **The statistical switch** ("agree off a bad event"): if the samplers `X`, `Y` on one seed
+space agree at every seed outside `bad`, then `distAdv X Y D ≤ Pr_s[bad s]`.
+
+**Proof sketch.** The acceptance events on `σ × ρ` agree outside `bad ∘ fst`
+(`abs_uprob_sub_le`), whose probability is `Pr[bad]` (`uprob_fst`). -/
+theorem distAdv_le_uprob_of_eq [Nonempty ρ] (X Y : σ → γ) (D : γ → ρ → Bool) (bad : σ → Prop)
+    (h : ∀ s, ¬ bad s → X s = Y s) : distAdv X Y D ≤ uprob bad := by
+  rw [distAdv_def, acceptProb_def, acceptProb_def, ← uprob_fst (β := ρ) bad]
+  exact abs_uprob_sub_le fun z hz => by rw [h z.1 hz]
+
+/-- **Acceptance as an average of sections**: `acceptProb X D` is the average over `a : σ` of
+the acceptance probability of the section `t ↦ X (a, t)` (`uprob_prod` after reassociating).
+`acceptProb X D = uexp fun a => acceptProb (fun t => X (a, t)) D`. -/
+theorem acceptProb_eq_uexp_sections (X : σ × τ → γ) (D : γ → ρ → Bool) :
+    acceptProb X D = uexp fun a => acceptProb (fun t => X (a, t)) D := by
+  rw [acceptProb_def, ← uprob_comp_equiv (Equiv.prodAssoc σ τ ρ).symm, uprob_prod]
+  simp only [acceptProb_def]
+  rfl
+
+/-- The average of a difference is at most the largest difference: some `a` has
+`|uexp f − uexp g| ≤ |f a − g a|` (for nonempty `σ`). -/
+theorem exists_abs_uexp_sub_le [Nonempty σ] (f g : σ → ℝ) :
+    ∃ a, |uexp f - uexp g| ≤ |f a - g a| := by
+  obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ (fun a => |f a - g a|)
+    Finset.univ_nonempty
+  refine ⟨a, ?_⟩
+  have hc : (0 : ℝ) < Fintype.card σ := Nat.cast_pos.2 Fintype.card_pos
+  rw [uexp_def, uexp_def, ← sub_div, abs_div, abs_of_pos hc, div_le_iff₀ hc, ← sum_sub_distrib]
+  calc |∑ i, (f i - g i)| ≤ ∑ i, |f i - g i| := abs_sum_le_sum_abs _ _
+    _ ≤ ∑ _i : σ, |f a - g a| := sum_le_sum fun i _ => ha i (mem_univ i)
+    _ = |f a - g a| * Fintype.card σ := by rw [sum_const, card_univ, nsmul_eq_mul, mul_comm]
+
+/-- **Fixing coordinates** (the advice of a non-uniform reduction): for samplers `X`, `Y` on
+`σ × τ` there is `a : σ` with `|acceptProb X D − acceptProb Y D| ≤
+|acceptProb (X (a, ·)) D − acceptProb (Y (a, ·)) D|` (`acceptProb_eq_uexp_sections`,
+`exists_abs_uexp_sub_le`). -/
+theorem exists_abs_sub_le_sections [Nonempty σ] (X Y : σ × τ → γ) (D : γ → ρ → Bool) :
+    ∃ a, |acceptProb X D - acceptProb Y D| ≤
+      |acceptProb (fun t => X (a, t)) D - acceptProb (fun t => Y (a, t)) D| := by
+  rw [acceptProb_eq_uexp_sections X, acceptProb_eq_uexp_sections Y]
+  exact exists_abs_uexp_sub_le _ _
+
+/-- **A negligible function times a polynomial is negligible**: for `p : PolyExpr`,
+`n ↦ p(n) · μ(n)` is negligible.
+`Negligible fun n => (p.eval n : ℝ) * μ n`.
+
+**Proof sketch.** `p(n) ≤ C (n + 1)^c ≤ C 2^c n^c` for `n ≥ 1` (`PolyExpr.eval_le`), and
+`n ↦ (C 2^c) (n^c μ(n))` is negligible (`Negligible.mul_pow`, `Negligible.const_mul`). -/
+theorem negligible_polyExpr_mul {μ : ℕ → ℝ} (hμ : Negligible μ) (p : PolyExpr) :
+    Negligible fun n => (p.eval n : ℝ) * μ n := by
+  obtain ⟨C, c, hC⟩ := p.eval_le
+  refine ((hμ.mul_pow c).const_mul ((C : ℝ) * 2 ^ c)).mono ⟨1, fun n hn => ?_⟩
+  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
+  have hp : (p.eval n : ℝ) ≤ C * 2 ^ c * (n : ℝ) ^ c := by
+    have h1 : (p.eval n : ℝ) ≤ C * ((n : ℝ) + 1) ^ c := by exact_mod_cast hC n
+    have h2 : ((n : ℝ) + 1) ^ c ≤ (2 * (n : ℝ)) ^ c :=
+      pow_le_pow_left₀ (by positivity) (by linarith) c
+    rw [mul_pow] at h2
+    nlinarith [show (0 : ℝ) ≤ C from Nat.cast_nonneg C]
+  rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (p.eval n)),
+    abs_of_nonneg (by positivity : (0 : ℝ) ≤ C * 2 ^ c), abs_mul,
+    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ c), ← mul_assoc]
+  exact mul_le_mul_of_nonneg_right hp (abs_nonneg _)
+
+end TCSlib.Cryptography.SecureComputation.ComposeProb
diff --git a/TCSlib/Cryptography/SecureComputation/ComposeSecurity/Reductions.lean b/TCSlib/Cryptography/SecureComputation/ComposeSecurity/Reductions.lean
new file mode 100644
index 000000000..8f1ba3491
--- /dev/null
+++ b/TCSlib/Cryptography/SecureComputation/ComposeSecurity/Reductions.lean
@@ -0,0 +1,106 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Complexity.Randomized.Closure
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Machines with advice-dependent pre- and post-processing and extra coins
+
+Two closure properties of non-uniform PPT machines used by the simulators and reductions of the
+composition theorem [Gol04, §7.3.1, proof of Theorem 7.3.3]: a machine may hand its argument,
+together with an advice string and a block of extra coins, to a polynomial-time pre-processor
+before running another machine (`ComposeSim.exists_pre`: a reduction `D ∘ Ψ`), or post-process
+another machine's output with an advice string and extra coins (`ComposeSim.exists_post`: a
+simulator that runs a simulator and then completes its output). Both combine the closure
+catalogue of `Complexity/Randomized/Closure.lean` (`exists_split`, `exists_withAdvice`,
+`exists_seq`) in one raw function of the layout (`NUPPT.ofPolyTime`).
+
+## Main results
+
+* `ComposeSim.exists_pre`, `ComposeSim.exists_post`.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §2.1 (closure of non-uniform PPT machines under composition, Definition 26.8).
+-/
+
+namespace TCSlib.Cryptography.SecureComputation.ComposeSim
+
+open Complexity Turing Complexity.NUPPT
+
+/-- **Pre-processing with advice and extra coins**: for an `NUPPT` `D`, a polynomial-time `Ψ`, a
+polynomially bounded advice family `α` and a coin polynomial `p`, there is an `NUPPT` `B` with
+coins `p + D.coins` such that `B(1^n, y; r) = D(1^n, Ψ ⟨⟨1^n, α n⟩, ⟨y, r_{<p(n)}⟩⟩; r_{≥p(n)})`.
+
+**Proof sketch.** Advice `⟨D.advice n, α n⟩`; the raw function reads `1^n`, the argument, the two
+advice halves and the coins from the layout (`inParam`, `inArg`, `inAdvice`, `inCoins`), cuts the
+coins at `p(n)` (`polyTimeComputable_pairTakePoly`, `polyTimeComputable_pairDropPoly`), applies
+`Ψ` and runs `D.output` (`NUPPT.polyTimeComputable_output`); the equation is `runAtL_ofPolyTime`
+with the projection identities. -/
+theorem exists_pre (D : NUPPT) {Ψ : List Bool → List Bool} (hΨ : PolyTimeComputable Ψ)
+    (α : ℕ → List Bool) (a : PolyExpr) (hα : ∀ n, (α n).length ≤ a.eval n) (p : PolyExpr) :
+    ∃ B : NUPPT, B.coins = .add p D.coins ∧ ∀ n y r, B.runAtL n y r =
+      D.runAtL n (Ψ (pairEncode (pairEncode (List.replicate n true) (α n))
+        (pairEncode y (r.take (p.eval n))))) (r.drop (p.eval n)) := by
+  have hcut := polyTimeComputable_inParam.pairEncode polyTimeComputable_inCoins
+  have hpre := hΨ.comp' ((polyTimeComputable_inParam.pairEncode
+      (polyTimeComputable_pairSndD.comp' polyTimeComputable_inAdvice)).pairEncode
+    (polyTimeComputable_inArg.pairEncode ((polyTimeComputable_pairTakePoly p).comp' hcut)))
+  have hF := D.polyTimeComputable_output.comp' (polyTimeComputable_layout polyTimeComputable_inParam
+    hpre (polyTimeComputable_pairFstD.comp' polyTimeComputable_inAdvice)
+    ((polyTimeComputable_pairDropPoly p).comp' hcut))
+  have hadv : ∀ n, (pairEncode (D.advice n) (α n)).length ≤
+      (PolyExpr.add (.add (.mul (.const 2) D.adv) (.const 2)) a).eval n := fun n => by
+    rw [length_pairEncode]
+    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
+    have h₁ := D.advice_length n
+    have h₂ := hα n
+    omega
+  refine ⟨ofPolyTime hF (.add p D.coins) _ (fun n => pairEncode (D.advice n) (α n)) hadv,
+    coins_ofPolyTime _ _ _ _ _, fun n y r => ?_⟩
+  rw [runAtL_ofPolyTime, runAtL_eq_output_layout]
+  simp only [advInput_eq, ← layout_eq, inParam_layout, inArg_layout, inAdvice_layout,
+    inCoins_layout, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
+
+/-- **Post-processing with advice and extra coins**: for an `NUPPT` `A`, a polynomial-time `Ψ`,
+a polynomially bounded advice family `α` and a coin polynomial `p`, there is an `NUPPT` `B` with
+coins `A.coins + p` such that
+`B(1^n, y; r) = Ψ ⟨⟨1^n, α n⟩, ⟨A(1^n, y; r_{<A.coins(n)}), r_{≥A.coins(n)}⟩⟩`.
+
+**Proof sketch.** Advice `⟨A.advice n, α n⟩`; the raw function cuts the coins at `A.coins(n)`,
+runs `A.output` on the layout with the first advice half and the head of the coins, and applies
+`Ψ` to the parameter, the second advice half, `A`'s output and the tail of the coins
+(`runAtL_ofPolyTime` with the projection identities). -/
+theorem exists_post (A : NUPPT) {Ψ : List Bool → List Bool} (hΨ : PolyTimeComputable Ψ)
+    (α : ℕ → List Bool) (a : PolyExpr) (hα : ∀ n, (α n).length ≤ a.eval n) (p : PolyExpr) :
+    ∃ B : NUPPT, B.coins = .add A.coins p ∧ ∀ n y r, B.runAtL n y r =
+      Ψ (pairEncode (pairEncode (List.replicate n true) (α n))
+        (pairEncode (A.runAtL n y (r.take (A.coinLen n))) (r.drop (A.coinLen n)))) := by
+  have hcut := polyTimeComputable_inParam.pairEncode polyTimeComputable_inCoins
+  have hout := A.polyTimeComputable_output.comp' (polyTimeComputable_layout
+    polyTimeComputable_inParam polyTimeComputable_inArg
+    (polyTimeComputable_pairFstD.comp' polyTimeComputable_inAdvice)
+    ((polyTimeComputable_pairTakePoly A.coins).comp' hcut))
+  have hF := hΨ.comp' ((polyTimeComputable_inParam.pairEncode
+      (polyTimeComputable_pairSndD.comp' polyTimeComputable_inAdvice)).pairEncode
+    (hout.pairEncode ((polyTimeComputable_pairDropPoly A.coins).comp' hcut)))
+  have hadv : ∀ n, (pairEncode (A.advice n) (α n)).length ≤
+      (PolyExpr.add (.add (.mul (.const 2) A.adv) (.const 2)) a).eval n := fun n => by
+    rw [length_pairEncode]
+    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
+    have h₁ := A.advice_length n
+    have h₂ := hα n
+    omega
+  refine ⟨ofPolyTime hF (.add A.coins p) _ (fun n => pairEncode (A.advice n) (α n)) hadv,
+    coins_ofPolyTime _ _ _ _ _, fun n y r => ?_⟩
+  rw [runAtL_ofPolyTime, runAtL_eq_output_layout, coinLen_eq]
+  simp only [advInput_eq, ← layout_eq, inParam_layout, inArg_layout, inAdvice_layout,
+    inCoins_layout, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
+
+end TCSlib.Cryptography.SecureComputation.ComposeSim
diff --git a/TCSlib/Cryptography/SecureComputation/ComposeSecurity/Runs.lean b/TCSlib/Cryptography/SecureComputation/ComposeSecurity/Runs.lean
new file mode 100644
index 000000000..9cb57cfc3
--- /dev/null
+++ b/TCSlib/Cryptography/SecureComputation/ComposeSecurity/Runs.lean
@@ -0,0 +1,632 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.SecureComputation.ComposePhases
+import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Assembly
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The real samples of the composed protocol, run by run
+
+Step 2 of the proof of the composition theorem [Gol04, §7.3.1, proof of Theorem 7.3.3]: the coins
+of an honest execution of `H.compose ρ` on `1^n` are the `main`-tapes `m` and one pair of
+`ρ`-tapes `t j` per call (`composeCoins`), and when every run's outputs are the ideal answers
+(`GoodRuns`), the real sample of either side is the assembled view (`ComposeSim.asmView`) of the
+real views of the runs (`realViewA`, `realViewB`), with the main phase and the other party's output
+those of the hybrid execution on the `main`-tapes (`realA_compose_eq`, `realB_compose_eq`, using
+`hM`).
+
+## Main definitions
+
+* `ComposeSim.splitCoins`: `{0,1}^a × ({0,1}^b)^q ≃ {0,1}^m` for `m = a + q·b`.
+* `HybridProtocol.composeCoins`: the coins of `H.compose ρ` as `main`-tapes and run tapes.
+* `HybridProtocol.inA`, `inB`: the call inputs as strings.
+* `HybridProtocol.realViewA`, `realViewB`: the encoded views of a party in the honest runs.
+* `HybridProtocol.GoodRuns`: every run's outputs are the ideal answers.
+
+## Main results
+
+* `ComposeSim.ofFn_splitCoins`, `HybridProtocol.ofFn_composeCoins_fst`, `_snd`.
+* `HybridProtocol.answersRealA_eq_answersA`, `answersRealB_eq_answersB`: under `GoodRuns` the honest
+  answers are the ideal ones.
+* `HybridProtocol.realA_compose_eq`, `realB_compose_eq`: the real samples under `GoodRuns`.
+
+## References
+
+* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
+  University Press, 2004, §7.3.1 (the proof of Theorem 7.3.3).
+-/
+
+namespace TCSlib.Cryptography.SecureComputation
+
+open Complexity Turing TCSlib.Cryptography ComposeMachines ComposeSim Compose
+
+namespace ComposeSim
+
+/-- **A tape and `q` blocks as one string**: `{0,1}^a × ({0,1}^b)^q ≃ {0,1}^m` for
+`m = a + q·b`, the tape followed by the blocks in order (`Fin.appendEquiv`, `FunFamily.blocks`). -/
+def splitCoins {m a q b : ℕ} (h : m = a + q * b) :
+    (Fin a → Bool) × (Fin q → Fin b → Bool) ≃ (Fin m → Bool) :=
+  ((Equiv.refl (Fin a → Bool)).prodCongr (FunFamily.blocks q b).symm).trans
+    ((Fin.appendEquiv a (q * b)).trans (Equiv.arrowCongr (finCongr h.symm) (Equiv.refl Bool)))
+
+/-- The defining equation of `splitCoins` (see `splitCoins`).
+`splitCoins h = ((Equiv.refl (Fin a → Bool)).prodCongr (FunFamily.blocks q b).symm).trans
+((Fin.appendEquiv a (q * b)).trans (Equiv.arrowCongr (finCongr h.symm) (Equiv.refl Bool)))`. -/
+theorem splitCoins_eq {m a q b : ℕ} (h : m = a + q * b) :
+    splitCoins h = ((Equiv.refl (Fin a → Bool)).prodCongr (FunFamily.blocks q b).symm).trans
+      ((Fin.appendEquiv a (q * b)).trans
+        (Equiv.arrowCongr (finCongr h.symm) (Equiv.refl Bool))) := rfl
+
+/-- The blocks as one string: `⟦(blocks q b).symm t⟧ = ⟦t 0⟧ ++ ⋯ ++ ⟦t (q − 1)⟧`.
+
+**Proof sketch.** `List.ofFn_mul` writes `⟦v⟧` for `v : Fin (q·b) → Bool` as the concatenation
+of `q` blocks of `b` bits, entry `j` of block `i` being `v (i·b + j)`; by
+`FunFamily.blocks_symm_apply` that is `t i j`, since `(i·b + j) / b = i` and
+`(i·b + j) % b = j` for `j < b`. -/
+theorem ofFn_blocks_symm (q b : ℕ) (t : Fin q → Fin b → Bool) :
+    List.ofFn ((FunFamily.blocks q b).symm t) = (List.ofFn fun j => List.ofFn (t j)).flatten := by
+  rw [List.ofFn_mul]
+  congr 1
+  refine List.ofFn_inj.2 (funext fun i => List.ofFn_inj.2 (funext fun j => ?_))
+  rw [FunFamily.blocks_symm_apply]
+  have hj := j.2
+  have hb : 0 < b := by omega
+  congr 1
+  · refine Fin.ext ?_
+    rw [Fin.coe_divNat]
+    show ((i : ℕ) * b + j) / b = i
+    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt hj, Nat.zero_add]
+  · refine Fin.ext ?_
+    rw [Fin.coe_modNat]
+    show ((i : ℕ) * b + j) % b = j
+    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
+
+/-- **The split coins as a string**: `⟦splitCoins h (u, t)⟧ = ⟦u⟧ ++ ⟦t 0⟧ ++ ⋯ ++ ⟦t (q − 1)⟧`. -/
+theorem ofFn_splitCoins {m a q b : ℕ} (h : m = a + q * b) (u : Fin a → Bool)
+    (t : Fin q → Fin b → Bool) :
+    List.ofFn (splitCoins h (u, t)) =
+      List.ofFn u ++ (List.ofFn fun j => List.ofFn (t j)).flatten := by
+  rw [splitCoins_eq, Equiv.trans_apply, Equiv.trans_apply, ofFn_arrowCongr_finCongr]
+  show List.ofFn (Fin.append u ((FunFamily.blocks q b).symm t)) = _
+  rw [List.ofFn_fin_append, ofFn_blocks_symm]
+
+/-- The first `a` bits of `splitCoins h (u, t)` are `u`.
+`(List.ofFn (splitCoins h (u, t))).take a = List.ofFn u`. -/
+theorem take_ofFn_splitCoins {m a q b : ℕ} (h : m = a + q * b) (u : Fin a → Bool)
+    (t : Fin q → Fin b → Bool) : (List.ofFn (splitCoins h (u, t))).take a = List.ofFn u := by
+  rw [ofFn_splitCoins, List.take_left' List.length_ofFn]
+
+/-- Block `j < q` of `splitCoins h (u, t)` is `t j`:
+`runTape a b j ⟦splitCoins h (u, t)⟧ = ⟦t j⟧` (`Compose.runTape_eq`). -/
+theorem runTape_ofFn_splitCoins {m a q b : ℕ} (h : m = a + q * b) (u : Fin a → Bool)
+    (t : Fin q → Fin b → Bool) (j : Fin q) :
+    runTape a b j (List.ofFn (splitCoins h (u, t))) = List.ofFn (t j) := by
+  rw [runTape_eq, ofFn_splitCoins, ← List.drop_drop, List.drop_left' List.length_ofFn]
+  have hblk := coinBlock_flatten (B := b) (List.ofFn fun j => List.ofFn (t j))
+    (fun c hc => by
+      obtain ⟨i, -, rfl⟩ := List.mem_ofFn.1 hc
+      exact List.length_ofFn) j (by rw [List.length_ofFn]; exact j.2)
+  rw [coinBlock_eq] at hblk
+  rw [hblk, List.getElem_ofFn]
+
+/-- **A concatenation over `L·R` indices in `L` blocks of `R`**:
+`(range (L·R)).flatMap f = (range L).flatMap fun j => (range R).flatMap fun p => f (R·j + p)`. -/
+theorem flatMap_range_mul (f : ℕ → List Bool) (R : ℕ) : ∀ L,
+    (List.range (L * R)).flatMap f =
+      (List.range L).flatMap fun j => (List.range R).flatMap fun p => f (R * j + p)
+  | 0 => by rw [Nat.zero_mul, List.range_zero, List.flatMap_nil, List.flatMap_nil]
+  | L + 1 => by
+    rw [Nat.succ_mul, List.range_add, List.flatMap_append, flatMap_range_mul f R L,
+      List.range_succ, List.flatMap_append, List.flatMap_singleton, List.flatMap_map,
+      Nat.mul_comm L R]
+
+end ComposeSim
+
+namespace HybridProtocol
+
+/-! ### Coins of the composed protocol -/
+
+section Coins
+
+variable {G : Functionality} (H : HybridProtocol G) (ρ : Protocol)
+
+/-- Alice's composed coin length at `1^n` is `main.P.coins + calls(n)·ρ.P.coins`.
+`(H.compose ρ).P.coinLen (List.replicate n true).length = H.main.P.coinLen (List.replicate n
+true).length + H.calls.eval n * ρ.P.coinLen (List.replicate n true).length`. -/
+theorem composeP_coinLen_eq (n : ℕ) :
+    (H.compose ρ).P.coinLen (List.replicate n true).length =
+      H.main.P.coinLen (List.replicate n true).length +
+        H.calls.eval n * ρ.P.coinLen (List.replicate n true).length := by
+  rw [compose_P_coinLen, List.length_replicate]
+
+/-- Bob's composed coin length at `1^n` is `main.V.coins + calls(n)·ρ.V.coins`.
+`(H.compose ρ).V.coinLen (List.replicate n true).length = H.main.V.coinLen (List.replicate n
+true).length + H.calls.eval n * ρ.V.coinLen (List.replicate n true).length`. -/
+theorem composeV_coinLen_eq (n : ℕ) :
+    (H.compose ρ).V.coinLen (List.replicate n true).length =
+      H.main.V.coinLen (List.replicate n true).length +
+        H.calls.eval n * ρ.V.coinLen (List.replicate n true).length := by
+  rw [compose_V_coinLen, List.length_replicate]
+
+/-- **The coins of `H.compose ρ` at `1^n`** as the `main`-tapes and one pair of `ρ`-tapes per
+call: Alice's tape is her `main`-tape followed by her `ρ`-tapes, Bob's likewise.
+`H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) ≃ (H.compose
+ρ).ExecCoins (H.compose ρ).P (List.replicate n true)`. -/
+def composeCoins (n : ℕ) :
+    H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) ≃
+      (H.compose ρ).ExecCoins (H.compose ρ).P (List.replicate n true) :=
+  ((Equiv.refl (H.Coins n)).prodCongr (Equiv.arrowProdEquivProdArrow _ _ _)).trans
+    ((Equiv.prodProdProdComm _ _ _ _).trans
+      ((splitCoins (H.composeP_coinLen_eq ρ n)).prodCongr
+        (splitCoins (H.composeV_coinLen_eq ρ n))))
+
+/-- Alice's composed tape is `splitCoins` of her `main`-tape and her run tapes.
+`(H.composeCoins ρ n (m, t)).1 = splitCoins (H.composeP_coinLen_eq ρ n) (m.1, fun j => (t j).1)`. -/
+theorem composeCoins_fst (n : ℕ) (m : H.Coins n)
+    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) :
+    (H.composeCoins ρ n (m, t)).1 =
+      splitCoins (H.composeP_coinLen_eq ρ n) (m.1, fun j => (t j).1) :=
+  rfl
+
+/-- Bob's composed tape is `splitCoins` of his `main`-tape and his run tapes.
+`(H.composeCoins ρ n (m, t)).2 = splitCoins (H.composeV_coinLen_eq ρ n) (m.2, fun j => (t j).2)`. -/
+theorem composeCoins_snd (n : ℕ) (m : H.Coins n)
+    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) :
+    (H.composeCoins ρ n (m, t)).2 =
+      splitCoins (H.composeV_coinLen_eq ρ n) (m.2, fun j => (t j).2) :=
+  rfl
+
+/-- Alice's composed tape: `⟦(composeCoins (m, t)).1⟧ = ⟦m.1⟧ ++ ⟦(t 0).1⟧ ++ ⋯`. -/
+theorem ofFn_composeCoins_fst (n : ℕ) (m : H.Coins n)
+    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) :
+    List.ofFn (H.composeCoins ρ n (m, t)).1 =
+      List.ofFn m.1 ++ (List.ofFn fun j => List.ofFn (t j).1).flatten :=
+  ofFn_splitCoins (H.composeP_coinLen_eq ρ n) m.1 fun j => (t j).1
+
+/-- Bob's composed tape: `⟦(composeCoins (m, t)).2⟧ = ⟦m.2⟧ ++ ⟦(t 0).2⟧ ++ ⋯`. -/
+theorem ofFn_composeCoins_snd (n : ℕ) (m : H.Coins n)
+    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) :
+    List.ofFn (H.composeCoins ρ n (m, t)).2 =
+      List.ofFn m.2 ++ (List.ofFn fun j => List.ofFn (t j).2).flatten :=
+  ofFn_splitCoins (H.composeV_coinLen_eq ρ n) m.2 fun j => (t j).2
+
+end Coins
+
+/-! ### The runs of an honest execution -/
+
+section Runs
+
+variable {G : Functionality} (H : HybridProtocol G) (ρ : Protocol)
+
+/-- **Alice's input to call `j`** as a string: `⟦callA(n, zA, rA, j)⟧` for `j < calls(n)`, `[]`
+otherwise. -/
+def inA (n : ℕ) (zA rA : List Bool) (j : ℕ) : List Bool :=
+  if h : j < H.calls.eval n then List.ofFn (H.callA n zA rA ⟨j, h⟩) else []
+
+/-- The defining equation of `inA`: `inA n zA rA j = ⟦callA(n, zA, rA, j)⟧` for `j < calls(n)`,
+`[]` otherwise. -/
+theorem inA_eq (n : ℕ) (zA rA : List Bool) (j : ℕ) :
+    H.inA n zA rA j =
+      if h : j < H.calls.eval n then List.ofFn (H.callA n zA rA ⟨j, h⟩) else [] := rfl
+
+/-- **Bob's input to call `j`** as a string: `⟦callB(n, zB, rB, j)⟧` for `j < calls(n)`, `[]`
+otherwise. -/
+def inB (n : ℕ) (zB rB : List Bool) (j : ℕ) : List Bool :=
+  if h : j < H.calls.eval n then List.ofFn (H.callB n zB rB ⟨j, h⟩) else []
+
+/-- The defining equation of `inB`: `inB n zB rB j = ⟦callB(n, zB, rB, j)⟧` for `j < calls(n)`,
+`[]` otherwise. -/
+theorem inB_eq (n : ℕ) (zB rB : List Bool) (j : ℕ) :
+    H.inB n zB rB j =
+      if h : j < H.calls.eval n then List.ofFn (H.callB n zB rB ⟨j, h⟩) else [] := rfl
+
+/-- The call inputs do not depend on how the parameter is written:
+`N = n → ⟦callA(N, zA, rA, j)⟧ = ⟦callA(n, zA, rA, j)⟧`. -/
+theorem ofFn_callA_congr {N n : ℕ} (hN : N = n) (zA rA : List Bool) (j : ℕ)
+    (h₁ : j < H.calls.eval N) (h₂ : j < H.calls.eval n) :
+    List.ofFn (H.callA N zA rA ⟨j, h₁⟩) = List.ofFn (H.callA n zA rA ⟨j, h₂⟩) := by
+  subst hN
+  rfl
+
+/-- The call inputs do not depend on how the parameter is written:
+`N = n → ⟦callB(N, zB, rB, j)⟧ = ⟦callB(n, zB, rB, j)⟧`. -/
+theorem ofFn_callB_congr {N n : ℕ} (hN : N = n) (zB rB : List Bool) (j : ℕ)
+    (h₁ : j < H.calls.eval N) (h₂ : j < H.calls.eval n) :
+    List.ofFn (H.callB N zB rB ⟨j, h₁⟩) = List.ofFn (H.callB n zB rB ⟨j, h₂⟩) := by
+  subst hN
+  rfl
+
+/-- **The run inputs of `H.compose ρ` at `1^n` are the call inputs**: for `j < calls(n)`,
+`runInputA 1^n zA ⟦(composeCoins (m, t)).1⟧ j = inA n zA ⟦m.1⟧ j`
+(`runInputA_of_lt`, `take_ofFn_splitCoins`). -/
+theorem runInputA_composeCoins (n : ℕ) (zA : List Bool) (m : H.Coins n)
+    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) (j : ℕ) :
+    H.runInputA (List.replicate n true) zA (List.ofFn (H.composeCoins ρ n (m, t)).1) j =
+      H.inA n zA (List.ofFn m.1) j := by
+  have hN : (List.replicate n true).length = n := List.length_replicate
+  rw [inA_eq]
+  by_cases hj : j < H.calls.eval n
+  · have hj' : j < H.calls.eval (List.replicate n true).length := by rw [hN]; exact hj
+    rw [dif_pos hj, H.runInputA_of_lt _ _ _ hj', ← Strategy.coinLen_eq,
+      composeCoins_fst, take_ofFn_splitCoins (H.composeP_coinLen_eq ρ n)]
+    exact H.ofFn_callA_congr hN _ _ j hj' hj
+  · rw [dif_neg hj, H.runInputA_of_ge _ _ _ (by rw [hN]; omega)]
+
+/-- Bob's run inputs at `1^n` are his call inputs (as `runInputA_composeCoins`).
+`H.runInputB (List.replicate n true) zB (List.ofFn (H.composeCoins ρ n (m, t)).2) j = H.inB n zB
+(List.ofFn m.2) j`. -/
+theorem runInputB_composeCoins (n : ℕ) (zB : List Bool) (m : H.Coins n)
+    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) (j : ℕ) :
+    H.runInputB (List.replicate n true) zB (List.ofFn (H.composeCoins ρ n (m, t)).2) j =
+      H.inB n zB (List.ofFn m.2) j := by
+  have hN : (List.replicate n true).length = n := List.length_replicate
+  rw [inB_eq]
+  by_cases hj : j < H.calls.eval n
+  · have hj' : j < H.calls.eval (List.replicate n true).length := by rw [hN]; exact hj
+    rw [dif_pos hj, H.runInputB_of_lt _ _ _ hj', ← Strategy.coinLen_eq,
+      composeCoins_snd, take_ofFn_splitCoins (H.composeV_coinLen_eq ρ n)]
+    exact H.ofFn_callB_congr hN _ _ j hj' hj
+  · rw [dif_neg hj, H.runInputB_of_ge _ _ _ (by rw [hN]; omega)]
+
+/-- **The honest run `j` at `1^n` is `ρ`'s execution on the call inputs and the run tapes**:
+`runExec 1^n zA zB ⟦c.1⟧ ⟦c.2⟧ j k = exec ρ.P ρ.V vF 1^n (inA j) (inB j) ⟦(t j).1⟧ ⟦(t j).2⟧ k`
+for `c = composeCoins (m, t)` (`runExec_eq`, `runTape_ofFn_splitCoins`). -/
+theorem runExec_composeCoins (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
+    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) (j : Fin (H.calls.eval n))
+    (k : ℕ) :
+    H.runExec ρ (List.replicate n true) zA zB (List.ofFn (H.composeCoins ρ n (m, t)).1)
+        (List.ofFn (H.composeCoins ρ n (m, t)).2) j k =
+      exec ρ.P ρ.V ρ.verifierFirst (List.replicate n true) (H.inA n zA (List.ofFn m.1) j)
+        (H.inB n zB (List.ofFn m.2) j) (List.ofFn (t j).1) (List.ofFn (t j).2) k := by
+  rw [runExec_eq, runInputA_composeCoins, runInputB_composeCoins, ← Strategy.coinLen_eq,
+    ← Strategy.coinLen_eq, ← Strategy.coinLen_eq, ← Strategy.coinLen_eq, composeCoins_fst,
+    composeCoins_snd,
+    runTape_ofFn_splitCoins (H.composeP_coinLen_eq ρ n) m.1 (fun j => (t j).1) j,
+    runTape_ofFn_splitCoins (H.composeV_coinLen_eq ρ n) m.2 (fun j => (t j).2) j]
+
+/-- The message of `ρ`'s move `p` in the honest run `j` at `1^n` is the move of `ρ`'s execution on
+the call inputs and the run tapes (`runMsg_eq`, as `runExec_composeCoins`).
+`H.runMsg ρ (List.replicate n true) zA zB (List.ofFn (H.composeCoins ρ n (m, t)).1) (List.ofFn
+(H.composeCoins ρ n (m, t)).2) j p = moveMsg ρ.P ρ.V ρ.verifierFirst (List.replicate n true) (H.inA
+n zA (List.ofFn m.1) j) (H.inB n zB …`. -/
+theorem runMsg_composeCoins (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
+    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) (j : Fin (H.calls.eval n))
+    (p : ℕ) :
+    H.runMsg ρ (List.replicate n true) zA zB (List.ofFn (H.composeCoins ρ n (m, t)).1)
+        (List.ofFn (H.composeCoins ρ n (m, t)).2) j p =
+      moveMsg ρ.P ρ.V ρ.verifierFirst (List.replicate n true) (H.inA n zA (List.ofFn m.1) j)
+        (H.inB n zB (List.ofFn m.2) j) (List.ofFn (t j).1) (List.ofFn (t j).2) p := by
+  rw [runMsg_eq, runInputA_composeCoins, runInputB_composeCoins, ← Strategy.coinLen_eq,
+    ← Strategy.coinLen_eq, ← Strategy.coinLen_eq, ← Strategy.coinLen_eq, composeCoins_fst,
+    composeCoins_snd,
+    runTape_ofFn_splitCoins (H.composeP_coinLen_eq ρ n) m.1 (fun j => (t j).1) j,
+    runTape_ofFn_splitCoins (H.composeV_coinLen_eq ρ n) m.2 (fun j => (t j).2) j]
+
+/-- **Every run gives the ideal answers**: for every call `j`, Alice's and Bob's `ρ`-outputs in
+the run on the call inputs and the tapes `t j` are `⟦f_A(callA_j, callB_j)⟧` and
+`⟦f_B(callA_j, callB_j)⟧`.
+`H.GoodRuns ρ n zA zB m t ↔ ∀ j : Fin (H.calls.eval n), ρ.outP (List.replicate n true) (H.inA n zA
+(List.ofFn m.1) j) (H.inB n zB (List.ofFn m.2) j) (t j) = List.ofFn (G.f n (H.callA n zA (List.ofFn
+m.1) j) (H.callB n zB (List.ofFn m.2) …`. -/
+def GoodRuns (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
+    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) : Prop :=
+  ∀ j : Fin (H.calls.eval n),
+    ρ.outP (List.replicate n true) (H.inA n zA (List.ofFn m.1) j) (H.inB n zB (List.ofFn m.2) j)
+        (t j) =
+      List.ofFn (G.f n (H.callA n zA (List.ofFn m.1) j) (H.callB n zB (List.ofFn m.2) j)).1 ∧
+    ρ.outV ρ.P (List.replicate n true) (H.inA n zA (List.ofFn m.1) j)
+        (H.inB n zB (List.ofFn m.2) j) (t j) =
+      List.ofFn (G.f n (H.callA n zA (List.ofFn m.1) j) (H.callB n zB (List.ofFn m.2) j)).2
+
+/-- The defining property of `GoodRuns` (see `GoodRuns`).
+`H.GoodRuns ρ n zA zB m t ↔ ∀ j : Fin (H.calls.eval n), ρ.outP (List.replicate n true) (H.inA n zA
+(List.ofFn m.1) j) (H.inB n zB (List.ofFn m.2) j) (t j) = List.ofFn (G.f n (H.callA n zA (List.ofFn
+m.1) j) (H.callB n zB (List.ofFn m.2) …`. -/
+theorem goodRuns_iff (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
+    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) :
+    H.GoodRuns ρ n zA zB m t ↔ ∀ j : Fin (H.calls.eval n),
+      ρ.outP (List.replicate n true) (H.inA n zA (List.ofFn m.1) j)
+          (H.inB n zB (List.ofFn m.2) j) (t j) =
+        List.ofFn (G.f n (H.callA n zA (List.ofFn m.1) j) (H.callB n zB (List.ofFn m.2) j)).1 ∧
+      ρ.outV ρ.P (List.replicate n true) (H.inA n zA (List.ofFn m.1) j)
+          (H.inB n zB (List.ofFn m.2) j) (t j) =
+        List.ofFn (G.f n (H.callA n zA (List.ofFn m.1) j) (H.callB n zB (List.ofFn m.2) j)).2 :=
+  Iff.rfl
+
+/-- **Under `GoodRuns`, Alice's honest answers are the ideal ones**:
+`answersRealA 1^n zA zB ⟦c.1⟧ ⟦c.2⟧ = answersA n zA zB ⟦m.1⟧ ⟦m.2⟧` for `c = composeCoins (m, t)`.
+
+**Proof sketch.** Both are concatenations over the calls `j < L` (`flatten_ofFn_eq_flatMap_range`;
+`1^n` has length `n`). Block `j` of the honest answers is `padFin` of Alice's output of the run
+on the call inputs and the run tapes (`runInputA_composeCoins`, `runExec_composeCoins`), which is
+`ρ.outP` of that run (`Protocol.outP_eq`, `Protocol.transcriptWith_eq`), i.e. `⟦f_A(…)⟧` by
+`GoodRuns`; padding a word of the right length is the identity (`ofFn_padFin`,
+`padTo_of_length`). -/
+theorem answersRealA_eq_answersA (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
+    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true))
+    (hg : H.GoodRuns ρ n zA zB m t) :
+    H.answersRealA ρ (List.replicate n true) zA zB (List.ofFn (H.composeCoins ρ n (m, t)).1)
+        (List.ofFn (H.composeCoins ρ n (m, t)).2) =
+      H.answersA n zA zB (List.ofFn m.1) (List.ofFn m.2) := by
+  have hN : (List.replicate n true).length = n := List.length_replicate
+  rw [answersRealA_eq, answersA_eq, flatten_ofFn_eq_flatMap_range (fun j =>
+      List.ofFn (padFin (G.outA.eval (List.replicate n true).length)
+        (ρ.P.next (List.replicate n true)
+          (H.runInputA (List.replicate n true) zA (List.ofFn (H.composeCoins ρ n (m, t)).1) j)
+          (runTape (H.main.P.coins.eval (List.replicate n true).length)
+            (ρ.P.coins.eval (List.replicate n true).length) j
+            (List.ofFn (H.composeCoins ρ n (m, t)).1))
+          (H.runExec ρ (List.replicate n true) zA zB (List.ofFn (H.composeCoins ρ n (m, t)).1)
+            (List.ofFn (H.composeCoins ρ n (m, t)).2) j
+            (ρ.rounds.eval (List.replicate n true).length)).1))),
+    show (List.ofFn fun j : Fin (H.calls.eval n) =>
+        List.ofFn (G.f n (H.callA n zA (List.ofFn m.1) j) (H.callB n zB (List.ofFn m.2) j)).1
+        ).flatten = (List.range (H.calls.eval n)).flatMap fun i => if h : i < H.calls.eval n then
+          List.ofFn (G.f n (H.callA n zA (List.ofFn m.1) ⟨i, h⟩)
+            (H.callB n zB (List.ofFn m.2) ⟨i, h⟩)).1 else [] by
+      rw [← flatten_ofFn_eq_flatMap_range]
+      exact congrArg List.flatten (List.ofFn_inj.2 (funext fun j => by rw [dif_pos j.2])),
+    flatMap_range_congr (by rw [hN])]
+  refine List.flatMap_congr fun j hj => ?_
+  have hjn : j < H.calls.eval n := List.mem_range.1 hj
+  rw [dif_pos hjn, runInputA_composeCoins, ← Strategy.coinLen_eq, ← Strategy.coinLen_eq,
+    composeCoins_fst, runTape_ofFn_splitCoins (H.composeP_coinLen_eq ρ n) m.1 (fun j => (t j).1)
+      ⟨j, hjn⟩, ← composeCoins_fst, runExec_composeCoins H ρ n zA zB m t ⟨j, hjn⟩,
+    ← Protocol.transcriptWith_eq, ← Protocol.outP_eq, (hg ⟨j, hjn⟩).1, ofFn_padFin,
+    padTo_of_length (by rw [List.length_ofFn, hN])]
+
+/-- **Under `GoodRuns`, Bob's honest answers are the ideal ones**:
+`answersRealB 1^n zA zB ⟦c.1⟧ ⟦c.2⟧ = answersB n zA zB ⟦m.1⟧ ⟦m.2⟧` for `c = composeCoins (m, t)`.
+
+**Proof sketch.** As `answersRealA_eq_answersA`: block `j` of Bob's honest answers is `padFin` of
+his output in run `j` on the call inputs and the run tapes (`runInputB_composeCoins`,
+`runExec_composeCoins`), which is `ρ.outV` of that run (`Protocol.outV_eq`), i.e. `⟦f_B(…)⟧` by
+`GoodRuns`; padding a word of the right length is the identity (`ofFn_padFin`,
+`padTo_of_length`). -/
+theorem answersRealB_eq_answersB (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
+    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true))
+    (hg : H.GoodRuns ρ n zA zB m t) :
+    H.answersRealB ρ (List.replicate n true) zA zB (List.ofFn (H.composeCoins ρ n (m, t)).1)
+        (List.ofFn (H.composeCoins ρ n (m, t)).2) =
+      H.answersB n zA zB (List.ofFn m.1) (List.ofFn m.2) := by
+  have hN : (List.replicate n true).length = n := List.length_replicate
+  rw [answersRealB_eq, answersB_eq, flatten_ofFn_eq_flatMap_range (fun j =>
+      List.ofFn (padFin (G.outB.eval (List.replicate n true).length)
+        (ρ.V.next (List.replicate n true)
+          (H.runInputB (List.replicate n true) zB (List.ofFn (H.composeCoins ρ n (m, t)).2) j)
+          (runTape (H.main.V.coins.eval (List.replicate n true).length)
+            (ρ.V.coins.eval (List.replicate n true).length) j
+            (List.ofFn (H.composeCoins ρ n (m, t)).2))
+          (H.runExec ρ (List.replicate n true) zA zB (List.ofFn (H.composeCoins ρ n (m, t)).1)
+            (List.ofFn (H.composeCoins ρ n (m, t)).2) j
+            (ρ.rounds.eval (List.replicate n true).length)).2))),
+    show (List.ofFn fun j : Fin (H.calls.eval n) =>
+        List.ofFn (G.f n (H.callA n zA (List.ofFn m.1) j) (H.callB n zB (List.ofFn m.2) j)).2
+        ).flatten = (List.range (H.calls.eval n)).flatMap fun i => if h : i < H.calls.eval n then
+          List.ofFn (G.f n (H.callA n zA (List.ofFn m.1) ⟨i, h⟩)
+            (H.callB n zB (List.ofFn m.2) ⟨i, h⟩)).2 else [] by
+      rw [← flatten_ofFn_eq_flatMap_range]
+      exact congrArg List.flatten (List.ofFn_inj.2 (funext fun j => by rw [dif_pos j.2])),
+    flatMap_range_congr (by rw [hN])]
+  refine List.flatMap_congr fun j hj => ?_
+  have hjn : j < H.calls.eval n := List.mem_range.1 hj
+  rw [dif_pos hjn, runInputB_composeCoins, ← Strategy.coinLen_eq, ← Strategy.coinLen_eq,
+    composeCoins_snd, runTape_ofFn_splitCoins (H.composeV_coinLen_eq ρ n) m.2 (fun j => (t j).2)
+      ⟨j, hjn⟩, ← composeCoins_snd, runExec_composeCoins H ρ n zA zB m t ⟨j, hjn⟩,
+    ← Protocol.transcriptWith_eq (π := ρ) (P' := ρ.P), ← Protocol.outV_eq, (hg ⟨j, hjn⟩).2,
+    ofFn_padFin, padTo_of_length (by rw [List.length_ofFn, hN])]
+
+/-- **Under `GoodRuns`, the main phase is the hybrid execution on the `main`-tapes**:
+`mainExec 1^n zA zB ⟦c.1⟧ ⟦c.2⟧ k = exec main.P main.V vF 1^n (privA n zA zB ⟦m.1⟧ ⟦m.2⟧)
+(privB …) ⟦m.1⟧ ⟦m.2⟧ k` (`mainExec_eq`, the answers, `take_ofFn_splitCoins`). -/
+theorem mainExec_composeCoins (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
+    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true))
+    (hg : H.GoodRuns ρ n zA zB m t) (k : ℕ) :
+    H.mainExec ρ (List.replicate n true) zA zB (List.ofFn (H.composeCoins ρ n (m, t)).1)
+        (List.ofFn (H.composeCoins ρ n (m, t)).2) k =
+      exec H.main.P H.main.V H.main.verifierFirst (List.replicate n true)
+        (H.privA n zA zB (List.ofFn m.1) (List.ofFn m.2))
+        (H.privB n zA zB (List.ofFn m.1) (List.ofFn m.2)) (List.ofFn m.1) (List.ofFn m.2) k := by
+  rw [mainExec_eq, H.answersRealA_eq_answersA ρ n zA zB m t hg,
+    H.answersRealB_eq_answersB ρ n zA zB m t hg, privA_eq, privB_eq, ← Strategy.coinLen_eq,
+    ← Strategy.coinLen_eq, composeCoins_fst, composeCoins_snd,
+    take_ofFn_splitCoins (H.composeP_coinLen_eq ρ n),
+    take_ofFn_splitCoins (H.composeV_coinLen_eq ρ n)]
+
+/-- **Alice's encoded views of the honest runs**: for `j < calls(n)`, her view of `ρ` on the call
+inputs `inA j`, `inB j` and the tapes `t j`; `[]` otherwise. -/
+def realViewA (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
+    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) (j : ℕ) : List Bool :=
+  if h : j < H.calls.eval n then
+    (ρ.viewP (List.replicate n true) (H.inA n zA (List.ofFn m.1) j)
+      (H.inB n zB (List.ofFn m.2) j) (t ⟨j, h⟩)).encode
+  else []
+
+/-- The defining equation of `realViewA` (see `realViewA`).
+`H.realViewA ρ n zA zB m t j = if h : j < H.calls.eval n then (ρ.viewP (List.replicate n true)
+(H.inA n zA (List.ofFn m.1) j) (H.inB n zB (List.ofFn m.2) j) (t ⟨j, h⟩)).encode else []`. -/
+theorem realViewA_eq (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
+    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) (j : ℕ) :
+    H.realViewA ρ n zA zB m t j =
+      if h : j < H.calls.eval n then
+        (ρ.viewP (List.replicate n true) (H.inA n zA (List.ofFn m.1) j)
+          (H.inB n zB (List.ofFn m.2) j) (t ⟨j, h⟩)).encode
+      else [] := rfl
+
+/-- **Bob's encoded views of the honest runs** (as `realViewA`, with `ρ.viewV`).
+`H.realViewB ρ n zA zB m t j = if h : j < H.calls.eval n then (ρ.viewV (List.replicate n true)
+(H.inA n zA (List.ofFn m.1) j) (H.inB n zB (List.ofFn m.2) j) (t ⟨j, h⟩)).encode else []`. -/
+def realViewB (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
+    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) (j : ℕ) : List Bool :=
+  if h : j < H.calls.eval n then
+    (ρ.viewV (List.replicate n true) (H.inA n zA (List.ofFn m.1) j)
+      (H.inB n zB (List.ofFn m.2) j) (t ⟨j, h⟩)).encode
+  else []
+
+/-- The defining equation of `realViewB` (see `realViewB`).
+`H.realViewB ρ n zA zB m t j = if h : j < H.calls.eval n then (ρ.viewV (List.replicate n true)
+(H.inA n zA (List.ofFn m.1) j) (H.inB n zB (List.ofFn m.2) j) (t ⟨j, h⟩)).encode else []`. -/
+theorem realViewB_eq (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
+    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) (j : ℕ) :
+    H.realViewB ρ n zA zB m t j =
+      if h : j < H.calls.eval n then
+        (ρ.viewV (List.replicate n true) (H.inA n zA (List.ofFn m.1) j)
+          (H.inB n zB (List.ofFn m.2) j) (t ⟨j, h⟩)).encode
+      else [] := rfl
+
+/-- **The real sample of Alice's side under `GoodRuns`**: with `c = composeCoins (m, t)`,
+`F.realA (H.compose ρ) n x y c` is the assembled view (`ComposeSim.asmView` with `ρ.P`'s coins,
+Bob's moves read, no leading filler) of Alice's real run views, her input, her `main`-tape and
+the hybrid main phase, paired with Bob's output in the hybrid execution on the `main`-tapes.
+
+**Proof sketch.** `compose_viewP` and `compose_outV` (with `hM`) give the view and Bob's output.
+Her tape is her `main`-tape followed by the run tapes (`ofFn_composeCoins_fst`), which are the
+tapes of the run views, of exact length (`padTo_of_length`). Her messages are Bob's run messages
+at the pairs, `L` blocks of `R` (`encodeMsgs_eq_flatMap`, `flatMap_range_mul`, `slotFromB_mul_add`),
+which are the chunks `segW` of the received messages of the run views (`runExec_composeCoins`,
+`exec_eq_map`, `segW_encodeMsgs`), followed by the main phase, the hybrid one under `GoodRuns`
+(`mainExec_composeCoins`). -/
+theorem realA_compose_eq {F : Functionality} (hM : ∀ n, 0 < H.main.rounds.eval n) (n : ℕ)
+    (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (m : H.Coins n)
+    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true))
+    (hg : H.GoodRuns ρ n (List.ofFn x) (List.ofFn y) m t) :
+    F.realA (H.compose ρ) n x y (H.composeCoins ρ n (m, t)) =
+      pairEncode (asmView H.calls ρ.rounds ρ.P.coins ρ.verifierFirst true 0
+          (List.replicate n true) (List.ofFn x) (List.ofFn m.1)
+          (Strategy.encodeMsgs (H.main.transcript (List.replicate n true)
+            (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
+            (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m).1)
+          (H.realViewA ρ n (List.ofFn x) (List.ofFn y) m t))
+        (H.main.outV H.main.P (List.replicate n true)
+          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
+          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m) := by
+  have hN : (List.replicate n true).length = n := List.length_replicate
+  have hL : H.calls.eval (List.replicate n true).length = H.calls.eval n := by rw [hN]
+  -- the tape: the `main`-tape followed by the run tapes
+  have htape : List.ofFn (H.composeCoins ρ n (m, t)).1 = List.ofFn m.1 ++
+      (List.range (H.calls.eval (List.replicate n true).length)).flatMap fun j =>
+        padTo (ρ.P.coins.eval (List.replicate n true).length)
+          (pairFstD (pairSndD (H.realViewA ρ n (List.ofFn x) (List.ofFn y) m t j))) := by
+    have hT0 : (List.ofFn fun j => List.ofFn (t j).1).flatten =
+        (List.range (H.calls.eval n)).flatMap fun j =>
+          if h : j < H.calls.eval n then List.ofFn (t ⟨j, h⟩).1 else [] := by
+      rw [← flatten_ofFn_eq_flatMap_range]
+      exact congrArg List.flatten (List.ofFn_inj.2 (funext fun j => by rw [dif_pos j.2]))
+    rw [ofFn_composeCoins_fst, hT0, flatMap_range_congr hL.symm]
+    congr 1
+    refine List.flatMap_congr fun j hj => ?_
+    have hjn : j < H.calls.eval n := by rw [← hL]; exact List.mem_range.1 hj
+    rw [dif_pos hjn, realViewA_eq, dif_pos hjn, Protocol.viewP_eq, View.encode_mk,
+      pairSndD_pairEncode, pairFstD_pairEncode, padTo_of_length (by
+        rw [List.length_ofFn, Strategy.coinLen_eq])]
+  -- Bob's run messages at the pairs: the chunks of the received messages of Alice's run views
+  have hmsgs : Strategy.encodeMsgs ((List.range (H.calls.eval (List.replicate n true).length *
+      ρ.rounds.eval (List.replicate n true).length)).map
+        (H.slotFromB ρ (List.replicate n true) (List.ofFn x) (List.ofFn y)
+          (List.ofFn (H.composeCoins ρ n (m, t)).1) (List.ofFn (H.composeCoins ρ n (m, t)).2))) =
+      (List.range (H.calls.eval (List.replicate n true).length)).flatMap fun j =>
+        segW ρ.verifierFirst true (ρ.rounds.eval (List.replicate n true).length)
+          (pairSndD (pairSndD (H.realViewA ρ n (List.ofFn x) (List.ofFn y) m t j))) := by
+    rw [encodeMsgs_eq_flatMap, List.flatMap_map, flatMap_range_mul]
+    refine List.flatMap_congr fun j hj => ?_
+    have hjn : j < H.calls.eval n := by rw [← hL]; exact List.mem_range.1 hj
+    rw [realViewA_eq, dif_pos hjn, Protocol.viewP_eq, View.encode_mk, pairSndD_pairEncode,
+      pairSndD_pairEncode, Protocol.transcriptWith_eq, exec_eq_map,
+      show (List.range (ρ.rounds.eval (List.replicate n true).length)).filter
+          (moverIsV ρ.verifierFirst) =
+        (List.range (ρ.rounds.eval (List.replicate n true).length)).filter
+          (fun q => moverIsV ρ.verifierFirst q == true) from
+        List.filter_congr fun q _ => (beq_true _).symm, segW_encodeMsgs]
+    refine List.flatMap_congr fun p hp => ?_
+    rw [slotFromB_mul_add H ρ _ _ _ _ _ (List.mem_range.1 hp), beq_true,
+      runMsg_composeCoins H ρ n _ _ m t ⟨j, hjn⟩ p]
+  have hmain := H.mainExec_composeCoins ρ n (List.ofFn x) (List.ofFn y) m t hg
+    (H.main.rounds.eval (List.replicate n true).length)
+  rw [Functionality.realA_eq, compose_viewP, compose_outV H ρ _ _ _ _ (hM _), View.encode_mk,
+    asmView_eq, encodeMsgs_append, hmsgs, hmain, H.answersRealB_eq_answersB ρ n _ _ m t hg, htape,
+    List.replicate_zero, Strategy.encodeMsgs_nil, List.append_nil,
+    Protocol.transcript_eq_transcriptWith, Protocol.transcriptWith_eq, Protocol.outV_eq,
+    Protocol.transcriptWith_eq, privB_eq, ← Strategy.coinLen_eq H.main.V, composeCoins_snd,
+    take_ofFn_splitCoins (H.composeV_coinLen_eq ρ n), ← privB_eq]
+
+/-- **The real sample of Bob's side under `GoodRuns`**: with `c = composeCoins (m, t)`,
+`F.realB (H.compose ρ) n x y c` is the assembled view (`ComposeSim.asmView` with `ρ.V`'s coins,
+Alice's moves read, `lead` leading fillers) of Bob's real run views, his input, his `main`-tape
+and the hybrid main phase, paired with Alice's output in the hybrid execution.
+
+**Proof sketch.** As `realA_compose_eq`, with `compose_viewV`, `compose_outP`, the second
+components, `slotFromA_mul_add` and the leading fillers between the runs and the main phase. -/
+theorem realB_compose_eq {F : Functionality} (hM : ∀ n, 0 < H.main.rounds.eval n) (n : ℕ)
+    (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (m : H.Coins n)
+    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true))
+    (hg : H.GoodRuns ρ n (List.ofFn x) (List.ofFn y) m t) :
+    F.realB (H.compose ρ) n x y (H.composeCoins ρ n (m, t)) =
+      pairEncode (asmView H.calls ρ.rounds ρ.V.coins ρ.verifierFirst false H.lead
+          (List.replicate n true) (List.ofFn y) (List.ofFn m.2)
+          (Strategy.encodeMsgs (H.main.transcript (List.replicate n true)
+            (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
+            (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m).2)
+          (H.realViewB ρ n (List.ofFn x) (List.ofFn y) m t))
+        (H.main.outP (List.replicate n true)
+          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
+          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m) := by
+  have hN : (List.replicate n true).length = n := List.length_replicate
+  have hL : H.calls.eval (List.replicate n true).length = H.calls.eval n := by rw [hN]
+  -- the tape: the `main`-tape followed by the run tapes
+  have htape : List.ofFn (H.composeCoins ρ n (m, t)).2 = List.ofFn m.2 ++
+      (List.range (H.calls.eval (List.replicate n true).length)).flatMap fun j =>
+        padTo (ρ.V.coins.eval (List.replicate n true).length)
+          (pairFstD (pairSndD (H.realViewB ρ n (List.ofFn x) (List.ofFn y) m t j))) := by
+    have hT0 : (List.ofFn fun j => List.ofFn (t j).2).flatten =
+        (List.range (H.calls.eval n)).flatMap fun j =>
+          if h : j < H.calls.eval n then List.ofFn (t ⟨j, h⟩).2 else [] := by
+      rw [← flatten_ofFn_eq_flatMap_range]
+      exact congrArg List.flatten (List.ofFn_inj.2 (funext fun j => by rw [dif_pos j.2]))
+    rw [ofFn_composeCoins_snd, hT0, flatMap_range_congr hL.symm]
+    congr 1
+    refine List.flatMap_congr fun j hj => ?_
+    have hjn : j < H.calls.eval n := by rw [← hL]; exact List.mem_range.1 hj
+    rw [dif_pos hjn, realViewB_eq, dif_pos hjn, Protocol.viewV_eq, View.encode_mk,
+      pairSndD_pairEncode, pairFstD_pairEncode, padTo_of_length (by
+        rw [List.length_ofFn, Strategy.coinLen_eq])]
+  -- Alice's run messages at the pairs: the chunks of the received messages of Bob's run views
+  have hmsgs : Strategy.encodeMsgs ((List.range (H.calls.eval (List.replicate n true).length *
+      ρ.rounds.eval (List.replicate n true).length)).map
+        (H.slotFromA ρ (List.replicate n true) (List.ofFn x) (List.ofFn y)
+          (List.ofFn (H.composeCoins ρ n (m, t)).1) (List.ofFn (H.composeCoins ρ n (m, t)).2))) =
+      (List.range (H.calls.eval (List.replicate n true).length)).flatMap fun j =>
+        segW ρ.verifierFirst false (ρ.rounds.eval (List.replicate n true).length)
+          (pairSndD (pairSndD (H.realViewB ρ n (List.ofFn x) (List.ofFn y) m t j))) := by
+    rw [encodeMsgs_eq_flatMap, List.flatMap_map, flatMap_range_mul]
+    refine List.flatMap_congr fun j hj => ?_
+    have hjn : j < H.calls.eval n := by rw [← hL]; exact List.mem_range.1 hj
+    rw [realViewB_eq, dif_pos hjn, Protocol.viewV_eq, View.encode_mk, pairSndD_pairEncode,
+      pairSndD_pairEncode, Protocol.transcriptWith_eq, exec_eq_map,
+      show (List.range (ρ.rounds.eval (List.replicate n true).length)).filter
+          (fun i => !moverIsV ρ.verifierFirst i) =
+        (List.range (ρ.rounds.eval (List.replicate n true).length)).filter
+          (fun q => moverIsV ρ.verifierFirst q == false) from
+        List.filter_congr fun q _ => (beq_false _).symm, segW_encodeMsgs]
+    refine List.flatMap_congr fun p hp => ?_
+    rw [slotFromA_mul_add H ρ _ _ _ _ _ (List.mem_range.1 hp),
+      runMsg_composeCoins H ρ n _ _ m t ⟨j, hjn⟩ p]
+    cases moverIsV ρ.verifierFirst p <;> rfl
+  have hmain := H.mainExec_composeCoins ρ n (List.ofFn x) (List.ofFn y) m t hg
+    (H.main.rounds.eval (List.replicate n true).length)
+  rw [Functionality.realB_eq, compose_viewV, compose_outP H ρ _ _ _ _ (hM _), View.encode_mk,
+    asmView_eq, encodeMsgs_append, encodeMsgs_append, hmsgs, hmain,
+    H.answersRealA_eq_answersA ρ n _ _ m t hg, htape, Protocol.transcript_eq_transcriptWith,
+    Protocol.transcriptWith_eq, Protocol.outP_eq, Protocol.transcriptWith_eq, privA_eq,
+    ← Strategy.coinLen_eq H.main.P, composeCoins_fst,
+    take_ofFn_splitCoins (H.composeP_coinLen_eq ρ n), ← privA_eq]
+
+end Runs
+
+end HybridProtocol
+
+end TCSlib.Cryptography.SecureComputation
diff --git a/TCSlib/Cryptography/SecureComputation/ComposeSecurity/SideA.lean b/TCSlib/Cryptography/SecureComputation/ComposeSecurity/SideA.lean
new file mode 100644
index 000000000..273c979d8
--- /dev/null
+++ b/TCSlib/Cryptography/SecureComputation/ComposeSecurity/SideA.lean
@@ -0,0 +1,470 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Template
+import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Correct
+import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Chain
+import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Sim
+import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Lengths
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The composition theorem: Alice's side
+
+Steps 1–5 of the proof of the composition theorem [Gol04, §7.3.1, proof of Theorem 7.3.3] for
+Alice's real and ideal samples of `H.compose ρ`. On the `main`-tapes `m`, a run word `V j` per
+call and the sample `sampleA m V` (the assembled view of `V`, her input, her `main`-tape and the
+hybrid main phase, paired with Bob's output in `main`):
+1. under `GoodRuns` the real sample is `sampleA m (real views)` (`realA_compose_sampleA`); the
+   bad event has probability at most `L(n) ε_c(n)` (`uprob_not_goodRuns_le`, `exists_correct`);
+2. the hybrid argument replaces the real views by `ρ`'s simulator, at most `ε₂(n)` per run
+   (`exists_gapA`: the reduction `exists_gap_le` with a polynomially long template,
+   `exists_tmplA_bound`; `abs_chain_le`);
+3. `sampleA m (simulated views)` is `D ∘ Φ` on the hybrid real sample, and `D` on the simulator
+   `S_A` is `D ∘ Φ` on the hybrid ideal sample (`acceptProb_realA_dPhi`, `acceptProb_post_pre`),
+   so `H.HBCSecure F` bounds the rest (`exists_simA`).
+
+## Main definitions
+
+* `HybridProtocol.viewRunA`, `simRunA`: Alice's real and simulated run words.
+* `HybridProtocol.sampleA`: Alice's sample from run words.
+
+## Main results
+
+* `HybridProtocol.realA_compose_sampleA`, `exists_tmplA_bound`, `exists_gapA`,
+  `acceptProb_realA_dPhi`.
+* `HybridProtocol.exists_simA`: Alice's side of `hbcSecure_compose`.
+
+## References
+
+* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
+  University Press, 2004, §7.3.1 (the proof of Theorem 7.3.3).
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §6.2, Definition 155.1.
+-/
+
+namespace TCSlib.Cryptography.SecureComputation
+
+open Finset Complexity Turing TCSlib.Cryptography ComposeMachines ComposeSim ComposeProb
+  ComposeBound
+
+namespace HybridProtocol
+
+variable {G : Functionality} (H : HybridProtocol G) (ρ : Protocol)
+
+/-- **Alice's real run word** for call `j`: her encoded view of `ρ` on the call inputs
+`inA n xs ⟦m.1⟧ j`, `inB n ys ⟦m.2⟧ j` and the tapes `t`.
+`H.viewRunA ρ n xs ys m j t = (ρ.viewP (List.replicate n true) (H.inA n xs (List.ofFn m.1) j) (H.inB
+n ys (List.ofFn m.2) j) t).encode`. -/
+def viewRunA (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (j : Fin (H.calls.eval n))
+    (t : ρ.ExecCoins ρ.P (List.replicate n true)) : List Bool :=
+  (ρ.viewP (List.replicate n true) (H.inA n xs (List.ofFn m.1) j)
+    (H.inB n ys (List.ofFn m.2) j) t).encode
+
+/-- The defining equation of `viewRunA` (see `viewRunA`).
+`H.viewRunA ρ n xs ys m j t = (ρ.viewP (List.replicate n true) (H.inA n xs (List.ofFn m.1) j) (H.inB
+n ys (List.ofFn m.2) j) t).encode`. -/
+theorem viewRunA_eq (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (j : Fin (H.calls.eval n))
+    (t : ρ.ExecCoins ρ.P (List.replicate n true)) :
+    H.viewRunA ρ n xs ys m j t =
+      (ρ.viewP (List.replicate n true) (H.inA n xs (List.ofFn m.1) j)
+        (H.inB n ys (List.ofFn m.2) j) t).encode := rfl
+
+/-- **Alice's simulated run word** for call `j`: the output of `ρ`'s simulator `S` on her call
+input and her ideal answer `⟦f_A(callA_j, callB_j)⟧`, with coins `s`.
+`H.simRunA S n xs ys m j s = S.runAt n (pairEncode (H.inA n xs (List.ofFn m.1) j) (List.ofFn (G.f n
+(H.callA n xs (List.ofFn m.1) j) (H.callB n ys (List.ofFn m.2) j)).1)) s`. -/
+def simRunA (S : NUPPT) (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (j : Fin (H.calls.eval n))
+    (s : S.Coins n) : List Bool :=
+  S.runAt n (pairEncode (H.inA n xs (List.ofFn m.1) j)
+    (List.ofFn (G.f n (H.callA n xs (List.ofFn m.1) j) (H.callB n ys (List.ofFn m.2) j)).1)) s
+
+/-- The defining equation of `simRunA` (see `simRunA`).
+`H.simRunA S n xs ys m j s = S.runAt n (pairEncode (H.inA n xs (List.ofFn m.1) j) (List.ofFn (G.f n
+(H.callA n xs (List.ofFn m.1) j) (H.callB n ys (List.ofFn m.2) j)).1)) s`. -/
+theorem simRunA_eq (S : NUPPT) (n : ℕ) (xs ys : List Bool) (m : H.Coins n)
+    (j : Fin (H.calls.eval n)) (s : S.Coins n) :
+    H.simRunA S n xs ys m j s =
+      S.runAt n (pairEncode (H.inA n xs (List.ofFn m.1) j)
+        (List.ofFn (G.f n (H.callA n xs (List.ofFn m.1) j) (H.callB n ys (List.ofFn m.2) j)).1))
+        s := rfl
+
+/-- **Alice's sample from run words**: the assembled view (`asmView` with `ρ.P`'s coins, Bob's
+moves read, no leading filler) of the words `V`, her input `xs`, her `main`-tape and the hybrid
+main phase on the ideal answers, paired with Bob's output in that hybrid execution.
+`H.sampleA ρ n xs ys m V = pairEncode (asmView H.calls ρ.rounds ρ.P.coins ρ.verifierFirst true 0
+(List.replicate n true) xs (List.ofFn m.1) (Strategy.encodeMsgs (H.main.transcript (List.replicate n
+true) (H.privA n xs ys (List.ofFn m.1) …`. -/
+def sampleA (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (V : ℕ → List Bool) : List Bool :=
+  pairEncode (asmView H.calls ρ.rounds ρ.P.coins ρ.verifierFirst true 0 (List.replicate n true)
+      xs (List.ofFn m.1) (Strategy.encodeMsgs (H.main.transcript (List.replicate n true)
+        (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2))
+        (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m).1) V)
+    (H.main.outV H.main.P (List.replicate n true) (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2))
+      (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m)
+
+/-- The defining equation of `sampleA` (see `sampleA`).
+`H.sampleA ρ n xs ys m V = pairEncode (asmView H.calls ρ.rounds ρ.P.coins ρ.verifierFirst true 0
+(List.replicate n true) xs (List.ofFn m.1) (Strategy.encodeMsgs (H.main.transcript (List.replicate n
+true) (H.privA n xs ys (List.ofFn m.1) …`. -/
+theorem sampleA_eq (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (V : ℕ → List Bool) :
+    H.sampleA ρ n xs ys m V =
+      pairEncode (asmView H.calls ρ.rounds ρ.P.coins ρ.verifierFirst true 0
+          (List.replicate n true) xs (List.ofFn m.1)
+          (Strategy.encodeMsgs (H.main.transcript (List.replicate n true)
+            (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2))
+            (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m).1) V)
+        (H.main.outV H.main.P (List.replicate n true)
+          (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2))
+          (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m) := rfl
+
+/-- **The real sample under `GoodRuns`** (step 2):
+`F.realA (H.compose ρ) n x y (composeCoins (m, t)) = sampleA m (j ↦ viewRunA m j (t j))`
+(`realA_compose_eq`, `realViewA_eq`). -/
+theorem realA_compose_sampleA {F : Functionality} (hM : ∀ n, 0 < H.main.rounds.eval n) (n : ℕ)
+    (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (m : H.Coins n)
+    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true))
+    (hg : H.GoodRuns ρ n (List.ofFn x) (List.ofFn y) m t) :
+    F.realA (H.compose ρ) n x y (H.composeCoins ρ n (m, t)) =
+      H.sampleA ρ n (List.ofFn x) (List.ofFn y) m fun j =>
+        if h : j < H.calls.eval n then H.viewRunA ρ n (List.ofFn x) (List.ofFn y) m ⟨j, h⟩
+          (t ⟨j, h⟩) else [] := by
+  have hV : H.realViewA ρ n (List.ofFn x) (List.ofFn y) m t = fun j =>
+      if h : j < H.calls.eval n then H.viewRunA ρ n (List.ofFn x) (List.ofFn y) m ⟨j, h⟩
+        (t ⟨j, h⟩) else [] :=
+    funext fun j => by rw [realViewA_eq]; rfl
+  rw [H.realA_compose_eq ρ hM n x y m t hg, hV, sampleA_eq]
+
+/-- **The templates of Alice's hybrid steps are polynomially long**: for some polynomial `q`, for
+all inputs, run indices `i` and coordinates `a`, the template (`ComposeSim.tmplW`) of the header
+`⟨⟨1^n, ⟦x⟧⟩, ⟨⟦m.1⟧, main phase⟩⟩`, the run words of hybrid `i` before and after run `i`, and
+Bob's output in `main` has at most `q(n)` bits.
+`∃ q : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (i : Fin
+(H.calls.eval n)) (a : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) ×
+S.Coins n)), (tmplW (pairEncode (pairEncode …`.
+
+**Proof sketch.** The main phase and Bob's output are polynomially long (`exists_main_msgs_le`,
+`exists_main_outV_le`); every run word is a real view (`exists_viewP_le`), a simulator output on
+an argument of `2 G.inA(n) + 2 + G.outA(n)` bits (`exists_runAt_le`) or empty; at most `L(n)` of
+them are encoded (`length_encodeMsgs_le`); the rest is `length_pairEncode`. -/
+theorem exists_tmplA_bound {F : Functionality} (hH : H.PolyTime F) (hρ : G.PolyTime ρ)
+    (S : NUPPT) :
+    ∃ q : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool)
+      (i : Fin (H.calls.eval n))
+      (a : H.Coins n ×
+        (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) × S.Coins n)),
+      (tmplW (pairEncode (pairEncode (List.replicate n true) (List.ofFn x))
+          (pairEncode (List.ofFn a.1.1) (Strategy.encodeMsgs (H.main.transcript
+            (List.replicate n true)
+            (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2))
+            (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1).1)))
+        ((List.range i).map (hybV (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
+          (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a))
+        ((List.range (H.calls.eval n - (i + 1))).map fun k =>
+          hybV (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
+            (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a (i + 1 + k))
+        (H.main.outV H.main.P (List.replicate n true)
+          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2))
+          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1)).length ≤
+        q.eval n := by
+  obtain ⟨E, hE⟩ := H.exists_main_msgs_le hH
+  obtain ⟨O, hO⟩ := H.exists_main_outV_le hH
+  obtain ⟨V, hV⟩ := exists_viewP_le hρ
+  obtain ⟨Sv, hSv⟩ := exists_runAt_le S (.add (.add (.mul (.const 2) G.inA) (.const 2)) G.outA)
+  -- every run word has at most `V(n) + Sv(n)` bits
+  have hw : ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (i : ℕ)
+      (a : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) ×
+        S.Coins n)) (j : ℕ),
+      (hybV (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
+        (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a j).length ≤ V.eval n + Sv.eval n := by
+    intro n x y i a j
+    rw [hybV_eq]
+    split_ifs with h₁ h₂
+    · rw [simRunA_eq]
+      refine (hSv n _ _ ?_).trans (Nat.le_add_left _ _)
+      rw [length_pairEncode, inA_val, List.length_ofFn, List.length_ofFn]
+      simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, le_refl]
+    · rw [viewRunA_eq, inA_val, inB_val]
+      exact (hV n _ _ _).trans (Nat.le_add_right _ _)
+    · exact Nat.zero_le _
+  -- the encoded word lists
+  obtain ⟨P, hP⟩ : ∃ P : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool)
+      (y : Fin (F.inB.eval n) → Bool) (i : ℕ)
+      (a : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) ×
+        S.Coins n)) (l : List ℕ), l.length ≤ H.calls.eval n →
+      (Strategy.encodeMsgs (l.map (hybV (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
+        (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a))).length ≤ P.eval n := by
+    refine ⟨.mul H.calls (.add (.mul (.const 2) (.add V Sv)) (.const 2)),
+      fun n x y i a l hl => ?_⟩
+    refine (length_encodeMsgs_le _ (V.eval n + Sv.eval n) fun w hw' => ?_).trans ?_
+    · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hw'
+      exact hw n x y i a j
+    · rw [List.length_map]
+      simp only [PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const]
+      exact Nat.mul_le_mul_right _ hl
+  let Hd : PolyExpr := .add (.add (.mul (.const 2) (.add (.add (.mul (.const 2) .var) (.const 2))
+    F.inA)) (.const 2)) (.add (.add (.mul (.const 2) H.main.P.coins) (.const 2)) E)
+  refine ⟨.add (.add (.mul (.const 2) (.add (.add (.mul (.const 2) Hd) (.const 2)) P))
+    (.const 2)) (.add (.add (.mul (.const 2) P) (.const 2)) O), fun n x y i a => ?_⟩
+  have h₁ := hP n x y i a (List.range i) (by rw [List.length_range]; exact i.2.le)
+  have h₂ : (Strategy.encodeMsgs ((List.range (H.calls.eval n - (i + 1))).map fun k =>
+      hybV (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
+        (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a (i + 1 + k))).length ≤ P.eval n := by
+    have h := hP n x y i a ((List.range (H.calls.eval n - (i + 1))).map fun k => i + 1 + k)
+      (by rw [List.length_map, List.length_range]; omega)
+    rwa [List.map_map] at h
+  have h₃ := (hE n x y a.1).1
+  have h₄ := hO n x y a.1
+  have hc : (List.ofFn a.1.1).length = H.main.P.coins.eval n := by
+    rw [List.length_ofFn, Strategy.coinLen_eq, List.length_replicate]
+  have hu : (List.replicate n true).length = n := List.length_replicate
+  rw [tmplW_eq, length_pairEncode, length_pairEncode, length_pairEncode, length_pairEncode,
+    length_pairEncode, length_pairEncode, hc, List.length_ofFn]
+  simp only [Hd, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
+  omega
+
+/-- **Alice's hybrid steps are bounded by `ρ`'s security** (step 3): for every non-uniform PPT
+`D` there is a negligible `ε₂` with, for all `n`, inputs, run indices `i` and coordinates `a`,
+`|Pr_t[D(sampleA a.1 (plugV i a (viewRunA a.1 i t)))] −
+Pr_s[D(sampleA a.1 (plugV i a (simRunA a.1 i s)))]| ≤ ε₂(n)`.
+
+**Proof sketch.** `exists_gap_le` with `ρ`'s Alice-side samplers, the instances
+`(x, y, i, a)`, the call inputs of `a.1` at `i`, and the template of `exists_tmplA_bound`. The
+filled template is the sample: `asmW_pairEncode`, `msgAt_encodeMsgs` and `getD_plug` turn it into
+`asmView` of `plugV`, and the first component of `ρ`'s real (ideal) sample is the real
+(simulated) run word (`Functionality.realA_eq`, `idealA_eq`, `inA_val`, `inB_val`). -/
+theorem exists_gapA {F : Functionality} (hH : H.PolyTime F) (hρ : G.PolyTime ρ) (S : NUPPT)
+    (hS : ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
+      ∀ n (x : Fin (G.inA.eval n) → Bool) (y : Fin (G.inB.eval n) → Bool),
+        distAdv (G.realA ρ n x y) (G.idealA S n x y) (D.distinguisherL n) ≤ ε n)
+    (D : NUPPT) :
+    ∃ ε₂ : ℕ → ℝ, Negligible ε₂ ∧ ∀ n (x : Fin (F.inA.eval n) → Bool)
+      (y : Fin (F.inB.eval n) → Bool) (i : Fin (H.calls.eval n))
+      (a : H.Coins n ×
+        (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) × S.Coins n)),
+      |acceptProb (fun t => H.sampleA ρ n (List.ofFn x) (List.ofFn y) a.1
+          (plugV (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
+            (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a
+            (H.viewRunA ρ n (List.ofFn x) (List.ofFn y) a.1 i t))) (D.distinguisherL n) -
+        acceptProb (fun s => H.sampleA ρ n (List.ofFn x) (List.ofFn y) a.1
+          (plugV (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
+            (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a
+            (H.simRunA S n (List.ofFn x) (List.ofFn y) a.1 i s))) (D.distinguisherL n)| ≤
+        ε₂ n := by
+  obtain ⟨q, hq⟩ := H.exists_tmplA_bound ρ hH hρ S
+  obtain ⟨ε₂, hε₂, h⟩ := exists_gap_le (T := fun n => ρ.ExecCoins ρ.P (List.replicate n true))
+    (Sc := fun n => S.Coins n) (fun n => G.realA ρ n) (fun n => G.idealA S n) hS H.calls
+    ρ.rounds ρ.P.coins ρ.verifierFirst true 0
+    (Θ := fun n => (Fin (F.inA.eval n) → Bool) × (Fin (F.inB.eval n) → Bool) ×
+      Fin (H.calls.eval n) ×
+      (H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) × S.Coins n)))
+    (fun n θ => H.callA n (List.ofFn θ.1) (List.ofFn θ.2.2.2.1.1) θ.2.2.1)
+    (fun n θ => H.callB n (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.2) θ.2.2.1)
+    (fun n θ => pairEncode (pairEncode (List.replicate n true) (List.ofFn θ.1))
+      (pairEncode (List.ofFn θ.2.2.2.1.1) (Strategy.encodeMsgs (H.main.transcript
+        (List.replicate n true)
+        (H.privA n (List.ofFn θ.1) (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.1)
+          (List.ofFn θ.2.2.2.1.2))
+        (H.privB n (List.ofFn θ.1) (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.1)
+          (List.ofFn θ.2.2.2.1.2)) θ.2.2.2.1).1)))
+    (fun n θ => H.main.outV H.main.P (List.replicate n true)
+      (H.privA n (List.ofFn θ.1) (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.1)
+        (List.ofFn θ.2.2.2.1.2))
+      (H.privB n (List.ofFn θ.1) (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.1)
+        (List.ofFn θ.2.2.2.1.2)) θ.2.2.2.1)
+    (fun n θ => (List.range θ.2.2.1).map (hybV (H.viewRunA ρ n (List.ofFn θ.1) (List.ofFn θ.2.1))
+      (H.simRunA S n (List.ofFn θ.1) (List.ofFn θ.2.1)) θ.2.2.1 θ.2.2.2))
+    (fun n θ => (List.range (H.calls.eval n - (θ.2.2.1 + 1))).map fun k =>
+      hybV (H.viewRunA ρ n (List.ofFn θ.1) (List.ofFn θ.2.1))
+        (H.simRunA S n (List.ofFn θ.1) (List.ofFn θ.2.1)) θ.2.2.1 θ.2.2.2 (θ.2.2.1 + 1 + k))
+    q (fun n θ => hq n θ.1 θ.2.1 θ.2.2.1 θ.2.2.2) D
+  refine ⟨ε₂, hε₂, fun n x y i a => ?_⟩
+  -- the filled template is the sample with run `i` replaced
+  have hfill : ∀ v : List Bool, H.sampleA ρ n (List.ofFn x) (List.ofFn y) a.1
+      (plugV (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
+        (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a v) =
+      pairEncode (asmW H.calls ρ.rounds ρ.P.coins ρ.verifierFirst true 0
+        (pairEncode (pairEncode (pairEncode (List.replicate n true) (List.ofFn x))
+          (pairEncode (List.ofFn a.1.1) (Strategy.encodeMsgs (H.main.transcript
+            (List.replicate n true)
+            (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2))
+            (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1).1)))
+          (Strategy.encodeMsgs ((List.range i).map (hybV (H.viewRunA ρ n (List.ofFn x)
+            (List.ofFn y)) (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a) ++
+            v :: (List.range (H.calls.eval n - (i + 1))).map fun k =>
+              hybV (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
+                (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a (i + 1 + k)))))
+        (H.main.outV H.main.P (List.replicate n true)
+          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2))
+          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1) := by
+    intro v
+    rw [sampleA_eq, asmW_pairEncode]
+    refine congrArg (fun w => pairEncode w _) (asmView_congr _ _ _ _ _ _ _ _ _ _ fun j hj => ?_)
+    rw [List.length_replicate] at hj
+    rw [msgAt_encodeMsgs, getD_plug _ _ i.2 hj, plugV_eq]
+  have hreal : ∀ t, H.viewRunA ρ n (List.ofFn x) (List.ofFn y) a.1 i t =
+      pairFstD (G.realA ρ n (H.callA n (List.ofFn x) (List.ofFn a.1.1) i)
+        (H.callB n (List.ofFn y) (List.ofFn a.1.2) i) t) := fun t => by
+    rw [Functionality.realA_eq, pairFstD_pairEncode, viewRunA_eq, inA_val, inB_val]
+  have hsim : ∀ s, H.simRunA S n (List.ofFn x) (List.ofFn y) a.1 i s =
+      pairFstD (G.idealA S n (H.callA n (List.ofFn x) (List.ofFn a.1.1) i)
+        (H.callB n (List.ofFn y) (List.ofFn a.1.2) i) s) := fun s => by
+    rw [Functionality.idealA_eq, pairFstD_pairEncode, simRunA_eq, inA_val]
+  simp only [hfill, hreal, hsim]
+  exact h n (x, y, i, a)
+
+/-- **The simulated sample is `D ∘ Φ` on the hybrid real sample** (step 4): if `DΦ` is the
+reduction of `exists_dPhi` (coins `calls · S.coins + D.coins`), then
+`Pr[DΦ(H.realA F n x y)] = Pr_{(m, s)}[D(sampleA m (j ↦ simRunA m j (s j)))]`.
+
+**Proof sketch.** Unfold `DΦ` (`acceptProb_pre`) and read its extra coins as one block of
+`S.coins(n)` bits per call (`blocksCoins`). On `H.realA`, `phiD` keeps Bob's output and applies
+`phiV` to Alice's view of `main`, whose private input is `⟨⟦x⟧, answers⟩` (`phiD_pairEncode`,
+`phiV_view`): run `j` is `S`'s output on the call input (`hcall`, `inA_val`), the `j`-th
+answer block (`coinBlock_flatten`) and the `j`-th coin block (`coinBlock_blocksCoins`), i.e.
+`simRunA` (`NUPPT.runAtL_eq_output_layout`). -/
+theorem acceptProb_realA_dPhi {F : Functionality} (S D DΦ : NUPPT) {fA : List Bool → List Bool}
+    (hcall : ∀ n (x r : List Bool) (j : Fin (H.calls.eval n)),
+      fA (pairEncode (List.replicate n true) (pairEncode x (pairEncode r
+        (List.replicate j true)))) = List.ofFn (H.callA n x r j))
+    (hc : DΦ.coins = .add (.mul H.calls S.coins) D.coins)
+    (hD : ∀ n y r, DΦ.runAtL n y r =
+      D.runAtL n (phiD S fA H.calls ρ.rounds ρ.P.coins G.outA ρ.verifierFirst true 0
+        (pairEncode (pairEncode (List.replicate n true) (S.advice n))
+          (pairEncode y (r.take ((PolyExpr.mul H.calls S.coins).eval n)))))
+        (r.drop ((PolyExpr.mul H.calls S.coins).eval n)))
+    (n : ℕ) (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) :
+    acceptProb (H.realA F n x y) (DΦ.distinguisherL n) =
+      acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) → S.Coins n) =>
+        H.sampleA ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
+          if h : j < H.calls.eval n then H.simRunA S n (List.ofFn x) (List.ofFn y) z.1 ⟨j, h⟩
+            (z.2 ⟨j, h⟩) else []) (D.distinguisherL n) := by
+  have hlen : (PolyExpr.mul H.calls S.coins).eval n = H.calls.eval n * S.coinLen n := by
+    rw [PolyExpr.eval_mul, NUPPT.coinLen_eq]
+  rw [acceptProb_pre (H.realA F n x y) DΦ D (.mul H.calls S.coins) n
+    (fun w e => phiD S fA H.calls ρ.rounds ρ.P.coins G.outA ρ.verifierFirst true 0
+      (pairEncode (pairEncode (List.replicate n true) (S.advice n)) (pairEncode w e))) hc (hD n)]
+  refine (acceptProb_comp_equiv ((Equiv.refl (H.Coins n)).prodCongr (blocksCoins hlen)) _
+    (D.distinguisherL n)).symm.trans ?_
+  refine congrArg (fun f => acceptProb f (D.distinguisherL n)) (funext fun z => ?_)
+  show phiD S fA H.calls ρ.rounds ρ.P.coins G.outA ρ.verifierFirst true 0
+      (pairEncode (pairEncode (List.replicate n true) (S.advice n))
+        (pairEncode (H.realA F n x y z.1) (List.ofFn (blocksCoins hlen z.2)))) = _
+  rw [realA_eq, phiD_pairEncode, Protocol.viewP_eq, View.encode_mk, privA_eq, phiV_view,
+    sampleA_eq, privA_eq, Protocol.transcript_eq_transcriptWith]
+  refine congrArg (fun w => pairEncode w _) (asmView_congr _ _ _ _ _ _ _ _ _ _ fun j hj => ?_)
+  rw [List.length_replicate] at hj
+  rw [dif_pos hj, simRunA_eq, NUPPT.runAt_eq, NUPPT.runAtL_eq_output_layout,
+    hcall n (List.ofFn x) (List.ofFn z.1.1) ⟨j, hj⟩, inA_val, ← NUPPT.coinLen_eq,
+    coinBlock_blocksCoins hlen z.2 ⟨j, hj⟩, answersA_eq,
+    coinBlock_flatten _ (fun c hc' => by
+      obtain ⟨i, -, rfl⟩ := List.mem_ofFn.1 hc'
+      exact List.length_ofFn) j (by rw [List.length_ofFn]; exact hj), List.getElem_ofFn]
+
+/-- **Alice's side of the composition theorem**: from `H.HBCSecure F` and `HBCSecure ρ G`, there
+is a non-uniform PPT `S_A` such that every non-uniform PPT `D` has a negligible `ε` with
+`distAdv (F.realA (H.compose ρ) n x y) (F.idealA S_A n x y) D ≤ ε(n)` for all `n`, `x`, `y`.
+
+**Proof sketch.** `S_A` post-processes the hybrid simulator by `Φ` (`exists_simulator`). For `D`:
+1. relabel the coins (`composeCoins`); the real sample is `sampleA` of the real views except
+   on `¬ GoodRuns` (`realA_compose_sampleA`, `distAdv_le_uprob_of_eq`), of probability at most
+   `L(n) ε_c(n)` (`uprob_not_goodRuns_le`, `exists_correct`);
+2. the real and simulated views are within `L(n) ε₂(n)` (`abs_chain_le`, `exists_gapA`);
+3. `D` on the simulated views is `DΦ` on `H.realA` (`acceptProb_realA_dPhi`), and `D` on
+   `S_A` is `DΦ` on `S_A^H` (`acceptProb_post_pre`, `phiD_pairEncode`), so `H.HBCSecure F`
+   bounds this distance by `ε₃(n)`.
+The total `L(n)(ε_c(n) + ε₂(n)) + ε₃(n)` is negligible (`negligible_polyExpr_mul`). -/
+theorem exists_simA {F : Functionality} (hM : ∀ n, 0 < H.main.rounds.eval n)
+    (hH : H.HBCSecure F) (hρ : SecureComputation.HBCSecure ρ G) :
+    ∃ SA : NUPPT, ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
+      ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool),
+        distAdv (F.realA (H.compose ρ) n x y) (F.idealA SA n x y) (D.distinguisherL n) ≤ ε n := by
+  obtain ⟨hHpt, SH, SHB, hHs⟩ := (HybridProtocol.hbcSecure_iff H F).mp hH
+  obtain ⟨hρpt, SρA, SρB, hρs⟩ := (SecureComputation.hbcSecure_iff ρ G).mp hρ
+  obtain ⟨-, -, ⟨fA, hfA, hcallA⟩, -, -⟩ := (HybridProtocol.polyTime_iff H F).mp hHpt
+  obtain ⟨SA, hSAc, hSA⟩ := exists_simulator SρA H.calls ρ.rounds ρ.P.coins G.outA
+    ρ.verifierFirst true 0 SH hfA
+  refine ⟨SA, fun D => ?_⟩
+  obtain ⟨εc, hεc, hc⟩ := exists_correct SρA SρB hρs
+  obtain ⟨ε₂, hε₂, h₂⟩ := H.exists_gapA ρ hHpt hρpt SρA (fun D => by
+    obtain ⟨ε, hε, h⟩ := hρs D
+    exact ⟨ε, hε, fun n x y => (h n x y).1⟩) D
+  obtain ⟨DΦ, hDΦc, hDΦ⟩ := exists_dPhi SρA H.calls ρ.rounds ρ.P.coins G.outA ρ.verifierFirst
+    true 0 D hfA
+  obtain ⟨ε₃, hε₃, h₃⟩ := hHs DΦ
+  refine ⟨fun n => (H.calls.eval n : ℝ) * εc n + (H.calls.eval n : ℝ) * ε₂ n + ε₃ n,
+    ((negligible_polyExpr_mul hεc H.calls).add (negligible_polyExpr_mul hε₂ H.calls)).add hε₃,
+    fun n x y => ?_⟩
+  -- step 1: the statistical switch
+  have s1 : |acceptProb (F.realA (H.compose ρ) n x y) (D.distinguisherL n) -
+      acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) →
+          ρ.ExecCoins ρ.P (List.replicate n true)) =>
+        H.sampleA ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
+          if h : j < H.calls.eval n then H.viewRunA ρ n (List.ofFn x) (List.ofFn y) z.1 ⟨j, h⟩
+            (z.2 ⟨j, h⟩) else []) (D.distinguisherL n)| ≤ H.calls.eval n * εc n := by
+    rw [← acceptProb_comp_equiv (H.composeCoins ρ n) (F.realA (H.compose ρ) n x y)]
+    have h := distAdv_le_uprob_of_eq _ _ (D.distinguisherL n)
+      (fun z : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) =>
+        ¬ H.GoodRuns ρ n (List.ofFn x) (List.ofFn y) z.1 z.2)
+      (fun z hz => H.realA_compose_sampleA ρ hM n x y z.1 z.2 (not_not.1 hz))
+    rw [distAdv_def] at h
+    exact h.trans (H.uprob_not_goodRuns_le ρ n _ _ (εc n) (hc n))
+  -- step 2: the hybrid argument over the runs
+  have s2 := abs_chain_le (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
+    (H.simRunA SρA n (List.ofFn x) (List.ofFn y)) (H.sampleA ρ n (List.ofFn x) (List.ofFn y))
+    (D.distinguisherL n) (ε₂ n) (fun i a => h₂ n x y i a)
+  -- step 3: the hybrid model
+  have hid : ∀ S : NUPPT, F.idealA S n x y = fun s =>
+      pairEncode (S.runAt n (pairEncode (List.ofFn x) (List.ofFn (F.f n x y).1)) s)
+        (List.ofFn (F.f n x y).2) := fun S => funext (Functionality.idealA_eq F S n x y)
+  have e3 : acceptProb (F.idealA SA n x y) (D.distinguisherL n) =
+      acceptProb (F.idealA SH n x y) (DΦ.distinguisherL n) := by
+    rw [hid SA, hid SH]
+    exact acceptProb_post_pre SA SH DΦ D (.mul H.calls SρA.coins) n
+      (fun hv e => phiV SρA fA H.calls ρ.rounds ρ.P.coins G.outA ρ.verifierFirst true 0
+        (pairEncode (pairEncode (List.replicate n true) (SρA.advice n)) (pairEncode hv e)))
+      (fun w e => phiD SρA fA H.calls ρ.rounds ρ.P.coins G.outA ρ.verifierFirst true 0
+        (pairEncode (pairEncode (List.replicate n true) (SρA.advice n)) (pairEncode w e)))
+      (pairEncode (List.ofFn x) (List.ofFn (F.f n x y).1)) (List.ofFn (F.f n x y).2) hSAc
+      (hSA n _) hDΦc (hDΦ n) (fun hv e => phiD_pairEncode _ _ _ _ _ _ _ _ _ _ _ _ _ _)
+  have s3 : |acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) → SρA.Coins n) =>
+        H.sampleA ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
+          if h : j < H.calls.eval n then H.simRunA SρA n (List.ofFn x) (List.ofFn y) z.1
+            ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n) -
+      acceptProb (F.idealA SA n x y) (D.distinguisherL n)| ≤ ε₃ n := by
+    rw [← H.acceptProb_realA_dPhi ρ SρA D DΦ hcallA hDΦc hDΦ n x y, e3]
+    have h := (h₃ n x y).1
+    rwa [distAdv_def] at h
+  rw [distAdv_def]
+  calc |acceptProb (F.realA (H.compose ρ) n x y) (D.distinguisherL n) -
+        acceptProb (F.idealA SA n x y) (D.distinguisherL n)|
+      ≤ |acceptProb (F.realA (H.compose ρ) n x y) (D.distinguisherL n) -
+          acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) →
+            ρ.ExecCoins ρ.P (List.replicate n true)) =>
+            H.sampleA ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
+              if h : j < H.calls.eval n then H.viewRunA ρ n (List.ofFn x) (List.ofFn y) z.1
+                ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n)| +
+        |acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) →
+            ρ.ExecCoins ρ.P (List.replicate n true)) =>
+            H.sampleA ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
+              if h : j < H.calls.eval n then H.viewRunA ρ n (List.ofFn x) (List.ofFn y) z.1
+                ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n) -
+          acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) → SρA.Coins n) =>
+            H.sampleA ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
+              if h : j < H.calls.eval n then H.simRunA SρA n (List.ofFn x) (List.ofFn y) z.1
+                ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n)| +
+        |acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) → SρA.Coins n) =>
+            H.sampleA ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
+              if h : j < H.calls.eval n then H.simRunA SρA n (List.ofFn x) (List.ofFn y) z.1
+                ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n) -
+          acceptProb (F.idealA SA n x y) (D.distinguisherL n)| :=
+        (abs_sub_le _ _ _).trans (add_le_add_right (abs_sub_le _ _ _) _)
+    _ ≤ _ := add_le_add (add_le_add s1 s2) s3
+
+end HybridProtocol
+
+end TCSlib.Cryptography.SecureComputation
diff --git a/TCSlib/Cryptography/SecureComputation/ComposeSecurity/SideB.lean b/TCSlib/Cryptography/SecureComputation/ComposeSecurity/SideB.lean
new file mode 100644
index 000000000..dba483711
--- /dev/null
+++ b/TCSlib/Cryptography/SecureComputation/ComposeSecurity/SideB.lean
@@ -0,0 +1,455 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Template
+import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Correct
+import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Chain
+import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Sim
+import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Lengths
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The composition theorem: Bob's side
+
+Steps 1–5 of the proof of the composition theorem [Gol04, §7.3.1, proof of Theorem 7.3.3] for
+Bob's real and ideal samples of `H.compose ρ`, as for Alice's (`ComposeSecurity/SideA.lean`). On
+the `main`-tapes `m`, a run word `V j` per call and the sample `sampleB m V` (the assembled view of
+`V`, his input, his `main`-tape, the leading fillers and the hybrid main phase, paired with
+Alice's output in `main`):
+1. under `GoodRuns` the real sample is `sampleB m (real views)` (`realB_compose_sampleB`);
+2. the hybrid argument replaces his real views by `ρ`'s simulator (`exists_gapB`,
+   `exists_tmplB_bound`, `abs_chain_le`);
+3. `sampleB m (simulated views)` is `D ∘ Φ` on the hybrid real sample (`acceptProb_realB_dPhi`),
+   and `H.HBCSecure F` bounds the rest (`exists_simB`).
+
+## Main definitions
+
+* `HybridProtocol.viewRunB`, `simRunB`: Bob's real and simulated run words.
+* `HybridProtocol.sampleB`: Bob's sample from run words.
+
+## Main results
+
+* `HybridProtocol.realB_compose_sampleB`, `exists_tmplB_bound`, `exists_gapB`,
+  `acceptProb_realB_dPhi`.
+* `HybridProtocol.exists_simB`: Bob's side of `hbcSecure_compose`.
+
+## References
+
+* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
+  University Press, 2004, §7.3.1 (the proof of Theorem 7.3.3).
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §6.2, Definition 155.1.
+-/
+
+namespace TCSlib.Cryptography.SecureComputation
+
+open Finset Complexity Turing TCSlib.Cryptography ComposeMachines ComposeSim ComposeProb
+  ComposeBound
+
+namespace HybridProtocol
+
+variable {G : Functionality} (H : HybridProtocol G) (ρ : Protocol)
+
+/-- **Bob's real run word** for call `j`: his encoded view of `ρ` on the call inputs
+`inA n xs ⟦m.1⟧ j`, `inB n ys ⟦m.2⟧ j` and the tapes `t`.
+`H.viewRunB ρ n xs ys m j t = (ρ.viewV (List.replicate n true) (H.inA n xs (List.ofFn m.1) j) (H.inB
+n ys (List.ofFn m.2) j) t).encode`. -/
+def viewRunB (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (j : Fin (H.calls.eval n))
+    (t : ρ.ExecCoins ρ.P (List.replicate n true)) : List Bool :=
+  (ρ.viewV (List.replicate n true) (H.inA n xs (List.ofFn m.1) j)
+    (H.inB n ys (List.ofFn m.2) j) t).encode
+
+/-- The defining equation of `viewRunB` (see `viewRunB`).
+`H.viewRunB ρ n xs ys m j t = (ρ.viewV (List.replicate n true) (H.inA n xs (List.ofFn m.1) j) (H.inB
+n ys (List.ofFn m.2) j) t).encode`. -/
+theorem viewRunB_eq (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (j : Fin (H.calls.eval n))
+    (t : ρ.ExecCoins ρ.P (List.replicate n true)) :
+    H.viewRunB ρ n xs ys m j t =
+      (ρ.viewV (List.replicate n true) (H.inA n xs (List.ofFn m.1) j)
+        (H.inB n ys (List.ofFn m.2) j) t).encode := rfl
+
+/-- **Bob's simulated run word** for call `j`: the output of `ρ`'s simulator `S` on his call
+input and his ideal answer `⟦f_B(callA_j, callB_j)⟧`, with coins `s`.
+`H.simRunB S n xs ys m j s = S.runAt n (pairEncode (H.inB n ys (List.ofFn m.2) j) (List.ofFn (G.f n
+(H.callA n xs (List.ofFn m.1) j) (H.callB n ys (List.ofFn m.2) j)).2)) s`. -/
+def simRunB (S : NUPPT) (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (j : Fin (H.calls.eval n))
+    (s : S.Coins n) : List Bool :=
+  S.runAt n (pairEncode (H.inB n ys (List.ofFn m.2) j)
+    (List.ofFn (G.f n (H.callA n xs (List.ofFn m.1) j) (H.callB n ys (List.ofFn m.2) j)).2)) s
+
+/-- The defining equation of `simRunB` (see `simRunB`).
+`H.simRunB S n xs ys m j s = S.runAt n (pairEncode (H.inB n ys (List.ofFn m.2) j) (List.ofFn (G.f n
+(H.callA n xs (List.ofFn m.1) j) (H.callB n ys (List.ofFn m.2) j)).2)) s`. -/
+theorem simRunB_eq (S : NUPPT) (n : ℕ) (xs ys : List Bool) (m : H.Coins n)
+    (j : Fin (H.calls.eval n)) (s : S.Coins n) :
+    H.simRunB S n xs ys m j s =
+      S.runAt n (pairEncode (H.inB n ys (List.ofFn m.2) j)
+        (List.ofFn (G.f n (H.callA n xs (List.ofFn m.1) j) (H.callB n ys (List.ofFn m.2) j)).2))
+        s := rfl
+
+/-- **Bob's sample from run words**: the assembled view (`asmView` with `ρ.V`'s coins, Alice's
+moves read, `lead` leading fillers) of the words `V`, his input `ys`, his `main`-tape and the
+hybrid main phase on the ideal answers, paired with Alice's output in that hybrid execution.
+`H.sampleB ρ n xs ys m V = pairEncode (asmView H.calls ρ.rounds ρ.V.coins ρ.verifierFirst false
+H.lead (List.replicate n true) ys (List.ofFn m.2) (Strategy.encodeMsgs (H.main.transcript
+(List.replicate n true) (H.privA n xs ys (List.ofFn …`. -/
+def sampleB (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (V : ℕ → List Bool) : List Bool :=
+  pairEncode (asmView H.calls ρ.rounds ρ.V.coins ρ.verifierFirst false H.lead
+      (List.replicate n true) ys (List.ofFn m.2) (Strategy.encodeMsgs (H.main.transcript
+        (List.replicate n true) (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2))
+        (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m).2) V)
+    (H.main.outP (List.replicate n true) (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2))
+      (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m)
+
+/-- The defining equation of `sampleB` (see `sampleB`).
+`H.sampleB ρ n xs ys m V = pairEncode (asmView H.calls ρ.rounds ρ.V.coins ρ.verifierFirst false
+H.lead (List.replicate n true) ys (List.ofFn m.2) (Strategy.encodeMsgs (H.main.transcript
+(List.replicate n true) (H.privA n xs ys (List.ofFn …`. -/
+theorem sampleB_eq (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (V : ℕ → List Bool) :
+    H.sampleB ρ n xs ys m V =
+      pairEncode (asmView H.calls ρ.rounds ρ.V.coins ρ.verifierFirst false H.lead
+          (List.replicate n true) ys (List.ofFn m.2)
+          (Strategy.encodeMsgs (H.main.transcript (List.replicate n true)
+            (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2))
+            (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m).2) V)
+        (H.main.outP (List.replicate n true) (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2))
+          (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m) := rfl
+
+/-- **Bob's real sample under `GoodRuns`** (step 2): `F.realB (H.compose ρ) n x y (composeCoins
+(m, t)) = sampleB m (j ↦ viewRunB m j (t j))` (`realB_compose_eq`, `realViewB_eq`). -/
+theorem realB_compose_sampleB {F : Functionality} (hM : ∀ n, 0 < H.main.rounds.eval n) (n : ℕ)
+    (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (m : H.Coins n)
+    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true))
+    (hg : H.GoodRuns ρ n (List.ofFn x) (List.ofFn y) m t) :
+    F.realB (H.compose ρ) n x y (H.composeCoins ρ n (m, t)) =
+      H.sampleB ρ n (List.ofFn x) (List.ofFn y) m fun j =>
+        if h : j < H.calls.eval n then H.viewRunB ρ n (List.ofFn x) (List.ofFn y) m ⟨j, h⟩
+          (t ⟨j, h⟩) else [] := by
+  have hV : H.realViewB ρ n (List.ofFn x) (List.ofFn y) m t = fun j =>
+      if h : j < H.calls.eval n then H.viewRunB ρ n (List.ofFn x) (List.ofFn y) m ⟨j, h⟩
+        (t ⟨j, h⟩) else [] :=
+    funext fun j => by rw [realViewB_eq]; rfl
+  rw [H.realB_compose_eq ρ hM n x y m t hg, hV, sampleB_eq]
+
+/-- **The templates of Bob's hybrid steps are polynomially long**: for some polynomial `q`, for
+all inputs, run indices `i` and coordinates `a`, the template (`ComposeSim.tmplW`) of the header
+`⟨⟨1^n, ⟦y⟧⟩, ⟨⟦m.2⟧, main phase⟩⟩`, the run words of hybrid `i` before and after run `i`, and
+Alice's output in `main` has at most `q(n)` bits.
+`∃ q : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (i : Fin
+(H.calls.eval n)) (a : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) ×
+S.Coins n)), (tmplW (pairEncode (pairEncode …`.
+
+**Proof sketch.** As `exists_tmplA_bound`, with Bob's half of the main phase
+(`exists_main_msgs_le`), Alice's output (`exists_main_outP_le`), Bob's views (`exists_viewV_le`)
+and simulator outputs on arguments of `2 G.inB(n) + 2 + G.outB(n)` bits (`exists_runAt_le`). -/
+theorem exists_tmplB_bound {F : Functionality} (hH : H.PolyTime F) (hρ : G.PolyTime ρ)
+    (S : NUPPT) :
+    ∃ q : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool)
+      (i : Fin (H.calls.eval n))
+      (a : H.Coins n ×
+        (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) × S.Coins n)),
+      (tmplW (pairEncode (pairEncode (List.replicate n true) (List.ofFn y))
+          (pairEncode (List.ofFn a.1.2) (Strategy.encodeMsgs (H.main.transcript
+            (List.replicate n true)
+            (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2))
+            (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1).2)))
+        ((List.range i).map (hybV (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
+          (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a))
+        ((List.range (H.calls.eval n - (i + 1))).map fun k =>
+          hybV (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
+            (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a (i + 1 + k))
+        (H.main.outP (List.replicate n true)
+          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2))
+          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1)).length ≤
+        q.eval n := by
+  obtain ⟨E, hE⟩ := H.exists_main_msgs_le hH
+  obtain ⟨O, hO⟩ := H.exists_main_outP_le hH
+  obtain ⟨V, hV⟩ := exists_viewV_le hρ
+  obtain ⟨Sv, hSv⟩ := exists_runAt_le S (.add (.add (.mul (.const 2) G.inB) (.const 2)) G.outB)
+  -- every run word has at most `V(n) + Sv(n)` bits
+  have hw : ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (i : ℕ)
+      (a : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) ×
+        S.Coins n)) (j : ℕ),
+      (hybV (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
+        (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a j).length ≤ V.eval n + Sv.eval n := by
+    intro n x y i a j
+    rw [hybV_eq]
+    split_ifs with h₁ h₂
+    · rw [simRunB_eq]
+      refine (hSv n _ _ ?_).trans (Nat.le_add_left _ _)
+      rw [length_pairEncode, inB_val, List.length_ofFn, List.length_ofFn]
+      simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, le_refl]
+    · rw [viewRunB_eq, inA_val, inB_val]
+      exact (hV n _ _ _).trans (Nat.le_add_right _ _)
+    · exact Nat.zero_le _
+  -- the encoded word lists
+  obtain ⟨P, hP⟩ : ∃ P : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool)
+      (y : Fin (F.inB.eval n) → Bool) (i : ℕ)
+      (a : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) ×
+        S.Coins n)) (l : List ℕ), l.length ≤ H.calls.eval n →
+      (Strategy.encodeMsgs (l.map (hybV (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
+        (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a))).length ≤ P.eval n := by
+    refine ⟨.mul H.calls (.add (.mul (.const 2) (.add V Sv)) (.const 2)),
+      fun n x y i a l hl => ?_⟩
+    refine (length_encodeMsgs_le _ (V.eval n + Sv.eval n) fun w hw' => ?_).trans ?_
+    · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hw'
+      exact hw n x y i a j
+    · rw [List.length_map]
+      simp only [PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const]
+      exact Nat.mul_le_mul_right _ hl
+  let Hd : PolyExpr := .add (.add (.mul (.const 2) (.add (.add (.mul (.const 2) .var) (.const 2))
+    F.inB)) (.const 2)) (.add (.add (.mul (.const 2) H.main.V.coins) (.const 2)) E)
+  refine ⟨.add (.add (.mul (.const 2) (.add (.add (.mul (.const 2) Hd) (.const 2)) P))
+    (.const 2)) (.add (.add (.mul (.const 2) P) (.const 2)) O), fun n x y i a => ?_⟩
+  have h₁ := hP n x y i a (List.range i) (by rw [List.length_range]; exact i.2.le)
+  have h₂ : (Strategy.encodeMsgs ((List.range (H.calls.eval n - (i + 1))).map fun k =>
+      hybV (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
+        (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a (i + 1 + k))).length ≤ P.eval n := by
+    have h := hP n x y i a ((List.range (H.calls.eval n - (i + 1))).map fun k => i + 1 + k)
+      (by rw [List.length_map, List.length_range]; omega)
+    rwa [List.map_map] at h
+  have h₃ := (hE n x y a.1).2
+  have h₄ := hO n x y a.1
+  have hc : (List.ofFn a.1.2).length = H.main.V.coins.eval n := by
+    rw [List.length_ofFn, Strategy.coinLen_eq, List.length_replicate]
+  have hu : (List.replicate n true).length = n := List.length_replicate
+  rw [tmplW_eq, length_pairEncode, length_pairEncode, length_pairEncode, length_pairEncode,
+    length_pairEncode, length_pairEncode, hc, List.length_ofFn]
+  simp only [Hd, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
+  omega
+
+/-- **Bob's hybrid steps are bounded by `ρ`'s security** (step 3): for every non-uniform PPT `D`
+there is a negligible `ε₂` with, for all `n`, inputs, run indices `i` and coordinates `a`,
+`|Pr_t[D(sampleB a.1 (plugV i a (viewRunB a.1 i t)))] −
+Pr_s[D(sampleB a.1 (plugV i a (simRunB a.1 i s)))]| ≤ ε₂(n)`.
+
+**Proof sketch.** As `exists_gapA`: `exists_gap_le` with `ρ`'s Bob-side samplers and the
+template of `exists_tmplB_bound`; the first component of `ρ`'s real (ideal) Bob sample is the
+real (simulated) run word (`Functionality.realB_eq`, `idealB_eq`, `inA_val`, `inB_val`). -/
+theorem exists_gapB {F : Functionality} (hH : H.PolyTime F) (hρ : G.PolyTime ρ) (S : NUPPT)
+    (hS : ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
+      ∀ n (x : Fin (G.inA.eval n) → Bool) (y : Fin (G.inB.eval n) → Bool),
+        distAdv (G.realB ρ n x y) (G.idealB S n x y) (D.distinguisherL n) ≤ ε n)
+    (D : NUPPT) :
+    ∃ ε₂ : ℕ → ℝ, Negligible ε₂ ∧ ∀ n (x : Fin (F.inA.eval n) → Bool)
+      (y : Fin (F.inB.eval n) → Bool) (i : Fin (H.calls.eval n))
+      (a : H.Coins n ×
+        (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) × S.Coins n)),
+      |acceptProb (fun t => H.sampleB ρ n (List.ofFn x) (List.ofFn y) a.1
+          (plugV (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
+            (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a
+            (H.viewRunB ρ n (List.ofFn x) (List.ofFn y) a.1 i t))) (D.distinguisherL n) -
+        acceptProb (fun s => H.sampleB ρ n (List.ofFn x) (List.ofFn y) a.1
+          (plugV (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
+            (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a
+            (H.simRunB S n (List.ofFn x) (List.ofFn y) a.1 i s))) (D.distinguisherL n)| ≤
+        ε₂ n := by
+  obtain ⟨q, hq⟩ := H.exists_tmplB_bound ρ hH hρ S
+  obtain ⟨ε₂, hε₂, h⟩ := exists_gap_le (T := fun n => ρ.ExecCoins ρ.P (List.replicate n true))
+    (Sc := fun n => S.Coins n) (fun n => G.realB ρ n) (fun n => G.idealB S n) hS H.calls
+    ρ.rounds ρ.V.coins ρ.verifierFirst false H.lead
+    (Θ := fun n => (Fin (F.inA.eval n) → Bool) × (Fin (F.inB.eval n) → Bool) ×
+      Fin (H.calls.eval n) ×
+      (H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) × S.Coins n)))
+    (fun n θ => H.callA n (List.ofFn θ.1) (List.ofFn θ.2.2.2.1.1) θ.2.2.1)
+    (fun n θ => H.callB n (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.2) θ.2.2.1)
+    (fun n θ => pairEncode (pairEncode (List.replicate n true) (List.ofFn θ.2.1))
+      (pairEncode (List.ofFn θ.2.2.2.1.2) (Strategy.encodeMsgs (H.main.transcript
+        (List.replicate n true)
+        (H.privA n (List.ofFn θ.1) (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.1)
+          (List.ofFn θ.2.2.2.1.2))
+        (H.privB n (List.ofFn θ.1) (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.1)
+          (List.ofFn θ.2.2.2.1.2)) θ.2.2.2.1).2)))
+    (fun n θ => H.main.outP (List.replicate n true)
+      (H.privA n (List.ofFn θ.1) (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.1)
+        (List.ofFn θ.2.2.2.1.2))
+      (H.privB n (List.ofFn θ.1) (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.1)
+        (List.ofFn θ.2.2.2.1.2)) θ.2.2.2.1)
+    (fun n θ => (List.range θ.2.2.1).map (hybV (H.viewRunB ρ n (List.ofFn θ.1) (List.ofFn θ.2.1))
+      (H.simRunB S n (List.ofFn θ.1) (List.ofFn θ.2.1)) θ.2.2.1 θ.2.2.2))
+    (fun n θ => (List.range (H.calls.eval n - (θ.2.2.1 + 1))).map fun k =>
+      hybV (H.viewRunB ρ n (List.ofFn θ.1) (List.ofFn θ.2.1))
+        (H.simRunB S n (List.ofFn θ.1) (List.ofFn θ.2.1)) θ.2.2.1 θ.2.2.2 (θ.2.2.1 + 1 + k))
+    q (fun n θ => hq n θ.1 θ.2.1 θ.2.2.1 θ.2.2.2) D
+  refine ⟨ε₂, hε₂, fun n x y i a => ?_⟩
+  -- the filled template is the sample with run `i` replaced
+  have hfill : ∀ v : List Bool, H.sampleB ρ n (List.ofFn x) (List.ofFn y) a.1
+      (plugV (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
+        (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a v) =
+      pairEncode (asmW H.calls ρ.rounds ρ.V.coins ρ.verifierFirst false H.lead
+        (pairEncode (pairEncode (pairEncode (List.replicate n true) (List.ofFn y))
+          (pairEncode (List.ofFn a.1.2) (Strategy.encodeMsgs (H.main.transcript
+            (List.replicate n true)
+            (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2))
+            (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1).2)))
+          (Strategy.encodeMsgs ((List.range i).map (hybV (H.viewRunB ρ n (List.ofFn x)
+            (List.ofFn y)) (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a) ++
+            v :: (List.range (H.calls.eval n - (i + 1))).map fun k =>
+              hybV (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
+                (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a (i + 1 + k)))))
+        (H.main.outP (List.replicate n true)
+          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2))
+          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1) := by
+    intro v
+    rw [sampleB_eq, asmW_pairEncode]
+    refine congrArg (fun w => pairEncode w _) (asmView_congr _ _ _ _ _ _ _ _ _ _ fun j hj => ?_)
+    rw [List.length_replicate] at hj
+    rw [msgAt_encodeMsgs, getD_plug _ _ i.2 hj, plugV_eq]
+  have hreal : ∀ t, H.viewRunB ρ n (List.ofFn x) (List.ofFn y) a.1 i t =
+      pairFstD (G.realB ρ n (H.callA n (List.ofFn x) (List.ofFn a.1.1) i)
+        (H.callB n (List.ofFn y) (List.ofFn a.1.2) i) t) := fun t => by
+    rw [Functionality.realB_eq, pairFstD_pairEncode, viewRunB_eq, inA_val, inB_val]
+  have hsim : ∀ s, H.simRunB S n (List.ofFn x) (List.ofFn y) a.1 i s =
+      pairFstD (G.idealB S n (H.callA n (List.ofFn x) (List.ofFn a.1.1) i)
+        (H.callB n (List.ofFn y) (List.ofFn a.1.2) i) s) := fun s => by
+    rw [Functionality.idealB_eq, pairFstD_pairEncode, simRunB_eq, inB_val]
+  simp only [hfill, hreal, hsim]
+  exact h n (x, y, i, a)
+
+/-- **Bob's simulated sample is `D ∘ Φ` on the hybrid real sample** (step 4): if `DΦ` is the
+reduction of `exists_dPhi` for Bob's post-processing (coins `calls · S.coins + D.coins`), then
+`Pr[DΦ(H.realB F n x y)] = Pr_{(m, s)}[D(sampleB m (j ↦ simRunB m j (s j)))]`.
+
+**Proof sketch.** As `acceptProb_realA_dPhi`, with Bob's view of `main`, whose private input is
+`⟨⟦y⟧, answers⟩`, his call inputs (`hcall`, `inB_val`) and his answer blocks. -/
+theorem acceptProb_realB_dPhi {F : Functionality} (S D DΦ : NUPPT) {fB : List Bool → List Bool}
+    (hcall : ∀ n (y r : List Bool) (j : Fin (H.calls.eval n)),
+      fB (pairEncode (List.replicate n true) (pairEncode y (pairEncode r
+        (List.replicate j true)))) = List.ofFn (H.callB n y r j))
+    (hc : DΦ.coins = .add (.mul H.calls S.coins) D.coins)
+    (hD : ∀ n y r, DΦ.runAtL n y r =
+      D.runAtL n (phiD S fB H.calls ρ.rounds ρ.V.coins G.outB ρ.verifierFirst false H.lead
+        (pairEncode (pairEncode (List.replicate n true) (S.advice n))
+          (pairEncode y (r.take ((PolyExpr.mul H.calls S.coins).eval n)))))
+        (r.drop ((PolyExpr.mul H.calls S.coins).eval n)))
+    (n : ℕ) (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) :
+    acceptProb (H.realB F n x y) (DΦ.distinguisherL n) =
+      acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) → S.Coins n) =>
+        H.sampleB ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
+          if h : j < H.calls.eval n then H.simRunB S n (List.ofFn x) (List.ofFn y) z.1 ⟨j, h⟩
+            (z.2 ⟨j, h⟩) else []) (D.distinguisherL n) := by
+  have hlen : (PolyExpr.mul H.calls S.coins).eval n = H.calls.eval n * S.coinLen n := by
+    rw [PolyExpr.eval_mul, NUPPT.coinLen_eq]
+  rw [acceptProb_pre (H.realB F n x y) DΦ D (.mul H.calls S.coins) n
+    (fun w e => phiD S fB H.calls ρ.rounds ρ.V.coins G.outB ρ.verifierFirst false H.lead
+      (pairEncode (pairEncode (List.replicate n true) (S.advice n)) (pairEncode w e))) hc (hD n)]
+  refine (acceptProb_comp_equiv ((Equiv.refl (H.Coins n)).prodCongr (blocksCoins hlen)) _
+    (D.distinguisherL n)).symm.trans ?_
+  refine congrArg (fun f => acceptProb f (D.distinguisherL n)) (funext fun z => ?_)
+  show phiD S fB H.calls ρ.rounds ρ.V.coins G.outB ρ.verifierFirst false H.lead
+      (pairEncode (pairEncode (List.replicate n true) (S.advice n))
+        (pairEncode (H.realB F n x y z.1) (List.ofFn (blocksCoins hlen z.2)))) = _
+  rw [realB_eq, phiD_pairEncode, Protocol.viewV_eq, View.encode_mk, privB_eq, phiV_view,
+    sampleB_eq, privB_eq, Protocol.transcript_eq_transcriptWith]
+  refine congrArg (fun w => pairEncode w _) (asmView_congr _ _ _ _ _ _ _ _ _ _ fun j hj => ?_)
+  rw [List.length_replicate] at hj
+  rw [dif_pos hj, simRunB_eq, NUPPT.runAt_eq, NUPPT.runAtL_eq_output_layout,
+    hcall n (List.ofFn y) (List.ofFn z.1.2) ⟨j, hj⟩, inB_val, ← NUPPT.coinLen_eq,
+    coinBlock_blocksCoins hlen z.2 ⟨j, hj⟩, answersB_eq,
+    coinBlock_flatten _ (fun c hc' => by
+      obtain ⟨i, -, rfl⟩ := List.mem_ofFn.1 hc'
+      exact List.length_ofFn) j (by rw [List.length_ofFn]; exact hj), List.getElem_ofFn]
+
+/-- **Bob's side of the composition theorem**: from `H.HBCSecure F` and `HBCSecure ρ G`, there is
+a non-uniform PPT `S_B` such that every non-uniform PPT `D` has a negligible `ε` with
+`distAdv (F.realB (H.compose ρ) n x y) (F.idealB S_B n x y) D ≤ ε(n)` for all `n`, `x`, `y`.
+
+**Proof sketch.** As `exists_simA`, with Bob's simulator post-processed by Bob's `Φ`
+(`exists_simulator` with `ρ.V`'s coins, Alice's moves read and `lead` fillers), his real sample
+(`realB_compose_sampleB`), the same bad event, the hybrid argument over his views
+(`exists_gapB`, `abs_chain_le`) and the hybrid model (`acceptProb_realB_dPhi`,
+`acceptProb_post_pre`). -/
+theorem exists_simB {F : Functionality} (hM : ∀ n, 0 < H.main.rounds.eval n)
+    (hH : H.HBCSecure F) (hρ : SecureComputation.HBCSecure ρ G) :
+    ∃ SB : NUPPT, ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
+      ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool),
+        distAdv (F.realB (H.compose ρ) n x y) (F.idealB SB n x y) (D.distinguisherL n) ≤ ε n := by
+  obtain ⟨hHpt, SHA, SH, hHs⟩ := (HybridProtocol.hbcSecure_iff H F).mp hH
+  obtain ⟨hρpt, SρA, SρB, hρs⟩ := (SecureComputation.hbcSecure_iff ρ G).mp hρ
+  obtain ⟨-, -, -, ⟨fB, hfB, hcallB⟩, -⟩ := (HybridProtocol.polyTime_iff H F).mp hHpt
+  obtain ⟨SB, hSBc, hSB⟩ := exists_simulator SρB H.calls ρ.rounds ρ.V.coins G.outB
+    ρ.verifierFirst false H.lead SH hfB
+  refine ⟨SB, fun D => ?_⟩
+  obtain ⟨εc, hεc, hc⟩ := exists_correct SρA SρB hρs
+  obtain ⟨ε₂, hε₂, h₂⟩ := H.exists_gapB ρ hHpt hρpt SρB (fun D => by
+    obtain ⟨ε, hε, h⟩ := hρs D
+    exact ⟨ε, hε, fun n x y => (h n x y).2⟩) D
+  obtain ⟨DΦ, hDΦc, hDΦ⟩ := exists_dPhi SρB H.calls ρ.rounds ρ.V.coins G.outB ρ.verifierFirst
+    false H.lead D hfB
+  obtain ⟨ε₃, hε₃, h₃⟩ := hHs DΦ
+  refine ⟨fun n => (H.calls.eval n : ℝ) * εc n + (H.calls.eval n : ℝ) * ε₂ n + ε₃ n,
+    ((negligible_polyExpr_mul hεc H.calls).add (negligible_polyExpr_mul hε₂ H.calls)).add hε₃,
+    fun n x y => ?_⟩
+  -- step 1: the statistical switch
+  have s1 : |acceptProb (F.realB (H.compose ρ) n x y) (D.distinguisherL n) -
+      acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) →
+          ρ.ExecCoins ρ.P (List.replicate n true)) =>
+        H.sampleB ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
+          if h : j < H.calls.eval n then H.viewRunB ρ n (List.ofFn x) (List.ofFn y) z.1 ⟨j, h⟩
+            (z.2 ⟨j, h⟩) else []) (D.distinguisherL n)| ≤ H.calls.eval n * εc n := by
+    rw [← acceptProb_comp_equiv (H.composeCoins ρ n) (F.realB (H.compose ρ) n x y)]
+    have h := distAdv_le_uprob_of_eq _ _ (D.distinguisherL n)
+      (fun z : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) =>
+        ¬ H.GoodRuns ρ n (List.ofFn x) (List.ofFn y) z.1 z.2)
+      (fun z hz => H.realB_compose_sampleB ρ hM n x y z.1 z.2 (not_not.1 hz))
+    rw [distAdv_def] at h
+    exact h.trans (H.uprob_not_goodRuns_le ρ n _ _ (εc n) (hc n))
+  -- step 2: the hybrid argument over the runs
+  have s2 := abs_chain_le (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
+    (H.simRunB SρB n (List.ofFn x) (List.ofFn y)) (H.sampleB ρ n (List.ofFn x) (List.ofFn y))
+    (D.distinguisherL n) (ε₂ n) (fun i a => h₂ n x y i a)
+  -- step 3: the hybrid model
+  have hid : ∀ S : NUPPT, F.idealB S n x y = fun s =>
+      pairEncode (S.runAt n (pairEncode (List.ofFn y) (List.ofFn (F.f n x y).2)) s)
+        (List.ofFn (F.f n x y).1) := fun S => funext (Functionality.idealB_eq F S n x y)
+  have e3 : acceptProb (F.idealB SB n x y) (D.distinguisherL n) =
+      acceptProb (F.idealB SH n x y) (DΦ.distinguisherL n) := by
+    rw [hid SB, hid SH]
+    exact acceptProb_post_pre SB SH DΦ D (.mul H.calls SρB.coins) n
+      (fun hv e => phiV SρB fB H.calls ρ.rounds ρ.V.coins G.outB ρ.verifierFirst false H.lead
+        (pairEncode (pairEncode (List.replicate n true) (SρB.advice n)) (pairEncode hv e)))
+      (fun w e => phiD SρB fB H.calls ρ.rounds ρ.V.coins G.outB ρ.verifierFirst false H.lead
+        (pairEncode (pairEncode (List.replicate n true) (SρB.advice n)) (pairEncode w e)))
+      (pairEncode (List.ofFn y) (List.ofFn (F.f n x y).2)) (List.ofFn (F.f n x y).1) hSBc
+      (hSB n _) hDΦc (hDΦ n) (fun hv e => phiD_pairEncode _ _ _ _ _ _ _ _ _ _ _ _ _ _)
+  have s3 : |acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) → SρB.Coins n) =>
+        H.sampleB ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
+          if h : j < H.calls.eval n then H.simRunB SρB n (List.ofFn x) (List.ofFn y) z.1
+            ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n) -
+      acceptProb (F.idealB SB n x y) (D.distinguisherL n)| ≤ ε₃ n := by
+    rw [← H.acceptProb_realB_dPhi ρ SρB D DΦ hcallB hDΦc hDΦ n x y, e3]
+    have h := (h₃ n x y).2
+    rwa [distAdv_def] at h
+  rw [distAdv_def]
+  calc |acceptProb (F.realB (H.compose ρ) n x y) (D.distinguisherL n) -
+        acceptProb (F.idealB SB n x y) (D.distinguisherL n)|
+      ≤ |acceptProb (F.realB (H.compose ρ) n x y) (D.distinguisherL n) -
+          acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) →
+            ρ.ExecCoins ρ.P (List.replicate n true)) =>
+            H.sampleB ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
+              if h : j < H.calls.eval n then H.viewRunB ρ n (List.ofFn x) (List.ofFn y) z.1
+                ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n)| +
+        |acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) →
+            ρ.ExecCoins ρ.P (List.replicate n true)) =>
+            H.sampleB ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
+              if h : j < H.calls.eval n then H.viewRunB ρ n (List.ofFn x) (List.ofFn y) z.1
+                ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n) -
+          acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) → SρB.Coins n) =>
+            H.sampleB ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
+              if h : j < H.calls.eval n then H.simRunB SρB n (List.ofFn x) (List.ofFn y) z.1
+                ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n)| +
+        |acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) → SρB.Coins n) =>
+            H.sampleB ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
+              if h : j < H.calls.eval n then H.simRunB SρB n (List.ofFn x) (List.ofFn y) z.1
+                ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n) -
+          acceptProb (F.idealB SB n x y) (D.distinguisherL n)| :=
+        (abs_sub_le _ _ _).trans (add_le_add_right (abs_sub_le _ _ _) _)
+    _ ≤ _ := add_le_add (add_le_add s1 s2) s3
+
+end HybridProtocol
+
+end TCSlib.Cryptography.SecureComputation
diff --git a/TCSlib/Cryptography/SecureComputation/ComposeSecurity/Sim.lean b/TCSlib/Cryptography/SecureComputation/ComposeSecurity/Sim.lean
new file mode 100644
index 000000000..38de80b4f
--- /dev/null
+++ b/TCSlib/Cryptography/SecureComputation/ComposeSecurity/Sim.lean
@@ -0,0 +1,257 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Assembly
+import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Reductions
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The post-processing `Φ` and the simulators of the composed protocol
+
+Steps 1 and 4 of the proof of the composition theorem [Gol04, §7.3.1, proof of Theorem 7.3.3]. A
+party's simulator for `H.compose ρ` runs the hybrid simulator `S^H` and post-processes its output
+`hv`, read as a view of `main` with private input `⟨x, a⟩`, `main`-tape `mt` and messages `me`:
+for each call `j < L(n)` it recomputes the call input `fcall ⟨1^n, ⟨x, ⟨mt, 1^j⟩⟩⟩`, runs `ρ`'s
+simulator `S^ρ` on it and on the `j`-th block of `a`, with the `j`-th block of fresh coins, and
+assembles the view of `H.compose ρ` (`ComposeSim.asmView`). The same post-processing applied to
+the hybrid real sample gives the last hybrid of the proof, and applied before a distinguisher it
+gives the reduction to the hybrid model's security (`exists_dPhi`).
+
+## Main definitions
+
+* `ComposeSim.simV`: one simulated run, `ComposeSim.vlW`: their encoded list.
+* `ComposeSim.phiV`: the post-processing of a view; `ComposeSim.phiD`: of a sample `⟨view, out⟩`.
+
+## Main results
+
+* `ComposeSim.phiV_view`: `phiV` on an encoded view of `main` with input `1^n` is the assembled
+  view of the simulated runs.
+* `ComposeSim.polyTimeComputable_phiV`, `polyTimeComputable_phiD`.
+* `ComposeSim.exists_simulator`, `ComposeSim.exists_dPhi`: the simulator and the reduction as
+  non-uniform PPT machines.
+
+## References
+
+* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
+  University Press, 2004, §7.3.1 (the proof of Theorem 7.3.3).
+-/
+
+namespace TCSlib.Cryptography.SecureComputation.ComposeSim
+
+open Complexity Turing Complexity.StateLoop TCSlib.Cryptography.EncodingMachines ComposeMachines
+
+variable (Sρ : NUPPT) (fcall : List Bool → List Bool) (calls rounds cρ out : PolyExpr)
+  (vF b : Bool) (lead : ℕ)
+
+/-- **One simulated run**: on `v = ⟨1^j, ⟨⟨u, α⟩, ⟨hv, s⟩⟩⟩` (`u = 1^n`, `α` the advice of
+`S^ρ`, `hv = ⟨⟨x₁, ⟨xin, a⟩⟩, ⟨mt, me⟩⟩` a view, `s` the fresh coins), `S^ρ`'s output on the
+call input `fcall ⟨u, ⟨xin, ⟨mt, 1^j⟩⟩⟩` and the answer block `coinBlock out(n) j a`, with
+advice `α` and coins `coinBlock Sρ.coins(n) j s`. -/
+def simV (v : List Bool) : List Bool :=
+  Sρ.output (NUPPT.layout (pairFstD (pairFstD (pairSndD v)))
+    (pairEncode
+      (fcall (pairEncode (pairFstD (pairFstD (pairSndD v)))
+        (pairEncode (pairFstD (pairSndD (pairFstD (pairFstD (pairSndD (pairSndD v))))))
+          (pairEncode (pairFstD (pairSndD (pairFstD (pairSndD (pairSndD v))))) (pairFstD v)))))
+      (coinBlock (out.eval (pairFstD (pairFstD (pairSndD v))).length) (pairFstD v).length
+        (pairSndD (pairSndD (pairFstD (pairFstD (pairSndD (pairSndD v))))))))
+    (pairSndD (pairFstD (pairSndD v)))
+    (coinBlock (Sρ.coins.eval (pairFstD (pairFstD (pairSndD v))).length) (pairFstD v).length
+      (pairSndD (pairSndD (pairSndD v)))))
+
+/-- `simV` on its word: with `w = ⟨⟨1^n, α⟩, ⟨⟨⟨x₁, ⟨xin, a⟩⟩, ⟨mt, me⟩⟩, s⟩⟩`,
+`simV ⟨1^j, w⟩ = Sρ.output (layout 1^n ⟨fcall ⟨1^n, ⟨xin, ⟨mt, 1^j⟩⟩⟩, coinBlock out(n) j a⟩ α
+(coinBlock Sρ.coins(n) j s))`. -/
+theorem simV_pairEncode (n j : ℕ) (α x₁ xin a mt me s : List Bool) :
+    simV Sρ fcall out (pairEncode (List.replicate j true)
+        (pairEncode (pairEncode (List.replicate n true) α)
+          (pairEncode (pairEncode (pairEncode x₁ (pairEncode xin a)) (pairEncode mt me)) s))) =
+      Sρ.output (NUPPT.layout (List.replicate n true)
+        (pairEncode (fcall (pairEncode (List.replicate n true)
+            (pairEncode xin (pairEncode mt (List.replicate j true)))))
+          (coinBlock (out.eval n) j a)) α (coinBlock (Sρ.coins.eval n) j s)) := by
+  simp only [simV, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
+
+/-- **The encoded list of the simulated runs** on `w = ⟨⟨1^n, α⟩, ⟨hv, s⟩⟩`:
+`vlW w = (range calls(n)).flatMap fun j => ⟨simV ⟨1^j, w⟩, []⟩`. -/
+def vlW (w : List Bool) : List Bool :=
+  (List.range (calls.eval (pairFstD (pairFstD w)).length)).flatMap fun j =>
+    pairEncode (simV Sρ fcall out (pairEncode (List.replicate j true) w)) []
+
+/-- The defining equation of `vlW` (see `vlW`).
+`vlW Sρ fcall calls out w = (List.range (calls.eval (pairFstD (pairFstD w)).length)).flatMap fun j
+=> pairEncode (simV Sρ fcall out (pairEncode (List.replicate j true) w)) []`. -/
+theorem vlW_eq (w : List Bool) :
+    vlW Sρ fcall calls out w =
+      (List.range (calls.eval (pairFstD (pairFstD w)).length)).flatMap fun j =>
+        pairEncode (simV Sρ fcall out (pairEncode (List.replicate j true) w)) [] := rfl
+
+/-- **The post-processing of a view** (`Φ` on views): on `w = ⟨⟨1^n, α⟩, ⟨hv, s⟩⟩` with
+`hv = ⟨⟨x₁, ⟨xin, a⟩⟩, ⟨mt, me⟩⟩`, the assembled view (`asmW`) of `x₁`, `xin`, `mt`, `me` and the
+simulated runs (`vlW`). -/
+def phiV (w : List Bool) : List Bool :=
+  asmW calls rounds cρ vF b lead
+    (pairEncode (pairEncode (pairEncode (pairFstD (pairFstD (pairFstD (pairSndD w))))
+        (pairFstD (pairSndD (pairFstD (pairFstD (pairSndD w))))))
+      (pairEncode (pairFstD (pairSndD (pairFstD (pairSndD w))))
+        (pairSndD (pairSndD (pairFstD (pairSndD w))))))
+      (vlW Sρ fcall calls out w))
+
+/-- The defining equation of `phiV` (see `phiV`).
+`phiV Sρ fcall calls rounds cρ out vF b lead w = asmW calls rounds cρ vF b lead (pairEncode
+(pairEncode (pairEncode (pairFstD (pairFstD (pairFstD (pairSndD w)))) (pairFstD (pairSndD (pairFstD
+(pairFstD (pairSndD w)))))) (pairEncode …`. -/
+theorem phiV_eq (w : List Bool) :
+    phiV Sρ fcall calls rounds cρ out vF b lead w =
+      asmW calls rounds cρ vF b lead
+        (pairEncode (pairEncode (pairEncode (pairFstD (pairFstD (pairFstD (pairSndD w))))
+            (pairFstD (pairSndD (pairFstD (pairFstD (pairSndD w))))))
+          (pairEncode (pairFstD (pairSndD (pairFstD (pairSndD w))))
+            (pairSndD (pairSndD (pairFstD (pairSndD w))))))
+          (vlW Sρ fcall calls out w)) := rfl
+
+/-- **`phiV` on a view of `main` with common input `1^n`**: on
+`⟨⟨1^n, α⟩, ⟨⟨⟨1^n, ⟨xin, a⟩⟩, ⟨mt, me⟩⟩, s⟩⟩` it is
+`asmView … 1^n xin mt me V` with `V j = S^ρ`'s output on the call input and the answer block
+`j`, with the coin block `j` (`asmW_pairEncode`, `asmView_congr`, `msgAt_encodeMsgs`). -/
+theorem phiV_view (n : ℕ) (α xin a mt me s : List Bool) :
+    phiV Sρ fcall calls rounds cρ out vF b lead
+        (pairEncode (pairEncode (List.replicate n true) α)
+          (pairEncode (pairEncode (pairEncode (List.replicate n true) (pairEncode xin a))
+            (pairEncode mt me)) s)) =
+      asmView calls rounds cρ vF b lead (List.replicate n true) xin mt me fun j =>
+        Sρ.output (NUPPT.layout (List.replicate n true)
+          (pairEncode (fcall (pairEncode (List.replicate n true)
+              (pairEncode xin (pairEncode mt (List.replicate j true)))))
+            (coinBlock (out.eval n) j a)) α (coinBlock (Sρ.coins.eval n) j s)) := by
+  rw [phiV_eq, vlW_eq]
+  simp only [pairFstD_pairEncode, pairSndD_pairEncode]
+  rw [asmW_pairEncode]
+  refine asmView_congr _ _ _ _ _ _ _ _ _ _ fun j hj => ?_
+  rw [List.length_replicate] at hj ⊢
+  rw [← List.flatMap_map (fun j => simV Sρ fcall out (pairEncode (List.replicate j true)
+      (pairEncode (pairEncode (List.replicate n true) α)
+        (pairEncode (pairEncode (pairEncode (List.replicate n true) (pairEncode xin a))
+          (pairEncode mt me)) s)))) (fun m => pairEncode m []),
+    ← encodeMsgs_eq_flatMap, msgAt_encodeMsgs, Compose.getD_map_range hj, simV_pairEncode]
+
+/-- **The post-processing of a sample** (`Φ` on samples `⟨view, out⟩`): on
+`w = ⟨⟨u, α⟩, ⟨⟨hv, o⟩, s⟩⟩`, `phiD w = ⟨phiV ⟨⟨u, α⟩, ⟨hv, s⟩⟩, o⟩`. -/
+def phiD (w : List Bool) : List Bool :=
+  pairEncode (phiV Sρ fcall calls rounds cρ out vF b lead
+      (pairEncode (pairFstD w) (pairEncode (pairFstD (pairFstD (pairSndD w)))
+        (pairSndD (pairSndD w)))))
+    (pairSndD (pairFstD (pairSndD w)))
+
+/-- `phiD` on its word: `phiD ⟨⟨u, α⟩, ⟨⟨hv, o⟩, s⟩⟩ = ⟨phiV ⟨⟨u, α⟩, ⟨hv, s⟩⟩, o⟩`. -/
+theorem phiD_pairEncode (u α hv o s : List Bool) :
+    phiD Sρ fcall calls rounds cρ out vF b lead
+        (pairEncode (pairEncode u α) (pairEncode (pairEncode hv o) s)) =
+      pairEncode (phiV Sρ fcall calls rounds cρ out vF b lead
+        (pairEncode (pairEncode u α) (pairEncode hv s))) o := by
+  simp only [phiD, pairFstD_pairEncode, pairSndD_pairEncode]
+
+variable {fcall}
+
+/-- **`simV` is polynomial-time** when `fcall` is: `PolyTimeComputable (simV Sρ fcall out)`.
+
+**Proof sketch.** The components `1^n`, `α`, `xin`, `a`, `mt`, `s` of the word are projections;
+the call input is `fcall` on a pairing of them; the answer block and the coin block are
+`coinSlice`s (`GI.coinSlice_poly`); and `S^ρ`'s output on the assembled layout is polynomial-time
+(`NUPPT.polyTimeComputable_output`, `NUPPT.polyTimeComputable_layout`). -/
+theorem polyTimeComputable_simV (hcall : PolyTimeComputable fcall) :
+    PolyTimeComputable (simV Sρ fcall out) := by
+  have hw := polyTimeComputable_pairSndD
+  have hu : PolyTimeComputable fun v => pairFstD (pairFstD (pairSndD v)) :=
+    polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairFstD.comp' hw)
+  have hhv : PolyTimeComputable fun v => pairFstD (pairSndD (pairSndD v)) :=
+    polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairSndD.comp' hw)
+  have hz : PolyTimeComputable fun v => pairSndD (pairFstD (pairFstD (pairSndD (pairSndD v)))) :=
+    polyTimeComputable_pairSndD.comp' (polyTimeComputable_pairFstD.comp'
+      (polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairSndD.comp' hw)))
+  have hxin := polyTimeComputable_pairFstD.comp' hz
+  have ha := polyTimeComputable_pairSndD.comp' hz
+  have hmt : PolyTimeComputable fun v => pairFstD (pairSndD (pairFstD (pairSndD (pairSndD v)))) :=
+    polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairSndD.comp' hhv)
+  have hs : PolyTimeComputable fun v => pairSndD (pairSndD (pairSndD v)) :=
+    polyTimeComputable_pairSndD.comp' (polyTimeComputable_pairSndD.comp' hw)
+  have hα : PolyTimeComputable fun v => pairSndD (pairFstD (pairSndD v)) :=
+    polyTimeComputable_pairSndD.comp' (polyTimeComputable_pairFstD.comp' hw)
+  have hin := hcall.comp' (hu.pairEncode (hxin.pairEncode (hmt.pairEncode
+    polyTimeComputable_pairFstD)))
+  exact (Sρ.polyTimeComputable_output.comp' (NUPPT.polyTimeComputable_layout hu
+    (hin.pairEncode (GI.coinSlice_poly out hu polyTimeComputable_pairFstD ha)) hα
+    (GI.coinSlice_poly Sρ.coins hu polyTimeComputable_pairFstD hs))).congr fun v => rfl
+
+/-- **`vlW` is polynomial-time** (`ComposeMachines.polyTimeComputable_flatMap_range` of
+`polyTimeComputable_simV` over the unary count `calls(n)`).
+`PolyTimeComputable (vlW Sρ fcall calls out)`. -/
+theorem polyTimeComputable_vlW (hcall : PolyTimeComputable fcall) :
+    PolyTimeComputable (vlW Sρ fcall calls out) := by
+  have hchunk : PolyTimeComputable fun v =>
+      pairEncode (simV Sρ fcall out (pairEncode (List.replicate (pairFstD v).length true)
+        (pairSndD v))) [] :=
+    ((polyTimeComputable_simV Sρ out hcall).comp' ((unaryLength_poly
+      polyTimeComputable_pairFstD).pairEncode polyTimeComputable_pairSndD)).pairEncode
+      (polyTimeComputable_const [])
+  exact (polyTimeComputable_flatMap_range (E := fun w j =>
+      pairEncode (simV Sρ fcall out (pairEncode (List.replicate j true) w)) []) hchunk
+    (unaryPolyOf_poly calls (unaryLength_poly (polyTimeComputable_pairFstD.comp'
+      polyTimeComputable_pairFstD)))).congr fun w => (vlW_eq Sρ fcall calls out w).symm
+
+/-- **`phiV` is polynomial-time** (`polyTimeComputable_asmW` after projections and `vlW`).
+`PolyTimeComputable (phiV Sρ fcall calls rounds cρ out vF b lead)`. -/
+theorem polyTimeComputable_phiV (hcall : PolyTimeComputable fcall) :
+    PolyTimeComputable (phiV Sρ fcall calls rounds cρ out vF b lead) := by
+  have hhv : PolyTimeComputable fun w => pairFstD (pairSndD w) :=
+    polyTimeComputable_pairFstD.comp' polyTimeComputable_pairSndD
+  have hv1 := polyTimeComputable_pairFstD.comp' hhv
+  have hv2 := polyTimeComputable_pairSndD.comp' hhv
+  exact ((polyTimeComputable_asmW calls rounds cρ vF b lead).comp'
+    ((((polyTimeComputable_pairFstD.comp' hv1).pairEncode (polyTimeComputable_pairFstD.comp'
+      (polyTimeComputable_pairSndD.comp' hv1))).pairEncode
+      ((polyTimeComputable_pairFstD.comp' hv2).pairEncode
+        (polyTimeComputable_pairSndD.comp' hv2))).pairEncode
+      (polyTimeComputable_vlW Sρ calls out hcall))).congr fun w => rfl
+
+/-- **`phiD` is polynomial-time** (`polyTimeComputable_phiV` after re-pairing).
+`PolyTimeComputable (phiD Sρ fcall calls rounds cρ out vF b lead)`. -/
+theorem polyTimeComputable_phiD (hcall : PolyTimeComputable fcall) :
+    PolyTimeComputable (phiD Sρ fcall calls rounds cρ out vF b lead) := by
+  have hsmp : PolyTimeComputable fun w => pairFstD (pairSndD w) :=
+    polyTimeComputable_pairFstD.comp' polyTimeComputable_pairSndD
+  exact (((polyTimeComputable_phiV Sρ calls rounds cρ out vF b lead hcall).comp'
+    (polyTimeComputable_pairFstD.pairEncode ((polyTimeComputable_pairFstD.comp' hsmp).pairEncode
+      (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD)))).pairEncode
+    (polyTimeComputable_pairSndD.comp' hsmp)).congr fun w => rfl
+
+/-- **The simulator of the composed protocol** (step 1): for a hybrid simulator `SH`, there is a
+non-uniform PPT `S` with coins `SH.coins + calls · Sρ.coins` such that
+`S(1^n, y; r) = phiV ⟨⟨1^n, Sρ.advice n⟩, ⟨SH(1^n, y; r_{<SH.coins(n)}), r_{≥SH.coins(n)}⟩⟩`
+(`exists_post`). -/
+theorem exists_simulator (SH : NUPPT) (hcall : PolyTimeComputable fcall) :
+    ∃ S : NUPPT, S.coins = .add SH.coins (.mul calls Sρ.coins) ∧ ∀ n y r, S.runAtL n y r =
+      phiV Sρ fcall calls rounds cρ out vF b lead
+        (pairEncode (pairEncode (List.replicate n true) (Sρ.advice n))
+          (pairEncode (SH.runAtL n y (r.take (SH.coinLen n))) (r.drop (SH.coinLen n)))) :=
+  exists_post SH (polyTimeComputable_phiV Sρ calls rounds cρ out vF b lead hcall) Sρ.advice Sρ.adv
+    Sρ.advice_length (.mul calls Sρ.coins)
+
+/-- **The reduction to the hybrid model** (step 4): for a distinguisher `D`, there is a non-uniform
+PPT `DΦ` with coins `calls · Sρ.coins + D.coins` such that
+`DΦ(1^n, w; r) = D(1^n, phiD ⟨⟨1^n, Sρ.advice n⟩, ⟨w, r_{<p(n)}⟩⟩; r_{≥p(n)})`,
+`p = calls · Sρ.coins` (`exists_pre`). -/
+theorem exists_dPhi (D : NUPPT) (hcall : PolyTimeComputable fcall) :
+    ∃ DΦ : NUPPT, DΦ.coins = .add (.mul calls Sρ.coins) D.coins ∧ ∀ n y r, DΦ.runAtL n y r =
+      D.runAtL n (phiD Sρ fcall calls rounds cρ out vF b lead
+        (pairEncode (pairEncode (List.replicate n true) (Sρ.advice n))
+          (pairEncode y (r.take ((PolyExpr.mul calls Sρ.coins).eval n)))))
+        (r.drop ((PolyExpr.mul calls Sρ.coins).eval n)) :=
+  exists_pre D (polyTimeComputable_phiD Sρ calls rounds cρ out vF b lead hcall) Sρ.advice Sρ.adv
+    Sρ.advice_length (.mul calls Sρ.coins)
+
+end TCSlib.Cryptography.SecureComputation.ComposeSim
diff --git a/TCSlib/Cryptography/SecureComputation/ComposeSecurity/Template.lean b/TCSlib/Cryptography/SecureComputation/ComposeSecurity/Template.lean
new file mode 100644
index 000000000..0cb67b913
--- /dev/null
+++ b/TCSlib/Cryptography/SecureComputation/ComposeSecurity/Template.lean
@@ -0,0 +1,191 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Accept
+import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Reductions
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The reduction of one hybrid step to the sub-protocol
+
+Step 3 of the proof of the composition theorem [Gol04, §7.3.1, proof of Theorem 7.3.3]. A
+distinguisher between neighbouring hybrids, at fixed inputs, run index and other coordinates,
+becomes a distinguisher for one sample of `ρ`: the reduction holds as advice a **template**
+(`tmplW`): the header `⟨⟨x₁, xin⟩, ⟨mt, me⟩⟩` of the assembled view, the encoded words of the
+runs before and after the run under attack, and the other party's output. On a `ρ`-sample `w`
+it inserts the view `pairFstD w` between them, assembles the view (`asmW`) and pairs it with the
+output (`hybW`). The template is chosen at each `n` for the worst-case instance, so one
+non-uniform machine serves every `n` (`exists_gap_le`).
+
+## Main definitions
+
+* `ComposeSim.tmplW`: the template; `ComposeSim.hybW`: the reduction's pre-processing.
+
+## Main results
+
+* `ComposeSim.hybW_tmplW`: the pre-processing on a template.
+* `ComposeSim.polyTimeComputable_hybW`.
+* `ComposeSim.exists_gap_le`: the worst-case gap over the instances of each `n` is at most the
+  sub-protocol's negligible bound.
+
+## References
+
+* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
+  University Press, 2004, §7.3.1 (the proof of Theorem 7.3.3).
+-/
+
+namespace TCSlib.Cryptography.SecureComputation.ComposeSim
+
+open Finset Complexity Turing TCSlib.Cryptography ComposeProb ComposeMachines
+
+/-- **The template of a hybrid step**: `⟨⟨hdr, encodeMsgs pre⟩, ⟨encodeMsgs suf, out⟩⟩` for the
+header `hdr`, the words `pre` of the runs before the attacked one, the words `suf` of those
+after it and the output `out`.
+`tmplW hdr pre suf out = pairEncode (pairEncode hdr (Strategy.encodeMsgs pre)) (pairEncode
+(Strategy.encodeMsgs suf) out)`. -/
+def tmplW (hdr : List Bool) (pre suf : List (List Bool)) (out : List Bool) : List Bool :=
+  pairEncode (pairEncode hdr (Strategy.encodeMsgs pre))
+    (pairEncode (Strategy.encodeMsgs suf) out)
+
+/-- The defining equation of `tmplW` (see `tmplW`).
+`tmplW hdr pre suf out = pairEncode (pairEncode hdr (Strategy.encodeMsgs pre)) (pairEncode
+(Strategy.encodeMsgs suf) out)`. -/
+theorem tmplW_eq (hdr : List Bool) (pre suf : List (List Bool)) (out : List Bool) :
+    tmplW hdr pre suf out =
+      pairEncode (pairEncode hdr (Strategy.encodeMsgs pre))
+        (pairEncode (Strategy.encodeMsgs suf) out) := rfl
+
+/-- **The pre-processing of the hybrid-step reduction**: on `z = ⟨⟨u, β⟩, ⟨w, r⟩⟩` with
+`β = ⟨⟨hdr, P⟩, ⟨Q, out⟩⟩`, the pair of `asmW ⟨hdr, P ++ ⟨pairFstD w, Q⟩⟩` and `out`. -/
+def hybW (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ) (z : List Bool) : List Bool :=
+  pairEncode (asmW calls rounds cρ vF b lead
+      (pairEncode (pairFstD (pairFstD (pairSndD (pairFstD z))))
+        (pairSndD (pairFstD (pairSndD (pairFstD z))) ++
+          pairEncode (pairFstD (pairFstD (pairSndD z))) (pairFstD (pairSndD (pairSndD
+            (pairFstD z)))))))
+    (pairSndD (pairSndD (pairSndD (pairFstD z))))
+
+/-- The defining equation of `hybW` (see `hybW`).
+`hybW calls rounds cρ vF b lead z = pairEncode (asmW calls rounds cρ vF b lead (pairEncode (pairFstD
+(pairFstD (pairSndD (pairFstD z)))) (pairSndD (pairFstD (pairSndD (pairFstD z))) ++ pairEncode
+(pairFstD (pairFstD (pairSndD z))) (pairFstD …`. -/
+theorem hybW_eq (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ) (z : List Bool) :
+    hybW calls rounds cρ vF b lead z =
+      pairEncode (asmW calls rounds cρ vF b lead
+          (pairEncode (pairFstD (pairFstD (pairSndD (pairFstD z))))
+            (pairSndD (pairFstD (pairSndD (pairFstD z))) ++
+              pairEncode (pairFstD (pairFstD (pairSndD z))) (pairFstD (pairSndD (pairSndD
+                (pairFstD z)))))))
+        (pairSndD (pairSndD (pairSndD (pairFstD z)))) := rfl
+
+/-- **The pre-processing on a template**: `hybW ⟨⟨u, tmplW hdr pre suf out⟩, ⟨w, r⟩⟩ =
+⟨asmW ⟨hdr, encodeMsgs (pre ++ pairFstD w :: suf)⟩, out⟩` (`encodeMsgs_append`). -/
+theorem hybW_tmplW (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ)
+    (u hdr out w r : List Bool) (pre suf : List (List Bool)) :
+    hybW calls rounds cρ vF b lead (pairEncode (pairEncode u (tmplW hdr pre suf out))
+        (pairEncode w r)) =
+      pairEncode (asmW calls rounds cρ vF b lead
+        (pairEncode hdr (Strategy.encodeMsgs (pre ++ pairFstD w :: suf)))) out := by
+  rw [hybW_eq, tmplW_eq, encodeMsgs_append, Strategy.encodeMsgs_cons]
+  simp only [pairFstD_pairEncode, pairSndD_pairEncode]
+
+/-- **The pre-processing is polynomial-time** (`polyTimeComputable_asmW` after projections,
+`append` and `pairEncode`).
+`PolyTimeComputable (hybW calls rounds cρ vF b lead)`. -/
+theorem polyTimeComputable_hybW (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ) :
+    PolyTimeComputable (hybW calls rounds cρ vF b lead) := by
+  have hβ : PolyTimeComputable fun z => pairSndD (pairFstD z) :=
+    polyTimeComputable_pairSndD.comp' polyTimeComputable_pairFstD
+  have h1 := polyTimeComputable_pairFstD.comp' hβ
+  have h2 := polyTimeComputable_pairSndD.comp' hβ
+  have hw : PolyTimeComputable fun z => pairFstD (pairFstD (pairSndD z)) :=
+    polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairFstD.comp'
+      polyTimeComputable_pairSndD)
+  exact (((polyTimeComputable_asmW calls rounds cρ vF b lead).comp'
+    ((polyTimeComputable_pairFstD.comp' h1).pairEncode
+      ((polyTimeComputable_pairSndD.comp' h1).append
+        (hw.pairEncode (polyTimeComputable_pairFstD.comp' h2))))).pairEncode
+    (polyTimeComputable_pairSndD.comp' h2)).congr fun z => rfl
+
+/-- **The worst-case hybrid step is bounded by the sub-protocol's security.** Let `rs n x y` and
+`is n x y` be samplers of `ρ` on inputs of `G`'s lengths, indistinguishable with a negligible
+bound uniform over the inputs (`hS`). Let `Θ n` be finite sets of instances, each with inputs
+`xA θ`, `yB θ` of `ρ` and a template whose length is at most `q(n)`. Then for every non-uniform
+PPT `D` there is a negligible `ε₂` with, for all `n` and `θ : Θ n`,
+`|Pr_t[D(K θ (pairFstD (rs t)))] − Pr_s[D(K θ (pairFstD (is s)))]| ≤ ε₂(n)`, where
+`K θ v = ⟨asmW ⟨hdr θ, encodeMsgs (pre θ ++ v :: suf θ)⟩, out θ⟩` (the template filled with `v`).
+
+**Proof sketch.** At each `n` with instances, take the instance `θ*` with the largest gap
+(`Finset.exists_max_image`) and give its template as advice (length at most `q(n)`). The
+machine `D ∘ hybW` with no extra coins (`exists_pre`) accepts a sample `w` as `D` accepts
+`K θ* (pairFstD w)` (`acceptProb_pre`, `hybW_tmplW`, `acceptProb_fst`), so its advantage
+between `rs` and `is` at the inputs of `θ*` is the gap at `θ*`, at most `ε₂(n)` by `hS`, and
+every gap at `n` is at most the gap at `θ*`. -/
+theorem exists_gap_le {G : Functionality} {T Sc : ℕ → Type} [∀ n, Fintype (T n)]
+    [∀ n, Fintype (Sc n)]
+    (rs : ∀ n, (Fin (G.inA.eval n) → Bool) → (Fin (G.inB.eval n) → Bool) → T n → List Bool)
+    (is : ∀ n, (Fin (G.inA.eval n) → Bool) → (Fin (G.inB.eval n) → Bool) → Sc n → List Bool)
+    (hS : ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
+      ∀ n (x : Fin (G.inA.eval n) → Bool) (y : Fin (G.inB.eval n) → Bool),
+        distAdv (rs n x y) (is n x y) (D.distinguisherL n) ≤ ε n)
+    (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ) {Θ : ℕ → Type} [∀ n, Fintype (Θ n)]
+    (xA : ∀ n, Θ n → Fin (G.inA.eval n) → Bool) (yB : ∀ n, Θ n → Fin (G.inB.eval n) → Bool)
+    (hdr out : ∀ n, Θ n → List Bool) (pre suf : ∀ n, Θ n → List (List Bool)) (q : PolyExpr)
+    (hq : ∀ n θ, (tmplW (hdr n θ) (pre n θ) (suf n θ) (out n θ)).length ≤ q.eval n)
+    (D : NUPPT) :
+    ∃ ε₂ : ℕ → ℝ, Negligible ε₂ ∧ ∀ n (θ : Θ n),
+      |acceptProb (fun t => pairEncode (asmW calls rounds cρ vF b lead (pairEncode (hdr n θ)
+            (Strategy.encodeMsgs (pre n θ ++ pairFstD (rs n (xA n θ) (yB n θ) t) :: suf n θ))))
+            (out n θ)) (D.distinguisherL n) -
+        acceptProb (fun s => pairEncode (asmW calls rounds cρ vF b lead (pairEncode (hdr n θ)
+            (Strategy.encodeMsgs (pre n θ ++ pairFstD (is n (xA n θ) (yB n θ) s) :: suf n θ))))
+            (out n θ)) (D.distinguisherL n)| ≤ ε₂ n := by
+  classical
+  -- the gap of an instance
+  let K : ∀ n, Θ n → List Bool → List Bool := fun n θ v =>
+    pairEncode (asmW calls rounds cρ vF b lead (pairEncode (hdr n θ)
+      (Strategy.encodeMsgs (pre n θ ++ v :: suf n θ)))) (out n θ)
+  let gap : ∀ n, Θ n → ℝ := fun n θ =>
+    |acceptProb (fun t => K n θ (pairFstD (rs n (xA n θ) (yB n θ) t))) (D.distinguisherL n) -
+      acceptProb (fun s => K n θ (pairFstD (is n (xA n θ) (yB n θ) s))) (D.distinguisherL n)|
+  have hmax : ∀ n, Nonempty (Θ n) → ∃ θs : Θ n, ∀ θ, gap n θ ≤ gap n θs := fun n hn => by
+    obtain ⟨θs, -, h⟩ := exists_max_image univ (gap n) univ_nonempty
+    exact ⟨θs, fun θ => h θ (mem_univ θ)⟩
+  -- the advice: the template of the worst instance
+  let β : ℕ → List Bool := fun n => if h : Nonempty (Θ n) then
+    tmplW (hdr n (Classical.choose (hmax n h))) (pre n (Classical.choose (hmax n h)))
+      (suf n (Classical.choose (hmax n h))) (out n (Classical.choose (hmax n h))) else []
+  have hβ : ∀ n, (β n).length ≤ q.eval n := fun n => by
+    by_cases h : Nonempty (Θ n)
+    · simp only [β, dif_pos h]
+      exact hq n _
+    · simp only [β, dif_neg h, List.length_nil]
+      exact Nat.zero_le _
+  obtain ⟨Dh, hc, hDh⟩ := exists_pre D (polyTimeComputable_hybW calls rounds cρ vF b lead) β q hβ
+    (.const 0)
+  obtain ⟨ε, hε, hbound⟩ := hS Dh
+  refine ⟨ε, hε, fun n θ => ?_⟩
+  have hn : Nonempty (Θ n) := ⟨θ⟩
+  have hθs := Classical.choose_spec (hmax n hn)
+  -- `Dh` accepts a sample as `D` accepts the filled template of the worst instance
+  have key : ∀ {σ : Type} [Fintype σ] (X : σ → List Bool),
+      acceptProb X (Dh.distinguisherL n) =
+        acceptProb (fun s => K n (Classical.choose (hmax n hn)) (pairFstD (X s)))
+          (D.distinguisherL n) := by
+    intro σ _ X
+    rw [acceptProb_pre X Dh D (.const 0) n (fun w e => hybW calls rounds cρ vF b lead
+      (pairEncode (pairEncode (List.replicate n true) (β n)) (pairEncode w e))) hc (hDh n)]
+    refine Eq.trans ?_ (acceptProb_fst (τ := Fin ((PolyExpr.const 0).eval n) → Bool)
+      (fun s => K n (Classical.choose (hmax n hn)) (pairFstD (X s))) (D.distinguisherL n))
+    refine congrArg (fun f => acceptProb f (D.distinguisherL n)) (funext fun z => ?_)
+    simp only [β, dif_pos hn]
+    rw [hybW_tmplW]
+  have h := hbound n (xA n (Classical.choose (hmax n hn))) (yB n (Classical.choose (hmax n hn)))
+  rw [distAdv_def, key, key] at h
+  exact (hθs θ).trans h
+
+end TCSlib.Cryptography.SecureComputation.ComposeSim

## ===== TCSlib/Cryptography/SecureComputation/ComposeSecurity.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ComposePhases
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Machines
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Efficiency
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Probability
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Reductions
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Assembly
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Runs
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Bounds
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Sim
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Chain
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Accept
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Correct
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Template
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Lengths
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.SideA
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.SideB

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The composition theorem for the semi-honest model

[Gol04, §7.3.1, Theorem 7.3.3]: if a protocol `H` privately computes `F` in the `G`-hybrid model
and a protocol `ρ` privately computes `G`, then `H` with every ideal call replaced by a run of `ρ`
privately computes `F`. Here "privately computes" is honest-but-curious security
[PS10, Definition 155.1] (`HBCSecure`, and `HybridProtocol.HBCSecure` in the hybrid model), and
the composed protocol is `H.compose ρ` (`Compose.lean`). The section and theorem numbers of
[Gol04] are cited from memory and should be verified at audit.

[PS10]'s proof of Theorem 163.7 (Yao's protocol) uses this theorem without stating it. By the
ruling of 2026-11-05, Yao's protocol is proved secure with an ideal OT, and the real protocol
follows from this theorem with Protocol 160.4 for `ρ`.

**Polynomial time** (ruling of 2026-11-05: security includes polynomial-time parties). The
messages of `H.compose ρ` are bounded by the sum of `main`'s and `ρ`'s bounds
(`compose_msg_bound`, proved). This uses that `H.PolyTime` bounds `main`'s messages for **any**
answers of the right lengths, since in `H.compose ρ` `main` runs on `ρ`'s outputs. The composed
strategies are PPT (`composeP_efficient`, `composeV_efficient`): each is a polynomial-time
function of the machine layout built from `main`'s and `ρ`'s machines and the call-input
functions (`ComposeSecurity/Efficiency.lean`).

**Deviations from [Gol04, Theorem 7.3.3].**
- **Calls first only**, and the layout with fillers (`Compose.lean`).
- **`main` has at least one move** (`hM`), forced by D8's output convention: if
  `main.rounds(n) = 0`, the last move of `H.compose ρ` is a run move or the leading filler, and
  its sender's output is that message instead of its output in `main`. The theorem then fails.
  For example, take `F = G` the swap functionality `(x, y) ↦ (y, x)` on bits, one call on the
  parties' inputs, `main` with no moves whose parties output their answers, and `ρ` the
  three-message protocol in which Alice sends `x`, Bob `y`, and Alice `y` (her output, as last
  mover). In `H.compose ρ` (six moves, `main`'s prover first) Bob's last message is a filler, so
  he outputs `[]`, not `x`. As `PolyExpr.eval` is monotone, `0 < main.rounds(n)` for a single
  `n` would suffice up to finitely many `n`; the uniform form is stated.
- **Uniform bounds**, as in `HBCSecure`: one negligible bound for all inputs of each length.

## Main definitions

* None: the composed protocol is defined in `Compose.lean` and its phases in
  `ComposePhases.lean`.

## Contents

* `ComposeSecurity/Machines.lean`: polynomial-time machines on encoded histories (loops over a
  data-dependent range, the interleaved-slot map, strategies as functions of the layout).
* `ComposeSecurity/Efficiency.lean`: the composed parties as polynomial-time functions of the
  machine layout.
* `ComposeSecurity/Probability.lean`: distinguishing-advantage tools (the statistical switch,
  fixing coordinates, a negligible function times a polynomial).
* `ComposeSecurity/Reductions.lean`: machines with advice-dependent pre- and post-processing.
* `ComposeSecurity/Assembly.lean`: a view of the composed protocol assembled from run views.
* `ComposeSecurity/Runs.lean`: the coins of the composed protocol run by run, and the real
  samples when every run gives the ideal answers.
* `ComposeSecurity/Bounds.lean`: lengths of encodings, transcripts and machine outputs.
* `ComposeSecurity/Sim.lean`: the post-processing `Φ`, the simulators and the reduction to the
  hybrid model.
* `ComposeSecurity/Chain.lean`: the hybrid argument over the runs.
* `ComposeSecurity/Accept.lean`: acceptance of machines with split coins; test machines.
* `ComposeSecurity/Correct.lean`: a secure protocol is correct; the union bound over the runs.
* `ComposeSecurity/Template.lean`: the reduction of one hybrid step to the sub-protocol.
* `ComposeSecurity/Lengths.lean`: polynomial bounds on the words of the templates.
* `ComposeSecurity/SideA.lean`, `ComposeSecurity/SideB.lean`: Alice's and Bob's sides of the
  composition theorem.

## Main results

* `HybridProtocol.exists_runExec_eq_transcript`, `exists_mainExec_eq_transcript`: the runs and
  the main phase are transcripts of `ρ` and `main` on inputs and coins of the right types.
* `HybridProtocol.compose_msg_bound`: the messages of `H.compose ρ` are polynomially bounded.
* `HybridProtocol.composeP_efficient`, `composeV_efficient`: the composed strategies are PPT;
  `polyTime_compose` (proved from the three).
* `HybridProtocol.hbcSecure_compose` ([Gol04, Theorem 7.3.3]): from Alice's and Bob's sides
  (`exists_simA`, `exists_simB`).

## References

* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
  University Press, 2004, §7.3.1 (privacy reductions and a composition theorem), Theorem 7.3.3.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2, Definition 155.1 and Theorem 163.7 (book pp. 155–164).
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing TCSlib.Cryptography

open Compose

namespace HybridProtocol

/-! ### Polynomial time -/

section Efficiency

variable {G : Functionality} (H : HybridProtocol G) (ρ : Protocol)

/-- A list of length `c` is the encoding of a `c`-bit string. -/
private theorem exists_ofFn_eq {c : ℕ} {l : List Bool} (h : l.length = c) :
    ∃ t : Fin c → Bool, List.ofFn t = l := by
  subst h
  exact ⟨fun i => l[i.1], List.ofFn_getElem l⟩

/-- Alice's honest answers have `calls(|x|) · G.outA(|x|)` bits. -/
theorem length_answersRealA (x zA zB rA rB : List Bool) :
    (H.answersRealA ρ x zA zB rA rB).length = H.calls.eval x.length * G.outA.eval x.length := by
  rw [answersRealA_eq, List.length_flatten, List.map_ofFn]
  simp only [Function.comp_def, List.length_ofFn, List.ofFn_const, List.sum_replicate,
    smul_eq_mul]

/-- Bob's honest answers have `calls(|x|) · G.outB(|x|)` bits. -/
theorem length_answersRealB (x zA zB rA rB : List Bool) :
    (H.answersRealB ρ x zA zB rA rB).length = H.calls.eval x.length * G.outB.eval x.length := by
  rw [answersRealB_eq, List.length_flatten, List.map_ofFn]
  simp only [Function.comp_def, List.length_ofFn, List.ofFn_const, List.sum_replicate,
    smul_eq_mul]

/-- **The main phase is a hybrid-format execution of `main`**: on common input `1^n`, inputs of
`F`'s lengths and tapes at least as long as the `main`-tapes, the main phase of an honest
execution of `H.compose ρ` is the transcript of `main` on `⟨x, aA⟩`, `⟨y, aB⟩` for answers `aA`,
`aB` of the hybrid lengths and some coins of `main` (those answers are the honest ones, the
coins the `main`-tapes).

**Proof sketch.** The honest answers have `calls(n) · G.outA(n)` and `calls(n) · G.outB(n)` bits
(`length_answersRealA`, `length_answersRealB`), and the `main`-tapes the lengths of `main`'s
coins, so each is `List.ofFn` of a string of the right type; `mainExec` is then `main`'s
transcript on them by definition. -/
theorem exists_mainExec_eq_transcript {F : Functionality} (n : ℕ) (x : Fin (F.inA.eval n) → Bool)
    (y : Fin (F.inB.eval n) → Bool) {rA rB : List Bool}
    (hrA : H.main.P.coins.eval (List.replicate n true).length ≤ rA.length)
    (hrB : H.main.V.coins.eval (List.replicate n true).length ≤ rB.length) :
    ∃ (aA : Fin (H.calls.eval n * G.outA.eval n) → Bool)
      (aB : Fin (H.calls.eval n * G.outB.eval n) → Bool) (r : H.Coins n),
      H.mainExec ρ (List.replicate n true) (List.ofFn x) (List.ofFn y) rA rB
          (H.main.rounds.eval (List.replicate n true).length) =
        H.main.transcript (List.replicate n true) (pairEncode (List.ofFn x) (List.ofFn aA))
          (pairEncode (List.ofFn y) (List.ofFn aB)) r := by
  obtain ⟨aA, haA⟩ := exists_ofFn_eq (c := H.calls.eval n * G.outA.eval n)
    (l := H.answersRealA ρ (List.replicate n true) (List.ofFn x) (List.ofFn y) rA rB)
    (by rw [length_answersRealA, List.length_replicate])
  obtain ⟨aB, haB⟩ := exists_ofFn_eq (c := H.calls.eval n * G.outB.eval n)
    (l := H.answersRealB ρ (List.replicate n true) (List.ofFn x) (List.ofFn y) rA rB)
    (by rw [length_answersRealB, List.length_replicate])
  obtain ⟨tA, htA⟩ := exists_ofFn_eq (c := H.main.P.coinLen (List.replicate n true).length)
    (l := rA.take (H.main.P.coins.eval (List.replicate n true).length))
    (by rw [Strategy.coinLen_eq, List.length_take]; exact Nat.min_eq_left hrA)
  obtain ⟨tB, htB⟩ := exists_ofFn_eq (c := H.main.V.coinLen (List.replicate n true).length)
    (l := rB.take (H.main.V.coins.eval (List.replicate n true).length))
    (by rw [Strategy.coinLen_eq, List.length_take]; exact Nat.min_eq_left hrB)
  refine ⟨aA, aB, (tA, tB), ?_⟩
  rw [mainExec_eq, ← haA, ← haB, ← htA, ← htB]
  rw [Protocol.transcript_eq_transcriptWith, Protocol.transcriptWith_eq]

/-- **Run `j` is an execution of `ρ` on inputs of `G`'s lengths**: on common input `1^n`, for
`j < calls(n)` and composed tapes of the right lengths, the honest run `j` is the transcript of
`ρ` on some inputs of `G`'s lengths and some coins of `ρ` (the call inputs and the run tapes).

**Proof sketch.** For `j < calls(n)` the run inputs are the call inputs (`runInputA_of_lt`,
`runInputB_of_lt`), of `G`'s input lengths, and the run tapes have the lengths of `ρ`'s coins
(`length_runTape`), so each is `List.ofFn` of a string of the right type; `runExec` is then
`ρ`'s transcript on them by definition. -/
theorem exists_runExec_eq_transcript (n : ℕ) (zA zB : List Bool) {rA rB : List Bool} {j : ℕ}
    (hj : j < H.calls.eval (List.replicate n true).length)
    (hrA : rA.length = H.main.P.coins.eval (List.replicate n true).length +
      H.calls.eval (List.replicate n true).length * ρ.P.coins.eval (List.replicate n true).length)
    (hrB : rB.length = H.main.V.coins.eval (List.replicate n true).length +
      H.calls.eval (List.replicate n true).length *
        ρ.V.coins.eval (List.replicate n true).length) :
    ∃ (xA : Fin (G.inA.eval n) → Bool) (yB : Fin (G.inB.eval n) → Bool)
      (r : ρ.ExecCoins ρ.P (List.replicate n true)),
      H.runExec ρ (List.replicate n true) zA zB rA rB j
          (ρ.rounds.eval (List.replicate n true).length) =
        ρ.transcript (List.replicate n true) (List.ofFn xA) (List.ofFn yB) r := by
  obtain ⟨xA, hxA⟩ := exists_ofFn_eq (c := G.inA.eval n)
    (l := H.runInputA (List.replicate n true) zA rA j)
    (by rw [H.runInputA_of_lt _ _ _ hj, List.length_ofFn, List.length_replicate])
  obtain ⟨yB, hyB⟩ := exists_ofFn_eq (c := G.inB.eval n)
    (l := H.runInputB (List.replicate n true) zB rB j)
    (by rw [H.runInputB_of_lt _ _ _ hj, List.length_ofFn, List.length_replicate])
  obtain ⟨tA, htA⟩ := exists_ofFn_eq (c := ρ.P.coinLen (List.replicate n true).length)
    (l := runTape (H.main.P.coins.eval (List.replicate n true).length)
      (ρ.P.coins.eval (List.replicate n true).length) j rA)
    ((length_runTape hrA hj).trans
      (Strategy.coinLen_eq ρ.P (List.replicate n true).length).symm)
  obtain ⟨tB, htB⟩ := exists_ofFn_eq (c := ρ.V.coinLen (List.replicate n true).length)
    (l := runTape (H.main.V.coins.eval (List.replicate n true).length)
      (ρ.V.coins.eval (List.replicate n true).length) j rB)
    ((length_runTape hrB hj).trans
      (Strategy.coinLen_eq ρ.V (List.replicate n true).length).symm)
  refine ⟨xA, yB, (tA, tB), ?_⟩
  rw [runExec_eq, ← hxA, ← hyB, ← htA, ← htB]
  rw [Protocol.transcript_eq_transcriptWith, Protocol.transcriptWith_eq]

/-- `ρ`'s move `p < R` of the honest run `j` is a message of that run's transcript. -/
theorem runMsg_mem (x zA zB rA rB : List Bool) (j : ℕ) {p : ℕ}
    (hp : p < ρ.rounds.eval x.length) :
    H.runMsg ρ x zA zB rA rB j p ∈ (H.runExec ρ x zA zB rA rB j (ρ.rounds.eval x.length)).1 ++
      (H.runExec ρ x zA zB rA rB j (ρ.rounds.eval x.length)).2 := by
  rw [runExec_eq, exec_eq_map, runMsg_eq]
  by_cases hm : moverIsV ρ.verifierFirst p = true
  · exact List.mem_append_left _
      (List.mem_map.2 ⟨p, List.mem_filter.2 ⟨List.mem_range.2 hp, hm⟩, rfl⟩)
  · refine List.mem_append_right _
      (List.mem_map.2 ⟨p, List.mem_filter.2 ⟨List.mem_range.2 hp, ?_⟩, rfl⟩)
    simpa using hm

/-- **The messages of `H.compose ρ` are polynomially bounded** (the message half of
`Functionality.PolyTime`): every message of an honest execution on common input `1^n` and inputs
of `F`'s lengths has at most `B_main(n) + B_ρ(n)` bits, with `B_main` the bound of `H.PolyTime`
and `B_ρ` that of `G.PolyTime ρ`.

**Proof sketch.** By `compose_transcript` a message is a filler (empty), a message of an honest
run, or a message of the main phase.
1. A run message is `ρ`'s move in the honest run `j < calls(n)` (`runMsg_mem`), a transcript of
   `ρ` on inputs of `G`'s lengths (`exists_runExec_eq_transcript`): at most `B_ρ(n)` bits.
2. A main-phase message is a message of `main` on `⟨x, aA⟩`, `⟨y, aB⟩` with answers of the
   hybrid lengths (`exists_mainExec_eq_transcript`); `H.PolyTime` bounds those for **any** such
   answers: at most `B_main(n)` bits. -/
theorem compose_msg_bound {F : Functionality} (hH : H.PolyTime F) (hρ : G.PolyTime ρ) :
    ∃ B : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool)
      (r : (H.compose ρ).ExecCoins (H.compose ρ).P (List.replicate n true)),
      ∀ msg ∈ ((H.compose ρ).transcript (List.replicate n true) (List.ofFn x) (List.ofFn y) r).1 ++
          ((H.compose ρ).transcript (List.replicate n true) (List.ofFn x) (List.ofFn y) r).2,
        msg.length ≤ B.eval n := by
  obtain ⟨-, -, -, -, B₁, hB₁⟩ := (HybridProtocol.polyTime_iff H F).mp hH
  obtain ⟨-, -, B₂, hB₂⟩ := (Functionality.polyTime_iff G ρ).mp hρ
  refine ⟨.add B₁ B₂, fun n x y r msg hmsg => ?_⟩
  rw [PolyExpr.eval_add]
  have hrA : (List.ofFn r.1).length = H.main.P.coins.eval (List.replicate n true).length +
      H.calls.eval (List.replicate n true).length *
        ρ.P.coins.eval (List.replicate n true).length :=
    (List.length_ofFn (f := r.1)).trans
      ((H.compose_P_coinLen ρ (List.replicate n true).length).trans
        (congrArg₂ (fun a b : ℕ => a + H.calls.eval (List.replicate n true).length * b)
          (Strategy.coinLen_eq H.main.P (List.replicate n true).length)
          (Strategy.coinLen_eq ρ.P (List.replicate n true).length)))
  have hrB : (List.ofFn r.2).length = H.main.V.coins.eval (List.replicate n true).length +
      H.calls.eval (List.replicate n true).length *
        ρ.V.coins.eval (List.replicate n true).length :=
    (List.length_ofFn (f := r.2)).trans
      ((H.compose_V_coinLen ρ (List.replicate n true).length).trans
        (congrArg₂ (fun a b : ℕ => a + H.calls.eval (List.replicate n true).length * b)
          (Strategy.coinLen_eq H.main.V (List.replicate n true).length)
          (Strategy.coinLen_eq ρ.V (List.replicate n true).length)))
  -- a message of an honest run
  have hrun : ∀ j p, j < H.calls.eval (List.replicate n true).length →
      p < ρ.rounds.eval (List.replicate n true).length →
      (H.runMsg ρ (List.replicate n true) (List.ofFn x) (List.ofFn y) (List.ofFn r.1)
        (List.ofFn r.2) j p).length ≤ B₁.eval n + B₂.eval n := by
    intro j p hj hp
    obtain ⟨xA, yB, r', h⟩ := H.exists_runExec_eq_transcript ρ n (List.ofFn x) (List.ofFn y) hj
      hrA hrB
    have hmem := H.runMsg_mem ρ (List.replicate n true) (List.ofFn x) (List.ofFn y)
      (List.ofFn r.1) (List.ofFn r.2) j hp
    rw [h] at hmem
    exact (hB₂ n xA yB r' _ hmem).trans (Nat.le_add_left _ _)
  -- a message of the main phase
  obtain ⟨aA, aB, r', hmain⟩ := H.exists_mainExec_eq_transcript ρ n x y
    (rA := List.ofFn r.1) (rB := List.ofFn r.2) (by omega) (by omega)
  have hmainB : ∀ msg ∈ (H.mainExec ρ (List.replicate n true) (List.ofFn x) (List.ofFn y)
      (List.ofFn r.1) (List.ofFn r.2) (H.main.rounds.eval (List.replicate n true).length)).1 ++
      (H.mainExec ρ (List.replicate n true) (List.ofFn x) (List.ofFn y)
        (List.ofFn r.1) (List.ofFn r.2) (H.main.rounds.eval (List.replicate n true).length)).2,
      msg.length ≤ B₁.eval n + B₂.eval n := by
    intro msg hmsg
    rw [hmain] at hmsg
    exact (hB₁ n x y aA aB r' msg hmsg).trans (Nat.le_add_right _ _)
  rw [compose_transcript] at hmsg
  simp only [List.mem_append, List.mem_map, List.mem_range] at hmsg
  have hR : ∀ q, q < H.calls.eval (List.replicate n true).length *
      ρ.rounds.eval (List.replicate n true).length →
      q / ρ.rounds.eval (List.replicate n true).length <
        H.calls.eval (List.replicate n true).length ∧
      q % ρ.rounds.eval (List.replicate n true).length <
        ρ.rounds.eval (List.replicate n true).length := by
    intro q hq
    have hR0 : 0 < ρ.rounds.eval (List.replicate n true).length := by
      rcases Nat.eq_zero_or_pos (ρ.rounds.eval (List.replicate n true).length) with h | h
      · rw [h, Nat.mul_zero] at hq
        omega
      · exact h
    exact ⟨(Nat.div_lt_iff_lt_mul hR0).2 hq, Nat.mod_lt _ hR0⟩
  rcases hmsg with ((⟨q, hq, rfl⟩ | hm) | ((⟨q, hq, rfl⟩ | hm) | hm))
  · rw [slotFromB_eq]
    split_ifs
    · exact hrun _ _ (hR q hq).1 (hR q hq).2
    · exact Nat.zero_le _
  · exact hmainB msg (List.mem_append_left _ hm)
  · rw [slotFromA_eq]
    split_ifs
    · exact Nat.zero_le _
    · exact hrun _ _ (hR q hq).1 (hR q hq).2
  · rw [List.eq_of_mem_replicate hm]
    exact Nat.zero_le _
  · exact hmainB msg (List.mem_append_right _ hm)

/-- **Alice's strategy in `H.compose ρ` is PPT** (`Strategy.Efficient`), when `main`'s and `ρ`'s
are and the call inputs are polynomial-time.

**Proof sketch.** Take polynomial-time functions of the machine layout for the efficient
strategies `ρ.P` and `main.P` (`ComposeMachines.Efficient.exists_polyTime`) and Alice's
call-input function from `H.PolyTime`. Alice's next message is `composePW` on the layout
`⟨⟨⟨1^n, ⟨⟨x, z⟩, hist⟩⟩, []⟩, r⟩` (`composeP_next_eq_composePW`):
1. the number `k = |hist|` of messages received, `L`, `R`, `k / R`, `k % R` and the mover test
   are unary computations (`GI.msgCount_poly`, `divNum_poly`, `modNum_poly`);
2. a run move is one activation of `ρ.P`'s machine on the call input (recomputed from the
   `main`-tape), the run tape cut from `r` and the run's messages read at the interleaved
   pairs (`ComposeMachines.runW`, `ComposeMachines.polyTimeComputable_slots`);
3. the main move is one activation of `main.P`'s machine on `⟨z, answers⟩` and the messages
   after the runs, the answers being `L(n)` such activations of `ρ.P`'s machine, padded and
   concatenated (`ComposeMachines.ansW`, `ComposeMachines.polyTimeComputable_flatMap_range`).
So `composePW` is polynomial-time (`polyTimeComputable_composePW`), and its uniform machine with
the coin polynomial `main.P.coins + calls · ρ.P.coins` computes `composeP`
(`GI.efficient_of_polyTime`). -/
theorem composeP_efficient {F : Functionality} (hH : H.PolyTime F) (hρ : G.PolyTime ρ) :
    (H.composeP ρ).Efficient := by
  obtain ⟨hmain, -, ⟨fA, hfA, hcallA⟩, -, -⟩ := (HybridProtocol.polyTime_iff H F).mp hH
  obtain ⟨hρP, -, -⟩ := (Functionality.polyTime_iff G ρ).mp hρ
  obtain ⟨Fρ, hFρ, hρeq⟩ := ComposeMachines.Efficient.exists_polyTime hρP
  obtain ⟨Fm, hFm, hmeq⟩ := ComposeMachines.Efficient.exists_polyTime hmain
  exact GI.efficient_of_polyTime _ (H.polyTimeComputable_composePW ρ hFρ hFm hfA)
    (H.composeP_next_eq_composePW ρ hρeq hmeq hcallA)

/-- **Bob's strategy in `H.compose ρ` is PPT** (`Strategy.Efficient`), when `main`'s and `ρ`'s
are and the call inputs are polynomial-time.

**Proof sketch.** As for Alice (`composeP_efficient`): Bob's next message is `composeVW` on the
layout (`composeV_next_eq_composeVW`), with `ρ.V`'s and `main.V`'s machines, Bob's call-input
function, the count `k = |hist| − 1`, the selector of Alice's moves, the drop count
`L·R + lead` before the main phase, and the coin polynomial `main.V.coins + calls · ρ.V.coins`;
`composeVW` is polynomial-time (`polyTimeComputable_composeVW`). -/
theorem composeV_efficient {F : Functionality} (hH : H.PolyTime F) (hρ : G.PolyTime ρ) :
    (H.composeV ρ).Efficient := by
  obtain ⟨-, hmain, -, ⟨fB, hfB, hcallB⟩, -⟩ := (HybridProtocol.polyTime_iff H F).mp hH
  obtain ⟨-, hρV, -⟩ := (Functionality.polyTime_iff G ρ).mp hρ
  obtain ⟨Fρ, hFρ, hρeq⟩ := ComposeMachines.Efficient.exists_polyTime hρV
  obtain ⟨Fm, hFm, hmeq⟩ := ComposeMachines.Efficient.exists_polyTime hmain
  exact GI.efficient_of_polyTime _ (H.polyTimeComputable_composeVW ρ hFρ hFm hfB)
    (H.composeV_next_eq_composeVW ρ hρeq hmeq hcallB)

/-- **The composed parties run in polynomial time** [Gol04, §7.3.1, the efficiency of the
protocol of Theorem 7.3.3]: if `H` runs in polynomial time on `F`'s inputs (`H.PolyTime F`) and
`ρ` on `G`'s (`G.PolyTime ρ`), then `H.compose ρ` runs in polynomial time on `F`'s inputs.
The two strategies are PPT (`composeP_efficient`, `composeV_efficient`, proved), and the
messages are bounded by `B_main + B_ρ` (`compose_msg_bound`, proved). The
message bound uses that `H.PolyTime` bounds `main`'s messages for **any** answers of the right
lengths, since `main` runs on `ρ`'s outputs. -/
theorem polyTime_compose {F : Functionality} (hH : H.PolyTime F) (hρ : G.PolyTime ρ) :
    F.PolyTime (H.compose ρ) :=
  (Functionality.polyTime_iff F (H.compose ρ)).mpr
    ⟨Eq.mpr (congrArg Strategy.Efficient (H.compose_P ρ))
        (H.composeP_efficient ρ hH hρ),
      Eq.mpr (congrArg Strategy.Efficient (H.compose_V ρ))
        (H.composeV_efficient ρ hH hρ),
      H.compose_msg_bound ρ hH hρ⟩

end Efficiency

/-! ### The composition theorem -/

/-- **The composition theorem for the semi-honest model** [Gol04, §7.3.1, Theorem 7.3.3; the
numbering is cited from memory and should be verified at audit]: if `H` is honest-but-curious
secure for `F` in the `G`-hybrid model (`H.HBCSecure F`) and `ρ` is honest-but-curious secure for
`G` ([PS10, Definition 155.1], `HBCSecure ρ G`), then `H.compose ρ` is honest-but-curious secure
for `F`, provided `main` has at least one move at every `n`.

**Deviations.** Ideal calls first, with the layout of `Compose.lean`; Definition 155.1 with
polynomial-time parties and one negligible bound for all inputs of each length; and the
hypothesis `hM` that `main` has at least one move. Without `hM` the statement is false under
D8's output convention (the module docstring gives an example): if `main.rounds(n) = 0`, the
last move of `H.compose ρ` is a run move or the leading filler, and its sender outputs that
message instead of its output in `main`.

**Proof sketch.** Write `L = calls(n)`. Efficiency is `polyTime_compose`. Alice's side is
`exists_simA` (`ComposeSecurity/SideA.lean`), Bob's is symmetric (`exists_simB`); for a
distinguisher `D` the sum of the two negligible bounds bounds both advantages. On Alice's side:
1. *The simulator* `S_A` (`ComposeSim.exists_simulator`), on `⟨1^n, ⟨x, f_A(x, y)⟩⟩`: run the
   hybrid simulator `S_A^H` on the same input and read its output as a view of `main` with
   private input `⟨x, a⟩` and tape `r_main`. For each `j < L`, recompute Alice's input to call
   `j`, `callA(n, x, r_main, j)` (polynomial time by `H.PolyTime`), and run `ρ`'s simulator
   `S_A^ρ` on it and the `j`-th `G.outA(n)`-bit block of `a`, with the `j`-th block of fresh
   coins. Output Alice's view of `H.compose ρ` (`ComposeSim.asmView`): input `x`, tape
   `r_main r_0 ⋯ r_{L−1}` (each cut or padded to its length), and the run messages at Bob's
   pairs, with fillers, followed by the hybrid view's messages (the layout of `compose_viewP`).
2. *Correct answers* (`ComposeProb.exists_correct`). The output clause of `HBCSecure ρ G`,
   applied to the machine that compares the second component of a sample with an advice string
   (each party's ideal output on the worst-case inputs of length `n`), bounds the probability
   that a party's `ρ`-output is not its ideal output by `ε_c(n)`, uniformly over the inputs. By
   the union bound, every run gives the ideal answers except with probability `L(n)ε_c(n)`
   (`uprob_not_goodRuns_le`), and then the real sample is the assembled view of the real run
   views with the hybrid main phase and Bob's output in `main` (`realA_compose_eq`, using `hM`;
   the statistical switch `ComposeProb.distAdv_le_uprob_of_eq`).
3. *Hybrid argument over the runs* (`ComposeProb.abs_chain_le`). In hybrid `i` the first `i`
   run views are `S_A^ρ`'s outputs on the call inputs and the ideal answers. Resampling run `i`
   at fixed other coordinates (`exists_hyb_step`), neighbouring hybrids give a distinguisher for
   `ρ`'s Alice side that holds as advice the template of the worst-case inputs, run index and
   coordinates at length `n`: the header of the view, the other runs' words and Bob's output,
   of polynomial length (`exists_tmplA_bound`). It inserts the `ρ`-view and assembles the
   sample in polynomial time (`ComposeSim.exists_gap_le`), so each step is within `ε₂(n)`.
4. *The hybrid model.* With every run simulated the sample is `Φ` applied to the hybrid real
   sample `H.realA F n x y` (`acceptProb_realA_dPhi`), and `idealA S_A` is `Φ` applied to
   `F.idealA S_A^H` (`ComposeProb.acceptProb_post_pre`). `D ∘ Φ` is a non-uniform PPT
   (`ComposeSim.exists_dPhi`), so `H.HBCSecure F` bounds the remaining distance by `ε₃(n)`.
5. In total `L(n)(ε_c(n) + ε₂(n)) + ε₃(n)`, negligible since `L` is a polynomial
   (`ComposeProb.negligible_polyExpr_mul`). -/
theorem hbcSecure_compose {G F : Functionality} (H : HybridProtocol G) (ρ : Protocol)
    (hM : ∀ n, 0 < H.main.rounds.eval n) (hH : H.HBCSecure F)
    (hρ : SecureComputation.HBCSecure ρ G) : SecureComputation.HBCSecure (H.compose ρ) F := by
  have hHpt := ((HybridProtocol.hbcSecure_iff H F).mp hH).1
  have hρpt := ((SecureComputation.hbcSecure_iff ρ G).mp hρ).1
  obtain ⟨SA, hSA⟩ := H.exists_simA ρ hM hH hρ
  obtain ⟨SB, hSB⟩ := H.exists_simB ρ hM hH hρ
  refine (SecureComputation.hbcSecure_iff (H.compose ρ) F).mpr
    ⟨H.polyTime_compose ρ hHpt hρpt, SA, SB, fun D => ?_⟩
  obtain ⟨εA, hεA, hA⟩ := hSA D
  obtain ⟨εB, hεB, hB⟩ := hSB D
  refine ⟨fun n => εA n + εB n, hεA.add hεB, fun n x y => ⟨?_, ?_⟩⟩
  · -- `εB n` bounds a distinguishing advantage, so it is nonnegative
    have h0 : 0 ≤ εB n := (abs_nonneg _).trans ((distAdv_def _ _ _).symm.le.trans (hB n x y))
    exact (hA n x y).trans (le_add_of_nonneg_right h0)
  · have h0 : 0 ≤ εA n := (abs_nonneg _).trans ((distAdv_def _ _ _).symm.le.trans (hA n x y))
    exact (hB n x y).trans (le_add_of_nonneg_left h0)

end HybridProtocol

end TCSlib.Cryptography.SecureComputation

## ===== TCSlib/Cryptography/SecureComputation/ComposeSecurity/Accept.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Runs
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Probability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Acceptance of machines with split coins

The bookkeeping between the distinguishers and simulators of the composition theorem
[Gol04, §7.3.1, proof of Theorem 7.3.3] and the samplers they act on:
* coins as two strings (`appendCoins`) or as blocks (`blocksCoins`), read back by `take`, `drop`
  and `coinBlock`;
* a distinguisher `B` that pre-processes its sample with `p(n)` of its coins and hands the rest
  to `D` accepts a sampler `X` as often as `D` accepts the pre-processed sampler on the seed
  extended by those coins (`acceptProb_pre`);
* a simulator that post-processes another machine's output, against a distinguisher that
  pre-processes with the same map, is accepted as the other machine against the distinguisher
  (`acceptProb_post_pre`);
* a test machine with output `[P w]` accepts with the probability of `P` (`acceptProb_test`);
  the comparison of the second component of a sample with an advice string is such a machine
  (`exists_test`).

## Main definitions

* `ComposeProb.appendCoins`, `ComposeProb.blocksCoins`.

## Main results

* `ComposeProb.acceptProb_pre`, `ComposeProb.acceptProb_post_pre`, `ComposeProb.acceptProb_test`,
  `ComposeProb.exists_test`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §2.1 (non-uniform PPT machines, Definition 26.8) and §6.2 (Definition 155.1).
-/

namespace TCSlib.Cryptography.SecureComputation.ComposeProb

open Complexity Turing TCSlib.Cryptography

/-! ### Coins as strings -/

/-- **Two coin strings as one**: `{0,1}^a × {0,1}^b ≃ {0,1}^c` for `c = a + b`, the first string
followed by the second (`Fin.appendEquiv`). -/
def appendCoins {a b c : ℕ} (h : c = a + b) : (Fin a → Bool) × (Fin b → Bool) ≃ (Fin c → Bool) :=
  (Fin.appendEquiv a b).trans (Equiv.arrowCongr (finCongr h.symm) (Equiv.refl Bool))

/-- The defining equation of `appendCoins` (see `appendCoins`).
`appendCoins h = (Fin.appendEquiv a b).trans (Equiv.arrowCongr (finCongr h.symm) (Equiv.refl
Bool))`. -/
theorem appendCoins_eq {a b c : ℕ} (h : c = a + b) :
    appendCoins h =
      (Fin.appendEquiv a b).trans (Equiv.arrowCongr (finCongr h.symm) (Equiv.refl Bool)) := rfl

/-- `⟦appendCoins h (u, v)⟧ = ⟦u⟧ ++ ⟦v⟧`. -/
theorem ofFn_appendCoins {a b c : ℕ} (h : c = a + b) (u : Fin a → Bool) (v : Fin b → Bool) :
    List.ofFn (appendCoins h (u, v)) = List.ofFn u ++ List.ofFn v := by
  rw [appendCoins_eq, Equiv.trans_apply, ofFn_arrowCongr_finCongr]
  exact List.ofFn_fin_append u v

/-- The first `a` bits of `appendCoins h (u, v)` are `u`.
`(List.ofFn (appendCoins h (u, v))).take a = List.ofFn u`. -/
theorem take_ofFn_appendCoins {a b c : ℕ} (h : c = a + b) (u : Fin a → Bool) (v : Fin b → Bool) :
    (List.ofFn (appendCoins h (u, v))).take a = List.ofFn u := by
  rw [ofFn_appendCoins, List.take_left' List.length_ofFn]

/-- The bits of `appendCoins h (u, v)` after the first `a` are `v`.
`(List.ofFn (appendCoins h (u, v))).drop a = List.ofFn v`. -/
theorem drop_ofFn_appendCoins {a b c : ℕ} (h : c = a + b) (u : Fin a → Bool) (v : Fin b → Bool) :
    (List.ofFn (appendCoins h (u, v))).drop a = List.ofFn v := by
  rw [ofFn_appendCoins, List.drop_left' List.length_ofFn]

/-- **Blocks of coins as one string**: `({0,1}^b)^q ≃ {0,1}^m` for `m = q·b`, the blocks in order
(`FunFamily.blocks`). -/
def blocksCoins {m q b : ℕ} (h : m = q * b) : (Fin q → Fin b → Bool) ≃ (Fin m → Bool) :=
  (FunFamily.blocks q b).symm.trans (Equiv.arrowCongr (finCongr h.symm) (Equiv.refl Bool))

/-- The defining equation of `blocksCoins` (see `blocksCoins`).
`blocksCoins h = (FunFamily.blocks q b).symm.trans (Equiv.arrowCongr (finCongr h.symm) (Equiv.refl
Bool))`. -/
theorem blocksCoins_eq {m q b : ℕ} (h : m = q * b) :
    blocksCoins h =
      (FunFamily.blocks q b).symm.trans (Equiv.arrowCongr (finCongr h.symm) (Equiv.refl Bool)) :=
  rfl

/-- `⟦blocksCoins h t⟧ = ⟦t 0⟧ ++ ⋯ ++ ⟦t (q − 1)⟧` (`ComposeSim.ofFn_blocks_symm`). -/
theorem ofFn_blocksCoins {m q b : ℕ} (h : m = q * b) (t : Fin q → Fin b → Bool) :
    List.ofFn (blocksCoins h t) = (List.ofFn fun j => List.ofFn (t j)).flatten := by
  rw [blocksCoins_eq, Equiv.trans_apply, ofFn_arrowCongr_finCongr, ComposeSim.ofFn_blocks_symm]

/-- Block `j` of `blocksCoins h t` is `t j`: `coinBlock b j ⟦blocksCoins h t⟧ = ⟦t j⟧`
(`coinBlock_flatten`). -/
theorem coinBlock_blocksCoins {m q b : ℕ} (h : m = q * b) (t : Fin q → Fin b → Bool) (j : Fin q) :
    coinBlock b j (List.ofFn (blocksCoins h t)) = List.ofFn (t j) := by
  rw [ofFn_blocksCoins, coinBlock_flatten (List.ofFn fun j => List.ofFn (t j))
    (fun c hc => by
      obtain ⟨i, -, rfl⟩ := List.mem_ofFn.1 hc
      exact List.length_ofFn) j (by rw [List.length_ofFn]; exact j.2), List.getElem_ofFn]

/-! ### Acceptance -/

/-- **A distinguisher with pre-processing and extra coins**: if `B` has coins `p + D.coins` and
`B(1^n, w; r) = D(1^n, Ψ w r_{<p(n)}; r_{≥p(n)})`, then
`acceptProb X (B.distinguisherL n) = acceptProb (fun (s, e) => Ψ (X s) ⟦e⟧) (D.distinguisherL n)`
over `e ∈ {0,1}^{p(n)}`.

**Proof sketch.** Split `B`'s coins as `{0,1}^{p(n)} × D.Coins n` (`appendCoins`,
`uprob_comp_equiv`); the cut coins are the two halves (`take_ofFn_appendCoins`,
`drop_ofFn_appendCoins`); reassociate the seed (`Equiv.prodAssoc`). -/
theorem acceptProb_pre {σ : Type*} [Fintype σ] (X : σ → List Bool) (B D : NUPPT) (p : PolyExpr)
    (n : ℕ) (Ψ : List Bool → List Bool → List Bool) (hc : B.coins = .add p D.coins)
    (hB : ∀ w r, B.runAtL n w r = D.runAtL n (Ψ w (r.take (p.eval n))) (r.drop (p.eval n))) :
    acceptProb X (B.distinguisherL n) =
      acceptProb (fun z : σ × (Fin (p.eval n) → Bool) => Ψ (X z.1) (List.ofFn z.2))
        (D.distinguisherL n) := by
  have hlen : B.coinLen n = p.eval n + D.coinLen n := by
    rw [NUPPT.coinLen_eq, NUPPT.coinLen_eq, hc, PolyExpr.eval_add]
  let e : (Fin (p.eval n) → Bool) × D.Coins n ≃ B.Coins n := appendCoins hlen
  rw [acceptProb_def, acceptProb_def]
  calc uprob (fun z : σ × B.Coins n => B.distinguisherL n (X z.1) z.2 = true)
      = uprob (fun z : σ × ((Fin (p.eval n) → Bool) × D.Coins n) =>
          B.distinguisherL n (X z.1) (e z.2) = true) :=
        (uprob_comp_equiv ((Equiv.refl σ).prodCongr e)
          (fun z : σ × B.Coins n => B.distinguisherL n (X z.1) z.2 = true)).symm
    _ = uprob (fun z : σ × ((Fin (p.eval n) → Bool) × D.Coins n) =>
          D.distinguisherL n (Ψ (X z.1) (List.ofFn z.2.1)) z.2.2 = true) := by
        congr 1
        funext z
        rw [NUPPT.distinguisherL_eq, NUPPT.distinguisherL_eq, NUPPT.runAt_eq, NUPPT.runAt_eq, hB,
          take_ofFn_appendCoins, drop_ofFn_appendCoins]
    _ = uprob (fun z : (σ × (Fin (p.eval n) → Bool)) × D.Coins n =>
          D.distinguisherL n (Ψ (X z.1.1) (List.ofFn z.1.2)) z.2 = true) :=
        (uprob_comp_equiv (Equiv.prodAssoc σ (Fin (p.eval n) → Bool) (D.Coins n))
          (fun z : σ × ((Fin (p.eval n) → Bool) × D.Coins n) =>
            D.distinguisherL n (Ψ (X z.1) (List.ofFn z.2.1)) z.2.2 = true)).symm

/-- **A simulator with post-processing against a distinguisher with pre-processing**: let
`S(1^n, w; r) = Ψ (S'(1^n, w; r_{<S'.coins(n)})) r_{≥S'.coins(n)}` with coins `S'.coins + p`, and
`B(1^n, v; r) = D(1^n, Ψd v r_{<p(n)}; r_{≥p(n)})` with coins `p + D.coins`, where
`Ψd ⟨hv, o⟩ e = ⟨Ψ hv e, o⟩`. Then `D` accepts `⟨S(1^n, w), o⟩` as often as `B` accepts
`⟨S'(1^n, w), o⟩`.

**Proof sketch.** Split `S`'s coins as `S'.Coins n × {0,1}^{p(n)}` (`appendCoins`,
`acceptProb_comp_equiv`; `take_ofFn_appendCoins`, `drop_ofFn_appendCoins`), and unfold `B` by
`acceptProb_pre`; the two samplers on `S'.Coins n × {0,1}^{p(n)}` agree by `hΨ`. -/
theorem acceptProb_post_pre (S S' B D : NUPPT) (p : PolyExpr) (n : ℕ)
    (Ψ Ψd : List Bool → List Bool → List Bool) (w o : List Bool)
    (hSc : S.coins = .add S'.coins p)
    (hS : ∀ r, S.runAtL n w r =
      Ψ (S'.runAtL n w (r.take (S'.coinLen n))) (r.drop (S'.coinLen n)))
    (hBc : B.coins = .add p D.coins)
    (hB : ∀ v r, B.runAtL n v r = D.runAtL n (Ψd v (r.take (p.eval n))) (r.drop (p.eval n)))
    (hΨ : ∀ hv e, Ψd (pairEncode hv o) e = pairEncode (Ψ hv e) o) :
    acceptProb (fun s : S.Coins n => pairEncode (S.runAt n w s) o) (D.distinguisherL n) =
      acceptProb (fun s : S'.Coins n => pairEncode (S'.runAt n w s) o) (B.distinguisherL n) := by
  have hlen : S.coinLen n = S'.coinLen n + p.eval n := by
    rw [NUPPT.coinLen_eq, NUPPT.coinLen_eq, hSc, PolyExpr.eval_add]
  rw [acceptProb_pre _ B D p n Ψd hBc hB]
  refine (acceptProb_comp_equiv (appendCoins hlen)
    (fun s : S.Coins n => pairEncode (S.runAt n w s) o) (D.distinguisherL n)).symm.trans ?_
  refine congrArg (fun f => acceptProb f (D.distinguisherL n)) (funext fun z => ?_)
  rw [hΨ, NUPPT.runAt_eq, NUPPT.runAt_eq, hS, take_ofFn_appendCoins, drop_ofFn_appendCoins]

/-- **A test machine**: if `B(1^n, w; r) = [P w]` for all `w`, `r`, then `B` accepts the sampler
`X` with probability `Pr_s[P (X s)]`:
`acceptProb X (B.distinguisherL n) = uprob (fun s => P (X s) = true)` (`uprob_fst`). -/
theorem acceptProb_test {σ : Type*} [Fintype σ] (X : σ → List Bool) (B : NUPPT) (n : ℕ)
    (P : List Bool → Bool) (hB : ∀ w r, B.runAtL n w r = [P w]) :
    acceptProb X (B.distinguisherL n) = uprob fun s => P (X s) = true := by
  have h : (fun z : σ × B.Coins n => B.distinguisherL n (X z.1) z.2 = true) =
      fun z => P (X z.1) = true := by
    funext z
    rw [NUPPT.distinguisherL_eq, NUPPT.runAt_eq, hB]
    simp
  rw [acceptProb_def, h]
  exact uprob_fst fun s => P (X s) = true

/-- **The comparison with an advice string**: for a polynomially bounded advice family `α` there
is an `NUPPT` `B` with `B(1^n, w; r) = [eqW ⟨pairSndD w, α n⟩]`, which accepts exactly when the
second component of the sample is `α n` (`BinArith.eqW_pairEncode`). -/
theorem exists_test (α : ℕ → List Bool) (a : PolyExpr) (hα : ∀ n, (α n).length ≤ a.eval n) :
    ∃ B : NUPPT, ∀ n w r, B.runAtL n w r = [BinArith.eqW (pairEncode (pairSndD w) (α n))] := by
  have hf : PolyTimeComputable fun z =>
      [BinArith.eqW (pairEncode (pairSndD (NUPPT.inArg z)) (NUPPT.inAdvice z))] :=
    BinArith.polyTimeComputable_eqW.comp' ((polyTimeComputable_pairSndD.comp'
      NUPPT.polyTimeComputable_inArg).pairEncode NUPPT.polyTimeComputable_inAdvice)
  refine ⟨NUPPT.ofPolyTime hf (.const 0) a α hα, fun n w r => ?_⟩
  rw [NUPPT.runAtL_ofPolyTime]
  simp only [NUPPT.advInput_eq, ← NUPPT.layout_eq, NUPPT.inArg_layout, NUPPT.inAdvice_layout]

end TCSlib.Cryptography.SecureComputation.ComposeProb

## ===== TCSlib/Cryptography/SecureComputation/ComposeSecurity/Assembly.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Efficiency

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Assembling a view of the composed protocol from views of the runs

The post-processing of the simulators and reductions of the composition theorem
[Gol04, §7.3.1, proof of Theorem 7.3.3]: a party's view of `H.compose ρ` is its common input, its
input, its tape (the `main`-tape followed by one `ρ`-tape per run) and its received messages
(the other party's run messages at the pairs, with fillers, the leading fillers and the main
phase). Given a word `V j` per run that reads as an encoded view of `ρ`
(`⟨⟨x, z⟩, ⟨r, encodeMsgs received⟩⟩`, `View.encode`), `asmView` assembles such a view: the run
tapes are cut or padded to `ρ`'s coin length, and the received run messages are placed at the
pairs where the other party moves (the `k`-th message received at the `k`-th such pair, `p / 2`).

## Main definitions

* `ComposeSim.segW`: the pair chunks of one run, from the run's encoded received messages.
* `ComposeSim.asmView`: the assembled encoded view; `ComposeSim.asmW` its word form.

## Main results

* `ComposeSim.moverIsV_beq_iff`, `length_filter_mover`, `getD_filter_map_mover`: the parity of
  the pairs at which a party moves, and the position of a run message among them.
* `ComposeSim.polyTimeComputable_asmW`: the assembly is polynomial-time.

## References

* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
  University Press, 2004, §7.3.1 (the proof of Theorem 7.3.3).
-/

namespace TCSlib.Cryptography.SecureComputation.ComposeSim

open Complexity Turing Complexity.StateLoop TCSlib.Cryptography.EncodingMachines ComposeMachines

/-! ### The pairs at which a party moves -/

/-- **The mover test is a parity**: `moverIsV vF q == b` iff `q % 2 = (if vF == b then 0 else 1)`
(`moverIsV_def`). -/
theorem moverIsV_beq_iff (vF b : Bool) (q : ℕ) :
    (moverIsV vF q == b) = true ↔ q % 2 = (if vF == b then 0 else 1) := by
  rw [moverIsV_def]
  rcases Nat.mod_two_eq_zero_or_one q with h | h <;> cases vF <;> cases b <;> simp [h]

/-- The number of `q < p` with `q % 2 = d` (for `d ≤ 1`) is `(p + 1 − d) / 2`. -/
theorem length_filter_mod_two {d : ℕ} (hd : d ≤ 1) :
    ∀ p, ((List.range p).filter fun q => q % 2 == d).length = (p + 1 - d) / 2
  | 0 => by
    rw [List.range_zero, List.filter_nil, List.length_nil]
    omega
  | p + 1 => by
    rw [List.range_succ, List.filter_append, List.length_append, length_filter_mod_two hd p,
      List.filter_singleton]
    by_cases h : p % 2 = d
    · rw [show (p % 2 == d) = true from beq_iff_eq.2 h, cond_true, List.length_singleton]
      omega
    · rw [show (p % 2 == d) = false from beq_eq_false_iff_ne.2 h, cond_false, List.length_nil]
      omega

/-- **The number of moves of a party before its move `p`** is `p / 2`: if
`moverIsV vF p == b`, then `|{q < p : moverIsV vF q == b}| = p / 2` (`moverIsV_beq_iff`,
`length_filter_mod_two`). -/
theorem length_filter_mover (vF b : Bool) {p : ℕ} (hp : (moverIsV vF p == b) = true) :
    ((List.range p).filter fun q => moverIsV vF q == b).length = p / 2 := by
  have hd : (if vF == b then 0 else 1) ≤ 1 := by split_ifs <;> omega
  have hpar := (moverIsV_beq_iff vF b p).1 hp
  have hfilt : ((List.range p).filter fun q => moverIsV vF q == b) =
      (List.range p).filter fun q => q % 2 == (if vF == b then 0 else 1) := by
    refine List.filter_congr fun q _ => ?_
    rw [Bool.eq_iff_iff, moverIsV_beq_iff]
    exact beq_iff_eq.symm
  rw [hfilt, length_filter_mod_two hd]
  split_ifs at hpar ⊢ <;> omega

/-- **A run message at its position**: for `p < R` with `moverIsV vF p == b`, entry `p / 2` of
the messages `f q` at the `q < R` with `moverIsV vF q == b` is `f p`
(`length_filter_mover`). -/
theorem getD_filter_map_mover (vF b : Bool) (f : ℕ → List Bool) {R p : ℕ} (hpR : p < R)
    (hp : (moverIsV vF p == b) = true) :
    (((List.range R).filter fun q => moverIsV vF q == b).map f).getD (p / 2) [] = f p := by
  obtain ⟨d, rfl⟩ : ∃ d, R = p + 1 + d := ⟨R - (p + 1), by omega⟩
  rw [List.range_add, List.range_succ, List.filter_append, List.filter_append,
    List.filter_singleton, hp, cond_true, List.map_append, List.map_append, List.map_singleton,
    List.append_assoc, List.getD_eq_getElem?_getD, List.getElem?_append_right (by
      rw [List.length_map, length_filter_mover vF b hp]), List.length_map,
    length_filter_mover vF b hp, Nat.sub_self, List.singleton_append, List.getElem?_cons_zero,
    Option.getD_some]

/-- Padding a word of the right length is the identity: `|w| = L → padTo L w = w`. -/
theorem padTo_of_length {L : ℕ} {w : List Bool} (h : w.length = L) : padTo L w = w := by
  rw [padTo_eq, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

/-- A concatenation over `range a` is one over `range b` when `a = b` (no rewriting inside the
chunks): `a = b → (range a).flatMap f = (range b).flatMap f`. -/
theorem flatMap_range_congr {a b : ℕ} (h : a = b) (f : ℕ → List Bool) :
    (List.range a).flatMap f = (List.range b).flatMap f := by
  subst h
  rfl

/-! ### One run's chunks -/

/-- **The pair chunks of one run**, from the encoded received messages `e` of the run's view:
for `p < R`, the chunk `⟨m_p, []⟩` with `m_p` the message received at the `p / 2`-th of the pairs
where the other party moves (`moverIsV vF p == b`) and `[]` (a filler) at the others:
`segW vF b R e = (range R).flatMap fun p =>
⟨if moverIsV vF p == b then pairFstD (pairSndD^[p / 2] e) else [], []⟩`. -/
def segW (vF b : Bool) (R : ℕ) (e : List Bool) : List Bool :=
  (List.range R).flatMap fun p =>
    pairEncode (if moverIsV vF p == b then pairFstD (pairSndD^[p / 2] e) else []) []

/-- The defining equation of `segW` (see `segW`).
`segW vF b R e = (List.range R).flatMap fun p => pairEncode (if moverIsV vF p == b then pairFstD
(pairSndD^[p / 2] e) else []) []`. -/
theorem segW_eq (vF b : Bool) (R : ℕ) (e : List Bool) :
    segW vF b R e = (List.range R).flatMap fun p =>
      pairEncode (if moverIsV vF p == b then pairFstD (pairSndD^[p / 2] e) else []) [] := rfl

/-- **`segW` on a real run**: if the run's received messages are the messages `f q` at the
`q < R` with `moverIsV vF q == b`, the chunks are `⟨f p, []⟩` at those pairs and `⟨[], []⟩` at
the others:
`segW vF b R (encodeMsgs (filter … (range R)).map f) =
(range R).flatMap fun p => ⟨if moverIsV vF p == b then f p else [], []⟩`
(`msgAt_encodeMsgs`, `getD_filter_map_mover`). -/
theorem segW_encodeMsgs (vF b : Bool) (R : ℕ) (f : ℕ → List Bool) :
    segW vF b R (Strategy.encodeMsgs (((List.range R).filter fun q => moverIsV vF q == b).map f)) =
      (List.range R).flatMap fun p =>
        pairEncode (if moverIsV vF p == b then f p else []) [] := by
  rw [segW_eq]
  refine List.flatMap_congr fun p hp => ?_
  by_cases h : (moverIsV vF p == b) = true
  · rw [if_pos h, if_pos h, msgAt_encodeMsgs, getD_filter_map_mover vF b f (List.mem_range.1 hp) h]
  · rw [if_neg h, if_neg h]

/-! ### The assembled view -/

/-- **The assembled encoded view** of a party of `H.compose ρ` (`n = |x₁|`, `L = calls(n)`,
`R = rounds(n)`, `c = cρ(n)`), from its common input `x₁`, input `xin`, `main`-tape `mt`, encoded
main-phase messages `me`, the number `lead` of leading fillers it receives, and one word `V j`
per run read as an encoded `ρ`-view: the view `⟨⟨x₁, xin⟩, ⟨mt ++ τ, E⟩⟩` with the tape
`τ = (range L).flatMap fun j => padTo c (tape of V j)` and the messages
`E = (range L).flatMap (fun j => segW vF b R (messages of V j)) ++ encodeMsgs [[]]^lead ++ me`. -/
def asmView (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ) (x₁ xin mt me : List Bool)
    (V : ℕ → List Bool) : List Bool :=
  pairEncode (pairEncode x₁ xin)
    (pairEncode (mt ++ (List.range (calls.eval x₁.length)).flatMap fun j =>
        padTo (cρ.eval x₁.length) (pairFstD (pairSndD (V j))))
      ((List.range (calls.eval x₁.length)).flatMap (fun j =>
          segW vF b (rounds.eval x₁.length) (pairSndD (pairSndD (V j)))) ++
        Strategy.encodeMsgs (List.replicate lead []) ++ me))

/-- The defining equation of `asmView` (see `asmView`).
`asmView calls rounds cρ vF b lead x₁ xin mt me V = pairEncode (pairEncode x₁ xin) (pairEncode (mt
++ (List.range (calls.eval x₁.length)).flatMap fun j => padTo (cρ.eval x₁.length) (pairFstD
(pairSndD (V j)))) ((List.range (calls.eval …`. -/
theorem asmView_eq (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ)
    (x₁ xin mt me : List Bool) (V : ℕ → List Bool) :
    asmView calls rounds cρ vF b lead x₁ xin mt me V =
      pairEncode (pairEncode x₁ xin)
        (pairEncode (mt ++ (List.range (calls.eval x₁.length)).flatMap fun j =>
            padTo (cρ.eval x₁.length) (pairFstD (pairSndD (V j))))
          ((List.range (calls.eval x₁.length)).flatMap (fun j =>
              segW vF b (rounds.eval x₁.length) (pairSndD (pairSndD (V j)))) ++
            Strategy.encodeMsgs (List.replicate lead []) ++ me)) := rfl

/-- `asmView` depends on the run words only below `L`: if `V j = V' j` for `j < calls(|x₁|)`, the
assembled views agree. -/
theorem asmView_congr (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ)
    (x₁ xin mt me : List Bool) {V V' : ℕ → List Bool}
    (h : ∀ j < calls.eval x₁.length, V j = V' j) :
    asmView calls rounds cρ vF b lead x₁ xin mt me V =
      asmView calls rounds cρ vF b lead x₁ xin mt me V' := by
  have h₁ : ((List.range (calls.eval x₁.length)).flatMap fun j =>
      padTo (cρ.eval x₁.length) (pairFstD (pairSndD (V j)))) =
      (List.range (calls.eval x₁.length)).flatMap fun j =>
        padTo (cρ.eval x₁.length) (pairFstD (pairSndD (V' j))) :=
    List.flatMap_congr fun j hj => by rw [h j (List.mem_range.1 hj)]
  have h₂ : ((List.range (calls.eval x₁.length)).flatMap fun j =>
      segW vF b (rounds.eval x₁.length) (pairSndD (pairSndD (V j)))) =
      (List.range (calls.eval x₁.length)).flatMap fun j =>
        segW vF b (rounds.eval x₁.length) (pairSndD (pairSndD (V' j))) :=
    List.flatMap_congr fun j hj => by rw [h j (List.mem_range.1 hj)]
  rw [asmView_eq, asmView_eq, h₁, h₂]

/-- **The assembly in word form**: on `w = ⟨⟨⟨x₁, xin⟩, ⟨mt, me⟩⟩, VL⟩`, `asmView` with the run
words `V j = pairFstD (pairSndD^[j] VL)` (the entries of an encoded list,
`msgAt_encodeMsgs`). -/
def asmW (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ) (w : List Bool) : List Bool :=
  asmView calls rounds cρ vF b lead (pairFstD (pairFstD (pairFstD w)))
    (pairSndD (pairFstD (pairFstD w))) (pairFstD (pairSndD (pairFstD w)))
    (pairSndD (pairSndD (pairFstD w))) fun j => pairFstD (pairSndD^[j] (pairSndD w))

/-- The defining equation of `asmW` (see `asmW`).
`asmW calls rounds cρ vF b lead w = asmView calls rounds cρ vF b lead (pairFstD (pairFstD (pairFstD
w))) (pairSndD (pairFstD (pairFstD w))) (pairFstD (pairSndD (pairFstD w))) (pairSndD (pairSndD
(pairFstD w))) fun j => pairFstD …`. -/
theorem asmW_eq (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ) (w : List Bool) :
    asmW calls rounds cρ vF b lead w =
      asmView calls rounds cρ vF b lead (pairFstD (pairFstD (pairFstD w)))
        (pairSndD (pairFstD (pairFstD w))) (pairFstD (pairSndD (pairFstD w)))
        (pairSndD (pairSndD (pairFstD w))) fun j => pairFstD (pairSndD^[j] (pairSndD w)) := rfl

/-- `asmW` on its word: `asmW … ⟨⟨⟨x₁, xin⟩, ⟨mt, me⟩⟩, VL⟩ =
asmView … x₁ xin mt me (fun j => pairFstD (pairSndD^[j] VL))`. -/
theorem asmW_pairEncode (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ)
    (x₁ xin mt me VL : List Bool) :
    asmW calls rounds cρ vF b lead
        (pairEncode (pairEncode (pairEncode x₁ xin) (pairEncode mt me)) VL) =
      asmView calls rounds cρ vF b lead x₁ xin mt me fun j => pairFstD (pairSndD^[j] VL) := by
  rw [asmW_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]

/-- **`segW` is polynomial-time** on `⟨1^R, e⟩` words given by polynomial-time maps
(`polyTimeComputable_flatMap_range` over `p < R`, the mover test `polyTimeComputable_moverW`,
`p / 2` by `divNum_poly`, the message by `iterSnd_poly`). -/
theorem polyTimeComputable_segW (vF b : Bool) {R : List Bool → ℕ} {e : List Bool → List Bool}
    (hR : PolyTimeComputable fun z => List.replicate (R z) true) (he : PolyTimeComputable e) :
    PolyTimeComputable fun z => segW vF b (R z) (e z) := by
  have hhalf : PolyTimeComputable fun v => List.replicate ((pairFstD v).length / 2) true :=
    (divNum_poly (unaryLength_poly polyTimeComputable_pairFstD) (unaryConst_poly 2)).congr
      fun v => by rw [divNum_eq]
  have hmsg := polyTimeComputable_pairFstD.comp'
    (iterSnd_poly (he.comp' polyTimeComputable_pairSndD) hhalf)
  have hchunk : PolyTimeComputable fun v =>
      pairEncode (if moverIsV vF (pairFstD v).length == b then
        pairFstD (pairSndD^[(pairFstD v).length / 2] (e (pairSndD v))) else []) [] :=
    (polyTimeComputable_ite ((polyTimeComputable_moverW vF b).congr fun v => moverW_eq vF b v)
      hmsg (polyTimeComputable_const [])).pairEncode (polyTimeComputable_const [])
  exact (polyTimeComputable_flatMap_range hchunk hR).congr fun z => (segW_eq vF b (R z) (e z)).symm

/-- **The assembly is polynomial-time**: `PolyTimeComputable (asmW calls rounds cρ vF b lead)`.

**Proof sketch.** The components `x₁`, `xin`, `mt`, `me` are projections. The tape part and the
message part are concatenations over the unary count `calls(|x₁|)`
(`polyTimeComputable_flatMap_range`) of a padded tape (`padTo_poly`) and of `segW`
(`polyTimeComputable_segW`) of the run word `pairFstD (pairSndD^[j] VL)` (`iterSnd_poly`),
followed by constant fillers and `me`; the word is `asmView` of these (`asmW_eq`,
`asmView_eq`). -/
theorem polyTimeComputable_asmW (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ) :
    PolyTimeComputable (asmW calls rounds cρ vF b lead) := by
  have hx₁ : PolyTimeComputable fun w => pairFstD (pairFstD (pairFstD w)) :=
    polyTimeComputable_pairFstD.comp'
      (polyTimeComputable_pairFstD.comp' polyTimeComputable_pairFstD)
  have hxin : PolyTimeComputable fun w => pairSndD (pairFstD (pairFstD w)) :=
    polyTimeComputable_pairSndD.comp'
      (polyTimeComputable_pairFstD.comp' polyTimeComputable_pairFstD)
  have hmt : PolyTimeComputable fun w => pairFstD (pairSndD (pairFstD w)) :=
    polyTimeComputable_pairFstD.comp'
      (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairFstD)
  have hme : PolyTimeComputable fun w => pairSndD (pairSndD (pairFstD w)) :=
    polyTimeComputable_pairSndD.comp'
      (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairFstD)
  -- the run word `V j` from `v = ⟨1^j, w⟩`
  have hV : PolyTimeComputable fun v =>
      pairFstD (pairSndD^[(pairFstD v).length] (pairSndD (pairSndD v))) :=
    polyTimeComputable_pairFstD.comp' (iterSnd_poly
      (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD)
      (unaryLength_poly polyTimeComputable_pairFstD))
  have hn : PolyTimeComputable fun v =>
      List.replicate (pairFstD (pairFstD (pairFstD (pairSndD v)))).length true :=
    unaryLength_poly (hx₁.comp' polyTimeComputable_pairSndD)
  have htape : PolyTimeComputable fun v =>
      padTo (cρ.eval (pairFstD (pairFstD (pairFstD (pairSndD v)))).length)
        (pairFstD (pairSndD (pairFstD (pairSndD^[(pairFstD v).length]
          (pairSndD (pairSndD v)))))) :=
    padTo_poly ((polyTimeComputable_pairFstD.comp' polyTimeComputable_pairSndD).comp' hV)
      (unaryPolyOf_poly cρ hn)
  have hseg : PolyTimeComputable fun v =>
      segW vF b (rounds.eval (pairFstD (pairFstD (pairFstD (pairSndD v)))).length)
        (pairSndD (pairSndD (pairFstD (pairSndD^[(pairFstD v).length]
          (pairSndD (pairSndD v)))))) :=
    polyTimeComputable_segW vF b (unaryPolyOf_poly rounds hn)
      ((polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD).comp' hV)
  have hL := unaryPolyOf_poly calls (unaryLength_poly hx₁)
  have hT := polyTimeComputable_flatMap_range (E := fun w j =>
    padTo (cρ.eval (pairFstD (pairFstD (pairFstD w))).length)
      (pairFstD (pairSndD (pairFstD (pairSndD^[j] (pairSndD w)))))) htape hL
  have hS := polyTimeComputable_flatMap_range (E := fun w j =>
    segW vF b (rounds.eval (pairFstD (pairFstD (pairFstD w))).length)
      (pairSndD (pairSndD (pairFstD (pairSndD^[j] (pairSndD w)))))) hseg hL
  exact (((hx₁.pairEncode hxin).pairEncode ((hmt.append hT).pairEncode
    ((hS.append (polyTimeComputable_const _)).append hme)))).congr fun w => by
      rw [asmW_eq, asmView_eq]

end TCSlib.Cryptography.SecureComputation.ComposeSim

## ===== TCSlib/Cryptography/SecureComputation/ComposeSecurity/Bounds.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Machines

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial length bounds

The advice of a non-uniform reduction has polynomially bounded length (`NUPPT.advice_length`). The
reductions of the composition theorem [Gol04, §7.3.1, proof of Theorem 7.3.3] hard-wire views and
outputs of executions, so their lengths must be bounded by a polynomial in `n`. This file collects
the lengths of the encodings (`encodeMsgs`, the machine layouts), of the transcripts, and of the
outputs of machines and efficient strategies.

## Main results

* `ComposeBound.length_encodeMsgs_le`, `length_transcriptWith_fst_le`, `_snd_le`.
* `ComposeBound.length_runAt_le`, `Efficient.length_next_le`, `length_ilayout`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §2.1 (non-uniform PPT machines, Definition 26.8) and §4.4 (time complexity of interactive
  machines).
-/

namespace TCSlib.Cryptography.SecureComputation.ComposeBound

open Complexity Turing

/-! ### Lengths of encodings and outputs -/

/-- **A transcript has at most `rounds` messages per party**:
`|(π.transcriptWith P' x y z r).1| ≤ π.rounds(|x|)` (`Compose.exec_eq_map`). -/
theorem length_transcriptWith_fst_le (π : Protocol) (P' : Strategy) (x y z : List Bool)
    (r : π.ExecCoins P' x) : (π.transcriptWith P' x y z r).1.length ≤ π.rounds.eval x.length := by
  rw [Protocol.transcriptWith_eq, Compose.exec_eq_map, List.length_map]
  exact (List.length_filter_le _ _).trans (List.length_range).le

/-- The verifier's half: `|(π.transcriptWith P' x y z r).2| ≤ π.rounds(|x|)`. -/
theorem length_transcriptWith_snd_le (π : Protocol) (P' : Strategy) (x y z : List Bool)
    (r : π.ExecCoins P' x) : (π.transcriptWith P' x y z r).2.length ≤ π.rounds.eval x.length := by
  rw [Protocol.transcriptWith_eq, Compose.exec_eq_map, List.length_map]
  exact (List.length_filter_le _ _).trans (List.length_range).le

/-- **The length of an encoded history**: if every message has at most `c` bits,
`|encodeMsgs l| ≤ |l| (2c + 2)` (`encodeMsgs_eq_flatMap`, `BinArith.length_encWords_le`). -/
theorem length_encodeMsgs_le (l : List (List Bool)) (c : ℕ) (h : ∀ w ∈ l, w.length ≤ c) :
    (Strategy.encodeMsgs l).length ≤ l.length * (2 * c + 2) := by
  rw [ComposeMachines.encodeMsgs_eq_flatMap, ← BinArith.encWords_def]
  exact BinArith.length_encWords_le l c h

/-- **The length of a machine layout**:
`|layout u y α r| = 2(2(2|u| + 2 + |y|) + 2 + |α|) + 2 + |r|`
(`NUPPT.layout_eq`, `length_pairEncode`). -/
theorem length_layout (u y α r : List Bool) :
    (NUPPT.layout u y α r).length = 2 * (2 * (2 * u.length + 2 + y.length) + 2 + α.length) + 2 +
      r.length := by
  rw [NUPPT.layout_eq, length_pairEncode, length_pairEncode, length_pairEncode]

/-- **The output of a machine is polynomially long**:
`|A.runAt n y r| ≤ A.Ct (|layout 1^n y (A.advice n) ⟦r⟧| + 1)^A.ct`
(`NUPPT.output_length_le`, `NUPPT.runAtL_eq_output_layout`). -/
theorem length_runAt_le (A : NUPPT) (n : ℕ) (y : List Bool) (r : A.Coins n) :
    (A.runAt n y r).length ≤ A.Ct * (2 * (2 * (2 * n + 2 + y.length) + 2 +
      (A.advice n).length) + 2 + A.coinLen n + 1) ^ A.ct := by
  have h := A.output_length_le (NUPPT.layout (List.replicate n true) y (A.advice n) (List.ofFn r))
  rw [NUPPT.timeBound_def, length_layout, List.length_replicate, List.length_ofFn] at h
  rw [NUPPT.runAt_eq, NUPPT.runAtL_eq_output_layout]
  exact h

/-- **The next message of an efficient strategy is polynomially long** in the length of its
activation's layout: for some `C, c`, `|S.next x z r hist| ≤ C (|GI.ilayout x z hist r| + 1)^c`
(`ComposeMachines.Efficient.exists_polyTime`, `PolyTimeComputable.output_length_le`). -/
theorem Efficient.length_next_le {S : Strategy} (h : S.Efficient) :
    ∃ C c : ℕ, ∀ x z r hist, (S.next x z r hist).length ≤
      C * ((GI.ilayout x z hist r).length + 1) ^ c := by
  obtain ⟨F, hF, hnext⟩ := ComposeMachines.Efficient.exists_polyTime h
  obtain ⟨C, c, hC⟩ := hF.output_length_le
  exact ⟨C, c, fun x z r hist => by rw [hnext]; exact hC _⟩

/-- **The length of a strategy layout**: `|GI.ilayout x z hist r| =
2(2(2|x| + 2 + (2(2|x| + 2 + |z|) + 2 + |encodeMsgs hist|)) + 2) + 2 + |r|`. -/
theorem length_ilayout (x z : List Bool) (hist : List (List Bool)) (r : List Bool) :
    (GI.ilayout x z hist r).length =
      2 * (2 * (2 * x.length + 2 + (2 * (2 * x.length + 2 + z.length) + 2 +
        (Strategy.encodeMsgs hist).length)) + 2) + 2 + r.length := by
  rw [GI.ilayout_def, length_layout, List.length_replicate, length_pairEncode, length_pairEncode,
    List.length_nil, Nat.add_zero]

end TCSlib.Cryptography.SecureComputation.ComposeBound

## ===== TCSlib/Cryptography/SecureComputation/ComposeSecurity/Chain.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Probability
import TCSlib.Cryptography.Pseudorandom.Indistinguishability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The hybrid argument over the runs

Step 3 of the proof of the composition theorem [Gol04, §7.3.1, proof of Theorem 7.3.3], in a
generic form. A sample is `Φ m V`, built from a seed `m : M` and one word `V j` per run `j < L`.
In the real sample run `j` is `real m j x_j` for an independent seed `x_j : X`; in the simulated
sample it is `sim m j s_j` for an independent `s_j : S`. The hybrid `i` (`hybV`) takes the first
`i` runs simulated and the others real, on the joint seed `(m, (x_j, s_j)_j)`. Neighbouring
hybrids differ in run `i` only, and resampling that run's seeds (`exists_hyb_step`, with the
published `acceptProb_update`) bounds their gap by the gap at fixed other coordinates (`plugV`:
run `i` replaced by a given word). Summing (`abs_sub_le_sum_hybrids`) gives `abs_chain_le`.

## Main definitions

* `ComposeProb.hybV`: the run words of hybrid `i`; `ComposeProb.plugV`: with run `i` replaced.

## Main results

* `ComposeProb.exists_hyb_step`: one step of the hybrid argument.
* `ComposeProb.abs_chain_le`: the real and the simulated samples are within `L · g` when every
  step at fixed other coordinates is within `g`.
* `ComposeProb.getD_plug`: the word list of the reduction's template.

## References

* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
  University Press, 2004, §7.3.1 (the proof of Theorem 7.3.3).
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley, draft of
  22 January 2026, §3.2 (hybrid arguments).
-/

namespace TCSlib.Cryptography.SecureComputation.ComposeProb

open Finset

section Chain

variable {M X S γ ρ : Type*} {L : ℕ}

/-- **The run words of hybrid `i`** on the seed `ω = (m, (x_j, s_j)_j)`: run `j < L` is
`sim m j s_j` for `j < i` and `real m j x_j` otherwise; `[]` for `j ≥ L`. -/
def hybV (real : M → Fin L → X → List Bool) (sim : M → Fin L → S → List Bool) (i : ℕ)
    (ω : M × (Fin L → X × S)) (j : ℕ) : List Bool :=
  if h : j < L then
    (if j < i then sim ω.1 ⟨j, h⟩ (ω.2 ⟨j, h⟩).2 else real ω.1 ⟨j, h⟩ (ω.2 ⟨j, h⟩).1)
  else []

/-- The defining equation of `hybV` (see `hybV`).
`hybV real sim i ω j = if h : j < L then (if j < i then sim ω.1 ⟨j, h⟩ (ω.2 ⟨j, h⟩).2 else real ω.1
⟨j, h⟩ (ω.2 ⟨j, h⟩).1) else []`. -/
theorem hybV_eq (real : M → Fin L → X → List Bool) (sim : M → Fin L → S → List Bool) (i : ℕ)
    (ω : M × (Fin L → X × S)) (j : ℕ) :
    hybV real sim i ω j =
      if h : j < L then
        (if j < i then sim ω.1 ⟨j, h⟩ (ω.2 ⟨j, h⟩).2 else real ω.1 ⟨j, h⟩ (ω.2 ⟨j, h⟩).1)
      else [] := rfl

/-- **Hybrid `i` with run `i` replaced by the word `v`**: `plugV real sim i a v j = v` for
`j = i` and `hybV real sim i a j` otherwise. -/
def plugV (real : M → Fin L → X → List Bool) (sim : M → Fin L → S → List Bool) (i : ℕ)
    (a : M × (Fin L → X × S)) (v : List Bool) (j : ℕ) : List Bool :=
  if j = i then v else hybV real sim i a j

/-- The defining equation of `plugV` (see `plugV`).
`plugV real sim i a v j = if j = i then v else hybV real sim i a j`. -/
theorem plugV_eq (real : M → Fin L → X → List Bool) (sim : M → Fin L → S → List Bool) (i : ℕ)
    (a : M × (Fin L → X × S)) (v : List Bool) (j : ℕ) :
    plugV real sim i a v j = if j = i then v else hybV real sim i a j := rfl

/-- Hybrid `i` with run `i` reseeded by `(x, s)` has the real run `i` on `x`:
`hybV i (m, update u i (x, s)) = plugV i (m, u) (real m i x)`. -/
theorem hybV_update (real : M → Fin L → X → List Bool) (sim : M → Fin L → S → List Bool)
    (i : Fin L) (m : M) (u : Fin L → X × S) (y : X × S) :
    hybV real sim i (m, Function.update u i y) = plugV real sim i (m, u) (real m i y.1) := by
  funext j
  rw [hybV_eq, plugV_eq, hybV_eq]
  by_cases hji : j = i
  · subst hji
    rw [dif_pos i.2, if_neg (lt_irrefl _), if_pos rfl]
    simp only [Fin.eta, Function.update_self]
  · rw [if_neg hji]
    by_cases hj : j < L
    · have hne : (⟨j, hj⟩ : Fin L) ≠ i := fun h => hji (congrArg Fin.val h)
      rw [dif_pos hj, dif_pos hj]
      simp only [Function.update_of_ne hne]
    · rw [dif_neg hj, dif_neg hj]

/-- Hybrid `i + 1` with run `i` reseeded by `(x, s)` has the simulated run `i` on `s`:
`hybV (i + 1) (m, update u i (x, s)) = plugV i (m, u) (sim m i s)`. -/
theorem hybV_succ_update (real : M → Fin L → X → List Bool) (sim : M → Fin L → S → List Bool)
    (i : Fin L) (m : M) (u : Fin L → X × S) (y : X × S) :
    hybV real sim ((i : ℕ) + 1) (m, Function.update u i y) =
      plugV real sim i (m, u) (sim m i y.2) := by
  funext j
  rw [hybV_eq, plugV_eq, hybV_eq]
  by_cases hji : j = i
  · subst hji
    rw [dif_pos i.2, if_pos (Nat.lt_succ_self _), if_pos rfl]
    simp only [Fin.eta, Function.update_self]
  · rw [if_neg hji]
    by_cases hj : j < L
    · have hne : (⟨j, hj⟩ : Fin L) ≠ i := fun h => hji (congrArg Fin.val h)
      have hlt : j < (i : ℕ) + 1 ↔ j < i := by omega
      rw [dif_pos hj, dif_pos hj]
      simp only [Function.update_of_ne hne, hlt]
    · rw [dif_neg hj, dif_neg hj]

variable [Fintype M] [Fintype X] [Fintype S] [Fintype ρ]

variable [Nonempty M] [Nonempty X] [Nonempty S]

/-- **One step of the hybrid argument**: for `i < L` there are fixed other coordinates `a` such
that the gap between hybrids `i` and `i + 1` is at most the gap between run `i` real and run `i`
simulated, the others as in `a`:
`|Pr[D(Φ(hyb i))] − Pr[D(Φ(hyb (i+1)))]| ≤
|Pr_x[D(Φ a.1 (plugV i a (real a.1 i x)))] − Pr_s[D(Φ a.1 (plugV i a (sim a.1 i s)))]|`.

**Proof sketch.** Overwrite run `i`'s seeds with a fresh `y : X × S` (`acceptProb_update`, after
moving `m` last and the fresh seed last, `acceptProb_comp_equiv`): hybrid `k` becomes
`hyb k (m, update u i y)`, which for `k = i` is the plugged real run on `y.1` and for `k = i + 1`
the plugged simulated run on `y.2` (`hybV_update`, `hybV_succ_update`). Fix the coordinates
`(u, m)` at the worst value (`exists_abs_sub_le_sections`) and drop the unused half of `y`
(`acceptProb_fst`, `acceptProb_snd`). -/
theorem exists_hyb_step (real : M → Fin L → X → List Bool) (sim : M → Fin L → S → List Bool)
    (Φ : M → (ℕ → List Bool) → γ) (D : γ → ρ → Bool) (i : Fin L) :
    ∃ a : M × (Fin L → X × S),
      |acceptProb (fun ω => Φ ω.1 (hybV real sim i ω)) D -
          acceptProb (fun ω => Φ ω.1 (hybV real sim ((i : ℕ) + 1) ω)) D| ≤
        |acceptProb (fun x => Φ a.1 (plugV real sim i a (real a.1 i x))) D -
          acceptProb (fun s => Φ a.1 (plugV real sim i a (sim a.1 i s))) D| := by
  classical
  -- overwrite run `i`'s seeds with a fresh seed; the fixed coordinates `(u, m)` come first
  have hk : ∀ k : ℕ, acceptProb (fun ω => Φ ω.1 (hybV real sim k ω)) D =
      acceptProb (fun w : ((Fin L → X × S) × M) × (X × S) =>
        Φ w.1.2 (hybV real sim k (w.1.2, Function.update w.1.1 i w.2))) D := by
    intro k
    refine (acceptProb_comp_equiv (Equiv.prodComm (Fin L → X × S) M)
      (fun ω : M × (Fin L → X × S) => Φ ω.1 (hybV real sim k ω)) D).symm.trans ?_
    refine (acceptProb_update i (fun u m => Φ m (hybV real sim k (m, u))) D).symm.trans ?_
    exact (acceptProb_comp_equiv (Equiv.prodComm ((Fin L → X × S) × M) (X × S)) _ D).symm
  rw [hk i, hk ((i : ℕ) + 1)]
  obtain ⟨a, ha⟩ := exists_abs_sub_le_sections
    (fun w : ((Fin L → X × S) × M) × (X × S) =>
      Φ w.1.2 (hybV real sim i (w.1.2, Function.update w.1.1 i w.2)))
    (fun w : ((Fin L → X × S) × M) × (X × S) =>
      Φ w.1.2 (hybV real sim ((i : ℕ) + 1) (w.1.2, Function.update w.1.1 i w.2))) D
  refine ⟨(a.2, a.1), ha.trans (le_of_eq ?_)⟩
  simp only [hybV_update, hybV_succ_update]
  rw [acceptProb_fst (fun x => Φ a.2 (plugV real sim i (a.2, a.1) (real a.2 i x))) D,
    acceptProb_snd (fun s => Φ a.2 (plugV real sim i (a.2, a.1) (sim a.2 i s))) D]

omit [Nonempty M] [Nonempty X] in
/-- Hybrid `0` is the real sample, the simulator seeds unused:
`Pr[D(Φ(hyb 0))] = Pr_{(m, x)}[D(Φ m (real runs on x))]`. -/
theorem acceptProb_hyb_zero (real : M → Fin L → X → List Bool) (sim : M → Fin L → S → List Bool)
    (Φ : M → (ℕ → List Bool) → γ) (D : γ → ρ → Bool) :
    acceptProb (fun ω => Φ ω.1 (hybV real sim 0 ω)) D =
      acceptProb (fun z : M × (Fin L → X) =>
        Φ z.1 fun j => if h : j < L then real z.1 ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) D := by
  let e : M × (Fin L → X × S) ≃ (M × (Fin L → X)) × (Fin L → S) :=
    { toFun := fun ω => ((ω.1, fun j => (ω.2 j).1), fun j => (ω.2 j).2)
      invFun := fun z => (z.1.1, fun j => (z.1.2 j, z.2 j))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← acceptProb_fst (τ := Fin L → S) (fun z : M × (Fin L → X) =>
      Φ z.1 fun j => if h : j < L then real z.1 ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) D,
    ← acceptProb_comp_equiv e]
  congr 1

omit [Nonempty M] [Nonempty S] in
/-- Hybrid `L` is the simulated sample, the real seeds unused:
`Pr[D(Φ(hyb L))] = Pr_{(m, s)}[D(Φ m (simulated runs on s))]`.

**Proof sketch.** Relabel the seed `(m, (x_j, s_j)_j)` as `((m, s), x)` (an equivalence,
`acceptProb_comp_equiv`) and drop the unused `x` (`acceptProb_fst`); in hybrid `L` every
run `j < L` is simulated (`hybV_eq`). -/
theorem acceptProb_hyb_last (real : M → Fin L → X → List Bool) (sim : M → Fin L → S → List Bool)
    (Φ : M → (ℕ → List Bool) → γ) (D : γ → ρ → Bool) :
    acceptProb (fun ω => Φ ω.1 (hybV real sim L ω)) D =
      acceptProb (fun z : M × (Fin L → S) =>
        Φ z.1 fun j => if h : j < L then sim z.1 ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) D := by
  let e : M × (Fin L → X × S) ≃ (M × (Fin L → S)) × (Fin L → X) :=
    { toFun := fun ω => ((ω.1, fun j => (ω.2 j).2), fun j => (ω.2 j).1)
      invFun := fun z => (z.1.1, fun j => (z.2 j, z.1.2 j))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← acceptProb_fst (τ := Fin L → X) (fun z : M × (Fin L → S) =>
      Φ z.1 fun j => if h : j < L then sim z.1 ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) D,
    ← acceptProb_comp_equiv e]
  congr 1
  funext ω
  congr 1
  funext j
  rw [hybV_eq]
  by_cases h : j < L
  · rw [dif_pos h, dif_pos h, if_pos h]
    rfl
  · rw [dif_neg h, dif_neg h]

/-- **The hybrid argument over the runs**: if for every run `i < L` and all fixed other
coordinates `a` the plugged real and simulated runs are within `g`, then the real sample and the
simulated sample are within `L · g`:
`|Pr_{(m, x)}[D(Φ m (real runs))] − Pr_{(m, s)}[D(Φ m (simulated runs))]| ≤ L · g`.

**Proof sketch.** The two samples are hybrids `0` and `L` (`acceptProb_hyb_zero`,
`acceptProb_hyb_last`); telescope (`abs_sub_le_sum_hybrids`) and bound each of the `L` steps by
`g` (`exists_hyb_step`). -/
theorem abs_chain_le (real : M → Fin L → X → List Bool) (sim : M → Fin L → S → List Bool)
    (Φ : M → (ℕ → List Bool) → γ) (D : γ → ρ → Bool) (g : ℝ)
    (hg : ∀ (i : Fin L) (a : M × (Fin L → X × S)),
      |acceptProb (fun x => Φ a.1 (plugV real sim i a (real a.1 i x))) D -
        acceptProb (fun s => Φ a.1 (plugV real sim i a (sim a.1 i s))) D| ≤ g) :
    |acceptProb (fun z : M × (Fin L → X) =>
        Φ z.1 fun j => if h : j < L then real z.1 ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) D -
      acceptProb (fun z : M × (Fin L → S) =>
        Φ z.1 fun j => if h : j < L then sim z.1 ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) D| ≤ L * g := by
  have h0 := acceptProb_hyb_zero real sim Φ D
  have hL := acceptProb_hyb_last real sim Φ D
  rw [← h0, ← hL]
  have htel := abs_sub_le_sum_hybrids
    (fun k => acceptProb (fun ω => Φ ω.1 (hybV real sim k ω)) D) L
  have hsum : ∑ k ∈ range L, |acceptProb (fun ω => Φ ω.1 (hybV real sim k ω)) D -
      acceptProb (fun ω => Φ ω.1 (hybV real sim (k + 1) ω)) D| ≤ ∑ _k ∈ range L, g :=
    sum_le_sum fun k hk => by
      obtain ⟨a, ha⟩ := exists_hyb_step real sim Φ D ⟨k, mem_range.1 hk⟩
      exact ha.trans (hg _ a)
  refine htel.trans (hsum.trans (le_of_eq ?_))
  rw [sum_const, card_range, nsmul_eq_mul]

end Chain

/-- **The template's word list**: for `i < L` and `j < L`, entry `j` of
`[f 0, …, f (i−1), v, f (i+1), …, f (L−1)]` is `v` for `j = i` and `f j` otherwise. -/
theorem getD_plug (f : ℕ → List Bool) (v : List Bool) {i L j : ℕ} (hi : i < L) (hj : j < L) :
    ((List.range i).map f ++ v :: (List.range (L - (i + 1))).map fun k => f (i + 1 + k)).getD j
        [] = if j = i then v else f j := by
  rw [List.getD_eq_getElem?_getD]
  rcases lt_trichotomy j i with h | h | h
  · rw [List.getElem?_append_left (by rw [List.length_map, List.length_range]; exact h),
      List.getElem?_map, List.getElem?_range h, Option.map_some, Option.getD_some,
      if_neg (Nat.ne_of_lt h)]
  · subst h
    rw [List.getElem?_append_right (by rw [List.length_map, List.length_range]),
      List.length_map, List.length_range, Nat.sub_self, List.getElem?_cons_zero,
      Option.getD_some, if_pos rfl]
  · obtain ⟨k, rfl⟩ : ∃ k, j = i + 1 + k := ⟨j - (i + 1), by omega⟩
    rw [List.getElem?_append_right (by rw [List.length_map, List.length_range]; omega),
      List.length_map, List.length_range, show i + 1 + k - i = k + 1 by omega,
      List.getElem?_cons_succ, List.getElem?_map, List.getElem?_range (by omega),
      Option.map_some, Option.getD_some, if_neg (by omega)]

end TCSlib.Cryptography.SecureComputation.ComposeProb

## ===== TCSlib/Cryptography/SecureComputation/ComposeSecurity/Correct.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Accept
import TCSlib.Cryptography.HardcoreBit.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Correct answers of the runs

Step 2 of the proof of the composition theorem [Gol04, §7.3.1, proof of Theorem 7.3.3]. The
output clause of honest-but-curious security makes a secure protocol correct: a distinguisher
that compares the other party's output in the sample with the ideal output on the worst-case
inputs of length `n`, given as advice, shows that each party's output differs from its ideal
output with negligible probability, uniformly over the inputs (`ComposeProb.exists_correct`).
By the union bound over the calls, every run of the composed protocol gives the ideal answers
except with probability `L(n)` times that bound (`HybridProtocol.uprob_not_goodRuns_le`).

## Main results

* `ComposeProb.exists_correct`: a secure protocol computes its functionality except with
  negligible probability.
* `HybridProtocol.inA_val`, `inB_val`: the call inputs at a call index.
* `HybridProtocol.uprob_not_goodRuns_le`: the bad event of the statistical switch.

## References

* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
  University Press, 2004, §7.3.1 (the proof of Theorem 7.3.3).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2, Definition 155.1.
-/

namespace TCSlib.Cryptography.SecureComputation

open Finset Complexity Turing TCSlib.Cryptography

namespace ComposeProb

/-- **A secure protocol computes its functionality** (the output clause of [PS10,
Definition 155.1]): if `ρ` has simulators `S_A`, `S_B` against every non-uniform PPT
distinguisher, there is a negligible `ε_c` with, for all `n` and all inputs `x`, `y` of `G`'s
lengths, `Pr_t[ρ.outP ≠ ⟦f_A(x, y)⟧ ∨ ρ.outV ≠ ⟦f_B(x, y)⟧] ≤ ε_c(n)` on common input `1^n`.

**Proof sketch.** For Alice's output take the inputs `w_n` maximizing
`Pr_t[outP ≠ ⟦f_A⟧]` at each `n`, and the test machine accepting when the second component of
its sample is `⟦f_A(w_n)⟧` (`exists_test`; advice of `G.outA(n)` bits). On Bob's ideal sample
at `w_n` it accepts with probability `1` (the second component is `⟦f_A(w_n)⟧`); on the real one
with `Pr_t[outP = ⟦f_A(w_n)⟧]` (`acceptProb_test`). So `Pr_t[outP ≠ ⟦f_A⟧] ≤
Pr_t[outP(w_n) ≠ ⟦f_A(w_n)⟧] = 1 − Pr_t[outP(w_n) = ⟦f_A(w_n)⟧] ≤ ε_A(n)` (`uprob_not`).
Likewise for Bob's output on Alice's side; take `ε_c = ε_A + ε_B` (`uprob_or_le`). -/
theorem exists_correct {G : Functionality} {ρ : Protocol} (SA SB : NUPPT)
    (hS : ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n (x : Fin (G.inA.eval n) → Bool) (y : Fin (G.inB.eval n) → Bool),
        distAdv (G.realA ρ n x y) (G.idealA SA n x y) (D.distinguisherL n) ≤ ε n ∧
          distAdv (G.realB ρ n x y) (G.idealB SB n x y) (D.distinguisherL n) ≤ ε n) :
    ∃ εc : ℕ → ℝ, Negligible εc ∧
      ∀ n (x : Fin (G.inA.eval n) → Bool) (y : Fin (G.inB.eval n) → Bool),
        uprob (fun t : ρ.ExecCoins ρ.P (List.replicate n true) =>
          ρ.outP (List.replicate n true) (List.ofFn x) (List.ofFn y) t ≠
              List.ofFn (G.f n x y).1 ∨
            ρ.outV ρ.P (List.replicate n true) (List.ofFn x) (List.ofFn y) t ≠
              List.ofFn (G.f n x y).2) ≤ εc n := by
  -- the worst-case inputs for each output
  have hmax : ∀ (n : ℕ) (q : (Fin (G.inA.eval n) → Bool) × (Fin (G.inB.eval n) → Bool) → ℝ),
      ∃ w, ∀ w', q w' ≤ q w := fun n q => by
    obtain ⟨w, -, hw⟩ := exists_max_image univ q univ_nonempty
    exact ⟨w, fun w' => hw w' (mem_univ w')⟩
  choose wA hwA using fun n => hmax n fun w => uprob fun t : ρ.ExecCoins ρ.P
    (List.replicate n true) => ρ.outP (List.replicate n true) (List.ofFn w.1) (List.ofFn w.2) t ≠
      List.ofFn (G.f n w.1 w.2).1
  choose wB hwB using fun n => hmax n fun w => uprob fun t : ρ.ExecCoins ρ.P
    (List.replicate n true) => ρ.outV ρ.P (List.replicate n true) (List.ofFn w.1)
      (List.ofFn w.2) t ≠ List.ofFn (G.f n w.1 w.2).2
  obtain ⟨BA, hBA⟩ := exists_test (fun n => List.ofFn (G.f n (wA n).1 (wA n).2).1) G.outA
    fun n => by rw [List.length_ofFn]
  obtain ⟨BB, hBB⟩ := exists_test (fun n => List.ofFn (G.f n (wB n).1 (wB n).2).2) G.outB
    fun n => by rw [List.length_ofFn]
  obtain ⟨εA, hεA, hA⟩ := hS BA
  obtain ⟨εB, hεB, hB⟩ := hS BB
  refine ⟨fun n => εA n + εB n, hεA.add hεB, fun n x y => (uprob_or_le _ _).trans
    (add_le_add ((hwA n (x, y)).trans ?_) ((hwB n (x, y)).trans ?_))⟩
  · -- Alice's output, through Bob's samples
    have h1 : acceptProb (G.realB ρ n (wA n).1 (wA n).2) (BA.distinguisherL n) =
        uprob fun t : ρ.ExecCoins ρ.P (List.replicate n true) =>
          ρ.outP (List.replicate n true) (List.ofFn (wA n).1) (List.ofFn (wA n).2) t =
            List.ofFn (G.f n (wA n).1 (wA n).2).1 := by
      rw [acceptProb_test _ BA n _ (hBA n)]
      simp only [Functionality.realB_eq, pairSndD_pairEncode, BinArith.eqW_pairEncode,
        decide_eq_true_iff]
    have h2 : acceptProb (G.idealB SB n (wA n).1 (wA n).2) (BA.distinguisherL n) = 1 := by
      rw [acceptProb_test _ BA n _ (hBA n)]
      simp only [Functionality.idealB_eq, pairSndD_pairEncode, BinArith.eqW_pairEncode,
        decide_true]
      exact uprob_true
    have h3 := (hA n (wA n).1 (wA n).2).2
    rw [distAdv_def, h1, h2, abs_le] at h3
    have h4 := uprob_not fun t : ρ.ExecCoins ρ.P (List.replicate n true) =>
      ρ.outP (List.replicate n true) (List.ofFn (wA n).1) (List.ofFn (wA n).2) t =
        List.ofFn (G.f n (wA n).1 (wA n).2).1
    exact (le_of_eq h4).trans (by linarith [h3.1])
  · -- Bob's output, through Alice's samples
    have h1 : acceptProb (G.realA ρ n (wB n).1 (wB n).2) (BB.distinguisherL n) =
        uprob fun t : ρ.ExecCoins ρ.P (List.replicate n true) =>
          ρ.outV ρ.P (List.replicate n true) (List.ofFn (wB n).1) (List.ofFn (wB n).2) t =
            List.ofFn (G.f n (wB n).1 (wB n).2).2 := by
      rw [acceptProb_test _ BB n _ (hBB n)]
      simp only [Functionality.realA_eq, pairSndD_pairEncode, BinArith.eqW_pairEncode,
        decide_eq_true_iff]
    have h2 : acceptProb (G.idealA SA n (wB n).1 (wB n).2) (BB.distinguisherL n) = 1 := by
      rw [acceptProb_test _ BB n _ (hBB n)]
      simp only [Functionality.idealA_eq, pairSndD_pairEncode, BinArith.eqW_pairEncode,
        decide_true]
      exact uprob_true
    have h3 := (hB n (wB n).1 (wB n).2).1
    rw [distAdv_def, h1, h2, abs_le] at h3
    have h4 := uprob_not fun t : ρ.ExecCoins ρ.P (List.replicate n true) =>
      ρ.outV ρ.P (List.replicate n true) (List.ofFn (wB n).1) (List.ofFn (wB n).2) t =
        List.ofFn (G.f n (wB n).1 (wB n).2).2
    exact (le_of_eq h4).trans (by linarith [h3.1])

end ComposeProb

namespace HybridProtocol

variable {G : Functionality} (H : HybridProtocol G) (ρ : Protocol)

/-- Alice's input to a call `j : Fin calls(n)` is `⟦callA(n, zA, rA, j)⟧` (`inA_eq`).
`H.inA n zA rA j = List.ofFn (H.callA n zA rA j)`. -/
theorem inA_val (n : ℕ) (zA rA : List Bool) (j : Fin (H.calls.eval n)) :
    H.inA n zA rA j = List.ofFn (H.callA n zA rA j) := by
  rw [inA_eq, dif_pos j.2]

/-- Bob's input to a call `j : Fin calls(n)` is `⟦callB(n, zB, rB, j)⟧` (`inB_eq`).
`H.inB n zB rB j = List.ofFn (H.callB n zB rB j)`. -/
theorem inB_val (n : ℕ) (zB rB : List Bool) (j : Fin (H.calls.eval n)) :
    H.inB n zB rB j = List.ofFn (H.callB n zB rB j) := by
  rw [inB_eq, dif_pos j.2]

/-- **The bad event of the statistical switch**: if on common input `1^n` every pair of inputs of
`G`'s lengths makes a party's `ρ`-output wrong with probability at most `ε_c`, then over the
`main`-tapes and the run tapes some run gives a wrong answer with probability at most
`calls(n) · ε_c`.
`uprob (fun z : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) => ¬
H.GoodRuns ρ n zA zB z.1 z.2) ≤ H.calls.eval n * εc`.

**Proof sketch.** `¬ GoodRuns` is the union over the calls `j` of the event that run `j`'s
outputs are wrong (`goodRuns_iff`; `uprob_exists_le`). For fixed `main`-tapes `m` that event
concerns the run tapes `t j` only, on the call inputs of `m`, which have `G`'s lengths
(`inA_val`, `inB_val`): its probability is at most `ε_c` (`HardcoreBit.pushesUniform_eval`),
hence so is its average over `m` (`uprob_prod`, `HardcoreBit.uexp_mono`,
`HardcoreBit.uexp_const`). -/
theorem uprob_not_goodRuns_le (n : ℕ) (zA zB : List Bool) (εc : ℝ)
    (hc : ∀ (xA : Fin (G.inA.eval n) → Bool) (yB : Fin (G.inB.eval n) → Bool),
      uprob (fun t : ρ.ExecCoins ρ.P (List.replicate n true) =>
        ρ.outP (List.replicate n true) (List.ofFn xA) (List.ofFn yB) t ≠
            List.ofFn (G.f n xA yB).1 ∨
          ρ.outV ρ.P (List.replicate n true) (List.ofFn xA) (List.ofFn yB) t ≠
            List.ofFn (G.f n xA yB).2) ≤ εc) :
    uprob (fun z : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) =>
      ¬ H.GoodRuns ρ n zA zB z.1 z.2) ≤ H.calls.eval n * εc := by
  -- the event that run `j` is wrong, on the run tape `t'`
  let bad : H.Coins n → Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) → Prop :=
    fun m j t' =>
      ρ.outP (List.replicate n true) (List.ofFn (H.callA n zA (List.ofFn m.1) j))
          (List.ofFn (H.callB n zB (List.ofFn m.2) j)) t' ≠
        List.ofFn (G.f n (H.callA n zA (List.ofFn m.1) j) (H.callB n zB (List.ofFn m.2) j)).1 ∨
      ρ.outV ρ.P (List.replicate n true) (List.ofFn (H.callA n zA (List.ofFn m.1) j))
          (List.ofFn (H.callB n zB (List.ofFn m.2) j)) t' ≠
        List.ofFn (G.f n (H.callA n zA (List.ofFn m.1) j) (H.callB n zB (List.ofFn m.2) j)).2
  have hsub : ∀ z : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)),
      ¬ H.GoodRuns ρ n zA zB z.1 z.2 → ∃ j ∈ (univ : Finset (Fin (H.calls.eval n))),
        bad z.1 j (z.2 j) := by
    intro z hz
    rw [goodRuns_iff] at hz
    push_neg at hz
    obtain ⟨j, hj⟩ := hz
    refine ⟨j, mem_univ j, ?_⟩
    show _ ∨ _
    rw [← H.inA_val n zA (List.ofFn z.1.1) j, ← H.inB_val n zB (List.ofFn z.1.2) j]
    by_cases h : ρ.outP (List.replicate n true) (H.inA n zA (List.ofFn z.1.1) j)
        (H.inB n zB (List.ofFn z.1.2) j) (z.2 j) =
      List.ofFn (G.f n (H.callA n zA (List.ofFn z.1.1) j) (H.callB n zB (List.ofFn z.1.2) j)).1
    · exact Or.inr (hj h)
    · exact Or.inl h
  calc uprob (fun z : H.Coins n × (Fin (H.calls.eval n) →
        ρ.ExecCoins ρ.P (List.replicate n true)) => ¬ H.GoodRuns ρ n zA zB z.1 z.2)
      ≤ uprob (fun z : H.Coins n × (Fin (H.calls.eval n) →
          ρ.ExecCoins ρ.P (List.replicate n true)) => ∃ j ∈ univ, bad z.1 j (z.2 j)) :=
        uprob_mono hsub
    _ ≤ ∑ j ∈ (univ : Finset (Fin (H.calls.eval n))),
          uprob (fun z : H.Coins n × (Fin (H.calls.eval n) →
            ρ.ExecCoins ρ.P (List.replicate n true)) => bad z.1 j (z.2 j)) :=
        uprob_exists_le _ _
    _ ≤ ∑ _j ∈ (univ : Finset (Fin (H.calls.eval n))), εc := sum_le_sum fun j _ => by
        rw [uprob_prod]
        refine (HardcoreBit.uexp_mono fun m => ?_).trans_eq (HardcoreBit.uexp_const (εc))
        rw [(HardcoreBit.pushesUniform_eval j).uprob_eq (bad m j)]
        exact hc _ _
    _ = H.calls.eval n * εc := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

end HybridProtocol

end TCSlib.Cryptography.SecureComputation

## ===== TCSlib/Cryptography/SecureComputation/ComposeSecurity/Efficiency.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Machines

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The composed parties as polynomial-time functions of the machine layout

The efficiency half of the composition theorem [Gol04, §7.3.1, the protocol of Theorem 7.3.3]:
Alice's and Bob's next-message functions in `H.compose ρ` (`HybridProtocol.composeP`,
`composeV`) are polynomial-time functions of the machine layout
`GI.ilayout x z hist r = ⟨⟨⟨1^{|x|}, ⟨⟨x, z⟩, encodeMsgs hist⟩⟩, []⟩, r⟩`, when `main`'s and `ρ`'s
strategies are efficient and the call inputs are polynomial-time (`HybridProtocol.PolyTime`,
`Functionality.PolyTime`).

The pieces are shared by the two parties and generic in the strategies:
* `ComposeMachines.runW`: one activation of a `ρ`-party in run `j` after `p` pairs of the run,
  on the call input (recomputed from the `main`-tape), the run tape cut from the coins and the
  run's messages read from the history at the interleaved pairs (`polyTimeComputable_slots`);
* `ComposeMachines.ansW`: the `L(n)` run outputs, each padded to the answer length, concatenated;
* `ComposeMachines.mainW`: one activation of a `main`-party on its input paired with the answers,
  its `main`-tape and the messages after the runs.

## Main definitions

* `ComposeMachines.runW`, `ansW`, `mainW`, `moverW`: the shared pieces.
* `HybridProtocol.composePW`, `composeVW`: the two parties on the layout.

## Main results

* `ComposeMachines.runW_ilayout`, `ansW_ilayout`, `mainW_ilayout`: the pieces on a layout.
* `ComposeMachines.polyTimeComputable_runW`, `polyTimeComputable_ansW`,
  `polyTimeComputable_mainW`: the pieces are polynomial-time.
* `HybridProtocol.composeP_next_eq_composePW`, `composeV_next_eq_composeVW`: the composed
  parties are the layout functions.
* `HybridProtocol.polyTimeComputable_composePW`, `polyTimeComputable_composeVW`: and these are
  polynomial-time.

## References

* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
  University Press, 2004, §7.3.1 (the composed protocol of Theorem 7.3.3).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §4.4 (interactive machines and their time complexity, pp. 114–116).
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing Complexity.StateLoop TCSlib.Cryptography.EncodingMachines

namespace ComposeMachines

/-! ### The mover test -/

/-- **The mover test in unary**: `moverW vF b w = [moverIsV vF |fst w| = b]` (whether the
party moving at position `|fst w|` of `ρ` is the verifier, compared with `b`). -/
def moverW (vF b : Bool) (w : List Bool) : List Bool :=
  [moverIsV vF (pairFstD w).length == b]

/-- The defining equation of `moverW`: `moverW vF b w = [moverIsV vF |fst w| == b]`. -/
theorem moverW_eq (vF b : Bool) (w : List Bool) :
    moverW vF b w = [moverIsV vF (pairFstD w).length == b] := rfl

/-- The mover test is polynomial-time: the parity of the unary length `|fst w|`
(`EncodingMachines.modNum_poly`, `eqTest_poly`), compared with constants
(`Complexity.polyTimeComputable_ite`).
`PolyTimeComputable (moverW vF b)`. -/
theorem polyTimeComputable_moverW (vF b : Bool) : PolyTimeComputable (moverW vF b) := by
  have hpar : PolyTimeComputable fun w =>
      [decide (modNum (pairFstD w).length 2 = (if vF then 0 else 1))] :=
    eqTest_poly (modNum_poly (unaryLength_poly polyTimeComputable_pairFstD) (unaryConst_poly 2))
      (unaryConst_poly _)
  have h := polyTimeComputable_ite hpar (polyTimeComputable_const [b])
    (polyTimeComputable_const [!b])
  refine h.congr fun w => ?_
  rw [moverW_eq, moverIsV_def, modNum_eq]
  rcases Nat.mod_two_eq_zero_or_one (pairFstD w).length with hp | hp <;>
    cases vF <;> cases b <;> simp [hp]

/-! ### One activation of a `ρ`-party in a run -/

/-- **One `ρ`-activation in run `j` after `p` pairs of the run**, on the word
`u = ⟨1^j, ⟨1^p, w⟩⟩` with `w` a layout (common input `x`, input `z`, messages `M`, coins `r`,
`n = |x|`): the `ρ`-party's machine `Fρ` on the layout with common input `x`, input
`fcall ⟨1^n, ⟨z, ⟨r_{<c₀(n)}, 1^j⟩⟩⟩` (the call input from the `main`-tape), the messages
of the run read at the pairs `R(n)·j + q`, `q < p`, selected by `moverIsV vF q = b`, and the run
tape `r[c₀(n) + j·c(n), c₀(n) + (j + 1)·c(n))`. -/
def runW (Fρ fcall : List Bool → List Bool) (c₀ c R : PolyExpr) (vF b : Bool)
    (u : List Bool) : List Bool :=
  Fρ (NUPPT.layout (List.replicate (GI.argX (pairSndD (pairSndD u))).length true)
    (pairEncode (pairEncode (GI.argX (pairSndD (pairSndD u)))
        (fcall (pairEncode (List.replicate (GI.argX (pairSndD (pairSndD u))).length true)
          (pairEncode (GI.argZ (pairSndD (pairSndD u)))
            (pairEncode ((NUPPT.inCoins (pairSndD (pairSndD u))).take
                (c₀.eval (GI.argX (pairSndD (pairSndD u))).length))
              (List.replicate (pairFstD u).length true))))))
      ((List.range (pairFstD (pairSndD u)).length).flatMap fun q =>
        if moverIsV vF q == b then
          pairEncode (pairFstD (pairSndD^[R.eval (GI.argX (pairSndD (pairSndD u))).length *
            (pairFstD u).length + q] (GI.argM (pairSndD (pairSndD u))))) []
        else []))
    []
    (((NUPPT.inCoins (pairSndD (pairSndD u))).drop
        (c₀.eval (GI.argX (pairSndD (pairSndD u))).length +
          (pairFstD u).length * c.eval (GI.argX (pairSndD (pairSndD u))).length)).take
      (c.eval (GI.argX (pairSndD (pairSndD u))).length)))

/-- The defining equation of `runW` (see `runW`).
`runW Fρ fcall c₀ c R vF b u = Fρ (NUPPT.layout (List.replicate (GI.argX (pairSndD (pairSndD
u))).length true) (pairEncode (pairEncode (GI.argX (pairSndD (pairSndD u))) (fcall (pairEncode
(List.replicate (GI.argX (pairSndD (pairSndD …`. -/
theorem runW_eq (Fρ fcall : List Bool → List Bool) (c₀ c R : PolyExpr) (vF b : Bool)
    (u : List Bool) :
    runW Fρ fcall c₀ c R vF b u =
      Fρ (NUPPT.layout (List.replicate (GI.argX (pairSndD (pairSndD u))).length true)
        (pairEncode (pairEncode (GI.argX (pairSndD (pairSndD u)))
            (fcall (pairEncode (List.replicate (GI.argX (pairSndD (pairSndD u))).length true)
              (pairEncode (GI.argZ (pairSndD (pairSndD u)))
                (pairEncode ((NUPPT.inCoins (pairSndD (pairSndD u))).take
                    (c₀.eval (GI.argX (pairSndD (pairSndD u))).length))
                  (List.replicate (pairFstD u).length true))))))
          ((List.range (pairFstD (pairSndD u)).length).flatMap fun q =>
            if moverIsV vF q == b then
              pairEncode (pairFstD (pairSndD^[R.eval (GI.argX (pairSndD (pairSndD u))).length *
                (pairFstD u).length + q] (GI.argM (pairSndD (pairSndD u))))) []
            else []))
        []
        (((NUPPT.inCoins (pairSndD (pairSndD u))).drop
            (c₀.eval (GI.argX (pairSndD (pairSndD u))).length +
              (pairFstD u).length * c.eval (GI.argX (pairSndD (pairSndD u))).length)).take
          (c.eval (GI.argX (pairSndD (pairSndD u))).length))) := rfl

/-- **`runW` on a layout**: on `⟨1^j, ⟨1^p, GI.ilayout x z hist r⟩⟩` it is `Fρ` on the layout of
the run activation: `runW … ⟨1^j, ⟨1^p, GI.ilayout x z hist r⟩⟩ =
Fρ (GI.ilayout x (fcall ⟨1^{|x|}, ⟨z, ⟨r_{<c₀}, 1^j⟩⟩⟩) (slotMsgs sel (R·j) p hist)
(runTape c₀ c j r))` with `sel q = (moverIsV vF q == b)` (`encodeMsgs_slotMsgs`). -/
theorem runW_ilayout (Fρ fcall : List Bool → List Bool) (c₀ c R : PolyExpr) (vF b : Bool)
    (x z : List Bool) (hist : List (List Bool)) (r : List Bool) (j p : ℕ) :
    runW Fρ fcall c₀ c R vF b (pairEncode (List.replicate j true)
        (pairEncode (List.replicate p true) (GI.ilayout x z hist r))) =
      Fρ (GI.ilayout x (fcall (pairEncode (List.replicate x.length true)
          (pairEncode z (pairEncode (r.take (c₀.eval x.length)) (List.replicate j true)))))
        (Compose.slotMsgs (fun q => moverIsV vF q == b) (R.eval x.length * j) p hist)
        (Compose.runTape (c₀.eval x.length) (c.eval x.length) j r)) := by
  rw [runW_eq, pairSndD_pairEncode, pairSndD_pairEncode, pairFstD_pairEncode,
    pairFstD_pairEncode, List.length_replicate, List.length_replicate, GI.argX_ilayout,
    GI.argZ_ilayout, GI.argM_ilayout, GI.inCoins_ilayout, GI.ilayout_def, encodeMsgs_slotMsgs,
    Compose.runTape_eq]

/-- **`runW` is polynomial-time** when `Fρ` and `fcall` are.
`PolyTimeComputable (runW Fρ fcall c₀ c R vF b)`.

**Proof sketch.** The layout is assembled (`NUPPT.polyTimeComputable_layout`) from the slot
projections, the unary polynomials `c₀(n)`, `c(n)`, `R(n)` (`unaryPoly_comp`), the call input
(`fcall` after `pairEncode`), the typed cuts of the coins (`EncodingMachines.truncate_poly`,
`Complexity.polyTimeComputable_pairDropPoly` at the unary count `c₀(n) + j·c(n)`) and the
interleaved-slot map at the offset `R(n)·j` (`polyTimeComputable_slots`). -/
theorem polyTimeComputable_runW {Fρ fcall : List Bool → List Bool} (hFρ : PolyTimeComputable Fρ)
    (hcall : PolyTimeComputable fcall) (c₀ c R : PolyExpr) (vF b : Bool) :
    PolyTimeComputable (runW Fρ fcall c₀ c R vF b) := by
  have hw : PolyTimeComputable fun u => pairSndD (pairSndD u) :=
    polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD
  have hx := GI.argX_poly.comp' hw
  have hn : PolyTimeComputable fun u =>
      List.replicate (GI.argX (pairSndD (pairSndD u))).length true := unaryLength_poly hx
  have hj : PolyTimeComputable fun u => List.replicate (pairFstD u).length true :=
    unaryLength_poly polyTimeComputable_pairFstD
  have hp : PolyTimeComputable fun u => List.replicate (pairFstD (pairSndD u)).length true :=
    unaryLength_poly (polyTimeComputable_pairFstD.comp' polyTimeComputable_pairSndD)
  have hr := NUPPT.polyTimeComputable_inCoins.comp' hw
  have hc₀ := unaryPoly_comp c₀ hx
  have hc := unaryPoly_comp c hx
  have hR := unaryPoly_comp R hx
  have hinp : PolyTimeComputable fun u => fcall (pairEncode
      (List.replicate (GI.argX (pairSndD (pairSndD u))).length true)
      (pairEncode (GI.argZ (pairSndD (pairSndD u)))
        (pairEncode ((NUPPT.inCoins (pairSndD (pairSndD u))).take
            (c₀.eval (GI.argX (pairSndD (pairSndD u))).length))
          (List.replicate (pairFstD u).length true)))) :=
    hcall.comp' (hn.pairEncode ((GI.argZ_poly.comp' hw).pairEncode
      ((truncate_poly hr hc₀).pairEncode hj)))
  have hsel : PolyTimeComputable fun w' => [moverIsV vF (pairFstD w').length == b] :=
    (polyTimeComputable_moverW vF b).congr fun w' => moverW_eq vF b w'
  have hslots := polyTimeComputable_slots (sel := fun _ q => moverIsV vF q == b)
    (off := fun u => R.eval (GI.argX (pairSndD (pairSndD u))).length * (pairFstD u).length)
    (p := fun u => (pairFstD (pairSndD u)).length)
    hsel
    (unaryMul_poly hR hj) hp (GI.argM_poly.comp' hw)
  have hdrop : PolyTimeComputable fun u => (NUPPT.inCoins (pairSndD (pairSndD u))).drop
      (c₀.eval (GI.argX (pairSndD (pairSndD u))).length +
        (pairFstD u).length * c.eval (GI.argX (pairSndD (pairSndD u))).length) :=
    ((polyTimeComputable_pairDropPoly .var).comp'
      ((unaryAdd_poly hc₀ (unaryMul_poly hj hc)).pairEncode hr)).congr fun u => by
        rw [pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var,
          List.length_replicate]
  exact (hFρ.comp' (NUPPT.polyTimeComputable_layout hn ((hx.pairEncode hinp).pairEncode hslots)
    (polyTimeComputable_const []) (truncate_poly hdrop hc))).congr fun u => by
      rw [runW_eq]

/-! ### The answers -/

/-- **The answers on the layout**: the `L(n)` run outputs of the `ρ`-party (`runW` with
`p = R(n)`), each padded to `out(n)` bits, concatenated:
`ansW … w = (range L(n)).flatMap fun j => padTo out(n) (runW … ⟨1^j, ⟨1^{R(n)}, w⟩⟩)`. -/
def ansW (Fρ fcall : List Bool → List Bool) (c₀ c R L out : PolyExpr) (vF b : Bool)
    (w : List Bool) : List Bool :=
  (List.range (L.eval (GI.argX w).length)).flatMap fun j =>
    padTo (out.eval (GI.argX w).length) (runW Fρ fcall c₀ c R vF b
      (pairEncode (List.replicate j true)
        (pairEncode (List.replicate (R.eval (GI.argX w).length) true) w)))

/-- The defining equation of `ansW` (see `ansW`).
`ansW Fρ fcall c₀ c R L out vF b w = (List.range (L.eval (GI.argX w).length)).flatMap fun j => padTo
(out.eval (GI.argX w).length) (runW Fρ fcall c₀ c R vF b (pairEncode (List.replicate j true)
(pairEncode (List.replicate (R.eval (GI.argX …`. -/
theorem ansW_eq (Fρ fcall : List Bool → List Bool) (c₀ c R L out : PolyExpr) (vF b : Bool)
    (w : List Bool) :
    ansW Fρ fcall c₀ c R L out vF b w =
      (List.range (L.eval (GI.argX w).length)).flatMap fun j =>
        padTo (out.eval (GI.argX w).length) (runW Fρ fcall c₀ c R vF b
          (pairEncode (List.replicate j true)
            (pairEncode (List.replicate (R.eval (GI.argX w).length) true) w))) := rfl

/-- **The answers are polynomial-time** (`polyTimeComputable_flatMap_range` over the unary count
`L(n)`, with the chunk `padTo_poly` of `polyTimeComputable_runW`).
`PolyTimeComputable (ansW Fρ fcall c₀ c R L out vF b)`. -/
theorem polyTimeComputable_ansW {Fρ fcall : List Bool → List Bool} (hFρ : PolyTimeComputable Fρ)
    (hcall : PolyTimeComputable fcall) (c₀ c R L out : PolyExpr) (vF b : Bool) :
    PolyTimeComputable (ansW Fρ fcall c₀ c R L out vF b) := by
  have hw := polyTimeComputable_pairSndD
  have hx := GI.argX_poly.comp' hw
  have hchunk : PolyTimeComputable fun v =>
      padTo (out.eval (GI.argX (pairSndD v)).length) (runW Fρ fcall c₀ c R vF b
        (pairEncode (List.replicate (pairFstD v).length true)
          (pairEncode (List.replicate (R.eval (GI.argX (pairSndD v)).length) true)
            (pairSndD v)))) :=
    padTo_poly ((polyTimeComputable_runW hFρ hcall c₀ c R vF b).comp
      ((unaryLength_poly polyTimeComputable_pairFstD).pairEncode
        ((unaryPoly_comp R hx).pairEncode hw))) (unaryPoly_comp out hx)
  exact (polyTimeComputable_flatMap_range hchunk (unaryPoly_comp L GI.argX_poly)).congr
    fun w => rfl

/-! ### One activation of a `main`-party -/

/-- **One `main`-activation on the layout**: the `main`-party's machine `Fm` on the layout with
common input `x`, input `⟨z, ans w⟩`, the messages after the first `d w` (`pairSndD^[d w] M`)
and the `main`-tape `r_{<c₀(n)}`. -/
def mainW (Fm ans : List Bool → List Bool) (d : List Bool → ℕ) (c₀ : PolyExpr) (w : List Bool) :
    List Bool :=
  Fm (NUPPT.layout (List.replicate (GI.argX w).length true)
    (pairEncode (pairEncode (GI.argX w) (pairEncode (GI.argZ w) (ans w)))
      (pairSndD^[d w] (GI.argM w)))
    [] ((NUPPT.inCoins w).take (c₀.eval (GI.argX w).length)))

/-- The defining equation of `mainW` (see `mainW`).
`mainW Fm ans d c₀ w = Fm (NUPPT.layout (List.replicate (GI.argX w).length true) (pairEncode
(pairEncode (GI.argX w) (pairEncode (GI.argZ w) (ans w))) (pairSndD^[d w] (GI.argM w))) []
((NUPPT.inCoins w).take (c₀.eval (GI.argX w).length)))`. -/
theorem mainW_eq (Fm ans : List Bool → List Bool) (d : List Bool → ℕ) (c₀ : PolyExpr)
    (w : List Bool) :
    mainW Fm ans d c₀ w =
      Fm (NUPPT.layout (List.replicate (GI.argX w).length true)
        (pairEncode (pairEncode (GI.argX w) (pairEncode (GI.argZ w) (ans w)))
          (pairSndD^[d w] (GI.argM w)))
        [] ((NUPPT.inCoins w).take (c₀.eval (GI.argX w).length))) := rfl

/-- **`mainW` on a layout**: `mainW Fm ans d c₀ (GI.ilayout x z hist r) =
Fm (GI.ilayout x ⟨z, ans (GI.ilayout x z hist r)⟩ (hist.drop (d …)) r_{<c₀})`
(`GI.iterate_pairSndD_encodeMsgs`). -/
theorem mainW_ilayout (Fm ans : List Bool → List Bool) (d : List Bool → ℕ) (c₀ : PolyExpr)
    (x z : List Bool) (hist : List (List Bool)) (r : List Bool) :
    mainW Fm ans d c₀ (GI.ilayout x z hist r) =
      Fm (GI.ilayout x (pairEncode z (ans (GI.ilayout x z hist r)))
        (hist.drop (d (GI.ilayout x z hist r))) (r.take (c₀.eval x.length))) := by
  rw [mainW_eq, GI.argX_ilayout, GI.argZ_ilayout, GI.argM_ilayout, GI.inCoins_ilayout,
    GI.iterate_pairSndD_encodeMsgs, GI.ilayout_def, GI.ilayout_def]

/-- **`mainW` is polynomial-time** when `Fm`, the answers and the unary drop count are
(`iterSnd_poly`, `EncodingMachines.truncate_poly`).
`PolyTimeComputable (mainW Fm ans d c₀)`. -/
theorem polyTimeComputable_mainW {Fm ans : List Bool → List Bool} (hFm : PolyTimeComputable Fm)
    (hans : PolyTimeComputable ans) {d : List Bool → ℕ}
    (hd : PolyTimeComputable fun w => List.replicate (d w) true) (c₀ : PolyExpr) :
    PolyTimeComputable (mainW Fm ans d c₀) :=
  (hFm.comp' (NUPPT.polyTimeComputable_layout (unaryLength_poly GI.argX_poly)
    ((GI.argX_poly.pairEncode (GI.argZ_poly.pairEncode hans)).pairEncode
      (iterSnd_poly GI.argM_poly hd))
    (polyTimeComputable_const [])
    (truncate_poly NUPPT.polyTimeComputable_inCoins (unaryPoly_comp c₀ GI.argX_poly)))).congr
    fun w => by rw [mainW_eq]


/-- **`ansW` on a layout**: the concatenation over `j < L(|x|)` of the padded run outputs
`padTo out(|x|) (Fρ (GI.ilayout x (fcall ⟨1^{|x|}, ⟨z, ⟨r_{<c₀}, 1^j⟩⟩⟩)
(slotMsgs sel (R·j) R hist) (runTape c₀ c j r)))` (`runW_ilayout`). -/
theorem ansW_ilayout (Fρ fcall : List Bool → List Bool) (c₀ c R L out : PolyExpr) (vF b : Bool)
    (x z : List Bool) (hist : List (List Bool)) (r : List Bool) :
    ansW Fρ fcall c₀ c R L out vF b (GI.ilayout x z hist r) =
      (List.range (L.eval x.length)).flatMap fun j =>
        padTo (out.eval x.length) (Fρ (GI.ilayout x
          (fcall (pairEncode (List.replicate x.length true)
            (pairEncode z (pairEncode (r.take (c₀.eval x.length)) (List.replicate j true)))))
          (Compose.slotMsgs (fun q => moverIsV vF q == b) (R.eval x.length * j)
            (R.eval x.length) hist)
          (Compose.runTape (c₀.eval x.length) (c.eval x.length) j r))) := by
  rw [ansW_eq, GI.argX_ilayout]
  refine List.flatMap_congr fun j _ => ?_
  rw [runW_ilayout]

/-- **A concatenation over `Fin L` as a concatenation over `range L`**:
`(List.ofFn fun j : Fin L => E j).flatten = (List.range L).flatMap E`. -/
theorem flatten_ofFn_eq_flatMap_range (E : ℕ → List Bool) (L : ℕ) :
    (List.ofFn fun j : Fin L => E j).flatten = (List.range L).flatMap E := by
  rw [List.ofFn_eq_map, ← List.map_coe_finRange, List.flatMap_map, List.flatMap_def]

end ComposeMachines

/-! ### The composed parties on the layout -/

namespace HybridProtocol

open ComposeMachines

section Parties

variable {G : Functionality} (H : HybridProtocol G) (ρ : Protocol)

/-- **Alice of `H.compose ρ` on the layout** [Gol04, §7.3.1], given machines `Fρ` for `ρ.P`,
`Fm` for `main.P` and `fcall` for her call inputs: with `k` the number of messages received
(`GI.msgCount`), `n = |x|`, `L = calls(n)`, `R = ρ.rounds(n)`:
- if `k < L·R`: `[]` if `ρ`'s mover `k % R` is Bob, else her `ρ`-move in run `k / R` after
  `k % R` pairs (`runW`, reading Bob's moves);
- else, if `main`'s verifier moves first and `k = L·R`: the leading filler `[]`;
- else her `main`-move on `⟨z, her answers⟩` (`ansW`) and the messages after the first `L·R`
  (`mainW`). -/
def composePW (Fρ Fm fcall : List Bool → List Bool) (w : List Bool) : List Bool :=
  if decide (GI.msgCount (GI.argM w) <
      H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length) then
    if moverIsV ρ.verifierFirst (GI.msgCount (GI.argM w) % ρ.rounds.eval (GI.argX w).length) then []
    else runW Fρ fcall H.main.P.coins ρ.P.coins ρ.rounds ρ.verifierFirst true
      (pairEncode
        (List.replicate (GI.msgCount (GI.argM w) / ρ.rounds.eval (GI.argX w).length) true)
        (pairEncode
          (List.replicate (GI.msgCount (GI.argM w) % ρ.rounds.eval (GI.argX w).length) true) w))
  else if (H.main.verifierFirst && decide (GI.msgCount (GI.argM w) =
      H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length)) then []
  else mainW Fm (ansW Fρ fcall H.main.P.coins ρ.P.coins ρ.rounds H.calls G.outA
      ρ.verifierFirst true)
    (fun w => H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length) H.main.P.coins w

/-- The defining equation of `composePW` (see `composePW`).
`H.composePW ρ Fρ Fm fcall w = if decide (GI.msgCount (GI.argM w) < H.calls.eval (GI.argX w).length
* ρ.rounds.eval (GI.argX w).length) then if moverIsV ρ.verifierFirst (GI.msgCount (GI.argM w) %
ρ.rounds.eval (GI.argX w).length) then [] …`. -/
theorem composePW_eq (Fρ Fm fcall : List Bool → List Bool) (w : List Bool) :
    H.composePW ρ Fρ Fm fcall w =
      if decide (GI.msgCount (GI.argM w) <
          H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length) then
        if moverIsV ρ.verifierFirst (GI.msgCount (GI.argM w) % ρ.rounds.eval (GI.argX w).length)
        then []
        else runW Fρ fcall H.main.P.coins ρ.P.coins ρ.rounds ρ.verifierFirst true
          (pairEncode
            (List.replicate (GI.msgCount (GI.argM w) / ρ.rounds.eval (GI.argX w).length) true)
            (pairEncode
              (List.replicate (GI.msgCount (GI.argM w) % ρ.rounds.eval (GI.argX w).length) true) w))
      else if (H.main.verifierFirst && decide (GI.msgCount (GI.argM w) =
          H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length)) then []
      else mainW Fm (ansW Fρ fcall H.main.P.coins ρ.P.coins ρ.rounds H.calls G.outA
          ρ.verifierFirst true)
        (fun w => H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length)
        H.main.P.coins w := rfl

/-- **Bob of `H.compose ρ` on the layout**, given machines `Fρ` for `ρ.V`, `Fm` for `main.V` and
`fcall` for his call inputs: with `c` the number of messages received and `k = c − 1`:
- if `k < L·R`: his `ρ`-move in run `k / R` after `k % R` pairs if `ρ`'s mover `k % R` is Bob
  (`runW`, reading Alice's moves), else `[]`;
- else his `main`-move on `⟨z, his answers⟩` and the messages after the first `L·R + lead`. -/
def composeVW (Fρ Fm fcall : List Bool → List Bool) (w : List Bool) : List Bool :=
  if decide (GI.msgCount (GI.argM w) - 1 <
      H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length) then
    if moverIsV ρ.verifierFirst ((GI.msgCount (GI.argM w) - 1) % ρ.rounds.eval (GI.argX w).length)
    then runW Fρ fcall H.main.V.coins ρ.V.coins ρ.rounds ρ.verifierFirst false
      (pairEncode
        (List.replicate ((GI.msgCount (GI.argM w) - 1) / ρ.rounds.eval (GI.argX w).length) true)
        (pairEncode
          (List.replicate ((GI.msgCount (GI.argM w) - 1) % ρ.rounds.eval (GI.argX w).length)
            true) w))
    else []
  else mainW Fm (ansW Fρ fcall H.main.V.coins ρ.V.coins ρ.rounds H.calls G.outB
      ρ.verifierFirst false)
    (fun w => H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length + H.lead)
    H.main.V.coins w

/-- The defining equation of `composeVW` (see `composeVW`).
`H.composeVW ρ Fρ Fm fcall w = if decide (GI.msgCount (GI.argM w) - 1 < H.calls.eval (GI.argX
w).length * ρ.rounds.eval (GI.argX w).length) then if moverIsV ρ.verifierFirst ((GI.msgCount
(GI.argM w) - 1) % ρ.rounds.eval (GI.argX w).length) …`. -/
theorem composeVW_eq (Fρ Fm fcall : List Bool → List Bool) (w : List Bool) :
    H.composeVW ρ Fρ Fm fcall w =
      if decide (GI.msgCount (GI.argM w) - 1 <
          H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length) then
        if moverIsV ρ.verifierFirst
          ((GI.msgCount (GI.argM w) - 1) % ρ.rounds.eval (GI.argX w).length)
        then runW Fρ fcall H.main.V.coins ρ.V.coins ρ.rounds ρ.verifierFirst false
          (pairEncode
            (List.replicate ((GI.msgCount (GI.argM w) - 1) / ρ.rounds.eval (GI.argX w).length) true)
            (pairEncode
              (List.replicate ((GI.msgCount (GI.argM w) - 1) % ρ.rounds.eval (GI.argX w).length)
                true) w))
        else []
      else mainW Fm (ansW Fρ fcall H.main.V.coins ρ.V.coins ρ.rounds H.calls G.outB
          ρ.verifierFirst false)
        (fun w => H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length + H.lead)
        H.main.V.coins w := rfl

/-- **Alice of `H.compose ρ` is `composePW`**: if `Fρ`, `Fm` compute `ρ.P` and `main.P` on the
layout and `fcall` computes Alice's call inputs (the `callA` clause of `HybridProtocol.PolyTime`),
then `(H.composeP ρ).next x z r hist = H.composePW ρ Fρ Fm fcall (GI.ilayout x z hist r)`.

**Proof sketch.** Unfold both sides (`composeP_next`, `composePW_eq`); the number of messages
read from the layout is `|hist|` (`GI.msgCount_encodeMsgs`). In a run branch `j = k / R < L`, so
the call input is `runInputA` (`runInputA_of_lt`) and `runW` is `runNextA` (`runW_ilayout`,
`runNextA_eq`). In the main branch `mainW` is `main.P.next` on the answers read by `ansW`, which
are `answersFromA` (`ansW_ilayout`, `answersFromA_eq`, `ofFn_padFin`). -/
theorem composeP_next_eq_composePW {Fρ Fm fcall : List Bool → List Bool}
    (hFρ : ∀ x z r hist, ρ.P.next x z r hist = Fρ (GI.ilayout x z hist r))
    (hFm : ∀ x z r hist, H.main.P.next x z r hist = Fm (GI.ilayout x z hist r))
    (hcall : ∀ n (x r : List Bool) (j : Fin (H.calls.eval n)),
      fcall (pairEncode (List.replicate n true) (pairEncode x (pairEncode r
        (List.replicate j true)))) = List.ofFn (H.callA n x r j))
    (x z r : List Bool) (hist : List (List Bool)) :
    (H.composeP ρ).next x z r hist = H.composePW ρ Fρ Fm fcall (GI.ilayout x z hist r) := by
  have hrun : ∀ j p, j < H.calls.eval x.length →
      H.runNextA ρ x z r hist j p =
        runW Fρ fcall H.main.P.coins ρ.P.coins ρ.rounds ρ.verifierFirst true
          (pairEncode (List.replicate j true)
            (pairEncode (List.replicate p true) (GI.ilayout x z hist r))) := by
    intro j p hj
    rw [runW_ilayout, hcall x.length z _ ⟨j, hj⟩, ← H.runInputA_of_lt x z r hj, ← hFρ,
      runNextA_eq]
    congr 2
    funext q
    rw [beq_true]
  rw [composeP_next, composePW_eq, GI.argM_ilayout, GI.argX_ilayout, GI.msgCount_encodeMsgs]
  simp only [decide_eq_true_eq, Bool.and_eq_true]
  by_cases hk : hist.length < H.calls.eval x.length * ρ.rounds.eval x.length
  · have hR : 0 < ρ.rounds.eval x.length := Nat.pos_of_ne_zero fun h => by
      rw [h, Nat.mul_zero] at hk
      omega
    have hj : hist.length / ρ.rounds.eval x.length < H.calls.eval x.length :=
      (Nat.div_lt_iff_lt_mul hR).2 hk
    rw [if_pos hk, if_pos hk]
    by_cases hm : moverIsV ρ.verifierFirst (hist.length % ρ.rounds.eval x.length) = true
    · rw [if_pos hm, if_pos hm]
    · rw [if_neg hm, if_neg hm, hrun _ _ hj]
  · rw [if_neg hk, if_neg hk]
    by_cases hl : H.main.verifierFirst = true ∧
        hist.length = H.calls.eval x.length * ρ.rounds.eval x.length
    · rw [if_pos hl, if_pos hl]
    · rw [if_neg hl, if_neg hl, mainW_ilayout, GI.argX_ilayout, ← hFm, answersFromA_eq,
        ansW_ilayout,
        flatten_ofFn_eq_flatMap_range
          (fun j => List.ofFn (padFin (G.outA.eval x.length)
            (H.runNextA ρ x z r hist j (ρ.rounds.eval x.length))))]
      congr 2
      refine List.flatMap_congr fun j hj => ?_
      rw [ofFn_padFin, hrun _ _ (List.mem_range.1 hj), runW_ilayout]

/-- **Bob of `H.compose ρ` is `composeVW`**: if `Fρ`, `Fm` compute `ρ.V` and `main.V` on the
layout and `fcall` computes Bob's call inputs, then
`(H.composeV ρ).next x z r hist = H.composeVW ρ Fρ Fm fcall (GI.ilayout x z hist r)`.

**Proof sketch.** As `composeP_next_eq_composePW`, with `k = |hist| − 1`, `runNextB`,
`runInputB_of_lt`, the selector `!moverIsV` (`beq_false`), `answersFromB` and the drop count
`L·R + lead`. -/
theorem composeV_next_eq_composeVW {Fρ Fm fcall : List Bool → List Bool}
    (hFρ : ∀ x z r hist, ρ.V.next x z r hist = Fρ (GI.ilayout x z hist r))
    (hFm : ∀ x z r hist, H.main.V.next x z r hist = Fm (GI.ilayout x z hist r))
    (hcall : ∀ n (y r : List Bool) (j : Fin (H.calls.eval n)),
      fcall (pairEncode (List.replicate n true) (pairEncode y (pairEncode r
        (List.replicate j true)))) = List.ofFn (H.callB n y r j))
    (x z r : List Bool) (hist : List (List Bool)) :
    (H.composeV ρ).next x z r hist = H.composeVW ρ Fρ Fm fcall (GI.ilayout x z hist r) := by
  have hrun : ∀ j p, j < H.calls.eval x.length →
      H.runNextB ρ x z r hist j p =
        runW Fρ fcall H.main.V.coins ρ.V.coins ρ.rounds ρ.verifierFirst false
          (pairEncode (List.replicate j true)
            (pairEncode (List.replicate p true) (GI.ilayout x z hist r))) := by
    intro j p hj
    rw [runW_ilayout, hcall x.length z _ ⟨j, hj⟩, ← H.runInputB_of_lt x z r hj, ← hFρ,
      runNextB_eq]
    congr 2
    funext q
    rw [beq_false]
  rw [composeV_next, composeVW_eq, GI.argM_ilayout, GI.argX_ilayout, GI.msgCount_encodeMsgs]
  simp only [decide_eq_true_eq]
  by_cases hk : hist.length - 1 < H.calls.eval x.length * ρ.rounds.eval x.length
  · have hR : 0 < ρ.rounds.eval x.length := Nat.pos_of_ne_zero fun h => by
      rw [h, Nat.mul_zero] at hk
      omega
    have hj : (hist.length - 1) / ρ.rounds.eval x.length < H.calls.eval x.length :=
      (Nat.div_lt_iff_lt_mul hR).2 hk
    rw [if_pos hk, if_pos hk]
    by_cases hm : moverIsV ρ.verifierFirst ((hist.length - 1) % ρ.rounds.eval x.length) = true
    · rw [if_pos hm, if_pos hm, hrun _ _ hj]
    · rw [if_neg hm, if_neg hm]
  · rw [if_neg hk, if_neg hk, mainW_ilayout, GI.argX_ilayout, ← hFm, answersFromB_eq, ansW_ilayout,
      flatten_ofFn_eq_flatMap_range
        (fun j => List.ofFn (padFin (G.outB.eval x.length)
          (H.runNextB ρ x z r hist j (ρ.rounds.eval x.length))))]
    congr 2
    refine List.flatMap_congr fun j hj => ?_
    rw [ofFn_padFin, hrun _ _ (List.mem_range.1 hj), runW_ilayout]

/-- **`composePW` is polynomial-time** when `Fρ`, `Fm` and `fcall` are.
`PolyTimeComputable (H.composePW ρ Fρ Fm fcall)`.

**Proof sketch.** Three branches (`Complexity.polyTimeComputable_ite`) on unary tests of the
message count (`GI.msgCount_poly`) against `L(n)·R(n)` (`ltTest_poly`, `eqTest_poly`), the
mover test at `k % R` (`polyTimeComputable_moverW`, `modNum_poly`), and the pieces
`polyTimeComputable_runW` (at `k / R`, `divNum_poly`), `polyTimeComputable_ansW` and
`polyTimeComputable_mainW`. -/
theorem polyTimeComputable_composePW {Fρ Fm fcall : List Bool → List Bool}
    (hFρ : PolyTimeComputable Fρ) (hFm : PolyTimeComputable Fm)
    (hcall : PolyTimeComputable fcall) : PolyTimeComputable (H.composePW ρ Fρ Fm fcall) := by
  have hk : PolyTimeComputable fun w => List.replicate (GI.msgCount (GI.argM w)) true :=
    GI.msgCount_poly.comp' GI.argM_poly
  have hR := unaryPoly_comp ρ.rounds GI.argX_poly
  have hLR := unaryMul_poly (unaryPoly_comp H.calls GI.argX_poly) hR
  have hdiv : PolyTimeComputable fun w =>
      List.replicate (GI.msgCount (GI.argM w) / ρ.rounds.eval (GI.argX w).length) true :=
    (divNum_poly hk hR).congr fun w => by rw [divNum_eq]
  have hmod : PolyTimeComputable fun w =>
      List.replicate (GI.msgCount (GI.argM w) % ρ.rounds.eval (GI.argX w).length) true :=
    (modNum_poly hk hR).congr fun w => by rw [modNum_eq]
  have hmv : PolyTimeComputable fun w =>
      [moverIsV ρ.verifierFirst (GI.msgCount (GI.argM w) % ρ.rounds.eval (GI.argX w).length)] :=
    ((polyTimeComputable_moverW ρ.verifierFirst true).comp'
      (hmod.pairEncode polyTimeComputable_id)).congr fun w => by
        rw [moverW_eq, pairFstD_pairEncode, List.length_replicate, beq_true]
  have hrun := (polyTimeComputable_runW hFρ hcall H.main.P.coins ρ.P.coins ρ.rounds
    ρ.verifierFirst true).comp' (hdiv.pairEncode (hmod.pairEncode polyTimeComputable_id))
  have hmain := polyTimeComputable_mainW hFm (polyTimeComputable_ansW hFρ hcall H.main.P.coins
    ρ.P.coins ρ.rounds H.calls G.outA ρ.verifierFirst true) hLR H.main.P.coins
  have hlead : PolyTimeComputable fun w =>
      [H.main.verifierFirst && decide (GI.msgCount (GI.argM w) =
      H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length)] :=
    polyTimeComputable_and (polyTimeComputable_const [H.main.verifierFirst]) (eqTest_poly hk hLR)
  exact (polyTimeComputable_ite (ltTest_poly hk hLR)
    (polyTimeComputable_ite hmv (polyTimeComputable_const []) hrun)
    (polyTimeComputable_ite hlead (polyTimeComputable_const []) hmain)).congr
    fun w => (H.composePW_eq ρ Fρ Fm fcall w).symm

/-- **`composeVW` is polynomial-time** when `Fρ`, `Fm` and `fcall` are.
`PolyTimeComputable (H.composeVW ρ Fρ Fm fcall)`.

**Proof sketch.** As `polyTimeComputable_composePW`, with the count `k − 1` (`unarySub_poly`),
two branches in the run phase and the drop count `L(n)·R(n) + lead` (`unaryAdd_poly`). -/
theorem polyTimeComputable_composeVW {Fρ Fm fcall : List Bool → List Bool}
    (hFρ : PolyTimeComputable Fρ) (hFm : PolyTimeComputable Fm)
    (hcall : PolyTimeComputable fcall) : PolyTimeComputable (H.composeVW ρ Fρ Fm fcall) := by
  have hk : PolyTimeComputable fun w => List.replicate (GI.msgCount (GI.argM w) - 1) true :=
    unarySub_poly (GI.msgCount_poly.comp' GI.argM_poly) (unaryConst_poly 1)
  have hR := unaryPoly_comp ρ.rounds GI.argX_poly
  have hLR := unaryMul_poly (unaryPoly_comp H.calls GI.argX_poly) hR
  have hdiv : PolyTimeComputable fun w =>
      List.replicate ((GI.msgCount (GI.argM w) - 1) / ρ.rounds.eval (GI.argX w).length) true :=
    (divNum_poly hk hR).congr fun w => by rw [divNum_eq]
  have hmod : PolyTimeComputable fun w =>
      List.replicate ((GI.msgCount (GI.argM w) - 1) % ρ.rounds.eval (GI.argX w).length) true :=
    (modNum_poly hk hR).congr fun w => by rw [modNum_eq]
  have hmv : PolyTimeComputable fun w =>
      [moverIsV ρ.verifierFirst
        ((GI.msgCount (GI.argM w) - 1) % ρ.rounds.eval (GI.argX w).length)] :=
    ((polyTimeComputable_moverW ρ.verifierFirst true).comp'
      (hmod.pairEncode polyTimeComputable_id)).congr fun w => by
        rw [moverW_eq, pairFstD_pairEncode, List.length_replicate, beq_true]
  have hrun := (polyTimeComputable_runW hFρ hcall H.main.V.coins ρ.V.coins ρ.rounds
    ρ.verifierFirst false).comp' (hdiv.pairEncode (hmod.pairEncode polyTimeComputable_id))
  have hmain := polyTimeComputable_mainW hFm (polyTimeComputable_ansW hFρ hcall H.main.V.coins
    ρ.V.coins ρ.rounds H.calls G.outB ρ.verifierFirst false)
    (unaryAdd_poly hLR (unaryConst_poly H.lead)) H.main.V.coins
  exact (polyTimeComputable_ite (ltTest_poly hk hLR)
    (polyTimeComputable_ite hmv hrun (polyTimeComputable_const [])) hmain).congr
    fun w => (H.composeVW_eq ρ Fρ Fm fcall w).symm

end Parties

end HybridProtocol

end TCSlib.Cryptography.SecureComputation

## ===== TCSlib/Cryptography/SecureComputation/ComposeSecurity/Lengths.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Runs
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Bounds

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial bounds on the words of the hybrid-step templates

The templates of the reductions of the composition theorem [Gol04, §7.3.1, proof of
Theorem 7.3.3] hold the hybrid main phase, the other party's output in `main`, real views of
`ρ` and simulator outputs. Each has a length bounded by a polynomial in `n`, uniformly over the
inputs and coins:
* the encoded messages of the main phase on the ideal answers (`H.PolyTime` bounds `main`'s
  messages for any answers of the hybrid lengths) and the parties' outputs in `main` (efficient
  strategies on a polynomially long layout);
* the encoded views of `ρ` on inputs of `G`'s lengths (`G.PolyTime ρ`);
* the outputs of a machine on polynomially long arguments.

## Main results

* `HybridProtocol.exists_main_msgs_le`, `exists_main_outV_le`, `exists_main_outP_le`.
* `ComposeBound.exists_viewP_le`, `exists_viewV_le`, `exists_runAt_le`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §2.1 (Definition 26.8) and §4.4 (time complexity of interactive machines).
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing TCSlib.Cryptography ComposeBound

/-- A list of length `c` is the encoding of a `c`-bit string. -/
private theorem exists_ofFn_eq {c : ℕ} {l : List Bool} (h : l.length = c) :
    ∃ t : Fin c → Bool, List.ofFn t = l := by
  subst h
  exact ⟨fun i => l[i.1], List.ofFn_getElem l⟩

namespace HybridProtocol

variable {G : Functionality} (H : HybridProtocol G)

/-- Alice's ideal answers have `calls(n) · G.outA(n)` bits.
`(H.answersA n x y rA rB).length = H.calls.eval n * G.outA.eval n`. -/
theorem length_answersA (n : ℕ) (x y rA rB : List Bool) :
    (H.answersA n x y rA rB).length = H.calls.eval n * G.outA.eval n := by
  rw [answersA_eq, List.length_flatten, List.map_ofFn]
  simp only [Function.comp_def, List.length_ofFn, List.ofFn_const, List.sum_replicate,
    smul_eq_mul]

/-- Bob's ideal answers have `calls(n) · G.outB(n)` bits.
`(H.answersB n x y rA rB).length = H.calls.eval n * G.outB.eval n`. -/
theorem length_answersB (n : ℕ) (x y rA rB : List Bool) :
    (H.answersB n x y rA rB).length = H.calls.eval n * G.outB.eval n := by
  rw [answersB_eq, List.length_flatten, List.map_ofFn]
  simp only [Function.comp_def, List.length_ofFn, List.ofFn_const, List.sum_replicate,
    smul_eq_mul]

/-- **The encoded main phase is polynomially long**: for some polynomial `E`, on common input
`1^n`, inputs of `F`'s lengths and any `main`-tapes, both halves of the encoded transcript of
`main` on the ideal answers have at most `E(n)` bits.
`∃ E : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (m : H.Coins
n), (Strategy.encodeMsgs (H.main.transcript (List.replicate n true) (H.privA n (List.ofFn x)
(List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) …`.

**Proof sketch.** The ideal answers are strings of the hybrid lengths (`length_answersA`,
`length_answersB`), so `H.PolyTime` bounds every message by `B(n)`; each half of the transcript
has at most `rounds(n)` messages (`length_transcriptWith_fst_le`), so its encoding has at most
`E(n) = rounds(n) (2B(n) + 2)` bits (`length_encodeMsgs_le`). -/
theorem exists_main_msgs_le {F : Functionality} (hH : H.PolyTime F) :
    ∃ E : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool)
      (m : H.Coins n),
      (Strategy.encodeMsgs (H.main.transcript (List.replicate n true)
          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m).1).length ≤
          E.eval n ∧
        (Strategy.encodeMsgs (H.main.transcript (List.replicate n true)
          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m).2).length ≤
          E.eval n := by
  obtain ⟨-, -, -, -, B, hB⟩ := (HybridProtocol.polyTime_iff H F).mp hH
  refine ⟨.mul H.main.rounds (.add (.mul (.const 2) B) (.const 2)), fun n x y m => ?_⟩
  obtain ⟨aA, haA⟩ := exists_ofFn_eq (c := H.calls.eval n * G.outA.eval n)
    (l := H.answersA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
    (H.length_answersA n _ _ _ _)
  obtain ⟨aB, haB⟩ := exists_ofFn_eq (c := H.calls.eval n * G.outB.eval n)
    (l := H.answersB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
    (H.length_answersB n _ _ _ _)
  have hmsg := hB n x y aA aB m
  rw [haA, haB, ← privA_eq, ← privB_eq, Protocol.transcript_eq_transcriptWith] at hmsg
  rw [Protocol.transcript_eq_transcriptWith]
  have h₁ := length_transcriptWith_fst_le H.main H.main.P (List.replicate n true)
    (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
    (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m
  have h₂ := length_transcriptWith_snd_le H.main H.main.P (List.replicate n true)
    (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
    (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m
  have hR : H.main.rounds.eval (List.replicate n true).length = H.main.rounds.eval n := by
    rw [List.length_replicate]
  simp only [PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const]
  exact ⟨(length_encodeMsgs_le _ (B.eval n) fun w hw => hmsg w (List.mem_append_left _ hw)).trans
      (Nat.mul_le_mul_right _ (h₁.trans hR.le)),
    (length_encodeMsgs_le _ (B.eval n) fun w hw => hmsg w (List.mem_append_right _ hw)).trans
      (Nat.mul_le_mul_right _ (h₂.trans hR.le))⟩

/-- **Bob's output in `main` is polynomially long**: for some polynomial `O`, on common input
`1^n`, inputs of `F`'s lengths and any `main`-tapes, Bob's output in the hybrid execution has at
most `O(n)` bits.
`∃ O : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (m : H.Coins
n), (H.main.outV H.main.P (List.replicate n true) (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn
m.1) (List.ofFn m.2)) (H.privB n …`.

**Proof sketch.** The output is `main.V.next` on `1^n`, Bob's private input, the messages he
received and his `main`-tape (`Protocol.outV_eq`), at most `C (|layout| + 1)^c` bits
(`Efficient.length_next_le`). The layout's length (`length_ilayout`) is linear in `n`, in his
private input's `2 F.inB(n) + 2 + calls(n) G.outB(n)` bits (`length_answersB`), in the encoded
messages (`exists_main_msgs_le`) and in his coin length; take `O = C (I + 1)^c` for that linear
bound `I`. -/
theorem exists_main_outV_le {F : Functionality} (hH : H.PolyTime F) :
    ∃ O : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool)
      (m : H.Coins n),
      (H.main.outV H.main.P (List.replicate n true)
        (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
        (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m).length ≤
        O.eval n := by
  obtain ⟨-, hV, -, -, -⟩ := (HybridProtocol.polyTime_iff H F).mp hH
  obtain ⟨C, c, hC⟩ := Efficient.length_next_le hV
  obtain ⟨E, hE⟩ := H.exists_main_msgs_le hH
  -- the layout: `1^n`, Bob's private input, the main phase and his `main`-tape
  let I : PolyExpr := .add (.add (.mul (.const 2) (.add (.mul (.const 2)
      (.add (.add (.mul (.const 2) .var) (.const 2))
        (.add (.add (.mul (.const 2) (.add (.add (.mul (.const 2) .var) (.const 2))
          (.add (.add (.mul (.const 2) F.inB) (.const 2)) (.mul H.calls G.outB)))) (.const 2)) E)))
      (.const 2))) (.const 2)) H.main.V.coins
  refine ⟨.mul (.const C) (.pow (.add I (.const 1)) c), fun n x y m => ?_⟩
  have hI : (GI.ilayout (List.replicate n true)
      (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
      (H.main.transcriptWith H.main.P (List.replicate n true)
        (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
        (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m).2
      (List.ofFn m.2)).length ≤ I.eval n := by
    have h₁ := (hE n x y m).2
    rw [Protocol.transcript_eq_transcriptWith] at h₁
    have hpB : (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)).length =
        2 * F.inB.eval n + 2 + H.calls.eval n * G.outB.eval n := by
      rw [privB_eq, length_pairEncode, H.length_answersB, List.length_ofFn]
    have hc : (List.ofFn m.2).length = H.main.V.coins.eval n := by
      rw [List.length_ofFn, Strategy.coinLen_eq, List.length_replicate]
    have hu : (List.replicate n true).length = n := List.length_replicate
    rw [length_ilayout, hpB, hc]
    simp only [I, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
    omega
  rw [Protocol.outV_eq]
  refine (hC _ _ _ _).trans ?_
  simp only [PolyExpr.eval_mul, PolyExpr.eval_pow, PolyExpr.eval_add, PolyExpr.eval_const]
  gcongr

/-- **Alice's output in `main` is polynomially long**: for some polynomial `O`, on common input
`1^n`, inputs of `F`'s lengths and any `main`-tapes, Alice's output in the hybrid execution has
at most `O(n)` bits.
`∃ O : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (m : H.Coins
n), (H.main.outP (List.replicate n true) (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1)
(List.ofFn m.2)) (H.privB n (List.ofFn x) …`.

**Proof sketch.** As `exists_main_outV_le`, with `main.P.next` on her private input
(`length_answersA`), the messages she received and her `main`-tape (`Protocol.outP_eq`). -/
theorem exists_main_outP_le {F : Functionality} (hH : H.PolyTime F) :
    ∃ O : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool)
      (m : H.Coins n),
      (H.main.outP (List.replicate n true)
        (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
        (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m).length ≤
        O.eval n := by
  obtain ⟨hP, -, -, -, -⟩ := (HybridProtocol.polyTime_iff H F).mp hH
  obtain ⟨C, c, hC⟩ := Efficient.length_next_le hP
  obtain ⟨E, hE⟩ := H.exists_main_msgs_le hH
  let I : PolyExpr := .add (.add (.mul (.const 2) (.add (.mul (.const 2)
      (.add (.add (.mul (.const 2) .var) (.const 2))
        (.add (.add (.mul (.const 2) (.add (.add (.mul (.const 2) .var) (.const 2))
          (.add (.add (.mul (.const 2) F.inA) (.const 2)) (.mul H.calls G.outA)))) (.const 2)) E)))
      (.const 2))) (.const 2)) H.main.P.coins
  refine ⟨.mul (.const C) (.pow (.add I (.const 1)) c), fun n x y m => ?_⟩
  have hI : (GI.ilayout (List.replicate n true)
      (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
      (H.main.transcriptWith H.main.P (List.replicate n true)
        (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
        (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m).1
      (List.ofFn m.1)).length ≤ I.eval n := by
    have h₁ := (hE n x y m).1
    rw [Protocol.transcript_eq_transcriptWith] at h₁
    have hpA : (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)).length =
        2 * F.inA.eval n + 2 + H.calls.eval n * G.outA.eval n := by
      rw [privA_eq, length_pairEncode, H.length_answersA, List.length_ofFn]
    have hc : (List.ofFn m.1).length = H.main.P.coins.eval n := by
      rw [List.length_ofFn, Strategy.coinLen_eq, List.length_replicate]
    have hu : (List.replicate n true).length = n := List.length_replicate
    rw [length_ilayout, hpA, hc]
    simp only [I, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
    omega
  rw [Protocol.outP_eq]
  refine (hC _ _ _ _).trans ?_
  simp only [PolyExpr.eval_mul, PolyExpr.eval_pow, PolyExpr.eval_add, PolyExpr.eval_const]
  gcongr

end HybridProtocol

namespace ComposeBound

/-- **Alice's encoded `ρ`-views are polynomially long**: for some polynomial `V`, on common input
`1^n` and inputs of `G`'s lengths, `|encode (viewP)| ≤ V(n)`.

**Proof sketch.** The encoded view is `⟨⟨1^n, x⟩, ⟨tape, encodeMsgs received⟩⟩` (`View.encode_mk`,
`length_pairEncode`): her tape has `ρ.P.coins(n)` bits, and she receives at most `rounds(n)`
messages (`length_transcriptWith_fst_le`) of at most `B(n)` bits each, `B` the bound of
`G.PolyTime ρ` (`length_encodeMsgs_le`); the sum is linear in these. -/
theorem exists_viewP_le {G : Functionality} {ρ : Protocol} (hρ : G.PolyTime ρ) :
    ∃ V : PolyExpr, ∀ n (x : Fin (G.inA.eval n) → Bool) (y : Fin (G.inB.eval n) → Bool)
      (t : ρ.ExecCoins ρ.P (List.replicate n true)),
      (ρ.viewP (List.replicate n true) (List.ofFn x) (List.ofFn y) t).encode.length ≤
        V.eval n := by
  obtain ⟨-, -, B, hB⟩ := (Functionality.polyTime_iff G ρ).mp hρ
  refine ⟨.add (.add (.mul (.const 2) (.add (.add (.mul (.const 2) .var) (.const 2)) G.inA))
      (.const 2)) (.add (.add (.mul (.const 2) ρ.P.coins) (.const 2))
        (.mul ρ.rounds (.add (.mul (.const 2) B) (.const 2)))), fun n x y t => ?_⟩
  have h₁ := length_transcriptWith_fst_le ρ ρ.P (List.replicate n true) (List.ofFn x)
    (List.ofFn y) t
  have hb := hB n x y t
  rw [Protocol.transcript_eq_transcriptWith] at hb
  have h₂ := (length_encodeMsgs_le _ (B.eval n) fun w hw =>
    hb w (List.mem_append_left _ hw)).trans (Nat.mul_le_mul_right _ h₁)
  have hR : ρ.rounds.eval (List.replicate n true).length = ρ.rounds.eval n := by
    rw [List.length_replicate]
  rw [hR] at h₂
  have hu : (List.replicate n true).length = n := List.length_replicate
  have hz : (List.ofFn x).length = G.inA.eval n := List.length_ofFn
  have ht : (List.ofFn t.1).length = ρ.P.coins.eval n := by
    rw [List.length_ofFn, Strategy.coinLen_eq, List.length_replicate]
  rw [Protocol.viewP_eq, View.encode_mk, length_pairEncode, length_pairEncode, length_pairEncode,
    ht]
  simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  omega

/-- **Bob's encoded `ρ`-views are polynomially long**: for some polynomial `V`, on common input
`1^n` and inputs of `G`'s lengths, `|encode (viewV)| ≤ V(n)`.

**Proof sketch.** As `exists_viewP_le`, with `ρ.V`'s tape and the messages he receives
(`length_transcriptWith_snd_le`). -/
theorem exists_viewV_le {G : Functionality} {ρ : Protocol} (hρ : G.PolyTime ρ) :
    ∃ V : PolyExpr, ∀ n (x : Fin (G.inA.eval n) → Bool) (y : Fin (G.inB.eval n) → Bool)
      (t : ρ.ExecCoins ρ.P (List.replicate n true)),
      (ρ.viewV (List.replicate n true) (List.ofFn x) (List.ofFn y) t).encode.length ≤
        V.eval n := by
  obtain ⟨-, -, B, hB⟩ := (Functionality.polyTime_iff G ρ).mp hρ
  refine ⟨.add (.add (.mul (.const 2) (.add (.add (.mul (.const 2) .var) (.const 2)) G.inB))
      (.const 2)) (.add (.add (.mul (.const 2) ρ.V.coins) (.const 2))
        (.mul ρ.rounds (.add (.mul (.const 2) B) (.const 2)))), fun n x y t => ?_⟩
  have h₁ := length_transcriptWith_snd_le ρ ρ.P (List.replicate n true) (List.ofFn x)
    (List.ofFn y) t
  have hb := hB n x y t
  rw [Protocol.transcript_eq_transcriptWith] at hb
  have h₂ := (length_encodeMsgs_le _ (B.eval n) fun w hw =>
    hb w (List.mem_append_right _ hw)).trans (Nat.mul_le_mul_right _ h₁)
  have hR : ρ.rounds.eval (List.replicate n true).length = ρ.rounds.eval n := by
    rw [List.length_replicate]
  rw [hR] at h₂
  have hu : (List.replicate n true).length = n := List.length_replicate
  have hz : (List.ofFn y).length = G.inB.eval n := List.length_ofFn
  have ht : (List.ofFn t.2).length = ρ.V.coins.eval n := by
    rw [List.length_ofFn, Strategy.coinLen_eq, List.length_replicate]
  rw [Protocol.viewV_eq, View.encode_mk, length_pairEncode, length_pairEncode, length_pairEncode,
    ht]
  simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  omega

/-- **A machine's outputs on polynomially long arguments are polynomially long**: for an `NUPPT`
`S` and a polynomial `k` there is a polynomial `O` with `|S.runAt n w s| ≤ O(n)` whenever
`|w| ≤ k(n)` (`length_runAt_le`, `NUPPT.advice_length`). -/
theorem exists_runAt_le (S : NUPPT) (k : PolyExpr) :
    ∃ O : PolyExpr, ∀ n (w : List Bool) (s : S.Coins n), w.length ≤ k.eval n →
      (S.runAt n w s).length ≤ O.eval n := by
  let I : PolyExpr := .add (.add (.mul (.const 2) (.add (.add (.mul (.const 2)
    (.add (.add (.mul (.const 2) .var) (.const 2)) k)) (.const 2)) S.adv)) (.const 2)) S.coins
  refine ⟨.mul (.const S.Ct) (.pow (.add I (.const 1)) S.ct), fun n w s hw => ?_⟩
  refine (length_runAt_le S n w s).trans ?_
  have ha := S.advice_length n
  have hI : 2 * (2 * (2 * n + 2 + w.length) + 2 + (S.advice n).length) + 2 + S.coinLen n ≤
      I.eval n := by
    simp only [I, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var,
      NUPPT.coinLen_eq]
    omega
  simp only [PolyExpr.eval_mul, PolyExpr.eval_pow, PolyExpr.eval_add, PolyExpr.eval_const]
  gcongr

end ComposeBound

end TCSlib.Cryptography.SecureComputation

## ===== TCSlib/Cryptography/SecureComputation/ComposeSecurity/Machines.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.EfficiencyRep
import TCSlib.Cryptography.ZeroKnowledge.EncodingMachines
import TCSlib.Cryptography.SecureComputation.Compose

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial-time machines on encoded histories

The machine infrastructure behind the efficiency of the composed parties
(`HybridProtocol.composeP_efficient`, `composeV_efficient`) [Gol04, §7.3.1, the protocol of
Theorem 7.3.3]: a party of `H.compose ρ` reads its history `encodeMsgs hist` at interleaved
positions (the messages of one run of `ρ` sit at every other pair, `Compose.slotMsgs`), and maps
`ρ`'s next-message function over the `L(n)` runs. Both are loops over a data-dependent range of
the unary FP toolkit (`ZeroKnowledge/EncodingMachines.lean`) and the peeling loops of
`GraphIsomorphism/EfficiencyRep.lean`.

## Main definitions

* `ComposeMachines.padTo`: zero padding, the string form of `padFin`.

## Main results

* `ComposeMachines.polyTimeComputable_flatMap_range`: concatenating a polynomial-time chunk over
  a data-dependent range is polynomial-time.
* `ComposeMachines.iterSnd_poly`, `msgAt_encodeMsgs`: the `i`-th message of an encoded history.
* `ComposeMachines.encodeMsgs_append`, `encodeMsgs_eq_flatMap`, `encodeMsgs_slotMsgs`: the
  history encoding as a concatenation of chunks, and the interleaved slots of a history.
* `ComposeMachines.polyTimeComputable_slots`: **the interleaved-slot map**: the encoded messages
  `slotMsgs sel off p hist` are a polynomial-time function of the encoded history, for a
  polynomial-time selector and unary offset and count.
* `ComposeMachines.Efficient.exists_polyTime`: an efficient strategy's next-message function is
  a polynomial-time function of the machine layout `GI.ilayout` (the converse of
  `GI.efficient_of_polyTime`).
* `ComposeMachines.ofFn_padFin`, `padTo_poly`: `padFin` as a polynomial-time string map.

## References

* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
  University Press, 2004, §7.3.1 (the composed protocol of Theorem 7.3.3).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §4.4 (interactive machines and their time complexity, pp. 114–116).
-/

namespace TCSlib.Cryptography.SecureComputation.ComposeMachines

open Complexity Turing Complexity.StateLoop TCSlib.Cryptography.EncodingMachines

/-! ### Loops over a data-dependent range -/

/-- Emitting `E i` at the indices `i < L` of `List.range N` gives the concatenation of the
`E i` over `i < min N L`:
`(range N).flatMap (fun i => if i < L then E i else []) = (range (min N L)).flatMap E`. -/
theorem flatMap_range_ite (E : ℕ → List Bool) (L : ℕ) :
    ∀ N, (List.range N).flatMap (fun i => if i < L then E i else []) =
      (List.range (min N L)).flatMap E
  | 0 => by simp
  | N + 1 => by
    rw [List.range_succ, List.flatMap_append, flatMap_range_ite E L N, List.flatMap_singleton]
    by_cases h : N < L
    · rw [if_pos h, show min (N + 1) L = N + 1 by omega, show min N L = N by omega,
        List.range_succ, List.flatMap_append, List.flatMap_singleton]
    · rw [if_neg h, List.append_nil, show min (N + 1) L = min N L by omega]

/-- **Concatenating a chunk over a data-dependent range**: if the chunk `E z i` is a
polynomial-time function of `⟨1^i, z⟩` and the count `n z` is a unary function, then
`z ↦ E z 0 ++ ⋯ ++ E z (n z − 1)` is polynomial-time.
`PolyTimeComputable fun z => (List.range (n z)).flatMap (E z)`.

**Proof sketch.** An instance of `Complexity.polyTimeComputable_iterateEmit` on the counter step
`EncodingMachines.cstep` from `⟨[], z⟩`, whose `i`-th iterate is `⟨1^i, z⟩` (`cstep_iterate`),
emitting `E z i` while `i < n z` (`flatMap_range_ite`); the number of rounds is the polynomial
bound of the unary count (`PolyTimeComputable.output_length_le`). -/
theorem polyTimeComputable_flatMap_range {E : List Bool → ℕ → List Bool}
    (hE : PolyTimeComputable fun w => E (pairSndD w) (pairFstD w).length)
    {n : List Bool → ℕ} (hn : PolyTimeComputable fun z => List.replicate (n z) true) :
    PolyTimeComputable fun z => (List.range (n z)).flatMap (E z) := by
  obtain ⟨C, c, hC⟩ := hn.output_length_le
  have hnP : ∀ z, n z ≤ (PolyExpr.normal C c).eval z.length := fun z => by
    have := hC z
    simpa [PolyExpr.eval_normal] using this
  have htest : PolyTimeComputable fun w => [decide ((pairFstD w).length < n (pairSndD w))] :=
    ltTest_poly (unaryLength_poly polyTimeComputable_pairFstD)
      (hn.comp polyTimeComputable_pairSndD)
  have hemit := polyTimeComputable_ite htest hE (polyTimeComputable_const [])
  have hL := polyTimeComputable_iterateEmit cstep_poly hemit (PolyExpr.normal C c)
    (cbound (PolyExpr.normal C c)) (cstep_horbit _)
  have hpre : PolyTimeComputable fun z => pairEncode [] z :=
    (polyTimeComputable_const []).pairEncode polyTimeComputable_id
  refine (hL.comp hpre).congr fun z => ?_
  simp only [Function.comp_apply]
  have horb : ∀ i, cstep^[i] (pairEncode [] z) = pairEncode (List.replicate i true) z :=
    fun i => by rw [cstep_iterate, List.append_nil]
  have hN : n z ≤ (PolyExpr.normal C c).eval (pairEncode [] z).length + 1 :=
    ((hnP z).trans ((PolyExpr.normal C c).eval_mono
      (by rw [length_pairEncode]; omega))).trans (Nat.le_succ _)
  simp only [horb, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
    decide_eq_true_eq]
  rw [flatMap_range_ite, min_eq_right hN]

/-! ### Reading an encoded history -/

/-- **The iterated second projection** `pairSndD^[i z] (s z)` is polynomial-time for a
polynomial-time `s` and a unary count `i`.
`PolyTimeComputable fun z => pairSndD^[i z] (s z)`.

**Proof sketch.** `GI.iterUnary_poly` with the step `⟨x₀, s⟩ ↦ pairSndD s` on
`⟨1^{i z}, s z⟩`; peeling never lengthens a word (`GI.length_iterate_le`,
`GI.length_pairSndD_le`), so the orbit is bounded by the input length. -/
theorem iterSnd_poly {s : List Bool → List Bool} (hs : PolyTimeComputable s)
    {i : List Bool → ℕ} (hi : PolyTimeComputable fun z => List.replicate (i z) true) :
    PolyTimeComputable fun z => pairSndD^[i z] (s z) := by
  have hstep : PolyTimeComputable fun w => pairSndD (pairSndD w) :=
    polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hclosed : ∀ x₀ k, (fun t => pairSndD (pairSndD (pairEncode x₀ t)))^[k] (pairSndD x₀) =
      pairSndD^[k] (pairSndD x₀) := by
    intro x₀ k
    congr 1
    funext t
    rw [pairSndD_pairEncode]
  have hit := GI.iterUnary_poly hstep .var fun x₀ k _ => by
    rw [hclosed, PolyExpr.eval_var]
    exact (GI.length_iterate_le GI.length_pairSndD_le _ k).trans (GI.length_pairSndD_le x₀)
  refine (hit.comp (hi.pairEncode hs)).congr fun z => ?_
  simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate]

/-- **The `i`-th message of an encoded history**: `pairFstD (pairSndD^[i] (encodeMsgs hist)) =
hist.getD i []` (`GI.iterate_pairSndD_encodeMsgs`, `Strategy.pairFstD_encodeMsgs`). -/
theorem msgAt_encodeMsgs (hist : List (List Bool)) (i : ℕ) :
    pairFstD (pairSndD^[i] (Strategy.encodeMsgs hist)) = hist.getD i [] := by
  rw [GI.iterate_pairSndD_encodeMsgs, Strategy.pairFstD_encodeMsgs, List.headD_eq_head?_getD,
    List.head?_drop, List.getD_eq_getElem?_getD]

/-- **The history encoding is a concatenation**:
`encodeMsgs (a ++ b) = encodeMsgs a ++ encodeMsgs b` (`pairEncode_nil_append`). -/
theorem encodeMsgs_append (a b : List (List Bool)) :
    Strategy.encodeMsgs (a ++ b) = Strategy.encodeMsgs a ++ Strategy.encodeMsgs b := by
  induction a with
  | nil => rw [List.nil_append, Strategy.encodeMsgs_nil, List.nil_append]
  | cons m a ih =>
    rw [List.cons_append, Strategy.encodeMsgs_cons, Strategy.encodeMsgs_cons, ih,
      ← BinArith.pairEncode_nil_append,
      ← BinArith.pairEncode_nil_append (b := Strategy.encodeMsgs a), List.append_assoc]

/-- **The history encoding chunk by chunk**: `encodeMsgs l = l.flatMap fun m => ⟨m, []⟩`. -/
theorem encodeMsgs_eq_flatMap (l : List (List Bool)) :
    Strategy.encodeMsgs l = l.flatMap fun m => pairEncode m [] := by
  induction l with
  | nil => rw [Strategy.encodeMsgs_nil, List.flatMap_nil]
  | cons m l ih =>
    rw [Strategy.encodeMsgs_cons, List.flatMap_cons, ← ih, BinArith.pairEncode_nil_append]

/-- **The encoded slots of a history**: the encoding of `slotMsgs sel off p hist` is the
concatenation over `q < p` of the chunk `⟨hist[off + q], []⟩` when `sel q`, read from the
encoded history (`msgAt_encodeMsgs`):
`encodeMsgs (slotMsgs sel off p hist) = (range p).flatMap fun q =>
if sel q then ⟨pairFstD (pairSndD^[off + q] (encodeMsgs hist)), []⟩ else []`. -/
theorem encodeMsgs_slotMsgs (sel : ℕ → Bool) (off p : ℕ) (hist : List (List Bool)) :
    Strategy.encodeMsgs (Compose.slotMsgs sel off p hist) =
      (List.range p).flatMap fun q =>
        if sel q then pairEncode (pairFstD (pairSndD^[off + q] (Strategy.encodeMsgs hist))) []
        else [] := by
  rw [Compose.slotMsgs_eq, encodeMsgs_eq_flatMap, List.flatMap_map]
  induction p with
  | zero => simp only [List.range_zero, List.filter_nil, List.flatMap_nil]
  | succ p ih =>
    rw [List.range_succ, List.filter_append, List.flatMap_append, List.flatMap_append, ih,
      List.flatMap_singleton]
    congr 1
    cases h : sel p
    · rw [List.filter_singleton, h, cond_false, List.flatMap_nil, if_neg Bool.false_ne_true]
    · rw [List.filter_singleton, h, cond_true, List.flatMap_singleton, if_pos rfl,
        msgAt_encodeMsgs]

/-- **The interleaved-slot map**: for a selector `sel z q` that is a polynomial-time test of
`⟨1^q, z⟩`, unary offset `off z` and count `p z`, and a polynomial-time word `M z`, the word
`(range (p z)).flatMap fun q => if sel z q then ⟨pairFstD (pairSndD^[off z + q] (M z)), []⟩
else []` is polynomial-time; on `M z = encodeMsgs hist` it is
`encodeMsgs (slotMsgs (sel z) (off z) (p z) hist)` (`encodeMsgs_slotMsgs`).

**Proof sketch.** `polyTimeComputable_flatMap_range` with the chunk built from the test, the
iterated projection at the unary count `off z + q` (`iterSnd_poly`, `unaryAdd_poly`) and
`pairEncode`. -/
theorem polyTimeComputable_slots {sel : List Bool → ℕ → Bool}
    (hsel : PolyTimeComputable fun w => [sel (pairSndD w) (pairFstD w).length])
    {off p : List Bool → ℕ} (hoff : PolyTimeComputable fun z => List.replicate (off z) true)
    (hp : PolyTimeComputable fun z => List.replicate (p z) true)
    {M : List Bool → List Bool} (hM : PolyTimeComputable M) :
    PolyTimeComputable fun z => (List.range (p z)).flatMap fun q =>
      if sel z q then pairEncode (pairFstD (pairSndD^[off z + q] (M z))) [] else [] := by
  have hcnt : PolyTimeComputable fun w =>
      List.replicate (off (pairSndD w) + (pairFstD w).length) true :=
    unaryAdd_poly (hoff.comp polyTimeComputable_pairSndD)
      (unaryLength_poly polyTimeComputable_pairFstD)
  have hmsg := polyTimeComputable_pairFstD.comp
    (iterSnd_poly (hM.comp polyTimeComputable_pairSndD) hcnt)
  exact polyTimeComputable_flatMap_range
    (polyTimeComputable_ite hsel (hmsg.pairEncode (polyTimeComputable_const []))
      (polyTimeComputable_const [])) hp

/-! ### Strategies as functions of the machine layout -/

/-- **An efficient strategy is a polynomial-time function of the layout** (the converse of
`GI.efficient_of_polyTime`): if `S.Efficient`, there is a polynomial-time `F` with
`S.next x z r hist = F (GI.ilayout x z hist r)` (the output
function of the uniform machine, `NUPPT.polyTimeComputable_output`; its advice is empty). -/
theorem Efficient.exists_polyTime {S : Strategy} (h : S.Efficient) :
    ∃ F : List Bool → List Bool, PolyTimeComputable F ∧
      ∀ x z r hist, S.next x z r hist = F (GI.ilayout x z hist r) := by
  obtain ⟨A, hA, -, hnext⟩ := (Strategy.efficient_iff S).1 h
  refine ⟨A.output, A.polyTimeComputable_output, fun x z r hist => ?_⟩
  rw [hnext, Strategy.ofNUPPT_next, NUPPT.runAtL_eq_output_layout, NUPPT.Uniform.advice_eq hA,
    GI.ilayout_def]

/-! ### Zero padding -/

/-- **Zero padding** to length `L` (and truncation to `L`): `padTo L w = (w ++ 0^L).take L`, the
string form of `padFin L w` (`ofFn_padFin`). -/
def padTo (L : ℕ) (w : List Bool) : List Bool := (w ++ List.replicate L false).take L

/-- The defining equation of `padTo`: `padTo L w = (w ++ 0^L).take L`. -/
theorem padTo_eq (L : ℕ) (w : List Bool) : padTo L w = (w ++ List.replicate L false).take L :=
  rfl

/-- Padding to a unary length is polynomial-time (`EncodingMachines.truncate_poly`, the zeros
`GI.zeros_poly` of the unary string).
`PolyTimeComputable fun x => padTo (L x) (s x)`. -/
theorem padTo_poly {s : List Bool → List Bool} (hs : PolyTimeComputable s)
    {L : List Bool → ℕ} (hL : PolyTimeComputable fun x => List.replicate (L x) true) :
    PolyTimeComputable fun x => padTo (L x) (s x) :=
  truncate_poly (hs.append ((GI.zeros_poly.comp' hL).congr fun x => by
    rw [List.length_replicate])) hL

/-- The padded word has length `L`: `|padTo L w| = L`. -/
theorem length_padTo (L : ℕ) (w : List Bool) : (padTo L w).length = L := by
  rw [padTo_eq, List.length_take, List.length_append, List.length_replicate]
  omega

/-- **`padFin` as a string**: `List.ofFn (padFin L w) = padTo L w`. -/
theorem ofFn_padFin (L : ℕ) (w : List Bool) : List.ofFn (padFin L w) = padTo L w := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_ofFn, padTo_eq, List.getElem?_take]
  by_cases hi : i < L
  · rw [dif_pos hi, if_pos hi, padFin_apply, Fin.val_mk, List.getD_eq_getElem?_getD,
      List.getElem?_append]
    split_ifs with h
    · rw [List.getElem?_eq_getElem h, Option.getD_some]
    · rw [List.getElem?_eq_none_iff.2 (by omega), Option.getD_none,
        List.getElem?_replicate, if_pos (by omega)]
  · rw [dif_neg hi, if_neg hi]

end TCSlib.Cryptography.SecureComputation.ComposeMachines

## ===== TCSlib/Cryptography/SecureComputation/ComposeSecurity/Probability.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Foundations.Experiments
import TCSlib.Cryptography.Foundations.Negligible
import TCSlib.Complexity.Randomized.PolyExpr

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Probability tools for the composition theorem

The distinguishing-advantage manipulations of the proof of [Gol04, §7.3.1, Theorem 7.3.3]
(`HybridProtocol.hbcSecure_compose`), on uniform seeds and coins (`acceptProb`, `distAdv`):
* the statistical switch: two samplers on one seed space that agree off a bad event are within
  the bad event's probability;
* fixing coordinates: the advantage between two samplers on `σ × τ` is at most the advantage of
  their sections at the worst `a : σ` (the advice of a non-uniform reduction);
* a negligible function times a polynomial is negligible.

Unused seed coordinates are dropped by the published `acceptProb_fst`, `acceptProb_snd`
(`Pseudorandom/Indistinguishability.lean`).

## Main results

* `ComposeProb.abs_uprob_sub_le`, `ComposeProb.distAdv_le_uprob_of_eq`,
  `ComposeProb.exists_abs_sub_le_sections`, `ComposeProb.negligible_polyExpr_mul`.

## References

* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
  University Press, 2004, §7.3.1 (the proof of Theorem 7.3.3).
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley, draft of
  22 January 2026, §1.2 (negligible functions) and §3.2 (hybrid arguments).
-/

namespace TCSlib.Cryptography.SecureComputation.ComposeProb

open Finset Complexity

variable {σ τ υ γ ρ : Type*} [Fintype σ] [Fintype τ] [Fintype υ] [Fintype ρ]

/-- Two events that agree off a third: `|Pr[A] − Pr[B]| ≤ Pr[C]` when `A ↔ B` outside `C`. -/
theorem abs_uprob_sub_le {A B C : υ → Prop} (h : ∀ u, ¬ C u → (A u ↔ B u)) :
    |uprob A - uprob B| ≤ uprob C := by
  have h1 : uprob A ≤ uprob B + uprob C :=
    (uprob_mono fun u ha => by
      by_cases hc : C u
      · exact Or.inr hc
      · exact Or.inl ((h u hc).1 ha)).trans (uprob_or_le B C)
  have h2 : uprob B ≤ uprob A + uprob C :=
    (uprob_mono fun u hb => by
      by_cases hc : C u
      · exact Or.inr hc
      · exact Or.inl ((h u hc).2 hb)).trans (uprob_or_le A C)
  rw [abs_le]
  constructor <;> linarith

/-- **The statistical switch** ("agree off a bad event"): if the samplers `X`, `Y` on one seed
space agree at every seed outside `bad`, then `distAdv X Y D ≤ Pr_s[bad s]`.

**Proof sketch.** The acceptance events on `σ × ρ` agree outside `bad ∘ fst`
(`abs_uprob_sub_le`), whose probability is `Pr[bad]` (`uprob_fst`). -/
theorem distAdv_le_uprob_of_eq [Nonempty ρ] (X Y : σ → γ) (D : γ → ρ → Bool) (bad : σ → Prop)
    (h : ∀ s, ¬ bad s → X s = Y s) : distAdv X Y D ≤ uprob bad := by
  rw [distAdv_def, acceptProb_def, acceptProb_def, ← uprob_fst (β := ρ) bad]
  exact abs_uprob_sub_le fun z hz => by rw [h z.1 hz]

/-- **Acceptance as an average of sections**: `acceptProb X D` is the average over `a : σ` of
the acceptance probability of the section `t ↦ X (a, t)` (`uprob_prod` after reassociating).
`acceptProb X D = uexp fun a => acceptProb (fun t => X (a, t)) D`. -/
theorem acceptProb_eq_uexp_sections (X : σ × τ → γ) (D : γ → ρ → Bool) :
    acceptProb X D = uexp fun a => acceptProb (fun t => X (a, t)) D := by
  rw [acceptProb_def, ← uprob_comp_equiv (Equiv.prodAssoc σ τ ρ).symm, uprob_prod]
  simp only [acceptProb_def]
  rfl

/-- The average of a difference is at most the largest difference: some `a` has
`|uexp f − uexp g| ≤ |f a − g a|` (for nonempty `σ`). -/
theorem exists_abs_uexp_sub_le [Nonempty σ] (f g : σ → ℝ) :
    ∃ a, |uexp f - uexp g| ≤ |f a - g a| := by
  obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ (fun a => |f a - g a|)
    Finset.univ_nonempty
  refine ⟨a, ?_⟩
  have hc : (0 : ℝ) < Fintype.card σ := Nat.cast_pos.2 Fintype.card_pos
  rw [uexp_def, uexp_def, ← sub_div, abs_div, abs_of_pos hc, div_le_iff₀ hc, ← sum_sub_distrib]
  calc |∑ i, (f i - g i)| ≤ ∑ i, |f i - g i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : σ, |f a - g a| := sum_le_sum fun i _ => ha i (mem_univ i)
    _ = |f a - g a| * Fintype.card σ := by rw [sum_const, card_univ, nsmul_eq_mul, mul_comm]

/-- **Fixing coordinates** (the advice of a non-uniform reduction): for samplers `X`, `Y` on
`σ × τ` there is `a : σ` with `|acceptProb X D − acceptProb Y D| ≤
|acceptProb (X (a, ·)) D − acceptProb (Y (a, ·)) D|` (`acceptProb_eq_uexp_sections`,
`exists_abs_uexp_sub_le`). -/
theorem exists_abs_sub_le_sections [Nonempty σ] (X Y : σ × τ → γ) (D : γ → ρ → Bool) :
    ∃ a, |acceptProb X D - acceptProb Y D| ≤
      |acceptProb (fun t => X (a, t)) D - acceptProb (fun t => Y (a, t)) D| := by
  rw [acceptProb_eq_uexp_sections X, acceptProb_eq_uexp_sections Y]
  exact exists_abs_uexp_sub_le _ _

/-- **A negligible function times a polynomial is negligible**: for `p : PolyExpr`,
`n ↦ p(n) · μ(n)` is negligible.
`Negligible fun n => (p.eval n : ℝ) * μ n`.

**Proof sketch.** `p(n) ≤ C (n + 1)^c ≤ C 2^c n^c` for `n ≥ 1` (`PolyExpr.eval_le`), and
`n ↦ (C 2^c) (n^c μ(n))` is negligible (`Negligible.mul_pow`, `Negligible.const_mul`). -/
theorem negligible_polyExpr_mul {μ : ℕ → ℝ} (hμ : Negligible μ) (p : PolyExpr) :
    Negligible fun n => (p.eval n : ℝ) * μ n := by
  obtain ⟨C, c, hC⟩ := p.eval_le
  refine ((hμ.mul_pow c).const_mul ((C : ℝ) * 2 ^ c)).mono ⟨1, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (p.eval n : ℝ) ≤ C * 2 ^ c * (n : ℝ) ^ c := by
    have h1 : (p.eval n : ℝ) ≤ C * ((n : ℝ) + 1) ^ c := by exact_mod_cast hC n
    have h2 : ((n : ℝ) + 1) ^ c ≤ (2 * (n : ℝ)) ^ c :=
      pow_le_pow_left₀ (by positivity) (by linarith) c
    rw [mul_pow] at h2
    nlinarith [show (0 : ℝ) ≤ C from Nat.cast_nonneg C]
  rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (p.eval n)),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ C * 2 ^ c), abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ c), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hp (abs_nonneg _)

end TCSlib.Cryptography.SecureComputation.ComposeProb

## ===== TCSlib/Cryptography/SecureComputation/ComposeSecurity/Reductions.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Complexity.Randomized.Closure

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machines with advice-dependent pre- and post-processing and extra coins

Two closure properties of non-uniform PPT machines used by the simulators and reductions of the
composition theorem [Gol04, §7.3.1, proof of Theorem 7.3.3]: a machine may hand its argument,
together with an advice string and a block of extra coins, to a polynomial-time pre-processor
before running another machine (`ComposeSim.exists_pre`: a reduction `D ∘ Ψ`), or post-process
another machine's output with an advice string and extra coins (`ComposeSim.exists_post`: a
simulator that runs a simulator and then completes its output). Both combine the closure
catalogue of `Complexity/Randomized/Closure.lean` (`exists_split`, `exists_withAdvice`,
`exists_seq`) in one raw function of the layout (`NUPPT.ofPolyTime`).

## Main results

* `ComposeSim.exists_pre`, `ComposeSim.exists_post`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §2.1 (closure of non-uniform PPT machines under composition, Definition 26.8).
-/

namespace TCSlib.Cryptography.SecureComputation.ComposeSim

open Complexity Turing Complexity.NUPPT

/-- **Pre-processing with advice and extra coins**: for an `NUPPT` `D`, a polynomial-time `Ψ`, a
polynomially bounded advice family `α` and a coin polynomial `p`, there is an `NUPPT` `B` with
coins `p + D.coins` such that `B(1^n, y; r) = D(1^n, Ψ ⟨⟨1^n, α n⟩, ⟨y, r_{<p(n)}⟩⟩; r_{≥p(n)})`.

**Proof sketch.** Advice `⟨D.advice n, α n⟩`; the raw function reads `1^n`, the argument, the two
advice halves and the coins from the layout (`inParam`, `inArg`, `inAdvice`, `inCoins`), cuts the
coins at `p(n)` (`polyTimeComputable_pairTakePoly`, `polyTimeComputable_pairDropPoly`), applies
`Ψ` and runs `D.output` (`NUPPT.polyTimeComputable_output`); the equation is `runAtL_ofPolyTime`
with the projection identities. -/
theorem exists_pre (D : NUPPT) {Ψ : List Bool → List Bool} (hΨ : PolyTimeComputable Ψ)
    (α : ℕ → List Bool) (a : PolyExpr) (hα : ∀ n, (α n).length ≤ a.eval n) (p : PolyExpr) :
    ∃ B : NUPPT, B.coins = .add p D.coins ∧ ∀ n y r, B.runAtL n y r =
      D.runAtL n (Ψ (pairEncode (pairEncode (List.replicate n true) (α n))
        (pairEncode y (r.take (p.eval n))))) (r.drop (p.eval n)) := by
  have hcut := polyTimeComputable_inParam.pairEncode polyTimeComputable_inCoins
  have hpre := hΨ.comp' ((polyTimeComputable_inParam.pairEncode
      (polyTimeComputable_pairSndD.comp' polyTimeComputable_inAdvice)).pairEncode
    (polyTimeComputable_inArg.pairEncode ((polyTimeComputable_pairTakePoly p).comp' hcut)))
  have hF := D.polyTimeComputable_output.comp' (polyTimeComputable_layout polyTimeComputable_inParam
    hpre (polyTimeComputable_pairFstD.comp' polyTimeComputable_inAdvice)
    ((polyTimeComputable_pairDropPoly p).comp' hcut))
  have hadv : ∀ n, (pairEncode (D.advice n) (α n)).length ≤
      (PolyExpr.add (.add (.mul (.const 2) D.adv) (.const 2)) a).eval n := fun n => by
    rw [length_pairEncode]
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    have h₁ := D.advice_length n
    have h₂ := hα n
    omega
  refine ⟨ofPolyTime hF (.add p D.coins) _ (fun n => pairEncode (D.advice n) (α n)) hadv,
    coins_ofPolyTime _ _ _ _ _, fun n y r => ?_⟩
  rw [runAtL_ofPolyTime, runAtL_eq_output_layout]
  simp only [advInput_eq, ← layout_eq, inParam_layout, inArg_layout, inAdvice_layout,
    inCoins_layout, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]

/-- **Post-processing with advice and extra coins**: for an `NUPPT` `A`, a polynomial-time `Ψ`,
a polynomially bounded advice family `α` and a coin polynomial `p`, there is an `NUPPT` `B` with
coins `A.coins + p` such that
`B(1^n, y; r) = Ψ ⟨⟨1^n, α n⟩, ⟨A(1^n, y; r_{<A.coins(n)}), r_{≥A.coins(n)}⟩⟩`.

**Proof sketch.** Advice `⟨A.advice n, α n⟩`; the raw function cuts the coins at `A.coins(n)`,
runs `A.output` on the layout with the first advice half and the head of the coins, and applies
`Ψ` to the parameter, the second advice half, `A`'s output and the tail of the coins
(`runAtL_ofPolyTime` with the projection identities). -/
theorem exists_post (A : NUPPT) {Ψ : List Bool → List Bool} (hΨ : PolyTimeComputable Ψ)
    (α : ℕ → List Bool) (a : PolyExpr) (hα : ∀ n, (α n).length ≤ a.eval n) (p : PolyExpr) :
    ∃ B : NUPPT, B.coins = .add A.coins p ∧ ∀ n y r, B.runAtL n y r =
      Ψ (pairEncode (pairEncode (List.replicate n true) (α n))
        (pairEncode (A.runAtL n y (r.take (A.coinLen n))) (r.drop (A.coinLen n)))) := by
  have hcut := polyTimeComputable_inParam.pairEncode polyTimeComputable_inCoins
  have hout := A.polyTimeComputable_output.comp' (polyTimeComputable_layout
    polyTimeComputable_inParam polyTimeComputable_inArg
    (polyTimeComputable_pairFstD.comp' polyTimeComputable_inAdvice)
    ((polyTimeComputable_pairTakePoly A.coins).comp' hcut))
  have hF := hΨ.comp' ((polyTimeComputable_inParam.pairEncode
      (polyTimeComputable_pairSndD.comp' polyTimeComputable_inAdvice)).pairEncode
    (hout.pairEncode ((polyTimeComputable_pairDropPoly A.coins).comp' hcut)))
  have hadv : ∀ n, (pairEncode (A.advice n) (α n)).length ≤
      (PolyExpr.add (.add (.mul (.const 2) A.adv) (.const 2)) a).eval n := fun n => by
    rw [length_pairEncode]
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    have h₁ := A.advice_length n
    have h₂ := hα n
    omega
  refine ⟨ofPolyTime hF (.add A.coins p) _ (fun n => pairEncode (A.advice n) (α n)) hadv,
    coins_ofPolyTime _ _ _ _ _, fun n y r => ?_⟩
  rw [runAtL_ofPolyTime, runAtL_eq_output_layout, coinLen_eq]
  simp only [advInput_eq, ← layout_eq, inParam_layout, inArg_layout, inAdvice_layout,
    inCoins_layout, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]

end TCSlib.Cryptography.SecureComputation.ComposeSim

## ===== TCSlib/Cryptography/SecureComputation/ComposeSecurity/Runs.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ComposePhases
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Assembly

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The real samples of the composed protocol, run by run

Step 2 of the proof of the composition theorem [Gol04, §7.3.1, proof of Theorem 7.3.3]: the coins
of an honest execution of `H.compose ρ` on `1^n` are the `main`-tapes `m` and one pair of
`ρ`-tapes `t j` per call (`composeCoins`), and when every run's outputs are the ideal answers
(`GoodRuns`), the real sample of either side is the assembled view (`ComposeSim.asmView`) of the
real views of the runs (`realViewA`, `realViewB`), with the main phase and the other party's output
those of the hybrid execution on the `main`-tapes (`realA_compose_eq`, `realB_compose_eq`, using
`hM`).

## Main definitions

* `ComposeSim.splitCoins`: `{0,1}^a × ({0,1}^b)^q ≃ {0,1}^m` for `m = a + q·b`.
* `HybridProtocol.composeCoins`: the coins of `H.compose ρ` as `main`-tapes and run tapes.
* `HybridProtocol.inA`, `inB`: the call inputs as strings.
* `HybridProtocol.realViewA`, `realViewB`: the encoded views of a party in the honest runs.
* `HybridProtocol.GoodRuns`: every run's outputs are the ideal answers.

## Main results

* `ComposeSim.ofFn_splitCoins`, `HybridProtocol.ofFn_composeCoins_fst`, `_snd`.
* `HybridProtocol.answersRealA_eq_answersA`, `answersRealB_eq_answersB`: under `GoodRuns` the honest
  answers are the ideal ones.
* `HybridProtocol.realA_compose_eq`, `realB_compose_eq`: the real samples under `GoodRuns`.

## References

* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
  University Press, 2004, §7.3.1 (the proof of Theorem 7.3.3).
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing TCSlib.Cryptography ComposeMachines ComposeSim Compose

namespace ComposeSim

/-- **A tape and `q` blocks as one string**: `{0,1}^a × ({0,1}^b)^q ≃ {0,1}^m` for
`m = a + q·b`, the tape followed by the blocks in order (`Fin.appendEquiv`, `FunFamily.blocks`). -/
def splitCoins {m a q b : ℕ} (h : m = a + q * b) :
    (Fin a → Bool) × (Fin q → Fin b → Bool) ≃ (Fin m → Bool) :=
  ((Equiv.refl (Fin a → Bool)).prodCongr (FunFamily.blocks q b).symm).trans
    ((Fin.appendEquiv a (q * b)).trans (Equiv.arrowCongr (finCongr h.symm) (Equiv.refl Bool)))

/-- The defining equation of `splitCoins` (see `splitCoins`).
`splitCoins h = ((Equiv.refl (Fin a → Bool)).prodCongr (FunFamily.blocks q b).symm).trans
((Fin.appendEquiv a (q * b)).trans (Equiv.arrowCongr (finCongr h.symm) (Equiv.refl Bool)))`. -/
theorem splitCoins_eq {m a q b : ℕ} (h : m = a + q * b) :
    splitCoins h = ((Equiv.refl (Fin a → Bool)).prodCongr (FunFamily.blocks q b).symm).trans
      ((Fin.appendEquiv a (q * b)).trans
        (Equiv.arrowCongr (finCongr h.symm) (Equiv.refl Bool))) := rfl

/-- The blocks as one string: `⟦(blocks q b).symm t⟧ = ⟦t 0⟧ ++ ⋯ ++ ⟦t (q − 1)⟧`.

**Proof sketch.** `List.ofFn_mul` writes `⟦v⟧` for `v : Fin (q·b) → Bool` as the concatenation
of `q` blocks of `b` bits, entry `j` of block `i` being `v (i·b + j)`; by
`FunFamily.blocks_symm_apply` that is `t i j`, since `(i·b + j) / b = i` and
`(i·b + j) % b = j` for `j < b`. -/
theorem ofFn_blocks_symm (q b : ℕ) (t : Fin q → Fin b → Bool) :
    List.ofFn ((FunFamily.blocks q b).symm t) = (List.ofFn fun j => List.ofFn (t j)).flatten := by
  rw [List.ofFn_mul]
  congr 1
  refine List.ofFn_inj.2 (funext fun i => List.ofFn_inj.2 (funext fun j => ?_))
  rw [FunFamily.blocks_symm_apply]
  have hj := j.2
  have hb : 0 < b := by omega
  congr 1
  · refine Fin.ext ?_
    rw [Fin.coe_divNat]
    show ((i : ℕ) * b + j) / b = i
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt hj, Nat.zero_add]
  · refine Fin.ext ?_
    rw [Fin.coe_modNat]
    show ((i : ℕ) * b + j) % b = j
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

/-- **The split coins as a string**: `⟦splitCoins h (u, t)⟧ = ⟦u⟧ ++ ⟦t 0⟧ ++ ⋯ ++ ⟦t (q − 1)⟧`. -/
theorem ofFn_splitCoins {m a q b : ℕ} (h : m = a + q * b) (u : Fin a → Bool)
    (t : Fin q → Fin b → Bool) :
    List.ofFn (splitCoins h (u, t)) =
      List.ofFn u ++ (List.ofFn fun j => List.ofFn (t j)).flatten := by
  rw [splitCoins_eq, Equiv.trans_apply, Equiv.trans_apply, ofFn_arrowCongr_finCongr]
  show List.ofFn (Fin.append u ((FunFamily.blocks q b).symm t)) = _
  rw [List.ofFn_fin_append, ofFn_blocks_symm]

/-- The first `a` bits of `splitCoins h (u, t)` are `u`.
`(List.ofFn (splitCoins h (u, t))).take a = List.ofFn u`. -/
theorem take_ofFn_splitCoins {m a q b : ℕ} (h : m = a + q * b) (u : Fin a → Bool)
    (t : Fin q → Fin b → Bool) : (List.ofFn (splitCoins h (u, t))).take a = List.ofFn u := by
  rw [ofFn_splitCoins, List.take_left' List.length_ofFn]

/-- Block `j < q` of `splitCoins h (u, t)` is `t j`:
`runTape a b j ⟦splitCoins h (u, t)⟧ = ⟦t j⟧` (`Compose.runTape_eq`). -/
theorem runTape_ofFn_splitCoins {m a q b : ℕ} (h : m = a + q * b) (u : Fin a → Bool)
    (t : Fin q → Fin b → Bool) (j : Fin q) :
    runTape a b j (List.ofFn (splitCoins h (u, t))) = List.ofFn (t j) := by
  rw [runTape_eq, ofFn_splitCoins, ← List.drop_drop, List.drop_left' List.length_ofFn]
  have hblk := coinBlock_flatten (B := b) (List.ofFn fun j => List.ofFn (t j))
    (fun c hc => by
      obtain ⟨i, -, rfl⟩ := List.mem_ofFn.1 hc
      exact List.length_ofFn) j (by rw [List.length_ofFn]; exact j.2)
  rw [coinBlock_eq] at hblk
  rw [hblk, List.getElem_ofFn]

/-- **A concatenation over `L·R` indices in `L` blocks of `R`**:
`(range (L·R)).flatMap f = (range L).flatMap fun j => (range R).flatMap fun p => f (R·j + p)`. -/
theorem flatMap_range_mul (f : ℕ → List Bool) (R : ℕ) : ∀ L,
    (List.range (L * R)).flatMap f =
      (List.range L).flatMap fun j => (List.range R).flatMap fun p => f (R * j + p)
  | 0 => by rw [Nat.zero_mul, List.range_zero, List.flatMap_nil, List.flatMap_nil]
  | L + 1 => by
    rw [Nat.succ_mul, List.range_add, List.flatMap_append, flatMap_range_mul f R L,
      List.range_succ, List.flatMap_append, List.flatMap_singleton, List.flatMap_map,
      Nat.mul_comm L R]

end ComposeSim

namespace HybridProtocol

/-! ### Coins of the composed protocol -/

section Coins

variable {G : Functionality} (H : HybridProtocol G) (ρ : Protocol)

/-- Alice's composed coin length at `1^n` is `main.P.coins + calls(n)·ρ.P.coins`.
`(H.compose ρ).P.coinLen (List.replicate n true).length = H.main.P.coinLen (List.replicate n
true).length + H.calls.eval n * ρ.P.coinLen (List.replicate n true).length`. -/
theorem composeP_coinLen_eq (n : ℕ) :
    (H.compose ρ).P.coinLen (List.replicate n true).length =
      H.main.P.coinLen (List.replicate n true).length +
        H.calls.eval n * ρ.P.coinLen (List.replicate n true).length := by
  rw [compose_P_coinLen, List.length_replicate]

/-- Bob's composed coin length at `1^n` is `main.V.coins + calls(n)·ρ.V.coins`.
`(H.compose ρ).V.coinLen (List.replicate n true).length = H.main.V.coinLen (List.replicate n
true).length + H.calls.eval n * ρ.V.coinLen (List.replicate n true).length`. -/
theorem composeV_coinLen_eq (n : ℕ) :
    (H.compose ρ).V.coinLen (List.replicate n true).length =
      H.main.V.coinLen (List.replicate n true).length +
        H.calls.eval n * ρ.V.coinLen (List.replicate n true).length := by
  rw [compose_V_coinLen, List.length_replicate]

/-- **The coins of `H.compose ρ` at `1^n`** as the `main`-tapes and one pair of `ρ`-tapes per
call: Alice's tape is her `main`-tape followed by her `ρ`-tapes, Bob's likewise.
`H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) ≃ (H.compose
ρ).ExecCoins (H.compose ρ).P (List.replicate n true)`. -/
def composeCoins (n : ℕ) :
    H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) ≃
      (H.compose ρ).ExecCoins (H.compose ρ).P (List.replicate n true) :=
  ((Equiv.refl (H.Coins n)).prodCongr (Equiv.arrowProdEquivProdArrow _ _ _)).trans
    ((Equiv.prodProdProdComm _ _ _ _).trans
      ((splitCoins (H.composeP_coinLen_eq ρ n)).prodCongr
        (splitCoins (H.composeV_coinLen_eq ρ n))))

/-- Alice's composed tape is `splitCoins` of her `main`-tape and her run tapes.
`(H.composeCoins ρ n (m, t)).1 = splitCoins (H.composeP_coinLen_eq ρ n) (m.1, fun j => (t j).1)`. -/
theorem composeCoins_fst (n : ℕ) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) :
    (H.composeCoins ρ n (m, t)).1 =
      splitCoins (H.composeP_coinLen_eq ρ n) (m.1, fun j => (t j).1) :=
  rfl

/-- Bob's composed tape is `splitCoins` of his `main`-tape and his run tapes.
`(H.composeCoins ρ n (m, t)).2 = splitCoins (H.composeV_coinLen_eq ρ n) (m.2, fun j => (t j).2)`. -/
theorem composeCoins_snd (n : ℕ) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) :
    (H.composeCoins ρ n (m, t)).2 =
      splitCoins (H.composeV_coinLen_eq ρ n) (m.2, fun j => (t j).2) :=
  rfl

/-- Alice's composed tape: `⟦(composeCoins (m, t)).1⟧ = ⟦m.1⟧ ++ ⟦(t 0).1⟧ ++ ⋯`. -/
theorem ofFn_composeCoins_fst (n : ℕ) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) :
    List.ofFn (H.composeCoins ρ n (m, t)).1 =
      List.ofFn m.1 ++ (List.ofFn fun j => List.ofFn (t j).1).flatten :=
  ofFn_splitCoins (H.composeP_coinLen_eq ρ n) m.1 fun j => (t j).1

/-- Bob's composed tape: `⟦(composeCoins (m, t)).2⟧ = ⟦m.2⟧ ++ ⟦(t 0).2⟧ ++ ⋯`. -/
theorem ofFn_composeCoins_snd (n : ℕ) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) :
    List.ofFn (H.composeCoins ρ n (m, t)).2 =
      List.ofFn m.2 ++ (List.ofFn fun j => List.ofFn (t j).2).flatten :=
  ofFn_splitCoins (H.composeV_coinLen_eq ρ n) m.2 fun j => (t j).2

end Coins

/-! ### The runs of an honest execution -/

section Runs

variable {G : Functionality} (H : HybridProtocol G) (ρ : Protocol)

/-- **Alice's input to call `j`** as a string: `⟦callA(n, zA, rA, j)⟧` for `j < calls(n)`, `[]`
otherwise. -/
def inA (n : ℕ) (zA rA : List Bool) (j : ℕ) : List Bool :=
  if h : j < H.calls.eval n then List.ofFn (H.callA n zA rA ⟨j, h⟩) else []

/-- The defining equation of `inA`: `inA n zA rA j = ⟦callA(n, zA, rA, j)⟧` for `j < calls(n)`,
`[]` otherwise. -/
theorem inA_eq (n : ℕ) (zA rA : List Bool) (j : ℕ) :
    H.inA n zA rA j =
      if h : j < H.calls.eval n then List.ofFn (H.callA n zA rA ⟨j, h⟩) else [] := rfl

/-- **Bob's input to call `j`** as a string: `⟦callB(n, zB, rB, j)⟧` for `j < calls(n)`, `[]`
otherwise. -/
def inB (n : ℕ) (zB rB : List Bool) (j : ℕ) : List Bool :=
  if h : j < H.calls.eval n then List.ofFn (H.callB n zB rB ⟨j, h⟩) else []

/-- The defining equation of `inB`: `inB n zB rB j = ⟦callB(n, zB, rB, j)⟧` for `j < calls(n)`,
`[]` otherwise. -/
theorem inB_eq (n : ℕ) (zB rB : List Bool) (j : ℕ) :
    H.inB n zB rB j =
      if h : j < H.calls.eval n then List.ofFn (H.callB n zB rB ⟨j, h⟩) else [] := rfl

/-- The call inputs do not depend on how the parameter is written:
`N = n → ⟦callA(N, zA, rA, j)⟧ = ⟦callA(n, zA, rA, j)⟧`. -/
theorem ofFn_callA_congr {N n : ℕ} (hN : N = n) (zA rA : List Bool) (j : ℕ)
    (h₁ : j < H.calls.eval N) (h₂ : j < H.calls.eval n) :
    List.ofFn (H.callA N zA rA ⟨j, h₁⟩) = List.ofFn (H.callA n zA rA ⟨j, h₂⟩) := by
  subst hN
  rfl

/-- The call inputs do not depend on how the parameter is written:
`N = n → ⟦callB(N, zB, rB, j)⟧ = ⟦callB(n, zB, rB, j)⟧`. -/
theorem ofFn_callB_congr {N n : ℕ} (hN : N = n) (zB rB : List Bool) (j : ℕ)
    (h₁ : j < H.calls.eval N) (h₂ : j < H.calls.eval n) :
    List.ofFn (H.callB N zB rB ⟨j, h₁⟩) = List.ofFn (H.callB n zB rB ⟨j, h₂⟩) := by
  subst hN
  rfl

/-- **The run inputs of `H.compose ρ` at `1^n` are the call inputs**: for `j < calls(n)`,
`runInputA 1^n zA ⟦(composeCoins (m, t)).1⟧ j = inA n zA ⟦m.1⟧ j`
(`runInputA_of_lt`, `take_ofFn_splitCoins`). -/
theorem runInputA_composeCoins (n : ℕ) (zA : List Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) (j : ℕ) :
    H.runInputA (List.replicate n true) zA (List.ofFn (H.composeCoins ρ n (m, t)).1) j =
      H.inA n zA (List.ofFn m.1) j := by
  have hN : (List.replicate n true).length = n := List.length_replicate
  rw [inA_eq]
  by_cases hj : j < H.calls.eval n
  · have hj' : j < H.calls.eval (List.replicate n true).length := by rw [hN]; exact hj
    rw [dif_pos hj, H.runInputA_of_lt _ _ _ hj', ← Strategy.coinLen_eq,
      composeCoins_fst, take_ofFn_splitCoins (H.composeP_coinLen_eq ρ n)]
    exact H.ofFn_callA_congr hN _ _ j hj' hj
  · rw [dif_neg hj, H.runInputA_of_ge _ _ _ (by rw [hN]; omega)]

/-- Bob's run inputs at `1^n` are his call inputs (as `runInputA_composeCoins`).
`H.runInputB (List.replicate n true) zB (List.ofFn (H.composeCoins ρ n (m, t)).2) j = H.inB n zB
(List.ofFn m.2) j`. -/
theorem runInputB_composeCoins (n : ℕ) (zB : List Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) (j : ℕ) :
    H.runInputB (List.replicate n true) zB (List.ofFn (H.composeCoins ρ n (m, t)).2) j =
      H.inB n zB (List.ofFn m.2) j := by
  have hN : (List.replicate n true).length = n := List.length_replicate
  rw [inB_eq]
  by_cases hj : j < H.calls.eval n
  · have hj' : j < H.calls.eval (List.replicate n true).length := by rw [hN]; exact hj
    rw [dif_pos hj, H.runInputB_of_lt _ _ _ hj', ← Strategy.coinLen_eq,
      composeCoins_snd, take_ofFn_splitCoins (H.composeV_coinLen_eq ρ n)]
    exact H.ofFn_callB_congr hN _ _ j hj' hj
  · rw [dif_neg hj, H.runInputB_of_ge _ _ _ (by rw [hN]; omega)]

/-- **The honest run `j` at `1^n` is `ρ`'s execution on the call inputs and the run tapes**:
`runExec 1^n zA zB ⟦c.1⟧ ⟦c.2⟧ j k = exec ρ.P ρ.V vF 1^n (inA j) (inB j) ⟦(t j).1⟧ ⟦(t j).2⟧ k`
for `c = composeCoins (m, t)` (`runExec_eq`, `runTape_ofFn_splitCoins`). -/
theorem runExec_composeCoins (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) (j : Fin (H.calls.eval n))
    (k : ℕ) :
    H.runExec ρ (List.replicate n true) zA zB (List.ofFn (H.composeCoins ρ n (m, t)).1)
        (List.ofFn (H.composeCoins ρ n (m, t)).2) j k =
      exec ρ.P ρ.V ρ.verifierFirst (List.replicate n true) (H.inA n zA (List.ofFn m.1) j)
        (H.inB n zB (List.ofFn m.2) j) (List.ofFn (t j).1) (List.ofFn (t j).2) k := by
  rw [runExec_eq, runInputA_composeCoins, runInputB_composeCoins, ← Strategy.coinLen_eq,
    ← Strategy.coinLen_eq, ← Strategy.coinLen_eq, ← Strategy.coinLen_eq, composeCoins_fst,
    composeCoins_snd,
    runTape_ofFn_splitCoins (H.composeP_coinLen_eq ρ n) m.1 (fun j => (t j).1) j,
    runTape_ofFn_splitCoins (H.composeV_coinLen_eq ρ n) m.2 (fun j => (t j).2) j]

/-- The message of `ρ`'s move `p` in the honest run `j` at `1^n` is the move of `ρ`'s execution on
the call inputs and the run tapes (`runMsg_eq`, as `runExec_composeCoins`).
`H.runMsg ρ (List.replicate n true) zA zB (List.ofFn (H.composeCoins ρ n (m, t)).1) (List.ofFn
(H.composeCoins ρ n (m, t)).2) j p = moveMsg ρ.P ρ.V ρ.verifierFirst (List.replicate n true) (H.inA
n zA (List.ofFn m.1) j) (H.inB n zB …`. -/
theorem runMsg_composeCoins (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) (j : Fin (H.calls.eval n))
    (p : ℕ) :
    H.runMsg ρ (List.replicate n true) zA zB (List.ofFn (H.composeCoins ρ n (m, t)).1)
        (List.ofFn (H.composeCoins ρ n (m, t)).2) j p =
      moveMsg ρ.P ρ.V ρ.verifierFirst (List.replicate n true) (H.inA n zA (List.ofFn m.1) j)
        (H.inB n zB (List.ofFn m.2) j) (List.ofFn (t j).1) (List.ofFn (t j).2) p := by
  rw [runMsg_eq, runInputA_composeCoins, runInputB_composeCoins, ← Strategy.coinLen_eq,
    ← Strategy.coinLen_eq, ← Strategy.coinLen_eq, ← Strategy.coinLen_eq, composeCoins_fst,
    composeCoins_snd,
    runTape_ofFn_splitCoins (H.composeP_coinLen_eq ρ n) m.1 (fun j => (t j).1) j,
    runTape_ofFn_splitCoins (H.composeV_coinLen_eq ρ n) m.2 (fun j => (t j).2) j]

/-- **Every run gives the ideal answers**: for every call `j`, Alice's and Bob's `ρ`-outputs in
the run on the call inputs and the tapes `t j` are `⟦f_A(callA_j, callB_j)⟧` and
`⟦f_B(callA_j, callB_j)⟧`.
`H.GoodRuns ρ n zA zB m t ↔ ∀ j : Fin (H.calls.eval n), ρ.outP (List.replicate n true) (H.inA n zA
(List.ofFn m.1) j) (H.inB n zB (List.ofFn m.2) j) (t j) = List.ofFn (G.f n (H.callA n zA (List.ofFn
m.1) j) (H.callB n zB (List.ofFn m.2) …`. -/
def GoodRuns (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) : Prop :=
  ∀ j : Fin (H.calls.eval n),
    ρ.outP (List.replicate n true) (H.inA n zA (List.ofFn m.1) j) (H.inB n zB (List.ofFn m.2) j)
        (t j) =
      List.ofFn (G.f n (H.callA n zA (List.ofFn m.1) j) (H.callB n zB (List.ofFn m.2) j)).1 ∧
    ρ.outV ρ.P (List.replicate n true) (H.inA n zA (List.ofFn m.1) j)
        (H.inB n zB (List.ofFn m.2) j) (t j) =
      List.ofFn (G.f n (H.callA n zA (List.ofFn m.1) j) (H.callB n zB (List.ofFn m.2) j)).2

/-- The defining property of `GoodRuns` (see `GoodRuns`).
`H.GoodRuns ρ n zA zB m t ↔ ∀ j : Fin (H.calls.eval n), ρ.outP (List.replicate n true) (H.inA n zA
(List.ofFn m.1) j) (H.inB n zB (List.ofFn m.2) j) (t j) = List.ofFn (G.f n (H.callA n zA (List.ofFn
m.1) j) (H.callB n zB (List.ofFn m.2) …`. -/
theorem goodRuns_iff (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) :
    H.GoodRuns ρ n zA zB m t ↔ ∀ j : Fin (H.calls.eval n),
      ρ.outP (List.replicate n true) (H.inA n zA (List.ofFn m.1) j)
          (H.inB n zB (List.ofFn m.2) j) (t j) =
        List.ofFn (G.f n (H.callA n zA (List.ofFn m.1) j) (H.callB n zB (List.ofFn m.2) j)).1 ∧
      ρ.outV ρ.P (List.replicate n true) (H.inA n zA (List.ofFn m.1) j)
          (H.inB n zB (List.ofFn m.2) j) (t j) =
        List.ofFn (G.f n (H.callA n zA (List.ofFn m.1) j) (H.callB n zB (List.ofFn m.2) j)).2 :=
  Iff.rfl

/-- **Under `GoodRuns`, Alice's honest answers are the ideal ones**:
`answersRealA 1^n zA zB ⟦c.1⟧ ⟦c.2⟧ = answersA n zA zB ⟦m.1⟧ ⟦m.2⟧` for `c = composeCoins (m, t)`.

**Proof sketch.** Both are concatenations over the calls `j < L` (`flatten_ofFn_eq_flatMap_range`;
`1^n` has length `n`). Block `j` of the honest answers is `padFin` of Alice's output of the run
on the call inputs and the run tapes (`runInputA_composeCoins`, `runExec_composeCoins`), which is
`ρ.outP` of that run (`Protocol.outP_eq`, `Protocol.transcriptWith_eq`), i.e. `⟦f_A(…)⟧` by
`GoodRuns`; padding a word of the right length is the identity (`ofFn_padFin`,
`padTo_of_length`). -/
theorem answersRealA_eq_answersA (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true))
    (hg : H.GoodRuns ρ n zA zB m t) :
    H.answersRealA ρ (List.replicate n true) zA zB (List.ofFn (H.composeCoins ρ n (m, t)).1)
        (List.ofFn (H.composeCoins ρ n (m, t)).2) =
      H.answersA n zA zB (List.ofFn m.1) (List.ofFn m.2) := by
  have hN : (List.replicate n true).length = n := List.length_replicate
  rw [answersRealA_eq, answersA_eq, flatten_ofFn_eq_flatMap_range (fun j =>
      List.ofFn (padFin (G.outA.eval (List.replicate n true).length)
        (ρ.P.next (List.replicate n true)
          (H.runInputA (List.replicate n true) zA (List.ofFn (H.composeCoins ρ n (m, t)).1) j)
          (runTape (H.main.P.coins.eval (List.replicate n true).length)
            (ρ.P.coins.eval (List.replicate n true).length) j
            (List.ofFn (H.composeCoins ρ n (m, t)).1))
          (H.runExec ρ (List.replicate n true) zA zB (List.ofFn (H.composeCoins ρ n (m, t)).1)
            (List.ofFn (H.composeCoins ρ n (m, t)).2) j
            (ρ.rounds.eval (List.replicate n true).length)).1))),
    show (List.ofFn fun j : Fin (H.calls.eval n) =>
        List.ofFn (G.f n (H.callA n zA (List.ofFn m.1) j) (H.callB n zB (List.ofFn m.2) j)).1
        ).flatten = (List.range (H.calls.eval n)).flatMap fun i => if h : i < H.calls.eval n then
          List.ofFn (G.f n (H.callA n zA (List.ofFn m.1) ⟨i, h⟩)
            (H.callB n zB (List.ofFn m.2) ⟨i, h⟩)).1 else [] by
      rw [← flatten_ofFn_eq_flatMap_range]
      exact congrArg List.flatten (List.ofFn_inj.2 (funext fun j => by rw [dif_pos j.2])),
    flatMap_range_congr (by rw [hN])]
  refine List.flatMap_congr fun j hj => ?_
  have hjn : j < H.calls.eval n := List.mem_range.1 hj
  rw [dif_pos hjn, runInputA_composeCoins, ← Strategy.coinLen_eq, ← Strategy.coinLen_eq,
    composeCoins_fst, runTape_ofFn_splitCoins (H.composeP_coinLen_eq ρ n) m.1 (fun j => (t j).1)
      ⟨j, hjn⟩, ← composeCoins_fst, runExec_composeCoins H ρ n zA zB m t ⟨j, hjn⟩,
    ← Protocol.transcriptWith_eq, ← Protocol.outP_eq, (hg ⟨j, hjn⟩).1, ofFn_padFin,
    padTo_of_length (by rw [List.length_ofFn, hN])]

/-- **Under `GoodRuns`, Bob's honest answers are the ideal ones**:
`answersRealB 1^n zA zB ⟦c.1⟧ ⟦c.2⟧ = answersB n zA zB ⟦m.1⟧ ⟦m.2⟧` for `c = composeCoins (m, t)`.

**Proof sketch.** As `answersRealA_eq_answersA`: block `j` of Bob's honest answers is `padFin` of
his output in run `j` on the call inputs and the run tapes (`runInputB_composeCoins`,
`runExec_composeCoins`), which is `ρ.outV` of that run (`Protocol.outV_eq`), i.e. `⟦f_B(…)⟧` by
`GoodRuns`; padding a word of the right length is the identity (`ofFn_padFin`,
`padTo_of_length`). -/
theorem answersRealB_eq_answersB (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true))
    (hg : H.GoodRuns ρ n zA zB m t) :
    H.answersRealB ρ (List.replicate n true) zA zB (List.ofFn (H.composeCoins ρ n (m, t)).1)
        (List.ofFn (H.composeCoins ρ n (m, t)).2) =
      H.answersB n zA zB (List.ofFn m.1) (List.ofFn m.2) := by
  have hN : (List.replicate n true).length = n := List.length_replicate
  rw [answersRealB_eq, answersB_eq, flatten_ofFn_eq_flatMap_range (fun j =>
      List.ofFn (padFin (G.outB.eval (List.replicate n true).length)
        (ρ.V.next (List.replicate n true)
          (H.runInputB (List.replicate n true) zB (List.ofFn (H.composeCoins ρ n (m, t)).2) j)
          (runTape (H.main.V.coins.eval (List.replicate n true).length)
            (ρ.V.coins.eval (List.replicate n true).length) j
            (List.ofFn (H.composeCoins ρ n (m, t)).2))
          (H.runExec ρ (List.replicate n true) zA zB (List.ofFn (H.composeCoins ρ n (m, t)).1)
            (List.ofFn (H.composeCoins ρ n (m, t)).2) j
            (ρ.rounds.eval (List.replicate n true).length)).2))),
    show (List.ofFn fun j : Fin (H.calls.eval n) =>
        List.ofFn (G.f n (H.callA n zA (List.ofFn m.1) j) (H.callB n zB (List.ofFn m.2) j)).2
        ).flatten = (List.range (H.calls.eval n)).flatMap fun i => if h : i < H.calls.eval n then
          List.ofFn (G.f n (H.callA n zA (List.ofFn m.1) ⟨i, h⟩)
            (H.callB n zB (List.ofFn m.2) ⟨i, h⟩)).2 else [] by
      rw [← flatten_ofFn_eq_flatMap_range]
      exact congrArg List.flatten (List.ofFn_inj.2 (funext fun j => by rw [dif_pos j.2])),
    flatMap_range_congr (by rw [hN])]
  refine List.flatMap_congr fun j hj => ?_
  have hjn : j < H.calls.eval n := List.mem_range.1 hj
  rw [dif_pos hjn, runInputB_composeCoins, ← Strategy.coinLen_eq, ← Strategy.coinLen_eq,
    composeCoins_snd, runTape_ofFn_splitCoins (H.composeV_coinLen_eq ρ n) m.2 (fun j => (t j).2)
      ⟨j, hjn⟩, ← composeCoins_snd, runExec_composeCoins H ρ n zA zB m t ⟨j, hjn⟩,
    ← Protocol.transcriptWith_eq (π := ρ) (P' := ρ.P), ← Protocol.outV_eq, (hg ⟨j, hjn⟩).2,
    ofFn_padFin, padTo_of_length (by rw [List.length_ofFn, hN])]

/-- **Under `GoodRuns`, the main phase is the hybrid execution on the `main`-tapes**:
`mainExec 1^n zA zB ⟦c.1⟧ ⟦c.2⟧ k = exec main.P main.V vF 1^n (privA n zA zB ⟦m.1⟧ ⟦m.2⟧)
(privB …) ⟦m.1⟧ ⟦m.2⟧ k` (`mainExec_eq`, the answers, `take_ofFn_splitCoins`). -/
theorem mainExec_composeCoins (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true))
    (hg : H.GoodRuns ρ n zA zB m t) (k : ℕ) :
    H.mainExec ρ (List.replicate n true) zA zB (List.ofFn (H.composeCoins ρ n (m, t)).1)
        (List.ofFn (H.composeCoins ρ n (m, t)).2) k =
      exec H.main.P H.main.V H.main.verifierFirst (List.replicate n true)
        (H.privA n zA zB (List.ofFn m.1) (List.ofFn m.2))
        (H.privB n zA zB (List.ofFn m.1) (List.ofFn m.2)) (List.ofFn m.1) (List.ofFn m.2) k := by
  rw [mainExec_eq, H.answersRealA_eq_answersA ρ n zA zB m t hg,
    H.answersRealB_eq_answersB ρ n zA zB m t hg, privA_eq, privB_eq, ← Strategy.coinLen_eq,
    ← Strategy.coinLen_eq, composeCoins_fst, composeCoins_snd,
    take_ofFn_splitCoins (H.composeP_coinLen_eq ρ n),
    take_ofFn_splitCoins (H.composeV_coinLen_eq ρ n)]

/-- **Alice's encoded views of the honest runs**: for `j < calls(n)`, her view of `ρ` on the call
inputs `inA j`, `inB j` and the tapes `t j`; `[]` otherwise. -/
def realViewA (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) (j : ℕ) : List Bool :=
  if h : j < H.calls.eval n then
    (ρ.viewP (List.replicate n true) (H.inA n zA (List.ofFn m.1) j)
      (H.inB n zB (List.ofFn m.2) j) (t ⟨j, h⟩)).encode
  else []

/-- The defining equation of `realViewA` (see `realViewA`).
`H.realViewA ρ n zA zB m t j = if h : j < H.calls.eval n then (ρ.viewP (List.replicate n true)
(H.inA n zA (List.ofFn m.1) j) (H.inB n zB (List.ofFn m.2) j) (t ⟨j, h⟩)).encode else []`. -/
theorem realViewA_eq (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) (j : ℕ) :
    H.realViewA ρ n zA zB m t j =
      if h : j < H.calls.eval n then
        (ρ.viewP (List.replicate n true) (H.inA n zA (List.ofFn m.1) j)
          (H.inB n zB (List.ofFn m.2) j) (t ⟨j, h⟩)).encode
      else [] := rfl

/-- **Bob's encoded views of the honest runs** (as `realViewA`, with `ρ.viewV`).
`H.realViewB ρ n zA zB m t j = if h : j < H.calls.eval n then (ρ.viewV (List.replicate n true)
(H.inA n zA (List.ofFn m.1) j) (H.inB n zB (List.ofFn m.2) j) (t ⟨j, h⟩)).encode else []`. -/
def realViewB (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) (j : ℕ) : List Bool :=
  if h : j < H.calls.eval n then
    (ρ.viewV (List.replicate n true) (H.inA n zA (List.ofFn m.1) j)
      (H.inB n zB (List.ofFn m.2) j) (t ⟨j, h⟩)).encode
  else []

/-- The defining equation of `realViewB` (see `realViewB`).
`H.realViewB ρ n zA zB m t j = if h : j < H.calls.eval n then (ρ.viewV (List.replicate n true)
(H.inA n zA (List.ofFn m.1) j) (H.inB n zB (List.ofFn m.2) j) (t ⟨j, h⟩)).encode else []`. -/
theorem realViewB_eq (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) (j : ℕ) :
    H.realViewB ρ n zA zB m t j =
      if h : j < H.calls.eval n then
        (ρ.viewV (List.replicate n true) (H.inA n zA (List.ofFn m.1) j)
          (H.inB n zB (List.ofFn m.2) j) (t ⟨j, h⟩)).encode
      else [] := rfl

/-- **The real sample of Alice's side under `GoodRuns`**: with `c = composeCoins (m, t)`,
`F.realA (H.compose ρ) n x y c` is the assembled view (`ComposeSim.asmView` with `ρ.P`'s coins,
Bob's moves read, no leading filler) of Alice's real run views, her input, her `main`-tape and
the hybrid main phase, paired with Bob's output in the hybrid execution on the `main`-tapes.

**Proof sketch.** `compose_viewP` and `compose_outV` (with `hM`) give the view and Bob's output.
Her tape is her `main`-tape followed by the run tapes (`ofFn_composeCoins_fst`), which are the
tapes of the run views, of exact length (`padTo_of_length`). Her messages are Bob's run messages
at the pairs, `L` blocks of `R` (`encodeMsgs_eq_flatMap`, `flatMap_range_mul`, `slotFromB_mul_add`),
which are the chunks `segW` of the received messages of the run views (`runExec_composeCoins`,
`exec_eq_map`, `segW_encodeMsgs`), followed by the main phase, the hybrid one under `GoodRuns`
(`mainExec_composeCoins`). -/
theorem realA_compose_eq {F : Functionality} (hM : ∀ n, 0 < H.main.rounds.eval n) (n : ℕ)
    (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true))
    (hg : H.GoodRuns ρ n (List.ofFn x) (List.ofFn y) m t) :
    F.realA (H.compose ρ) n x y (H.composeCoins ρ n (m, t)) =
      pairEncode (asmView H.calls ρ.rounds ρ.P.coins ρ.verifierFirst true 0
          (List.replicate n true) (List.ofFn x) (List.ofFn m.1)
          (Strategy.encodeMsgs (H.main.transcript (List.replicate n true)
            (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
            (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m).1)
          (H.realViewA ρ n (List.ofFn x) (List.ofFn y) m t))
        (H.main.outV H.main.P (List.replicate n true)
          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m) := by
  have hN : (List.replicate n true).length = n := List.length_replicate
  have hL : H.calls.eval (List.replicate n true).length = H.calls.eval n := by rw [hN]
  -- the tape: the `main`-tape followed by the run tapes
  have htape : List.ofFn (H.composeCoins ρ n (m, t)).1 = List.ofFn m.1 ++
      (List.range (H.calls.eval (List.replicate n true).length)).flatMap fun j =>
        padTo (ρ.P.coins.eval (List.replicate n true).length)
          (pairFstD (pairSndD (H.realViewA ρ n (List.ofFn x) (List.ofFn y) m t j))) := by
    have hT0 : (List.ofFn fun j => List.ofFn (t j).1).flatten =
        (List.range (H.calls.eval n)).flatMap fun j =>
          if h : j < H.calls.eval n then List.ofFn (t ⟨j, h⟩).1 else [] := by
      rw [← flatten_ofFn_eq_flatMap_range]
      exact congrArg List.flatten (List.ofFn_inj.2 (funext fun j => by rw [dif_pos j.2]))
    rw [ofFn_composeCoins_fst, hT0, flatMap_range_congr hL.symm]
    congr 1
    refine List.flatMap_congr fun j hj => ?_
    have hjn : j < H.calls.eval n := by rw [← hL]; exact List.mem_range.1 hj
    rw [dif_pos hjn, realViewA_eq, dif_pos hjn, Protocol.viewP_eq, View.encode_mk,
      pairSndD_pairEncode, pairFstD_pairEncode, padTo_of_length (by
        rw [List.length_ofFn, Strategy.coinLen_eq])]
  -- Bob's run messages at the pairs: the chunks of the received messages of Alice's run views
  have hmsgs : Strategy.encodeMsgs ((List.range (H.calls.eval (List.replicate n true).length *
      ρ.rounds.eval (List.replicate n true).length)).map
        (H.slotFromB ρ (List.replicate n true) (List.ofFn x) (List.ofFn y)
          (List.ofFn (H.composeCoins ρ n (m, t)).1) (List.ofFn (H.composeCoins ρ n (m, t)).2))) =
      (List.range (H.calls.eval (List.replicate n true).length)).flatMap fun j =>
        segW ρ.verifierFirst true (ρ.rounds.eval (List.replicate n true).length)
          (pairSndD (pairSndD (H.realViewA ρ n (List.ofFn x) (List.ofFn y) m t j))) := by
    rw [encodeMsgs_eq_flatMap, List.flatMap_map, flatMap_range_mul]
    refine List.flatMap_congr fun j hj => ?_
    have hjn : j < H.calls.eval n := by rw [← hL]; exact List.mem_range.1 hj
    rw [realViewA_eq, dif_pos hjn, Protocol.viewP_eq, View.encode_mk, pairSndD_pairEncode,
      pairSndD_pairEncode, Protocol.transcriptWith_eq, exec_eq_map,
      show (List.range (ρ.rounds.eval (List.replicate n true).length)).filter
          (moverIsV ρ.verifierFirst) =
        (List.range (ρ.rounds.eval (List.replicate n true).length)).filter
          (fun q => moverIsV ρ.verifierFirst q == true) from
        List.filter_congr fun q _ => (beq_true _).symm, segW_encodeMsgs]
    refine List.flatMap_congr fun p hp => ?_
    rw [slotFromB_mul_add H ρ _ _ _ _ _ (List.mem_range.1 hp), beq_true,
      runMsg_composeCoins H ρ n _ _ m t ⟨j, hjn⟩ p]
  have hmain := H.mainExec_composeCoins ρ n (List.ofFn x) (List.ofFn y) m t hg
    (H.main.rounds.eval (List.replicate n true).length)
  rw [Functionality.realA_eq, compose_viewP, compose_outV H ρ _ _ _ _ (hM _), View.encode_mk,
    asmView_eq, encodeMsgs_append, hmsgs, hmain, H.answersRealB_eq_answersB ρ n _ _ m t hg, htape,
    List.replicate_zero, Strategy.encodeMsgs_nil, List.append_nil,
    Protocol.transcript_eq_transcriptWith, Protocol.transcriptWith_eq, Protocol.outV_eq,
    Protocol.transcriptWith_eq, privB_eq, ← Strategy.coinLen_eq H.main.V, composeCoins_snd,
    take_ofFn_splitCoins (H.composeV_coinLen_eq ρ n), ← privB_eq]

/-- **The real sample of Bob's side under `GoodRuns`**: with `c = composeCoins (m, t)`,
`F.realB (H.compose ρ) n x y c` is the assembled view (`ComposeSim.asmView` with `ρ.V`'s coins,
Alice's moves read, `lead` leading fillers) of Bob's real run views, his input, his `main`-tape
and the hybrid main phase, paired with Alice's output in the hybrid execution.

**Proof sketch.** As `realA_compose_eq`, with `compose_viewV`, `compose_outP`, the second
components, `slotFromA_mul_add` and the leading fillers between the runs and the main phase. -/
theorem realB_compose_eq {F : Functionality} (hM : ∀ n, 0 < H.main.rounds.eval n) (n : ℕ)
    (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true))
    (hg : H.GoodRuns ρ n (List.ofFn x) (List.ofFn y) m t) :
    F.realB (H.compose ρ) n x y (H.composeCoins ρ n (m, t)) =
      pairEncode (asmView H.calls ρ.rounds ρ.V.coins ρ.verifierFirst false H.lead
          (List.replicate n true) (List.ofFn y) (List.ofFn m.2)
          (Strategy.encodeMsgs (H.main.transcript (List.replicate n true)
            (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
            (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m).2)
          (H.realViewB ρ n (List.ofFn x) (List.ofFn y) m t))
        (H.main.outP (List.replicate n true)
          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m) := by
  have hN : (List.replicate n true).length = n := List.length_replicate
  have hL : H.calls.eval (List.replicate n true).length = H.calls.eval n := by rw [hN]
  -- the tape: the `main`-tape followed by the run tapes
  have htape : List.ofFn (H.composeCoins ρ n (m, t)).2 = List.ofFn m.2 ++
      (List.range (H.calls.eval (List.replicate n true).length)).flatMap fun j =>
        padTo (ρ.V.coins.eval (List.replicate n true).length)
          (pairFstD (pairSndD (H.realViewB ρ n (List.ofFn x) (List.ofFn y) m t j))) := by
    have hT0 : (List.ofFn fun j => List.ofFn (t j).2).flatten =
        (List.range (H.calls.eval n)).flatMap fun j =>
          if h : j < H.calls.eval n then List.ofFn (t ⟨j, h⟩).2 else [] := by
      rw [← flatten_ofFn_eq_flatMap_range]
      exact congrArg List.flatten (List.ofFn_inj.2 (funext fun j => by rw [dif_pos j.2]))
    rw [ofFn_composeCoins_snd, hT0, flatMap_range_congr hL.symm]
    congr 1
    refine List.flatMap_congr fun j hj => ?_
    have hjn : j < H.calls.eval n := by rw [← hL]; exact List.mem_range.1 hj
    rw [dif_pos hjn, realViewB_eq, dif_pos hjn, Protocol.viewV_eq, View.encode_mk,
      pairSndD_pairEncode, pairFstD_pairEncode, padTo_of_length (by
        rw [List.length_ofFn, Strategy.coinLen_eq])]
  -- Alice's run messages at the pairs: the chunks of the received messages of Bob's run views
  have hmsgs : Strategy.encodeMsgs ((List.range (H.calls.eval (List.replicate n true).length *
      ρ.rounds.eval (List.replicate n true).length)).map
        (H.slotFromA ρ (List.replicate n true) (List.ofFn x) (List.ofFn y)
          (List.ofFn (H.composeCoins ρ n (m, t)).1) (List.ofFn (H.composeCoins ρ n (m, t)).2))) =
      (List.range (H.calls.eval (List.replicate n true).length)).flatMap fun j =>
        segW ρ.verifierFirst false (ρ.rounds.eval (List.replicate n true).length)
          (pairSndD (pairSndD (H.realViewB ρ n (List.ofFn x) (List.ofFn y) m t j))) := by
    rw [encodeMsgs_eq_flatMap, List.flatMap_map, flatMap_range_mul]
    refine List.flatMap_congr fun j hj => ?_
    have hjn : j < H.calls.eval n := by rw [← hL]; exact List.mem_range.1 hj
    rw [realViewB_eq, dif_pos hjn, Protocol.viewV_eq, View.encode_mk, pairSndD_pairEncode,
      pairSndD_pairEncode, Protocol.transcriptWith_eq, exec_eq_map,
      show (List.range (ρ.rounds.eval (List.replicate n true).length)).filter
          (fun i => !moverIsV ρ.verifierFirst i) =
        (List.range (ρ.rounds.eval (List.replicate n true).length)).filter
          (fun q => moverIsV ρ.verifierFirst q == false) from
        List.filter_congr fun q _ => (beq_false _).symm, segW_encodeMsgs]
    refine List.flatMap_congr fun p hp => ?_
    rw [slotFromA_mul_add H ρ _ _ _ _ _ (List.mem_range.1 hp),
      runMsg_composeCoins H ρ n _ _ m t ⟨j, hjn⟩ p]
    cases moverIsV ρ.verifierFirst p <;> rfl
  have hmain := H.mainExec_composeCoins ρ n (List.ofFn x) (List.ofFn y) m t hg
    (H.main.rounds.eval (List.replicate n true).length)
  rw [Functionality.realB_eq, compose_viewV, compose_outP H ρ _ _ _ _ (hM _), View.encode_mk,
    asmView_eq, encodeMsgs_append, encodeMsgs_append, hmsgs, hmain,
    H.answersRealA_eq_answersA ρ n _ _ m t hg, htape, Protocol.transcript_eq_transcriptWith,
    Protocol.transcriptWith_eq, Protocol.outP_eq, Protocol.transcriptWith_eq, privA_eq,
    ← Strategy.coinLen_eq H.main.P, composeCoins_fst,
    take_ofFn_splitCoins (H.composeP_coinLen_eq ρ n), ← privA_eq]

end Runs

end HybridProtocol

end TCSlib.Cryptography.SecureComputation

## ===== TCSlib/Cryptography/SecureComputation/ComposeSecurity/SideA.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Template
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Correct
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Chain
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Sim
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Lengths

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The composition theorem: Alice's side

Steps 1–5 of the proof of the composition theorem [Gol04, §7.3.1, proof of Theorem 7.3.3] for
Alice's real and ideal samples of `H.compose ρ`. On the `main`-tapes `m`, a run word `V j` per
call and the sample `sampleA m V` (the assembled view of `V`, her input, her `main`-tape and the
hybrid main phase, paired with Bob's output in `main`):
1. under `GoodRuns` the real sample is `sampleA m (real views)` (`realA_compose_sampleA`); the
   bad event has probability at most `L(n) ε_c(n)` (`uprob_not_goodRuns_le`, `exists_correct`);
2. the hybrid argument replaces the real views by `ρ`'s simulator, at most `ε₂(n)` per run
   (`exists_gapA`: the reduction `exists_gap_le` with a polynomially long template,
   `exists_tmplA_bound`; `abs_chain_le`);
3. `sampleA m (simulated views)` is `D ∘ Φ` on the hybrid real sample, and `D` on the simulator
   `S_A` is `D ∘ Φ` on the hybrid ideal sample (`acceptProb_realA_dPhi`, `acceptProb_post_pre`),
   so `H.HBCSecure F` bounds the rest (`exists_simA`).

## Main definitions

* `HybridProtocol.viewRunA`, `simRunA`: Alice's real and simulated run words.
* `HybridProtocol.sampleA`: Alice's sample from run words.

## Main results

* `HybridProtocol.realA_compose_sampleA`, `exists_tmplA_bound`, `exists_gapA`,
  `acceptProb_realA_dPhi`.
* `HybridProtocol.exists_simA`: Alice's side of `hbcSecure_compose`.

## References

* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
  University Press, 2004, §7.3.1 (the proof of Theorem 7.3.3).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2, Definition 155.1.
-/

namespace TCSlib.Cryptography.SecureComputation

open Finset Complexity Turing TCSlib.Cryptography ComposeMachines ComposeSim ComposeProb
  ComposeBound

namespace HybridProtocol

variable {G : Functionality} (H : HybridProtocol G) (ρ : Protocol)

/-- **Alice's real run word** for call `j`: her encoded view of `ρ` on the call inputs
`inA n xs ⟦m.1⟧ j`, `inB n ys ⟦m.2⟧ j` and the tapes `t`.
`H.viewRunA ρ n xs ys m j t = (ρ.viewP (List.replicate n true) (H.inA n xs (List.ofFn m.1) j) (H.inB
n ys (List.ofFn m.2) j) t).encode`. -/
def viewRunA (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (j : Fin (H.calls.eval n))
    (t : ρ.ExecCoins ρ.P (List.replicate n true)) : List Bool :=
  (ρ.viewP (List.replicate n true) (H.inA n xs (List.ofFn m.1) j)
    (H.inB n ys (List.ofFn m.2) j) t).encode

/-- The defining equation of `viewRunA` (see `viewRunA`).
`H.viewRunA ρ n xs ys m j t = (ρ.viewP (List.replicate n true) (H.inA n xs (List.ofFn m.1) j) (H.inB
n ys (List.ofFn m.2) j) t).encode`. -/
theorem viewRunA_eq (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (j : Fin (H.calls.eval n))
    (t : ρ.ExecCoins ρ.P (List.replicate n true)) :
    H.viewRunA ρ n xs ys m j t =
      (ρ.viewP (List.replicate n true) (H.inA n xs (List.ofFn m.1) j)
        (H.inB n ys (List.ofFn m.2) j) t).encode := rfl

/-- **Alice's simulated run word** for call `j`: the output of `ρ`'s simulator `S` on her call
input and her ideal answer `⟦f_A(callA_j, callB_j)⟧`, with coins `s`.
`H.simRunA S n xs ys m j s = S.runAt n (pairEncode (H.inA n xs (List.ofFn m.1) j) (List.ofFn (G.f n
(H.callA n xs (List.ofFn m.1) j) (H.callB n ys (List.ofFn m.2) j)).1)) s`. -/
def simRunA (S : NUPPT) (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (j : Fin (H.calls.eval n))
    (s : S.Coins n) : List Bool :=
  S.runAt n (pairEncode (H.inA n xs (List.ofFn m.1) j)
    (List.ofFn (G.f n (H.callA n xs (List.ofFn m.1) j) (H.callB n ys (List.ofFn m.2) j)).1)) s

/-- The defining equation of `simRunA` (see `simRunA`).
`H.simRunA S n xs ys m j s = S.runAt n (pairEncode (H.inA n xs (List.ofFn m.1) j) (List.ofFn (G.f n
(H.callA n xs (List.ofFn m.1) j) (H.callB n ys (List.ofFn m.2) j)).1)) s`. -/
theorem simRunA_eq (S : NUPPT) (n : ℕ) (xs ys : List Bool) (m : H.Coins n)
    (j : Fin (H.calls.eval n)) (s : S.Coins n) :
    H.simRunA S n xs ys m j s =
      S.runAt n (pairEncode (H.inA n xs (List.ofFn m.1) j)
        (List.ofFn (G.f n (H.callA n xs (List.ofFn m.1) j) (H.callB n ys (List.ofFn m.2) j)).1))
        s := rfl

/-- **Alice's sample from run words**: the assembled view (`asmView` with `ρ.P`'s coins, Bob's
moves read, no leading filler) of the words `V`, her input `xs`, her `main`-tape and the hybrid
main phase on the ideal answers, paired with Bob's output in that hybrid execution.
`H.sampleA ρ n xs ys m V = pairEncode (asmView H.calls ρ.rounds ρ.P.coins ρ.verifierFirst true 0
(List.replicate n true) xs (List.ofFn m.1) (Strategy.encodeMsgs (H.main.transcript (List.replicate n
true) (H.privA n xs ys (List.ofFn m.1) …`. -/
def sampleA (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (V : ℕ → List Bool) : List Bool :=
  pairEncode (asmView H.calls ρ.rounds ρ.P.coins ρ.verifierFirst true 0 (List.replicate n true)
      xs (List.ofFn m.1) (Strategy.encodeMsgs (H.main.transcript (List.replicate n true)
        (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2))
        (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m).1) V)
    (H.main.outV H.main.P (List.replicate n true) (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2))
      (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m)

/-- The defining equation of `sampleA` (see `sampleA`).
`H.sampleA ρ n xs ys m V = pairEncode (asmView H.calls ρ.rounds ρ.P.coins ρ.verifierFirst true 0
(List.replicate n true) xs (List.ofFn m.1) (Strategy.encodeMsgs (H.main.transcript (List.replicate n
true) (H.privA n xs ys (List.ofFn m.1) …`. -/
theorem sampleA_eq (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (V : ℕ → List Bool) :
    H.sampleA ρ n xs ys m V =
      pairEncode (asmView H.calls ρ.rounds ρ.P.coins ρ.verifierFirst true 0
          (List.replicate n true) xs (List.ofFn m.1)
          (Strategy.encodeMsgs (H.main.transcript (List.replicate n true)
            (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2))
            (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m).1) V)
        (H.main.outV H.main.P (List.replicate n true)
          (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2))
          (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m) := rfl

/-- **The real sample under `GoodRuns`** (step 2):
`F.realA (H.compose ρ) n x y (composeCoins (m, t)) = sampleA m (j ↦ viewRunA m j (t j))`
(`realA_compose_eq`, `realViewA_eq`). -/
theorem realA_compose_sampleA {F : Functionality} (hM : ∀ n, 0 < H.main.rounds.eval n) (n : ℕ)
    (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true))
    (hg : H.GoodRuns ρ n (List.ofFn x) (List.ofFn y) m t) :
    F.realA (H.compose ρ) n x y (H.composeCoins ρ n (m, t)) =
      H.sampleA ρ n (List.ofFn x) (List.ofFn y) m fun j =>
        if h : j < H.calls.eval n then H.viewRunA ρ n (List.ofFn x) (List.ofFn y) m ⟨j, h⟩
          (t ⟨j, h⟩) else [] := by
  have hV : H.realViewA ρ n (List.ofFn x) (List.ofFn y) m t = fun j =>
      if h : j < H.calls.eval n then H.viewRunA ρ n (List.ofFn x) (List.ofFn y) m ⟨j, h⟩
        (t ⟨j, h⟩) else [] :=
    funext fun j => by rw [realViewA_eq]; rfl
  rw [H.realA_compose_eq ρ hM n x y m t hg, hV, sampleA_eq]

/-- **The templates of Alice's hybrid steps are polynomially long**: for some polynomial `q`, for
all inputs, run indices `i` and coordinates `a`, the template (`ComposeSim.tmplW`) of the header
`⟨⟨1^n, ⟦x⟧⟩, ⟨⟦m.1⟧, main phase⟩⟩`, the run words of hybrid `i` before and after run `i`, and
Bob's output in `main` has at most `q(n)` bits.
`∃ q : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (i : Fin
(H.calls.eval n)) (a : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) ×
S.Coins n)), (tmplW (pairEncode (pairEncode …`.

**Proof sketch.** The main phase and Bob's output are polynomially long (`exists_main_msgs_le`,
`exists_main_outV_le`); every run word is a real view (`exists_viewP_le`), a simulator output on
an argument of `2 G.inA(n) + 2 + G.outA(n)` bits (`exists_runAt_le`) or empty; at most `L(n)` of
them are encoded (`length_encodeMsgs_le`); the rest is `length_pairEncode`. -/
theorem exists_tmplA_bound {F : Functionality} (hH : H.PolyTime F) (hρ : G.PolyTime ρ)
    (S : NUPPT) :
    ∃ q : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool)
      (i : Fin (H.calls.eval n))
      (a : H.Coins n ×
        (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) × S.Coins n)),
      (tmplW (pairEncode (pairEncode (List.replicate n true) (List.ofFn x))
          (pairEncode (List.ofFn a.1.1) (Strategy.encodeMsgs (H.main.transcript
            (List.replicate n true)
            (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2))
            (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1).1)))
        ((List.range i).map (hybV (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
          (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a))
        ((List.range (H.calls.eval n - (i + 1))).map fun k =>
          hybV (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
            (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a (i + 1 + k))
        (H.main.outV H.main.P (List.replicate n true)
          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2))
          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1)).length ≤
        q.eval n := by
  obtain ⟨E, hE⟩ := H.exists_main_msgs_le hH
  obtain ⟨O, hO⟩ := H.exists_main_outV_le hH
  obtain ⟨V, hV⟩ := exists_viewP_le hρ
  obtain ⟨Sv, hSv⟩ := exists_runAt_le S (.add (.add (.mul (.const 2) G.inA) (.const 2)) G.outA)
  -- every run word has at most `V(n) + Sv(n)` bits
  have hw : ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (i : ℕ)
      (a : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) ×
        S.Coins n)) (j : ℕ),
      (hybV (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
        (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a j).length ≤ V.eval n + Sv.eval n := by
    intro n x y i a j
    rw [hybV_eq]
    split_ifs with h₁ h₂
    · rw [simRunA_eq]
      refine (hSv n _ _ ?_).trans (Nat.le_add_left _ _)
      rw [length_pairEncode, inA_val, List.length_ofFn, List.length_ofFn]
      simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, le_refl]
    · rw [viewRunA_eq, inA_val, inB_val]
      exact (hV n _ _ _).trans (Nat.le_add_right _ _)
    · exact Nat.zero_le _
  -- the encoded word lists
  obtain ⟨P, hP⟩ : ∃ P : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool)
      (y : Fin (F.inB.eval n) → Bool) (i : ℕ)
      (a : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) ×
        S.Coins n)) (l : List ℕ), l.length ≤ H.calls.eval n →
      (Strategy.encodeMsgs (l.map (hybV (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
        (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a))).length ≤ P.eval n := by
    refine ⟨.mul H.calls (.add (.mul (.const 2) (.add V Sv)) (.const 2)),
      fun n x y i a l hl => ?_⟩
    refine (length_encodeMsgs_le _ (V.eval n + Sv.eval n) fun w hw' => ?_).trans ?_
    · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hw'
      exact hw n x y i a j
    · rw [List.length_map]
      simp only [PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const]
      exact Nat.mul_le_mul_right _ hl
  let Hd : PolyExpr := .add (.add (.mul (.const 2) (.add (.add (.mul (.const 2) .var) (.const 2))
    F.inA)) (.const 2)) (.add (.add (.mul (.const 2) H.main.P.coins) (.const 2)) E)
  refine ⟨.add (.add (.mul (.const 2) (.add (.add (.mul (.const 2) Hd) (.const 2)) P))
    (.const 2)) (.add (.add (.mul (.const 2) P) (.const 2)) O), fun n x y i a => ?_⟩
  have h₁ := hP n x y i a (List.range i) (by rw [List.length_range]; exact i.2.le)
  have h₂ : (Strategy.encodeMsgs ((List.range (H.calls.eval n - (i + 1))).map fun k =>
      hybV (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
        (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a (i + 1 + k))).length ≤ P.eval n := by
    have h := hP n x y i a ((List.range (H.calls.eval n - (i + 1))).map fun k => i + 1 + k)
      (by rw [List.length_map, List.length_range]; omega)
    rwa [List.map_map] at h
  have h₃ := (hE n x y a.1).1
  have h₄ := hO n x y a.1
  have hc : (List.ofFn a.1.1).length = H.main.P.coins.eval n := by
    rw [List.length_ofFn, Strategy.coinLen_eq, List.length_replicate]
  have hu : (List.replicate n true).length = n := List.length_replicate
  rw [tmplW_eq, length_pairEncode, length_pairEncode, length_pairEncode, length_pairEncode,
    length_pairEncode, length_pairEncode, hc, List.length_ofFn]
  simp only [Hd, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  omega

/-- **Alice's hybrid steps are bounded by `ρ`'s security** (step 3): for every non-uniform PPT
`D` there is a negligible `ε₂` with, for all `n`, inputs, run indices `i` and coordinates `a`,
`|Pr_t[D(sampleA a.1 (plugV i a (viewRunA a.1 i t)))] −
Pr_s[D(sampleA a.1 (plugV i a (simRunA a.1 i s)))]| ≤ ε₂(n)`.

**Proof sketch.** `exists_gap_le` with `ρ`'s Alice-side samplers, the instances
`(x, y, i, a)`, the call inputs of `a.1` at `i`, and the template of `exists_tmplA_bound`. The
filled template is the sample: `asmW_pairEncode`, `msgAt_encodeMsgs` and `getD_plug` turn it into
`asmView` of `plugV`, and the first component of `ρ`'s real (ideal) sample is the real
(simulated) run word (`Functionality.realA_eq`, `idealA_eq`, `inA_val`, `inB_val`). -/
theorem exists_gapA {F : Functionality} (hH : H.PolyTime F) (hρ : G.PolyTime ρ) (S : NUPPT)
    (hS : ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n (x : Fin (G.inA.eval n) → Bool) (y : Fin (G.inB.eval n) → Bool),
        distAdv (G.realA ρ n x y) (G.idealA S n x y) (D.distinguisherL n) ≤ ε n)
    (D : NUPPT) :
    ∃ ε₂ : ℕ → ℝ, Negligible ε₂ ∧ ∀ n (x : Fin (F.inA.eval n) → Bool)
      (y : Fin (F.inB.eval n) → Bool) (i : Fin (H.calls.eval n))
      (a : H.Coins n ×
        (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) × S.Coins n)),
      |acceptProb (fun t => H.sampleA ρ n (List.ofFn x) (List.ofFn y) a.1
          (plugV (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
            (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a
            (H.viewRunA ρ n (List.ofFn x) (List.ofFn y) a.1 i t))) (D.distinguisherL n) -
        acceptProb (fun s => H.sampleA ρ n (List.ofFn x) (List.ofFn y) a.1
          (plugV (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
            (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a
            (H.simRunA S n (List.ofFn x) (List.ofFn y) a.1 i s))) (D.distinguisherL n)| ≤
        ε₂ n := by
  obtain ⟨q, hq⟩ := H.exists_tmplA_bound ρ hH hρ S
  obtain ⟨ε₂, hε₂, h⟩ := exists_gap_le (T := fun n => ρ.ExecCoins ρ.P (List.replicate n true))
    (Sc := fun n => S.Coins n) (fun n => G.realA ρ n) (fun n => G.idealA S n) hS H.calls
    ρ.rounds ρ.P.coins ρ.verifierFirst true 0
    (Θ := fun n => (Fin (F.inA.eval n) → Bool) × (Fin (F.inB.eval n) → Bool) ×
      Fin (H.calls.eval n) ×
      (H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) × S.Coins n)))
    (fun n θ => H.callA n (List.ofFn θ.1) (List.ofFn θ.2.2.2.1.1) θ.2.2.1)
    (fun n θ => H.callB n (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.2) θ.2.2.1)
    (fun n θ => pairEncode (pairEncode (List.replicate n true) (List.ofFn θ.1))
      (pairEncode (List.ofFn θ.2.2.2.1.1) (Strategy.encodeMsgs (H.main.transcript
        (List.replicate n true)
        (H.privA n (List.ofFn θ.1) (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.1)
          (List.ofFn θ.2.2.2.1.2))
        (H.privB n (List.ofFn θ.1) (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.1)
          (List.ofFn θ.2.2.2.1.2)) θ.2.2.2.1).1)))
    (fun n θ => H.main.outV H.main.P (List.replicate n true)
      (H.privA n (List.ofFn θ.1) (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.1)
        (List.ofFn θ.2.2.2.1.2))
      (H.privB n (List.ofFn θ.1) (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.1)
        (List.ofFn θ.2.2.2.1.2)) θ.2.2.2.1)
    (fun n θ => (List.range θ.2.2.1).map (hybV (H.viewRunA ρ n (List.ofFn θ.1) (List.ofFn θ.2.1))
      (H.simRunA S n (List.ofFn θ.1) (List.ofFn θ.2.1)) θ.2.2.1 θ.2.2.2))
    (fun n θ => (List.range (H.calls.eval n - (θ.2.2.1 + 1))).map fun k =>
      hybV (H.viewRunA ρ n (List.ofFn θ.1) (List.ofFn θ.2.1))
        (H.simRunA S n (List.ofFn θ.1) (List.ofFn θ.2.1)) θ.2.2.1 θ.2.2.2 (θ.2.2.1 + 1 + k))
    q (fun n θ => hq n θ.1 θ.2.1 θ.2.2.1 θ.2.2.2) D
  refine ⟨ε₂, hε₂, fun n x y i a => ?_⟩
  -- the filled template is the sample with run `i` replaced
  have hfill : ∀ v : List Bool, H.sampleA ρ n (List.ofFn x) (List.ofFn y) a.1
      (plugV (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
        (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a v) =
      pairEncode (asmW H.calls ρ.rounds ρ.P.coins ρ.verifierFirst true 0
        (pairEncode (pairEncode (pairEncode (List.replicate n true) (List.ofFn x))
          (pairEncode (List.ofFn a.1.1) (Strategy.encodeMsgs (H.main.transcript
            (List.replicate n true)
            (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2))
            (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1).1)))
          (Strategy.encodeMsgs ((List.range i).map (hybV (H.viewRunA ρ n (List.ofFn x)
            (List.ofFn y)) (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a) ++
            v :: (List.range (H.calls.eval n - (i + 1))).map fun k =>
              hybV (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
                (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a (i + 1 + k)))))
        (H.main.outV H.main.P (List.replicate n true)
          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2))
          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1) := by
    intro v
    rw [sampleA_eq, asmW_pairEncode]
    refine congrArg (fun w => pairEncode w _) (asmView_congr _ _ _ _ _ _ _ _ _ _ fun j hj => ?_)
    rw [List.length_replicate] at hj
    rw [msgAt_encodeMsgs, getD_plug _ _ i.2 hj, plugV_eq]
  have hreal : ∀ t, H.viewRunA ρ n (List.ofFn x) (List.ofFn y) a.1 i t =
      pairFstD (G.realA ρ n (H.callA n (List.ofFn x) (List.ofFn a.1.1) i)
        (H.callB n (List.ofFn y) (List.ofFn a.1.2) i) t) := fun t => by
    rw [Functionality.realA_eq, pairFstD_pairEncode, viewRunA_eq, inA_val, inB_val]
  have hsim : ∀ s, H.simRunA S n (List.ofFn x) (List.ofFn y) a.1 i s =
      pairFstD (G.idealA S n (H.callA n (List.ofFn x) (List.ofFn a.1.1) i)
        (H.callB n (List.ofFn y) (List.ofFn a.1.2) i) s) := fun s => by
    rw [Functionality.idealA_eq, pairFstD_pairEncode, simRunA_eq, inA_val]
  simp only [hfill, hreal, hsim]
  exact h n (x, y, i, a)

/-- **The simulated sample is `D ∘ Φ` on the hybrid real sample** (step 4): if `DΦ` is the
reduction of `exists_dPhi` (coins `calls · S.coins + D.coins`), then
`Pr[DΦ(H.realA F n x y)] = Pr_{(m, s)}[D(sampleA m (j ↦ simRunA m j (s j)))]`.

**Proof sketch.** Unfold `DΦ` (`acceptProb_pre`) and read its extra coins as one block of
`S.coins(n)` bits per call (`blocksCoins`). On `H.realA`, `phiD` keeps Bob's output and applies
`phiV` to Alice's view of `main`, whose private input is `⟨⟦x⟧, answers⟩` (`phiD_pairEncode`,
`phiV_view`): run `j` is `S`'s output on the call input (`hcall`, `inA_val`), the `j`-th
answer block (`coinBlock_flatten`) and the `j`-th coin block (`coinBlock_blocksCoins`), i.e.
`simRunA` (`NUPPT.runAtL_eq_output_layout`). -/
theorem acceptProb_realA_dPhi {F : Functionality} (S D DΦ : NUPPT) {fA : List Bool → List Bool}
    (hcall : ∀ n (x r : List Bool) (j : Fin (H.calls.eval n)),
      fA (pairEncode (List.replicate n true) (pairEncode x (pairEncode r
        (List.replicate j true)))) = List.ofFn (H.callA n x r j))
    (hc : DΦ.coins = .add (.mul H.calls S.coins) D.coins)
    (hD : ∀ n y r, DΦ.runAtL n y r =
      D.runAtL n (phiD S fA H.calls ρ.rounds ρ.P.coins G.outA ρ.verifierFirst true 0
        (pairEncode (pairEncode (List.replicate n true) (S.advice n))
          (pairEncode y (r.take ((PolyExpr.mul H.calls S.coins).eval n)))))
        (r.drop ((PolyExpr.mul H.calls S.coins).eval n)))
    (n : ℕ) (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) :
    acceptProb (H.realA F n x y) (DΦ.distinguisherL n) =
      acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) → S.Coins n) =>
        H.sampleA ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
          if h : j < H.calls.eval n then H.simRunA S n (List.ofFn x) (List.ofFn y) z.1 ⟨j, h⟩
            (z.2 ⟨j, h⟩) else []) (D.distinguisherL n) := by
  have hlen : (PolyExpr.mul H.calls S.coins).eval n = H.calls.eval n * S.coinLen n := by
    rw [PolyExpr.eval_mul, NUPPT.coinLen_eq]
  rw [acceptProb_pre (H.realA F n x y) DΦ D (.mul H.calls S.coins) n
    (fun w e => phiD S fA H.calls ρ.rounds ρ.P.coins G.outA ρ.verifierFirst true 0
      (pairEncode (pairEncode (List.replicate n true) (S.advice n)) (pairEncode w e))) hc (hD n)]
  refine (acceptProb_comp_equiv ((Equiv.refl (H.Coins n)).prodCongr (blocksCoins hlen)) _
    (D.distinguisherL n)).symm.trans ?_
  refine congrArg (fun f => acceptProb f (D.distinguisherL n)) (funext fun z => ?_)
  show phiD S fA H.calls ρ.rounds ρ.P.coins G.outA ρ.verifierFirst true 0
      (pairEncode (pairEncode (List.replicate n true) (S.advice n))
        (pairEncode (H.realA F n x y z.1) (List.ofFn (blocksCoins hlen z.2)))) = _
  rw [realA_eq, phiD_pairEncode, Protocol.viewP_eq, View.encode_mk, privA_eq, phiV_view,
    sampleA_eq, privA_eq, Protocol.transcript_eq_transcriptWith]
  refine congrArg (fun w => pairEncode w _) (asmView_congr _ _ _ _ _ _ _ _ _ _ fun j hj => ?_)
  rw [List.length_replicate] at hj
  rw [dif_pos hj, simRunA_eq, NUPPT.runAt_eq, NUPPT.runAtL_eq_output_layout,
    hcall n (List.ofFn x) (List.ofFn z.1.1) ⟨j, hj⟩, inA_val, ← NUPPT.coinLen_eq,
    coinBlock_blocksCoins hlen z.2 ⟨j, hj⟩, answersA_eq,
    coinBlock_flatten _ (fun c hc' => by
      obtain ⟨i, -, rfl⟩ := List.mem_ofFn.1 hc'
      exact List.length_ofFn) j (by rw [List.length_ofFn]; exact hj), List.getElem_ofFn]

/-- **Alice's side of the composition theorem**: from `H.HBCSecure F` and `HBCSecure ρ G`, there
is a non-uniform PPT `S_A` such that every non-uniform PPT `D` has a negligible `ε` with
`distAdv (F.realA (H.compose ρ) n x y) (F.idealA S_A n x y) D ≤ ε(n)` for all `n`, `x`, `y`.

**Proof sketch.** `S_A` post-processes the hybrid simulator by `Φ` (`exists_simulator`). For `D`:
1. relabel the coins (`composeCoins`); the real sample is `sampleA` of the real views except
   on `¬ GoodRuns` (`realA_compose_sampleA`, `distAdv_le_uprob_of_eq`), of probability at most
   `L(n) ε_c(n)` (`uprob_not_goodRuns_le`, `exists_correct`);
2. the real and simulated views are within `L(n) ε₂(n)` (`abs_chain_le`, `exists_gapA`);
3. `D` on the simulated views is `DΦ` on `H.realA` (`acceptProb_realA_dPhi`), and `D` on
   `S_A` is `DΦ` on `S_A^H` (`acceptProb_post_pre`, `phiD_pairEncode`), so `H.HBCSecure F`
   bounds this distance by `ε₃(n)`.
The total `L(n)(ε_c(n) + ε₂(n)) + ε₃(n)` is negligible (`negligible_polyExpr_mul`). -/
theorem exists_simA {F : Functionality} (hM : ∀ n, 0 < H.main.rounds.eval n)
    (hH : H.HBCSecure F) (hρ : SecureComputation.HBCSecure ρ G) :
    ∃ SA : NUPPT, ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool),
        distAdv (F.realA (H.compose ρ) n x y) (F.idealA SA n x y) (D.distinguisherL n) ≤ ε n := by
  obtain ⟨hHpt, SH, SHB, hHs⟩ := (HybridProtocol.hbcSecure_iff H F).mp hH
  obtain ⟨hρpt, SρA, SρB, hρs⟩ := (SecureComputation.hbcSecure_iff ρ G).mp hρ
  obtain ⟨-, -, ⟨fA, hfA, hcallA⟩, -, -⟩ := (HybridProtocol.polyTime_iff H F).mp hHpt
  obtain ⟨SA, hSAc, hSA⟩ := exists_simulator SρA H.calls ρ.rounds ρ.P.coins G.outA
    ρ.verifierFirst true 0 SH hfA
  refine ⟨SA, fun D => ?_⟩
  obtain ⟨εc, hεc, hc⟩ := exists_correct SρA SρB hρs
  obtain ⟨ε₂, hε₂, h₂⟩ := H.exists_gapA ρ hHpt hρpt SρA (fun D => by
    obtain ⟨ε, hε, h⟩ := hρs D
    exact ⟨ε, hε, fun n x y => (h n x y).1⟩) D
  obtain ⟨DΦ, hDΦc, hDΦ⟩ := exists_dPhi SρA H.calls ρ.rounds ρ.P.coins G.outA ρ.verifierFirst
    true 0 D hfA
  obtain ⟨ε₃, hε₃, h₃⟩ := hHs DΦ
  refine ⟨fun n => (H.calls.eval n : ℝ) * εc n + (H.calls.eval n : ℝ) * ε₂ n + ε₃ n,
    ((negligible_polyExpr_mul hεc H.calls).add (negligible_polyExpr_mul hε₂ H.calls)).add hε₃,
    fun n x y => ?_⟩
  -- step 1: the statistical switch
  have s1 : |acceptProb (F.realA (H.compose ρ) n x y) (D.distinguisherL n) -
      acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) →
          ρ.ExecCoins ρ.P (List.replicate n true)) =>
        H.sampleA ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
          if h : j < H.calls.eval n then H.viewRunA ρ n (List.ofFn x) (List.ofFn y) z.1 ⟨j, h⟩
            (z.2 ⟨j, h⟩) else []) (D.distinguisherL n)| ≤ H.calls.eval n * εc n := by
    rw [← acceptProb_comp_equiv (H.composeCoins ρ n) (F.realA (H.compose ρ) n x y)]
    have h := distAdv_le_uprob_of_eq _ _ (D.distinguisherL n)
      (fun z : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) =>
        ¬ H.GoodRuns ρ n (List.ofFn x) (List.ofFn y) z.1 z.2)
      (fun z hz => H.realA_compose_sampleA ρ hM n x y z.1 z.2 (not_not.1 hz))
    rw [distAdv_def] at h
    exact h.trans (H.uprob_not_goodRuns_le ρ n _ _ (εc n) (hc n))
  -- step 2: the hybrid argument over the runs
  have s2 := abs_chain_le (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
    (H.simRunA SρA n (List.ofFn x) (List.ofFn y)) (H.sampleA ρ n (List.ofFn x) (List.ofFn y))
    (D.distinguisherL n) (ε₂ n) (fun i a => h₂ n x y i a)
  -- step 3: the hybrid model
  have hid : ∀ S : NUPPT, F.idealA S n x y = fun s =>
      pairEncode (S.runAt n (pairEncode (List.ofFn x) (List.ofFn (F.f n x y).1)) s)
        (List.ofFn (F.f n x y).2) := fun S => funext (Functionality.idealA_eq F S n x y)
  have e3 : acceptProb (F.idealA SA n x y) (D.distinguisherL n) =
      acceptProb (F.idealA SH n x y) (DΦ.distinguisherL n) := by
    rw [hid SA, hid SH]
    exact acceptProb_post_pre SA SH DΦ D (.mul H.calls SρA.coins) n
      (fun hv e => phiV SρA fA H.calls ρ.rounds ρ.P.coins G.outA ρ.verifierFirst true 0
        (pairEncode (pairEncode (List.replicate n true) (SρA.advice n)) (pairEncode hv e)))
      (fun w e => phiD SρA fA H.calls ρ.rounds ρ.P.coins G.outA ρ.verifierFirst true 0
        (pairEncode (pairEncode (List.replicate n true) (SρA.advice n)) (pairEncode w e)))
      (pairEncode (List.ofFn x) (List.ofFn (F.f n x y).1)) (List.ofFn (F.f n x y).2) hSAc
      (hSA n _) hDΦc (hDΦ n) (fun hv e => phiD_pairEncode _ _ _ _ _ _ _ _ _ _ _ _ _ _)
  have s3 : |acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) → SρA.Coins n) =>
        H.sampleA ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
          if h : j < H.calls.eval n then H.simRunA SρA n (List.ofFn x) (List.ofFn y) z.1
            ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n) -
      acceptProb (F.idealA SA n x y) (D.distinguisherL n)| ≤ ε₃ n := by
    rw [← H.acceptProb_realA_dPhi ρ SρA D DΦ hcallA hDΦc hDΦ n x y, e3]
    have h := (h₃ n x y).1
    rwa [distAdv_def] at h
  rw [distAdv_def]
  calc |acceptProb (F.realA (H.compose ρ) n x y) (D.distinguisherL n) -
        acceptProb (F.idealA SA n x y) (D.distinguisherL n)|
      ≤ |acceptProb (F.realA (H.compose ρ) n x y) (D.distinguisherL n) -
          acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) →
            ρ.ExecCoins ρ.P (List.replicate n true)) =>
            H.sampleA ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
              if h : j < H.calls.eval n then H.viewRunA ρ n (List.ofFn x) (List.ofFn y) z.1
                ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n)| +
        |acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) →
            ρ.ExecCoins ρ.P (List.replicate n true)) =>
            H.sampleA ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
              if h : j < H.calls.eval n then H.viewRunA ρ n (List.ofFn x) (List.ofFn y) z.1
                ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n) -
          acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) → SρA.Coins n) =>
            H.sampleA ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
              if h : j < H.calls.eval n then H.simRunA SρA n (List.ofFn x) (List.ofFn y) z.1
                ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n)| +
        |acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) → SρA.Coins n) =>
            H.sampleA ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
              if h : j < H.calls.eval n then H.simRunA SρA n (List.ofFn x) (List.ofFn y) z.1
                ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n) -
          acceptProb (F.idealA SA n x y) (D.distinguisherL n)| :=
        (abs_sub_le _ _ _).trans (add_le_add_right (abs_sub_le _ _ _) _)
    _ ≤ _ := add_le_add (add_le_add s1 s2) s3

end HybridProtocol

end TCSlib.Cryptography.SecureComputation

## ===== TCSlib/Cryptography/SecureComputation/ComposeSecurity/SideB.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Template
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Correct
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Chain
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Sim
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Lengths

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The composition theorem: Bob's side

Steps 1–5 of the proof of the composition theorem [Gol04, §7.3.1, proof of Theorem 7.3.3] for
Bob's real and ideal samples of `H.compose ρ`, as for Alice's (`ComposeSecurity/SideA.lean`). On
the `main`-tapes `m`, a run word `V j` per call and the sample `sampleB m V` (the assembled view of
`V`, his input, his `main`-tape, the leading fillers and the hybrid main phase, paired with
Alice's output in `main`):
1. under `GoodRuns` the real sample is `sampleB m (real views)` (`realB_compose_sampleB`);
2. the hybrid argument replaces his real views by `ρ`'s simulator (`exists_gapB`,
   `exists_tmplB_bound`, `abs_chain_le`);
3. `sampleB m (simulated views)` is `D ∘ Φ` on the hybrid real sample (`acceptProb_realB_dPhi`),
   and `H.HBCSecure F` bounds the rest (`exists_simB`).

## Main definitions

* `HybridProtocol.viewRunB`, `simRunB`: Bob's real and simulated run words.
* `HybridProtocol.sampleB`: Bob's sample from run words.

## Main results

* `HybridProtocol.realB_compose_sampleB`, `exists_tmplB_bound`, `exists_gapB`,
  `acceptProb_realB_dPhi`.
* `HybridProtocol.exists_simB`: Bob's side of `hbcSecure_compose`.

## References

* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
  University Press, 2004, §7.3.1 (the proof of Theorem 7.3.3).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2, Definition 155.1.
-/

namespace TCSlib.Cryptography.SecureComputation

open Finset Complexity Turing TCSlib.Cryptography ComposeMachines ComposeSim ComposeProb
  ComposeBound

namespace HybridProtocol

variable {G : Functionality} (H : HybridProtocol G) (ρ : Protocol)

/-- **Bob's real run word** for call `j`: his encoded view of `ρ` on the call inputs
`inA n xs ⟦m.1⟧ j`, `inB n ys ⟦m.2⟧ j` and the tapes `t`.
`H.viewRunB ρ n xs ys m j t = (ρ.viewV (List.replicate n true) (H.inA n xs (List.ofFn m.1) j) (H.inB
n ys (List.ofFn m.2) j) t).encode`. -/
def viewRunB (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (j : Fin (H.calls.eval n))
    (t : ρ.ExecCoins ρ.P (List.replicate n true)) : List Bool :=
  (ρ.viewV (List.replicate n true) (H.inA n xs (List.ofFn m.1) j)
    (H.inB n ys (List.ofFn m.2) j) t).encode

/-- The defining equation of `viewRunB` (see `viewRunB`).
`H.viewRunB ρ n xs ys m j t = (ρ.viewV (List.replicate n true) (H.inA n xs (List.ofFn m.1) j) (H.inB
n ys (List.ofFn m.2) j) t).encode`. -/
theorem viewRunB_eq (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (j : Fin (H.calls.eval n))
    (t : ρ.ExecCoins ρ.P (List.replicate n true)) :
    H.viewRunB ρ n xs ys m j t =
      (ρ.viewV (List.replicate n true) (H.inA n xs (List.ofFn m.1) j)
        (H.inB n ys (List.ofFn m.2) j) t).encode := rfl

/-- **Bob's simulated run word** for call `j`: the output of `ρ`'s simulator `S` on his call
input and his ideal answer `⟦f_B(callA_j, callB_j)⟧`, with coins `s`.
`H.simRunB S n xs ys m j s = S.runAt n (pairEncode (H.inB n ys (List.ofFn m.2) j) (List.ofFn (G.f n
(H.callA n xs (List.ofFn m.1) j) (H.callB n ys (List.ofFn m.2) j)).2)) s`. -/
def simRunB (S : NUPPT) (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (j : Fin (H.calls.eval n))
    (s : S.Coins n) : List Bool :=
  S.runAt n (pairEncode (H.inB n ys (List.ofFn m.2) j)
    (List.ofFn (G.f n (H.callA n xs (List.ofFn m.1) j) (H.callB n ys (List.ofFn m.2) j)).2)) s

/-- The defining equation of `simRunB` (see `simRunB`).
`H.simRunB S n xs ys m j s = S.runAt n (pairEncode (H.inB n ys (List.ofFn m.2) j) (List.ofFn (G.f n
(H.callA n xs (List.ofFn m.1) j) (H.callB n ys (List.ofFn m.2) j)).2)) s`. -/
theorem simRunB_eq (S : NUPPT) (n : ℕ) (xs ys : List Bool) (m : H.Coins n)
    (j : Fin (H.calls.eval n)) (s : S.Coins n) :
    H.simRunB S n xs ys m j s =
      S.runAt n (pairEncode (H.inB n ys (List.ofFn m.2) j)
        (List.ofFn (G.f n (H.callA n xs (List.ofFn m.1) j) (H.callB n ys (List.ofFn m.2) j)).2))
        s := rfl

/-- **Bob's sample from run words**: the assembled view (`asmView` with `ρ.V`'s coins, Alice's
moves read, `lead` leading fillers) of the words `V`, his input `ys`, his `main`-tape and the
hybrid main phase on the ideal answers, paired with Alice's output in that hybrid execution.
`H.sampleB ρ n xs ys m V = pairEncode (asmView H.calls ρ.rounds ρ.V.coins ρ.verifierFirst false
H.lead (List.replicate n true) ys (List.ofFn m.2) (Strategy.encodeMsgs (H.main.transcript
(List.replicate n true) (H.privA n xs ys (List.ofFn …`. -/
def sampleB (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (V : ℕ → List Bool) : List Bool :=
  pairEncode (asmView H.calls ρ.rounds ρ.V.coins ρ.verifierFirst false H.lead
      (List.replicate n true) ys (List.ofFn m.2) (Strategy.encodeMsgs (H.main.transcript
        (List.replicate n true) (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2))
        (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m).2) V)
    (H.main.outP (List.replicate n true) (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2))
      (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m)

/-- The defining equation of `sampleB` (see `sampleB`).
`H.sampleB ρ n xs ys m V = pairEncode (asmView H.calls ρ.rounds ρ.V.coins ρ.verifierFirst false
H.lead (List.replicate n true) ys (List.ofFn m.2) (Strategy.encodeMsgs (H.main.transcript
(List.replicate n true) (H.privA n xs ys (List.ofFn …`. -/
theorem sampleB_eq (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (V : ℕ → List Bool) :
    H.sampleB ρ n xs ys m V =
      pairEncode (asmView H.calls ρ.rounds ρ.V.coins ρ.verifierFirst false H.lead
          (List.replicate n true) ys (List.ofFn m.2)
          (Strategy.encodeMsgs (H.main.transcript (List.replicate n true)
            (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2))
            (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m).2) V)
        (H.main.outP (List.replicate n true) (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2))
          (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m) := rfl

/-- **Bob's real sample under `GoodRuns`** (step 2): `F.realB (H.compose ρ) n x y (composeCoins
(m, t)) = sampleB m (j ↦ viewRunB m j (t j))` (`realB_compose_eq`, `realViewB_eq`). -/
theorem realB_compose_sampleB {F : Functionality} (hM : ∀ n, 0 < H.main.rounds.eval n) (n : ℕ)
    (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true))
    (hg : H.GoodRuns ρ n (List.ofFn x) (List.ofFn y) m t) :
    F.realB (H.compose ρ) n x y (H.composeCoins ρ n (m, t)) =
      H.sampleB ρ n (List.ofFn x) (List.ofFn y) m fun j =>
        if h : j < H.calls.eval n then H.viewRunB ρ n (List.ofFn x) (List.ofFn y) m ⟨j, h⟩
          (t ⟨j, h⟩) else [] := by
  have hV : H.realViewB ρ n (List.ofFn x) (List.ofFn y) m t = fun j =>
      if h : j < H.calls.eval n then H.viewRunB ρ n (List.ofFn x) (List.ofFn y) m ⟨j, h⟩
        (t ⟨j, h⟩) else [] :=
    funext fun j => by rw [realViewB_eq]; rfl
  rw [H.realB_compose_eq ρ hM n x y m t hg, hV, sampleB_eq]

/-- **The templates of Bob's hybrid steps are polynomially long**: for some polynomial `q`, for
all inputs, run indices `i` and coordinates `a`, the template (`ComposeSim.tmplW`) of the header
`⟨⟨1^n, ⟦y⟧⟩, ⟨⟦m.2⟧, main phase⟩⟩`, the run words of hybrid `i` before and after run `i`, and
Alice's output in `main` has at most `q(n)` bits.
`∃ q : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (i : Fin
(H.calls.eval n)) (a : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) ×
S.Coins n)), (tmplW (pairEncode (pairEncode …`.

**Proof sketch.** As `exists_tmplA_bound`, with Bob's half of the main phase
(`exists_main_msgs_le`), Alice's output (`exists_main_outP_le`), Bob's views (`exists_viewV_le`)
and simulator outputs on arguments of `2 G.inB(n) + 2 + G.outB(n)` bits (`exists_runAt_le`). -/
theorem exists_tmplB_bound {F : Functionality} (hH : H.PolyTime F) (hρ : G.PolyTime ρ)
    (S : NUPPT) :
    ∃ q : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool)
      (i : Fin (H.calls.eval n))
      (a : H.Coins n ×
        (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) × S.Coins n)),
      (tmplW (pairEncode (pairEncode (List.replicate n true) (List.ofFn y))
          (pairEncode (List.ofFn a.1.2) (Strategy.encodeMsgs (H.main.transcript
            (List.replicate n true)
            (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2))
            (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1).2)))
        ((List.range i).map (hybV (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
          (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a))
        ((List.range (H.calls.eval n - (i + 1))).map fun k =>
          hybV (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
            (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a (i + 1 + k))
        (H.main.outP (List.replicate n true)
          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2))
          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1)).length ≤
        q.eval n := by
  obtain ⟨E, hE⟩ := H.exists_main_msgs_le hH
  obtain ⟨O, hO⟩ := H.exists_main_outP_le hH
  obtain ⟨V, hV⟩ := exists_viewV_le hρ
  obtain ⟨Sv, hSv⟩ := exists_runAt_le S (.add (.add (.mul (.const 2) G.inB) (.const 2)) G.outB)
  -- every run word has at most `V(n) + Sv(n)` bits
  have hw : ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (i : ℕ)
      (a : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) ×
        S.Coins n)) (j : ℕ),
      (hybV (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
        (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a j).length ≤ V.eval n + Sv.eval n := by
    intro n x y i a j
    rw [hybV_eq]
    split_ifs with h₁ h₂
    · rw [simRunB_eq]
      refine (hSv n _ _ ?_).trans (Nat.le_add_left _ _)
      rw [length_pairEncode, inB_val, List.length_ofFn, List.length_ofFn]
      simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, le_refl]
    · rw [viewRunB_eq, inA_val, inB_val]
      exact (hV n _ _ _).trans (Nat.le_add_right _ _)
    · exact Nat.zero_le _
  -- the encoded word lists
  obtain ⟨P, hP⟩ : ∃ P : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool)
      (y : Fin (F.inB.eval n) → Bool) (i : ℕ)
      (a : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) ×
        S.Coins n)) (l : List ℕ), l.length ≤ H.calls.eval n →
      (Strategy.encodeMsgs (l.map (hybV (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
        (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a))).length ≤ P.eval n := by
    refine ⟨.mul H.calls (.add (.mul (.const 2) (.add V Sv)) (.const 2)),
      fun n x y i a l hl => ?_⟩
    refine (length_encodeMsgs_le _ (V.eval n + Sv.eval n) fun w hw' => ?_).trans ?_
    · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hw'
      exact hw n x y i a j
    · rw [List.length_map]
      simp only [PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const]
      exact Nat.mul_le_mul_right _ hl
  let Hd : PolyExpr := .add (.add (.mul (.const 2) (.add (.add (.mul (.const 2) .var) (.const 2))
    F.inB)) (.const 2)) (.add (.add (.mul (.const 2) H.main.V.coins) (.const 2)) E)
  refine ⟨.add (.add (.mul (.const 2) (.add (.add (.mul (.const 2) Hd) (.const 2)) P))
    (.const 2)) (.add (.add (.mul (.const 2) P) (.const 2)) O), fun n x y i a => ?_⟩
  have h₁ := hP n x y i a (List.range i) (by rw [List.length_range]; exact i.2.le)
  have h₂ : (Strategy.encodeMsgs ((List.range (H.calls.eval n - (i + 1))).map fun k =>
      hybV (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
        (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a (i + 1 + k))).length ≤ P.eval n := by
    have h := hP n x y i a ((List.range (H.calls.eval n - (i + 1))).map fun k => i + 1 + k)
      (by rw [List.length_map, List.length_range]; omega)
    rwa [List.map_map] at h
  have h₃ := (hE n x y a.1).2
  have h₄ := hO n x y a.1
  have hc : (List.ofFn a.1.2).length = H.main.V.coins.eval n := by
    rw [List.length_ofFn, Strategy.coinLen_eq, List.length_replicate]
  have hu : (List.replicate n true).length = n := List.length_replicate
  rw [tmplW_eq, length_pairEncode, length_pairEncode, length_pairEncode, length_pairEncode,
    length_pairEncode, length_pairEncode, hc, List.length_ofFn]
  simp only [Hd, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  omega

/-- **Bob's hybrid steps are bounded by `ρ`'s security** (step 3): for every non-uniform PPT `D`
there is a negligible `ε₂` with, for all `n`, inputs, run indices `i` and coordinates `a`,
`|Pr_t[D(sampleB a.1 (plugV i a (viewRunB a.1 i t)))] −
Pr_s[D(sampleB a.1 (plugV i a (simRunB a.1 i s)))]| ≤ ε₂(n)`.

**Proof sketch.** As `exists_gapA`: `exists_gap_le` with `ρ`'s Bob-side samplers and the
template of `exists_tmplB_bound`; the first component of `ρ`'s real (ideal) Bob sample is the
real (simulated) run word (`Functionality.realB_eq`, `idealB_eq`, `inA_val`, `inB_val`). -/
theorem exists_gapB {F : Functionality} (hH : H.PolyTime F) (hρ : G.PolyTime ρ) (S : NUPPT)
    (hS : ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n (x : Fin (G.inA.eval n) → Bool) (y : Fin (G.inB.eval n) → Bool),
        distAdv (G.realB ρ n x y) (G.idealB S n x y) (D.distinguisherL n) ≤ ε n)
    (D : NUPPT) :
    ∃ ε₂ : ℕ → ℝ, Negligible ε₂ ∧ ∀ n (x : Fin (F.inA.eval n) → Bool)
      (y : Fin (F.inB.eval n) → Bool) (i : Fin (H.calls.eval n))
      (a : H.Coins n ×
        (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) × S.Coins n)),
      |acceptProb (fun t => H.sampleB ρ n (List.ofFn x) (List.ofFn y) a.1
          (plugV (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
            (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a
            (H.viewRunB ρ n (List.ofFn x) (List.ofFn y) a.1 i t))) (D.distinguisherL n) -
        acceptProb (fun s => H.sampleB ρ n (List.ofFn x) (List.ofFn y) a.1
          (plugV (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
            (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a
            (H.simRunB S n (List.ofFn x) (List.ofFn y) a.1 i s))) (D.distinguisherL n)| ≤
        ε₂ n := by
  obtain ⟨q, hq⟩ := H.exists_tmplB_bound ρ hH hρ S
  obtain ⟨ε₂, hε₂, h⟩ := exists_gap_le (T := fun n => ρ.ExecCoins ρ.P (List.replicate n true))
    (Sc := fun n => S.Coins n) (fun n => G.realB ρ n) (fun n => G.idealB S n) hS H.calls
    ρ.rounds ρ.V.coins ρ.verifierFirst false H.lead
    (Θ := fun n => (Fin (F.inA.eval n) → Bool) × (Fin (F.inB.eval n) → Bool) ×
      Fin (H.calls.eval n) ×
      (H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) × S.Coins n)))
    (fun n θ => H.callA n (List.ofFn θ.1) (List.ofFn θ.2.2.2.1.1) θ.2.2.1)
    (fun n θ => H.callB n (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.2) θ.2.2.1)
    (fun n θ => pairEncode (pairEncode (List.replicate n true) (List.ofFn θ.2.1))
      (pairEncode (List.ofFn θ.2.2.2.1.2) (Strategy.encodeMsgs (H.main.transcript
        (List.replicate n true)
        (H.privA n (List.ofFn θ.1) (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.1)
          (List.ofFn θ.2.2.2.1.2))
        (H.privB n (List.ofFn θ.1) (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.1)
          (List.ofFn θ.2.2.2.1.2)) θ.2.2.2.1).2)))
    (fun n θ => H.main.outP (List.replicate n true)
      (H.privA n (List.ofFn θ.1) (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.1)
        (List.ofFn θ.2.2.2.1.2))
      (H.privB n (List.ofFn θ.1) (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.1)
        (List.ofFn θ.2.2.2.1.2)) θ.2.2.2.1)
    (fun n θ => (List.range θ.2.2.1).map (hybV (H.viewRunB ρ n (List.ofFn θ.1) (List.ofFn θ.2.1))
      (H.simRunB S n (List.ofFn θ.1) (List.ofFn θ.2.1)) θ.2.2.1 θ.2.2.2))
    (fun n θ => (List.range (H.calls.eval n - (θ.2.2.1 + 1))).map fun k =>
      hybV (H.viewRunB ρ n (List.ofFn θ.1) (List.ofFn θ.2.1))
        (H.simRunB S n (List.ofFn θ.1) (List.ofFn θ.2.1)) θ.2.2.1 θ.2.2.2 (θ.2.2.1 + 1 + k))
    q (fun n θ => hq n θ.1 θ.2.1 θ.2.2.1 θ.2.2.2) D
  refine ⟨ε₂, hε₂, fun n x y i a => ?_⟩
  -- the filled template is the sample with run `i` replaced
  have hfill : ∀ v : List Bool, H.sampleB ρ n (List.ofFn x) (List.ofFn y) a.1
      (plugV (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
        (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a v) =
      pairEncode (asmW H.calls ρ.rounds ρ.V.coins ρ.verifierFirst false H.lead
        (pairEncode (pairEncode (pairEncode (List.replicate n true) (List.ofFn y))
          (pairEncode (List.ofFn a.1.2) (Strategy.encodeMsgs (H.main.transcript
            (List.replicate n true)
            (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2))
            (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1).2)))
          (Strategy.encodeMsgs ((List.range i).map (hybV (H.viewRunB ρ n (List.ofFn x)
            (List.ofFn y)) (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a) ++
            v :: (List.range (H.calls.eval n - (i + 1))).map fun k =>
              hybV (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
                (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a (i + 1 + k)))))
        (H.main.outP (List.replicate n true)
          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2))
          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1) := by
    intro v
    rw [sampleB_eq, asmW_pairEncode]
    refine congrArg (fun w => pairEncode w _) (asmView_congr _ _ _ _ _ _ _ _ _ _ fun j hj => ?_)
    rw [List.length_replicate] at hj
    rw [msgAt_encodeMsgs, getD_plug _ _ i.2 hj, plugV_eq]
  have hreal : ∀ t, H.viewRunB ρ n (List.ofFn x) (List.ofFn y) a.1 i t =
      pairFstD (G.realB ρ n (H.callA n (List.ofFn x) (List.ofFn a.1.1) i)
        (H.callB n (List.ofFn y) (List.ofFn a.1.2) i) t) := fun t => by
    rw [Functionality.realB_eq, pairFstD_pairEncode, viewRunB_eq, inA_val, inB_val]
  have hsim : ∀ s, H.simRunB S n (List.ofFn x) (List.ofFn y) a.1 i s =
      pairFstD (G.idealB S n (H.callA n (List.ofFn x) (List.ofFn a.1.1) i)
        (H.callB n (List.ofFn y) (List.ofFn a.1.2) i) s) := fun s => by
    rw [Functionality.idealB_eq, pairFstD_pairEncode, simRunB_eq, inB_val]
  simp only [hfill, hreal, hsim]
  exact h n (x, y, i, a)

/-- **Bob's simulated sample is `D ∘ Φ` on the hybrid real sample** (step 4): if `DΦ` is the
reduction of `exists_dPhi` for Bob's post-processing (coins `calls · S.coins + D.coins`), then
`Pr[DΦ(H.realB F n x y)] = Pr_{(m, s)}[D(sampleB m (j ↦ simRunB m j (s j)))]`.

**Proof sketch.** As `acceptProb_realA_dPhi`, with Bob's view of `main`, whose private input is
`⟨⟦y⟧, answers⟩`, his call inputs (`hcall`, `inB_val`) and his answer blocks. -/
theorem acceptProb_realB_dPhi {F : Functionality} (S D DΦ : NUPPT) {fB : List Bool → List Bool}
    (hcall : ∀ n (y r : List Bool) (j : Fin (H.calls.eval n)),
      fB (pairEncode (List.replicate n true) (pairEncode y (pairEncode r
        (List.replicate j true)))) = List.ofFn (H.callB n y r j))
    (hc : DΦ.coins = .add (.mul H.calls S.coins) D.coins)
    (hD : ∀ n y r, DΦ.runAtL n y r =
      D.runAtL n (phiD S fB H.calls ρ.rounds ρ.V.coins G.outB ρ.verifierFirst false H.lead
        (pairEncode (pairEncode (List.replicate n true) (S.advice n))
          (pairEncode y (r.take ((PolyExpr.mul H.calls S.coins).eval n)))))
        (r.drop ((PolyExpr.mul H.calls S.coins).eval n)))
    (n : ℕ) (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) :
    acceptProb (H.realB F n x y) (DΦ.distinguisherL n) =
      acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) → S.Coins n) =>
        H.sampleB ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
          if h : j < H.calls.eval n then H.simRunB S n (List.ofFn x) (List.ofFn y) z.1 ⟨j, h⟩
            (z.2 ⟨j, h⟩) else []) (D.distinguisherL n) := by
  have hlen : (PolyExpr.mul H.calls S.coins).eval n = H.calls.eval n * S.coinLen n := by
    rw [PolyExpr.eval_mul, NUPPT.coinLen_eq]
  rw [acceptProb_pre (H.realB F n x y) DΦ D (.mul H.calls S.coins) n
    (fun w e => phiD S fB H.calls ρ.rounds ρ.V.coins G.outB ρ.verifierFirst false H.lead
      (pairEncode (pairEncode (List.replicate n true) (S.advice n)) (pairEncode w e))) hc (hD n)]
  refine (acceptProb_comp_equiv ((Equiv.refl (H.Coins n)).prodCongr (blocksCoins hlen)) _
    (D.distinguisherL n)).symm.trans ?_
  refine congrArg (fun f => acceptProb f (D.distinguisherL n)) (funext fun z => ?_)
  show phiD S fB H.calls ρ.rounds ρ.V.coins G.outB ρ.verifierFirst false H.lead
      (pairEncode (pairEncode (List.replicate n true) (S.advice n))
        (pairEncode (H.realB F n x y z.1) (List.ofFn (blocksCoins hlen z.2)))) = _
  rw [realB_eq, phiD_pairEncode, Protocol.viewV_eq, View.encode_mk, privB_eq, phiV_view,
    sampleB_eq, privB_eq, Protocol.transcript_eq_transcriptWith]
  refine congrArg (fun w => pairEncode w _) (asmView_congr _ _ _ _ _ _ _ _ _ _ fun j hj => ?_)
  rw [List.length_replicate] at hj
  rw [dif_pos hj, simRunB_eq, NUPPT.runAt_eq, NUPPT.runAtL_eq_output_layout,
    hcall n (List.ofFn y) (List.ofFn z.1.2) ⟨j, hj⟩, inB_val, ← NUPPT.coinLen_eq,
    coinBlock_blocksCoins hlen z.2 ⟨j, hj⟩, answersB_eq,
    coinBlock_flatten _ (fun c hc' => by
      obtain ⟨i, -, rfl⟩ := List.mem_ofFn.1 hc'
      exact List.length_ofFn) j (by rw [List.length_ofFn]; exact hj), List.getElem_ofFn]

/-- **Bob's side of the composition theorem**: from `H.HBCSecure F` and `HBCSecure ρ G`, there is
a non-uniform PPT `S_B` such that every non-uniform PPT `D` has a negligible `ε` with
`distAdv (F.realB (H.compose ρ) n x y) (F.idealB S_B n x y) D ≤ ε(n)` for all `n`, `x`, `y`.

**Proof sketch.** As `exists_simA`, with Bob's simulator post-processed by Bob's `Φ`
(`exists_simulator` with `ρ.V`'s coins, Alice's moves read and `lead` fillers), his real sample
(`realB_compose_sampleB`), the same bad event, the hybrid argument over his views
(`exists_gapB`, `abs_chain_le`) and the hybrid model (`acceptProb_realB_dPhi`,
`acceptProb_post_pre`). -/
theorem exists_simB {F : Functionality} (hM : ∀ n, 0 < H.main.rounds.eval n)
    (hH : H.HBCSecure F) (hρ : SecureComputation.HBCSecure ρ G) :
    ∃ SB : NUPPT, ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool),
        distAdv (F.realB (H.compose ρ) n x y) (F.idealB SB n x y) (D.distinguisherL n) ≤ ε n := by
  obtain ⟨hHpt, SHA, SH, hHs⟩ := (HybridProtocol.hbcSecure_iff H F).mp hH
  obtain ⟨hρpt, SρA, SρB, hρs⟩ := (SecureComputation.hbcSecure_iff ρ G).mp hρ
  obtain ⟨-, -, -, ⟨fB, hfB, hcallB⟩, -⟩ := (HybridProtocol.polyTime_iff H F).mp hHpt
  obtain ⟨SB, hSBc, hSB⟩ := exists_simulator SρB H.calls ρ.rounds ρ.V.coins G.outB
    ρ.verifierFirst false H.lead SH hfB
  refine ⟨SB, fun D => ?_⟩
  obtain ⟨εc, hεc, hc⟩ := exists_correct SρA SρB hρs
  obtain ⟨ε₂, hε₂, h₂⟩ := H.exists_gapB ρ hHpt hρpt SρB (fun D => by
    obtain ⟨ε, hε, h⟩ := hρs D
    exact ⟨ε, hε, fun n x y => (h n x y).2⟩) D
  obtain ⟨DΦ, hDΦc, hDΦ⟩ := exists_dPhi SρB H.calls ρ.rounds ρ.V.coins G.outB ρ.verifierFirst
    false H.lead D hfB
  obtain ⟨ε₃, hε₃, h₃⟩ := hHs DΦ
  refine ⟨fun n => (H.calls.eval n : ℝ) * εc n + (H.calls.eval n : ℝ) * ε₂ n + ε₃ n,
    ((negligible_polyExpr_mul hεc H.calls).add (negligible_polyExpr_mul hε₂ H.calls)).add hε₃,
    fun n x y => ?_⟩
  -- step 1: the statistical switch
  have s1 : |acceptProb (F.realB (H.compose ρ) n x y) (D.distinguisherL n) -
      acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) →
          ρ.ExecCoins ρ.P (List.replicate n true)) =>
        H.sampleB ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
          if h : j < H.calls.eval n then H.viewRunB ρ n (List.ofFn x) (List.ofFn y) z.1 ⟨j, h⟩
            (z.2 ⟨j, h⟩) else []) (D.distinguisherL n)| ≤ H.calls.eval n * εc n := by
    rw [← acceptProb_comp_equiv (H.composeCoins ρ n) (F.realB (H.compose ρ) n x y)]
    have h := distAdv_le_uprob_of_eq _ _ (D.distinguisherL n)
      (fun z : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) =>
        ¬ H.GoodRuns ρ n (List.ofFn x) (List.ofFn y) z.1 z.2)
      (fun z hz => H.realB_compose_sampleB ρ hM n x y z.1 z.2 (not_not.1 hz))
    rw [distAdv_def] at h
    exact h.trans (H.uprob_not_goodRuns_le ρ n _ _ (εc n) (hc n))
  -- step 2: the hybrid argument over the runs
  have s2 := abs_chain_le (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
    (H.simRunB SρB n (List.ofFn x) (List.ofFn y)) (H.sampleB ρ n (List.ofFn x) (List.ofFn y))
    (D.distinguisherL n) (ε₂ n) (fun i a => h₂ n x y i a)
  -- step 3: the hybrid model
  have hid : ∀ S : NUPPT, F.idealB S n x y = fun s =>
      pairEncode (S.runAt n (pairEncode (List.ofFn y) (List.ofFn (F.f n x y).2)) s)
        (List.ofFn (F.f n x y).1) := fun S => funext (Functionality.idealB_eq F S n x y)
  have e3 : acceptProb (F.idealB SB n x y) (D.distinguisherL n) =
      acceptProb (F.idealB SH n x y) (DΦ.distinguisherL n) := by
    rw [hid SB, hid SH]
    exact acceptProb_post_pre SB SH DΦ D (.mul H.calls SρB.coins) n
      (fun hv e => phiV SρB fB H.calls ρ.rounds ρ.V.coins G.outB ρ.verifierFirst false H.lead
        (pairEncode (pairEncode (List.replicate n true) (SρB.advice n)) (pairEncode hv e)))
      (fun w e => phiD SρB fB H.calls ρ.rounds ρ.V.coins G.outB ρ.verifierFirst false H.lead
        (pairEncode (pairEncode (List.replicate n true) (SρB.advice n)) (pairEncode w e)))
      (pairEncode (List.ofFn y) (List.ofFn (F.f n x y).2)) (List.ofFn (F.f n x y).1) hSBc
      (hSB n _) hDΦc (hDΦ n) (fun hv e => phiD_pairEncode _ _ _ _ _ _ _ _ _ _ _ _ _ _)
  have s3 : |acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) → SρB.Coins n) =>
        H.sampleB ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
          if h : j < H.calls.eval n then H.simRunB SρB n (List.ofFn x) (List.ofFn y) z.1
            ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n) -
      acceptProb (F.idealB SB n x y) (D.distinguisherL n)| ≤ ε₃ n := by
    rw [← H.acceptProb_realB_dPhi ρ SρB D DΦ hcallB hDΦc hDΦ n x y, e3]
    have h := (h₃ n x y).2
    rwa [distAdv_def] at h
  rw [distAdv_def]
  calc |acceptProb (F.realB (H.compose ρ) n x y) (D.distinguisherL n) -
        acceptProb (F.idealB SB n x y) (D.distinguisherL n)|
      ≤ |acceptProb (F.realB (H.compose ρ) n x y) (D.distinguisherL n) -
          acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) →
            ρ.ExecCoins ρ.P (List.replicate n true)) =>
            H.sampleB ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
              if h : j < H.calls.eval n then H.viewRunB ρ n (List.ofFn x) (List.ofFn y) z.1
                ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n)| +
        |acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) →
            ρ.ExecCoins ρ.P (List.replicate n true)) =>
            H.sampleB ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
              if h : j < H.calls.eval n then H.viewRunB ρ n (List.ofFn x) (List.ofFn y) z.1
                ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n) -
          acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) → SρB.Coins n) =>
            H.sampleB ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
              if h : j < H.calls.eval n then H.simRunB SρB n (List.ofFn x) (List.ofFn y) z.1
                ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n)| +
        |acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) → SρB.Coins n) =>
            H.sampleB ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
              if h : j < H.calls.eval n then H.simRunB SρB n (List.ofFn x) (List.ofFn y) z.1
                ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n) -
          acceptProb (F.idealB SB n x y) (D.distinguisherL n)| :=
        (abs_sub_le _ _ _).trans (add_le_add_right (abs_sub_le _ _ _) _)
    _ ≤ _ := add_le_add (add_le_add s1 s2) s3

end HybridProtocol

end TCSlib.Cryptography.SecureComputation

## ===== TCSlib/Cryptography/SecureComputation/ComposeSecurity/Sim.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Assembly
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Reductions

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The post-processing `Φ` and the simulators of the composed protocol

Steps 1 and 4 of the proof of the composition theorem [Gol04, §7.3.1, proof of Theorem 7.3.3]. A
party's simulator for `H.compose ρ` runs the hybrid simulator `S^H` and post-processes its output
`hv`, read as a view of `main` with private input `⟨x, a⟩`, `main`-tape `mt` and messages `me`:
for each call `j < L(n)` it recomputes the call input `fcall ⟨1^n, ⟨x, ⟨mt, 1^j⟩⟩⟩`, runs `ρ`'s
simulator `S^ρ` on it and on the `j`-th block of `a`, with the `j`-th block of fresh coins, and
assembles the view of `H.compose ρ` (`ComposeSim.asmView`). The same post-processing applied to
the hybrid real sample gives the last hybrid of the proof, and applied before a distinguisher it
gives the reduction to the hybrid model's security (`exists_dPhi`).

## Main definitions

* `ComposeSim.simV`: one simulated run, `ComposeSim.vlW`: their encoded list.
* `ComposeSim.phiV`: the post-processing of a view; `ComposeSim.phiD`: of a sample `⟨view, out⟩`.

## Main results

* `ComposeSim.phiV_view`: `phiV` on an encoded view of `main` with input `1^n` is the assembled
  view of the simulated runs.
* `ComposeSim.polyTimeComputable_phiV`, `polyTimeComputable_phiD`.
* `ComposeSim.exists_simulator`, `ComposeSim.exists_dPhi`: the simulator and the reduction as
  non-uniform PPT machines.

## References

* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
  University Press, 2004, §7.3.1 (the proof of Theorem 7.3.3).
-/

namespace TCSlib.Cryptography.SecureComputation.ComposeSim

open Complexity Turing Complexity.StateLoop TCSlib.Cryptography.EncodingMachines ComposeMachines

variable (Sρ : NUPPT) (fcall : List Bool → List Bool) (calls rounds cρ out : PolyExpr)
  (vF b : Bool) (lead : ℕ)

/-- **One simulated run**: on `v = ⟨1^j, ⟨⟨u, α⟩, ⟨hv, s⟩⟩⟩` (`u = 1^n`, `α` the advice of
`S^ρ`, `hv = ⟨⟨x₁, ⟨xin, a⟩⟩, ⟨mt, me⟩⟩` a view, `s` the fresh coins), `S^ρ`'s output on the
call input `fcall ⟨u, ⟨xin, ⟨mt, 1^j⟩⟩⟩` and the answer block `coinBlock out(n) j a`, with
advice `α` and coins `coinBlock Sρ.coins(n) j s`. -/
def simV (v : List Bool) : List Bool :=
  Sρ.output (NUPPT.layout (pairFstD (pairFstD (pairSndD v)))
    (pairEncode
      (fcall (pairEncode (pairFstD (pairFstD (pairSndD v)))
        (pairEncode (pairFstD (pairSndD (pairFstD (pairFstD (pairSndD (pairSndD v))))))
          (pairEncode (pairFstD (pairSndD (pairFstD (pairSndD (pairSndD v))))) (pairFstD v)))))
      (coinBlock (out.eval (pairFstD (pairFstD (pairSndD v))).length) (pairFstD v).length
        (pairSndD (pairSndD (pairFstD (pairFstD (pairSndD (pairSndD v))))))))
    (pairSndD (pairFstD (pairSndD v)))
    (coinBlock (Sρ.coins.eval (pairFstD (pairFstD (pairSndD v))).length) (pairFstD v).length
      (pairSndD (pairSndD (pairSndD v)))))

/-- `simV` on its word: with `w = ⟨⟨1^n, α⟩, ⟨⟨⟨x₁, ⟨xin, a⟩⟩, ⟨mt, me⟩⟩, s⟩⟩`,
`simV ⟨1^j, w⟩ = Sρ.output (layout 1^n ⟨fcall ⟨1^n, ⟨xin, ⟨mt, 1^j⟩⟩⟩, coinBlock out(n) j a⟩ α
(coinBlock Sρ.coins(n) j s))`. -/
theorem simV_pairEncode (n j : ℕ) (α x₁ xin a mt me s : List Bool) :
    simV Sρ fcall out (pairEncode (List.replicate j true)
        (pairEncode (pairEncode (List.replicate n true) α)
          (pairEncode (pairEncode (pairEncode x₁ (pairEncode xin a)) (pairEncode mt me)) s))) =
      Sρ.output (NUPPT.layout (List.replicate n true)
        (pairEncode (fcall (pairEncode (List.replicate n true)
            (pairEncode xin (pairEncode mt (List.replicate j true)))))
          (coinBlock (out.eval n) j a)) α (coinBlock (Sρ.coins.eval n) j s)) := by
  simp only [simV, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]

/-- **The encoded list of the simulated runs** on `w = ⟨⟨1^n, α⟩, ⟨hv, s⟩⟩`:
`vlW w = (range calls(n)).flatMap fun j => ⟨simV ⟨1^j, w⟩, []⟩`. -/
def vlW (w : List Bool) : List Bool :=
  (List.range (calls.eval (pairFstD (pairFstD w)).length)).flatMap fun j =>
    pairEncode (simV Sρ fcall out (pairEncode (List.replicate j true) w)) []

/-- The defining equation of `vlW` (see `vlW`).
`vlW Sρ fcall calls out w = (List.range (calls.eval (pairFstD (pairFstD w)).length)).flatMap fun j
=> pairEncode (simV Sρ fcall out (pairEncode (List.replicate j true) w)) []`. -/
theorem vlW_eq (w : List Bool) :
    vlW Sρ fcall calls out w =
      (List.range (calls.eval (pairFstD (pairFstD w)).length)).flatMap fun j =>
        pairEncode (simV Sρ fcall out (pairEncode (List.replicate j true) w)) [] := rfl

/-- **The post-processing of a view** (`Φ` on views): on `w = ⟨⟨1^n, α⟩, ⟨hv, s⟩⟩` with
`hv = ⟨⟨x₁, ⟨xin, a⟩⟩, ⟨mt, me⟩⟩`, the assembled view (`asmW`) of `x₁`, `xin`, `mt`, `me` and the
simulated runs (`vlW`). -/
def phiV (w : List Bool) : List Bool :=
  asmW calls rounds cρ vF b lead
    (pairEncode (pairEncode (pairEncode (pairFstD (pairFstD (pairFstD (pairSndD w))))
        (pairFstD (pairSndD (pairFstD (pairFstD (pairSndD w))))))
      (pairEncode (pairFstD (pairSndD (pairFstD (pairSndD w))))
        (pairSndD (pairSndD (pairFstD (pairSndD w))))))
      (vlW Sρ fcall calls out w))

/-- The defining equation of `phiV` (see `phiV`).
`phiV Sρ fcall calls rounds cρ out vF b lead w = asmW calls rounds cρ vF b lead (pairEncode
(pairEncode (pairEncode (pairFstD (pairFstD (pairFstD (pairSndD w)))) (pairFstD (pairSndD (pairFstD
(pairFstD (pairSndD w)))))) (pairEncode …`. -/
theorem phiV_eq (w : List Bool) :
    phiV Sρ fcall calls rounds cρ out vF b lead w =
      asmW calls rounds cρ vF b lead
        (pairEncode (pairEncode (pairEncode (pairFstD (pairFstD (pairFstD (pairSndD w))))
            (pairFstD (pairSndD (pairFstD (pairFstD (pairSndD w))))))
          (pairEncode (pairFstD (pairSndD (pairFstD (pairSndD w))))
            (pairSndD (pairSndD (pairFstD (pairSndD w))))))
          (vlW Sρ fcall calls out w)) := rfl

/-- **`phiV` on a view of `main` with common input `1^n`**: on
`⟨⟨1^n, α⟩, ⟨⟨⟨1^n, ⟨xin, a⟩⟩, ⟨mt, me⟩⟩, s⟩⟩` it is
`asmView … 1^n xin mt me V` with `V j = S^ρ`'s output on the call input and the answer block
`j`, with the coin block `j` (`asmW_pairEncode`, `asmView_congr`, `msgAt_encodeMsgs`). -/
theorem phiV_view (n : ℕ) (α xin a mt me s : List Bool) :
    phiV Sρ fcall calls rounds cρ out vF b lead
        (pairEncode (pairEncode (List.replicate n true) α)
          (pairEncode (pairEncode (pairEncode (List.replicate n true) (pairEncode xin a))
            (pairEncode mt me)) s)) =
      asmView calls rounds cρ vF b lead (List.replicate n true) xin mt me fun j =>
        Sρ.output (NUPPT.layout (List.replicate n true)
          (pairEncode (fcall (pairEncode (List.replicate n true)
              (pairEncode xin (pairEncode mt (List.replicate j true)))))
            (coinBlock (out.eval n) j a)) α (coinBlock (Sρ.coins.eval n) j s)) := by
  rw [phiV_eq, vlW_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]
  rw [asmW_pairEncode]
  refine asmView_congr _ _ _ _ _ _ _ _ _ _ fun j hj => ?_
  rw [List.length_replicate] at hj ⊢
  rw [← List.flatMap_map (fun j => simV Sρ fcall out (pairEncode (List.replicate j true)
      (pairEncode (pairEncode (List.replicate n true) α)
        (pairEncode (pairEncode (pairEncode (List.replicate n true) (pairEncode xin a))
          (pairEncode mt me)) s)))) (fun m => pairEncode m []),
    ← encodeMsgs_eq_flatMap, msgAt_encodeMsgs, Compose.getD_map_range hj, simV_pairEncode]

/-- **The post-processing of a sample** (`Φ` on samples `⟨view, out⟩`): on
`w = ⟨⟨u, α⟩, ⟨⟨hv, o⟩, s⟩⟩`, `phiD w = ⟨phiV ⟨⟨u, α⟩, ⟨hv, s⟩⟩, o⟩`. -/
def phiD (w : List Bool) : List Bool :=
  pairEncode (phiV Sρ fcall calls rounds cρ out vF b lead
      (pairEncode (pairFstD w) (pairEncode (pairFstD (pairFstD (pairSndD w)))
        (pairSndD (pairSndD w)))))
    (pairSndD (pairFstD (pairSndD w)))

/-- `phiD` on its word: `phiD ⟨⟨u, α⟩, ⟨⟨hv, o⟩, s⟩⟩ = ⟨phiV ⟨⟨u, α⟩, ⟨hv, s⟩⟩, o⟩`. -/
theorem phiD_pairEncode (u α hv o s : List Bool) :
    phiD Sρ fcall calls rounds cρ out vF b lead
        (pairEncode (pairEncode u α) (pairEncode (pairEncode hv o) s)) =
      pairEncode (phiV Sρ fcall calls rounds cρ out vF b lead
        (pairEncode (pairEncode u α) (pairEncode hv s))) o := by
  simp only [phiD, pairFstD_pairEncode, pairSndD_pairEncode]

variable {fcall}

/-- **`simV` is polynomial-time** when `fcall` is: `PolyTimeComputable (simV Sρ fcall out)`.

**Proof sketch.** The components `1^n`, `α`, `xin`, `a`, `mt`, `s` of the word are projections;
the call input is `fcall` on a pairing of them; the answer block and the coin block are
`coinSlice`s (`GI.coinSlice_poly`); and `S^ρ`'s output on the assembled layout is polynomial-time
(`NUPPT.polyTimeComputable_output`, `NUPPT.polyTimeComputable_layout`). -/
theorem polyTimeComputable_simV (hcall : PolyTimeComputable fcall) :
    PolyTimeComputable (simV Sρ fcall out) := by
  have hw := polyTimeComputable_pairSndD
  have hu : PolyTimeComputable fun v => pairFstD (pairFstD (pairSndD v)) :=
    polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairFstD.comp' hw)
  have hhv : PolyTimeComputable fun v => pairFstD (pairSndD (pairSndD v)) :=
    polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairSndD.comp' hw)
  have hz : PolyTimeComputable fun v => pairSndD (pairFstD (pairFstD (pairSndD (pairSndD v)))) :=
    polyTimeComputable_pairSndD.comp' (polyTimeComputable_pairFstD.comp'
      (polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairSndD.comp' hw)))
  have hxin := polyTimeComputable_pairFstD.comp' hz
  have ha := polyTimeComputable_pairSndD.comp' hz
  have hmt : PolyTimeComputable fun v => pairFstD (pairSndD (pairFstD (pairSndD (pairSndD v)))) :=
    polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairSndD.comp' hhv)
  have hs : PolyTimeComputable fun v => pairSndD (pairSndD (pairSndD v)) :=
    polyTimeComputable_pairSndD.comp' (polyTimeComputable_pairSndD.comp' hw)
  have hα : PolyTimeComputable fun v => pairSndD (pairFstD (pairSndD v)) :=
    polyTimeComputable_pairSndD.comp' (polyTimeComputable_pairFstD.comp' hw)
  have hin := hcall.comp' (hu.pairEncode (hxin.pairEncode (hmt.pairEncode
    polyTimeComputable_pairFstD)))
  exact (Sρ.polyTimeComputable_output.comp' (NUPPT.polyTimeComputable_layout hu
    (hin.pairEncode (GI.coinSlice_poly out hu polyTimeComputable_pairFstD ha)) hα
    (GI.coinSlice_poly Sρ.coins hu polyTimeComputable_pairFstD hs))).congr fun v => rfl

/-- **`vlW` is polynomial-time** (`ComposeMachines.polyTimeComputable_flatMap_range` of
`polyTimeComputable_simV` over the unary count `calls(n)`).
`PolyTimeComputable (vlW Sρ fcall calls out)`. -/
theorem polyTimeComputable_vlW (hcall : PolyTimeComputable fcall) :
    PolyTimeComputable (vlW Sρ fcall calls out) := by
  have hchunk : PolyTimeComputable fun v =>
      pairEncode (simV Sρ fcall out (pairEncode (List.replicate (pairFstD v).length true)
        (pairSndD v))) [] :=
    ((polyTimeComputable_simV Sρ out hcall).comp' ((unaryLength_poly
      polyTimeComputable_pairFstD).pairEncode polyTimeComputable_pairSndD)).pairEncode
      (polyTimeComputable_const [])
  exact (polyTimeComputable_flatMap_range (E := fun w j =>
      pairEncode (simV Sρ fcall out (pairEncode (List.replicate j true) w)) []) hchunk
    (unaryPolyOf_poly calls (unaryLength_poly (polyTimeComputable_pairFstD.comp'
      polyTimeComputable_pairFstD)))).congr fun w => (vlW_eq Sρ fcall calls out w).symm

/-- **`phiV` is polynomial-time** (`polyTimeComputable_asmW` after projections and `vlW`).
`PolyTimeComputable (phiV Sρ fcall calls rounds cρ out vF b lead)`. -/
theorem polyTimeComputable_phiV (hcall : PolyTimeComputable fcall) :
    PolyTimeComputable (phiV Sρ fcall calls rounds cρ out vF b lead) := by
  have hhv : PolyTimeComputable fun w => pairFstD (pairSndD w) :=
    polyTimeComputable_pairFstD.comp' polyTimeComputable_pairSndD
  have hv1 := polyTimeComputable_pairFstD.comp' hhv
  have hv2 := polyTimeComputable_pairSndD.comp' hhv
  exact ((polyTimeComputable_asmW calls rounds cρ vF b lead).comp'
    ((((polyTimeComputable_pairFstD.comp' hv1).pairEncode (polyTimeComputable_pairFstD.comp'
      (polyTimeComputable_pairSndD.comp' hv1))).pairEncode
      ((polyTimeComputable_pairFstD.comp' hv2).pairEncode
        (polyTimeComputable_pairSndD.comp' hv2))).pairEncode
      (polyTimeComputable_vlW Sρ calls out hcall))).congr fun w => rfl

/-- **`phiD` is polynomial-time** (`polyTimeComputable_phiV` after re-pairing).
`PolyTimeComputable (phiD Sρ fcall calls rounds cρ out vF b lead)`. -/
theorem polyTimeComputable_phiD (hcall : PolyTimeComputable fcall) :
    PolyTimeComputable (phiD Sρ fcall calls rounds cρ out vF b lead) := by
  have hsmp : PolyTimeComputable fun w => pairFstD (pairSndD w) :=
    polyTimeComputable_pairFstD.comp' polyTimeComputable_pairSndD
  exact (((polyTimeComputable_phiV Sρ calls rounds cρ out vF b lead hcall).comp'
    (polyTimeComputable_pairFstD.pairEncode ((polyTimeComputable_pairFstD.comp' hsmp).pairEncode
      (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD)))).pairEncode
    (polyTimeComputable_pairSndD.comp' hsmp)).congr fun w => rfl

/-- **The simulator of the composed protocol** (step 1): for a hybrid simulator `SH`, there is a
non-uniform PPT `S` with coins `SH.coins + calls · Sρ.coins` such that
`S(1^n, y; r) = phiV ⟨⟨1^n, Sρ.advice n⟩, ⟨SH(1^n, y; r_{<SH.coins(n)}), r_{≥SH.coins(n)}⟩⟩`
(`exists_post`). -/
theorem exists_simulator (SH : NUPPT) (hcall : PolyTimeComputable fcall) :
    ∃ S : NUPPT, S.coins = .add SH.coins (.mul calls Sρ.coins) ∧ ∀ n y r, S.runAtL n y r =
      phiV Sρ fcall calls rounds cρ out vF b lead
        (pairEncode (pairEncode (List.replicate n true) (Sρ.advice n))
          (pairEncode (SH.runAtL n y (r.take (SH.coinLen n))) (r.drop (SH.coinLen n)))) :=
  exists_post SH (polyTimeComputable_phiV Sρ calls rounds cρ out vF b lead hcall) Sρ.advice Sρ.adv
    Sρ.advice_length (.mul calls Sρ.coins)

/-- **The reduction to the hybrid model** (step 4): for a distinguisher `D`, there is a non-uniform
PPT `DΦ` with coins `calls · Sρ.coins + D.coins` such that
`DΦ(1^n, w; r) = D(1^n, phiD ⟨⟨1^n, Sρ.advice n⟩, ⟨w, r_{<p(n)}⟩⟩; r_{≥p(n)})`,
`p = calls · Sρ.coins` (`exists_pre`). -/
theorem exists_dPhi (D : NUPPT) (hcall : PolyTimeComputable fcall) :
    ∃ DΦ : NUPPT, DΦ.coins = .add (.mul calls Sρ.coins) D.coins ∧ ∀ n y r, DΦ.runAtL n y r =
      D.runAtL n (phiD Sρ fcall calls rounds cρ out vF b lead
        (pairEncode (pairEncode (List.replicate n true) (Sρ.advice n))
          (pairEncode y (r.take ((PolyExpr.mul calls Sρ.coins).eval n)))))
        (r.drop ((PolyExpr.mul calls Sρ.coins).eval n)) :=
  exists_pre D (polyTimeComputable_phiD Sρ calls rounds cρ out vF b lead hcall) Sρ.advice Sρ.adv
    Sρ.advice_length (.mul calls Sρ.coins)

end TCSlib.Cryptography.SecureComputation.ComposeSim

## ===== TCSlib/Cryptography/SecureComputation/ComposeSecurity/Template.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Accept
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Reductions

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The reduction of one hybrid step to the sub-protocol

Step 3 of the proof of the composition theorem [Gol04, §7.3.1, proof of Theorem 7.3.3]. A
distinguisher between neighbouring hybrids, at fixed inputs, run index and other coordinates,
becomes a distinguisher for one sample of `ρ`: the reduction holds as advice a **template**
(`tmplW`): the header `⟨⟨x₁, xin⟩, ⟨mt, me⟩⟩` of the assembled view, the encoded words of the
runs before and after the run under attack, and the other party's output. On a `ρ`-sample `w`
it inserts the view `pairFstD w` between them, assembles the view (`asmW`) and pairs it with the
output (`hybW`). The template is chosen at each `n` for the worst-case instance, so one
non-uniform machine serves every `n` (`exists_gap_le`).

## Main definitions

* `ComposeSim.tmplW`: the template; `ComposeSim.hybW`: the reduction's pre-processing.

## Main results

* `ComposeSim.hybW_tmplW`: the pre-processing on a template.
* `ComposeSim.polyTimeComputable_hybW`.
* `ComposeSim.exists_gap_le`: the worst-case gap over the instances of each `n` is at most the
  sub-protocol's negligible bound.

## References

* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
  University Press, 2004, §7.3.1 (the proof of Theorem 7.3.3).
-/

namespace TCSlib.Cryptography.SecureComputation.ComposeSim

open Finset Complexity Turing TCSlib.Cryptography ComposeProb ComposeMachines

/-- **The template of a hybrid step**: `⟨⟨hdr, encodeMsgs pre⟩, ⟨encodeMsgs suf, out⟩⟩` for the
header `hdr`, the words `pre` of the runs before the attacked one, the words `suf` of those
after it and the output `out`.
`tmplW hdr pre suf out = pairEncode (pairEncode hdr (Strategy.encodeMsgs pre)) (pairEncode
(Strategy.encodeMsgs suf) out)`. -/
def tmplW (hdr : List Bool) (pre suf : List (List Bool)) (out : List Bool) : List Bool :=
  pairEncode (pairEncode hdr (Strategy.encodeMsgs pre))
    (pairEncode (Strategy.encodeMsgs suf) out)

/-- The defining equation of `tmplW` (see `tmplW`).
`tmplW hdr pre suf out = pairEncode (pairEncode hdr (Strategy.encodeMsgs pre)) (pairEncode
(Strategy.encodeMsgs suf) out)`. -/
theorem tmplW_eq (hdr : List Bool) (pre suf : List (List Bool)) (out : List Bool) :
    tmplW hdr pre suf out =
      pairEncode (pairEncode hdr (Strategy.encodeMsgs pre))
        (pairEncode (Strategy.encodeMsgs suf) out) := rfl

/-- **The pre-processing of the hybrid-step reduction**: on `z = ⟨⟨u, β⟩, ⟨w, r⟩⟩` with
`β = ⟨⟨hdr, P⟩, ⟨Q, out⟩⟩`, the pair of `asmW ⟨hdr, P ++ ⟨pairFstD w, Q⟩⟩` and `out`. -/
def hybW (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ) (z : List Bool) : List Bool :=
  pairEncode (asmW calls rounds cρ vF b lead
      (pairEncode (pairFstD (pairFstD (pairSndD (pairFstD z))))
        (pairSndD (pairFstD (pairSndD (pairFstD z))) ++
          pairEncode (pairFstD (pairFstD (pairSndD z))) (pairFstD (pairSndD (pairSndD
            (pairFstD z)))))))
    (pairSndD (pairSndD (pairSndD (pairFstD z))))

/-- The defining equation of `hybW` (see `hybW`).
`hybW calls rounds cρ vF b lead z = pairEncode (asmW calls rounds cρ vF b lead (pairEncode (pairFstD
(pairFstD (pairSndD (pairFstD z)))) (pairSndD (pairFstD (pairSndD (pairFstD z))) ++ pairEncode
(pairFstD (pairFstD (pairSndD z))) (pairFstD …`. -/
theorem hybW_eq (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ) (z : List Bool) :
    hybW calls rounds cρ vF b lead z =
      pairEncode (asmW calls rounds cρ vF b lead
          (pairEncode (pairFstD (pairFstD (pairSndD (pairFstD z))))
            (pairSndD (pairFstD (pairSndD (pairFstD z))) ++
              pairEncode (pairFstD (pairFstD (pairSndD z))) (pairFstD (pairSndD (pairSndD
                (pairFstD z)))))))
        (pairSndD (pairSndD (pairSndD (pairFstD z)))) := rfl

/-- **The pre-processing on a template**: `hybW ⟨⟨u, tmplW hdr pre suf out⟩, ⟨w, r⟩⟩ =
⟨asmW ⟨hdr, encodeMsgs (pre ++ pairFstD w :: suf)⟩, out⟩` (`encodeMsgs_append`). -/
theorem hybW_tmplW (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ)
    (u hdr out w r : List Bool) (pre suf : List (List Bool)) :
    hybW calls rounds cρ vF b lead (pairEncode (pairEncode u (tmplW hdr pre suf out))
        (pairEncode w r)) =
      pairEncode (asmW calls rounds cρ vF b lead
        (pairEncode hdr (Strategy.encodeMsgs (pre ++ pairFstD w :: suf)))) out := by
  rw [hybW_eq, tmplW_eq, encodeMsgs_append, Strategy.encodeMsgs_cons]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]

/-- **The pre-processing is polynomial-time** (`polyTimeComputable_asmW` after projections,
`append` and `pairEncode`).
`PolyTimeComputable (hybW calls rounds cρ vF b lead)`. -/
theorem polyTimeComputable_hybW (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ) :
    PolyTimeComputable (hybW calls rounds cρ vF b lead) := by
  have hβ : PolyTimeComputable fun z => pairSndD (pairFstD z) :=
    polyTimeComputable_pairSndD.comp' polyTimeComputable_pairFstD
  have h1 := polyTimeComputable_pairFstD.comp' hβ
  have h2 := polyTimeComputable_pairSndD.comp' hβ
  have hw : PolyTimeComputable fun z => pairFstD (pairFstD (pairSndD z)) :=
    polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairFstD.comp'
      polyTimeComputable_pairSndD)
  exact (((polyTimeComputable_asmW calls rounds cρ vF b lead).comp'
    ((polyTimeComputable_pairFstD.comp' h1).pairEncode
      ((polyTimeComputable_pairSndD.comp' h1).append
        (hw.pairEncode (polyTimeComputable_pairFstD.comp' h2))))).pairEncode
    (polyTimeComputable_pairSndD.comp' h2)).congr fun z => rfl

/-- **The worst-case hybrid step is bounded by the sub-protocol's security.** Let `rs n x y` and
`is n x y` be samplers of `ρ` on inputs of `G`'s lengths, indistinguishable with a negligible
bound uniform over the inputs (`hS`). Let `Θ n` be finite sets of instances, each with inputs
`xA θ`, `yB θ` of `ρ` and a template whose length is at most `q(n)`. Then for every non-uniform
PPT `D` there is a negligible `ε₂` with, for all `n` and `θ : Θ n`,
`|Pr_t[D(K θ (pairFstD (rs t)))] − Pr_s[D(K θ (pairFstD (is s)))]| ≤ ε₂(n)`, where
`K θ v = ⟨asmW ⟨hdr θ, encodeMsgs (pre θ ++ v :: suf θ)⟩, out θ⟩` (the template filled with `v`).

**Proof sketch.** At each `n` with instances, take the instance `θ*` with the largest gap
(`Finset.exists_max_image`) and give its template as advice (length at most `q(n)`). The
machine `D ∘ hybW` with no extra coins (`exists_pre`) accepts a sample `w` as `D` accepts
`K θ* (pairFstD w)` (`acceptProb_pre`, `hybW_tmplW`, `acceptProb_fst`), so its advantage
between `rs` and `is` at the inputs of `θ*` is the gap at `θ*`, at most `ε₂(n)` by `hS`, and
every gap at `n` is at most the gap at `θ*`. -/
theorem exists_gap_le {G : Functionality} {T Sc : ℕ → Type} [∀ n, Fintype (T n)]
    [∀ n, Fintype (Sc n)]
    (rs : ∀ n, (Fin (G.inA.eval n) → Bool) → (Fin (G.inB.eval n) → Bool) → T n → List Bool)
    (is : ∀ n, (Fin (G.inA.eval n) → Bool) → (Fin (G.inB.eval n) → Bool) → Sc n → List Bool)
    (hS : ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n (x : Fin (G.inA.eval n) → Bool) (y : Fin (G.inB.eval n) → Bool),
        distAdv (rs n x y) (is n x y) (D.distinguisherL n) ≤ ε n)
    (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ) {Θ : ℕ → Type} [∀ n, Fintype (Θ n)]
    (xA : ∀ n, Θ n → Fin (G.inA.eval n) → Bool) (yB : ∀ n, Θ n → Fin (G.inB.eval n) → Bool)
    (hdr out : ∀ n, Θ n → List Bool) (pre suf : ∀ n, Θ n → List (List Bool)) (q : PolyExpr)
    (hq : ∀ n θ, (tmplW (hdr n θ) (pre n θ) (suf n θ) (out n θ)).length ≤ q.eval n)
    (D : NUPPT) :
    ∃ ε₂ : ℕ → ℝ, Negligible ε₂ ∧ ∀ n (θ : Θ n),
      |acceptProb (fun t => pairEncode (asmW calls rounds cρ vF b lead (pairEncode (hdr n θ)
            (Strategy.encodeMsgs (pre n θ ++ pairFstD (rs n (xA n θ) (yB n θ) t) :: suf n θ))))
            (out n θ)) (D.distinguisherL n) -
        acceptProb (fun s => pairEncode (asmW calls rounds cρ vF b lead (pairEncode (hdr n θ)
            (Strategy.encodeMsgs (pre n θ ++ pairFstD (is n (xA n θ) (yB n θ) s) :: suf n θ))))
            (out n θ)) (D.distinguisherL n)| ≤ ε₂ n := by
  classical
  -- the gap of an instance
  let K : ∀ n, Θ n → List Bool → List Bool := fun n θ v =>
    pairEncode (asmW calls rounds cρ vF b lead (pairEncode (hdr n θ)
      (Strategy.encodeMsgs (pre n θ ++ v :: suf n θ)))) (out n θ)
  let gap : ∀ n, Θ n → ℝ := fun n θ =>
    |acceptProb (fun t => K n θ (pairFstD (rs n (xA n θ) (yB n θ) t))) (D.distinguisherL n) -
      acceptProb (fun s => K n θ (pairFstD (is n (xA n θ) (yB n θ) s))) (D.distinguisherL n)|
  have hmax : ∀ n, Nonempty (Θ n) → ∃ θs : Θ n, ∀ θ, gap n θ ≤ gap n θs := fun n hn => by
    obtain ⟨θs, -, h⟩ := exists_max_image univ (gap n) univ_nonempty
    exact ⟨θs, fun θ => h θ (mem_univ θ)⟩
  -- the advice: the template of the worst instance
  let β : ℕ → List Bool := fun n => if h : Nonempty (Θ n) then
    tmplW (hdr n (Classical.choose (hmax n h))) (pre n (Classical.choose (hmax n h)))
      (suf n (Classical.choose (hmax n h))) (out n (Classical.choose (hmax n h))) else []
  have hβ : ∀ n, (β n).length ≤ q.eval n := fun n => by
    by_cases h : Nonempty (Θ n)
    · simp only [β, dif_pos h]
      exact hq n _
    · simp only [β, dif_neg h, List.length_nil]
      exact Nat.zero_le _
  obtain ⟨Dh, hc, hDh⟩ := exists_pre D (polyTimeComputable_hybW calls rounds cρ vF b lead) β q hβ
    (.const 0)
  obtain ⟨ε, hε, hbound⟩ := hS Dh
  refine ⟨ε, hε, fun n θ => ?_⟩
  have hn : Nonempty (Θ n) := ⟨θ⟩
  have hθs := Classical.choose_spec (hmax n hn)
  -- `Dh` accepts a sample as `D` accepts the filled template of the worst instance
  have key : ∀ {σ : Type} [Fintype σ] (X : σ → List Bool),
      acceptProb X (Dh.distinguisherL n) =
        acceptProb (fun s => K n (Classical.choose (hmax n hn)) (pairFstD (X s)))
          (D.distinguisherL n) := by
    intro σ _ X
    rw [acceptProb_pre X Dh D (.const 0) n (fun w e => hybW calls rounds cρ vF b lead
      (pairEncode (pairEncode (List.replicate n true) (β n)) (pairEncode w e))) hc (hDh n)]
    refine Eq.trans ?_ (acceptProb_fst (τ := Fin ((PolyExpr.const 0).eval n) → Bool)
      (fun s => K n (Classical.choose (hmax n hn)) (pairFstD (X s))) (D.distinguisherL n))
    refine congrArg (fun f => acceptProb f (D.distinguisherL n)) (funext fun z => ?_)
    simp only [β, dif_pos hn]
    rw [hybW_tmplW]
  have h := hbound n (xA n (Classical.choose (hmax n hn))) (yB n (Classical.choose (hmax n hn)))
  rw [distAdv_def, key, key] at h
  exact (hθs θ).trans h

end TCSlib.Cryptography.SecureComputation.ComposeSim

## ===== TCSlib/Cryptography/SecureComputation/Hybrid.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Honest-but-curious protocols in a hybrid model, ideal calls first (statement phase)

The `G`-hybrid model of [Gol04, §7.3.1] (oracle-aided protocols): the parties may hand inputs to
a trusted party computing a functionality `G` and receive its outputs. A protocol secure in that
model, with `G` then realized by a secure protocol, gives a secure protocol. This is
[Gol04, Theorem 7.3.3], the composition theorem (`SecureComputation/Compose.lean`).

[PS10]'s proof of Theorem 163.7 uses this step without stating it (inventory Thm-163.7). By the
ruling of 2026-11-05, Yao's protocol is first stated and proved in the OT-hybrid model, and the
real protocol follows by composition.

**The special case taken: all ideal calls first.** A `HybridProtocol G` makes `calls(n)` ideal
calls to `G`, then runs a protocol `main` of the ch. 2–4 model (D8).
- Each party computes its input to every call from `1^n`, its own input and its own coins (its
  coins in `main`), before any message. Yao's protocol is of this form: Alice's inputs are her
  wire keys (from her coins), Bob's are his input bits.
- In `main`, each party's private input is its input paired with its answers from the calls.
  Its view in `main` therefore holds its input, its coins, its answers and the messages it
  received: the view of [Gol04]'s oracle-aided protocol.
- Gol04's general form, with calls interleaved with messages, is not needed for Yao, and is not
  formalized.

**Security** is Definition 155.1 with the hybrid execution in the real samplers
(`HybridProtocol.HBCSecure`). It includes polynomial time (ruling of 2026-11-05):
- `main`'s strategies are PPT;
- the call inputs are polynomial-time computable;
- the messages of hybrid executions are polynomially bounded.

## Main definitions

* `SecureComputation.HybridProtocol`: a protocol in the `G`-hybrid model, ideal calls first.
* `HybridProtocol.answersA`, `answersB`, `privA`, `privB`: the answers and the private inputs
  of `main`.
* `HybridProtocol.realA`, `realB`: the real samplers of Definition 155.1 in the hybrid model.
* `HybridProtocol.PolyTime`, `HybridProtocol.HBCSecure`: polynomial time and security in the
  hybrid model.

## Main results

* `HybridProtocol.answersA_eq`, `answersB_eq`, `privA_eq`, `privB_eq`, `coins_eq`: the answers,
  complete private-input words and coin type.
* `HybridProtocol.realA_eq`, `realB_eq`, `polyTime_iff`, `hbcSecure_iff`: the sampler, time and
  security clauses.
* `HybridProtocol.pairFstD_privA`, `pairSndD_privA`, `pairFstD_privB`, `pairSndD_privB`: a
  party's private input in `main` decodes to its input and its answers.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2, Definition 155.1 and Theorem 163.7 (book pp. 155–164).
* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2*, Cambridge University Press,
  2004, §7.3.1 (oracle-aided protocols, privacy reductions) and Theorem 7.3.3.
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing TCSlib.Cryptography

/-- **A protocol in the `G`-hybrid model, ideal calls first** [Gol04, §7.3.1, oracle-aided
protocols, specialized]: `calls(n)` calls to a trusted party computing `G`, whose inputs each
party computes from `1^n`, its input and its coins in `main`; then the protocol `main`, in which
each party's private input is its input paired with its answers. -/
structure HybridProtocol (G : Functionality) where
  /-- The protocol run after the ideal calls. -/
  main : Protocol
  /-- The number of ideal calls. -/
  calls : PolyExpr
  /-- Alice's input to call `j`, from `n`, her input and her coins. -/
  callA : ∀ n, List Bool → List Bool → Fin (calls.eval n) → Fin (G.inA.eval n) → Bool
  /-- Bob's input to call `j`, from `n`, his input and his coins. -/
  callB : ∀ n, List Bool → List Bool → Fin (calls.eval n) → Fin (G.inB.eval n) → Bool

namespace HybridProtocol

variable {G : Functionality} (H : HybridProtocol G)

/-- **Alice's answers**: her outputs from the `calls(n)` ideal calls, concatenated, for the
inputs `x`, `y` and the coins `rA`, `rB`. -/
def answersA (n : ℕ) (x y rA rB : List Bool) : List Bool :=
  (List.ofFn fun j : Fin (H.calls.eval n) =>
    List.ofFn (G.f n (H.callA n x rA j) (H.callB n y rB j)).1).flatten

/-- Alice's answers are the concatenation of her ideal outputs in call order. -/
theorem answersA_eq (n : ℕ) (x y rA rB : List Bool) :
    H.answersA n x y rA rB =
      (List.ofFn fun j : Fin (H.calls.eval n) =>
        List.ofFn (G.f n (H.callA n x rA j) (H.callB n y rB j)).1).flatten := rfl

/-- **Bob's answers**: his outputs from the ideal calls, concatenated. -/
def answersB (n : ℕ) (x y rA rB : List Bool) : List Bool :=
  (List.ofFn fun j : Fin (H.calls.eval n) =>
    List.ofFn (G.f n (H.callA n x rA j) (H.callB n y rB j)).2).flatten

/-- Bob's answers are the concatenation of his ideal outputs in call order. -/
theorem answersB_eq (n : ℕ) (x y rA rB : List Bool) :
    H.answersB n x y rA rB =
      (List.ofFn fun j : Fin (H.calls.eval n) =>
        List.ofFn (G.f n (H.callA n x rA j) (H.callB n y rB j)).2).flatten := rfl

/-- Alice's private input in `main`: `⟨x, her answers⟩`. -/
def privA (n : ℕ) (x y rA rB : List Bool) : List Bool := pairEncode x (H.answersA n x y rA rB)

/-- Alice's complete private-input word pairs her original input with her ideal answers. -/
theorem privA_eq (n : ℕ) (x y rA rB : List Bool) :
    H.privA n x y rA rB = pairEncode x (H.answersA n x y rA rB) := rfl

/-- Bob's private input in `main`: `⟨y, his answers⟩`. -/
def privB (n : ℕ) (x y rA rB : List Bool) : List Bool := pairEncode y (H.answersB n x y rA rB)

/-- Bob's complete private-input word pairs his original input with his ideal answers. -/
theorem privB_eq (n : ℕ) (x y rA rB : List Bool) :
    H.privB n x y rA rB = pairEncode y (H.answersB n x y rA rB) := rfl

/-- Alice's private input decodes to her input. -/
@[simp] theorem pairFstD_privA (n : ℕ) (x y rA rB : List Bool) :
    pairFstD (H.privA n x y rA rB) = x := by
  simp [privA]

/-- Alice's private input decodes to her answers. -/
@[simp] theorem pairSndD_privA (n : ℕ) (x y rA rB : List Bool) :
    pairSndD (H.privA n x y rA rB) = H.answersA n x y rA rB := by
  simp [privA]

/-- Bob's private input decodes to his input. -/
@[simp] theorem pairFstD_privB (n : ℕ) (x y rA rB : List Bool) :
    pairFstD (H.privB n x y rA rB) = y := by
  simp [privB]

/-- Bob's private input decodes to his answers. -/
@[simp] theorem pairSndD_privB (n : ℕ) (x y rA rB : List Bool) :
    pairSndD (H.privB n x y rA rB) = H.answersB n x y rA rB := by
  simp [privB]

/-- The coins of a hybrid execution at `n`: Alice's and Bob's tapes in `main`. -/
abbrev Coins (n : ℕ) : Type := H.main.ExecCoins H.main.P (List.replicate n true)

/-- The hybrid coin type is the pair of main-protocol tapes on the unary common input. -/
theorem coins_eq (n : ℕ) :
    H.Coins n = H.main.ExecCoins H.main.P (List.replicate n true) := rfl

/-- **The hybrid real sampler for Alice's side**: on the coins of a hybrid execution with common
input `1^n`, `⟨view_A, out_B⟩`, where Alice's view in `main` holds her input, her answers, her
coins and the messages she received. -/
def realA (F : Functionality) (n : ℕ) (x : Fin (F.inA.eval n) → Bool)
    (y : Fin (F.inB.eval n) → Bool) : H.Coins n → List Bool := fun r =>
  pairEncode (H.main.viewP (List.replicate n true)
      (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
      (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2)) r).encode
    (H.main.outV H.main.P (List.replicate n true)
      (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
      (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2)) r)

/-- Alice's hybrid real sampler pairs her main-protocol view with Bob's output, using the
complete private inputs formed from the parties' inputs and ideal answers. -/
theorem realA_eq (F : Functionality) (n : ℕ) (x : Fin (F.inA.eval n) → Bool)
    (y : Fin (F.inB.eval n) → Bool) (r : H.Coins n) :
    H.realA F n x y r =
      pairEncode (H.main.viewP (List.replicate n true)
          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2)) r).encode
        (H.main.outV H.main.P (List.replicate n true)
          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2)) r) := rfl

/-- **The hybrid real sampler for Bob's side**: `⟨view_B, out_A⟩`. -/
def realB (F : Functionality) (n : ℕ) (x : Fin (F.inA.eval n) → Bool)
    (y : Fin (F.inB.eval n) → Bool) : H.Coins n → List Bool := fun r =>
  pairEncode (H.main.viewV (List.replicate n true)
      (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
      (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2)) r).encode
    (H.main.outP (List.replicate n true)
      (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
      (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2)) r)

/-- Bob's hybrid real sampler pairs his main-protocol view with Alice's output, using the
complete private inputs formed from the parties' inputs and ideal answers. -/
theorem realB_eq (F : Functionality) (n : ℕ) (x : Fin (F.inA.eval n) → Bool)
    (y : Fin (F.inB.eval n) → Bool) (r : H.Coins n) :
    H.realB F n x y r =
      pairEncode (H.main.viewV (List.replicate n true)
          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2)) r).encode
        (H.main.outP (List.replicate n true)
          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2)) r) := rfl

/-- **The parties run in polynomial time** in the hybrid model, on `F`'s inputs (ruling of
2026-11-05, as `Functionality.PolyTime`):
- `main`'s strategies are PPT;
- the call inputs are computed in polynomial time from `⟨1^n, ⟨input, ⟨coins, 1^j⟩⟩⟩`;
- for a polynomial `B`, every message of `main` has at most `B(n)` bits, in every execution on
  private inputs of the hybrid format `⟨input, answers⟩`, for **any** answers of the right
  lengths. The ideal answers are a special case. The composition theorem feeds `main` the
  sub-protocol's outputs, which equal the ideal answers only computationally. -/
def PolyTime (F : Functionality) : Prop :=
  H.main.P.Efficient ∧ H.main.V.Efficient ∧
    (∃ f : List Bool → List Bool, PolyTimeComputable f ∧
      ∀ n (x r : List Bool) (j : Fin (H.calls.eval n)),
        f (pairEncode (List.replicate n true) (pairEncode x (pairEncode r
          (List.replicate j true)))) = List.ofFn (H.callA n x r j)) ∧
    (∃ f : List Bool → List Bool, PolyTimeComputable f ∧
      ∀ n (y r : List Bool) (j : Fin (H.calls.eval n)),
        f (pairEncode (List.replicate n true) (pairEncode y (pairEncode r
          (List.replicate j true)))) = List.ofFn (H.callB n y r j)) ∧
    ∃ B : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool)
      (aA : Fin (H.calls.eval n * G.outA.eval n) → Bool)
      (aB : Fin (H.calls.eval n * G.outB.eval n) → Bool) (r : H.Coins n),
      ∀ msg ∈ (H.main.transcript (List.replicate n true)
          (pairEncode (List.ofFn x) (List.ofFn aA))
          (pairEncode (List.ofFn y) (List.ofFn aB)) r).1 ++
        (H.main.transcript (List.replicate n true)
          (pairEncode (List.ofFn x) (List.ofFn aA))
          (pairEncode (List.ofFn y) (List.ofFn aB)) r).2,
        msg.length ≤ B.eval n

/-- Hybrid polynomial time consists of efficient main strategies, polynomial-time call inputs,
and a polynomial bound on messages for every pair of answer strings of the required lengths.

**Proof sketch.** The right-hand side repeats the definition's strategy, call-input and
message-bound clauses in the same order, so the equivalence is reflexive. -/
theorem polyTime_iff (F : Functionality) :
    H.PolyTime F ↔
      H.main.P.Efficient ∧ H.main.V.Efficient ∧
        (∃ f : List Bool → List Bool, PolyTimeComputable f ∧
          ∀ n (x r : List Bool) (j : Fin (H.calls.eval n)),
            f (pairEncode (List.replicate n true) (pairEncode x (pairEncode r
              (List.replicate j true)))) = List.ofFn (H.callA n x r j)) ∧
        (∃ f : List Bool → List Bool, PolyTimeComputable f ∧
          ∀ n (y r : List Bool) (j : Fin (H.calls.eval n)),
            f (pairEncode (List.replicate n true) (pairEncode y (pairEncode r
              (List.replicate j true)))) = List.ofFn (H.callB n y r j)) ∧
        ∃ B : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool)
          (aA : Fin (H.calls.eval n * G.outA.eval n) → Bool)
          (aB : Fin (H.calls.eval n * G.outB.eval n) → Bool) (r : H.Coins n),
          ∀ msg ∈ (H.main.transcript (List.replicate n true)
              (pairEncode (List.ofFn x) (List.ofFn aA))
              (pairEncode (List.ofFn y) (List.ofFn aB)) r).1 ++
            (H.main.transcript (List.replicate n true)
              (pairEncode (List.ofFn x) (List.ofFn aA))
              (pairEncode (List.ofFn y) (List.ofFn aB)) r).2,
            msg.length ≤ B.eval n := Iff.rfl

/-- **Honest-but-curious security in the `G`-hybrid model** [PS10, Definition 155.1, with the
hybrid execution of [Gol04, §7.3.1]]: the parties run in polynomial time (`PolyTime`), and
there are non-uniform PPT simulators `S_A`, `S_B` such that for every non-uniform PPT
distinguisher `D` there is a negligible `ε` with, for all `n` and all inputs `x`, `y`, `D`'s
advantage between Alice's hybrid real and ideal samplers, and between Bob's, at most `ε(n)`. -/
def HBCSecure (F : Functionality) : Prop :=
  H.PolyTime F ∧ ∃ SA SB : NUPPT, ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool),
      distAdv (H.realA F n x y) (F.idealA SA n x y) (D.distinguisherL n) ≤ ε n ∧
        distAdv (H.realB F n x y) (F.idealB SB n x y) (D.distinguisherL n) ≤ ε n

/-- Hybrid honest-but-curious security consists of hybrid polynomial time and two simulators
with negligible distinguishing advantages uniform over inputs of each length. -/
theorem hbcSecure_iff (F : Functionality) :
    H.HBCSecure F ↔
      H.PolyTime F ∧ ∃ SA SB : NUPPT, ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
        ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool),
          distAdv (H.realA F n x y) (F.idealA SA n x y) (D.distinguisherL n) ≤ ε n ∧
            distAdv (H.realB F n x y) (F.idealB SB n x y) (D.distinguisherL n) ≤ ε n := Iff.rfl

end HybridProtocol

end TCSlib.Cryptography.SecureComputation

## ===== TCSlib/Cryptography/SecureComputation/Compose.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Hybrid

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Sequential composition in the hybrid model: the composed protocol

The protocol of the composition theorem [Gol04, §7.3.1, Theorem 7.3.3]: a protocol `H` in the
`G`-hybrid model (`HybridProtocol`, ideal calls first) with its ideal calls replaced by runs of
a protocol `ρ` meant to compute `G`, on the interaction model of
`ZeroKnowledge/Interaction.lean` (D8). Its phase lemmas are in `ComposePhases.lean`, and the
composition theorem, `hbcSecure_compose`, in `ComposeSecurity.lean`. The section and theorem
numbers of [Gol04] are cited from memory and should be verified at audit.

**The layout** of `H.compose ρ` (`HybridProtocol.compose`). Write `n = |x|` for the common input
`x = 1^n`, `L = calls(n)`, `R = ρ.rounds(n)`, `M = main.rounds(n)`, and `lead = 1` if `main`'s
verifier (Bob) moves first, `0` otherwise. Alice (the prover) moves first and the parties
alternate, Alice at the even positions `t` and Bob at the odd ones, for `L · 2R + lead + M`
moves.
- **The runs.** The positions `t < L · 2R` form the `L · R` pairs `(2q, 2q + 1)`. Pair
  `q = R · j + p` carries `ρ`'s move `p` of run `j`: at its even position if `ρ`'s mover `p` is
  Alice, at its odd one if it is Bob. The other position is a **filler**, the empty message `[]`.
  Run `j` is an honest execution of `ρ` on the inputs of call `j` (`callA`, `callB`, computed
  from the parties' inputs and their tapes for `main`) and on the parties' `j`-th `ρ`-tapes.
- **The main phase.** If `main`'s verifier moves first, one leading `[]` from Alice; then
  `main`'s `M` moves. Each party's private input in `main` is its input paired with its
  **answers**: its outputs of the `L` runs, each read at `G`'s output length (`padFin`) and
  concatenated, in place of the ideal answers of the hybrid model.
- **Coins.** Each party's tape is its tape for `main`, then one `ρ`-tape per run.
- **Positions.** A party finds its position from the number of messages it has received:
  Alice, having received `k`, is at pair `k`; Bob, having received `c ≥ 1`, at pair `c − 1`.

**Why fillers.** D8 executions alternate strictly, while consecutive runs of `ρ` may give one
party two moves in a row (when `R` is odd), and so may the passage from the runs to `main`.
Giving each move of `ρ` its own pair keeps the alternation without parity arithmetic on
`PolyExpr`s; the leading filler does the same before `main`.

**Why no trailing filler: D8's output convention.** A party's output is its next-message
function on its complete history, so the last mover's output is its last message, which the
other party receives. With `M ≥ 1` the last move is `main`'s last move, whose mover outputs that
message in `main` as well. A trailing filler would make its sender's output part of the other
party's view. For the same reason the composition needs `M ≥ 1`: with `M = 0` the last move is a
run move or the leading filler, and its sender's output is that message, not its output in
`main` (`ComposePhases.lean`, `ComposeSecurity.lean`).

**Deviations from [Gol04, §7.3.1].**
- **Calls first only.** Gol04's oracle-aided protocols interleave calls and messages. Here all
  calls come first (`HybridProtocol`), so all runs of `ρ` precede `main`.
- **Strict alternation by fillers**, as above: `2R` moves per run and the leading filler.
- **Answers at `G`'s lengths.** A party's answer from a run is its `ρ`-output padded or truncated
  to `G`'s output length; it is the ideal answer when `ρ`'s output is correct.

## Main definitions

* `Compose.moveMsg`, `Compose.slotMsgs`, `Compose.runTape`: the message of a move, the messages
  of a run read at the pair positions, and the tape of a run.
* `HybridProtocol.lead`: the leading filler of the main phase.
* `HybridProtocol.runInputA`, `runInputB`, `runNextA`, `runNextB`, `answersFromA`,
  `answersFromB`: the parties' inputs, moves and answers of the runs.
* `HybridProtocol.composeP`, `composeV`, `compose`: the composed protocol.

## Main results

* `Compose.exec_eq_map`: the messages each party receives are the messages of the other party's
  moves, in order.
* `HybridProtocol.compose_rounds`, `compose_rounds_eval`, `compose_verifierFirst`,
  `compose_P_coinLen`, `compose_V_coinLen`: the shape of `H.compose ρ`.

## References

* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
  University Press, 2004, §7.3.1 (privacy reductions and a composition theorem), Theorem 7.3.3.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §4.4 (interactive protocols) and §6.2, Definition 155.1 (book pp. 114–116, 155).
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing TCSlib.Cryptography

namespace Compose

/-! ### Executions, slots and tapes -/

/-- **The message of move `k`** of the execution `P_{rP}(x, zP) ↔ V_{rV}(x, zV)` with first mover
`vF` [PS10, §4.4]: the next message of the party moving at `k` on the messages it has received
in the first `k` moves. -/
def moveMsg (P V : Strategy) (vF : Bool) (x zP zV rP rV : List Bool) (k : ℕ) : List Bool :=
  if moverIsV vF k then V.next x zV rV (exec P V vF x zP zV rP rV k).2
  else P.next x zP rP (exec P V vF x zP zV rP rV k).1

/-- The message of move `k` is `V.next` on `V`'s received messages if `V` moves at `k`, and
`P.next` on `P`'s otherwise. -/
theorem moveMsg_eq (P V : Strategy) (vF : Bool) (x zP zV rP rV : List Bool) (k : ℕ) :
    moveMsg P V vF x zP zV rP rV k =
      if moverIsV vF k then V.next x zV rV (exec P V vF x zP zV rP rV k).2
      else P.next x zP rP (exec P V vF x zP zV rP rV k).1 := rfl

/-- **The received messages are the other party's moves**: after `k` moves, `P` has received the
messages of the moves `i < k` made by `V`, and `V` those of the moves `i < k` made by `P`, in
order.

**Proof sketch.** Induction on `k`: move `k` appends its message, `moveMsg k`, to the list of the
party not moving (`exec_succ`), and `k` joins that party's side of the filter of
`range (k + 1)`. -/
theorem exec_eq_map (P V : Strategy) (vF : Bool) (x zP zV rP rV : List Bool) (k : ℕ) :
    exec P V vF x zP zV rP rV k =
      (((List.range k).filter (moverIsV vF)).map (moveMsg P V vF x zP zV rP rV),
        ((List.range k).filter fun i => !moverIsV vF i).map (moveMsg P V vF x zP zV rP rV)) := by
  induction k with
  | zero => simp only [exec_zero, List.range_zero, List.filter_nil, List.map_nil]
  | succ k ih =>
    rw [exec_succ, List.range_succ, List.filter_append, List.filter_append, List.map_append,
      List.map_append]
    cases h : moverIsV vF k
    · have hm : moveMsg P V vF x zP zV rP rV k =
          P.next x zP rP (exec P V vF x zP zV rP rV k).1 := by
        rw [moveMsg_eq, h, if_neg Bool.false_ne_true]
      simp only [h, Bool.false_eq_true, if_false, List.filter_cons, List.filter_nil,
        Bool.not_false, if_true, List.map_cons, List.map_nil, List.append_nil]
      rw [hm, ih]
    · have hm : moveMsg P V vF x zP zV rP rV k =
          V.next x zV rV (exec P V vF x zP zV rP rV k).2 := by
        rw [moveMsg_eq, h, if_pos rfl]
      simp only [h, if_true, List.filter_cons, List.filter_nil, Bool.not_true,
        Bool.false_eq_true, if_false, List.map_cons, List.map_nil, List.append_nil]
      rw [hm, ih]

/-- With the verifier first, the prover has received a message after any positive number of
moves. -/
theorem exec_fst_length_pos (P V : Strategy) {vF : Bool} (x zP zV rP rV : List Bool) {k : ℕ}
    (hv : vF = true) (hk : 0 < k) : 0 < (exec P V vF x zP zV rP rV k).1.length := by
  rw [exec_eq_map, List.length_map]
  refine List.length_pos_of_mem (a := 0) (List.mem_filter.2 ⟨List.mem_range.2 hk, ?_⟩)
  rw [hv, moverIsV_true]
  rfl

/-- With the prover first, the verifier has received a message after any positive number of
moves. -/
theorem exec_snd_length_pos (P V : Strategy) {vF : Bool} (x zP zV rP rV : List Bool) {k : ℕ}
    (hv : vF = false) (hk : 0 < k) : 0 < (exec P V vF x zP zV rP rV k).2.length := by
  rw [exec_eq_map, List.length_map]
  refine List.length_pos_of_mem (a := 0) (List.mem_filter.2 ⟨List.mem_range.2 hk, ?_⟩)
  rw [hv, moverIsV_false]
  rfl

/-- **The messages of a run read from the pairs**: the entries `off + p'` of `hist` (`[]` beyond
its end), for the `p' < p` with `sel p'`, in order. -/
def slotMsgs (sel : ℕ → Bool) (off p : ℕ) (hist : List (List Bool)) : List (List Bool) :=
  ((List.range p).filter sel).map fun p' => hist.getD (off + p') []

/-- `slotMsgs sel off p hist` lists `hist[off + p']` over the `p' < p` with `sel p'`. -/
theorem slotMsgs_eq (sel : ℕ → Bool) (off p : ℕ) (hist : List (List Bool)) :
    slotMsgs sel off p hist = ((List.range p).filter sel).map fun p' => hist.getD (off + p') [] :=
  rfl

/-- If `hist[off + p'] = f p'` at the selected `p' < p`, the run's messages are the `f p'`. -/
theorem slotMsgs_eq_map {sel : ℕ → Bool} {off p : ℕ} {hist : List (List Bool)}
    {f : ℕ → List Bool} (hf : ∀ p' < p, sel p' = true → hist.getD (off + p') [] = f p') :
    slotMsgs sel off p hist = ((List.range p).filter sel).map f := by
  refine List.map_congr_left fun p' hp' => ?_
  rw [List.mem_filter, List.mem_range] at hp'
  exact hf p' hp'.1 hp'.2

/-- **The tape of run `j`**: the `c` bits after the first `c₀ + j · c` bits of `r`. -/
def runTape (c₀ c j : ℕ) (r : List Bool) : List Bool := (r.drop (c₀ + j * c)).take c

/-- The tape of run `j` is `r[c₀ + j·c, c₀ + (j + 1)·c)`. -/
theorem runTape_eq (c₀ c j : ℕ) (r : List Bool) : runTape c₀ c j r = (r.drop (c₀ + j * c)).take c :=
  rfl

/-- The tape of run `j < L` of a tape of `c₀ + L·c` bits has `c` bits. -/
theorem length_runTape {c₀ c j L : ℕ} {r : List Bool} (hr : r.length = c₀ + L * c)
    (hj : j < L) : (runTape c₀ c j r).length = c := by
  have := Nat.mul_le_mul_right c (Nat.succ_le_of_lt hj)
  rw [Nat.succ_mul] at this
  rw [runTape_eq, List.length_take, List.length_drop, hr]
  omega

/-- Entry `i < q` of `[f 0, …, f (q − 1)]` is `f i`. -/
theorem getD_map_range {f : ℕ → List Bool} {q i : ℕ} (h : i < q) :
    ((List.range q).map f).getD i [] = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

/-- An entry of the first part of an append. -/
theorem getD_append_left {l₁ l₂ : List (List Bool)} {i : ℕ} (h : i < l₁.length) :
    (l₁ ++ l₂).getD i [] = l₁.getD i [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, ← List.getD_eq_getElem?_getD]

/-- With the prover first, the prover moves at the even positions. -/
theorem moverIsV_false_two_mul (q : ℕ) : moverIsV false (2 * q) = false := by
  rw [moverIsV_false, decide_eq_false_iff_not]
  omega

/-- With the prover first, the verifier moves at the odd positions. -/
theorem moverIsV_false_two_mul_add_one (q : ℕ) : moverIsV false (2 * q + 1) = true := by
  rw [moverIsV_false, decide_eq_true_eq]
  omega

end Compose

open Compose

namespace HybridProtocol

/-! ### The composed protocol -/

section Construction

variable {G : Functionality} (H : HybridProtocol G) (ρ : Protocol)

/-- **The leading filler** of the main phase: `1` if `main`'s verifier (Bob) moves first, so that
Alice's empty message hands the move to Bob; `0` otherwise. -/
def lead : ℕ := if H.main.verifierFirst then 1 else 0

/-- `lead = 1` if `main`'s verifier moves first, `0` otherwise. -/
theorem lead_eq : H.lead = if H.main.verifierFirst then 1 else 0 := rfl

/-- With `main`'s verifier first there is one leading filler. -/
theorem lead_of_true (h : H.main.verifierFirst = true) : H.lead = 1 := by
  rw [lead_eq, if_pos h]

/-- With `main`'s prover first there is no leading filler. -/
theorem lead_of_false (h : H.main.verifierFirst = false) : H.lead = 0 := by
  rw [lead_eq, h]
  rfl

/-- **Alice's input to run `j`**, on common input `x`, input `z` and composed tape `r`: her input
to ideal call `j`, `callA(|x|, z, r_main, j)` with `r_main` the first `main.P.coins(|x|)` bits
of `r`, when `j < calls(|x|)`; `[]` otherwise (never used). -/
def runInputA (x z r : List Bool) (j : ℕ) : List Bool :=
  if h : j < H.calls.eval x.length then
    List.ofFn (H.callA x.length z (r.take (H.main.P.coins.eval x.length)) ⟨j, h⟩)
  else []

/-- For `j < calls(|x|)`, Alice's input to run `j` is her input to call `j`. -/
theorem runInputA_of_lt (x z r : List Bool) {j : ℕ} (h : j < H.calls.eval x.length) :
    H.runInputA x z r j =
      List.ofFn (H.callA x.length z (r.take (H.main.P.coins.eval x.length)) ⟨j, h⟩) := by
  rw [runInputA, dif_pos h]

/-- For `j ≥ calls(|x|)`, Alice's input to run `j` is `[]`. -/
theorem runInputA_of_ge (x z r : List Bool) {j : ℕ} (h : H.calls.eval x.length ≤ j) :
    H.runInputA x z r j = [] := by
  rw [runInputA, dif_neg (Nat.not_lt.2 h)]

/-- **Bob's input to run `j`**: his input to ideal call `j`, `callB(|x|, z, r_main, j)` with
`r_main` the first `main.V.coins(|x|)` bits of his tape, when `j < calls(|x|)`; `[]`
otherwise. -/
def runInputB (x z r : List Bool) (j : ℕ) : List Bool :=
  if h : j < H.calls.eval x.length then
    List.ofFn (H.callB x.length z (r.take (H.main.V.coins.eval x.length)) ⟨j, h⟩)
  else []

/-- For `j < calls(|x|)`, Bob's input to run `j` is his input to call `j`. -/
theorem runInputB_of_lt (x z r : List Bool) {j : ℕ} (h : j < H.calls.eval x.length) :
    H.runInputB x z r j =
      List.ofFn (H.callB x.length z (r.take (H.main.V.coins.eval x.length)) ⟨j, h⟩) := by
  rw [runInputB, dif_pos h]

/-- For `j ≥ calls(|x|)`, Bob's input to run `j` is `[]`. -/
theorem runInputB_of_ge (x z r : List Bool) {j : ℕ} (h : H.calls.eval x.length ≤ j) :
    H.runInputB x z r j = [] := by
  rw [runInputB, dif_neg (Nat.not_lt.2 h)]

/-- **Alice's `ρ`-move in run `j` after `p` pairs of the run**: `ρ.P.next` on her input to run
`j`, her `j`-th `ρ`-tape, and Bob's run-`j` messages among the pairs `R·j + p'`, `p' < p`, where
`ρ`'s mover `p'` is Bob (Bob's message of pair `q` is `hist[q]`). With `p = R` it is her output of
run `j`. -/
def runNextA (x z r : List Bool) (hist : List (List Bool)) (j p : ℕ) : List Bool :=
  ρ.P.next x (H.runInputA x z r j)
    (runTape (H.main.P.coins.eval x.length) (ρ.P.coins.eval x.length) j r)
    (slotMsgs (moverIsV ρ.verifierFirst) (ρ.rounds.eval x.length * j) p hist)

/-- Alice's `ρ`-move in run `j` is `ρ.P.next` on her run input, run tape and run messages. -/
theorem runNextA_eq (x z r : List Bool) (hist : List (List Bool)) (j p : ℕ) :
    H.runNextA ρ x z r hist j p =
      ρ.P.next x (H.runInputA x z r j)
        (runTape (H.main.P.coins.eval x.length) (ρ.P.coins.eval x.length) j r)
        (slotMsgs (moverIsV ρ.verifierFirst) (ρ.rounds.eval x.length * j) p hist) := rfl

/-- **Bob's `ρ`-move in run `j` after `p` pairs of the run**: `ρ.V.next` on his input to run `j`,
his `j`-th `ρ`-tape, and Alice's run-`j` messages among the pairs `R·j + p'`, `p' < p`, where
`ρ`'s mover `p'` is Alice (Alice's message of pair `q` is `hist[q]`). With `p = R` it is his
output of run `j`. -/
def runNextB (x z r : List Bool) (hist : List (List Bool)) (j p : ℕ) : List Bool :=
  ρ.V.next x (H.runInputB x z r j)
    (runTape (H.main.V.coins.eval x.length) (ρ.V.coins.eval x.length) j r)
    (slotMsgs (fun p' => !moverIsV ρ.verifierFirst p') (ρ.rounds.eval x.length * j) p hist)

/-- Bob's `ρ`-move in run `j` is `ρ.V.next` on his run input, run tape and run messages. -/
theorem runNextB_eq (x z r : List Bool) (hist : List (List Bool)) (j p : ℕ) :
    H.runNextB ρ x z r hist j p =
      ρ.V.next x (H.runInputB x z r j)
        (runTape (H.main.V.coins.eval x.length) (ρ.V.coins.eval x.length) j r)
        (slotMsgs (fun p' => !moverIsV ρ.verifierFirst p') (ρ.rounds.eval x.length * j) p
          hist) := rfl

/-- **Alice's answers** read from her history: her outputs of the `calls(|x|)` runs, each padded
or truncated to `G.outA(|x|)` bits, concatenated. -/
def answersFromA (x z r : List Bool) (hist : List (List Bool)) : List Bool :=
  (List.ofFn fun j : Fin (H.calls.eval x.length) =>
    List.ofFn (padFin (G.outA.eval x.length)
      (H.runNextA ρ x z r hist j (ρ.rounds.eval x.length)))).flatten

/-- Alice's answers are her padded run outputs, concatenated. -/
theorem answersFromA_eq (x z r : List Bool) (hist : List (List Bool)) :
    H.answersFromA ρ x z r hist =
      (List.ofFn fun j : Fin (H.calls.eval x.length) =>
        List.ofFn (padFin (G.outA.eval x.length)
          (H.runNextA ρ x z r hist j (ρ.rounds.eval x.length)))).flatten := rfl

/-- **Bob's answers** read from his history: his outputs of the runs, each padded or truncated to
`G.outB(|x|)` bits, concatenated. -/
def answersFromB (x z r : List Bool) (hist : List (List Bool)) : List Bool :=
  (List.ofFn fun j : Fin (H.calls.eval x.length) =>
    List.ofFn (padFin (G.outB.eval x.length)
      (H.runNextB ρ x z r hist j (ρ.rounds.eval x.length)))).flatten

/-- Bob's answers are his padded run outputs, concatenated. -/
theorem answersFromB_eq (x z r : List Bool) (hist : List (List Bool)) :
    H.answersFromB ρ x z r hist =
      (List.ofFn fun j : Fin (H.calls.eval x.length) =>
        List.ofFn (padFin (G.outB.eval x.length)
          (H.runNextB ρ x z r hist j (ρ.rounds.eval x.length)))).flatten := rfl

/-- **Alice in `H.compose ρ`** [Gol04, §7.3.1, the composed protocol], on common input `x`
(`n = |x|`, `L = calls(n)`, `R = ρ.rounds(n)`), input `z` and tape `r`, having received the
`k = |hist|` messages `hist`; her move is at position `2k`, in pair `k`.
- If `k < L·R` (run `j = k / R`, position `p = k % R`): `[]` if `ρ`'s mover `p` is Bob; otherwise
  her `ρ`-move (`runNextA`).
- Else, if `main`'s verifier moves first and `k = L·R`: the leading filler `[]`.
- Else: `main.P.next` on `⟨z, her answers⟩`, her `main`-tape (the first `main.P.coins(n)` bits)
  and the messages received after the runs.

Her tape is her `main`-tape followed by `L` tapes for `ρ`. -/
def composeP : Strategy where
  next x z r hist :=
    if hist.length < H.calls.eval x.length * ρ.rounds.eval x.length then
      if moverIsV ρ.verifierFirst (hist.length % ρ.rounds.eval x.length) then []
      else H.runNextA ρ x z r hist (hist.length / ρ.rounds.eval x.length)
        (hist.length % ρ.rounds.eval x.length)
    else if H.main.verifierFirst = true ∧
        hist.length = H.calls.eval x.length * ρ.rounds.eval x.length then []
    else H.main.P.next x (pairEncode z (H.answersFromA ρ x z r hist))
      (r.take (H.main.P.coins.eval x.length))
      (hist.drop (H.calls.eval x.length * ρ.rounds.eval x.length))
  coins := .add H.main.P.coins (.mul H.calls ρ.P.coins)

/-- Alice's next message in `H.compose ρ` (see `composeP`). -/
theorem composeP_next (x z r : List Bool) (hist : List (List Bool)) :
    (H.composeP ρ).next x z r hist =
      if hist.length < H.calls.eval x.length * ρ.rounds.eval x.length then
        if moverIsV ρ.verifierFirst (hist.length % ρ.rounds.eval x.length) then []
        else H.runNextA ρ x z r hist (hist.length / ρ.rounds.eval x.length)
          (hist.length % ρ.rounds.eval x.length)
      else if H.main.verifierFirst = true ∧
          hist.length = H.calls.eval x.length * ρ.rounds.eval x.length then []
      else H.main.P.next x (pairEncode z (H.answersFromA ρ x z r hist))
        (r.take (H.main.P.coins.eval x.length))
        (hist.drop (H.calls.eval x.length * ρ.rounds.eval x.length)) := rfl

/-- Alice's coins in `H.compose ρ`: `main.P.coins + calls · ρ.P.coins`. -/
theorem composeP_coins : (H.composeP ρ).coins = .add H.main.P.coins (.mul H.calls ρ.P.coins) :=
  rfl

/-- **Bob in `H.compose ρ`**, on common input `x`, input `z` and tape `r`, having received the
`c = |hist|` messages `hist`; his move is at position `2c − 1`, in pair `q = c − 1`.
- If `q < L·R` (run `j = q / R`, position `p = q % R`): his `ρ`-move (`runNextB`) if `ρ`'s mover
  `p` is Bob; otherwise `[]`.
- Else: `main.V.next` on `⟨z, his answers⟩`, his `main`-tape and the messages received after
  the runs and the leading filler.

His tape is his `main`-tape followed by `L` tapes for `ρ`. -/
def composeV : Strategy where
  next x z r hist :=
    if hist.length - 1 < H.calls.eval x.length * ρ.rounds.eval x.length then
      if moverIsV ρ.verifierFirst ((hist.length - 1) % ρ.rounds.eval x.length) then
        H.runNextB ρ x z r hist ((hist.length - 1) / ρ.rounds.eval x.length)
          ((hist.length - 1) % ρ.rounds.eval x.length)
      else []
    else H.main.V.next x (pairEncode z (H.answersFromB ρ x z r hist))
      (r.take (H.main.V.coins.eval x.length))
      (hist.drop (H.calls.eval x.length * ρ.rounds.eval x.length + H.lead))
  coins := .add H.main.V.coins (.mul H.calls ρ.V.coins)

/-- Bob's next message in `H.compose ρ` (see `composeV`). -/
theorem composeV_next (x z r : List Bool) (hist : List (List Bool)) :
    (H.composeV ρ).next x z r hist =
      if hist.length - 1 < H.calls.eval x.length * ρ.rounds.eval x.length then
        if moverIsV ρ.verifierFirst ((hist.length - 1) % ρ.rounds.eval x.length) then
          H.runNextB ρ x z r hist ((hist.length - 1) / ρ.rounds.eval x.length)
            ((hist.length - 1) % ρ.rounds.eval x.length)
        else []
      else H.main.V.next x (pairEncode z (H.answersFromB ρ x z r hist))
        (r.take (H.main.V.coins.eval x.length))
        (hist.drop (H.calls.eval x.length * ρ.rounds.eval x.length + H.lead)) := rfl

/-- Bob's coins in `H.compose ρ`: `main.V.coins + calls · ρ.V.coins`. -/
theorem composeV_coins : (H.composeV ρ).coins = .add H.main.V.coins (.mul H.calls ρ.V.coins) :=
  rfl

/-- **The composed protocol** `H.compose ρ` [Gol04, §7.3.1, the protocol of Theorem 7.3.3]: `H`
with its ideal calls to `G` replaced by runs of `ρ`. Alice (`composeP`) moves first; the
`calls · (2 · ρ.rounds) + lead + main.rounds` moves are the `calls` runs of `ρ`, each in `2 ·
ρ.rounds` moves with fillers, the leading filler, and `main` (see the module docstring). -/
def compose : Protocol where
  P := H.composeP ρ
  V := H.composeV ρ
  rounds := .add (.add (.mul H.calls (.mul (.const 2) ρ.rounds)) (.const H.lead)) H.main.rounds
  verifierFirst := false

/-- Alice's strategy in `H.compose ρ` is `composeP`. -/
theorem compose_P : (H.compose ρ).P = H.composeP ρ := rfl

/-- Bob's strategy in `H.compose ρ` is `composeV`. -/
theorem compose_V : (H.compose ρ).V = H.composeV ρ := rfl

/-- `H.compose ρ` has `calls · (2 · ρ.rounds) + lead + main.rounds` moves. -/
theorem compose_rounds :
    (H.compose ρ).rounds =
      .add (.add (.mul H.calls (.mul (.const 2) ρ.rounds)) (.const H.lead)) H.main.rounds := rfl

/-- At `n`, `H.compose ρ` has `calls(n) · (2 · ρ.rounds(n)) + lead + main.rounds(n)` moves. -/
theorem compose_rounds_eval (n : ℕ) :
    (H.compose ρ).rounds.eval n =
      H.calls.eval n * (2 * ρ.rounds.eval n) + H.lead + H.main.rounds.eval n := rfl

/-- In `H.compose ρ` Alice (the prover) moves first. -/
theorem compose_verifierFirst : (H.compose ρ).verifierFirst = false := rfl

/-- Alice's tape in `H.compose ρ` has `main.P.coins(n) + calls(n) · ρ.P.coins(n)` bits.

**Proof sketch.** Read the strategy and its coin polynomial through their public equations,
evaluate the sum and product, and re-express the two component lengths with `Strategy.coinLen_eq`. -/
theorem compose_P_coinLen (n : ℕ) :
    (H.compose ρ).P.coinLen n = H.main.P.coinLen n + H.calls.eval n * ρ.P.coinLen n :=
  calc
    (H.compose ρ).P.coinLen n = (H.composeP ρ).coins.eval n :=
      (Strategy.coinLen_eq ((H.compose ρ).P) n).trans
        (congrArg (fun S : Strategy => S.coins.eval n) (H.compose_P ρ))
    _ = (PolyExpr.add H.main.P.coins (PolyExpr.mul H.calls ρ.P.coins)).eval n :=
      congrArg (fun p : PolyExpr => p.eval n) (H.composeP_coins ρ)
    _ = H.main.P.coins.eval n + H.calls.eval n * ρ.P.coins.eval n :=
      (PolyExpr.eval_add H.main.P.coins (.mul H.calls ρ.P.coins) n).trans
        (congrArg (fun c : ℕ => H.main.P.coins.eval n + c)
          (PolyExpr.eval_mul H.calls ρ.P.coins n))
    _ = H.main.P.coinLen n + H.calls.eval n * ρ.P.coinLen n :=
      congrArg₂ (fun a b : ℕ => a + b) (Strategy.coinLen_eq H.main.P n).symm
        (congrArg (fun c : ℕ => H.calls.eval n * c) (Strategy.coinLen_eq ρ.P n).symm)

/-- Bob's tape in `H.compose ρ` has `main.V.coins(n) + calls(n) · ρ.V.coins(n)` bits.

**Proof sketch.** Read the strategy and its coin polynomial through their public equations,
evaluate the sum and product, and re-express the two component lengths with `Strategy.coinLen_eq`. -/
theorem compose_V_coinLen (n : ℕ) :
    (H.compose ρ).V.coinLen n = H.main.V.coinLen n + H.calls.eval n * ρ.V.coinLen n :=
  calc
    (H.compose ρ).V.coinLen n = (H.composeV ρ).coins.eval n :=
      (Strategy.coinLen_eq ((H.compose ρ).V) n).trans
        (congrArg (fun S : Strategy => S.coins.eval n) (H.compose_V ρ))
    _ = (PolyExpr.add H.main.V.coins (PolyExpr.mul H.calls ρ.V.coins)).eval n :=
      congrArg (fun p : PolyExpr => p.eval n) (H.composeV_coins ρ)
    _ = H.main.V.coins.eval n + H.calls.eval n * ρ.V.coins.eval n :=
      (PolyExpr.eval_add H.main.V.coins (.mul H.calls ρ.V.coins) n).trans
        (congrArg (fun c : ℕ => H.main.V.coins.eval n + c)
          (PolyExpr.eval_mul H.calls ρ.V.coins n))
    _ = H.main.V.coinLen n + H.calls.eval n * ρ.V.coinLen n :=
      congrArg₂ (fun a b : ℕ => a + b) (Strategy.coinLen_eq H.main.V n).symm
        (congrArg (fun c : ℕ => H.calls.eval n * c) (Strategy.coinLen_eq ρ.V n).symm)

end Construction

end HybridProtocol

end TCSlib.Cryptography.SecureComputation

## ===== TCSlib/Cryptography/SecureComputation/ComposePhases.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Compose

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Sequential composition in the hybrid model: the phases of an honest execution

The phase lemmas of `H.compose ρ` (`Compose.lean`), the protocol of the composition theorem
[Gol04, §7.3.1, Theorem 7.3.3]; they let a reader check the layout without unfolding the
strategies. In an honest execution on common input `x`, inputs `zA`, `zB` and tapes `rA`,
`rB` (write `L = calls(|x|)`, `R = ρ.rounds(|x|)`, `M = main.rounds(|x|)`):
- **(a) The runs** (`compose_exec_run`, `compose_exec_runs`). Pair `q = R · j + p < L · R`
  carries the message of `ρ`'s move `p` in the honest execution of `ρ` on the inputs of call
  `j` and the `j`-th `ρ`-tapes (`runExec`), at its mover's position, and a filler `[]` at the
  other. So the run-`j` messages each party received are the transcript of that execution.
- **(b) The main phase** (`compose_exec_main`). After the runs and the leading filler, the
  messages are those of `main`'s honest execution on `⟨zA, aA⟩`, `⟨zB, aB⟩` and the `main`-tapes
  (`mainExec`), where `aA`, `aB` are the parties' outputs of the honest runs read at `G`'s
  output lengths (`answersRealA`, `answersRealB`).
- **(c) The outputs** (`compose_outP`, `compose_outV`). When `M ≥ 1`, each party's output is
  its output in that execution of `main`. With `M = 0` this fails (`Compose.lean`, on D8's
  output convention).

## Main definitions

* `HybridProtocol.runExec`, `runMsg`: the honest run `j` and the message of its move `p`.
* `HybridProtocol.slotFromA`, `slotFromB`: each party's message at a pair.
* `HybridProtocol.answersRealA`, `answersRealB`: the answers of an honest execution.
* `HybridProtocol.mainExec`: the main phase of an honest execution.

## Main results

* `HybridProtocol.compose_exec_run`, `compose_exec_runs`: phase lemma (a).
* `HybridProtocol.compose_exec_main`, `compose_exec_rounds`: phase lemma (b), and the complete
  execution.
* `HybridProtocol.compose_outP`, `compose_outV`: phase lemma (c); `compose_transcript`,
  `compose_viewP`, `compose_viewV`: the transcript and the views.

## References

* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
  University Press, 2004, §7.3.1 (privacy reductions and a composition theorem), Theorem 7.3.3.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §4.4 (interactive protocols: executions, views, outputs; book pp. 114–116).
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing TCSlib.Cryptography

open Compose

namespace HybridProtocol

/-! ### The phases of an honest execution -/

section Phases

variable {G : Functionality} (H : HybridProtocol G) (ρ : Protocol) (x zA zB rA rB : List Bool)

/-- **The honest run `j`** after `k` moves: the execution of `ρ` on the common input `x`, the
inputs of call `j` (`runInputA`, `runInputB`) and the `j`-th `ρ`-tapes of Alice's tape `rA` and
Bob's tape `rB`. -/
def runExec (j k : ℕ) : List (List Bool) × List (List Bool) :=
  exec ρ.P ρ.V ρ.verifierFirst x (H.runInputA x zA rA j) (H.runInputB x zB rB j)
    (runTape (H.main.P.coins.eval x.length) (ρ.P.coins.eval x.length) j rA)
    (runTape (H.main.V.coins.eval x.length) (ρ.V.coins.eval x.length) j rB) k

/-- The honest run `j` is `ρ`'s execution on the call inputs and the run tapes. -/
theorem runExec_eq (j k : ℕ) :
    H.runExec ρ x zA zB rA rB j k =
      exec ρ.P ρ.V ρ.verifierFirst x (H.runInputA x zA rA j) (H.runInputB x zB rB j)
        (runTape (H.main.P.coins.eval x.length) (ρ.P.coins.eval x.length) j rA)
        (runTape (H.main.V.coins.eval x.length) (ρ.V.coins.eval x.length) j rB) k := rfl

/-- **The message of `ρ`'s move `p` in the honest run `j`**. -/
def runMsg (j p : ℕ) : List Bool :=
  moveMsg ρ.P ρ.V ρ.verifierFirst x (H.runInputA x zA rA j) (H.runInputB x zB rB j)
    (runTape (H.main.P.coins.eval x.length) (ρ.P.coins.eval x.length) j rA)
    (runTape (H.main.V.coins.eval x.length) (ρ.V.coins.eval x.length) j rB) p

/-- The message of move `p` of run `j` is `moveMsg` of the honest run `j`. -/
theorem runMsg_eq (j p : ℕ) :
    H.runMsg ρ x zA zB rA rB j p =
      moveMsg ρ.P ρ.V ρ.verifierFirst x (H.runInputA x zA rA j) (H.runInputB x zB rB j)
        (runTape (H.main.P.coins.eval x.length) (ρ.P.coins.eval x.length) j rA)
        (runTape (H.main.V.coins.eval x.length) (ρ.V.coins.eval x.length) j rB) p := rfl

/-- **Bob's message at pair `q`** of an honest execution of `H.compose ρ` (`R = ρ.rounds(|x|)`):
`ρ`'s move `q % R` of run `q / R` if Bob makes it, and the filler `[]` otherwise. -/
def slotFromB (q : ℕ) : List Bool :=
  if moverIsV ρ.verifierFirst (q % ρ.rounds.eval x.length) then
    H.runMsg ρ x zA zB rA rB (q / ρ.rounds.eval x.length) (q % ρ.rounds.eval x.length)
  else []

/-- Bob's message at pair `q` is `ρ`'s move `q % R` of run `q / R` if his, `[]` otherwise. -/
theorem slotFromB_eq (q : ℕ) :
    H.slotFromB ρ x zA zB rA rB q =
      if moverIsV ρ.verifierFirst (q % ρ.rounds.eval x.length) then
        H.runMsg ρ x zA zB rA rB (q / ρ.rounds.eval x.length) (q % ρ.rounds.eval x.length)
      else [] := rfl

/-- **Alice's message at pair `q`**: `ρ`'s move `q % R` of run `q / R` if Alice makes it, and the
filler `[]` otherwise. -/
def slotFromA (q : ℕ) : List Bool :=
  if moverIsV ρ.verifierFirst (q % ρ.rounds.eval x.length) then []
  else H.runMsg ρ x zA zB rA rB (q / ρ.rounds.eval x.length) (q % ρ.rounds.eval x.length)

/-- Alice's message at pair `q` is `ρ`'s move `q % R` of run `q / R` if hers, `[]` otherwise. -/
theorem slotFromA_eq (q : ℕ) :
    H.slotFromA ρ x zA zB rA rB q =
      if moverIsV ρ.verifierFirst (q % ρ.rounds.eval x.length) then []
      else H.runMsg ρ x zA zB rA rB (q / ρ.rounds.eval x.length) (q % ρ.rounds.eval x.length) :=
  rfl

/-- **Alice's answers in an honest execution**: her outputs of the honest runs (`ρ.P.next` on
her complete run history), each padded or truncated to `G.outA(|x|)` bits, concatenated. -/
def answersRealA : List Bool :=
  (List.ofFn fun j : Fin (H.calls.eval x.length) =>
    List.ofFn (padFin (G.outA.eval x.length)
      (ρ.P.next x (H.runInputA x zA rA j)
        (runTape (H.main.P.coins.eval x.length) (ρ.P.coins.eval x.length) j rA)
        (H.runExec ρ x zA zB rA rB j (ρ.rounds.eval x.length)).1))).flatten

/-- Alice's answers in an honest execution are her padded outputs of the honest runs. -/
theorem answersRealA_eq :
    H.answersRealA ρ x zA zB rA rB =
      (List.ofFn fun j : Fin (H.calls.eval x.length) =>
        List.ofFn (padFin (G.outA.eval x.length)
          (ρ.P.next x (H.runInputA x zA rA j)
            (runTape (H.main.P.coins.eval x.length) (ρ.P.coins.eval x.length) j rA)
            (H.runExec ρ x zA zB rA rB j (ρ.rounds.eval x.length)).1))).flatten := rfl

/-- **Bob's answers in an honest execution**: his outputs of the honest runs, each padded or
truncated to `G.outB(|x|)` bits, concatenated. -/
def answersRealB : List Bool :=
  (List.ofFn fun j : Fin (H.calls.eval x.length) =>
    List.ofFn (padFin (G.outB.eval x.length)
      (ρ.V.next x (H.runInputB x zB rB j)
        (runTape (H.main.V.coins.eval x.length) (ρ.V.coins.eval x.length) j rB)
        (H.runExec ρ x zA zB rA rB j (ρ.rounds.eval x.length)).2))).flatten

/-- Bob's answers in an honest execution are his padded outputs of the honest runs. -/
theorem answersRealB_eq :
    H.answersRealB ρ x zA zB rA rB =
      (List.ofFn fun j : Fin (H.calls.eval x.length) =>
        List.ofFn (padFin (G.outB.eval x.length)
          (ρ.V.next x (H.runInputB x zB rB j)
            (runTape (H.main.V.coins.eval x.length) (ρ.V.coins.eval x.length) j rB)
            (H.runExec ρ x zA zB rA rB j (ρ.rounds.eval x.length)).2))).flatten := rfl

/-- **The main phase of an honest execution** after `m` moves: the execution of `main` on the
private inputs `⟨zA, Alice's answers⟩` and `⟨zB, Bob's answers⟩` and the `main`-tapes (the first
`main.P.coins(|x|)` bits of `rA`, the first `main.V.coins(|x|)` bits of `rB`). -/
def mainExec (m : ℕ) : List (List Bool) × List (List Bool) :=
  exec H.main.P H.main.V H.main.verifierFirst x (pairEncode zA (H.answersRealA ρ x zA zB rA rB))
    (pairEncode zB (H.answersRealB ρ x zA zB rA rB)) (rA.take (H.main.P.coins.eval x.length))
    (rB.take (H.main.V.coins.eval x.length)) m

/-- The main phase is `main`'s execution on the inputs paired with the honest answers. -/
theorem mainExec_eq (m : ℕ) :
    H.mainExec ρ x zA zB rA rB m =
      exec H.main.P H.main.V H.main.verifierFirst x
        (pairEncode zA (H.answersRealA ρ x zA zB rA rB))
        (pairEncode zB (H.answersRealB ρ x zA zB rA rB)) (rA.take (H.main.P.coins.eval x.length))
        (rB.take (H.main.V.coins.eval x.length)) m := rfl

/-! #### The run phase -/

/-- Division by `R` of `R·j + p` with `p < R`. -/
private theorem mul_add_div_of_lt {R j p : ℕ} (hp : p < R) : (R * j + p) / R = j := by
  rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hp, Nat.add_zero]

/-- Remainder modulo `R` of `R·j + p` with `p < R`. -/
private theorem mul_add_mod_of_lt {R j p : ℕ} (hp : p < R) : (R * j + p) % R = p := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hp]

/-- The pairs of run `j < L` come before pair `L·R`. -/
private theorem mul_add_le_of_lt {R j L : ℕ} (hj : j < L) : R * j + R ≤ L * R := by
  have := Nat.mul_le_mul_right R (Nat.succ_le_of_lt hj)
  rw [Nat.succ_mul, Nat.mul_comm j R] at this
  exact this

/-- Bob's message at pair `R·j + p`, `p < R`, is `ρ`'s move `p` of run `j` if his. -/
theorem slotFromB_mul_add {j p : ℕ} (hp : p < ρ.rounds.eval x.length) :
    H.slotFromB ρ x zA zB rA rB (ρ.rounds.eval x.length * j + p) =
      if moverIsV ρ.verifierFirst p then H.runMsg ρ x zA zB rA rB j p else [] := by
  rw [slotFromB_eq, mul_add_div_of_lt hp, mul_add_mod_of_lt hp]

/-- Alice's message at pair `R·j + p`, `p < R`, is `ρ`'s move `p` of run `j` if hers. -/
theorem slotFromA_mul_add {j p : ℕ} (hp : p < ρ.rounds.eval x.length) :
    H.slotFromA ρ x zA zB rA rB (ρ.rounds.eval x.length * j + p) =
      if moverIsV ρ.verifierFirst p then [] else H.runMsg ρ x zA zB rA rB j p := by
  rw [slotFromA_eq, mul_add_div_of_lt hp, mul_add_mod_of_lt hp]

/-- **Alice reads run `j` from the pairs**: if `hist` holds Bob's honest messages at the pairs
before `R·j + p` (`p ≤ R`), her run-`j` history is the one of the honest run `j` after `p`
moves. -/
theorem slotMsgs_runFst {j p : ℕ} (hp : p ≤ ρ.rounds.eval x.length) {hist : List (List Bool)}
    (hh : ∀ i < ρ.rounds.eval x.length * j + p, hist.getD i [] = H.slotFromB ρ x zA zB rA rB i) :
    slotMsgs (moverIsV ρ.verifierFirst) (ρ.rounds.eval x.length * j) p hist =
      (H.runExec ρ x zA zB rA rB j p).1 := by
  rw [slotMsgs_eq_map (f := H.runMsg ρ x zA zB rA rB j), runExec_eq, exec_eq_map]
  · rfl
  · intro p' hp' hsel
    rw [hh _ (by omega), slotFromB_mul_add H ρ x zA zB rA rB (by omega), if_pos hsel]

/-- **Bob reads run `j` from the pairs**: if `hist` holds Alice's honest messages at the pairs
before `R·j + p` (`p ≤ R`), his run-`j` history is the one of the honest run `j` after `p`
moves. -/
theorem slotMsgs_runSnd {j p : ℕ} (hp : p ≤ ρ.rounds.eval x.length) {hist : List (List Bool)}
    (hh : ∀ i < ρ.rounds.eval x.length * j + p, hist.getD i [] = H.slotFromA ρ x zA zB rA rB i) :
    slotMsgs (fun p' => !moverIsV ρ.verifierFirst p') (ρ.rounds.eval x.length * j) p hist =
      (H.runExec ρ x zA zB rA rB j p).2 := by
  rw [slotMsgs_eq_map (f := H.runMsg ρ x zA zB rA rB j), runExec_eq, exec_eq_map]
  · rfl
  · intro p' hp' hsel
    rw [Bool.not_eq_true'] at hsel
    rw [hh _ (by omega), slotFromA_mul_add H ρ x zA zB rA rB (by omega), hsel]
    rfl

/-- **Phase lemma, the run phase**: after the first `q ≤ L·R` pairs of an honest execution of
`H.compose ρ` (`L = calls(|x|)`, `R = ρ.rounds(|x|)`), Alice has received Bob's messages
`slotFromB 0, …, slotFromB (q − 1)` and Bob Alice's `slotFromA 0, …, slotFromA (q − 1)`: at
each pair, `ρ`'s move of the honest run on the call inputs, or a filler.

**Proof sketch.** Induction on `q`. At pair `q < L·R` (run `j = q / R`, position `p = q % R`):
1. Alice moves at `2q` (`moverIsV_false_two_mul`), having received `q` messages, so she computes
   `j` and `p`. If `ρ`'s mover `p` is Bob she sends `[]`. Otherwise her run-`j` history read from
   the pairs is the honest run's after `p` moves (`slotMsgs_runFst`, by the induction
   hypothesis), so she sends `ρ`'s move `p` (`moveMsg`).
2. Bob moves at `2q + 1` having received `q + 1` messages, so he computes the same `j`, `p`, and
   symmetrically sends `ρ`'s move `p` or `[]` (`slotMsgs_runSnd`). -/
theorem compose_exec_run {q : ℕ} (hq : q ≤ H.calls.eval x.length * ρ.rounds.eval x.length) :
    exec (H.compose ρ).P (H.compose ρ).V (H.compose ρ).verifierFirst x zA zB rA rB (2 * q) =
      ((List.range q).map (H.slotFromB ρ x zA zB rA rB),
        (List.range q).map (H.slotFromA ρ x zA zB rA rB)) := by
  induction q with
  | zero => simp only [Nat.mul_zero, exec_zero, List.range_zero, List.map_nil]
  | succ q ih =>
    have hq' : q < H.calls.eval x.length * ρ.rounds.eval x.length := by omega
    have hR : 0 < ρ.rounds.eval x.length := by
      rcases Nat.eq_zero_or_pos (ρ.rounds.eval x.length) with h | h
      · rw [h, Nat.mul_zero] at hq'
        omega
      · exact h
    have hpR : q % ρ.rounds.eval x.length < ρ.rounds.eval x.length := Nat.mod_lt _ hR
    have hqd : ρ.rounds.eval x.length * (q / ρ.rounds.eval x.length) +
        q % ρ.rounds.eval x.length = q := Nat.div_add_mod q _
    -- Alice's move at `2q`
    have hA : (H.compose ρ).P.next x zA rA ((List.range q).map (H.slotFromB ρ x zA zB rA rB)) =
        H.slotFromA ρ x zA zB rA rB q := by
      rw [compose_P, composeP_next, List.length_map, List.length_range, if_pos hq',
        slotFromA_eq]
      by_cases hm : moverIsV ρ.verifierFirst (q % ρ.rounds.eval x.length) = true
      · rw [if_pos hm, if_pos hm]
      · rw [if_neg hm, if_neg hm, runNextA_eq, runMsg_eq, moveMsg_eq, if_neg hm,
          slotMsgs_runFst H ρ x zA zB rA rB hpR.le, runExec_eq]
        intro i hi
        rw [getD_map_range (by omega)]
    -- Bob's move at `2q + 1`
    have hB : (H.compose ρ).V.next x zB rB
        ((List.range q).map (H.slotFromA ρ x zA zB rA rB) ++ [H.slotFromA ρ x zA zB rA rB q]) =
        H.slotFromB ρ x zA zB rA rB q := by
      have hlen : ((List.range q).map (H.slotFromA ρ x zA zB rA rB) ++
          [H.slotFromA ρ x zA zB rA rB q]).length - 1 = q := by
        rw [List.length_append, List.length_map, List.length_range, List.length_singleton,
          Nat.add_sub_cancel]
      rw [compose_V, composeV_next, hlen, if_pos hq', slotFromB_eq]
      by_cases hm : moverIsV ρ.verifierFirst (q % ρ.rounds.eval x.length) = true
      · rw [if_pos hm, if_pos hm, runNextB_eq, runMsg_eq, moveMsg_eq, if_pos hm,
          slotMsgs_runSnd H ρ x zA zB rA rB hpR.le, runExec_eq]
        intro i hi
        rw [getD_append_left (by rw [List.length_map, List.length_range]; omega),
          getD_map_range (by omega)]
      · rw [if_neg hm, if_neg hm]
    rw [show 2 * (q + 1) = 2 * q + 1 + 1 by ring, exec_succ, exec_succ, ih hq'.le]
    simp only [compose_verifierFirst, moverIsV_false_two_mul, moverIsV_false_two_mul_add_one,
      if_true, Bool.false_eq_true, if_false]
    rw [hA, hB, List.range_succ, List.map_append, List.map_append, List.map_singleton,
      List.map_singleton]

/-- **Phase lemma (a), the runs**: after the run phase of an honest execution of `H.compose ρ`
(`L·2R` moves), for every run `j < L`, the run-`j` messages Alice received (read at the pairs
where `ρ`'s mover is Bob) and those Bob received (at the pairs where `ρ`'s mover is Alice) are
the transcript of the honest execution of `ρ` on the inputs of call `j` and the `j`-th tapes
(`runExec`, `runInputA_of_lt`).

**Proof sketch.** By `compose_exec_run` with `q = L·R`, the received lists hold the honest pair
messages; the pairs of run `j` come before `L·R`, so `slotMsgs_runFst` and `slotMsgs_runSnd`
read the honest run `j` from them. -/
theorem compose_exec_runs {j : ℕ} (hj : j < H.calls.eval x.length) :
    slotMsgs (moverIsV ρ.verifierFirst) (ρ.rounds.eval x.length * j) (ρ.rounds.eval x.length)
        (exec (H.compose ρ).P (H.compose ρ).V (H.compose ρ).verifierFirst x zA zB rA rB
          (H.calls.eval x.length * (2 * ρ.rounds.eval x.length))).1 =
      (H.runExec ρ x zA zB rA rB j (ρ.rounds.eval x.length)).1 ∧
    slotMsgs (fun p => !moverIsV ρ.verifierFirst p) (ρ.rounds.eval x.length * j)
        (ρ.rounds.eval x.length)
        (exec (H.compose ρ).P (H.compose ρ).V (H.compose ρ).verifierFirst x zA zB rA rB
          (H.calls.eval x.length * (2 * ρ.rounds.eval x.length))).2 =
      (H.runExec ρ x zA zB rA rB j (ρ.rounds.eval x.length)).2 := by
  have hjR := mul_add_le_of_lt (R := ρ.rounds.eval x.length) hj
  rw [show H.calls.eval x.length * (2 * ρ.rounds.eval x.length) =
    2 * (H.calls.eval x.length * ρ.rounds.eval x.length) by ring,
    compose_exec_run H ρ x zA zB rA rB le_rfl]
  refine ⟨slotMsgs_runFst H ρ x zA zB rA rB le_rfl fun i hi => ?_,
    slotMsgs_runSnd H ρ x zA zB rA rB le_rfl fun i hi => ?_⟩
  · exact getD_map_range (by omega)
  · exact getD_map_range (by omega)

/-! #### The main phase -/

/-- Alice's answers read from a history that starts with Bob's honest run messages are her
honest answers. -/
theorem answersFromA_run (Y : List (List Bool)) :
    H.answersFromA ρ x zA rA ((List.range (H.calls.eval x.length * ρ.rounds.eval x.length)).map
      (H.slotFromB ρ x zA zB rA rB) ++ Y) = H.answersRealA ρ x zA zB rA rB := by
  rw [answersFromA_eq, answersRealA_eq]
  refine congrArg List.flatten (congrArg List.ofFn (funext fun j => ?_))
  have hjR := mul_add_le_of_lt (R := ρ.rounds.eval x.length) j.2
  rw [runNextA_eq, slotMsgs_runFst H ρ x zA zB rA rB le_rfl]
  intro i hi
  rw [getD_append_left (by rw [List.length_map, List.length_range]; omega),
    getD_map_range (by omega)]

/-- Bob's answers read from a history that starts with Alice's honest run messages are his
honest answers. -/
theorem answersFromB_run (Y : List (List Bool)) :
    H.answersFromB ρ x zB rB ((List.range (H.calls.eval x.length * ρ.rounds.eval x.length)).map
      (H.slotFromA ρ x zA zB rA rB) ++ Y) = H.answersRealB ρ x zA zB rA rB := by
  rw [answersFromB_eq, answersRealB_eq]
  refine congrArg List.flatten (congrArg List.ofFn (funext fun j => ?_))
  have hjR := mul_add_le_of_lt (R := ρ.rounds.eval x.length) j.2
  rw [runNextB_eq, slotMsgs_runSnd H ρ x zA zB rA rB le_rfl]
  intro i hi
  rw [getD_append_left (by rw [List.length_map, List.length_range]; omega),
    getD_map_range (by omega)]

/-- **Alice's move in the main phase** after `m` moves of `main` (`m ≥ 1` if `main`'s verifier
moves first): her `main`-move on `⟨zA, her honest answers⟩`, her `main`-tape and `main`'s
messages.

**Proof sketch.** She has received `L·R + k` messages, `k` of them in `main`: she is past the
runs, and not at the leading filler, since `k ≥ 1` when `main`'s verifier moves first
(`exec_fst_length_pos`). Her answers are read from the run messages (`answersFromA_run`), and the
messages after the first `L·R` are `main`'s. -/
theorem compose_P_next_main {m : ℕ} (hm : H.main.verifierFirst = true → 0 < m) :
    (H.compose ρ).P.next x zA rA
        ((List.range (H.calls.eval x.length * ρ.rounds.eval x.length)).map
          (H.slotFromB ρ x zA zB rA rB) ++ (H.mainExec ρ x zA zB rA rB m).1) =
      H.main.P.next x (pairEncode zA (H.answersRealA ρ x zA zB rA rB))
        (rA.take (H.main.P.coins.eval x.length)) (H.mainExec ρ x zA zB rA rB m).1 := by
  have hlen : ((List.range (H.calls.eval x.length * ρ.rounds.eval x.length)).map
      (H.slotFromB ρ x zA zB rA rB) ++ (H.mainExec ρ x zA zB rA rB m).1).length =
      H.calls.eval x.length * ρ.rounds.eval x.length +
        (H.mainExec ρ x zA zB rA rB m).1.length := by
    rw [List.length_append, List.length_map, List.length_range]
  have hlead : ¬(H.main.verifierFirst = true ∧
      H.calls.eval x.length * ρ.rounds.eval x.length + (H.mainExec ρ x zA zB rA rB m).1.length =
        H.calls.eval x.length * ρ.rounds.eval x.length) := by
    rintro ⟨hv, hl⟩
    have := exec_fst_length_pos H.main.P H.main.V x (pairEncode zA (H.answersRealA ρ x zA zB rA rB))
      (pairEncode zB (H.answersRealB ρ x zA zB rA rB)) (rA.take (H.main.P.coins.eval x.length))
      (rB.take (H.main.V.coins.eval x.length)) hv (hm hv)
    rw [← mainExec_eq] at this
    omega
  rw [compose_P, composeP_next, hlen, if_neg (by omega), if_neg hlead, answersFromA_run,
    List.drop_left' (by rw [List.length_map, List.length_range])]

/-- **Bob's move in the main phase** after `m` moves of `main` (`m ≥ 1` if `main`'s prover moves
first): his `main`-move on `⟨zB, his honest answers⟩`, his `main`-tape and `main`'s messages.

**Proof sketch.** He has received `L·R + lead + k` messages, `k` of them in `main`, and
`lead + k ≥ 1`: either the leading filler was sent, or `main`'s prover moved first
(`exec_snd_length_pos`). So he is past the runs. His answers are read from the run messages
(`answersFromB_run`), and the messages after the first `L·R + lead` are `main`'s. -/
theorem compose_V_next_main {m : ℕ} (hm : H.main.verifierFirst = false → 0 < m) :
    (H.compose ρ).V.next x zB rB
        ((List.range (H.calls.eval x.length * ρ.rounds.eval x.length)).map
          (H.slotFromA ρ x zA zB rA rB) ++ List.replicate H.lead [] ++
          (H.mainExec ρ x zA zB rA rB m).2) =
      H.main.V.next x (pairEncode zB (H.answersRealB ρ x zA zB rA rB))
        (rB.take (H.main.V.coins.eval x.length)) (H.mainExec ρ x zA zB rA rB m).2 := by
  have hlen : ((List.range (H.calls.eval x.length * ρ.rounds.eval x.length)).map
      (H.slotFromA ρ x zA zB rA rB) ++ List.replicate H.lead [] ++
        (H.mainExec ρ x zA zB rA rB m).2).length =
      H.calls.eval x.length * ρ.rounds.eval x.length + H.lead +
        (H.mainExec ρ x zA zB rA rB m).2.length := by
    rw [List.length_append, List.length_append, List.length_map, List.length_range,
      List.length_replicate]
  have hpos : 0 < H.lead + (H.mainExec ρ x zA zB rA rB m).2.length := by
    cases hv : H.main.verifierFirst
    · have := exec_snd_length_pos H.main.P H.main.V x
        (pairEncode zA (H.answersRealA ρ x zA zB rA rB))
        (pairEncode zB (H.answersRealB ρ x zA zB rA rB)) (rA.take (H.main.P.coins.eval x.length))
        (rB.take (H.main.V.coins.eval x.length)) hv (hm hv)
      rw [← mainExec_eq] at this
      omega
    · rw [H.lead_of_true hv]
      omega
  rw [compose_V, composeV_next, hlen, if_neg (by omega), List.drop_left'
      (by rw [List.length_append, List.length_map, List.length_range, List.length_replicate]),
    List.append_assoc, answersFromB_run]

/-- **Phase lemma (b), the main phase**: after the run phase, the leading filler and `m` further
moves of an honest execution of `H.compose ρ`, Alice has received Bob's run messages followed by
the messages she receives in `main`, and Bob has received Alice's run messages, the leading
filler (`lead` empty messages) and the messages he receives in `main`, where `main` is executed
on `⟨zA, Alice's honest answers⟩`, `⟨zB, Bob's honest answers⟩` and the `main`-tapes
(`mainExec`).

**Proof sketch.** Induction on `m`.
1. `m = 0`: the run phase (`compose_exec_run` with `q = L·R`), then, if `main`'s verifier moves
   first, Alice's leading filler: she has received `L·R` messages, which she reads as the lead.
2. At `m + 1`: position `L·2R + lead + m` has `main`'s mover at `m` (the parity of `lead + m`).
   The mover has received the messages of the runs (and the lead), then `main`'s. It is past the
   runs, and Alice not at the lead, since `main`'s first mover has already moved
   (`exec_fst_length_pos`, `exec_snd_length_pos`). So it plays its `main`-move on its honest
   answers (`answersFromA_run`, `answersFromB_run`) and `main`'s messages
   (`compose_P_next_main`, `compose_V_next_main`). -/
theorem compose_exec_main (m : ℕ) :
    exec (H.compose ρ).P (H.compose ρ).V (H.compose ρ).verifierFirst x zA zB rA rB
        (H.calls.eval x.length * (2 * ρ.rounds.eval x.length) + H.lead + m) =
      ((List.range (H.calls.eval x.length * ρ.rounds.eval x.length)).map
          (H.slotFromB ρ x zA zB rA rB) ++ (H.mainExec ρ x zA zB rA rB m).1,
        (List.range (H.calls.eval x.length * ρ.rounds.eval x.length)).map
          (H.slotFromA ρ x zA zB rA rB) ++ List.replicate H.lead [] ++
          (H.mainExec ρ x zA zB rA rB m).2) := by
  set L := H.calls.eval x.length with hL
  set R := ρ.rounds.eval x.length with hR
  induction m with
  | zero =>
    rw [Nat.add_zero, mainExec_eq, exec_zero]
    simp only [List.append_nil]
    cases hv : H.main.verifierFirst
    · rw [H.lead_of_false hv, Nat.add_zero, List.replicate_zero, List.append_nil,
        show L * (2 * R) = 2 * (L * R) by ring, compose_exec_run H ρ x zA zB rA rB le_rfl]
    · rw [H.lead_of_true hv, show L * (2 * R) + 1 = 2 * (L * R) + 1 by ring, exec_succ,
        compose_exec_run H ρ x zA zB rA rB le_rfl]
      simp only [compose_verifierFirst, moverIsV_false_two_mul, Bool.false_eq_true, if_false]
      have hlead : (H.compose ρ).P.next x zA rA ((List.range (L * R)).map
          (H.slotFromB ρ x zA zB rA rB)) = [] := by
        rw [compose_P, composeP_next, List.length_map, List.length_range, if_neg (lt_irrefl _),
          if_pos ⟨hv, rfl⟩]
      rw [hlead, List.replicate_one]
  | succ m ih =>
    have hmv : moverIsV (H.compose ρ).verifierFirst (L * (2 * R) + H.lead + m) =
        moverIsV H.main.verifierFirst m := by
      rw [compose_verifierFirst, show L * (2 * R) = 2 * (L * R) by ring]
      cases hv : H.main.verifierFirst
      · rw [H.lead_of_false hv, moverIsV_false, moverIsV_false]
        congr 1
        apply propext
        omega
      · rw [H.lead_of_true hv, moverIsV_false, moverIsV_true]
        congr 1
        apply propext
        omega
    rw [← Nat.add_assoc, exec_succ, ih, mainExec_eq H ρ x zA zB rA rB (m + 1), exec_succ,
      ← mainExec_eq]
    simp only [hmv]
    cases hm : moverIsV H.main.verifierFirst m
    · simp only [Bool.false_eq_true, if_false]
      have hm' : H.main.verifierFirst = true → 0 < m := by
        intro hv
        rw [hv, moverIsV_true, decide_eq_false_iff_not] at hm
        omega
      rw [compose_P_next_main H ρ x zA zB rA rB hm', List.append_assoc]
    · simp only [if_true]
      have hm' : H.main.verifierFirst = false → 0 < m := by
        intro hv
        rw [hv, moverIsV_false, decide_eq_true_eq] at hm
        omega
      rw [compose_V_next_main H ρ x zA zB rA rB hm', List.append_assoc]

/-- **Phase lemma, the complete transcript**: the transcript of an honest execution of
`H.compose ρ` (all `L·2R + lead + M` moves) is, for Alice, Bob's run messages followed by
`main`'s messages to her, and for Bob, Alice's run messages, the leading filler and `main`'s
messages to him (`compose_exec_main` with `m = M`). -/
theorem compose_exec_rounds :
    exec (H.compose ρ).P (H.compose ρ).V (H.compose ρ).verifierFirst x zA zB rA rB
        ((H.compose ρ).rounds.eval x.length) =
      ((List.range (H.calls.eval x.length * ρ.rounds.eval x.length)).map
          (H.slotFromB ρ x zA zB rA rB) ++
          (H.mainExec ρ x zA zB rA rB (H.main.rounds.eval x.length)).1,
        (List.range (H.calls.eval x.length * ρ.rounds.eval x.length)).map
          (H.slotFromA ρ x zA zB rA rB) ++ List.replicate H.lead [] ++
          (H.mainExec ρ x zA zB rA rB (H.main.rounds.eval x.length)).2) := by
  rw [compose_rounds_eval, compose_exec_main]

end Phases

/-! ### The phases in terms of `Protocol` -/

section Outputs

variable {G : Functionality} (H : HybridProtocol G) (ρ : Protocol) (x zA zB : List Bool)
  (r : (H.compose ρ).ExecCoins (H.compose ρ).P x)

/-- **The transcript of `H.compose ρ`** on coins `r = (rA, rB)`: Bob's run messages and `main`'s
messages to Alice; Alice's run messages, the leading filler and `main`'s messages to Bob
(`compose_exec_rounds` on the tapes `List.ofFn rA`, `List.ofFn rB`). -/
theorem compose_transcript :
    (H.compose ρ).transcript x zA zB r =
      ((List.range (H.calls.eval x.length * ρ.rounds.eval x.length)).map
          (H.slotFromB ρ x zA zB (List.ofFn r.1) (List.ofFn r.2)) ++
          (H.mainExec ρ x zA zB (List.ofFn r.1) (List.ofFn r.2)
            (H.main.rounds.eval x.length)).1,
        (List.range (H.calls.eval x.length * ρ.rounds.eval x.length)).map
          (H.slotFromA ρ x zA zB (List.ofFn r.1) (List.ofFn r.2)) ++ List.replicate H.lead [] ++
          (H.mainExec ρ x zA zB (List.ofFn r.1) (List.ofFn r.2)
            (H.main.rounds.eval x.length)).2) :=
  ((Protocol.transcript_eq_transcriptWith (H.compose ρ) x zA zB r).trans
    (Protocol.transcriptWith_eq (H.compose ρ) (H.compose ρ).P x zA zB r)).trans
    (H.compose_exec_rounds ρ x zA zB (List.ofFn r.1) (List.ofFn r.2))

/-- **Alice's view in `H.compose ρ`**: the common input, her input, her whole tape, and Bob's run
messages followed by `main`'s messages to her. -/
theorem compose_viewP :
    (H.compose ρ).viewP x zA zB r =
      ⟨x, zA, List.ofFn r.1,
        (List.range (H.calls.eval x.length * ρ.rounds.eval x.length)).map
          (H.slotFromB ρ x zA zB (List.ofFn r.1) (List.ofFn r.2)) ++
          (H.mainExec ρ x zA zB (List.ofFn r.1) (List.ofFn r.2)
            (H.main.rounds.eval x.length)).1⟩ :=
  (Protocol.viewP_eq (H.compose ρ) x zA zB r).trans
    (congrArg (fun t : List (List Bool) × List (List Bool) =>
      (⟨x, zA, List.ofFn r.1, t.1⟩ : View))
      ((Protocol.transcript_eq_transcriptWith (H.compose ρ) x zA zB r).symm.trans
        (H.compose_transcript ρ x zA zB r)))

/-- **Bob's view in `H.compose ρ`**: the common input, his input, his whole tape, and Alice's run
messages, the leading filler and `main`'s messages to him. -/
theorem compose_viewV :
    (H.compose ρ).viewV x zA zB r =
      ⟨x, zB, List.ofFn r.2,
        (List.range (H.calls.eval x.length * ρ.rounds.eval x.length)).map
          (H.slotFromA ρ x zA zB (List.ofFn r.1) (List.ofFn r.2)) ++ List.replicate H.lead [] ++
          (H.mainExec ρ x zA zB (List.ofFn r.1) (List.ofFn r.2)
            (H.main.rounds.eval x.length)).2⟩ :=
  (Protocol.viewV_eq (H.compose ρ) x zA zB r).trans
    (congrArg (fun t : List (List Bool) × List (List Bool) =>
      (⟨x, zB, List.ofFn r.2, t.2⟩ : View))
      ((Protocol.transcript_eq_transcriptWith (H.compose ρ) x zA zB r).symm.trans
        (H.compose_transcript ρ x zA zB r)))

/-- **Phase lemma (c), Alice's output** in terms of `Protocol.outP`: when `main` has at least one
move, Alice's output in `H.compose ρ` is her `main`-output on `⟨zA, her honest answers⟩`, her
`main`-tape and her complete `main`-history.

**Proof sketch.** Her complete history is Bob's run messages followed by `main`'s messages to
her (`compose_exec_rounds`). If `main`'s verifier moves first, it has moved, as `M ≥ 1`, so she
is not at the leading filler, and `compose_P_next_main` applies. -/
theorem compose_outP (hM : 0 < H.main.rounds.eval x.length) :
    (H.compose ρ).outP x zA zB r =
      H.main.P.next x (pairEncode zA (H.answersRealA ρ x zA zB (List.ofFn r.1) (List.ofFn r.2)))
        ((List.ofFn r.1).take (H.main.P.coins.eval x.length))
        (H.mainExec ρ x zA zB (List.ofFn r.1) (List.ofFn r.2)
          (H.main.rounds.eval x.length)).1 :=
  (Protocol.outP_eq (H.compose ρ) x zA zB r).trans
    ((congrArg (fun t : List (List Bool) × List (List Bool) =>
      (H.compose ρ).P.next x zA (List.ofFn r.1) t.1)
      ((Protocol.transcript_eq_transcriptWith (H.compose ρ) x zA zB r).symm.trans
        (H.compose_transcript ρ x zA zB r))).trans
      (compose_P_next_main H ρ x zA zB (List.ofFn r.1) (List.ofFn r.2)
        (m := H.main.rounds.eval x.length) (fun _ => hM)))

/-- **Phase lemma (c), Bob's output** in terms of `Protocol.outV`: when `main` has at least one
move, Bob's output in `H.compose ρ` is his `main`-output on `⟨zB, his honest answers⟩`, his
`main`-tape and his complete `main`-history.

**Proof sketch.** His complete history is Alice's run messages, the leading filler and `main`'s
messages to him (`compose_exec_rounds`). He is past the runs, because the leading filler or
`main`'s first move (by Alice, as `M ≥ 1`) follows them, and `compose_V_next_main` applies. -/
theorem compose_outV (hM : 0 < H.main.rounds.eval x.length) :
    (H.compose ρ).outV (H.compose ρ).P x zA zB r =
      H.main.V.next x (pairEncode zB (H.answersRealB ρ x zA zB (List.ofFn r.1) (List.ofFn r.2)))
        ((List.ofFn r.2).take (H.main.V.coins.eval x.length))
        (H.mainExec ρ x zA zB (List.ofFn r.1) (List.ofFn r.2)
          (H.main.rounds.eval x.length)).2 :=
  (Protocol.outV_eq (H.compose ρ) (H.compose ρ).P x zA zB r).trans
    ((congrArg (fun t : List (List Bool) × List (List Bool) =>
      (H.compose ρ).V.next x zB (List.ofFn r.2) t.2)
      ((Protocol.transcript_eq_transcriptWith (H.compose ρ) x zA zB r).symm.trans
        (H.compose_transcript ρ x zA zB r))).trans
      (compose_V_next_main H ρ x zA zB (List.ofFn r.1) (List.ofFn r.2)
        (m := H.main.rounds.eval x.length) (fun _ => hM)))

end Outputs

end HybridProtocol

end TCSlib.Cryptography.SecureComputation
