## ===== briefs/pass-shelat-ch5-8/gates/21-dl-folds/pack.md =====

# Gate 21 · Post-consolidation folds DL-36 and DL-37

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews).

- **PR:** draft [PR #299](https://github.com/Shilun-Allan-Li/tcslib/pull/299) at
  `fcdb65794698395f8eaa377df0789f7552681633` (branch `land/pass-shelat-dl-folds`, tree
  `bc738121c68729f6b1172cc10cf7b559705a52f5`).
- **Target and base:** the PR targets `cryptography/pass-shelat-ch2-4` on base
  `934eac64c410ef69a2f52eb92b91e501c655ed2b`.
  - The fill was issued on `d3f2290a2c66f614e8807903b89ac595086578b3`, the merge of #298.
  - Every commit between the two touches records only.
- **Commits:** the worker's 3 checkpoint commits (Claude job `dl-folds`), rebased with authors kept. There are no
  landing edits.
- **Scope:** a **refactor audit**, meant to change no audited statement and no mathematical content. The job:
  - repays duplication-ledger rows DL-36 (left by the nm-cca2 fill) and DL-37 (left by the nm-sim fill);
  - promotes the generic lemmas that those fills' reviews accepted;
  - deletes the copies and re-points every use.
- **Brief:** `fills/dl-folds/issued-r1/brief.md` on the records branch, with item groups G, R, B, L and E.
- **Seyoon's rulings of 2026-11-13:**
  - one job;
  - R7 closed as no-fold;
  - the `blocks` aliases are in scope, but fold only if no audited statement changes.

## What changed

All paths are under `TCSlib/Cryptography/`. The PR touches 36 Lean files: 35 modified and 1 new
(`Games/Forwarding.lean`).
- `NMI/` = `Encryption/PublicKey/NonMalleability/Indistinguishability/`.
- `NMS/` = `…/NonMalleability/Simulation/`.

The worker's REPORT §0 lists every item with its disposition. In summary:

**Games layer (G1–G7)**
- `buildComp_budget_eq`, `buildComp_of_ret` → `Games`; `toCompOn_budget_eq` → `Complexity.NUPPT`.
- `InteractiveHandler.impl_of_query` and `finish_of_ret` are new, with `padFin` forms of the old nm-sim lemmas. The
  private PRF `impl_of_query` is folded into them.
- `expect_toCompOn_outLen`, the possible-output and cost lemmas, and `simulate_costBoundedBy_once` are promoted.
- `Games.expect_simulate_eager` (G5): `ChallengeSim.expect_simulate_eager` is now derived from it, with its
  statement unchanged.
- `Games.expect_eq_until_bad` (G6): `prob_eq_until_bad` is derived from it, with its statement unchanged.
- A new module, `Games/Forwarding.lean`, holds `Games.fwdHandler`/`fwdHandler_impl`.
- `NUPPT.exists_withAdviceOn` is promoted.
- `Games.cntRead`/`ansRead` move into `Games/BitCodec`.

**Readers (R1–R3)**
- The NM finalization readers `finU`/`finZ`/`finW`/`finL` and nm-sim's `finSt` fold onto `InteractiveHandler.rU`,
  `rZ`, `rW`, `rL` and `rS`. New readers on a finalization input: `rU_finInput`, `rZ_finInput`, `rW_finInput`,
  `rS_finInput` and `rL_finInput`, plus `finA` with `finA_finInput`.
- The round-input readers `rdU`…`rdLog` and Forward's private `rState`…`rLog` fold onto the same readers.
- The answer reader becomes one `InteractiveHandler.rAns`. It replaces `rdAns`, Forward's `rAns`, AdaptiveCPA's `rFwd`
  and PRFGame's `rY`.

**Blocks (B1–B3)**
- `chunkAt` → `coinBlock`.
- The block lemmas move beside `coinBlock`, folding Lamport's `coinBlock_flatten`.
- The block-window restatements are derived from `FunFamily.ofFn_blocks`. That covers `OneWay`, `NMCCA2.ofFn_nthCt`,
  `EnsembleLemmas` and `FromPRF`, and GGM `Evaluator`'s `drop_take_ofFn_blocks`, which the worker's grep found.
- **B3 is escalated:** both `blocks` aliases are kept (REPORT §9.4).

**Lists (L1–L4)**
- `Foundations/BitLists` gains `flatMap_range_drop`, `ofFn_natAdd_eq_drop`, `decide_map_ofFn`,
  `length_flatten_map_const`/`_range` and `ofFn_eq_map_range`. The latter's two ZK copies are deleted.
- `Games.padFin_append_split` is promoted.
- `EnsembleLemmas.seedEquiv`/`seedEquivPoly` are promoted.
- nm-sim's `ofFn_padFin_eq_padL` is deleted in favour of the A4 lemma.

**Iterate and emit, and leftovers (E1–E3)**
- The new `Games.iterEmit` comes with `polyTimeComputable_iterEmit`.
- `logEmit` and `chunkMap` are now instances of it, with their types unchanged.
- `relabelN` and `relabel` keep their definitions and are bridged by `relabelN_eq_iterEmit` and
  `relabel_eq_iterEmit`.
- `polyTimeComputable_guessBit` → `NMI/Encrypt`; `ctLen_pos` and `indImpl_eq_of_msgLen_eq_zero` →
  `PublicKey/OracleSecurity`.

**Name map:** `evidence/census/namemap.tsv` in the delivery has 110 rows, and is complete for public names.

## Disclosed for the audit

**1. Thirteen re-pointed NM-helper headers (REPORT §9.5; accepted by the maintainer).**
- The headers that name a deleted copy change. They are:
  - `chalRun_eq`, `realView_eq`, `idealView_eq`, `take_eq_flatten_chunkAt`, `recView_nmOutL`;
  - `altMsg_eq`, `nmFin_eq`, `nmOutL_eq`, `nmOutput_eq_entryTails`;
  - `simCt_eq`, `simFin_eq`, `simMsg_eq`, `simOutL_eq`;
  - three `rdU` field types of `NMSim.ChalParams`.
- Each is the base header with only the name map applied (`rdU`→`rU` … `chunkAt`→`coinBlock`), and every folded
  definition has exactly its successor's body. The maintainer re-checked all 13 independently.
- The accepted DL-37 payback names exactly these folds, which is why the headers must change.
- All 16 endpoints and every declaration of the owned files `Indistinguishability.lean` and `Simulation.lean` are
  byte-identical (`review.md`).

**2. The B3 escalation.** Folding the aliases would restate:
- the headers `EnsembleLemmas.exists_copiesRed`, `ofFn_blocks_symm`, `take_drop_ofFn_blocks` and
  `CommitmentLemmas.ComLoop.emit_init_of_lt`;
- the bodies of `PRFGame.pkTapes` and `Ensemble.copies`.

So both aliases are kept, and the item is recorded as ledger row DL-38 with its correction.

## Questions for the audit

**1. Statement freeze**
- Does any audited statement change, beyond item 1 above?
- Are the 13 headers really rename-only, with every folded definition body-identical to its successor?
- Are the 16 endpoints byte-identical?
  - `prfFixedScheme_cpa`, `prfFixedScheme_cca1`, `not_prfFixedScheme_cca2`, `prfFixedScheme_not_cca2`;
  - `INDSecure.adaptive_cpa`;
  - `SingleBitSecure.bitwise_padded_cpa`, `exists_adaptive_cpa`, `padded_cpa`;
  - `exists_adaptiveCPA_of_rsa` and `exists_adaptiveCPA_of_factoring`;
  - #294's three IND-CCA2 ⇔ NM-CCA2 theorems;
  - #297's three SIM-NME theorems.
- decls2 from the base to the head: 62 ADDED, 81 REMOVED, 13 CHANGED.

**2. Faithful promotion**
- Is each promoted lemma at least as general as the copies it replaces?
- Are the derived lemmas real corollaries? That covers G5, G6, the B2 block window, the E1 instances and the E1
  bridges.
- Is any deleted copy still needed?
- Does the brief name a copy that was left in place without a recorded reason?

**3. Rule 10** (no touched declaration reads another file's definition, including generated matchers and
projections)
- Whole-file seals over the full closures:

  | Variant | Head | Base |
  |---|---|---|
  | A | 40/47 | 39/46 |
  | B | 35/47 | 34/46 |

- There are 0 new failing declarations, and every failing set is identical to the base. `Games/Forwarding`
  passes both variants.
- The maintainer ran the base side independently, on a copy of the base tree.
- Paired controls: 30 probes and 94 sealed negatives, ALL_OK.
- The explicit-unfold scan finds 0 foreign definitions.
- The worker's harness reports 17 failing variants and the maintainer's 19. The difference comes from the
  maintainer's stricter harness, for example `Games/Probability`'s `dist_apply`, as at Gate 20. Both sides are
  identical at base and head.

**4. Homes and API (policy §1, §3)**
- Is each lemma at its lowest legal home, with no import cycle?
- Names, formula docstrings, module docstrings and `## Contents`/`## Main` entries.
- No `@[simp]` is added.
- Is the new module `Games/Forwarding.lean` well placed?
- `Games/BitCodec` now imports `Complexity.ClassNP.PolyTimeBlockLoop`, for `polyTimeComputable_isNil`. Its closure
  grows from 31 to 41 modules. `Games/Efficiency` already depends on that module. Is this acceptable?

## Also check

**Axioms**
- Census: 2037 → 1974 stored constants.
- Every constant is standard, except the base admission `lamport_oneTimeSecure`.
- The 16 endpoints print `[propext, Classical.choice, Quot.sound]`.
- 6 constants change their axiom sets, all within the standard three: generated matchers and auxiliary proofs,
  `length_flatten_map_const` and `map_coinBlock_flatten`.

**Admissions:** 45 declarations in 24 modules, unchanged.

**Lint:** no new FAIL. The ThreeColoring `Machines` size WARN is gone, because that file went from 1007 lines to 998.

**Sizes and widths**
- Every file is below 1000 lines; `Games/Efficiency.lean` is at 979, so the next change that grows it must split
  it.
- No file gains a line over 100 characters (`source-head.json`).

**Duplication**
- REPORT §0.6 lists further copies, now ledger row DL-38 (open, deferred). That is not a finding.
- What you can raise:
  - a copy this job should have folded and did not;
  - a disagreement with DL-38.

## Evidence

- **`review.md`:** the maintainer's delivery review, verdict ACCEPT.
- **`verification.zip`** (= `fills/dl-folds/final-r1/review-evidence.zip`, SHA-256 `203cfa9a…`): the review's raw
  evidence, complete.
  - It has 1104 entries, and `unzip -Z1` equals its `SHA256SUMS` exactly.
  - It covers:
    - integrity (`git am` replay and manifest check);
    - the base seals on a base tree copy, and the head seals;
    - the build and the final-tree check;
    - the census and name map;
    - decls2, header bytes, definition bodies and the ChalParams diff;
    - axioms;
    - controls;
    - the scan;
    - lint;
    - sizes;
    - the BitCodec import closure.
- **The worker's own evidence:** on the exchange at `8c1dd9c9f61b743e29be06c48478eb1ee05c6914`, under
  `inbox/fills/dl-folds/evidence/`. Its `SHA256SUMS` lists 3082 files, all delivered.
- **`landing/`:** at the final head.
  - `root-checks.jsonl`: root `TCSlib` and both `audits/*/Checks`, rc 0.
  - `final-tree-check.txt`: 1199/1199 modules with rc 0 at the head's source hashes.
  - `axioms-head.txt`.
- **`worker-report.md`:** the worker's `REPORT.md`.
- **`pr.diff.txt`:** `git diff` from the base to the head (36 paths, 1691 insertions, 1677 deletions).
- **`source-head.json`:** the head hashes, line counts and over-width counts of the 36 changed files.
- **`sources.zip`:** the source closure at the head of every changed module, 197 files.

## Findings delivery

Return `gate21-dl-folds-findings.md` as a Markdown file in this chat. If you have several evidence files, return
a ZIP. The user dispatches and merges.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

**Severities**
- **blocker:** a false or unusable statement, or a scope violation.
- **major:** a changed audited statement beyond the disclosed rename set, a lost generality, a forbidden new read in
  a touched declaration, or necessary evidence that cannot be verified.
- **minor:** documentation or API defects.
- **note:** anything else.

Report the audited head and the counts by severity. The gate closes at zero blockers and zero majors.

## ===== briefs/pass-shelat-ch5-8/gates/21-dl-folds/review.md =====

# dl-folds · maintainer delivery review (r1)

**Verdict: ACCEPT.** No landing edit is needed.

- **Delivery:** Claude worker, exchange `8c1dd9c9f61b743e29be06c48478eb1ee05c6914` (`inbox/fills/dl-folds/`).
  - Checkpoints: `f6f773c0`, `6d988dc8`, `ae4ca8e6`.
  - Worker head: `5ad4c07759ee60e6c66fcc1c3b560176267b7c10`, tree `f5f85616dd6733bd295c75dd705a4285167c523a`: 3 commits on
    the issue base `d3f2290a2c66f614e8807903b89ac595086578b3`.
- **Landing branch:** `land/pass-shelat-dl-folds`, the 3 worker commits (authors kept) rebased onto records tip
  `934eac64c410ef69a2f52eb92b91e501c655ed2b`. The 5 commits from `d3f2290a` to that tip change only records. The rebase had
  no conflict.
  - Head: `fcdb65794698395f8eaa377df0789f7552681633`, tree `bc738121c68729f6b1172cc10cf7b559705a52f5`.
  - Its `TCSlib/`, `audits/`, `scripts/`, lakefile and manifest are identical to the worker's head.
- **Evidence:** `review-evidence.zip`, SHA-256 `203cfa9ae085b3e2485ebc11c6c7c178ae23fd409b9049c22b27cfacb7a96b78`.
  - It has 1104 entries. Its manifest is `evidence-SHA256SUMS` (SHA-256 `032669b5…`).
  - `unzip -Z1` lists exactly the manifest's paths. Nothing was left out.
- **Extracts:** in `landing/`.

## Dispositions

| Item | Disposition |
|---|---|
| G1–G7 | Done. There is a new module, `Games/Forwarding.lean` (G7), with a module docstring and an entry in the `Games` facade. |
| R1–R3 | Done. The four answer-reader copies became one `InteractiveHandler.rAns`. |
| B1, B2 | Done. B2 also covers the GGM `Evaluator` restatement that the worker's grep found: its proof was re-derived through `FunFamily.ofFn_blocks`, and its statement is unchanged. |
| **B3** | **Escalated, as the ruling allows.** Both `blocks` aliases are kept. A fold would change four headers (`EnsembleLemmas.exists_copiesRed`, `ofFn_blocks_symm`, `take_drop_ofFn_blocks`, `CommitmentLemmas.ComLoop.emit_init_of_lt`) and two definition bodies (`PRFGame.pkTapes`, `Ensemble.copies`). The maintainer confirms this against the code. The smallest correction is a gate-approved restatement; every affected definition is definitionally equal (`blocks_eq` is `rfl`). |
| L1–L4 | Done. Both ZK copies of `ofFn_eq_map_range` are deleted. |
| E1–E3 | Done. `logEmit` and `chunkMap` are `iterEmit` instances with unchanged types. `relabelN` and `relabel` keep their definitions and are bridged by `relabelN_eq_iterEmit` and `relabel_eq_iterEmit`. |

## §9.5: the 13 re-pointed NM-helper headers (accepted)

The helper headers that name a deleted copy change. They are:
- `chalRun_eq`, `realView_eq`, `idealView_eq`, `take_eq_flatten_chunkAt`, `recView_nmOutL`;
- `altMsg_eq`, `nmFin_eq`, `nmOutL_eq`, `nmOutput_eq_entryTails`;
- `simCt_eq`, `simFin_eq`, `simMsg_eq`, `simOutL_eq`;
- the `rdU` field types of `NMSim.ChalParams`.

Why they are accepted:
- **Rename only.** Each is the base header with the name map applied (`rdU`→`rU` … `rdLog`→`rL`, `finU`/`finZ`/`finW`→`rU`/`rZ`/`rW`, `finSt`→`rS`, `chunkAt`→`coinBlock`), and nothing else. The maintainer re-checked all 13 with their own token map, and all 13 are identical after it.
- **Same bodies.** Every folded definition has exactly its successor's body.
- **Required by the ruling.** The DL-37 payback that Seyoon accepted names exactly these folds, so these headers must change. This matches the R6 precedent of the consolidation.
- **Frozen statements are untouched.** All 16 endpoint headers, and every declaration of the owned files `Indistinguishability.lean` and `Simulation.lean`, are byte-identical: 102/102.
- This is disclosed to the gate.

## Checks (re-run by the reviewer)

**Integrity**
- `evidence/SHA256SUMS` passes 3082/3082. The delivered paths are exactly the manifest's.
- `git am` at the base, with the worker's committer and dates, reproduces all 3 commits and tree `f5f85616`.
- The 36 changed paths are byte-identical to `src/`.

**Build**
- The 226 changed and downstream modules were rebuilt through root `TCSlib` and both `audits/*/Checks`. All have
  rc 0.
- All 1199 TCSlib/`audits` modules end with rc 0 at the head's source hash.
- After the container restart, every olean matched its recorded object hash.

**Statements**
- decls2 over the 36 files: 62 ADDED, 81 REMOVED, 13 CHANGED (the §9.5 set). The maintainer re-ran it.
- Of the 26 changed definition bodies, 24 are re-pointings under the name map; the other two are the E1 instances.
- The name map has 110 rows. In every row the old name is gone and the new one is present. Every removed public
  declaration is mapped. The unmapped removed names were all private at the base.
- No stale qualified names or module-docstring entries remain.

**Axioms**
- The census counts 2037 stored constants at the base and 1974 at the head.
- They are standard, except the base admission `lamport_oneTimeSecure` (`sorryAx`).
- The 16 endpoints print `[propext, Classical.choice, Quot.sound]`.
- The 6 changed axiom sets are the worker's, all within the standard three.

**Rule 10**
- Whole-file seals over the full closures. Both sides were run independently: the base on a copy of the base tree.

  | Variant | Head | Base |
  |---|---|---|
  | A | 40/47 | 39/46 |
  | B | 35/47 | 34/46 |

- **0 new failing declarations.** Every failing set is identical to the base. `Games/Forwarding` passes both
  variants.
- The worker counts 17 failing variants and the reviewer 19. The difference comes from the reviewer's stricter
  harness (for example `Games/Probability`'s `dist_apply`), as in the consolidation review.
- Paired controls: 30 probes over `iterEmit`, `rAns`, `finA`, `cntRead`, `ansRead`, `coinBlock`, `fwdHandler`,
  `logEmit`, `chunkMap`, `PolyExpr.eval` and `padFin`. ALL_OK: 94 sealed negatives, each failing exactly once.
- The explicit-unfold scan finds 0 foreign definitions, at the head and at the base.

**Admissions:** 45 declarations in 24 issued modules, as in `base-sorries.txt`.

**Lint:** 216 FAIL at the base and the head. WARN goes from 103 to 102: `ThreeColoring/Machines.lean` dropped from
1007 lines to 998.

**Sizes and widths:** every file is below 1000 lines, and no line is newly over 100 characters.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| 1 | low | `Games/BitCodec` now imports `Complexity.ClassNP.PolyTimeBlockLoop`, for `polyTimeComputable_isNil` (`cntRead`). Its closure grows from 31 to 41 modules (`landing/bitcodec-import-closure.txt`). `Games/Efficiency` already depends on that module, so the Games layer gains no new dependency. | Accepted. |
| 2 | low | `Games/Efficiency.lean` is at 979 lines. | Recorded. The next change that grows it must split it first. |
| 3 | nit | The docstring of `OracleComp.CostBoundedBy.bind_of_allOutputs` has no formula. | Follow-up; not worth rebuilding everything downstream of `Games/OracleComp`. |
| 4 | info | The worker's map covers public names. The private renames are in REPORT §6, §9.8 and §10.4. | Recorded. |
| 5 | info | New duplication found but not folded: REPORT §0.6 lists inline re-proofs, further block-window restatements, other iterate-and-emit loops, and Complexity copies (out of scope). | Recorded in the ledger as DL-38. |

## ===== briefs/pass-shelat-ch5-8/gates/21-dl-folds/worker-report.md =====

# Fill `dl-folds` — DL-36 and DL-37 folds and accepted promotions

**Status: final delivery.** §0 is the final summary and the final checks. §1–§8 are the
checkpoint-1 report, §9 checkpoint 2 and §10 checkpoint 3, kept as delivered (their numbers are
checkpoint numbers; the final ones are in §0).

| | |
|---|---|
| Unit | `dl-folds` (brief `outbox/fills/dl-folds/brief.md`, exchange `a0a46d7c5`; `evidence/inputs/`, SHA256SUMS 7/7 OK) |
| Worker | Claude |
| Issue base | `d3f2290a2c66f614e8807903b89ac595086578b3` (merge of #298) on `cryptography/pass-shelat-ch2-4` |
| Branch | local `fill/dl-folds`, head `5ad4c07759ee60e6c66fcc1c3b560176267b7c10` = checkpoint 3 (three commits on the base: `b3f7dae2c` checkpoint 1, `a2b3b3a4f` checkpoint 2, `5ad4c0775` checkpoint 3); the final delivery adds evidence only |
| Toolchain | Lean 4.25.0, Mathlib of the base's `lake-manifest.json` |
| Order | base `order.txt` 421 modules; final `evidence/final/order-final.txt`, 422 modules (`Games/Forwarding` new) |

## 0. Final summary

### 0.1 Items

| Item | Disposition | Where |
|---|---|---|
| G1 budget reduction, `buildComp_of_ret` | done | §3 |
| G2 calls and finalizations (and the private PRF copy) | done | §3 |
| G3 `expect_toCompOn_outLen` | done | §3 |
| G4 possible outputs, costs | done | §3 |
| G5 one-shot coins drawn in advance | done; `ChallengeSim.expect_simulate_eager` derived | §3 |
| G6 equal until bad in expectation | done; `prob_eq_until_bad` derived | §3 |
| G7 forwarding handler, hard-wired advice, log readings | done (new module `Games/Forwarding.lean`) | §3 |
| R1 finalization readers | done | §9.3 |
| R2 round-input readers | done | §9.3 |
| R3 answer reader (four copies) | done | §3, §9.3 |
| B1 `chunkAt` → `coinBlock` | done | §9.3 |
| B2 block lemmas, one block window | done (plus GGM's restatement, found by the grep) | §9.3 |
| B3 the two `blocks` aliases | **escalated**: kept, with the list of statements a fold would change | §9.4 |
| L1 lists | done (both ZK copies deleted) | §9.3 |
| L2 `padFin_append_split` | done | §9.3 |
| L3 `seedEquiv`, `seedEquivPoly` | done | §9.3 |
| L4 `ofFn_padFin_eq_padL` | done (same statement; copy deleted) | §9.3 |
| E1 iterate and emit | done (`logEmit`, `chunkMap` instances; `relabel` bridged) | §10.2 |
| E2 `polyTimeComputable_guessBit` | done | §10.2 |
| E3 `ctLen_pos`, `indImpl_eq_of_msgLen_eq_zero` | done | §10.2 |

One question for the reviewer is open: the 13 NM helper headers re-pointed by R1/R2/B1 (§9.5).

### 0.2 Final checks (`evidence/final/`)

| Check | Result | Evidence |
|---|---|---|
| **Full fresh sweep** | all 422 modules of `order-final.txt` rechecked in order, one `lean_check_tree.sh` call each: **422/422 pass, 0 errors** (`CookLevin/Hardness`, 314 s, ran as its own job) | `sweep.tsv`, `sweep-logs/`, `sweep-run.log` |
| **Sorry census** | **45 declarations in 24 modules**, identical to `base-sorries.txt` and to the base bootstrap | `sorry-census-final.txt`, `logs/sorry-census-base.txt` |
| **Census** (36 changed and new modules, base against final) | REMOVED 110 (the listed copies and their generated auxiliaries), ADDED 83 (all public, semireducible, not `simp`, not instances), **CHANGED 1** (the generated matcher `ChallengeSim.expect_simulate_eager.match_1_1` of the G5 re-derivation: a proof artifact), REPOINTED 40 (types equal after the name map), name map complete (every removed name mapped; every old name gone and every new name present) | `census/census-final.log`, `census/census-diff-final.txt`, `../census/namemap.tsv` |
| **Statements** (decls2 over the 36 files) | 62 ADDED, 81 REMOVED, 13 CHANGED; **13/13 identical after the textual name map** (R1/R2/B1 re-pointings in NM helper files, §9.5); **0 CHANGED in the owned files `NMI.lean`, `Simulation.lean`** | `statements/decls2-final.tsv`, `decls2-final-modmap.txt` |
| **Audited endpoints and owned files, byte comparison** | the 16 endpoint headers and every theorem/definition header of `NMI.lean` and `Simulation.lean`: **96/96 byte-identical** | `statements/endpoint-headers.txt` (tool `tools/endpoints_headers.py`) |
| **Definition bodies** | 26 changed: 24 re-pointings (identical after the name map) and the 2 intended E1 instances `logEmit`, `chunkMap` (types unchanged) | `statements/bodies-final.tsv`, `bodies-final-modmap.txt` |
| **Axioms** | 1974 stored constants of the 36 modules and the 16 endpoints. Every constant uses a subset of `propext`, `Classical.choice`, `Quot.sound`, except the base's admitted `Authentication.lamport_oneTimeSecure` (`sorryAx`, as at the base). **Every endpoint: `[Classical.choice, Quot.sound, propext]`**, as at the base. Changed sets (6, all within the three): the generated `ChallengeSim.expect_simulate_eager.match_1_1` and `simParams._proof_3/_5` lose `Classical.choice`/`Quot.sound`, `simParams._proof_4` gains them (the auxiliary proofs of `simParams`' fields are renumbered by the re-pointed fields), `length_flatten_map_const` gains `Quot.sound` (now `List.length_flatten`/`List.sum_replicate_nat`), `map_coinBlock_flatten` gains `Classical.choice` (now derived from `coinBlock_flatten`). | `axioms/axioms-final.log`, `axioms/axioms-compare.txt` (base: `logs/census/axioms-base.log`; endpoints outside the base superset: the consolidation's `ENDPOINT` lines, all three axioms) |
| **Seals A and B** (whole file, full TCSlib import closure; A = `PolyExpr.eval` exempt, B = sealed) | 47 files: the 46 base-superset files, which contain every changed file except the facade `Games.lean` (imports only, no declaration), and the new `Games/Forwarding.lean`: **0 new failing declarations**; the 17 failing variants fail exactly as at the base (pre-existing, e.g. `EnsemblesLemmas` 10/10, `Lamport` B 11, `AdaptiveCPA/Handler` B 3, `OracleSecurity` B 2) | `final/seal-compare.txt`, `logs/seal/final/`, `logs/seal/base/`, sources `seal-src/final/`, `seal-src/base/` |
| **Paired controls** | 10 examples reading one definition each by `rfl` (`PolyExpr.eval`, `iterEmit`, `rAns`, `finA`, `ansRead`, `cntRead`, `coinBlock`, `logEmit`, `chunkMap`, `fwdHandler`): unsealed **pass**; sealed **10/10 fail, one error each**; sealed with `PolyExpr.eval` open **9/10 fail**, only the `PolyExpr.eval` example passes. (A first run had an ill-posed `iterEmit` example that failed unsealed; it was corrected and the three runs repeated; the first run is kept in `final-checks.log`.) | `controls/`, `controls/src/` |
| **Explicit-unfold scan** (every identifier passed to `rw`/`simp`/`unfold`/`delta`/… in each of the 36 files, resolved in the file's namespaces and `open`s) | 1863 theorems, 108 own definitions, 4 core (`reduceIte`), 531 local/unresolved, **0 foreign TCSlib definitions** | `rwids/rwids-final.tsv`, `rwids/scan-*.log`, `rwids/src/` (tool `tools/rwids.py`, the consolidation's, with two fixes noted in its header) |
| **Lint** | 216 FAIL (exactly the base's lines), 102 WARN (the base's minus `ZeroKnowledge/ThreeColoring/Machines.lean`, now 998 lines) | `lint-final.log`, `lint-diff.txt` |
| **`audits/`** | none of the 87 deleted or moved names occurs in `audits/` | `audits-check.txt` |
| **Patch replay** | the three patches applied to the base give the branch's tree `f5f85616…` | `patch-replay.log` |

### 0.3 Files (base → final, lines)

| File | Base | Final |
|---|---|---|
| `Games.lean` (facade) | 61 | 64 |
| `Games/Forwarding.lean` (**new**) | — | 212 |
| `Games/OracleComp.lean` | 331 | 371 |
| `Games/Simulate.lean` | 327 | 374 |
| `Games/Probability.lean` | 397 | 409 |
| `Games/Machines.lean` | 216 | 278 |
| `Games/BitCodec.lean` | 399 | 444 |
| `Games/Hopping.lean` | 445 | 524 |
| `Games/Efficiency.lean` | 844 | 979 |
| `Games/Efficiency/OracleBridge.lean` | 321 | 410 |
| `Foundations/BitLists.lean` | 105 | 179 |
| `Asymptotic/Adversary.lean` | 373 | 452 |
| `Asymptotic/EnsemblesLemmas.lean` | 865 | 887 |
| `Authentication/Signatures/Lamport.lean` | 581 | 567 |
| `Pseudorandom/Functions/Asymptotic/GGM/Evaluator.lean` | 265 | 254 |
| `Encryption/PrivateKey/FromPRF/ReductionMachine.lean` | 573 | 572 |
| `Encryption/PrivateKey/OracleFromPRF/Handler.lean` | 702 | 672 |
| `Encryption/PublicKey/AdaptiveCPA/Handler.lean` | 543 | 542 |
| `Encryption/PublicKey/OracleSecurity.lean` | 723 | 765 |
| `Encryption/PublicKey/OracleSecurity/ChallengeSim.lean` | 315 | 369 |
| `NMI.lean` | 655 | 647 |
| `NMI/Forward.lean` | 350 | 140 |
| `NMI/Decrypt.lean` | 350 | 318 |
| `NMI/Encrypt.lean` | 332 | 331 |
| `Simulation.lean` | 795 | 797 |
| `NMS/Generic.lean` | 460 | 181 |
| `NMS/Rounds.lean` | 356 | 45 |
| `NMS/Hybrid.lean` | 683 | 575 |
| `NMS/Challenge.lean` | 415 | 450 |
| `NMS/Simulator.lean` | 628 | 636 |
| `NMS/Reduction.lean` | 661 | 682 |
| `NMS/Recover.lean` | 519 | 495 |
| `NMS/SimIND.lean` | 912 | 913 |
| `NMS/IndSim.lean` | 293 | 294 |
| `ZeroKnowledge/ThreeColoring/Machines.lean` | 1007 | 998 |
| `ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean` | 450 | 440 |

36 paths: 35 changed, 1 new; nothing deleted. Every file is below 1000 lines.

### 0.4 Imports (all checkpoints)

| Module | Change | Reason |
|---|---|---|
| `Games.lean` (facade) | + `Games.Forwarding` | its new child; only `TCSlib.lean` imports the facade |
| `Games/Forwarding.lean` (new) | `Games.Efficiency` | `InteractiveHandler` |
| `Games/BitCodec.lean` | + `TCSlib.Complexity.ClassNP.PolyTimeBlockLoop`, + `Mathlib.Data.List.GetD` | `polyTimeComputable_isNil` (`cntRead`), `List.getD_append*` (`padFin_append_split`) |
| `Foundations/BitLists.lean` | + `Mathlib.Data.Fintype.Basic` | the decidable equality in `decide_map_ofFn`'s statement |
| `Asymptotic/Adversary.lean` | + `TCSlib.Cryptography.Foundations.BitLists` | `length_flatten_map_range` (`coinBlock_flatten_append`) |
| `OracleSecurity/ChallengeSim.lean` (consumer) | + `Games.Hopping` | `Games.expect_simulate_eager` |
| `NMI/Forward.lean` (consumer) | `Games.Efficiency` → `Games.Forwarding` | `Games.fwdHandler` |

Every added import is acyclic: the Complexity and Mathlib modules import no Cryptography module,
`BitLists` imports only Mathlib, `Hopping` imports only `Simulate` and `Advantage`, and nothing below
`Games.lean` imports it. The final order is the base order with `Games/Hopping` before `ChallengeSim`,
`Foundations/BitLists` before `Asymptotic/Adversary`, and `Games/Forwarding` before `NMI/Forward`
(stable topological re-sort, `tools/reorder.py`).

### 0.5 Name map

`evidence/census/namemap.tsv` (old → new full names; `-` for a deleted declaration without a
successor) is complete for the public constants: the census lists no removed name outside it, and
every row is checked (old gone, new present). The private renames and deletions are in §6, §9.8 and
§10.4. Summary of the public map:

| Old | New |
|---|---|
| `NMSim.buildComp_budget_eq`, `buildComp_of_ret` | `Games.buildComp_budget_eq`, `buildComp_of_ret` |
| `NMSim.toCompOn_budget_eq` | `Complexity.NUPPT.toCompOn_budget_eq` |
| `NMSim.impl_of_ret`, `impl_of_query`, `finish_of_ret` | `Games.InteractiveHandler.impl_of_ret_padFin`, `impl_of_query_padFin`, `finish_of_ret_padFin` |
| `NMSim.expect_toCompOn_outLen`, `expect_simulate_eager`, `expect_eq_until_bad`, `simulate_costBoundedBy_once` | `Games.*` (same last names) |
| `NMSim.expect_congr_of_allOutputs`, `expect_expect_sample` | `Games.ProbComp.*` |
| `NMSim.bind_congr_of_allOutputs` | `Games.OracleComp.bind_congr_of_allOutputs` |
| `NMSim.costBoundedBy_bind_of_allOutputs` | `Games.OracleComp.CostBoundedBy.bind_of_allOutputs` |
| `NMCCA2.fwdHandler` (+ 8 `simps` lemmas, `congr_simp`), `fwdHandler_impl` | `Games.fwdHandler` (+ the same), `Games.fwdHandler_impl` |
| `NMCCA2.exists_withAdviceOn` | `Complexity.NUPPT.exists_withAdviceOn` |
| `NMCCA2.cntRead`, `ansRead` (+ `_eq`, `polyTimeComputable_`) | `Games.*` |
| `NMCCA2.finU`, `finZ`, `finW`, `finL`; `NMSim.finSt` | `Games.InteractiveHandler.rU`, `rZ`, `rW`, `rL`; `rS` |
| `NMCCA2.finA` | `Games.InteractiveHandler.finA` |
| `NMSim.finSt_finInput`, `polyTimeComputable_finSt` | `InteractiveHandler.rS_finInput`, `polyTimeComputable_rS` |
| `NMSim.rdU`, `rdZ`, `rdW`, `rdState`, `rdIdx`, `rdQuery`, `rdLog`, `rdAns` | `InteractiveHandler.rU`, `rZ`, `rW`, `rS`, `rI`, `rX`, `rL`, `rAns` |
| `NMSim.rdAns_eq`, `rdAns_input` | `InteractiveHandler.rAns_eq`, `rAns_input` |
| `NMCCA2.fin*_eq`, `fields_finInput`, `polyTimeComputable_finFields`; `NMSim.rd*_eq` (except `rdAns_eq`), `finSt_eq`, `fields_input`, `polyTimeComputable_rd` | — (uses read the per-reader `_input`/`_finInput`/`polyTimeComputable_` lemmas) |
| `NMSim.chunkAt`, `chunkAt_eq`, `length_chunkAt` | `coinBlock`, `coinBlock_eq`, `length_coinBlock` |
| `NMSim.chunkAt_flatten_append`, `map_chunkAt_flatten`, `ofFn_block` | `coinBlock_flatten_append`, `map_coinBlock_flatten`, `ofFn_block_eq_coinBlock` |
| `Authentication.coinBlock_flatten` | `TCSlib.Cryptography.coinBlock_flatten` |
| `NMSim.ofFn_natAdd_eq_drop`, `decide_map_ofFn`, `length_flatten_map_const`, `length_flatten_map_range`, `ofFn_eq_map_range`; `ColMachines.ofFn_eq_map_range`, `GI.ofFn_eq_map_range` | `TCSlib.Cryptography.*` (BitLists) |
| `NMSim.padFin_append_split` | `Games.padFin_append_split` |
| `NMSim.seedEquiv`, `seedEquiv_ofFn`, `seedEquivPoly`, `seedEquivPoly_ofFn` | `EnsembleLemmas.*` |
| `NMSim.ofFn_padFin_eq_padL` | `EnsembleLemmas.ofFn_padFin_eq_padL` |
| `NMSim.polyTimeComputable_guessBit` | `NMCCA2.polyTimeComputable_guessBit` |
| `NMSim.ctLen_pos`, `NMCCA2.indImpl_eq_of_msgLen_eq_zero` | `FixedLengthPKScheme.ctLen_pos`, `indImpl_eq_of_msgLen_eq_zero` |

New declarations without a predecessor: `Games.InteractiveHandler.impl_of_query`, `finish_of_ret`,
`rAns` (and `rAns_eq`, `rAns_input`, `polyTimeComputable_rAns`), `rU_finInput`, `rZ_finInput`,
`rW_finInput`, `rS_finInput`, `rL_finInput`, `finA_finInput`, `polyTimeComputable_finA`;
`Games.iterEmit`, `iterEmit_eq`, `length_iterate_le_add`, `polyTimeComputable_iterEmit`,
`iterEmit_encode`; `EffFill.relabelN_eq_iterEmit`, `relabel_eq_iterEmit`.

### 0.6 New duplication found (not folded)

- §7: inline re-proofs of `impl_of_query` (`acHandler_impl_forward`) and of a returning finalization
  (`pkHandler_finish`, `acHandler_finish`); a local `have` that is `polyTimeComputable_ansRead`
  (`OracleFromPRF.lean`).
- §9.3: further block-window restatements (`Primality.ofFn_chunk`, `ColRep.drop_take_ofFn_blockRead`,
  `Factoring.fac_ofFn_halves`, already corollaries; `HardCoreLoops.take_drop_blocksStr`, a different
  definition); Complexity copies of `ofFn_eq_map_range` and `flatMap_range_drop` (out of scope).
- §10.2: other iterate-and-emit loops (`BlockEncryptor`, `EnsembleLemmas.CopiesLoop`,
  `StretchMachine`, `CommitmentLemmas.ComLoop`, ZK `EncodingMachines`), and the ZK pair
  `GI.iterate_pairSndD_encodeMsgs` / `ColMachines.iterate_pairSndD_encodeMsgs`.

### 0.7 Evidence

`evidence/SHA256SUMS` lists every evidence file, and the delivered evidence paths are
exactly the manifest's (checked by `tools/pack.py` at packing). Directories: `inputs/` (the brief's
inputs), `logs/` (environment, base bootstrap, base census and axioms, base seals, base lint and
sorry census), `cp1/`, `cp2/`, `cp3/` (checkpoint sweeps, censuses, statements, lint, patch
replays), `final/` (§0.2), `census/namemap.tsv`, `grep/` (receipts of groups G, R/B/L, E), `b3/` (the
B3 probe and its output), `seal-src/` (every seal and scan source, base, checkpoints and final),
`tools/` (every script and the census, axiom and probe sources).

## 1. Checkpoint 1 at a glance

- All seven G items are **done**: the listed copies are deleted (14 `NMSim` lemmas; `NMCCA2`'s
  `fwdHandler`, `fwdHandler_impl`, `exists_withAdviceOn`, `cntRead` and `ansRead` with their
  lemmas; the private PRF `impl_of_query`), their uses re-pointed, and the promoted lemmas
  published in the Games layer under new names (§3). No item is escalated.
- **Statements:** `decls2` over the 24 changed and new files: 28 ADDED, 23 REMOVED, **0 CHANGED**
  (`evidence/cp1/statements/decls2-cp1.tsv`). The audited endpoints are untouched (none of their
  files' headers changed; the endpoint files `Indistinguishability.lean` and `Simulation.lean`
  changed only in one proof line and in docstrings, §5).
- **Census** (public constants, base against checkpoint 1, name map applied): REMOVED 32 = the
  listed copies and their generated `simps` field lemmas and `congr_simp`; ADDED 41 = the promoted
  lemmas, the published readers, the generated lemmas of the moved definitions, and three
  generated matchers of the re-derived `ChallengeSim.expect_simulate_eager`; **CHANGED 1**, that
  re-derived proof's generated matcher `ChallengeSim.expect_simulate_eager.match_1_1` (a proof
  artifact, not a statement); REPOINTED 6 (types equal after the name map); map check 0 bad
  (`evidence/cp1/census/census-diff-cp1.txt`).
- **Build:** every module from the first edited one (`Games/OracleComp`, position 199) to the end of
  the recomputed order checked, 224/224 pass (`evidence/cp1/sweep.tsv`); after a last
  docstring-only edit, positions 286–422 rechecked, 137/137 pass (`evidence/cp1/sweep2.tsv`).
- **Sorry census:** 45 declarations in 24 modules, identical to `base-sorries.txt`
  (`evidence/cp1/sorry-census.txt`, `evidence/logs/sorry-census-base.txt`).
- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b`: 216 FAIL,
  103 WARN, the same FAIL and WARN lines as at the base (`evidence/cp1/lint-cp1.log`,
  `evidence/logs/lint-base.log`).
- **Rule 10 (early check):** whole-file seals A and B of 11 changed and new files pass with no
  failing declaration (`evidence/logs/seal/cp1/results.jsonl`, sources `evidence/seal-src/cp1/`).
  The full seal comparison (every changed file, base and final, controls, explicit-unfold scan)
  belongs to the final delivery.
- **Patch replay:** the series applied to the base gives the branch's tree
  (`evidence/cp1/patch-replay.log`).

## 2. Files (checkpoint 1)

| File | Lines base → cp1 |
|---|---|
| `Games/OracleComp.lean` | 331 → 371 |
| `Games/Simulate.lean` | 327 → 374 |
| `Games/Probability.lean` | 397 → 409 |
| `Games/Machines.lean` | 216 → 278 |
| `Games/BitCodec.lean` | 399 → 430 |
| `Games/Hopping.lean` | 445 → 524 |
| `Games/Efficiency.lean` | 844 → 935 |
| `Games/Forwarding.lean` (**new**) | — → 212 |
| `Games.lean` (facade) | 61 → 64 |
| `Encryption/PublicKey/OracleSecurity/ChallengeSim.lean` | 315 → 369 |
| `Encryption/PrivateKey/OracleFromPRF/Handler.lean` | 702 → 673 |
| `NMI/Forward.lean` | 350 → 230 |
| `NMI/Decrypt.lean` | 350 → 298 |
| `NMI/Encrypt.lean` | 332 → 332 |
| `NMI.lean` (`Indistinguishability.lean`) | 655 → 655 |
| `NMS/Generic.lean` | 460 → 224 |
| `NMS/Rounds.lean` | 356 → 194 |
| `NMS/Challenge.lean` | 415 → 416 |
| `NMS/Hybrid.lean` | 683 → 683 |
| `NMS/SimIND.lean` | 912 → 911 |
| `NMS/Simulator.lean` | 628 → 628 |
| `NMS/Reduction.lean` | 661 → 661 |
| `NMS/IndSim.lean` | 293 → 293 |
| `Simulation.lean` | 795 → 796 |

Paths are relative to `TCSlib/Cryptography/`; `NMI/`, `NMS/` as in the brief. Every file stays below
1000 lines. `Games/Efficiency.lean` keeps 64 lines of room for the R1 readers of checkpoint 2.

## 3. Items of group G

The grep receipts (searches at the base, with hits) are in `evidence/grep/group-G.txt`
(script `evidence/tools/greps_g.sh`).

### G1 — budget reduction and `buildComp_of_ret` — done

- `NMSim.buildComp_of_ret` → `Games.buildComp_of_ret` (`Games/Machines.lean`, in section
  `BuildComp` beside `buildComp_zero_of_ret`, `buildComp_succ_of_ret`).
- `NMSim.buildComp_budget_eq` → `Games.buildComp_budget_eq`, beside `buildComp_costBoundedBy`.
- `NMSim.toCompOn_budget_eq` → `Complexity.NUPPT.toCompOn_budget_eq`, beside
  `NUPPT.toCompOn_costBoundedBy` (the namespace of the `NUPPT.toCompOn_*` lemmas of the file).
- Statements are the copies' up to the namespace; proofs unchanged. Uses re-pointed:
  `NMS/Simulator.lean` (`NUPPT.toCompOn_budget_eq`), `Rounds`' own uses moved with the lemmas.
- Further copies: none (receipts G1-budget, G1-ret).

### G2 — calls and finalizations — done

- **Published (Fin form)** beside `InteractiveHandler.impl_of_ret` in `Games/Efficiency.lean`:
  - `InteractiveHandler.impl_of_query`: answer `y' y` and state `s' y` as vectors, the general form
    of both `NMSim.impl_of_query` and the private PRF copy (any outer index `j`, any `perCall ≥ 1`);
  - `InteractiveHandler.finish_of_ret`: `finRun … = ⟨[true], ⟦b⟧⟩ → finish = pure b`.
- **The list forms are different statements** (lists `u`, `v`, `b` with length hypotheses and
  `padFin` in the conclusion), so they are kept as corollaries, derived from the Fin forms with
  `ofFn_padFin_of_length`:
  - `NMSim.impl_of_ret` → `InteractiveHandler.impl_of_ret_padFin`;
  - `NMSim.impl_of_query` → `InteractiveHandler.impl_of_query_padFin`;
  - `NMSim.finish_of_ret` → `InteractiveHandler.finish_of_ret_padFin`.

  They live in the new `Games/Forwarding.lean`, not beside `impl_of_ret`: with them
  `Games/Efficiency.lean` would pass 1000 lines once the R1 readers are added (935 lines now, plus
  about 45). Their statements are the NMSim copies' (same argument order), so the uses only change
  name: `NMS/Challenge.lean` (3), `NMS/Simulator.lean`, `NMS/Reduction.lean`.
- **Private PRF `impl_of_query`** (`OracleFromPRF/Handler.lean:421`) folded onto the published
  `InteractiveHandler.impl_of_query` (with `j = 0`, `perCall = 1` from `pkHandler_perCall`); its
  private helper `encodeLog_one`, used only there, is deleted. The three uses
  (`pkHandler_impl_enc`, `pkHandler_impl_dec_open`, `pkHandler_impl_challenge_none`) now open each
  round goal with `show pkRun q atkBit b _ = _` (the copy stated its hypotheses on `pkRun`
  directly) and, in the second round, `simp only [Fin.val_zero, List.replicate_zero]` (the
  published lemma writes the outer index of the log as `1^j`, the copy as `[]`). Nothing else in
  those proofs changed.
- Further copies (receipts G2-impl, G2-buildComp-use), not folded, recorded in §7:
  `AdaptiveCPA/Handler.lean` `acHandler_impl_forward` re-proves `impl_of_query` inline, and
  `pkHandler_finish`, `acHandler_finish` re-prove a return-at-budget-0 finalization inline. They
  are proofs of published theorems, not declarations, so the brief's rule that other proofs stay
  unchanged keeps them.

### G3 — `expect_toCompOn_outLen` — done

`NMSim.expect_toCompOn_outLen` → `Games.expect_toCompOn_outLen` (`Games/Efficiency.lean`, after
`exists_toCompOn_of_toComp`). Uses (`NMS/Simulator`, `IndSim`, `SimINDGap`) resolve to it through
`open TCSlib.Cryptography.Games` without a source change. No further copy.

### G4 — reasoning on the possible outputs, costs — done

| Copy | Promoted | Home |
|---|---|---|
| `NMSim.expect_congr_of_allOutputs` | `Games.ProbComp.expect_congr_of_allOutputs` | `Games/Hopping.lean`, after `expect_mono_of_allOutputs` |
| `NMSim.bind_congr_of_allOutputs` | `Games.OracleComp.bind_congr_of_allOutputs` | `Games/OracleComp.lean`, after `AllOutputs.bind` |
| `NMSim.costBoundedBy_bind_of_allOutputs` | `Games.OracleComp.CostBoundedBy.bind_of_allOutputs` | `Games/OracleComp.lean`, after `bind_congr_of_allOutputs` |
| `NMSim.expect_expect_sample` | `Games.ProbComp.expect_expect_sample` | `Games/Probability.lean`, section `Sampling` |
| `NMSim.simulate_costBoundedBy_once` | `Games.simulate_costBoundedBy_once` | `Games/Simulate.lean`, after `simulate_costBoundedBy` |

`CostBoundedBy.bind_of_allOutputs` cannot sit directly beside `CostBoundedBy.bind`: it needs
`AllOutputs`, which the file defines after the cost section; it is the last lemma of the
"Possible outputs" section, named in the `CostBoundedBy.bind` style. No further copies.

### G5 — one-shot coins drawn in advance — done

- `NMSim.expect_simulate_eager` (with its private helper `simulate_eq_of_used`) →
  `Games.expect_simulate_eager` (`Games/Hopping.lean`, new section "One-shot coins drawn in
  advance"; the helper stays private there).
- `ChallengeSim.expect_simulate_eager` keeps its name and statement (decls2: unchanged) and is now
  derived from it: with the coins `re` fixed, the CPA oracle becomes a deterministic oracle `OE re`
  (a local `let` defined by `match` in the proof) whose simulation is `chRun (g · re)` (induction);
  from the unchallenged state `Games.expect_simulate_eager` (used = "challenge recorded") gives the
  average; from a recorded state the oracle is already deterministic and `chRun_some_congr` removes
  the dependence on `re`. `ChallengeSim.lean` gains `import TCSlib.Cryptography.Games.Hopping`.
- Uses: `NMS/Hybrid.lean` resolves to the Games lemma unchanged; `PaddedCPA.lean` keeps using the
  ChallengeSim lemma.

### G6 — equal until bad in expectation — done

`NMSim.expect_eq_until_bad` → `Games.expect_eq_until_bad`, directly before `prob_eq_until_bad`.
`prob_eq_until_bad` keeps its statement (decls2: unchanged) and both conjuncts are now derived from
it: "`Q` and good" is `𝔼[if bad then 0 else 1_Q]`, and "bad" is `1 − 𝔼[if bad then 0 else 1]`
(`prob_not`). The private `expect_ite_one_split`, used only by the old second conjunct, is deleted.
Use re-pointed: `NMS/SimIND.lean` (resolves through `open Games`; docstrings qualified).

### G7 — the forwarding handler, hard-wired advice, log readings — done

- **New module `Games/Forwarding.lean`** (imports `Games.Efficiency`; module docstring; imported by
  the facade `Games.lean`, `## Contents` updated):
  - `NMCCA2.fwdHandler` (with its `simps` field lemmas `_stateLen`, `_seedLen`, `_perCall`,
    `_init`, `_advIn`, `_outLen`, `_finCall`, `_finRun`) → `Games.fwdHandler` (same lemmas);
  - `NMCCA2.fwdHandler_impl` → `Games.fwdHandler_impl`, now proved from
    `InteractiveHandler.impl_of_query` and the published `_input` lemmas of the readers;
  - `NMCCA2.exists_withAdviceOn` → `Complexity.NUPPT.exists_withAdviceOn` (it is a fact about
    `NUPPT`, like `NUPPT.exists_withAdvice`); proof unchanged;
  - the three list-form call lemmas of G2.
- **Why a new `Games/` module and not `Games/Efficiency.lean` or a sibling under
  `Games/Efficiency/`:** `Games/Efficiency.lean` would pass 1000 lines (§2). A sibling under
  `Games/Efficiency/` must import `Games.Efficiency` (it needs `InteractiveHandler`), so the
  facade `Games/Efficiency.lean` could not import it, and the lint would add a new FAIL
  ("facade does not import child module") for both `Games/Efficiency.lean` and `Games.lean`.
  Under `Games/` the facade `Games.lean` imports it, and the lint has no new FAIL.
- **Rule 10 and the definition's body:** `fwdHandler`'s round function, the private `fwdRun`,
  moved with it. It read the round input through `Forward`'s private readers `rState`, `rIdx`,
  `rQuery`, `rLog`, `rAns`; it now reads it through the published `InteractiveHandler.rS`, `rI`,
  `rX`, `rL` and the new `InteractiveHandler.rAns` (R3, published in this checkpoint because
  `fwdRun` needs it), with the same bodies. This is the only definition body that changed
  (recorded body change). `Forward`'s private readers and their private `fields_input`, used only
  by `fwdRun` and `fwdHandler_impl`, are deleted (they are R2's private copies).
- `NMCCA2.simulate_fwdHandler_impl` is not in the item list and stays in `NMI/Forward.lean` with
  its name; its statement now mentions `Games.fwdHandler` (re-pointed). The definitions that
  instantiate the handler, `NMCCA2.decHandler`, `NMCCA2.encHandler` and `NMSim.copyHandler`, are
  textually unchanged and now elaborate to `Games.fwdHandler` (census REPOINTED rows of their
  `eq_1` lemmas).
- `cntRead`, `ansRead`, `cntRead_eq`, `ansRead_eq`, `polyTimeComputable_cntRead`,
  `polyTimeComputable_ansRead` → `Games.*` in `Games/BitCodec.lean` (new section "Readings of a log
  entry"). `polyTimeComputable_cntRead` needs `Complexity.polyTimeComputable_isNil`, so
  `Games/BitCodec.lean` imports `TCSlib.Complexity.ClassNP.PolyTimeBlockLoop` (§4).
  `length_logEmit_cntRead` and `logEmit_ansRead` stay in `NMI/Decrypt.lean` (they need `logEmit`,
  item E1). In `length_logEmit_cntRead` the hypothesis `cntRead [] = []` was `rfl`; `cntRead` is
  now another file's definition, so it reads `by rw [cntRead_eq]; rfl` (Rule 10).
- Uses re-pointed: `NMS/SimIND.lean` (`open NMCCA2 (…)` drops the moved names;
  `NMCCA2.fwdHandler_outLen` → `fwdHandler_outLen`), `NMI.lean`, `NMS/Simulator.lean`,
  `NMS/IndSim.lean` (`NUPPT.exists_withAdviceOn`), and docstrings.
- Further copies (receipts G7-*): the private `rY` (PRF handler) and `rFwd` (AdaptiveCPA handler)
  are R3 copies of the answer reader (checkpoint 2). `OracleFromPRF.lean:536` re-proves
  `polyTimeComputable_ansRead` as a local `have` inside a proof (§7).
  `DiscreteLogHardcore.lean:1130` `dlb_fα` has `ansRead`'s body but reads a field of a different
  layout, so it is not a copy.

## 4. Imports and order

| Module | Import change | Reason |
|---|---|---|
| `Games/BitCodec.lean` | + `TCSlib.Complexity.ClassNP.PolyTimeBlockLoop` | `polyTimeComputable_isNil` for `polyTimeComputable_cntRead`; a Complexity module (order 67 < 225), no TCSlib.Cryptography import, so acyclic |
| `Games.lean` (facade) | + `TCSlib.Cryptography.Games.Forwarding` | the facade imports its new child; only `TCSlib.lean` imports `Games.lean`, so acyclic |
| `Games/Forwarding.lean` (new) | `TCSlib.Cryptography.Games.Efficiency` | `InteractiveHandler` |
| `OracleSecurity/ChallengeSim.lean` (consumer) | + `TCSlib.Cryptography.Games.Hopping` | `Games.expect_simulate_eager` |
| `NMI/Forward.lean` (consumer) | `Games.Efficiency` → `Games.Forwarding` | `Games.fwdHandler` |

No downstream module is imported to reach a lemma. The order is recomputed with a stable
topological sort of the base order (`evidence/tools/reorder.py`): `Games/Hopping` moves before
`ChallengeSim` (265 and 266), and `Games/Forwarding` is inserted at 280, before its first consumer
`NMI/Forward` (`evidence/cp1/order-cp1.txt`).

## 5. Statements, bodies and proofs

- `decls2` (`evidence/tools/decls2.py`, the maintainer's tool): 0 CHANGED over the 24 files.
- `bodies.py` (`evidence/tools/bodies.py`, complement to decls2: every definition's whole text and
  every private theorem's header, private declarations included):
  `evidence/cp1/statements/bodies-cp1.tsv` has no CHANGED-BODY and no CHANGED-PRIVATE-HEADER row;
  its REMOVED/ADDED rows are the moves of §3 (`fwdRun`'s body change from private to published
  readers is a move between files and is recorded in G7).
- Proofs that changed beyond re-pointed names, each required by its item:
  `Games.prob_eq_until_bad` (G6), `ChallengeSim.expect_simulate_eager` (G5), the three PRF handler
  proofs (G2), `NMCCA2.length_logEmit_cntRead` (G7, Rule 10), and the moved `fwdHandler_impl` (G7).
- The audited endpoint files `NMI.lean` and `Simulation.lean`: one proof line of
  `nmSecure_cca2_of_indSecure_cca2` re-pointed (`exists_withAdviceOn` →
  `NUPPT.exists_withAdviceOn`) and docstrings re-pointed; no header changed.

## 6. Name map (checkpoint 1)

`evidence/census/namemap.tsv` is the cumulative map (old full name → new full name), checked
against the census (`MAP-CHECK`: every old name absent at head, every new name present). Short
form (NMSim = `Composability.NMSim`, NMCCA2 = `Composability.NMCCA2`, `IH` =
`Games.InteractiveHandler`):

| Old | New |
|---|---|
| `NMSim.buildComp_budget_eq` | `Games.buildComp_budget_eq` |
| `NMSim.toCompOn_budget_eq` | `Complexity.NUPPT.toCompOn_budget_eq` |
| `NMSim.buildComp_of_ret` | `Games.buildComp_of_ret` |
| `NMSim.impl_of_ret` | `IH.impl_of_ret_padFin` |
| `NMSim.impl_of_query` | `IH.impl_of_query_padFin` |
| `NMSim.finish_of_ret` | `IH.finish_of_ret_padFin` |
| (private) `PRFGame.impl_of_query` | `IH.impl_of_query` |
| (private) `PRFGame.encodeLog_one` | — (helper of the deleted copy) |
| `NMSim.expect_toCompOn_outLen` | `Games.expect_toCompOn_outLen` |
| `NMSim.expect_congr_of_allOutputs` | `Games.ProbComp.expect_congr_of_allOutputs` |
| `NMSim.bind_congr_of_allOutputs` | `Games.OracleComp.bind_congr_of_allOutputs` |
| `NMSim.expect_expect_sample` | `Games.ProbComp.expect_expect_sample` |
| `NMSim.costBoundedBy_bind_of_allOutputs` | `Games.OracleComp.CostBoundedBy.bind_of_allOutputs` |
| `NMSim.simulate_costBoundedBy_once` | `Games.simulate_costBoundedBy_once` |
| `NMSim.expect_simulate_eager` | `Games.expect_simulate_eager` |
| (private) `NMSim.simulate_eq_of_used` | (private) `Games.simulate_eq_of_used` |
| `NMSim.expect_eq_until_bad` | `Games.expect_eq_until_bad` |
| (private) `Games.expect_ite_one_split` | — (unused after G6) |
| `NMCCA2.fwdHandler` and its 8 `simps` lemmas, `fwdHandler.congr_simp` | `Games.fwdHandler` and the same lemmas |
| (private) `NMCCA2.fwdRun`, `polyTimeComputable_fwdRun` | (private) `Games.fwdRun`, `polyTimeComputable_fwdRun` |
| `NMCCA2.fwdHandler_impl` | `Games.fwdHandler_impl` |
| (private) `NMCCA2.rState`, `rIdx`, `rQuery`, `rLog`, `rAns` | `IH.rS`, `rI`, `rX`, `rL`, `rAns` |
| (private) `NMCCA2.fields_input` (Forward) | `IH.rS_input`, `rI_input`, `rX_input`, `rL_input`, `rAns_input` |
| `NMCCA2.exists_withAdviceOn` | `Complexity.NUPPT.exists_withAdviceOn` |
| `NMCCA2.cntRead`, `cntRead_eq`, `polyTimeComputable_cntRead` | `Games.cntRead`, `cntRead_eq`, `polyTimeComputable_cntRead` |
| `NMCCA2.ansRead`, `ansRead_eq`, `polyTimeComputable_ansRead` | `Games.ansRead`, `ansRead_eq`, `polyTimeComputable_ansRead` |

New declarations without a predecessor: `IH.impl_of_query` (also the PRF copy's successor),
`IH.finish_of_ret`, `IH.rAns`, `IH.rAns_input`, `IH.polyTimeComputable_rAns`.

## 7. New duplication found (not folded)

1. `AdaptiveCPA/Handler.lean` `acHandler_impl_forward` re-proves `InteractiveHandler.impl_of_query`
   inline (`buildComp_succ_of_query`, then `buildComp_zero_of_ret` with `Fin.append`).
2. `pkHandler_finish` (`OracleFromPRF/Handler.lean`) and `acHandler_finish`
   (`AdaptiveCPA/Handler.lean`) re-prove a returning finalization inline (`buildComp_zero_of_ret`),
   the content of `InteractiveHandler.finish_of_ret`.
3. `OracleFromPRF.lean:536` proves `PolyTimeComputable fun z => pairSndD (pairSndD (pairFstD z))`
   as a local `have`, which is `Games.polyTimeComputable_ansRead`.

Each is inside the proof of a published theorem; the brief keeps other proofs unchanged, so they
are listed for a later cleanup.

## 8. Evidence (checkpoint 1)

`evidence/SHA256SUMS` lists every evidence file, and the delivered evidence paths are exactly the
manifest's paths (checked by `evidence/tools/pack.py`).

| Path | Content |
|---|---|
| `inputs/` | the brief's inputs (brief, addendum, README, `order.txt`, `roots.txt`, `base-sorries.txt`, their SHA256SUMS) |
| `logs/preflight.log`, `cache-*.log`, `packages-check.log`, `mathlib-roots.txt` | environment and narrowed cache fetch (addendum) |
| `logs/bootstrap.tsv`, `logs/bootstrap/` | the base bootstrap, 421/421 |
| `logs/census/census-base.log`, `logs/census/axioms-base.log` | base census (13,639 constants) and base axioms of the 46-file superset |
| `logs/seal/base/` | base whole-file seals A/B, scans, `results.jsonl` (46 files) |
| `logs/lint-base.log`, `logs/sorry-census-base.txt` | base lint and sorry census |
| `cp1/order-cp1.txt`, `cp1/changed-modules.txt` | recomputed order; changed and new modules |
| `cp1/sweep-list.txt`, `cp1/sweep.tsv`, `cp1/sweep-logs/` | checkpoint sweep 199–422 |
| `cp1/sweep2-list.txt`, `cp1/sweep2.tsv`, `cp1/sweep2-logs/` | recheck 286–422 after docstring edits |
| `cp1/sorry-census.txt` | 45 in 24, as at the base |
| `cp1/census/census-cp1.log`, `cp1/census/census-diff-cp1.txt` | census and its comparison |
| `cp1/statements/decls2-cp1.tsv`, `bodies-cp1.tsv` | statement and body comparison |
| `cp1/lint-cp1.log`, `cp1/patch-replay.log` | lint; patch replay |
| `logs/seal/cp1/`, `seal-src/` | early seals of 11 files; all seal sources |
| `census/namemap.tsv` | cumulative name map |
| `grep/group-G.txt` | grep receipts |
| `tools/` | every script used (`chk.py`, `sweep.py`, `reorder.py`, `sorrycensus.py`, `census_diff.py`, `decls2.py`, `bodies.py`, `seal.py`, `files.py`, `greps_g.sh`, `gen_census.py`, `pack.py`) and the census sources (`tools/census/`) |

## 9. Checkpoint 2 — groups R, B, L

### 9.1 At a glance

- R1, R2, R3, B1, B2, L1, L2, L3, L4: **done**. B3: **escalated** (both aliases kept, §9.4).
- **Build:** recomputed order `evidence/cp2/order-cp2.txt` (422 modules). Three sweeps, all
  passing: 160–422 after the R/B/L edits (`cp2/sweep.tsv`, 263/263), 262–422 after docstring and
  `open` edits (`cp2/sweep2.tsv`, 161/161), and 205–422 after the GGM fold
  (`cp2/sweep3.tsv`, 218/218). Every module from the first edited one (`Foundations/BitLists`,
  position 160) to the end passed after its last edit.
- **Sorry census:** 45 declarations in 24 modules, identical to the base (`cp2/sorry-census.txt`).
- **Lint:** 216 FAIL (the base's lines), 102 WARN: one WARN fewer than the base, because
  `ZeroKnowledge/ThreeColoring/Machines.lean` drops from 1007 to 998 lines (`cp2/lint-cp2.log`).
- **Census** (`cp2/census/census-diff-cp2.txt`, 34 changed and new modules, cumulative name map):
  REMOVED 106 (the listed copies, their generated auxiliaries, and the checkpoint-1 removals),
  ADDED 70, **CHANGED 1** (the generated matcher of the re-derived
  `ChallengeSim.expect_simulate_eager`, as at checkpoint 1), REPOINTED 40 (types equal after the name
  map), every removed name in the map, map check 0 bad.
- **Statements:** `decls2` over the 34 files: 52 ADDED, 78 REMOVED, **13 CHANGED**; all 13 are equal
  to the base header after the textual re-pointing `rdU→rU`, `rdState→rS`, …, `finU→rU`, `finSt→rS`,
  `chunkAt→coinBlock` (`cp2/statements/decls2-cp2-modmap.txt`: SAME-MODULO-MAP 13, DIFFERENT 0;
  tool `tools/decls2_map.py`). The 24 changed definition bodies and private headers
  (`bodies-cp2.tsv`) are likewise all re-pointings only (`bodies-cp2-modmap.txt`: 24/24). No header
  of the owned files `NMI.lean` and `Simulation.lean` and no endpoint changed; see §9.5 for the
  question this raises.
- **Rule 10 (early check):** seals A and B of 16 changed files (`logs/seal/cp2/`): no failing
  declaration except `Asymptotic/EnsemblesLemmas.lean`, whose 10 failing declarations are exactly the
  base's (`logs/seal/base/results.jsonl`), so none is new.
- **Patch replay:** the two patches applied to the base give the branch's tree
  (`cp2/patch-replay.log`).

### 9.2 Files changed at checkpoint 2 (base → checkpoint 2, lines)

| File | Lines |
|---|---|
| `Foundations/BitLists.lean` | 105 → 179 |
| `Asymptotic/Adversary.lean` | 373 → 452 |
| `Asymptotic/EnsemblesLemmas.lean` | 865 → 887 |
| `Games/BitCodec.lean` | 399 → 444 |
| `Games/Efficiency.lean` | 844 → 979 |
| `Authentication/Signatures/Lamport.lean` | 581 → 567 |
| `Pseudorandom/Functions/Asymptotic/GGM/Evaluator.lean` | 265 → 254 |
| `Encryption/PrivateKey/FromPRF/ReductionMachine.lean` | 573 → 572 |
| `Encryption/PrivateKey/OracleFromPRF/Handler.lean` | 702 → 672 |
| `Encryption/PublicKey/AdaptiveCPA/Handler.lean` | 543 → 542 |
| `ZeroKnowledge/ThreeColoring/Machines.lean` | 1007 → 998 |
| `ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean` | 450 → 440 |
| `NMI.lean` | 655 → 646 |
| `NMI/Forward.lean` | 350 → 156 |
| `NMI/Decrypt.lean` | 350 → 318 |
| `NMI/Encrypt.lean` | 332 → 345 |
| `Simulation.lean` | 795 → 797 |
| `NMS/Generic.lean` | 460 → 200 |
| `NMS/Rounds.lean` | 356 → 45 |
| `NMS/Hybrid.lean` | 683 → 575 |
| `NMS/Challenge.lean` | 415 → 450 |
| `NMS/Simulator.lean` | 628 → 636 |
| `NMS/Reduction.lean` | 661 → 682 |
| `NMS/Recover.lean` | 519 → 520 |
| `NMS/SimIND.lean` | 912 → 913 |
| `NMS/IndSim.lean` | 293 → 294 |

Every file stays below 1000 lines (`Games/Efficiency.lean` 979). Some NM files grew because the
deleted bundle lemmas `fields_input`, `fields_finInput`, `polyTimeComputable_rd` and
`polyTimeComputable_finFields` are replaced by one `have` per field from the published per-reader
lemmas, and the published names are brought in with `open … (…)` lists.

### 9.3 Items

The grep receipts are in `evidence/grep/groups-RBL.txt` (script `tools/greps_rbl.sh`).

**R1 — finalization readers: done.**
- Beside `InteractiveHandler.finInput` (`Games/Efficiency.lean`, new subsection "Readers of a
  finalization input"): `rU_finInput`, `rZ_finInput`, `rW_finInput`, `rS_finInput`, `rL_finInput`;
  the new reader `InteractiveHandler.finA` (`finA w = pairFstD (pairSndD (pairSndD w))`) with
  `finA_finInput` and `polyTimeComputable_finA`.
- Deleted: `NMCCA2.finU`, `finZ`, `finW`, `finA`, `finL` and their `_eq`, `fields_finInput`,
  `polyTimeComputable_finFields` (`NMI/Forward.lean`); `NMSim.finSt`, `finSt_eq`, `finSt_finInput`,
  `polyTimeComputable_finSt` (`NMS/Simulator.lean`).
- Re-pointed: the private `dCnt`, `dCt`, `dIn`, `dFin` (`NMI/Decrypt.lean`) and `eBit`, `eMsg`,
  `eTape`, `eCt` (`NMI/Encrypt.lean`); the nm-sim finalizations `simFin`, `simOutL`, `nmFin`,
  `nmOutL` and SimIND's private `copyFin`, with their proofs.

**R2 — round-input readers: done.** Deleted `NMSim.rdU`, `rdZ`, `rdW`, `rdState`, `rdIdx`,
`rdQuery`, `rdLog` with their `_eq`, and the bundle lemmas `NMSim.fields_input` and
`NMSim.polyTimeComputable_rd` (`NMS/Rounds.lean`); uses re-pointed to `InteractiveHandler.rU`, `rZ`,
`rW`, `rS`, `rI`, `rX`, `rL` and their `_input`/`polyTimeComputable_` lemmas in `NMS/Challenge`,
`Simulator`, `Reduction`. `Forward`'s private `rState`, `rIdx`, `rQuery`, `rLog` were removed at
checkpoint 1 with `fwdRun`. The handler-specific private `fields_input` lemmas of the PRF and
AdaptiveCPA handlers read their state fields as well; they are not copies and stay.

**R3 — the answer reader: done.** `InteractiveHandler.rAns` (published at checkpoint 1) gains
`rAns_eq`. Re-pointed: `NMSim.rdAns` and `rdAns_input` (deleted; → `rAns`, `rAns_input`), the
private `rFwd` (AdaptiveCPA handler; deleted, `acRun` reads `rAns`) and the private `rY` (PRF handler;
deleted, `rCt` and `pkRun` read `rAns`; the private `rY_one` now states `rAns w = y` and reads it
through `rAns_eq`).

**B1 — `chunkAt` onto `coinBlock`: done.** `NMSim.chunkAt`, `chunkAt_eq`, `length_chunkAt` deleted;
every use re-pointed to `coinBlock`, `coinBlock_eq`, `length_coinBlock` (definition bodies
`realView`, `idealView`, `nmOutL`, `simOutL` included; `length_chunkAt _ _ _ h` becomes
`length_coinBlock h`, whose block arguments are implicit).

**B2 — block lemmas and the block window: done.**
- Beside `coinBlock` (`Asymptotic/Adversary.lean`): `coinBlock_flatten` (Lamport's
  `Authentication.coinBlock_flatten`, moved, statement unchanged, now `TCSlib.Cryptography.
  coinBlock_flatten`), `map_coinBlock_flatten` (NMSim's `map_chunkAt_flatten`, now derived from
  `coinBlock_flatten` entry by entry: the two were the same fact), `coinBlock_flatten_append`
  (NMSim's `chunkAt_flatten_append`).
- The block window is `FunFamily.ofFn_blocks` (reused, not re-proved). Derived from it, statements
  unchanged: `ofFn_block_eq_coinBlock` (NMSim's `ofFn_block`, with a tail, beside
  `FunFamily.ofFn_blocks`), `NMCCA2.ofFn_nthCt` (`NMI.lean`; proof only),
  `EnsembleLemmas.take_drop_ofFn_blocks` (proof only), `MultiMsg.take_drop_ofFn_blocks`
  (`ReductionMachine.lean`; now `(FunFamily.ofFn_blocks …).symm`), and, found by the grep,
  `GGM`'s public `drop_take_ofFn_blocks` (`GGM/Evaluator.lean`; it re-proved the window element by
  element; now `rw [Nat.mul_comm ℓ k, FunFamily.ofFn_blocks]`). `OneWay.ofFn_block_eq_take_drop`
  already was a corollary of `FunFamily.ofFn_blocks`.
- Not exact copies, so kept: `take_eq_flatten_chunkAt` and `drop_flatten_append` (`NMS/Hybrid.lean`;
  the first now reads `coinBlock`, its name is unchanged because renaming is not allowed).
- Further window facts found and left (receipt B2): the private `Primality.ofFn_chunk`, `ColRep`'s
  `drop_take_ofFn_blockRead` (both already corollaries of the published `ofFn_drop_take`), the
  private `Factoring.fac_ofFn_halves` (already a corollary of `OneWay.ofFn_block_eq_take_drop`),
  `HardCoreLoops.take_drop_blocksStr` (a different definition, `blocksStr`), the GIZK `Closeness`
  field readers (a different layout); Complexity files (`NPPoly`, `PSubsetPPolyTableauCorrect`) are
  out of scope.

**L1 — lists: done.** In `Foundations/BitLists.lean`: `flatMap_range_drop` (the general form of
both private copies, `NMS/Generic.lean` and `NMI/Forward.lean`; Forward's `logEmit_encodeLog` now
instantiates it with `fun l => G (codec.encodeLog l)`), `ofFn_natAdd_eq_drop`, `decide_map_ofFn`,
`ofFn_eq_map_range` (three copies deleted: NMSim's, `ColMachines.ofFn_eq_map_range`, whose one use
passes `fun t => h t t.isLt`, and `GI.ofFn_eq_map_range`), `length_flatten_map_const` (now
`List.length_flatten`, `List.map_const'` and `List.sum_replicate_nat`, as the brief asks), and
`length_flatten_map_range` (NMSim's, needed by `coinBlock_flatten_append`; same Mathlib route).
Mathlib has none of the others as stated. Further copies outside scope: `Codec/Valid.lean`'s
`ofFn_eq_map_range` and `NPPoly`'s `flatMap_range_drop_take` (Complexity files).

**L2: done.** `NMSim.padFin_append_split` → `Games.padFin_append_split` (`Games/BitCodec.lean`,
beside `padFin_nil`; `padFin` itself is in `Asymptotic/Adversary.lean`). It has no use after G2.

**L3: done.** `NMSim.seedEquiv`, `seedEquiv_ofFn`, `seedEquivPoly`, `seedEquivPoly_ofFn` →
`EnsembleLemmas.*` beside `coinsEquiv` (`Asymptotic/EnsemblesLemmas.lean`, 887 lines).

**L4: done.** The statements agree up to the namespace (`List.ofFn (padFin k a) =
EnsembleLemmas.padL k a`), so `NMSim.ofFn_padFin_eq_padL` is deleted and its uses re-pointed to
`EnsembleLemmas.ofFn_padFin_eq_padL`.

`NMS/Rounds.lean` keeps only `length_ofFn_coins`, which the brief keeps local; its module docstring
now says where the rest went.

### 9.4 B3 — escalated: both `blocks` aliases kept

Probe `evidence/b3/B3Uses.lean` (run on the oleans of all 421 modules, output
`evidence/b3/b3-uses.log`): every constant whose type, definition body or proof mentions
`EnsembleLemmas.blocks`, `blocks_eq`, `blocks_apply`, `blocks_symm_apply` or the private
`Ensemble.blocks`/`blocks_eq` of `Asymptotic/Ensembles.lean`.

- **Statements that mention `EnsembleLemmas.blocks`** (folding would change them):
  - theorem headers: `EnsembleLemmas.exists_copiesRed`, `EnsembleLemmas.ofFn_blocks_symm`,
    `EnsembleLemmas.take_drop_ofFn_blocks` (Asymptotic, ch. 2–4),
    `CommitmentLemmas.ComLoop.emit_init_of_lt` (ZeroKnowledge, ch. 4);
  - a definition body: `PRFGame.pkTapes` (`OracleFromPRF/Handler.lean`).
  - (the alias's own lemmas `blocks_eq`, `blocks_apply`, `blocks_symm_apply`).
- **Proofs only** (would only be re-pointed): `ColRep.pushesUniform_blockRead`,
  `PRFGame.ofFn_pkTapes`, `PRFGame.pkTapes_apply`, `Ensemble.Indist.copies`,
  `MultiMsg.take_drop_ofFn_blocks`, the private `owpComStr_eq_loopOut` (Commitment).
- **The private alias of `Ensembles.lean`** is in the body of the definition `Ensemble.copies` and in
  its `eq_1` lemma; its documented purpose is that definition.
- **Obstruction:** the four headers and the two definition bodies are audited ch. 2–5 statements;
  a fold changes their text (and, for `pkTapes` and `Ensemble.copies`, the body) from the alias to
  `FunFamily.blocks`. The alias is public, so the body change is not the allowed private→published
  reader change.
- **Smallest correction:** a gate approval to restate `exists_copiesRed`, `ofFn_blocks_symm`,
  `take_drop_ofFn_blocks` and `ComLoop.emit_init_of_lt` with `FunFamily.blocks` and to re-point the
  bodies of `pkTapes` and `Ensemble.copies` (all definitionally equal: `blocks_eq` and the private
  `blocks_eq` are `rfl`); the aliases and their three lemmas can then be deleted with no proof
  change beyond re-pointing.

### 9.5 Header re-pointing in the NM helper files (decision for the reviewer)

Folding R1, R2 and B1 re-points names that the headers of 13 NM helper theorems and the field types
of `NMSim.ChalParams` mention (`decls2-cp2-modmap.txt`): `chalRun_eq`, `realView_eq`,
`idealView_eq`, `take_eq_flatten_chunkAt`, `recView_nmOutL`, `altMsg_eq`, `nmFin_eq`, `nmOutL_eq`,
`nmOutput_eq_entryTails`, `simCt_eq`, `simFin_eq`, `simMsg_eq`, `simOutL_eq`. Each is the base header
with the deleted reader or block name replaced by its published successor (`rdU`→`rU`, …,
`chunkAt`→`coinBlock`), and the census shows their types equal after the name map. I read "every
theorem of the NM files that Gates 06, 18 and 19 audited" as the owned files `NMI.lean` and
`Simulation.lean` (whose headers are byte-identical) and the endpoints. If the gates' audit is meant
to cover these helper headers byte for byte, R1, R2 and B1 cannot be folded without an alias, and
the smallest correction is to accept these 13 re-pointed headers.

### 9.6 Imports (checkpoint 2)

| Module | Import change | Reason | Acyclic |
|---|---|---|---|
| `Foundations/BitLists.lean` | + `Mathlib.Data.Fintype.Basic` | the decidable equality of `Fin k → Bool` in `decide_map_ofFn`'s statement | Mathlib only |
| `Asymptotic/Adversary.lean` | + `TCSlib.Cryptography.Foundations.BitLists` | `length_flatten_map_range` for `coinBlock_flatten_append` | `BitLists` imports only Mathlib |
| `Games/BitCodec.lean` | + `Mathlib.Data.List.GetD` | `List.getD_append`, `getD_append_right` in `padFin_append_split` | Mathlib only |
| NM consumers | `open TCSlib.Cryptography.Games.InteractiveHandler (…)`, `open TCSlib.Cryptography.EnsembleLemmas (…)` | the re-pointed names | no import |

The recomputed order places `Foundations/BitLists` (160) before `Asymptotic/Adversary` (161).

### 9.7 Definition bodies changed (re-pointing only)

Private → published reader (the allowed kind): `PRFGame.pkRun`, `PRFGame.rCt` (`rY`→`rAns`),
`AdaptiveCPA.acRun` (`rFwd`→`rAns`), `NMCCA2.dCnt`, `dCt`, `dIn`, `dFin`, `eMsg`, `eTape`, `eCt`
(`fin*`→`rU`/`rZ`/`rW`/`rL`/`finA`). Public copy → published successor (the deleted copies' uses):
`NMSim.ChalParams` (field types), `chalRun`, `realView`, `idealView`, `altMsg`, `nmFin`, `nmOutL`,
`nmParams`, `simCt`, `simFin`, `simMsg`, `simOutL`, `simParams` (`rd*`/`fin*`/`finSt`→`r*`,
`chunkAt`→`coinBlock`, and inside `nmParams`/`simParams` the polynomial-time fields read from
`polyTimeComputable_rU`, `_rX`, `_rAns` instead of projections of `polyTimeComputable_rd`). All 24
are identical to the base after the name map (`bodies-cp2-modmap.txt`).

### 9.8 Name map (checkpoint 2)

The rows are appended to `evidence/census/namemap.tsv` ("checkpoint 2" block and its generated
auxiliaries). `-` marks a deleted declaration without a successor of its own: the `_eq` lemmas of
the deleted readers (their published successors have `_input`/`_finInput` lemmas instead; no use
needed them) and the bundle lemmas `fields_input`, `fields_finInput`, `polyTimeComputable_rd`,
`polyTimeComputable_finFields` (each use reads the published per-reader lemmas).

## 10. Checkpoint 3 — group E

### 10.1 At a glance

- E1, E2, E3: **done**; nothing escalated.
- **Build:** order unchanged from checkpoint 2 (`cp3/order-cp3.txt`). Sweep of positions 253–422
  from the first edited module (`Encryption/PublicKey/OracleSecurity`), 170/170
  (`cp3/sweep.tsv`); recheck of 281–422 after a docstring rewrap in `NMI/Forward.lean`, 142/142
  (`cp3/sweep2.tsv`).
- **Sorry census:** 45 in 24, as at the base (`cp3/sorry-census.txt`). **Lint:** 216 FAIL (the
  base's lines), 102 WARN (§9.1) (`cp3/lint-cp3.log`).
- **Census** (36 changed and new modules): REMOVED 110, ADDED 83, CHANGED 1 (the same generated
  matcher as before), REPOINTED 40, map check 0 bad, every removed name mapped
  (`cp3/census/census-diff-cp3.txt`).
- **Statements:** `decls2` 13 CHANGED, all the checkpoint-2 re-pointings (13/13 SAME-MODULO-MAP).
  Definition bodies: 24 re-pointings and the 2 intended E1 redefinitions (§10.2): `NMCCA2.logEmit`
  and `NMSim.chunkMap` (`cp3/statements/bodies-cp3-modmap.txt`).
- **Patch replay:** three patches, the branch's tree (`cp3/patch-replay.log`).

### 10.2 Items

**E1 — iterate and emit: done.**
- New, beside `relabelN` (`Games/Efficiency/OracleBridge.lean`, 321 → 410 lines, in namespace
  `TCSlib.Cryptography.Games` before the `EffFill` history translator):
  - `iterEmit step emit m x = (List.range m).flatMap fun i => emit (step^[i] x)`, with `iterEmit_eq`;
  - `length_iterate_le_add`: if one step never makes a word longer than `max |y| c`, the orbit stays
    within `|x| + c`;
  - `polyTimeComputable_iterEmit`: `fun x => iterEmit step emit (|x| + 1) x` is polynomial-time,
    from `Complexity.polyTimeComputable_iterateEmit` (read-only, used as is) with the orbit bound
    of `length_iterate_le_add`;
  - `iterEmit_encode`: on `enc l`, for an encoding whose step drops the first element and whose
    emission reads it, `m ≥ |l|` rounds emit `l.flatMap g` (from `flatMap_range_drop`, L1).
- **Instances** (definition bodies changed to the instance; types unchanged; definitional
  equality by unfolding `iterEmit`):
  - `NMCCA2.logEmit G L := iterEmit pairSndD G (|L| + 1) L`. `logEmit_eq` keeps its statement and
    now reads `iterEmit_eq` (not `rfl`: Rule 10); `polyTimeComputable_logEmit` and
    `logEmit_encodeLog` keep their statements and are corollaries of `polyTimeComputable_iterEmit`
    (`c = 0`) and `iterEmit_encode` (encoding `codec.encodeLog`). The private
    `length_iterate_pairSndD_le` and `iterate_pairSndD_encodeLog` are deleted (their content is
    `length_iterate_le_add` and the iterate step of `iterEmit_encode`); `length_le_length_encodeLog`
    stays.
  - `NMSim.chunkMap c f x := iterEmit (chunkStep c) (chunkEmit c f) (|x| + 1) x`. `chunkMap_eq`,
    `polyTimeComputable_chunkMap` and `chunkMap_flatten` keep their statements and are corollaries
    of `iterEmit_eq`, `polyTimeComputable_iterEmit` (`c = 2`, the private `length_chunkStep_le`)
    and `iterEmit_encode` (encoding `l ↦ ⟨ctx, l.flatten⟩`). The private
    `length_iterate_chunkStep_le` is deleted.
- **`relabelN` and `relabel` are kept** (they are the efficiency fill's T4 definitions, audited at
  Gate 10; `relabelN` also has a round-count argument of its own). Bridging equations, proved through
  `iterEmit_eq`: `EffFill.relabelN_eq_iterEmit : relabelN m w = iterEmit pairSndD relabelEmit m w`
  and `EffFill.relabel_eq_iterEmit : relabel x = iterEmit pairSndD relabelEmit (|x| + 1) x`.
  `bridgePre_poly` keeps its statement and is now a corollary of `polyTimeComputable_iterEmit`
  (its private orbit bound is gone). `relabelN_encodeHist` and `length_le_length_encodeHist` are
  unchanged (their statements are about `relabelN` with any `m ≥ |L|`). No foreign body was needed.
- **Further iterate-and-emit constructions found** (receipt E1-*), not folded: their round count
  is a polynomial other than `|x| + 1` or their definitions are in audited ch. 2–4 files:
  `BlockEncryptor.blockEncFun`, `decListFun`, `EnsembleLemmas.CopiesLoop`, `StretchMachine`'s
  `prgIter`, `CommitmentLemmas.ComLoop`, the ZK `EncodingMachines` counter loops. Also two public
  copies of one fact in ZK: `GI.iterate_pairSndD_encodeMsgs` (`GraphIsomorphism/EfficiencyRep.lean`)
  and `ColMachines.iterate_pairSndD_encodeMsgs` (`ThreeColoring/Machines.lean`) — new duplication,
  outside this unit's items.

**E2 — `polyTimeComputable_guessBit`: done.** `NMSim.polyTimeComputable_guessBit`
(`NMS/Recover.lean`) → `NMCCA2.polyTimeComputable_guessBit` (`NMI/Encrypt.lean`, after
`guessBit_eq`); the private `polyTimeComputable_guessFun` is now `polyTimeComputable_guessBit`
composed with the reader of `w`. Recover reaches it through its `open NMCCA2 (…)` list.

**E3 — done.** `NMSim.ctLen_pos` (`NMS/Recover.lean`) and `NMCCA2.indImpl_eq_of_msgLen_eq_zero`
(`NMI/Encrypt.lean`) → `FixedLengthPKScheme.ctLen_pos` and
`FixedLengthPKScheme.indImpl_eq_of_msgLen_eq_zero` (`Encryption/PublicKey/OracleSecurity.lean`,
723 → 765 lines, new subsection at the end of `FixedLengthPKScheme`; statements unchanged up to the
namespace, proofs unchanged, read through the published `_onSpec` equations). Uses:
`NMS/Recover`, `NMS/IndSim` (`S.ctLen_pos …`) and one proof line of the endpoint
`indSecure_cca2_of_nmSecure_cca2` in `NMI.lean` (`S.indImpl_eq_of_msgLen_eq_zero …`; header
unchanged).

### 10.3 Files changed at checkpoint 3 (base → checkpoint 3, lines)

| File | Lines |
|---|---|
| `Games/Efficiency/OracleBridge.lean` | 321 → 410 |
| `Encryption/PublicKey/OracleSecurity.lean` | 723 → 765 |
| `NMI.lean` | 655 → 647 |
| `NMI/Encrypt.lean` | 332 → 331 |
| `NMI/Forward.lean` | 350 → 140 |
| `NMS/Generic.lean` | 460 → 181 |
| `NMS/Recover.lean` | 519 → 495 |
| `NMS/IndSim.lean` | 293 → 294 |

No import changes at checkpoint 3 (`OracleBridge` reaches `Foundations/BitLists` through its
existing imports).

### 10.4 Name map (checkpoint 3)

| Old | New |
|---|---|
| `NMSim.polyTimeComputable_guessBit` | `NMCCA2.polyTimeComputable_guessBit` |
| `NMSim.ctLen_pos` | `FixedLengthPKScheme.ctLen_pos` |
| `NMCCA2.indImpl_eq_of_msgLen_eq_zero` | `FixedLengthPKScheme.indImpl_eq_of_msgLen_eq_zero` |
| (private) `NMCCA2.length_iterate_pairSndD_le`, `iterate_pairSndD_encodeLog` | — (`Games.length_iterate_le_add`, `Games.iterEmit_encode`) |
| (private) `NMSim.length_iterate_chunkStep_le` | — (`Games.length_iterate_le_add`) |

New: `Games.iterEmit`, `iterEmit_eq`, `length_iterate_le_add`, `polyTimeComputable_iterEmit`,
`iterEmit_encode`, `EffFill.relabelN_eq_iterEmit`, `EffFill.relabel_eq_iterEmit`.

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

## ===== briefs/pass-shelat-ch5-8/fills/dl-folds/issued-r1/brief.md =====

# Claude job · post-consolidation folds DL-36 and DL-37 (`dl-folds`)

**Issue base** `d3f2290a2c66f614e8807903b89ac595086578b3` on `cryptography/pass-shelat-ch2-4` (the merge of #298, the
DL-30–DL-34 consolidation). **Unit** `dl-folds`. **Worker** Claude (standing ruling, 2026-11-11). **Lean** 4.25.0 and
the Mathlib revision in that commit's `lake-manifest.json`.

This job repays two rows of `briefs/pass-shelat-ch5-8/duplication-ledger.md`. Read both rows, and DL-30 to DL-34 for
what the consolidation already did.
- **DL-36:** the copies left by the nm-cca2 fill.
- **DL-37:** the copies left by the nm-sim fill.

It also promotes the generic lemmas that the two fills' reviews accepted:
- the nm-cca2 review, `fills/nm-cca2/final-r1/review.md`, finding 4 and its promotion paragraph;
- the nm-sim review, `fills/nm-sim/final-r1/review.md`, § *Promotion requests*.

Seyoon's rulings (2026-11-13): this is **one job with three checkpoints**; R7 of the consolidation is closed as
no-fold (not in scope); the two `blocks` aliases are in scope (item B3).

The job is a **refactor with no mathematical change**:
- promote each generic lemma to its shared home;
- delete the copies;
- re-point every use.

No audited statement changes.

## Checkout and delivery

- Fetch `cryptography/pass-shelat-ch2-4`. Start a local branch `fill/dl-folds` at the exact issue base, and record
  the base in `REPORT.md`. Keep the branch local.
- Read `policy.md` (§1 file layout, Rule 10 and abbreviations; §3 docstrings), the attached environment addendum
  and `README.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/dl-folds/` on `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `src/`: every changed or new file;
  - `evidence/`, with a `SHA256SUMS` manifest (see *Evidence completeness*).
- Commit as `fill dl-folds: checkpoint N` and `fill dl-folds: final`.
- Pull with rebase before pushing, push only your delivery path, and never force-push. Campaign changes land by a
  maintainer PR for Seyoon's approval.

## The items

Paths are relative to `TCSlib/Cryptography/`. Line numbers are at the issue base. Abbreviations:
- `NMI/` = `Encryption/PublicKey/NonMalleability/Indistinguishability/`, and `NMI.lean` is its owned file;
- `NMS/` = `Encryption/PublicKey/NonMalleability/Simulation/`.

**Grep first.** For every item, search the whole library at the base for further copies under other names,
including private ones. List each copy you find, then fold it in or record why not. Two copies outside the ledger
are already known: the private `impl_of_query` (G2) and the second `take_drop_ofFn_blocks` (B2).

### G · the Games layer (checkpoint 1)

| Item | Now | Action |
|---|---|---|
| G1 | `NMSim.buildComp_budget_eq` (`NMS/Generic.lean:67`), `toCompOn_budget_eq` (`:101`), `buildComp_of_ret` (`NMS/Rounds.lean:146`) | Promote to `Games/Machines.lean`, with `buildComp_of_ret` beside the `buildComp_*_of_ret` lemmas, or to `Games/Efficiency/Replay.lean` beside `buildComp_of_replaysFrom`. |
| G2 | `NMSim.impl_of_ret` (`NMS/Rounds.lean:173`) beside the published `InteractiveHandler.impl_of_ret` (`Games/Efficiency.lean:620`); `NMSim.impl_of_query` (`Rounds.lean:198`) and the private `impl_of_query` (`Encryption/PrivateKey/OracleFromPRF/Handler.lean:421`); `NMSim.finish_of_ret` (`Rounds.lean:233`) | Delete `NMSim.impl_of_ret` and re-point its uses to `InteractiveHandler.impl_of_ret`. If its list form is a different statement, keep it as a corollary there. Promote `impl_of_query` and `finish_of_ret` beside `impl_of_ret`, and fold the private PRF copy. |
| G3 | `NMSim.expect_toCompOn_outLen` (`NMS/Generic.lean:151`) | Promote to `Games/Efficiency.lean`. |
| G4 | `NMSim.expect_congr_of_allOutputs` (`Generic.lean:118`), `bind_congr_of_allOutputs` (`:133`), `expect_expect_sample` (`:124`); `costBoundedBy_bind_of_allOutputs` (`NMS/Rounds.lean:296`), `simulate_costBoundedBy_once` (`:320`) | Promote:<br>• `expect_congr_of_allOutputs` → `Games/Hopping.lean`, beside `expect_mono_of_allOutputs`;<br>• `bind_congr_of_allOutputs` → `Games/OracleComp.lean`, beside `AllOutputs.bind`;<br>• `costBoundedBy_bind_of_allOutputs` → `Games/OracleComp.lean`, beside `CostBoundedBy.bind`;<br>• `expect_expect_sample` → `Games/Probability.lean`;<br>• `simulate_costBoundedBy_once` → `Games/Simulate.lean` or `Games/Hopping.lean`. |
| G5 | `NMSim.expect_simulate_eager` (`Generic.lean:193`), the general form of `ChallengeSim.expect_simulate_eager` (`Encryption/PublicKey/OracleSecurity/ChallengeSim.lean:146`) | Promote the general form to `Games/Hopping.lean`. Derive the ChallengeSim lemma from it, keeping its name and statement. |
| G6 | `NMSim.expect_eq_until_bad` (`Generic.lean:237`), the expectation form of `Games.prob_eq_until_bad` (`Games/Hopping.lean:208`) | Promote it beside `prob_eq_until_bad`, and re-derive that lemma's first conjunct from it, keeping its statement. |
| G7 | `NMCCA2.fwdHandler`, `fwdHandler_impl` (`NMI/Forward.lean:99`, `:133`); `exists_withAdviceOn` (`NMI/Decrypt.lean:330`); `cntRead`, `ansRead` and their `polyTimeComputable_*` (`Decrypt.lean:54–72`) | Promote:<br>• `fwdHandler`, `fwdHandler_impl` and `exists_withAdviceOn` → `Games/Efficiency.lean`, or a new sibling under `Games/Efficiency/` if the size limit requires;<br>• `cntRead` and `ansRead`, with their `polyTimeComputable_*` → `Games/BitCodec.lean`. |

### R · readers (checkpoint 2)

| Item | Now | Action |
|---|---|---|
| R1 | Finalization readers `NMCCA2.finU`, `finZ`, `finW`, `finA`, `finL`, with their `_eq`, `fields_finInput` and `polyTimeComputable_finFields` (`NMI/Forward.lean:204–250`); `NMSim.finSt` and its lemmas (`NMS/Simulator.lean:105`) | `finU`, `finZ`, `finW` and `finL` have the bodies of the published `InteractiveHandler.rU`, `rZ`, `rW` and `rL`, and `finSt` has the body of `rS` (`Games/Efficiency.lean:458–474`).<br>• Beside `InteractiveHandler.finInput` (`Games/Efficiency.lean:647`), add the readers on a finalization input: `rU_finInput`, `rZ_finInput`, `rW_finInput`, `rS_finInput` and `rL_finInput`.<br>• Publish `finA` as one new reader beside them, with its `_finInput` lemma and `polyTimeComputable_*`.<br>• Delete the copies and re-point every use: the private `dCnt`, `dCt`, `dIn` and `dFin` (`NMI/Decrypt.lean:104–120`); `eBit`, `eMsg`, `eTape` and `eCt` (`NMI/Encrypt.lean:56–71`); and the nm-sim finalization. |
| R2 | Round-input readers `NMSim.rdU`, `rdZ`, `rdW`, `rdState`, `rdIdx`, `rdQuery`, `rdLog` with their `_eq` (`NMS/Rounds.lean:51–92`); the private `rState`, `rIdx`, `rQuery` and `rLog` (`NMI/Forward.lean:54–60`) | These are `InteractiveHandler.rU`, `rZ`, `rW`, `rS`, `rI`, `rX` and `rL`. Delete the copies and re-point every use. |
| R3 | The answer reader `pairSndD (pairSndD (pairFstD (rL w)))`, in four copies:<br>• `NMSim.rdAns` (`Rounds.lean:94`);<br>• the private `rAns` (`NMI/Forward.lean:62`);<br>• the private `rFwd` (`Encryption/PublicKey/AdaptiveCPA/Handler.lean:168`);<br>• the private `rY` (`Encryption/PrivateKey/OracleFromPRF/Handler.lean:196`). | Publish one reader beside `rL`, with a formula docstring and `polyTimeComputable_*`. Re-point all four. |

### B · blocks (checkpoint 2)

| Item | Now | Action |
|---|---|---|
| B1 | `NMSim.chunkAt`, `chunkAt_eq`, `length_chunkAt` (`NMS/Hybrid.lean:364–370`) | Fold them onto `coinBlock`, `coinBlock_eq` and `length_coinBlock` (`Asymptotic/Adversary.lean:89–95`). There are about 58 uses. |
| B2 | The block lemmas `ofFn_block` (`NMS/Hybrid.lean:448`), `chunkAt_flatten_append` (`:405`) and `map_chunkAt_flatten` (`:429`); Lamport's `coinBlock_flatten` (`Authentication/Signatures/Lamport.lean:96`); the block-window facts `OneWay.ofFn_block_eq_take_drop` (`Asymptotic/OneWayLemmas.lean:78`), `NMCCA2.ofFn_nthCt` (`NMI.lean:214`), `EnsembleLemmas.take_drop_ofFn_blocks` (`Asymptotic/EnsemblesLemmas.lean:395`) and the restated `take_drop_ofFn_blocks` (`Encryption/PrivateKey/FromPRF/ReductionMachine.lean:222`) | • Place the block lemmas beside `coinBlock`, folding `coinBlock_flatten` if it is the same fact.<br>• Prove one block-window lemma there, or reuse `FunFamily.ofFn_blocks`.<br>• Delete exact copies.<br>• Keep each public statement that has other uses, or that a gate audited, and derive it as a corollary with an unchanged statement. |
| B3 | The `blocks` aliases of `FunFamily.blocks`:<br>• the public `EnsembleLemmas.blocks`, `blocks_eq`, `blocks_apply` and `blocks_symm_apply` (`Asymptotic/EnsemblesLemmas.lean:369–386`);<br>• the private `blocks` and `blocks_eq` in `Asymptotic/Ensembles.lean:214`. | Fold each alias onto `FunFamily.blocks` (and its `_apply` lemmas) **only if** no audited statement changes. For a theorem, that means its header; for a definition, its type and body.<br>• List every declaration whose statement mentions the alias.<br>• If folding would change one, keep the alias and escalate it with that list. The Ensembles alias is documented as kept for `Ensemble.copies`. |

### L · lists, codecs and coins (checkpoint 2)

| Item | Now | Action |
|---|---|---|
| L1 | The private `flatMap_range_drop` in `NMS/Generic.lean:382` and in `NMI/Forward.lean:303`; `NMSim.ofFn_natAdd_eq_drop` (`NMS/Hybrid.lean:467`), `decide_map_ofFn` (`:482`) and `length_flatten_map_const` (`:396`); `ofFn_eq_map_range` in `NMS/Hybrid.lean:473`, `ZeroKnowledge/ThreeColoring/Machines.lean:919` and `ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean:67` | Promote one of each to `Foundations/BitLists.lean`. Use Mathlib where it already has the fact; `length_flatten_map_const` is `List.length_flatten` plus a constant sum. Delete the copies, both ZK copies included. |
| L2 | `NMSim.padFin_append_split` (`NMS/Rounds.lean:155`) | Promote beside `padFin` (`Games/BitCodec.lean`). |
| L3 | `NMSim.seedEquiv`, `seedEquivPoly` (`NMS/Rounds.lean:250`, `:264`) | Promote to `Asymptotic/EnsemblesLemmas.lean`, beside `coinsEquiv`. That file is 865 lines; keep it under 1000. |
| L4 | `NMSim.ofFn_padFin_eq_padL` (`NMS/Rounds.lean:283`) beside `EnsembleLemmas.ofFn_padFin_eq_padL` (`Asymptotic/EnsemblesLemmas.lean:167`) | If the statements agree up to names, delete the copy and re-point. Otherwise derive the copy from the A4 lemma. |

### E · iterate-and-emit, and the NM leftovers (checkpoint 3)

| Item | Now | Action |
|---|---|---|
| E1 | Three iterate-and-emit constructions:<br>• `Games.EffFill.relabelN` and `relabel` (`Games/Efficiency/OracleBridge.lean:62`, `:71`), with `relabelN_encodeHist` (`:119`), `length_le_length_encodeHist` (`:134`) and the orbit bound inside `bridgePre_poly` (`:168`);<br>• `NMCCA2.logEmit` (`NMI/Forward.lean:259`), with `polyTimeComputable_logEmit` (`:278`), `logEmit_encodeLog` (`:339`) and the private `length_iterate_pairSndD_le` (`:267`), `iterate_pairSndD_encodeLog` (`:289`) and `length_le_length_encodeLog` (`:325`);<br>• `NMSim.chunkStep`, `chunkEmit`, `chunkMap`, `polyTimeComputable_chunkMap` and `chunkMap_flatten` (`NMS/Generic.lean:287–409`). | • Define one generic iterate-and-emit construction beside `relabelN`, with its polynomial-time lemma. It uses `Complexity.polyTimeComputable_iterateEmit` (`TCSlib/Complexity/Randomized/Repetition.lean:351`), which is read-only for this job.<br>• Make `logEmit` and `chunkMap` instances of it, and their lemmas corollaries of its generic facts.<br>• For `relabelN` and `relabel`: redefine them as instances only if their types and every audited statement that mentions them stay unchanged. Otherwise keep their definitions and prove a bridging equation `relabel x = …` through published readers.<br>• Escalate if the bridge needs a foreign body. |
| E2 | `NMSim.polyTimeComputable_guessBit` (`NMS/Recover.lean:53`), whose content the private `polyTimeComputable_guessFun` (`NMI/Encrypt.lean:263`) re-proves | Promote it to `NMI/Encrypt.lean` beside `guessBit`'s use, and make the private lemma use it or delete it. |
| E3 | `NMSim.ctLen_pos` (`NMS/Recover.lean:278`) and `NMCCA2.indImpl_eq_of_msgLen_eq_zero` (`NMI/Encrypt.lean:318`) | Promote both to `Encryption/PublicKey/OracleSecurity.lean`, which is 723 lines after the consolidation's split. |

**Not promoted (review decisions):** `length_ofFn_coins` and the private `lin_*` stay local.

## Rules

- **No statement changes.**
  - No existing declaration other than the listed copies may change its statement, name, attributes or
    visibility.
  - The exceptions are the listed publications and the promoted lemmas, which get their new names.
  - Every other proof stays unchanged except for re-pointed names.
  - Each gate-audited theorem keeps its statement byte for byte. That includes the endpoints below and every
    theorem of the NM files that Gates 06, 18 and 19 audited.
  - A definition's body may change only from a private reader to a published reader with the same body, as R6 of
    the consolidation did. Record each such change.
- **Deleting copies.** Delete them; leave no deprecated aliases (precedent: #192). Re-point every use in the
  library, `audits/` included.
- **Names.** Choose names in the home namespace. The report's census maps every old name to its new name.
- **Docstrings.**
  - Public promoted lemmas keep or gain a formula docstring, and a proof sketch when nontrivial (policy §3).
  - Update every module docstring's `## Contents`, `## Main definitions` or `## Main results` that names a moved
    declaration.
- **Imports.**
  - You may add imports to consumer files.
  - An import added to an existing Games, Asymptotic or Foundations module must be acyclic, and listed in the
    report with its reason.
  - Do not import a downstream module to reach a lemma.
- **Rule 10.** A promoted lemma may read definitions in two ways only:
  - through their bodies, for definitions of its new home file;
  - through published readers, for other files' definitions.

  Where a proof read its old file's definitions, rewrite it through readers or escalate. Generated matchers and
  projections count.
- **Simp.** Add no `@[simp]` and do not change global simp sets.
- **Size.** Keep every file below 1000 lines. You may create a new module under `Games/Efficiency/`, `Games/` or
  `Foundations/` to stay below that limit. Give it a module docstring and add it to its facade.
- **Out of scope.**
  - Every file outside `TCSlib/Cryptography/`, except uses in `audits/`. `Complexity/Randomized/Repetition.lean`
    is read-only.
  - Notably the Arora–Barak files and other campaigns' files.
  - R7 (the length vectors): closed as no-fold.
  - DL-35 (inherited ch. 2–4).
- **Escalation.** An item may not be foldable without a Rule-10 violation, an import cycle or a statement change.
  If so:
  - leave it as it is;
  - record the exact obstruction and the smallest correction;
  - continue with the other items.

  A checkpoint must still compile.

## Checkpoints

1. Group G.
2. Groups R, B, L.
3. Group E.

Send the final delivery with full evidence.

## Checks and report

- **Bootstrap and sweep.** Bootstrap from `order.txt` (421 modules) and the narrow `roots.txt` (112), following the
  addendum. Check one module per `scripts/lean_check_tree.sh` call, with one Lean process per olean tree. Insert any
  new module before its first consumer, and recompute the order if imports change.
  - At each checkpoint, rebuild every edited module and everything after it in the order.
  - At the final delivery, run a full fresh sweep with 0 errors.
  - Compare the `sorry` warnings with `base-sorries.txt`. There must be **no change**: 45 declarations in 24
    modules.
- **Census.** Compare all declarations of the changed files, base against final, by name, type and attributes.
  Report:
  - removed: the listed copies only;
  - added: the promoted lemmas, readers and any new module;
  - changed: expected 0, apart from listed visibility changes;
  - the old → new name map, **complete** (the consolidation's map missed two rows).
- **Statement check.** Run a textual header comparison over every changed file (decls2, or an equivalent):
  - 0 CHANGED headers;
  - every audited endpoint byte-identical.
- **Axioms.** Print the axioms of:
  - every stored constant of every changed or new file;
  - the campaign endpoints:
    - `prfFixedScheme_cpa`, `prfFixedScheme_cca1`, `not_prfFixedScheme_cca2`, `prfFixedScheme_not_cca2`;
    - `INDSecure.adaptive_cpa`;
    - `SingleBitSecure.bitwise_padded_cpa`, `exists_adaptive_cpa` and `padded_cpa`;
    - both `Implications.PublicKey` entries;
    - `nmSecure_cca2_of_indSecure_cca2`, `indSecure_cca2_of_nmSecure_cca2` and `indSecure_cca2_iff_nmSecure_cca2`;
    - `nmSecure_of_simNMSecure`, `simNMSecure_of_nmSecure_cpa` and `simNMSecure_cpa_iff_nmSecure_cpa`.

  Expect only `propext`, `Classical.choice` and `Quot.sound`, as at the base. List any constant whose axioms
  changed.
- **Rule 10 evidence.**
  - Run whole-file seals A and B of every changed or new file over its full TCSlib import closure, at base and
    final. Report each failing declaration, and confirm there is no new one.
  - Add paired controls that pass unsealed and fail sealed, each sealed negative failing exactly once.
  - Run the explicit-unfold scan of every changed file.
  - Report the seals with `PolyExpr.eval` both sealed and unsealed (Gate 17's remark).
- **Lint.** Run `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b`. Allow no new FAIL
  versus the base.
- **Grep receipts.** For each item, give the search you ran for further copies, and its hits.
- **Report.** Give:
  - the base;
  - each item's disposition: done, not a copy, or escalated;
  - the changed and new files, with line counts;
  - the import changes;
  - the census and the name map;
  - the evidence;
  - any new duplication you found.

### Evidence completeness

Gate 20 held the consolidation for omitted raw evidence (G20-01).
- Every file that `evidence/SHA256SUMS` names must be in the delivery. That includes:
  - seal and control sources, manifests and request records;
  - every raw log and `results.jsonl`;
  - the census and collector runs;
  - the probe sources and the tools used.
- If the evidence is too large for one commit, deliver it in several commits, or as numbered ZIP parts, each part
  with an entry list. Do not leave anything out for size.
- Check before delivery that the delivered paths are exactly the manifest's paths.

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
| DL-36 | nm-cca2 fill (delivery review 2026-11-12): `NMCCA2.logEmit` (`PublicKey/NonMalleability/Indistinguishability/Forward.lean`) generalizes `Games.EffFill.relabelN`/`relabel` (`Games/Efficiency/OracleBridge.lean`), and its log facts `logEmit_encodeLog`, `iterate_pairSndD_encodeLog`, `flatMap_range_drop`, `length_le_length_encodeLog`, `length_iterate_pairSndD_le`, `polyTimeComputable_logEmit` mirror `relabelN_encodeHist`, `length_le_length_encodeHist` and the orbit bound of `bridgePre_poly` (undisclosed); public `finU`, `finZ`, `finW`, `finA`, `finL`, `fields_finInput` are the DL-34 round-input readers (`rU`…`rL`) again; `ofFn_nthCt` (owned file) is DL-34's generic block fact (`ofFn_acTapes`, `ofFn_pkTapes`); the private readers `rState`…`rAns` (disclosed). Promotion requests: `fwdHandler`/`fwdHandler_impl`, `exists_withAdviceOn` (→ `Games/Efficiency`), `cntRead`/`ansRead` (→ `BitCodec`), `indImpl_eq_of_msgLen_eq_zero` (→ `PublicKey/OracleSecurity`, after that file is split: it is at 999 lines). | several | Open (job `dl-folds` staged 2026-11-13) | After the DL-30–DL-34 consolidation lands: put `logEmit` beside `relabelN` with `relabel x = logEmit relabelEmit x`; re-point `dCnt`/`dCt`/`dIn`/`dFin`/`eBit`/`eMsg`/`eTape`/`eCt` to R6's readers and delete `finU`…`fields_finInput`; derive `ofFn_nthCt` from the generic block lemma; promote the accepted requests. |
| DL-37 | nm-sim fill (delivery review 2026-11-13; **undisclosed**, accepted as debt by Seyoon 2026-11-13): `NMSim.chunkAt`/`chunkAt_eq`/`length_chunkAt` (`PublicKey/NonMalleability/Simulation/Hybrid.lean`) and the block lemmas `ofFn_block`, `chunkAt_flatten_append`, `map_chunkAt_flatten`; private `padFin_replicate_false` (`Simulation/Challenge.lean`); `Rounds.impl_of_ret`, `rdU`…`rdLog`/`rdState`, `rdAns`, `Simulator.finSt` (`Simulation/Rounds.lean`, `Simulator.lean`); also generic neighbours `expect_eq_until_bad`, `NMSim.expect_simulate_eager`, `expect_congr_of_allOutputs`, `chunkMap`; disclosed: `flatMap_range_drop`, `ofFn_padFin_eq_padL`, `polyTimeComputable_guessBit`, `ofFn_eq_map_range` | `coinBlock`/`coinBlock_eq`/`length_coinBlock` (`Asymptotic/Adversary.lean`), `OneWayLemmas.ofFn_block_eq_take_drop`, `NMCCA2.ofFn_nthCt`, Lamport `coinBlock_flatten`; `PRFGame.padFin_replicate_false` (`OracleFromPRF/Transfer.lean`; → `Games.padFin_replicate_false` in the consolidation); DL-34 private `impl_of_ret` (`AdaptiveCPA/Handler.lean`, `PRFGame`) and readers `rU`…`rL`/`rS`; `Games.prob_eq_until_bad`, `BitwiseSim.expect_simulate_eager`, `ProbComp.expect_mono_of_allOutputs`, `relabelN`/`logEmit` (DL-36); ZK `ofFn_eq_map_range` ×2; A4 `EnsembleLemmas.ofFn_padFin_eq_padL`; `rFwd`/`rY`/Forward `rAns` | Open (job `dl-folds` staged 2026-11-13; first item paid at the consolidation landing, LE-repoint-nmsim `6f853adc`) | Landing of the consolidation (after nm-sim): delete the private `padFin_replicate_false` and use `Games.padFin_replicate_false`; re-point the nm-sim files to the moved names. Post-consolidation fold window, with DL-36: fold `chunkAt` onto `coinBlock` (58 uses) and place the block lemmas beside it; re-point `rdU`…`rdLog`, `rdState`, `finSt` to `InteractiveHandler.rU`…`rS` and `impl_of_ret` to `InteractiveHandler.impl_of_ret`; derive `prob_eq_until_bad` and `ChallengeSim.expect_simulate_eager` from the general nm-sim forms; one iterate-and-emit definition for `relabelN`/`logEmit`/`chunkMap`; merge the three `ofFn_eq_map_range` into `Foundations/BitLists`; make `NMSim.ofFn_padFin_eq_padL` the A4 lemma; fold `rdAns` with the `rFwd`/`rY`/`rAns` readers; promote the accepted requests (review r1 table). |
| DL-38 | dl-folds fill (worker REPORT §0.6, disclosed; delivery review 2026-11-14): inline re-proofs of `impl_of_query` (`acHandler_impl_forward`) and of a returning finalization (`pkHandler_finish`, `acHandler_finish`); a local `have` equal to `polyTimeComputable_ansRead` (`OracleFromPRF.lean`); further block-window restatements (`Primality.ofFn_chunk`, `ColRep.drop_take_ofFn_blockRead`, `Factoring.fac_ofFn_halves`, already corollaries); other iterate-and-emit loops (`BlockEncryptor`, `EnsembleLemmas.CopiesLoop`, `StretchMachine`, `CommitmentLemmas.ComLoop`, ZK `EncodingMachines`); the ZK pair `GI.iterate_pairSndD_encodeMsgs` / `ColMachines.iterate_pairSndD_encodeMsgs`; and the B3 `blocks` aliases (`EnsembleLemmas.blocks` and its lemmas, private `Ensembles.blocks`), escalated. | `InteractiveHandler.impl_of_query`, `finish_of_ret`; `Games.polyTimeComputable_ansRead`; `FunFamily.ofFn_blocks`; `Games.iterEmit`; `FunFamily.blocks` | Open (deferred) | Opportunistic: fold each when its file is next touched. The B3 aliases need a gate-approved restatement of `exists_copiesRed`, `ofFn_blocks_symm`, `take_drop_ofFn_blocks`, `ComLoop.emit_init_of_lt` and of the bodies of `PRFGame.pkTapes`, `Ensemble.copies` (all definitionally equal). Complexity copies of `ofFn_eq_map_range` and `flatMap_range_drop` are another campaign's. |

## ===== briefs/pass-shelat-ch5-8/gates/21-dl-folds/pr.diff.txt =====

diff --git a/TCSlib/Cryptography/Asymptotic/Adversary.lean b/TCSlib/Cryptography/Asymptotic/Adversary.lean
index 4f1e84a21..e2018d8af 100644
--- a/TCSlib/Cryptography/Asymptotic/Adversary.lean
+++ b/TCSlib/Cryptography/Asymptotic/Adversary.lean
@@ -6,6 +6,7 @@ Authors: TCSlib contributors
 import TCSlib.Complexity.Randomized.PPT
 import TCSlib.Cryptography.Foundations.Experiments
 import TCSlib.Cryptography.HardcoreBit.Basic
+import TCSlib.Cryptography.Foundations.BitLists
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
@@ -59,7 +60,9 @@ by `ifEq`).
 ## Main results
 
 * `TCSlib.Cryptography.coinBlock_eq`, `TCSlib.Cryptography.length_coinBlock` — the segment
-  equation and its full-length condition.
+  equation and its full-length condition; `coinBlock_flatten`, `map_coinBlock_flatten`,
+  `coinBlock_flatten_append` — the segments of a concatenation of equal-length blocks;
+  `ofFn_block_eq_coinBlock` — block `i` of a string of blocks and a tail is segment `i`.
 * `TCSlib.Cryptography.decodeFin_ofFn`, `TCSlib.Cryptography.padFin_ofFn` — decoding and
   padding invert `List.ofFn`; `TCSlib.Cryptography.decodeFin_eq_some_iff` — decoding succeeds
   exactly on the encoding; `TCSlib.Cryptography.ofFn_padFin_of_length` — padding a string of the
@@ -98,6 +101,58 @@ theorem length_coinBlock {B i : ℕ} {r : List Bool} (h : (i + 1) * B ≤ r.leng
   rw [Nat.add_mul, Nat.one_mul] at h
   omega
 
+/-- **The blocks of a concatenation of `B`-bit blocks:** if every block of `l` has `B` bits,
+segment `i < |l|` of `l.flatten` is `l[i]`.
+
+**Proof sketch.** Induction on `l`: segment `0` is the first block (`List.take_left'`), and
+segment `i + 1` drops the first block (`List.drop_append`) and is segment `i` of the rest. -/
+theorem coinBlock_flatten {B : ℕ} : ∀ (l : List (List Bool)), (∀ c ∈ l, c.length = B) →
+    ∀ (i : ℕ) (hi : i < l.length), coinBlock B i l.flatten = l[i]
+  | [], _, _, hi => by simp at hi
+  | c :: cs, hl, 0, _ => by
+    have hc : c.length = B := hl c (by simp)
+    simp [coinBlock_eq, ← hc]
+  | c :: cs, hl, i + 1, hi => by
+    have hc : c.length = B := hl c (by simp)
+    have hrest := coinBlock_flatten cs (fun d hd => hl d (by simp [hd])) i (by simpa using hi)
+    simp only [List.getElem_cons_succ, ← hrest, coinBlock_eq, List.flatten_cons]
+    rw [show (i + 1) * B = c.length + i * B by rw [hc, Nat.succ_mul]; ring, List.drop_append,
+      List.drop_eq_nil_of_le (by omega), List.nil_append, Nat.add_sub_cancel_left]
+
+/-- **The blocks of a concatenation, mapped:** if every block of `cs` has `k` bits, mapping `F`
+over the segments `coinBlock k i cs.flatten` for `i < |cs|` is mapping `F` over `cs`
+(`coinBlock_flatten`, entry by entry). -/
+theorem map_coinBlock_flatten {α : Type} (k : ℕ) (F : List Bool → α) :
+    ∀ cs : List (List Bool), (∀ c ∈ cs, c.length = k) →
+      (List.range cs.length).map (fun i => F (coinBlock k i cs.flatten)) = cs.map F := by
+  intro cs hc
+  refine List.ext_getElem (by rw [List.length_map, List.length_range, List.length_map])
+    fun i h₁ h₂ => ?_
+  rw [List.getElem_map, List.getElem_range, List.getElem_map,
+    coinBlock_flatten cs hc i (by rw [List.length_map, List.length_range] at h₁; exact h₁)]
+
+/-- **Reading back the blocks before a tail:** if `g 0, …, g (r-1)` have `k` bits each, segment
+`i < r` of `g 0 ++ ⋯ ++ g (r-1) ++ t` is `g i`.
+
+**Proof sketch.** Induction on `r`: for `i < r` the last block and the tail form the new tail;
+for `i = r` the segment starts right after the first `r·k` bits (`length_flatten_map_range`). -/
+theorem coinBlock_flatten_append (k r : ℕ) (g : ℕ → List Bool) (hg : ∀ i < r, (g i).length = k)
+    (t : List Bool) (i : ℕ) (hi : i < r) :
+    coinBlock k i (((List.range r).map g).flatten ++ t) = g i := by
+  induction r generalizing t with
+  | zero => exact absurd hi (Nat.not_lt_zero _)
+  | succ r ih =>
+    rw [List.range_succ, List.map_append, List.flatten_append, List.map_singleton,
+      List.flatten_singleton, List.append_assoc]
+    by_cases h : i < r
+    · exact ih (fun j hj => hg j (by omega)) _ h
+    · have hir : i = r := by omega
+      subst hir
+      rw [coinBlock_eq, List.drop_append_of_le_length (by
+          rw [length_flatten_map_range k i g fun j hj => hg j (by omega)]),
+        List.drop_of_length_le (by rw [length_flatten_map_range k i g fun j hj => hg j (by omega)]),
+        List.nil_append, List.take_left' (hg i (by omega))]
+
 /-- Decode a string as an `ℓ`-bit string: `some` of its bits if the length is exactly `ℓ`,
 `none` otherwise (a wrong-length answer of an inverter is a failure, D5). -/
 def decodeFin (ℓ : ℕ) (w : List Bool) : Option (Fin ℓ → Bool) :=
@@ -237,6 +292,30 @@ theorem FunFamily.ofFn_blocks (q ℓ : ℕ) (ω : Fin (q * ℓ) → Bool) (j : F
     rw [Nat.mul_comm]
     omega
 
+/-- **Block `i` of a string of `r` blocks of `k` bits and a tail** is segment `i`:
+`⟦j ↦ w (castAdd sl (finProdFinEquiv (i, j)))⟧ = coinBlock k i ⟦w⟧`.
+
+**Proof sketch.** The block is block `i` of the first `r·k` bits (`FunFamily.blocks_apply`),
+whose word is the window `(⟦w⟧.take (r·k)).drop (i·k)).take k` (`FunFamily.ofFn_blocks`,
+`List.ofFn_add`); the tail does not reach the window since `i·k + k ≤ r·k`. -/
+theorem ofFn_block_eq_coinBlock {r k sl : ℕ} (w : Fin (r * k + sl) → Bool) (i : Fin r) :
+    List.ofFn (fun j : Fin k => w (Fin.castAdd sl (finProdFinEquiv (i, j)))) =
+      coinBlock k i (List.ofFn w) := by
+  have hle : (i : ℕ) * k + k ≤ r * k := by
+    have := Nat.mul_le_mul_right k (Nat.succ_le_of_lt i.isLt)
+    rw [Nat.succ_mul] at this
+    exact this
+  have hblk : (fun j : Fin k => w (Fin.castAdd sl (finProdFinEquiv (i, j)))) =
+      FunFamily.blocks r k (fun p => w (Fin.castAdd sl p)) i :=
+    funext fun j => (FunFamily.blocks_apply r k (fun p => w (Fin.castAdd sl p)) i j).symm
+  have hx : (List.ofFn fun p : Fin (r * k) => w (Fin.castAdd sl p)).length = r * k :=
+    List.length_ofFn
+  have hw : List.ofFn w = List.ofFn (fun p : Fin (r * k) => w (Fin.castAdd sl p)) ++
+      List.ofFn (fun j : Fin sl => w (Fin.natAdd (r * k) j)) := List.ofFn_add
+  rw [hblk, FunFamily.ofFn_blocks, coinBlock_eq, hw,
+    List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by
+      rw [List.length_drop]; omega)]
+
 /-- `A(1^n, y)` as an inverter: output decoded as an `ℓ`-bit string, wrong length = failure
 [PS10, Definitions 27.3 and 28.4, the experiment `f(A(1^n, y)) = y`].
 
diff --git a/TCSlib/Cryptography/Asymptotic/EnsemblesLemmas.lean b/TCSlib/Cryptography/Asymptotic/EnsemblesLemmas.lean
index 710088b0d..a0de8e3a2 100644
--- a/TCSlib/Cryptography/Asymptotic/EnsemblesLemmas.lean
+++ b/TCSlib/Cryptography/Asymptotic/EnsemblesLemmas.lean
@@ -33,6 +33,9 @@ part of the public API of the campaign.
 * `TCSlib.Cryptography.EnsembleLemmas.coinsEquiv` — the coin-splitting bijection
   `{0,1}^a × {0,1}^b ≃ {0,1}^m` for `m = a + b` (`Fin.appendEquiv` transported along the
   length equation).
+* `TCSlib.Cryptography.EnsembleLemmas.seedEquiv`, `seedEquivPoly` — seeds made of two machines'
+  coins, or of a machine's coins and a string (`seedEquiv_ofFn`, `seedEquivPoly_ofFn`: the seed
+  is the concatenation).
 * `TCSlib.Cryptography.EnsembleLemmas.padL` — the padded/truncated string `padFin` as a list.
 * `TCSlib.Cryptography.EnsembleLemmas.blocks` — the blockwise bijection
   `{0,1}^{q·ℓ} ≃ ({0,1}^ℓ)^q` (an alias of `FunFamily.blocks`, `Asymptotic/Adversary.lean`).
@@ -154,6 +157,34 @@ theorem drop_ofFn_coinsEquiv {m a b : ℕ} (h : m = a + b) (c : (Fin a → Bool)
     (List.ofFn (coinsEquiv h c)).drop a = List.ofFn c.2 := by
   rw [ofFn_coinsEquiv, List.drop_left' List.length_ofFn]
 
+/-- **A seed of two machines' coins:** for `L = A.coins + B.coins`,
+`A.Coins n × B.Coins n ≃ {0,1}^{L(n)}`, concatenating the two coin strings (`seedEquiv_ofFn`). -/
+def seedEquiv {A B : NUPPT} {L : PolyExpr} (h : L = A.coins.add B.coins) (n : ℕ) :
+    A.Coins n × B.Coins n ≃ (Fin (L.eval n) → Bool) :=
+  ((NUPPT.coinsEquivPoly rfl n).prodCongr (NUPPT.coinsEquivPoly rfl n)).trans
+    (coinsEquiv (by rw [h, PolyExpr.eval_add]))
+
+/-- The seed is the concatenation of the coins: `⟦seedEquiv h n (r₁, r₂)⟧ = ⟦r₁⟧ ++ ⟦r₂⟧`. -/
+theorem seedEquiv_ofFn {A B : NUPPT} {L : PolyExpr} (h : L = A.coins.add B.coins) (n : ℕ)
+    (c : A.Coins n × B.Coins n) :
+    List.ofFn (seedEquiv h n c) = List.ofFn c.1 ++ List.ofFn c.2 := by
+  rw [seedEquiv, Equiv.trans_apply, ofFn_coinsEquiv, Equiv.prodCongr_apply,
+    Prod.map_fst, Prod.map_snd, NUPPT.coinsEquivPoly_ofFn, NUPPT.coinsEquivPoly_ofFn]
+
+/-- **A seed of a machine's coins and a string:** for `L = A.coins + L₂`,
+`A.Coins n × {0,1}^{L₂(n)} ≃ {0,1}^{L(n)}`, concatenating (`seedEquivPoly_ofFn`). -/
+def seedEquivPoly {A : NUPPT} {L L₂ : PolyExpr} (h : L = A.coins.add L₂) (n : ℕ) :
+    A.Coins n × (Fin (L₂.eval n) → Bool) ≃ (Fin (L.eval n) → Bool) :=
+  ((NUPPT.coinsEquivPoly rfl n).prodCongr (Equiv.refl _)).trans
+    (coinsEquiv (by rw [h, PolyExpr.eval_add]))
+
+/-- The seed is the concatenation: `⟦seedEquivPoly h n (r, w)⟧ = ⟦r⟧ ++ ⟦w⟧`. -/
+theorem seedEquivPoly_ofFn {A : NUPPT} {L L₂ : PolyExpr} (h : L = A.coins.add L₂) (n : ℕ)
+    (c : A.Coins n × (Fin (L₂.eval n) → Bool)) :
+    List.ofFn (seedEquivPoly h n c) = List.ofFn c.1 ++ List.ofFn c.2 := by
+  rw [seedEquivPoly, Equiv.trans_apply, ofFn_coinsEquiv, Equiv.prodCongr_apply,
+    Prod.map_fst, Prod.map_snd, NUPPT.coinsEquivPoly_ofFn, Equiv.refl_apply]
+
 /-! ### Padding as an FP function -/
 
 /-- The padded/truncated string of `padFin` as a list: exactly `k` bits, the bits of `a`
@@ -391,20 +422,11 @@ theorem finProdFinEquiv_symm_mk {q ℓ : ℕ} (i : Fin q) (j : Fin ℓ) (h : i *
   simp [finProdFinEquiv_apply_val]
   ring
 
-/-- The `i`-th chunk of `s` bits of the string of a `q·s`-bit word is its block `i`. -/
+/-- The `i`-th chunk of `s` bits of the string of a `q·s`-bit word is its block `i`
+(`FunFamily.ofFn_blocks`, the block window, through `blocks_eq`). -/
 theorem take_drop_ofFn_blocks {q s : ℕ} (w : Fin (q * s) → Bool) (i : ℕ) (hi : i < q) :
     ((List.ofFn w).drop (i * s)).take s = List.ofFn (blocks q s w ⟨i, hi⟩) := by
-  have hle : i * s + s ≤ q * s := by
-    rw [← Nat.succ_mul]
-    exact Nat.mul_le_mul_right s hi
-  refine List.ext_getElem ?_ fun j h₁ h₂ => ?_
-  · simp only [List.length_take, List.length_drop, List.length_ofFn]
-    omega
-  · simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn, blocks_apply]
-    congr 1
-    ext
-    simp [finProdFinEquiv_apply_val]
-    ring
+  rw [blocks_eq, FunFamily.ofFn_blocks]
 
 /-- The string of `(blocks q ℓ).symm V` is the concatenation of the `q` block strings
 (`List.ofFn_mul`). -/
diff --git a/TCSlib/Cryptography/Authentication/Signatures/Lamport.lean b/TCSlib/Cryptography/Authentication/Signatures/Lamport.lean
index ade832e58..2f4b0795f 100644
--- a/TCSlib/Cryptography/Authentication/Signatures/Lamport.lean
+++ b/TCSlib/Cryptography/Authentication/Signatures/Lamport.lean
@@ -92,20 +92,6 @@ theorem length_flatten_ofFn {B : ℕ} : ∀ {q : ℕ} (g : Fin q → List Bool),
       length_flatten_ofFn (fun i => g i.succ) (fun i => hg i.succ), Nat.succ_mul]
     omega
 
-/-- Segment `i` of a concatenation of `B`-bit blocks is block `i`. -/
-theorem coinBlock_flatten {B : ℕ} : ∀ (l : List (List Bool)), (∀ c ∈ l, c.length = B) →
-    ∀ (i : ℕ) (hi : i < l.length), coinBlock B i l.flatten = l[i]
-  | [], _, _, hi => by simp at hi
-  | c :: cs, hl, 0, _ => by
-    have hc : c.length = B := hl c (by simp)
-    simp [coinBlock_eq, ← hc]
-  | c :: cs, hl, i + 1, hi => by
-    have hc : c.length = B := hl c (by simp)
-    have hrest := coinBlock_flatten cs (fun d hd => hl d (by simp [hd])) i (by simpa using hi)
-    simp only [List.getElem_cons_succ, ← hrest, coinBlock_eq, List.flatten_cons]
-    rw [show (i + 1) * B = c.length + i * B by rw [hc, Nat.succ_mul]; ring, List.drop_append,
-      List.drop_eq_nil_of_le (by omega), List.nil_append, Nat.add_sub_cancel_left]
-
 /-- Segment `i` of the concatenation of `B`-bit blocks `g 0, …, g (q − 1)` is `g i`. -/
 theorem coinBlock_flatten_ofFn {q B : ℕ} (g : Fin q → List Bool) (hg : ∀ i, (g i).length = B)
     (i : Fin q) : coinBlock B i (List.ofFn g).flatten = g i := by
diff --git a/TCSlib/Cryptography/Encryption/PrivateKey/FromPRF/ReductionMachine.lean b/TCSlib/Cryptography/Encryption/PrivateKey/FromPRF/ReductionMachine.lean
index 654d5c5d6..11f31f81a 100644
--- a/TCSlib/Cryptography/Encryption/PrivateKey/FromPRF/ReductionMachine.lean
+++ b/TCSlib/Cryptography/Encryption/PrivateKey/FromPRF/ReductionMachine.lean
@@ -217,11 +217,10 @@ theorem zipWith_xor_flatten_ofFn : ∀ {k : ℕ} (F G : Fin k → List Bool),
       zipWith_xor_flatten_ofFn (fun j => F j.succ) (fun j => G j.succ) fun j => h j.succ]
 
 /-- A string of `q·s` bits read as `q` chunks of `s` bits: chunk `i` is block `i` of
-`FunFamily.blocks` (the canonical `EnsembleLemmas.take_drop_ofFn_blocks`, read through
-`EnsembleLemmas.blocks_eq`). -/
+`FunFamily.blocks` (the block window `FunFamily.ofFn_blocks`, read backwards). -/
 theorem take_drop_ofFn_blocks {q s : ℕ} (w : Fin (q * s) → Bool) (i : ℕ) (hi : i < q) :
-    ((List.ofFn w).drop (i * s)).take s = List.ofFn (FunFamily.blocks q s w ⟨i, hi⟩) := by
-  rw [EnsembleLemmas.take_drop_ofFn_blocks w i hi, EnsembleLemmas.blocks_eq]
+    ((List.ofFn w).drop (i * s)).take s = List.ofFn (FunFamily.blocks q s w ⟨i, hi⟩) :=
+  (FunFamily.ofFn_blocks q s w ⟨i, hi⟩).symm
 
 /-! ### The next-query machine of Thm-99.2.1 -/
 
diff --git a/TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Handler.lean b/TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Handler.lean
index 121bdb30a..c61bad1a2 100644
--- a/TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Handler.lean
+++ b/TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Handler.lean
@@ -48,7 +48,7 @@ The finalization asks nothing and outputs the adversary's bit.
 namespace TCSlib.Cryptography.Composability.PRFGame
 
 open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
-open TCSlib.Cryptography.Games.InteractiveHandler (rU rW rS rI rX rL rCnt)
+open TCSlib.Cryptography.Games.InteractiveHandler (rU rW rS rI rX rL rCnt rAns)
 
 /-! ### Lengths and states -/
 
@@ -192,14 +192,12 @@ private def rFlag (w : List Bool) : Bool := (pairSndD (rS w)).headD false
 /-- The recorded challenge of the state. -/
 private def rRec (w : List Bool) : List Bool :=
   ((pairSndD (rS w)).drop 1).take (ctP.eval (rU w).length)
-/-- The outer answer recorded in the log `⟨⟨[], ⟨x, y⟩⟩, []⟩`. -/
-private def rY (w : List Bool) : List Bool := pairSndD (pairSndD (pairFstD (rL w)))
 /-- Tape `j` of the seed. -/
 private def rNonce (w : List Bool) : List Bool :=
   ((rW w).drop ((rCnt w).length * (rU w).length)).take (rU w).length
 /-- The ciphertext `⟨r, m ⊕ y⟩` with the tape `r` and the outer answer `y`. -/
 private def rCt (w m : List Bool) : List Bool :=
-  pairEncode (rNonce w) (List.zipWith xor m (rY w))
+  pairEncode (rNonce w) (List.zipWith xor m (rAns w))
 /-- The selected challenge message `m_b`. -/
 private def rMsg (b : Bool) (w : List Bool) : List Bool :=
   if b then (rX w).drop (rU w).length else (rX w).take (rU w).length
@@ -223,7 +221,7 @@ private def pkRun (atkBit b : Bool) (w : List Bool) : List Bool :=
     else
       if atkBit && !rFlag w && rWF w then
         if decide (rL w = []) then pairEncode [false] (pairEncode [] (pairFstD (rX w)))
-        else pairEncode [true] ((true :: List.zipWith xor (pairSndD (rX w)) (rY w)) ++ rS w)
+        else pairEncode [true] ((true :: List.zipWith xor (pairSndD (rX w)) (rAns w)) ++ rS w)
       else pairEncode [true]
         (List.replicate ((PolyExpr.add .var (.const 1)).eval (rU w).length) false ++ rS w)
   else
@@ -252,7 +250,7 @@ private theorem polyTimeComputable_pkRun (atkBit b : Bool) :
     ((polyTimeComputable_pairTakePoly ctP).comp
       (hU.pairEncode (polyTimeComputable_tail.comp hT))).congr fun w => by
         simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]; rfl
-  have hY : PolyTimeComputable rY := hD.comp (hD.comp (hF.comp hL))
+  have hY : PolyTimeComputable rAns := InteractiveHandler.polyTimeComputable_rAns
   have hOff : PolyTimeComputable fun w =>
       List.replicate ((rCnt w).length * (rU w).length) true :=
     (OneWay.polyTimeComputable_unaryMulPair.comp (hCnt.pairEncode hU)).congr fun w => by
@@ -266,7 +264,7 @@ private theorem polyTimeComputable_pkRun (atkBit b : Bool) :
       simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
         PolyExpr.eval_var]; rfl
   have hXor : ∀ {m : List Bool → List Bool}, PolyTimeComputable m →
-      PolyTimeComputable fun w => List.zipWith xor (m w) (rY w) := fun hm =>
+      PolyTimeComputable fun w => List.zipWith xor (m w) (rAns w) := fun hm =>
     (polyTimeComputable_pairXor.comp (hm.pairEncode hY)).congr fun w => by
       simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
   have hCt : ∀ {m : List Bool → List Bool}, PolyTimeComputable m →
@@ -407,47 +405,6 @@ section Answers
 variable (atkBit b : Bool) (n : ℕ) (z : List Bool)
   (ω : Fin ((pkHandler q atkBit b).seedLen.eval n) → Bool)
 
-/-- The outer log after one outer query `x'` answered `y`. -/
-private theorem encodeLog_one (x' y : Fin ((pkOut 0).eval n) → Bool) :
-    (bitCodec (fun j => (pkOut j).eval n) (fun j => (pkOut j).eval n) 0).encodeLog
-        ([] ++ [⟨0, x', y⟩]) =
-      pairEncode (pairEncode [] (pairEncode (List.ofFn x') (List.ofFn y))) [] := by
-  rw [List.nil_append, MachineCodec.encodeLog_cons, MachineCodec.encodeLog_nil,
-    bitCodec_encodeEntry]
-  rfl
-
-/-- A call whose first round asks `x'` of the outer oracle, and whose second round, with the
-answer `y` in the log, returns `ans y ‖ s' y`, is the query `x'` followed by `(ans y, s' y)`. -/
-private theorem impl_of_query {i : Fin 3} (x : Fin ((pkDin i).eval n) → Bool)
-    (s : Fin ((pkStLen q).eval n) → Bool) (x' : Fin ((pkOut 0).eval n) → Bool)
-    (ans : (Fin ((pkOut 0).eval n) → Bool) → Fin ((pkDout i).eval n) → Bool)
-    (s' : (Fin ((pkOut 0).eval n) → Bool) → Fin ((pkStLen q).eval n) → Bool)
-    (h1 : pkRun q atkBit b (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn s) i
-      (List.ofFn x) []) = pairEncode [false] (pairEncode [] (List.ofFn x')))
-    (h2 : ∀ y, pkRun q atkBit b (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn s) i
-      (List.ofFn x) (pairEncode (pairEncode [] (pairEncode (List.ofFn x') (List.ofFn y))) [])) =
-        pairEncode [true] (List.ofFn (ans y) ++ List.ofFn (s' y))) :
-    (pkHandler q atkBit b).impl n z ω i x s =
-      .query 0 x' fun y => .pure (ans y, s' y) := by
-  rw [InteractiveHandler.impl_apply, InteractiveHandler.call_eq, pkHandler_perCall,
-    PolyExpr.eval_const]
-  rw [buildComp_succ_of_query (i := 0) (x := x') (by
-    show decodeBitMove _ _ _ (pkRun q atkBit b _) = _
-    rw [MachineCodec.encodeLog_nil, h1]
-    exact decodeBitMove_query (fun j => (pkOut j).eval n) (fun j => (pkOut j).eval n) _ 0 x'),
-    OracleComp.query_bind]
-  congr 1
-  funext y
-  rw [buildComp_zero_of_ret (a := Fin.append (ans y) (s' y)) (by
-    show decodeBitMove _ _ _ (pkRun q atkBit b _) = _
-    rw [encodeLog_one, h2, ← List.ofFn_fin_append]
-    exact decodeBitMove_ret _ _ _ _), OracleComp.pure_bind]
-  congr 2
-  · funext k
-    exact Fin.append_left (ans y) (s' y) k
-  · funext k
-    exact Fin.append_right (ans y) (s' y) k
-
 /-- The round input of a call, field by field, on an encoded state with `j ≤ q(n)`. -/
 private theorem fields_input {i : Fin 3} (x L : List Bool) (j : ℕ)
     (o : Option (Fin (ctP.eval n) → Bool)) (hj : j ≤ q.eval n) :
@@ -486,8 +443,9 @@ private theorem recBits_fields (o : Option (Fin (ctP.eval n) → Bool)) :
 
 /-- The outer answer recorded in a one-entry log. -/
 private theorem rY_one (w : List Bool) (x' y : List Bool)
-    (hL : rL w = pairEncode (pairEncode [] (pairEncode x' y)) []) : rY w = y := by
-  rw [rY, hL, pairFstD_pairEncode, pairSndD_pairEncode, pairSndD_pairEncode]
+    (hL : rL w = pairEncode (pairEncode [] (pairEncode x' y)) []) : rAns w = y := by
+  rw [InteractiveHandler.rAns_eq, hL, pairFstD_pairEncode, pairSndD_pairEncode,
+    pairSndD_pairEncode]
 
 /-- The index word of oracle `2`. -/
 private theorem replicate_two : List.replicate ((2 : Fin 3) : ℕ) true = [true, true] := rfl
@@ -507,7 +465,7 @@ state `pkState (j + 1) o`.
 **Proof sketch.** Read the round input field by field (`fields_input`); the first round, with an
 empty log, asks the outer oracle at the tape `T_j` (`rNonce_fields`); the second, with the answer
 `y` in the log (`rY_one`), returns `⟨T_j, m ⊕ y⟩` and the state with count `j + 1`
-(`rNew_fields`); `impl_of_query` assembles the two rounds. -/
+(`rNew_fields`); `InteractiveHandler.impl_of_query` assembles the two rounds. -/
 theorem pkHandler_impl_enc (x : Fin ((pkDin 0).eval n) → Bool) (j : ℕ)
     (o : Option (Fin (ctP.eval n) → Bool)) (hj : j < q.eval n) :
     (pkHandler q atkBit b).impl n z ω 0 x (pkState q n j o) =
@@ -519,12 +477,16 @@ theorem pkHandler_impl_enc (x : Fin ((pkDin 0).eval n) → Bool) (j : ℕ)
       (List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩))) =
       List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩) :=
     ofFn_padFin_of_length (by rw [List.length_ofFn, hn])
-  refine impl_of_query q atkBit b n z ω x _ _ _ _ ?_ ?_
-  · obtain ⟨-, -, -, hI, -, hL, -, -, -⟩ :=
+  refine InteractiveHandler.impl_of_query _ n z ω x _ 0 _ _ _
+    (by rw [pkHandler_perCall, PolyExpr.eval_const]) ?_ ?_
+  · show pkRun q atkBit b _ = _
+    obtain ⟨-, -, -, hI, -, hL, -, -, -⟩ :=
       fields_input q atkBit b n z ω (i := 0) (List.ofFn x) [] j o hj.le
     rw [pkRun, hI, hL, hT, rNonce_fields q atkBit b n z ω (i := 0) _ _ j o hj]
     rfl
   · intro y
+    show pkRun q atkBit b _ = _
+    simp only [Fin.val_zero, List.replicate_zero]
     obtain ⟨-, -, -, hI, hX, hL, -, hFlag, hRec⟩ :=
       fields_input q atkBit b n z ω (i := 0) (List.ofFn x)
         (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((pkOut 0).eval n)
@@ -549,7 +511,7 @@ state is kept.
 
 **Proof sketch.** As for `pkHandler_impl_enc`: the open test reads `atkBit`, the flag and the
 well-formedness of `⟦x⟧` (`fields_input`); the first round asks the outer oracle at `x₀`, the second
-returns `⟨1, v ⊕ y⟩` with the state unchanged (`impl_of_query`). -/
+returns `⟨1, v ⊕ y⟩` with the state unchanged (`InteractiveHandler.impl_of_query`). -/
 theorem pkHandler_impl_dec_open (x : Fin ((pkDin 1).eval n) → Bool) (j : ℕ)
     (o : Option (Fin (ctP.eval n) → Bool)) (hj : j ≤ q.eval n)
     (hop : (atkBit && !o.isSome && decWF n (List.ofFn x)) = true) :
@@ -565,8 +527,10 @@ theorem pkHandler_impl_dec_open (x : Fin ((pkDin 1).eval n) → Bool) (j : ℕ)
   have hx0 : List.ofFn (padFin ((pkOut 0).eval n) (pairFstD (List.ofFn x))) =
       pairFstD (List.ofFn x) := ofFn_padFin_of_length (by rw [hwf.1, hn])
   have hc : ((1 : Fin 3) : ℕ) = 1 := rfl
-  refine impl_of_query q atkBit b n z ω x _ _ _ _ ?_ ?_
-  · obtain ⟨hU, -, -, hI, hX, hL, -, hFlag, -⟩ :=
+  refine InteractiveHandler.impl_of_query _ n z ω x _ 0 _ _ _
+    (by rw [pkHandler_perCall, PolyExpr.eval_const]) ?_ ?_
+  · show pkRun q atkBit b _ = _
+    obtain ⟨hU, -, -, hI, hX, hL, -, hFlag, -⟩ :=
       fields_input q atkBit b n z ω (i := 1) (List.ofFn x) [] j o hj
     have hWF : rWF (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn (pkState q n j o))
         (1 : Fin 3)
@@ -575,6 +539,8 @@ theorem pkHandler_impl_dec_open (x : Fin ((pkDin 1).eval n) → Bool) (j : ℕ)
     rw [pkRun, hI, Fin.val_one, List.replicate_one, hFlag, hWF, hop, hL, hX, hx0]
     rfl
   · intro y
+    show pkRun q atkBit b _ = _
+    simp only [Fin.val_zero, List.replicate_zero]
     obtain ⟨hU, -, hS, hI, hX, hL, -, hFlag, -⟩ :=
       fields_input q atkBit b n z ω (i := 1) (List.ofFn x)
         (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((pkOut 0).eval n)
@@ -653,13 +619,17 @@ theorem pkHandler_impl_challenge_none (x : Fin ((pkDin 2).eval n) → Bool) (j :
       rw [List.length_ofFn, pkDin_two, PolyExpr.eval_add, PolyExpr.eval_var]
     rw [AdaptiveCPA.msgOf_eq]
     cases b <;> simp [hx]
-  refine impl_of_query q atkBit b n z ω x _ _ _ _ ?_ ?_
-  · obtain ⟨-, -, -, hI, -, hL, -, hFlag, -⟩ :=
+  refine InteractiveHandler.impl_of_query _ n z ω x _ 0 _ _ _
+    (by rw [pkHandler_perCall, PolyExpr.eval_const]) ?_ ?_
+  · show pkRun q atkBit b _ = _
+    obtain ⟨-, -, -, hI, -, hL, -, hFlag, -⟩ :=
       fields_input q atkBit b n z ω (i := 2) (List.ofFn x) [] j none hj.le
     rw [pkRun, hI, replicate_two, hFlag, hL, hT,
       rNonce_fields q atkBit b n z ω (i := 2) _ _ j none hj]
     rfl
   · intro y
+    show pkRun q atkBit b _ = _
+    simp only [Fin.val_zero, List.replicate_zero]
     obtain ⟨hU, -, -, hI, hX, hL, -, hFlag, -⟩ :=
       fields_input q atkBit b n z ω (i := 2) (List.ofFn x)
         (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((pkOut 0).eval n)
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/AdaptiveCPA/Handler.lean b/TCSlib/Cryptography/Encryption/PublicKey/AdaptiveCPA/Handler.lean
index 470a9e07f..3382bf3d7 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/AdaptiveCPA/Handler.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/AdaptiveCPA/Handler.lean
@@ -53,7 +53,7 @@ per inner query is the forwarded challenge; its finalization asks nothing and ou
 namespace TCSlib.Cryptography.Composability.AdaptiveCPA
 
 open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
-open TCSlib.Cryptography.Games.InteractiveHandler (rU rZ rW rS rI rX rL rCnt)
+open TCSlib.Cryptography.Games.InteractiveHandler (rU rZ rW rS rI rX rL rCnt rAns)
 
 /-! ### Messages, lengths and states -/
 
@@ -164,8 +164,6 @@ private def rIst (w : List Bool) : List Bool := pairFstD (pairSndD (rS w))
 /-- The latest ciphertext of the state. -/
 private def rLat (w : List Bool) : List Bool :=
   (pairSndD (pairSndD (rS w))).take (S.ctLen.eval (rU w).length)
-/-- The outer answer recorded in the log `⟨⟨1, ⟨x, y⟩⟩, []⟩`. -/
-private def rFwd (w : List Bool) : List Bool := pairSndD (pairSndD (pairFstD (rL w)))
 /-- The new state `⟨1^{j+1}, ⟨1^{i⋆}, y⟩⟩`, padded. -/
 private def rNew (w y : List Bool) : List Bool :=
   EnsembleLemmas.padL ((acStLen S cap).eval (rU w).length)
@@ -193,7 +191,7 @@ private def acRun (w : List Bool) : List Bool :=
     if decide (cap.eval (rU w).length ≤ (rCnt w).length) then pairEncode [true] (rLat S w ++ rS w)
     else if decide ((rCnt w).length = (rIst w).length) then
       if decide (rL w = []) then pairEncode [false] (pairEncode [true] (rX w))
-      else pairEncode [true] (rFwd w ++ rNew S cap w (rFwd w))
+      else pairEncode [true] (rAns w ++ rNew S cap w (rAns w))
     else pairEncode [true] (rEnc S w ++ rNew S cap w (rEnc S w))
   else pairEncode [true] (List.replicate ((S.msgLen.add (.const 1)).eval (rU w).length) false ++
     rS w)
@@ -214,7 +212,7 @@ private theorem polyTimeComputable_acRun : PolyTimeComputable (acRun S cap) := b
   have hLat : PolyTimeComputable (rLat S) :=
     ((polyTimeComputable_pairTakePoly S.ctLen).comp (hU.pairEncode (hD.comp (hD.comp hS)))).congr
       fun w => by simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]; rfl
-  have hFwd : PolyTimeComputable rFwd := hD.comp (hD.comp (hF.comp hL))
+  have hFwd : PolyTimeComputable rAns := InteractiveHandler.polyTimeComputable_rAns
   have hNew : ∀ {y : List Bool → List Bool}, PolyTimeComputable y →
       PolyTimeComputable fun w => rNew S cap w (y w) := fun hy =>
     EnsembleLemmas.polyTimeComputable_padL (acStLen S cap) hU
@@ -516,11 +514,12 @@ theorem acHandler_impl_forward (x : Fin ((acDin S 1).eval n) → Bool) (j : ℕ)
       rw [rNew, hU, hCnt, hIst, List.length_replicate, hs', acState_eq,
         EnsembleLemmas.ofFn_padFin_eq_padL, List.replicate_succ,
         ofFn_padFin_of_length (List.length_ofFn)]
-    have hFwd : rFwd (InteractiveHandler.input n z (List.ofFn ω)
+    have hFwd : rAns (InteractiveHandler.input n z (List.ofFn ω)
         (List.ofFn (acState S cap ist n j c)) (1 : Fin 2) (List.ofFn x)
         ((bitCodec (fun j => (acDin S j).eval n) (fun j => (acDout S j).eval n) 0).encodeLog
           ([] ++ [⟨1, x, y⟩]))) = List.ofFn y := by
-      rw [rFwd, hL, hlog, pairFstD_pairEncode, pairSndD_pairEncode, pairSndD_pairEncode]
+      rw [InteractiveHandler.rAns_eq, hL, hlog, pairFstD_pairEncode, pairSndD_pairEncode,
+        pairSndD_pairEncode]
     have hh : ([true].headD false = true) := rfl
     have hc1 : ¬ (decide (cap.eval n ≤ j) = true) := by rw [decide_eq_true_eq]; omega
     have hc2 : decide (j = ist n) = true := decide_eq_true heq
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability.lean b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability.lean
index 4d25cc629..3cf6deba3 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability.lean
@@ -210,23 +210,14 @@ theorem nmCodec_eq_bitCodec (n ℓ : ℕ) :
     S.nmCodec n ℓ = bitCodec (S.inLens n) (S.outLens n) (ℓ * S.ctLen.eval n) := rfl
 
 /-- Ciphertext `i` of an output string is its `i`-th block of `ctLen(n)` bits:
-`⟦S.nthCt w i⟧ = (⟦w⟧.drop (i · ctLen(n))).take ctLen(n)`. -/
+`⟦S.nthCt w i⟧ = (⟦w⟧.drop (i · ctLen(n))).take ctLen(n)` (`FunFamily.ofFn_blocks`, the block
+window). -/
 theorem ofFn_nthCt {n ℓ : ℕ} (w : Fin (ℓ * S.ctLen.eval n) → Bool) (i : Fin ℓ) :
     List.ofFn (S.nthCt w i) =
       ((List.ofFn w).drop (i * S.ctLen.eval n)).take (S.ctLen.eval n) := by
-  have hle : (i : ℕ) * S.ctLen.eval n + S.ctLen.eval n ≤ ℓ * S.ctLen.eval n := by
-    have := Nat.mul_le_mul_right (S.ctLen.eval n) (Nat.succ_le_of_lt i.isLt)
-    rw [Nat.succ_mul] at this
-    exact this
-  refine List.ext_getElem ?_ fun j h₁ h₂ => ?_
-  · simp only [List.length_ofFn, List.length_take, List.length_drop]
-    omega
-  · rw [List.getElem_ofFn, List.getElem_take, List.getElem_drop, List.getElem_ofFn]
-    refine congrArg w (Fin.ext ?_)
-    rw [finProdFinEquiv_apply_val]
-    show j + S.ctLen.eval n * i = i * S.ctLen.eval n + j
-    rw [Nat.mul_comm]
-    omega
+  have hblk : S.nthCt w i = FunFamily.blocks ℓ (S.ctLen.eval n) w i :=
+    funext fun j => (FunFamily.blocks_apply ℓ (S.ctLen.eval n) w i j).symm
+  rw [hblk, FunFamily.ofFn_blocks]
 
 /-! ### (⇒) The CCA2 adversary built from a non-malleability adversary -/
 
@@ -400,7 +391,7 @@ private theorem accept_indGame_decRed (A D B B' : NUPPT) (q ℓ : PolyExpr) (n :
 
 **Proof sketch.** Given `A` (budget `q`, `ℓ` ciphertexts) and `D`, T2
 (`Games.exists_interactiveHandlerMachine`) makes the handler `decHandler S ℓ D` a machine `B`, and
-`exists_withAdviceOn` hard-wires `D`'s advice into it (`B'`). `B'`'s budget is
+`NUPPT.exists_withAdviceOn` hard-wires `D`'s advice into it (`B'`). `B'`'s budget is
 `q · 1 + ℓ`, a polynomial; CCA2 security gives a negligible bound on `B'`'s advantage, which at
 every `n` equals the advantage of `D` between `NM_0` and `NM_1` (`accept_indGame_decRed`). -/
 theorem nmSecure_cca2_of_indSecure_cca2 (h : S.INDSecure .cca2) : S.NMSecure .cca2 := by
@@ -408,7 +399,7 @@ theorem nmSecure_cca2_of_indSecure_cca2 (h : S.INDSecure .cca2) : S.NMSecure .cc
   intro A q ℓ D
   obtain ⟨B, hB⟩ := exists_interactiveHandlerMachine A q (acDin S) (acDout S) (acDin S)
     (acDout S) (ℓ.mul S.ctLen) (decHandler S ℓ D)
-  obtain ⟨B', hc, hB'⟩ := exists_withAdviceOn B D.advice D.adv D.advice_length
+  obtain ⟨B', hc, hB'⟩ := NUPPT.exists_withAdviceOn B D.advice D.adv D.advice_length
   obtain ⟨ε, hε, hbound⟩ := (S.INDSecure_iff .cca2).1 h B'
     ((q.mul (decHandler S ℓ D).perCall).add (decHandler S ℓ D).finCall)
   refine ⟨ε, hε, fun n => ?_⟩
@@ -598,7 +589,8 @@ private theorem accept_nmGame_encRed (A B : NUPPT) (q : PolyExpr) (n : ℕ)
 the handler `encHandler S` a machine `B`, with budget `q · 1 + 0`. Non-malleability for `B`, two
 output ciphertexts and `guessDist` gives a negligible bound. At `n` with `msgLen(n) > 0`, `A`'s
 CCA2 advantage equals that experiment's advantage (`accept_nmGame_encRed`). At `msgLen(n) = 0` the
-two CCA2 games coincide (`indImpl_eq_of_msgLen_eq_zero`), so `A`'s advantage is `0`. -/
+two CCA2 games coincide (`FixedLengthPKScheme.indImpl_eq_of_msgLen_eq_zero`), so `A`'s advantage
+is `0`. -/
 theorem indSecure_cca2_of_nmSecure_cca2 (h : S.NMSecure .cca2) : S.INDSecure .cca2 := by
   rw [INDSecure_iff]
   intro A q
@@ -611,7 +603,7 @@ theorem indSecure_cca2_of_nmSecure_cca2 (h : S.NMSecure .cca2) : S.INDSecure .cc
   by_cases hm : S.msgLen.eval n = 0
   · have hg : S.indGame .cca2 A (q.eval n) false n = S.indGame .cca2 A (q.eval n) true n := by
       rw [S.indGame_eq, S.indGame_eq]
-      simp only [indImpl_eq_of_msgLen_eq_zero S .cca2 n _ _ hm]
+      simp only [S.indImpl_eq_of_msgLen_eq_zero .cca2 n _ _ hm]
     rw [hg, advantage_self]
     exact (advantage_nonneg _ _).trans hn
   · obtain ⟨φ, hφ⟩ := hB n
@@ -634,7 +626,7 @@ end Proof
    (`Games.exists_interactiveHandlerMachine`) makes this a machine, for the forwarding handler
    `NMCCA2.decHandler`: `advIn = pk`, one outer call per query, and `finCall = ℓ` in
    finalization before running `D`, for total budget `q + ℓ`. `D`'s advice is carried through
-   `z = ⟨pk, α⟩` and hard-wired afterwards (`NMCCA2.exists_withAdviceOn`, from the public
+   `z = ⟨pk, α⟩` and hard-wired afterwards (`NUPPT.exists_withAdviceOn`, from the public
    `exists_withAdvice`/`exists_comp` closure lemmas). The two games accept with the same
    probability at every `n` (`nmSecure_cca2_of_indSecure_cca2`).
 2. (⇐) Given an IND adversary `A` with guess `g`, the NM adversary runs `A`, forwarding its
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability/Decrypt.lean b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability/Decrypt.lean
index 36b61a520..9e7f1bced 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability/Decrypt.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability/Decrypt.lean
@@ -14,7 +14,7 @@ set_option autoImplicit false
 
 Direction (⇒) of [PS10, Theorem 175.9]. Given a non-malleability adversary `A` whose output is
 `ℓ(n)` ciphertexts and a distinguisher `D`, the CCA2 adversary runs `A` on the public key and
-forwards all of `A`'s queries to its own oracles (`NMCCA2.fwdHandler`). In the finalization it
+forwards all of `A`'s queries to its own oracles (`Games.fwdHandler`). In the finalization it
 asks its decryption oracle for each of `A`'s `ℓ(n)` ciphertexts in turn and outputs `D`'s
 verdict on the concatenated answers. Under CCA2 the decryption oracle refuses the recorded
 challenge with `⊥`, exactly as the non-malleability experiment decrypts a copy of the challenge.
@@ -22,19 +22,20 @@ challenge with `⊥`, exactly as the non-malleability experiment decrypts a copy
 This file builds the handler (`decHandler S ℓ D`): its seed is `D`'s coins, and the reduction
 input is `⟨pk, α⟩`, where `α` is `D`'s advice. It proves the finalization's equation against
 any outer oracle whose decryption answers are deterministic and keep the state
-(`simulate_decHandler_finish`). The advice is hard-wired afterwards (`exists_withAdviceOn`,
-from `NUPPT.exists_comp` and `NUPPT.exists_withAdvice`).
+(`simulate_decHandler_finish`). The advice is hard-wired afterwards
+(`Complexity.NUPPT.exists_withAdviceOn`, from `NUPPT.exists_comp` and `NUPPT.exists_withAdvice`).
+The per-entry readings of a log are `Games.cntRead` and `Games.ansRead`.
 
 ## Main definitions
 
-* `NMCCA2.cntRead`, `NMCCA2.ansRead`: the per-entry readings of a log (one token, the answer).
 * `NMCCA2.decHandler`: the handler of the reduction.
 
 ## Main results
 
+* `NMCCA2.length_logEmit_cntRead`, `NMCCA2.logEmit_ansRead`: counting the entries of a log and
+  collecting their answers.
 * `NMCCA2.simulate_decHandler_impl`: the handler forwards.
 * `NMCCA2.simulate_decHandler_finish`: the finalization decrypts the `ℓ` blocks and runs `D`.
-* `NMCCA2.exists_withAdviceOn`: hard-wiring a second component of the input.
 
 ## References
 
@@ -45,32 +46,13 @@ from `NUPPT.exists_comp` and `NUPPT.exists_withAdvice`).
 namespace TCSlib.Cryptography.Composability.NMCCA2
 
 open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
+open TCSlib.Cryptography.Games.InteractiveHandler (rU rZ rW rS rI rX rL rAns finA)
+open TCSlib.Cryptography.Games.InteractiveHandler (rU_finInput rZ_finInput rW_finInput
+  rL_finInput finA_finInput polyTimeComputable_rU polyTimeComputable_rZ polyTimeComputable_rW
+  polyTimeComputable_rL polyTimeComputable_finA)
 open AdaptiveCPA (acDin acDout acDin_zero acDout_zero)
 
-/-! ### Readings of a log entry -/
-
-/-- One token for a nonempty log and nothing for the empty one:
-`cntRead v = if v = [] then [] else [true]`. With `logEmit` it counts the entries of a log. -/
-def cntRead (v : List Bool) : List Bool := if decide (v = []) then [] else [true]
-
-/-- `cntRead v = if v = [] then [] else [true]`. -/
-theorem cntRead_eq (v : List Bool) : cntRead v = if decide (v = []) then [] else [true] := rfl
-
-/-- The token reading is polynomial-time: `PolyTimeComputable cntRead`. -/
-theorem polyTimeComputable_cntRead : PolyTimeComputable cntRead :=
-  polyTimeComputable_ite polyTimeComputable_isNil (polyTimeComputable_const [])
-    (polyTimeComputable_const [true])
-
-/-- The answer `y` of the first entry `⟨1^i, ⟨x, y⟩⟩` of a log:
-`ansRead v = pairSndD (pairSndD (pairFstD v))`. -/
-def ansRead (v : List Bool) : List Bool := pairSndD (pairSndD (pairFstD v))
-
-/-- `ansRead v = pairSndD (pairSndD (pairFstD v))`. -/
-theorem ansRead_eq (v : List Bool) : ansRead v = pairSndD (pairSndD (pairFstD v)) := rfl
-
-/-- The answer reading is polynomial-time: `PolyTimeComputable ansRead`. -/
-theorem polyTimeComputable_ansRead : PolyTimeComputable ansRead :=
-  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD)
+/-! ### Readings of a log -/
 
 section Readings
 
@@ -79,7 +61,7 @@ variable {k : ℕ} {din dout : Fin k → ℕ} {dα : ℕ}
 /-- **Counting the entries:** `|logEmit cntRead ⟦h⟧| = |h|`. -/
 theorem length_logEmit_cntRead (h : QueryLog (bitSpec din dout)) :
     (logEmit cntRead ((bitCodec din dout dα).encodeLog h)).length = h.length := by
-  rw [logEmit_encodeLog _ cntRead (fun _ => [true]) rfl
+  rw [logEmit_encodeLog _ cntRead (fun _ => [true]) (by rw [cntRead_eq]; rfl)
     (fun e t => by rw [cntRead_eq, decide_eq_false (pairEncode_ne_nil _ _)]; rfl)]
   simp only [List.length_flatMap, List.length_singleton, List.map_const', List.sum_replicate,
     smul_eq_mul, mul_one]
@@ -101,42 +83,46 @@ end Readings
 variable (S : FixedLengthPKScheme) (ℓ : PolyExpr) (D : NUPPT)
 
 /-- The number of decryptions asked so far, in unary. -/
-private def dCnt (w : List Bool) : List Bool := logEmit cntRead (finL w)
+private def dCnt (w : List Bool) : List Bool := logEmit cntRead (rL w)
 
 /-- The next block of the adversary's output: `ctLen(n)` bits from position `j · ctLen(n)`, for
 `j` the decryptions asked so far, padded with `false`. -/
 private def dCt (w : List Bool) : List Bool :=
-  EnsembleLemmas.padL (S.ctLen.eval (finU w).length)
-    ((finA w).drop ((dCnt w).length * S.ctLen.eval (finU w).length))
+  EnsembleLemmas.padL (S.ctLen.eval (rU w).length)
+    ((finA w).drop ((dCnt w).length * S.ctLen.eval (rU w).length))
 
 /-- `D`'s input layout: parameter `1^n`, the collected answers, the advice (the second component
 of the reduction input) and the seed as coins. -/
 private def dIn (w : List Bool) : List Bool :=
-  pairEncode (pairEncode (pairEncode (finU w) (logEmit ansRead (finL w))) (pairSndD (finZ w)))
-    (finW w)
+  pairEncode (pairEncode (pairEncode (rU w) (logEmit ansRead (rL w))) (pairSndD (rZ w)))
+    (rW w)
 
 /-- **One round of the finalization.** After `ℓ(n)` decryptions, output `D`'s verdict
 `[D(answers) = [true]]`; before, ask the decryption oracle (index `0`) the next block. -/
 private def dFin (w : List Bool) : List Bool :=
-  if decide (ℓ.eval (finU w).length ≤ (dCnt w).length) then
+  if decide (ℓ.eval (rU w).length ≤ (dCnt w).length) then
     pairEncode [true] [decide (D.output (dIn w) = [true])]
   else pairEncode [false] (pairEncode [] (dCt S w))
 
 /-- The finalization round is polynomial-time. -/
 private theorem polyTimeComputable_dFin : PolyTimeComputable (dFin S ℓ D) := by
-  obtain ⟨hU, hZ, hW, hA, hL⟩ := polyTimeComputable_finFields
+  have hU := polyTimeComputable_rU
+  have hZ := polyTimeComputable_rZ
+  have hW := polyTimeComputable_rW
+  have hA := polyTimeComputable_finA
+  have hL := polyTimeComputable_rL
   have hCnt : PolyTimeComputable dCnt :=
     (polyTimeComputable_logEmit polyTimeComputable_cntRead).comp hL
-  have hAns : PolyTimeComputable fun w => logEmit ansRead (finL w) :=
+  have hAns : PolyTimeComputable fun w => logEmit ansRead (rL w) :=
     (polyTimeComputable_logEmit polyTimeComputable_ansRead).comp hL
   have hOff : PolyTimeComputable fun w =>
-      List.replicate ((dCnt w).length * S.ctLen.eval (finU w).length) true :=
+      List.replicate ((dCnt w).length * S.ctLen.eval (rU w).length) true :=
     (OneWay.polyTimeComputable_unaryMulPair.comp
       (hCnt.pairEncode ((polyTimeComputable_unaryPoly S.ctLen).comp hU))).congr fun w => by
         simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
           List.length_replicate]
   have hDrop : PolyTimeComputable fun w =>
-      (finA w).drop ((dCnt w).length * S.ctLen.eval (finU w).length) :=
+      (finA w).drop ((dCnt w).length * S.ctLen.eval (rU w).length) :=
     (polyTimeComputable_dropPrefixByLength.comp (hOff.pairEncode hA)).congr fun w => by
       simp only [Function.comp_apply, PrefixByLength.drop_def, pairFstD_pairEncode,
         pairSndD_pairEncode, List.length_replicate]
@@ -147,7 +133,7 @@ private theorem polyTimeComputable_dFin : PolyTimeComputable (dFin S ℓ D) := b
     (polyTimeComputable_pairEq.comp ((D.polyTimeComputable_output.comp hIn).pairEncode
       (polyTimeComputable_const [true]))).congr fun w => by
         simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
-  have hT : PolyTimeComputable fun w => [decide (ℓ.eval (finU w).length ≤ (dCnt w).length)] :=
+  have hT : PolyTimeComputable fun w => [decide (ℓ.eval (rU w).length ≤ (dCnt w).length)] :=
     (polyTimeComputable_lenLe.comp (hCnt.pairEncode
       ((polyTimeComputable_unaryPoly ℓ).comp hU))).congr fun w => by
         simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
@@ -254,13 +240,25 @@ theorem simulate_decHandler_finish (n : ℕ) (z : List Bool)
       w = InteractiveHandler.finInput n z (List.ofFn ω) (List.ofFn s) (List.ofFn a)
         ((bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n) 0).encodeLog
           (hist j)) →
-      (dCnt w).length = j ∧ finU w = List.replicate n true ∧
+      (dCnt w).length = j ∧ rU w = List.replicate n true ∧
       dIn w = NUPPT.layout (List.replicate n true)
         ((List.range j).map fun i => List.ofFn (ans (decBlock S n a i) st)).flatten
         (pairSndD z) (List.ofFn ω) ∧
       dCt S w = List.ofFn (decBlock S n a j) := by
     intro j w hw
-    obtain ⟨hU, hZ, hW, hA, hL⟩ := fields_finInput n z (List.ofFn ω) (List.ofFn s)
+    have hU := rU_finInput n z (List.ofFn ω) (List.ofFn s)
+      (List.ofFn a) ((bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n)
+        0).encodeLog (hist j))
+    have hZ := rZ_finInput n z (List.ofFn ω) (List.ofFn s)
+      (List.ofFn a) ((bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n)
+        0).encodeLog (hist j))
+    have hW := rW_finInput n z (List.ofFn ω) (List.ofFn s)
+      (List.ofFn a) ((bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n)
+        0).encodeLog (hist j))
+    have hA := finA_finInput n z (List.ofFn ω) (List.ofFn s)
+      (List.ofFn a) ((bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n)
+        0).encodeLog (hist j))
+    have hL := rL_finInput n z (List.ofFn ω) (List.ofFn s)
       (List.ofFn a) ((bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n)
         0).encodeLog (hist j))
     rw [← hw] at hU hZ hW hA hL
@@ -317,34 +315,4 @@ theorem simulate_decHandler_finish (n : ℕ) (z : List Bool)
   rw [InteractiveHandler.finish_eq, decHandler_finCall, ← h0]
   exact key (ℓ.eval n) 0 (Nat.zero_add _)
 
-/-! ### Hard-wiring the advice -/
-
-/-- **Hard-wiring a second input component** [PS10, §2.1, implicit]: for a machine `B` and a
-polynomially bounded family `β n` there is a machine `B'` with the same coins (`h`) whose
-computation on the input `x` is `B`'s on `⟨x, β n⟩`, for every codec and budget:
-`B'.toCompOn codec n q x (coinsCongr h n r) = B.toCompOn codec n q ⟨x, β n⟩ r`.
-
-**Proof sketch.** `B₁ := NUPPT.exists_comp B` with the re-pairing
-`⟨⟨x, L⟩, β⟩ ↦ ⟨⟨x, β⟩, L⟩`, then `B' := NUPPT.exists_withAdvice B₁ β`; on `⟨x, L⟩` (the input
-and the encoded log) `B'` runs `B` on `⟨⟨x, β n⟩, L⟩`. -/
-theorem exists_withAdviceOn (B : NUPPT) (β : ℕ → List Bool) (b : PolyExpr)
-    (hβ : ∀ n, (β n).length ≤ b.eval n) :
-    ∃ (B' : NUPPT) (h : B.coins = B'.coins), ∀ (n : ℕ) {ι α : Type} {spec : OracleSpec ι}
-      (codec : MachineCodec spec α) (q : ℕ) (x : List Bool) (r : B.Coins n),
-      B'.toCompOn codec n q x (NUPPT.coinsCongr h n r) =
-        B.toCompOn codec n q (pairEncode x (β n)) r := by
-  have hpre : PolyTimeComputable fun w : List Bool =>
-      pairEncode (pairEncode (pairFstD (pairFstD w)) (pairSndD w)) (pairSndD (pairFstD w)) :=
-    ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD).pairEncode
-      polyTimeComputable_pairSndD).pairEncode
-      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD)
-  obtain ⟨B₁, hc₁, -, -, hB₁⟩ := NUPPT.exists_comp B hpre polyTimeComputable_id
-  obtain ⟨B', hc', hB'⟩ := NUPPT.exists_withAdvice B₁ β b hβ
-  refine ⟨B', (hc'.trans hc₁).symm, fun n ι α spec codec q x r => ?_⟩
-  rw [NUPPT.toCompOn_eq, NUPPT.toCompOn_eq]
-  congr 1
-  funext hist
-  rw [NUPPT.runAt_coinsCongr, hB', hB₁, NUPPT.runAt_eq]
-  simp only [pairFstD_pairEncode, pairSndD_pairEncode, id_eq]
-
 end TCSlib.Cryptography.Composability.NMCCA2
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability/Encrypt.lean b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability/Encrypt.lean
index 491119076..86a12aae1 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability/Encrypt.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability/Encrypt.lean
@@ -14,15 +14,16 @@ set_option autoImplicit false
 
 Direction (⇐) of [PS10, Theorem 175.9]. Given a CCA2 adversary `A` with guess `g`, the
 non-malleability adversary runs `A` on the public key and forwards all of `A`'s queries to its own
-oracles (`NMCCA2.fwdHandler`). It then outputs two fresh encryptions under `pk`, with its own
+oracles (`Games.fwdHandler`). It then outputs two fresh encryptions under `pk`, with its own
 coins: of `g^{m}` and of `(¬g)^{m}`, where `m = msgLen(n)`. The distinguisher `guessDist` reads `g`
 back from the two decryptions: from the first message bit if the first decryption is valid,
 and otherwise from the negated last bit of the second.
 
 This file builds the handler (`encHandler S`), whose seed is two encryption tapes. It proves
 the finalization's equation (`encHandler_finish`) and defines the distinguisher with its two
-verdicts (`guessBit_valid`, `guessBit_refused`). It also shows that at `msgLen(n) = 0` the two
-CCA2 oracles coincide (`indImpl_eq_of_msgLen_eq_zero`).
+verdicts (`guessBit_valid`, `guessBit_refused`), and shows that the verdict is polynomial-time
+(`polyTimeComputable_guessBit`). That the two CCA2 oracles coincide at `msgLen(n) = 0` is
+`FixedLengthPKScheme.indImpl_eq_of_msgLen_eq_zero` (`Encryption/PublicKey/OracleSecurity.lean`).
 
 ## Main definitions
 
@@ -34,7 +35,7 @@ CCA2 oracles coincide (`indImpl_eq_of_msgLen_eq_zero`).
 
 * `NMCCA2.simulate_encHandler_impl`, `NMCCA2.encHandler_finish`.
 * `NMCCA2.guessDist_distinguisherL`, `NMCCA2.guessBit_valid`, `NMCCA2.guessBit_refused`.
-* `NMCCA2.indImpl_eq_of_msgLen_eq_zero`.
+* `NMCCA2.polyTimeComputable_guessBit`: the verdict is polynomial-time.
 
 ## References
 
@@ -45,6 +46,10 @@ CCA2 oracles coincide (`indImpl_eq_of_msgLen_eq_zero`).
 namespace TCSlib.Cryptography.Composability.NMCCA2
 
 open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
+open TCSlib.Cryptography.Games.InteractiveHandler (rU rZ rW rS rI rX rL rAns finA)
+open TCSlib.Cryptography.Games.InteractiveHandler (rU_finInput rZ_finInput rW_finInput
+  finA_finInput polyTimeComputable_rU polyTimeComputable_rZ polyTimeComputable_rW
+  polyTimeComputable_finA)
 open AdaptiveCPA (acDin acDout acDout_zero)
 
 variable (S : FixedLengthPKScheme)
@@ -58,27 +63,30 @@ private def eBit (β : Bool) (w : List Bool) : Bool :=
 
 /-- The plaintext of ciphertext `β`: its bit repeated `msgLen(n)` times. -/
 private def eMsg (β : Bool) (w : List Bool) : List Bool :=
-  if eBit β w then List.replicate (S.msgLen.eval (finU w).length) true
-  else List.replicate (S.msgLen.eval (finU w).length) false
+  if eBit β w then List.replicate (S.msgLen.eval (rU w).length) true
+  else List.replicate (S.msgLen.eval (rU w).length) false
 
 /-- The coins of ciphertext `β`: the first (`β = true`) or the second `ρ(n)` bits of the seed. -/
 private def eTape (β : Bool) (w : List Bool) : List Bool :=
-  if β then (finW w).take (S.enc.coins.eval (finU w).length)
-  else (finW w).drop (S.enc.coins.eval (finU w).length)
+  if β then (rW w).take (S.enc.coins.eval (rU w).length)
+  else (rW w).drop (S.enc.coins.eval (rU w).length)
 
 /-- Ciphertext `β`: `Enc` on `⟨1^n, ⟨pk, plaintext⟩⟩` with empty advice and its coins, padded to
 `ctLen(n)` bits. -/
 private def eCt (β : Bool) (w : List Bool) : List Bool :=
-  EnsembleLemmas.padL (S.ctLen.eval (finU w).length)
-    (S.enc.output (pairEncode (pairEncode (pairEncode (finU w)
-      (pairEncode (finZ w) (eMsg S β w))) []) (eTape S β w)))
+  EnsembleLemmas.padL (S.ctLen.eval (rU w).length)
+    (S.enc.output (pairEncode (pairEncode (pairEncode (rU w)
+      (pairEncode (rZ w) (eMsg S β w))) []) (eTape S β w)))
 
 /-- **The finalization's round:** output the two ciphertexts, `⟨[true], c₁ ‖ c₂⟩`. -/
 private def eFin (w : List Bool) : List Bool := pairEncode [true] (eCt S true w ++ eCt S false w)
 
 /-- The finalization round is polynomial-time. -/
 private theorem polyTimeComputable_eFin : PolyTimeComputable (eFin S) := by
-  obtain ⟨hU, hZ, hW, hA, -⟩ := polyTimeComputable_finFields
+  have hU := polyTimeComputable_rU
+  have hZ := polyTimeComputable_rZ
+  have hW := polyTimeComputable_rW
+  have hA := polyTimeComputable_finA
   have hg : PolyTimeComputable fun w => [(finA w).headD false] := polyTimeComputable_headD.comp hA
   have hBit : ∀ β, PolyTimeComputable fun w => [eBit β w] := by
     intro β
@@ -214,7 +222,13 @@ theorem encHandler_finish (n : ℕ) (z : List Bool)
     rw [encHandler, fwdHandler_finRun]
   rw [InteractiveHandler.finish_eq, encHandler_finCall, PolyExpr.eval_const]
   refine buildComp_zero_of_ret ?_
-  obtain ⟨hU, hZ, hW, hA, -⟩ := fields_finInput n z (List.ofFn ω) (List.ofFn s) (List.ofFn a)
+  have hU := rU_finInput n z (List.ofFn ω) (List.ofFn s) (List.ofFn a)
+    ((bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n) 0).encodeLog [])
+  have hZ := rZ_finInput n z (List.ofFn ω) (List.ofFn s) (List.ofFn a)
+    ((bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n) 0).encodeLog [])
+  have hW := rW_finInput n z (List.ofFn ω) (List.ofFn s) (List.ofFn a)
+    ((bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n) 0).encodeLog [])
+  have hA := finA_finInput n z (List.ofFn ω) (List.ofFn s) (List.ofFn a)
     ((bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n) 0).encodeLog [])
   have hCt : ∀ β, eCt S β (InteractiveHandler.finInput n z (List.ofFn ω) (List.ofFn s)
       (List.ofFn a) ((bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n)
@@ -253,6 +267,16 @@ def guessBit (w : List Bool) : Bool :=
 theorem guessBit_eq (w : List Bool) :
     guessBit w = if w.headD false then (w.drop 1).headD false else !w.reverse.headD false := rfl
 
+/-- **The verdict is polynomial-time:** `PolyTimeComputable fun w => [guessBit w]` (`headD`, `tail`,
+`reverse` and `not`, through `polyTimeComputable_ite`). -/
+theorem polyTimeComputable_guessBit : PolyTimeComputable fun w => [guessBit w] :=
+  (polyTimeComputable_ite polyTimeComputable_headD
+    (polyTimeComputable_headD.comp polyTimeComputable_tail)
+    (polyTimeComputable_not
+      (polyTimeComputable_headD.comp BinArith.polyTimeComputable_reverse))).congr fun w => by
+    rw [guessBit_eq]
+    split <;> rfl
+
 /-- The distinguisher's raw function on the machine input `⟨⟨⟨1^n, w⟩, α⟩, ρ⟩`. -/
 private def guessFun (x : List Bool) : List Bool :=
   if (pairSndD (pairFstD (pairFstD x))).headD false then
@@ -263,10 +287,9 @@ private def guessFun (x : List Bool) : List Bool :=
 private theorem polyTimeComputable_guessFun : PolyTimeComputable guessFun := by
   have hw : PolyTimeComputable fun x => pairSndD (pairFstD (pairFstD x)) :=
     polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)
-  exact polyTimeComputable_ite (polyTimeComputable_headD.comp hw)
-    (polyTimeComputable_headD.comp (polyTimeComputable_tail.comp hw))
-    (polyTimeComputable_not
-      (polyTimeComputable_headD.comp (BinArith.polyTimeComputable_reverse.comp hw)))
+  refine (polyTimeComputable_guessBit.comp hw).congr fun x => ?_
+  rw [Function.comp_apply, guessFun, guessBit_eq]
+  split <;> rfl
 
 /-- **The distinguisher** of the reduction (⇐): the uniform machine without coins computing
 `[guessBit w]` on its argument `w`. -/
@@ -305,28 +328,4 @@ theorem guessBit_refused {m : ℕ} (hm : 0 < m) (g : Bool) :
   rw [FixedLengthScheme.decAnswer_some, h2, guessBit_eq, ofFn_zeroBits, List.replicate_succ]
   simp
 
-/-! ### Empty messages -/
-
-/-- **With empty messages the two CCA2 oracles coincide:** if `msgLen(n) = 0`, then
-`S.indImpl atk false n pk sk = S.indImpl atk true n pk sk` (both halves of a challenge are the
-empty message).
-
-**Proof sketch.** Compare query by query through the published equations: decryption does not
-depend on the bit (`indImpl_dec_onSpec`), a repeated challenge repeats the record
-(`indImpl_challenge_repeat_onSpec`), and a first challenge encrypts a half of the query
-(`indImpl_challenge_none_onSpec`), whose string is `[]` either way. -/
-theorem indImpl_eq_of_msgLen_eq_zero (atk : Attack) (n : ℕ) (pk sk : List Bool)
-    (h : S.msgLen.eval n = 0) : S.indImpl atk false n pk sk = S.indImpl atk true n pk sk := by
-  have h0 : ∀ f : Fin (S.msgLen.eval n) → Bool, List.ofFn f = [] := fun f =>
-    List.eq_nil_of_length_eq_zero (by rw [List.length_ofFn, h])
-  funext i x s
-  match i with
-  | 0 => rw [S.indImpl_dec_onSpec, S.indImpl_dec_onSpec]
-  | 1 =>
-    cases s with
-    | some c => rw [S.indImpl_challenge_repeat_onSpec, S.indImpl_challenge_repeat_onSpec]
-    | none =>
-      rw [S.indImpl_challenge_none_onSpec, S.indImpl_challenge_none_onSpec]
-      simp only [h0]
-
 end TCSlib.Cryptography.Composability.NMCCA2
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability/Forward.lean b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability/Forward.lean
index f854ae60f..cb97e77e3 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability/Forward.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability/Forward.lean
@@ -2,7 +2,7 @@
 Copyright (c) 2026 TCSlib contributors. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 -/
-import TCSlib.Cryptography.Games.Efficiency
+import TCSlib.Cryptography.Games.Forwarding
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
@@ -13,27 +13,25 @@ set_option autoImplicit false
 
 Both reductions of [PS10, Theorem 175.9] run the adversary once against the reduction's own
 oracles: every query is **forwarded** unchanged to the outer oracle of the same index, and only
-the finalization differs. This file builds that handler once, generically in the oracle lengths
-(`fwdHandler`), as a `Games.InteractiveHandler` with one outer call per inner query and an empty
-state, so that T2 (`Games.exists_interactiveHandlerMachine`) makes it a machine. Its answers are
-the outer oracle's (`fwdHandler_impl`), so simulating it is running the adversary against the
-outer oracles (`simulate_fwdHandler_impl`).
-
-It also provides the readers of a finalization input `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩` (`finU`,
-`finZ`, `finW`, `finA`, `finL`) and of an encoded outer log: `logEmit G L` concatenates `G` of the
-successive suffixes of the nested log `L`, is polynomial-time for polynomial-time `G`
-(`polyTimeComputable_logEmit`), and on an encoded log is the concatenation of `G`'s values on the
-entries (`logEmit_encodeLog`).
+the finalization differs. That handler is `Games.fwdHandler`, with one outer call per inner query
+and an empty state, so that T2 (`Games.exists_interactiveHandlerMachine`) makes it a machine. Its
+answers are the outer oracle's (`Games.fwdHandler_impl`), so simulating it is running the
+adversary against the outer oracles (`simulate_fwdHandler_impl`).
+
+It also provides the readers of an encoded outer log: `logEmit G L` concatenates `G` of the
+successive suffixes of the nested log `L` (iterate and emit, `Games.iterEmit`), is polynomial-time
+for polynomial-time `G` (`polyTimeComputable_logEmit`), and on an encoded log is the concatenation
+of `G`'s values on the entries (`logEmit_encodeLog`). The readers of a finalization input are the
+published `Games.InteractiveHandler.rU`, `rZ`, `rW`, `rL` (with their `_finInput` lemmas) and
+`finA`.
 
 ## Main definitions
 
-* `NMCCA2.fwdHandler`: the forwarding handler with a given finalization.
-* `NMCCA2.finU`, `finZ`, `finW`, `finA`, `finL`: the fields of a finalization input.
 * `NMCCA2.logEmit`: concatenated readings of the suffixes of an encoded log.
 
 ## Main results
 
-* `NMCCA2.fwdHandler_impl`, `NMCCA2.simulate_fwdHandler_impl`: forwarding.
+* `NMCCA2.simulate_fwdHandler_impl`: simulating the forwarding handler.
 * `NMCCA2.polyTimeComputable_logEmit`, `NMCCA2.logEmit_encodeLog`.
 
 ## References
@@ -48,73 +46,7 @@ open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
 
 variable {k : ℕ}
 
-/-! ### Readers of a round input -/
-
-/-- The state `s` of a round input `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`. -/
-private def rState (w : List Bool) : List Bool := pairFstD (pairSndD w)
-/-- The oracle index `1^i` of a round input. -/
-private def rIdx (w : List Bool) : List Bool := pairFstD (pairFstD (pairSndD (pairSndD w)))
-/-- The query `x` of a round input. -/
-private def rQuery (w : List Bool) : List Bool := pairSndD (pairFstD (pairSndD (pairSndD w)))
-/-- The outer log `L` of the call so far. -/
-private def rLog (w : List Bool) : List Bool := pairSndD (pairSndD (pairSndD w))
-/-- The outer answer `y` recorded in a one-entry log `⟨⟨1^j, ⟨x, y⟩⟩, []⟩`. -/
-private def rAns (w : List Bool) : List Bool := pairSndD (pairSndD (pairFstD (rLog w)))
-
-/-- The fields of a round input (DL-30–34 overlap: the round-input readers). -/
-private theorem fields_input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
-    rState (InteractiveHandler.input n z ω s i x L) = s ∧
-      rIdx (InteractiveHandler.input n z ω s i x L) = List.replicate i true ∧
-      rQuery (InteractiveHandler.input n z ω s i x L) = x ∧
-      rLog (InteractiveHandler.input n z ω s i x L) = L := by
-  simp only [InteractiveHandler.input_eq, rState, rIdx, rQuery, rLog, pairFstD_pairEncode,
-    pairSndD_pairEncode, and_self]
-
-/-- **One forwarding round.** With an empty outer log, ask the outer oracle `i` the query `x`;
-with the outer answer `y` in the log, return `y` and keep the state. -/
-private def fwdRun (w : List Bool) : List Bool :=
-  if decide (rLog w = []) then pairEncode [false] (pairEncode (rIdx w) (rQuery w))
-  else pairEncode [true] (rAns w ++ rState w)
-
-/-- The forwarding round is polynomial-time. -/
-private theorem polyTimeComputable_fwdRun : PolyTimeComputable fwdRun := by
-  have hF := polyTimeComputable_pairFstD
-  have hD := polyTimeComputable_pairSndD
-  have hS : PolyTimeComputable rState := hF.comp hD
-  have hI : PolyTimeComputable rIdx := hF.comp (hF.comp (hD.comp hD))
-  have hX : PolyTimeComputable rQuery := hD.comp (hF.comp (hD.comp hD))
-  have hL : PolyTimeComputable rLog := hD.comp (hD.comp hD)
-  have hA : PolyTimeComputable rAns := hD.comp (hD.comp (hF.comp hL))
-  exact polyTimeComputable_ite (polyTimeComputable_isNil.comp hL)
-    ((polyTimeComputable_const [false]).pairEncode (hI.pairEncode hX))
-    ((polyTimeComputable_const [true]).pairEncode (hA.append hS))
-
-/-! ### The forwarding handler -/
-
-/-- **The forwarding handler** for `k` bit-string oracles with lengths `din`, `dout`, inner and
-outer alike: empty state, the seed of `seedLen(n)` bits, one outer call per inner query, which
-forwards the query to the outer oracle of the same index and returns its answer; the adversary's
-input `advIn`, and the finalization `finRun` with `outLen(n)`-bit output and at most `finCall(n)`
-outer queries. -/
-def fwdHandler (din dout : Fin k → PolyExpr) (seedLen : PolyExpr)
-    (advIn : List Bool → List Bool) (advIn_poly : PolyTimeComputable advIn)
-    (outLen finCall : PolyExpr) (finRun : List Bool → List Bool)
-    (finRun_poly : PolyTimeComputable finRun) : InteractiveHandler k din dout k din dout where
-  stateLen := .const 0
-  seedLen := seedLen
-  perCall := .const 1
-  init _ := zeroBits _
-  run := fwdRun
-  poly := polyTimeComputable_fwdRun
-  advIn := advIn
-  advIn_poly := advIn_poly
-  outLen := outLen
-  finCall := finCall
-  finRun := finRun
-  finRun_poly := finRun_poly
-
-attribute [simps (config := { isSimp := false }) stateLen seedLen perCall init advIn outLen finCall
-  finRun] fwdHandler
+/-! ### Simulating the forwarding handler -/
 
 section Forward
 
@@ -122,63 +54,11 @@ variable (din dout : Fin k → PolyExpr) (seedLen : PolyExpr) (advIn : List Bool
   (advIn_poly : PolyTimeComputable advIn) (outLen finCall : PolyExpr)
   (finRun : List Bool → List Bool) (finRun_poly : PolyTimeComputable finRun)
 
-/-- **The forwarding handler forwards:** the inner query `x` to oracle `i` in state `s` is the
-outer query `x` to oracle `i`, answered with the outer answer `y` and the state kept:
-`H.impl n z ω i x s = query i x (fun y => pure (y, s))`.
-
-**Proof sketch.** The call's first round has an empty outer log, so it is the query
-`⟨[false], ⟨1^i, x⟩⟩` (`decodeBitMove_query`); its second round reads the answer `y` from the
-one-entry log and returns `y ‖ s` (`decodeBitMove_ret`), which `impl` splits back into `y` and
-`s` (`Fin.append_left`, `Fin.append_right`). -/
-theorem fwdHandler_impl (n : ℕ) (z : List Bool)
-    (ω : Fin ((fwdHandler din dout seedLen advIn advIn_poly outLen finCall finRun
-      finRun_poly).seedLen.eval n) → Bool) (i : Fin k) (x : Fin ((din i).eval n) → Bool)
-    (s : Fin ((fwdHandler din dout seedLen advIn advIn_poly outLen finCall finRun
-      finRun_poly).stateLen.eval n) → Bool) :
-    (fwdHandler din dout seedLen advIn advIn_poly outLen finCall finRun finRun_poly).impl n z ω
-        i x s = .query i x fun y => .pure (y, s) := by
-  rw [InteractiveHandler.impl_apply, InteractiveHandler.call_eq, fwdHandler_perCall,
-    PolyExpr.eval_const]
-  rw [buildComp_succ_of_query (i := i) (x := x) (by
-    show decodeBitMove _ _ _ (fwdRun _) = _
-    obtain ⟨-, hI, hX, hL⟩ := fields_input (k := k) n z (List.ofFn ω) (List.ofFn s) i
-      (List.ofFn x)
-      ((bitCodec (fun j => (din j).eval n) (fun j => (dout j).eval n) 0).encodeLog [])
-    rw [fwdRun, hI, hX, hL, MachineCodec.encodeLog_nil, if_pos (decide_eq_true rfl)]
-    exact decodeBitMove_query (fun j => (din j).eval n) (fun j => (dout j).eval n) _ i x),
-    OracleComp.query_bind]
-  congr 1
-  funext y
-  rw [buildComp_zero_of_ret (a := Fin.append y s) (by
-    show decodeBitMove _ _ _ (fwdRun _) = _
-    obtain ⟨hS, -, -, hL⟩ := fields_input (k := k) n z (List.ofFn ω) (List.ofFn s) i
-      (List.ofFn x)
-      ((bitCodec (fun j => (din j).eval n) (fun j => (dout j).eval n) 0).encodeLog
-        ([] ++ [⟨i, x, y⟩]))
-    have hlog : (bitCodec (fun j => (din j).eval n) (fun j => (dout j).eval n) 0).encodeLog
-        ([] ++ [⟨i, x, y⟩]) = pairEncode (pairEncode (List.replicate i true)
-          (pairEncode (List.ofFn x) (List.ofFn y))) [] := by
-      rw [List.nil_append, MachineCodec.encodeLog_cons, MachineCodec.encodeLog_nil,
-        bitCodec_encodeEntry]
-    have hA : rAns (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x)
-        ((bitCodec (fun j => (din j).eval n) (fun j => (dout j).eval n) 0).encodeLog
-          ([] ++ [⟨i, x, y⟩]))) = List.ofFn y := by
-      rw [rAns, hL, hlog, pairFstD_pairEncode, pairSndD_pairEncode, pairSndD_pairEncode]
-    rw [fwdRun, hA, hS, hL, hlog, if_neg (fun h => pairEncode_ne_nil _ _ (of_decide_eq_true h)),
-      ← List.ofFn_fin_append]
-    exact decodeBitMove_ret _ _ _ _)]
-  rw [OracleComp.pure_bind]
-  congr 2
-  · funext j
-    exact Fin.append_left y s j
-  · funext j
-    exact Fin.append_right y s j
-
 /-- **Simulating the forwarding handler is running the computation:** for every computation
 `c` against the oracles and every state `s`, `simulate (H.impl n z ω) c s = c.bind (fun a =>
 pure (a, s))`.
 
-**Proof sketch.** Induction on `c`, with `fwdHandler_impl` at each query. -/
+**Proof sketch.** Induction on `c`, with `Games.fwdHandler_impl` at each query. -/
 theorem simulate_fwdHandler_impl (n : ℕ) (z : List Bool)
     (ω : Fin ((fwdHandler din dout seedLen advIn advIn_poly outLen finCall finRun
       finRun_poly).seedLen.eval n) → Bool) {α : Type}
@@ -198,129 +78,32 @@ theorem simulate_fwdHandler_impl (n : ℕ) (z : List Bool)
 
 end Forward
 
-/-! ### Readers of a finalization input -/
-
-/-- The parameter `1^n` of a finalization input `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩`. -/
-def finU (w : List Bool) : List Bool := pairFstD (pairFstD w)
-
-/-- `finU w = pairFstD (pairFstD w)`. -/
-theorem finU_eq (w : List Bool) : finU w = pairFstD (pairFstD w) := rfl
-
-/-- The reduction input `z` of a finalization input. -/
-def finZ (w : List Bool) : List Bool := pairFstD (pairSndD (pairFstD w))
-
-/-- `finZ w = pairFstD (pairSndD (pairFstD w))`. -/
-theorem finZ_eq (w : List Bool) : finZ w = pairFstD (pairSndD (pairFstD w)) := rfl
-
-/-- The seed `ω` of a finalization input. -/
-def finW (w : List Bool) : List Bool := pairSndD (pairSndD (pairFstD w))
-
-/-- `finW w = pairSndD (pairSndD (pairFstD w))`. -/
-theorem finW_eq (w : List Bool) : finW w = pairSndD (pairSndD (pairFstD w)) := rfl
-
-/-- The adversary's output `a` of a finalization input. -/
-def finA (w : List Bool) : List Bool := pairFstD (pairSndD (pairSndD w))
-
-/-- `finA w = pairFstD (pairSndD (pairSndD w))`. -/
-theorem finA_eq (w : List Bool) : finA w = pairFstD (pairSndD (pairSndD w)) := rfl
-
-/-- The outer log `L` of the finalization so far. -/
-def finL (w : List Bool) : List Bool := pairSndD (pairSndD (pairSndD w))
-
-/-- `finL w = pairSndD (pairSndD (pairSndD w))`. -/
-theorem finL_eq (w : List Bool) : finL w = pairSndD (pairSndD (pairSndD w)) := rfl
-
-/-- **The fields of a finalization input:** on `finInput n z ω s a L = ⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a,
-L⟩⟩⟩` the readers return `1^n`, `z`, `ω`, `a` and `L`. -/
-theorem fields_finInput (n : ℕ) (z ω s a L : List Bool) :
-    finU (InteractiveHandler.finInput n z ω s a L) = List.replicate n true ∧
-      finZ (InteractiveHandler.finInput n z ω s a L) = z ∧
-      finW (InteractiveHandler.finInput n z ω s a L) = ω ∧
-      finA (InteractiveHandler.finInput n z ω s a L) = a ∧
-      finL (InteractiveHandler.finInput n z ω s a L) = L := by
-  simp only [InteractiveHandler.finInput_eq, seedIn_eq, finU, finZ, finW, finA, finL,
-    pairFstD_pairEncode, pairSndD_pairEncode, and_self]
-
-/-- The finalization-input readers are polynomial-time: `PolyTimeComputable finU`, and the same
-for `finZ`, `finW`, `finA` and `finL`. -/
-theorem polyTimeComputable_finFields :
-    PolyTimeComputable finU ∧ PolyTimeComputable finZ ∧ PolyTimeComputable finW ∧
-      PolyTimeComputable finA ∧ PolyTimeComputable finL := by
-  have hF := polyTimeComputable_pairFstD
-  have hD := polyTimeComputable_pairSndD
-  exact ⟨hF.comp hF, hF.comp (hD.comp hF), hD.comp (hD.comp hF), hF.comp (hD.comp hD),
-    hD.comp (hD.comp hD)⟩
-
 /-! ### Readers of an encoded log -/
 
 /-- **Concatenated readings of an encoded log:** `G` applied to the successive suffixes
 `L, snd L, snd (snd L), …` of the nested log `L = ⟨e₁, ⟨e₂, ⟨…, []⟩⟩⟩`, for `|L| + 1` steps, and
-concatenated: `logEmit G L = (List.range (|L| + 1)).flatMap fun i => G (pairSndD^[i] L)`. -/
+concatenated: iterate and emit (`Games.iterEmit`) with the step `pairSndD`,
+`logEmit G L = (List.range (|L| + 1)).flatMap fun i => G (pairSndD^[i] L)`. -/
 def logEmit (G : List Bool → List Bool) (L : List Bool) : List Bool :=
-  (List.range (L.length + 1)).flatMap fun i => G (pairSndD^[i] L)
+  iterEmit pairSndD G (L.length + 1) L
 
-/-- `logEmit G L = (List.range (|L| + 1)).flatMap fun i => G (pairSndD^[i] L)`. -/
+/-- `logEmit G L = (List.range (|L| + 1)).flatMap fun i => G (pairSndD^[i] L)`
+(`Games.iterEmit_eq`). -/
 theorem logEmit_eq (G : List Bool → List Bool) (L : List Bool) :
-    logEmit G L = (List.range (L.length + 1)).flatMap fun i => G (pairSndD^[i] L) := rfl
-
-/-- The iterated second projection never lengthens a word. -/
-private theorem length_iterate_pairSndD_le (L : List Bool) (i : ℕ) :
-    (pairSndD^[i] L).length ≤ L.length := by
-  induction i with
-  | zero => exact le_rfl
-  | succ i ih =>
-    rw [Function.iterate_succ_apply']
-    exact (length_pairSndD_le _).trans ih
+    logEmit G L = (List.range (L.length + 1)).flatMap fun i => G (pairSndD^[i] L) := by
+  rw [logEmit, iterEmit_eq]
 
 /-- **The readings of an encoded log are polynomial-time** when `G` is
-(`Complexity.polyTimeComputable_iterateEmit` with the step `pairSndD`, which never lengthens a
-word, and `|L|` rounds). -/
+(`Games.polyTimeComputable_iterEmit` with the step `pairSndD`, which never lengthens a word). -/
 theorem polyTimeComputable_logEmit {G : List Bool → List Bool} (hG : PolyTimeComputable G) :
     PolyTimeComputable (logEmit G) :=
-  (polyTimeComputable_iterateEmit polyTimeComputable_pairSndD hG .var .var
-    (fun x i _ => by rw [PolyExpr.eval_var]; exact length_iterate_pairSndD_le x i)).congr
-    fun L => by rw [PolyExpr.eval_var, logEmit_eq]
+  (polyTimeComputable_iterEmit polyTimeComputable_pairSndD hG 0
+    fun y => (length_pairSndD_le y).trans (le_max_left _ _)).congr fun L => by rw [logEmit]
 
 section LogEmit
 
 variable {ι : Type} {spec : OracleSpec ι} {α : Type}
 
-/-- The second projection of an encoded log drops its first entry. -/
-private theorem iterate_pairSndD_encodeLog (codec : MachineCodec spec α) (h : QueryLog spec)
-    (i : ℕ) : pairSndD^[i] (codec.encodeLog h) = codec.encodeLog (h.drop i) := by
-  induction i generalizing h with
-  | zero => rfl
-  | succ i ih =>
-    rw [Function.iterate_succ_apply]
-    cases h with
-    | nil =>
-      rw [MachineCodec.encodeLog_nil, pairSndD_of_pairDecode_eq_none pairDecode_nil,
-        ← MachineCodec.encodeLog_nil codec, ih, List.drop_nil, List.drop_nil]
-    | cons e t =>
-      rw [MachineCodec.encodeLog_cons, pairSndD_pairEncode, ih, List.drop_succ_cons]
-
-/-- Reading the suffixes of a log within at least its number of steps. -/
-private theorem flatMap_range_drop (codec : MachineCodec spec α) (G : List Bool → List Bool)
-    (g : (Σ i, spec.dom i × spec.rng i) → List Bool) (hnil : G [] = [])
-    (hcons : ∀ e t, G (pairEncode (codec.encodeEntry e) t) = g e) :
-    ∀ (h : QueryLog spec) (m : ℕ), h.length ≤ m →
-      ((List.range m).flatMap fun i => G (codec.encodeLog (h.drop i))) = h.flatMap g := by
-  intro h
-  induction h with
-  | nil =>
-    intro m _
-    rw [List.flatMap_nil]
-    refine List.flatMap_eq_nil_iff.2 fun i _ => ?_
-    rw [List.drop_nil, MachineCodec.encodeLog_nil, hnil]
-  | cons e t ih =>
-    intro m hm
-    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by rw [List.length_cons] at hm; omega⟩
-    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, List.drop_zero,
-      MachineCodec.encodeLog_cons, hcons, List.flatMap_cons]
-    congr 1
-    simp only [List.drop_succ_cons]
-    exact ih m' (by rw [List.length_cons] at hm; omega)
-
 /-- An encoded log is at least as long as its number of entries. -/
 private theorem length_le_length_encodeLog (codec : MachineCodec spec α) (h : QueryLog spec) :
     h.length ≤ (codec.encodeLog h).length := by
@@ -334,16 +117,23 @@ private theorem length_le_length_encodeLog (codec : MachineCodec spec α) (h : Q
 reads only the first entry of a nonempty log, `G ⟨⟦e⟧, t⟩ = g e`, then
 `logEmit G (codec.encodeLog h) = h.flatMap g`.
 
-**Proof sketch.** The `i`-th suffix of the encoded log encodes `h.drop i`; the first `|h|`
-readings are `g` of the entries and the rest are `G [] = []`, since `|h| ≤ |L|`. -/
+**Proof sketch.** `Games.iterEmit_encode` with the encoding `codec.encodeLog`: `pairSndD` drops
+the first entry of an encoded log (`MachineCodec.encodeLog_cons`) and fixes the empty one, and
+`|h| ≤ |L|` (`length_le_length_encodeLog`). -/
 theorem logEmit_encodeLog (codec : MachineCodec spec α) (G : List Bool → List Bool)
     (g : (Σ i, spec.dom i × spec.rng i) → List Bool) (hnil : G [] = [])
     (hcons : ∀ e t, G (pairEncode (codec.encodeEntry e) t) = g e) (h : QueryLog spec) :
     logEmit G (codec.encodeLog h) = h.flatMap g := by
-  rw [logEmit_eq]
-  simp only [iterate_pairSndD_encodeLog]
-  exact flatMap_range_drop codec G g hnil hcons h _
-    (Nat.le_succ_of_le (length_le_length_encodeLog codec h))
+  rw [logEmit]
+  refine iterEmit_encode pairSndD G codec.encodeLog g h ?_ (fun e _ t => ?_) ?_
+    (fun e _ t => ?_) _ (Nat.le_succ_of_le (length_le_length_encodeLog codec h))
+  · rw [MachineCodec.encodeLog_nil]
+    exact pairSndD_of_pairDecode_eq_none pairDecode_nil
+  · rw [MachineCodec.encodeLog_cons, pairSndD_pairEncode]
+  · rw [MachineCodec.encodeLog_nil]
+    exact hnil
+  · rw [MachineCodec.encodeLog_cons]
+    exact hcons e _
 
 end LogEmit
 
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation.lean b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation.lean
index ef63d352c..cc2bfbc9c 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation.lean
@@ -536,8 +536,8 @@ theorem ofFn_snmEntry {n : ℕ} (sk : List Bool) (copy : Bool) (c : Fin (S.ctLen
 /-- **The real experiment's view is `realView`:** for an output `w` and a final state `s`,
 `snmView a (M.draw … a ρ) (d_i)_i (snmSigma w) = realView … ⟦w⟧ s`, with `a` the recorded parameter.
 
-**Proof sketch.** Block by block: `ofFn_block` for the ciphertexts, `decide_map_ofFn` for the
-copy test, `ofFn_snmEntry` for the entries and `ofFn_natAdd_eq_drop` for `σ`. -/
+**Proof sketch.** Block by block: `ofFn_block_eq_coinBlock` for the ciphertexts, `decide_map_ofFn`
+for the copy test, `ofFn_snmEntry` for the entries and `ofFn_natAdd_eq_drop` for `σ`. -/
 theorem snmView_realView (M : MsgSampler) (n r sl : ℕ) (sk : List Bool) (ρ : M.samp.Coins n)
     (w : Fin (r * S.ctLen.eval n + sl) → Bool) (s : S.SnmState M n) :
     S.snmView ((s.map Prod.snd).getD (zeroBits (M.paramLen.eval n)))
@@ -548,15 +548,16 @@ theorem snmView_realView (M : MsgSampler) (n r sl : ℕ) (sk : List Bool) (ρ :
   rw [snmView_eq, realView_eq, M.draw_eq, drawWith_eq, snmSigma_eq, ofFn_natAdd_eq_drop]
   congr 3
   refine ofFn_eq_map_range _ _ fun i => ?_
-  have hc : chunkAt (S.ctLen.eval n) i (List.ofFn w) = List.ofFn (S.snmCt w i) := by
-    rw [snmCt_eq, ofFn_block]
+  have hc : coinBlock (S.ctLen.eval n) i (List.ofFn w) = List.ofFn (S.snmCt w i) := by
+    rw [snmCt_eq, ofFn_block_eq_coinBlock]
   rw [hc, decide_map_ofFn, ofFn_snmEntry]
 
 /-- **The ideal experiment's view is `idealView`:** for an output `w` and the oracle's final state
 `sa`, `snmView a (M.draw … a ρ) (d_i)_i (snmSigma w) = idealView … ⟦w⟧ sa`.
 
-**Proof sketch.** Entry `i` of `w` is the block `chunkAt (ctLen(n) + 1) i ⟦w⟧` (`ofFn_block`),
-whose head is the `COPY` flag and whose tail is the ciphertext (`simEntry_fst`, `simEntry_snd`). -/
+**Proof sketch.** Entry `i` of `w` is the block `coinBlock (ctLen(n) + 1) i ⟦w⟧`
+(`ofFn_block_eq_coinBlock`), whose head is the `COPY` flag and whose tail is the ciphertext
+(`simEntry_fst`, `simEntry_snd`). -/
 theorem snmView_idealView (M : MsgSampler) (n r sl : ℕ) (sk : List Bool) (ρ : M.samp.Coins n)
     (w : Fin (r * (S.ctLen.eval n + 1) + sl) → Bool)
     (sa : Option (Fin (M.paramLen.eval n) → Bool)) :
@@ -567,9 +568,9 @@ theorem snmView_idealView (M : MsgSampler) (n r sl : ℕ) (sk : List Bool) (ρ :
   rw [snmView_eq, idealView_eq, M.draw_eq, drawWith_eq, snmSigma_eq, ofFn_natAdd_eq_drop]
   congr 3
   refine ofFn_eq_map_range _ _ fun i => ?_
-  have hc : chunkAt (S.ctLen.eval n + 1) i (List.ofFn w) =
+  have hc : coinBlock (S.ctLen.eval n + 1) i (List.ofFn w) =
       (S.simEntry w i).1 :: List.ofFn (S.simEntry w i).2 := by
-    rw [← ofFn_block, List.ofFn_succ, simEntry_fst]
+    rw [← ofFn_block_eq_coinBlock, List.ofFn_succ, simEntry_fst]
     exact congrArg _ (congrArg List.ofFn (funext fun j => (simEntry_snd S w i j).symm))
   rw [hc, List.headD_cons, List.tail_cons, ofFn_snmEntry]
 
@@ -751,11 +752,12 @@ Theorem 3, at one message]: Definition 172.6 implies SIM-NME′ under a chosen-p
    the real experiment (`castImpl_snmImpl`, `NMSim.realAcc_eq_hybAcc`).
 2. **The simulator** (`NMSim.exists_simulator`) runs `A` on `pk`, answering `Dec` with `⊥`. On `A`'s
    first challenge `a` it makes its only query `a`, gets `h(m)`, draws `m̃ = M(a; ρ̃)` with its own
-   coins and `M`'s advice (hard-wired, `exists_withAdviceOn`), and answers `⟨Enc_pk(m̃), h(m)⟩`;
-   repeated challenges get the recorded answer. It outputs `A`'s ciphertexts, each flagged `COPY`
-   iff it equals its dummy challenge, and `σ`; if `A` never asks it never queries. Its run at
-   budget `1` is its run at T2's budget (`NMSim.toCompOn_budget_eq`; it asks at most one query,
-   `NMSim.chalHandler_costBoundedBy`), and against the history oracle it is `H_true`.
+   coins and `M`'s advice (hard-wired, `NUPPT.exists_withAdviceOn`), and answers
+   `⟨Enc_pk(m̃), h(m)⟩`; repeated challenges get the recorded answer. It outputs `A`'s
+   ciphertexts, each flagged `COPY` iff it equals its dummy challenge, and `σ`; if `A` never asks
+   it never queries. Its run at budget `1` is its run at T2's budget (`NUPPT.toCompOn_budget_eq`;
+   it asks at most one query, `NMSim.chalHandler_costBoundedBy`), and against the history oracle
+   it is `H_true`.
 3. **The NM adversary** `B` (`NMSim.exists_nmAdversary`) runs `A`; on `a` it draws `m, m̃ ← M(a)`,
    asks its challenge on `⟨m, m̃⟩`, receives `y = Enc_pk(m_b)` and answers `A` with `⟨y, h(m)⟩`. It
    outputs each of `A`'s ciphertexts followed by the pair
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Challenge.lean b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Challenge.lean
index 8915ae42d..d247dab72 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Challenge.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Challenge.lean
@@ -45,6 +45,10 @@ states (`chalState`) and that a whole run asks at most one outer query
 namespace TCSlib.Cryptography.Composability.NMSim
 
 open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
+open TCSlib.Cryptography.Games.InteractiveHandler (rU rZ rW rS rI rX rL rAns finA)
+open TCSlib.Cryptography.Games.InteractiveHandler (rU_input rS_input rI_input rX_input rL_input
+  polyTimeComputable_rU polyTimeComputable_rS polyTimeComputable_rI polyTimeComputable_rX
+  polyTimeComputable_rL)
 
 variable (S : FixedLengthPKScheme)
 
@@ -67,19 +71,19 @@ structure ChalParams (pl hl : PolyExpr) (k' : ℕ) (din' dout' : Fin k' → Poly
   /-- It is polynomial-time. -/
   qry_poly : PolyTimeComputable qry
   /-- It has the outer query length. -/
-  qry_len : ∀ w, (qry w).length = (din' j).eval (rdU w).length
+  qry_len : ∀ w, (qry w).length = (din' j).eval (rU w).length
   /-- The ciphertext part of the answer, from the round input with the outer answer. -/
   ansY : List Bool → List Bool
   /-- It is polynomial-time. -/
   ansY_poly : PolyTimeComputable ansY
   /-- It has `ctLen(n)` bits. -/
-  ansY_len : ∀ w, (ansY w).length = S.ctLen.eval (rdU w).length
+  ansY_len : ∀ w, (ansY w).length = S.ctLen.eval (rU w).length
   /-- The history part of the answer, from the round input with the outer answer. -/
   ansH : List Bool → List Bool
   /-- It is polynomial-time. -/
   ansH_poly : PolyTimeComputable ansH
   /-- It has `hl(n)` bits. -/
-  ansH_len : ∀ w, (ansH w).length = hl.eval (rdU w).length
+  ansH_len : ∀ w, (ansH w).length = hl.eval (rU w).length
   /-- The length of the output. -/
   outLen : PolyExpr
   /-- The bound on the outer queries of the finalization. -/
@@ -97,17 +101,17 @@ challenge with the flag set returns the recorded `⟨Y, H⟩`; otherwise, with a
 asks `qry w` to the outer oracle `j`, and with the answer in the log it returns `⟨Y, H⟩` and the
 state `[true] ‖ Y ‖ H ‖ x`. -/
 def chalRun (P : ChalParams S pl hl k' din' dout') (w : List Bool) : List Bool :=
-  if decide (rdIdx w = []) then
-    pairEncode [true] (List.replicate ((S.msgLen.add (.const 1)).eval (rdU w).length) false ++
-      rdState w)
-  else if (rdState w).headD false then
-    pairEncode [true] (((rdState w).drop 1).take ((S.ctLen.add hl).eval (rdU w).length) ++
-      rdState w)
-  else if decide (rdLog w = []) then
+  if decide (rI w = []) then
+    pairEncode [true] (List.replicate ((S.msgLen.add (.const 1)).eval (rU w).length) false ++
+      rS w)
+  else if (rS w).headD false then
+    pairEncode [true] (((rS w).drop 1).take ((S.ctLen.add hl).eval (rU w).length) ++
+      rS w)
+  else if decide (rL w = []) then
     pairEncode [false] (pairEncode (List.replicate P.j true) (P.qry w))
   else
     pairEncode [true] (P.ansY w ++ P.ansH w ++
-      (true :: (P.ansY w ++ P.ansH w ++ EnsembleLemmas.padL (pl.eval (rdU w).length) (rdQuery w))))
+      (true :: (P.ansY w ++ P.ansH w ++ EnsembleLemmas.padL (pl.eval (rU w).length) (rX w))))
 
 /-- `chalRun P w` is `⟨[true], 0^{msgLen+1} ‖ s⟩` if `i = 0`; else
 `⟨[true], (s.drop 1).take (ctLen + hl) ‖ s⟩` if the flag is set; else
@@ -115,22 +119,26 @@ def chalRun (P : ChalParams S pl hl k' din' dout') (w : List Bool) : List Bool :
 `⟨[true], Y ‖ H ‖ (true :: Y ‖ H ‖ padL pl x)⟩`, with `Y = ansY w` and `H = ansH w`. -/
 theorem chalRun_eq (P : ChalParams S pl hl k' din' dout') (w : List Bool) :
     chalRun P w =
-      if decide (rdIdx w = []) then
-        pairEncode [true] (List.replicate ((S.msgLen.add (.const 1)).eval (rdU w).length) false ++
-          rdState w)
-      else if (rdState w).headD false then
-        pairEncode [true] (((rdState w).drop 1).take ((S.ctLen.add hl).eval (rdU w).length) ++
-          rdState w)
-      else if decide (rdLog w = []) then
+      if decide (rI w = []) then
+        pairEncode [true] (List.replicate ((S.msgLen.add (.const 1)).eval (rU w).length) false ++
+          rS w)
+      else if (rS w).headD false then
+        pairEncode [true] (((rS w).drop 1).take ((S.ctLen.add hl).eval (rU w).length) ++
+          rS w)
+      else if decide (rL w = []) then
         pairEncode [false] (pairEncode (List.replicate P.j true) (P.qry w))
       else
         pairEncode [true] (P.ansY w ++ P.ansH w ++ (true :: (P.ansY w ++ P.ansH w ++
-          EnsembleLemmas.padL (pl.eval (rdU w).length) (rdQuery w)))) := rfl
+          EnsembleLemmas.padL (pl.eval (rU w).length) (rX w)))) := rfl
 
 /-- The round is polynomial-time. -/
 theorem polyTimeComputable_chalRun (P : ChalParams S pl hl k' din' dout') :
     PolyTimeComputable (chalRun P) := by
-  obtain ⟨hU, -, -, hS, hI, hQ, hL, -⟩ := polyTimeComputable_rd
+  have hU := polyTimeComputable_rU
+  have hS := polyTimeComputable_rS
+  have hI := polyTimeComputable_rI
+  have hQ := polyTimeComputable_rX
+  have hL := polyTimeComputable_rL
   have hT := polyTimeComputable_const [true]
   have hY := P.ansY_poly
   have hH := P.ansH_poly
@@ -245,9 +253,13 @@ theorem chalHandler_impl_dec (x : Fin ((snmDin S pl 0).eval n) → Bool)
     (o : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (hl.eval n) → Bool) ×
       (Fin (pl.eval n) → Bool))) :
     (chalHandler P).impl n z ω 0 x (chalState P n o) = .pure (zeroBits _, chalState P n o) := by
-  obtain ⟨hU, -, -, hS, hI, -, -⟩ := fields_input (k := 2) n z (List.ofFn ω)
+  have hU := rU_input (k := 2) n z (List.ofFn ω)
     (List.ofFn (chalState P n o)) 0 (List.ofFn x) []
-  rw [impl_of_ret (chalHandler P) n z ω 0 x (chalState P n o)
+  have hS := rS_input (k := 2) n z (List.ofFn ω)
+    (List.ofFn (chalState P n o)) 0 (List.ofFn x) []
+  have hI := rI_input (k := 2) n z (List.ofFn ω)
+    (List.ofFn (chalState P n o)) 0 (List.ofFn x) []
+  rw [InteractiveHandler.impl_of_ret_padFin (chalHandler P) n z ω 0 x (chalState P n o)
     (List.replicate ((S.msgLen.add (.const 1)).eval n) false) (List.ofFn (chalState P n o))
     (by rw [List.length_replicate, snmDout_zero]) List.length_ofFn (by
       show chalRun P _ = _
@@ -259,14 +271,18 @@ theorem chalHandler_impl_some (x : Fin ((snmDin S pl 1).eval n) → Bool)
     (y : Fin (S.ctLen.eval n) → Bool) (h : Fin (hl.eval n) → Bool) (a : Fin (pl.eval n) → Bool) :
     (chalHandler P).impl n z ω 1 x (chalState P n (some (y, h, a))) =
       .pure (padFin _ (List.ofFn y ++ List.ofFn h), chalState P n (some (y, h, a))) := by
-  obtain ⟨hU, -, -, hS, hI, -, -⟩ := fields_input (k := 2) n z (List.ofFn ω)
+  have hU := rU_input (k := 2) n z (List.ofFn ω)
+    (List.ofFn (chalState P n (some (y, h, a)))) 1 (List.ofFn x) []
+  have hS := rS_input (k := 2) n z (List.ofFn ω)
+    (List.ofFn (chalState P n (some (y, h, a)))) 1 (List.ofFn x) []
+  have hI := rI_input (k := 2) n z (List.ofFn ω)
     (List.ofFn (chalState P n (some (y, h, a)))) 1 (List.ofFn x) []
   have hans : ((List.ofFn (chalState P n (some (y, h, a)))).drop 1).take
       ((S.ctLen.add hl).eval n) = List.ofFn y ++ List.ofFn h := by
     rw [ofFn_chalState_some, List.drop_one, List.tail_cons, PolyExpr.eval_add]
     exact List.take_left' (by rw [List.length_append, List.length_ofFn, List.length_ofFn])
-  rw [impl_of_ret (chalHandler P) n z ω 1 x _ (List.ofFn y ++ List.ofFn h)
-    (List.ofFn (chalState P n (some (y, h, a))))
+  rw [InteractiveHandler.impl_of_ret_padFin (chalHandler P) n z ω 1 x _
+    (List.ofFn y ++ List.ofFn h) (List.ofFn (chalState P n (some (y, h, a))))
     (by rw [List.length_append, List.length_ofFn, List.length_ofFn, snmDout_one, PolyExpr.eval_add])
     List.length_ofFn (by
       show chalRun P _ = _
@@ -278,11 +294,11 @@ theorem chalHandler_impl_some (x : Fin ((snmDin S pl 1).eval n) → Bool)
 answers `⟨Y, H⟩ = ⟨ansY w₁, ansH w₁⟩` (`w₁` the round input with `y` in the log), recording
 `⟨Y, H, x⟩`.
 
-**Proof sketch.** `impl_of_query` with the answer `ansY w₁ ‖ ansH w₁` and the encoded state
-`chalState (some ⟨Y, H, x⟩)` (lengths by `ansY_len`, `ansH_len`; `perCall = 1`). The first
-round, on `w₀` (a challenge, flag unset, empty log), is the query branch of `chalRun_eq`; the
-second, on `w₁`, is its answer branch, with `x` read back through `padL`
-(`ofFn_chalState_some`, `ofFn_padFin_of_length`). -/
+**Proof sketch.** `InteractiveHandler.impl_of_query_padFin` with the answer `ansY w₁ ‖ ansH w₁`
+and the encoded state `chalState (some ⟨Y, H, x⟩)` (lengths by `ansY_len`, `ansH_len`;
+`perCall = 1`). The first round, on `w₀` (a challenge, flag unset, empty log), is the query
+branch of `chalRun_eq`; the second, on `w₁`, is its answer branch, with `x` read back through
+`padL` (`ofFn_chalState_some`, `ofFn_padFin_of_length`). -/
 theorem chalHandler_impl_none (x : Fin ((snmDin S pl 1).eval n) → Bool) :
     (chalHandler P).impl n z ω 1 x (chalState P n none) =
       .query P.j (padFin _ (P.qry (InteractiveHandler.input n z (List.ofFn ω)
@@ -315,7 +331,13 @@ theorem chalHandler_impl_none (x : Fin ((snmDin S pl 1).eval n) → Bool) :
             padFin (pl.eval n) (List.ofFn x)))) := by
   set w₀ := InteractiveHandler.input n z (List.ofFn ω) (List.ofFn (chalState P n none)) (1 : Fin 2)
     (List.ofFn x) [] with hw₀
-  obtain ⟨hU₀, -, -, hS₀, hI₀, -, hL₀⟩ := fields_input (k := 2) n z (List.ofFn ω)
+  have hU₀ := rU_input (k := 2) n z (List.ofFn ω)
+    (List.ofFn (chalState P n none)) (1 : Fin 2) (List.ofFn x) []
+  have hS₀ := rS_input (k := 2) n z (List.ofFn ω)
+    (List.ofFn (chalState P n none)) (1 : Fin 2) (List.ofFn x) []
+  have hI₀ := rI_input (k := 2) n z (List.ofFn ω)
+    (List.ofFn (chalState P n none)) (1 : Fin 2) (List.ofFn x) []
+  have hL₀ := rL_input (k := 2) n z (List.ofFn ω)
     (List.ofFn (chalState P n none)) (1 : Fin 2) (List.ofFn x) []
   have hq : List.ofFn (padFin ((din' P.j).eval n) (P.qry w₀)) = P.qry w₀ :=
     ofFn_padFin_of_length (by rw [P.qry_len, hU₀, List.length_replicate])
@@ -335,10 +357,11 @@ theorem chalHandler_impl_none (x : Fin ((snmDin S pl 1).eval n) → Bool) :
       (pairEncode (pairEncode (List.replicate P.j true) (pairEncode (P.qry w₀) (List.ofFn y))) [])
     with hW₁
   have hY : ∀ y, (P.ansY (W₁ y)).length = S.ctLen.eval n := fun y => by
-    rw [P.ansY_len, hW₁, (fields_input (k := 2) n z _ _ 1 _ _).1, List.length_replicate]
+    rw [P.ansY_len, hW₁, rU_input (k := 2) n z _ _ 1 _ _, List.length_replicate]
   have hH : ∀ y, (P.ansH (W₁ y)).length = hl.eval n := fun y => by
-    rw [P.ansH_len, hW₁, (fields_input (k := 2) n z _ _ 1 _ _).1, List.length_replicate]
-  rw [impl_of_query (chalHandler P) n z ω 1 x (chalState P n none) P.j (padFin _ (P.qry w₀))
+    rw [P.ansH_len, hW₁, rU_input (k := 2) n z _ _ 1 _ _, List.length_replicate]
+  rw [InteractiveHandler.impl_of_query_padFin (chalHandler P) n z ω 1 x (chalState P n none) P.j
+    (padFin _ (P.qry w₀))
     (fun y => P.ansY (W₁ y) ++ P.ansH (W₁ y))
     (fun y => List.ofFn (chalState P n (some (padFin _ (P.ansY (W₁ y)), padFin _ (P.ansH (W₁ y)),
       padFin (pl.eval n) (List.ofFn x)))))
@@ -351,7 +374,19 @@ theorem chalHandler_impl_none (x : Fin ((snmDin S pl 1).eval n) → Bool) :
     rw [chalRun_eq, hI₀, hU₀, hS₀, hL₀, List.length_replicate, headD_ofFn_chalState, hq]
     rfl
   · rw [hq]
-    obtain ⟨hU₁, -, -, hS₁, hI₁, hQ₁, hL₁⟩ := fields_input (k := 2) n z (List.ofFn ω)
+    have hU₁ := rU_input (k := 2) n z (List.ofFn ω)
+      (List.ofFn (chalState P n none)) (1 : Fin 2) (List.ofFn x)
+      (pairEncode (pairEncode (List.replicate P.j true) (pairEncode (P.qry w₀) (List.ofFn y))) [])
+    have hS₁ := rS_input (k := 2) n z (List.ofFn ω)
+      (List.ofFn (chalState P n none)) (1 : Fin 2) (List.ofFn x)
+      (pairEncode (pairEncode (List.replicate P.j true) (pairEncode (P.qry w₀) (List.ofFn y))) [])
+    have hI₁ := rI_input (k := 2) n z (List.ofFn ω)
+      (List.ofFn (chalState P n none)) (1 : Fin 2) (List.ofFn x)
+      (pairEncode (pairEncode (List.replicate P.j true) (pairEncode (P.qry w₀) (List.ofFn y))) [])
+    have hQ₁ := rX_input (k := 2) n z (List.ofFn ω)
+      (List.ofFn (chalState P n none)) (1 : Fin 2) (List.ofFn x)
+      (pairEncode (pairEncode (List.replicate P.j true) (pairEncode (P.qry w₀) (List.ofFn y))) [])
+    have hL₁ := rL_input (k := 2) n z (List.ofFn ω)
       (List.ofFn (chalState P n none)) (1 : Fin 2) (List.ofFn x)
       (pairEncode (pairEncode (List.replicate P.j true) (pairEncode (P.qry w₀) (List.ofFn y))) [])
     show chalRun P (W₁ y) = _
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Generic.lean b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Generic.lean
index 357c11533..1cbb4d1d4 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Generic.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Generic.lean
@@ -10,21 +10,20 @@ set_option relaxedAutoImplicit false
 set_option autoImplicit false
 
 /-!
-# Generic tools for Theorem 174.8
+# Chunk maps for Theorem 174.8
 
-Three generic facts used by both directions of [PS10, Theorem 174.8]. None of them is specific
-to encryption.
+A generic tool used by both directions of [PS10, Theorem 174.8], not specific to encryption:
+**chunk maps** (`chunkMap`), a polynomial-time map applied to the consecutive fixed-length chunks
+of a string, concatenated (`polyTimeComputable_chunkMap`, `chunkMap_flatten`): an instance of
+iterate and emit (`Games.iterEmit`). The machines of
+both reductions read and write their tuples of ciphertexts and entries this way.
 
-* **Budget reduction** (`buildComp_budget_eq`, `toCompOn_budget_eq`). A machine's computation at
-  budget `K ≥ j` that makes at most `j` queries on every path is its computation at budget `j`.
-  The simulator of the ideal experiment runs at budget `1`, while T2 builds it at a polynomial
-  budget.
-* **One-shot coins drawn in advance** (`expect_simulate_eager`). An implementation that samples
-  coins `t` at most once, on the call that leaves the "unused" states, has the law of the
-  implementations with `t` fixed in advance, averaged over `t`.
-* **Chunk maps** (`chunkMap`). A polynomial-time map applied to the consecutive fixed-length
-  chunks of a string, concatenated (`polyTimeComputable_chunkMap`, `chunkMap_flatten`). The
-  machines of both reductions read and write their tuples of ciphertexts and entries this way.
+The other generic facts first proved here now live in the Games layer: budget reduction
+(`Games.buildComp_budget_eq`, `Complexity.NUPPT.toCompOn_budget_eq`), output-length transport
+(`Games.expect_toCompOn_outLen`), reasoning on the possible outputs
+(`Games.ProbComp.expect_congr_of_allOutputs`, `Games.ProbComp.expect_expect_sample`,
+`Games.OracleComp.bind_congr_of_allOutputs`), one-shot coins drawn in advance
+(`Games.expect_simulate_eager`) and equal until bad in expectation (`Games.expect_eq_until_bad`).
 
 ## Main definitions
 
@@ -32,12 +31,6 @@ to encryption.
 
 ## Main results
 
-* `NMSim.buildComp_budget_eq`, `NMSim.toCompOn_budget_eq`.
-* `NMSim.expect_toCompOn_outLen`: a machine's output length may be changed along an equality.
-* `NMSim.expect_congr_of_allOutputs`, `NMSim.expect_expect_sample`,
-  `NMSim.bind_congr_of_allOutputs`.
-* `NMSim.expect_simulate_eager`.
-* `NMSim.expect_eq_until_bad`: equal until bad, for functions of the final state.
 * `NMSim.polyTimeComputable_chunkMap`, `NMSim.chunkMap_flatten`.
 
 ## References
@@ -50,234 +43,6 @@ namespace TCSlib.Cryptography.Composability.NMSim
 
 open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
 
-/-! ### Budget reduction -/
-
-section Budget
-
-variable {ι α : Type} {spec : OracleSpec ι}
-
-/-- **Budget reduction for `buildComp`.** If the computation of `next` at budget `K` from the log
-`hist` makes at most `j ≤ K` queries on every path, it is the computation at budget `j`:
-`buildComp next t j hist = buildComp next t K hist`.
-
-**Proof sketch.** Induction on `j`. A final output is the same at every budget. A query at budget
-`K` costs `1 ≤ j`, so `j = j' + 1` and `K = K' + 1`; both computations ask the same query and
-continue with the same log, at budgets `j'` and `K' ≥ j'`, and the continuation makes at most `j'`
-queries. At `j = 0` a query is impossible unless `K = 0`, where both give `timeout`. -/
-theorem buildComp_budget_eq (next : QueryLog spec → Move spec α) (t : α) :
-    ∀ (j K : ℕ) (hist : QueryLog spec), j ≤ K →
-      (buildComp next t K hist).CostBoundedBy (fun _ => 1) j →
-      buildComp next t j hist = buildComp next t K hist := by
-  intro j
-  induction j with
-  | zero =>
-    intro K hist _ hc
-    cases h : next hist with
-    | ret a =>
-      cases K with
-      | zero => rfl
-      | succ K => rw [buildComp_zero_of_ret h, buildComp_succ_of_ret h]
-    | query i x =>
-      cases K with
-      | zero => rfl
-      | succ K =>
-        rw [buildComp_succ_of_query h, OracleComp.costBoundedBy_query] at hc
-        exact absurd hc.1 (by omega)
-  | succ j ih =>
-    intro K hist hK hc
-    obtain ⟨K, rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
-    cases h : next hist with
-    | ret a => rw [buildComp_succ_of_ret h, buildComp_succ_of_ret h]
-    | query i x =>
-      rw [buildComp_succ_of_query h] at hc ⊢
-      rw [buildComp_succ_of_query h]
-      rw [OracleComp.costBoundedBy_query] at hc
-      congr 1
-      funext y
-      exact ih K _ (by omega) (by simpa using hc.2 y)
-
-/-- **Budget reduction for a machine:** if `D`'s computation on `x` at budget `K ≥ j` makes at
-most `j` queries on every path, it is `D`'s computation at budget `j`. -/
-theorem toCompOn_budget_eq (D : NUPPT) {β : Type} (codec : MachineCodec spec β) (n j K : ℕ)
-    (x : List Bool) (r : D.Coins n) (hjK : j ≤ K)
-    (hc : (D.toCompOn codec n K x r).CostBoundedBy (fun _ => 1) j) :
-    D.toCompOn codec n j x r = D.toCompOn codec n K x r := by
-  rw [NUPPT.toCompOn_eq] at hc ⊢
-  rw [NUPPT.toCompOn_eq]
-  exact buildComp_budget_eq _ _ j K [] hjK hc
-
-end Budget
-
-/-! ### Expectations on the possible outputs -/
-
-section Expect
-
-variable {α β : Type}
-
-/-- Two functions that agree on every possible output have the same expectation. -/
-theorem expect_congr_of_allOutputs {c : ProbComp α} {P : α → Prop} (hc : c.AllOutputs P)
-    {f g : α → ℝ} (h : ∀ a, P a → f a = g a) : ProbComp.expect c f = ProbComp.expect c g :=
-  le_antisymm (ProbComp.expect_mono_of_allOutputs hc fun a ha => (h a ha).le)
-    (ProbComp.expect_mono_of_allOutputs hc fun a ha => (h a ha).ge)
-
-/-- **Fubini for a uniform sample:** `𝔼_c[𝔼_{t ← T}[h a t]] = 𝔼_{t ← T}[𝔼_c[h a t]]`. -/
-theorem expect_expect_sample (c : ProbComp α) (T : Type) [Fintype T] [Nonempty T]
-    (h : α → T → ℝ) :
-    ProbComp.expect c (fun a => ProbComp.expect (ProbComp.sample T) (h a)) =
-      ProbComp.expect (ProbComp.sample T) fun t => ProbComp.expect c fun a => h a t := by
-  simp only [ProbComp.expect_sample]
-  rw [ProbComp.expect_const_mul, ProbComp.expect_sum]
-
-/-- Two continuations that agree on every possible output give the same computation:
-`c.bind f = c.bind g` when `f a = g a` whenever `P a`, and `c.AllOutputs P`. -/
-theorem bind_congr_of_allOutputs {ι : Type} {spec : OracleSpec ι} {c : OracleComp spec α}
-    {P : α → Prop} (hc : c.AllOutputs P) {f g : α → OracleComp spec β}
-    (h : ∀ a, P a → f a = g a) : c.bind f = c.bind g := by
-  induction c with
-  | pure a =>
-    rw [OracleComp.pure_bind, OracleComp.pure_bind]
-    exact h a (OracleComp.allOutputs_pure.1 hc)
-  | query i x k ih =>
-    rw [OracleComp.query_bind, OracleComp.query_bind]
-    congr 1
-    funext y
-    exact ih y (OracleComp.allOutputs_query.1 hc y)
-
-end Expect
-
-/-- **Changing a machine's output length along `d = d'`** keeps the law of its output read as a
-list: `𝔼[G (⟦p.1⟧, p.2)]` over the runs through `bitCodec ins outs d` and `bitCodec ins outs d'`
-agree. -/
-theorem expect_toCompOn_outLen {k : ℕ} {ins outs : Fin k → ℕ} {σ : Type}
-    (O : QueryImpl (bitSpec ins outs) σ unifSpec) (A : NUPPT) (n q : ℕ) (x : List Bool)
-    (r : A.Coins n) (s : σ) {d d' : ℕ} (hd : d = d') (G : List Bool × σ → ℝ) :
-    ProbComp.expect (simulate O (A.toCompOn (bitCodec ins outs d) n q x r) s)
-        (fun p => G (List.ofFn p.1, p.2)) =
-      ProbComp.expect (simulate O (A.toCompOn (bitCodec ins outs d') n q x r) s)
-        (fun p => G (List.ofFn p.1, p.2)) := by
-  subst hd
-  rfl
-
-/-! ### One-shot coins drawn in advance -/
-
-section Eager
-
-variable {ι σ α T : Type} {spec : OracleSpec ι} [Fintype T] [Nonempty T]
-
-/-- From a used state, an implementation that agrees with `O` there simulates like `O`. -/
-private theorem simulate_eq_of_used (O O' : QueryImpl spec σ unifSpec) (used : σ → Prop)
-    (hused : ∀ i x s, used s → O' i x s = O i x s)
-    (hstick : ∀ i x s, used s → (O i x s).AllOutputs fun p => used p.2)
-    (c : OracleComp spec α) {s : σ} (hs : used s) : simulate O' c s = simulate O c s := by
-  induction c generalizing s with
-  | pure a => rw [simulate_pure, simulate_pure]
-  | query i x k ih =>
-    rw [simulate_query, simulate_query, hused i x s hs]
-    exact bind_congr_of_allOutputs (hstick i x s hs) fun p hp => ih p.1 hp
-
-/-- **One-shot coins drawn in advance.** Let `O` be an implementation and `OE t` its variants with
-coins `t ∈ T` fixed in advance, and let `used` mark the states after the coins are spent:
-- from a used state, `OE t` is `O`, and `O` keeps the state used;
-- from an unused state, a call either does not use the coins (`OE t` is `O` for every `t`, and the
-  state stays unused), or it is the one that spends them (`O` samples `t` and runs `OE t`, and
-  every successor is used).
-
-Then from an unused state, `O`'s simulation has the law of `OE t`'s, averaged over `t`:
-`𝔼[G(simulate O c s)] = 𝔼_{t ← T} 𝔼[G(simulate (OE t) c s)]`.
-
-**Proof sketch.** Induction on `c`. From used states the two simulations coincide
-(`simulate_eq_of_used`). At a query from an unused state: in the first case, rewrite the call,
-apply the induction hypothesis at the (unused) successors and exchange the expectations
-(`expect_expect_sample`); in the second, expand `O`'s sample and conclude from the coincidence at
-the (used) successors. -/
-theorem expect_simulate_eager (O : QueryImpl spec σ unifSpec) (OE : T → QueryImpl spec σ unifSpec)
-    (used : σ → Prop) (hused : ∀ t i x s, used s → OE t i x s = O i x s)
-    (hstick : ∀ i x s, used s → (O i x s).AllOutputs fun p => used p.2)
-    (hfresh : ∀ i x s, ¬ used s →
-      (∀ t, OE t i x s = O i x s ∧ (O i x s).AllOutputs fun p => ¬ used p.2) ∨
-      (O i x s = (ProbComp.sample T).bind (fun t => OE t i x s) ∧
-        ∀ t, (OE t i x s).AllOutputs fun p => used p.2))
-    (c : OracleComp spec α) (G : α × σ → ℝ) {s : σ} (hs : ¬ used s) :
-    ProbComp.expect (simulate O c s) G =
-      ProbComp.expect (ProbComp.sample T) fun t => ProbComp.expect (simulate (OE t) c s) G := by
-  induction c generalizing s with
-  | pure a =>
-    simp only [simulate_pure, ProbComp.expect_pure]
-    exact (ProbComp.expect_const _ _).symm
-  | query i x k ih =>
-    simp only [simulate_query, ProbComp.expect_bind]
-    rcases hfresh i x s hs with h | ⟨h, hu⟩
-    · have hO : ∀ t, OE t i x s = O i x s := fun t => (h t).1
-      have hun : (O i x s).AllOutputs fun p => ¬ used p.2 :=
-        (h (Classical.arbitrary T)).2
-      simp only [hO]
-      rw [expect_congr_of_allOutputs hun fun p hp => ih p.1 hp, expect_expect_sample]
-    · rw [h, ProbComp.expect_bind]
-      refine congrArg _ (funext fun t => ?_)
-      refine expect_congr_of_allOutputs (hu t) fun p hp => ?_
-      rw [simulate_eq_of_used O (OE t) used (hused t) hstick _ hp]
-
-end Eager
-
-/-! ### Equal until bad, for functions of the final state -/
-
-section UntilBad
-
-variable {ι σ α : Type} {spec : OracleSpec ι}
-
-/-- **Equal until bad, in expectation, for functions of the output and the final state.** Let two
-implementations give, from every good state, the same law to good successors, and let each keep
-bad states bad. Then from a good state, for every function `G` of the output and the final state,
-`𝔼[G · 1_{good}]` is the same under both simulations. This generalizes `prob_eq_until_bad`
-(`Games/Hopping.lean`), whose events read only the output.
-
-**Proof sketch.** Induction on the computation. From a bad successor the continuation's value is
-`0` on both sides (`simulate_allOutputs_bad`); from a good one the two values agree by induction;
-so both expectations only see the values at good successors, which `hagree` equates. -/
-theorem expect_eq_until_bad {impl₀ impl₁ : QueryImpl spec σ unifSpec} (bad : σ → Prop)
-    [DecidablePred bad]
-    (hagree : ∀ i x s, ¬ bad s → ∀ g : spec.rng i × σ → ℝ,
-      ProbComp.expect (impl₀ i x s) (fun ys => if bad ys.2 then 0 else g ys) =
-        ProbComp.expect (impl₁ i x s) (fun ys => if bad ys.2 then 0 else g ys))
-    (hstick₀ : ∀ i x s, bad s → (impl₀ i x s).AllOutputs fun ys => bad ys.2)
-    (hstick₁ : ∀ i x s, bad s → (impl₁ i x s).AllOutputs fun ys => bad ys.2)
-    (c : OracleComp spec α) (G : α × σ → ℝ) {s : σ} (hs : ¬ bad s) :
-    ProbComp.expect (simulate impl₀ c s) (fun r => if bad r.2 then 0 else G r) =
-      ProbComp.expect (simulate impl₁ c s) (fun r => if bad r.2 then 0 else G r) := by
-  induction c generalizing s with
-  | pure a => rw [simulate_pure, simulate_pure]
-  | query i x k ih =>
-    simp only [simulate_query, ProbComp.expect_bind]
-    have hz : ∀ (impl : QueryImpl spec σ unifSpec),
-        (∀ i x s, bad s → (impl i x s).AllOutputs fun ys => bad ys.2) →
-        ∀ ys : spec.rng i × σ, bad ys.2 →
-          ProbComp.expect (simulate impl (k ys.1) ys.2) (fun r => if bad r.2 then 0 else G r) =
-            0 := by
-      intro impl hst ys hb
-      rw [expect_congr_of_allOutputs (simulate_allOutputs_bad bad hst _ hb)
-        (g := fun _ => 0) fun r hr => if_pos hr, ProbComp.expect_const]
-    have h0 : ∀ ys : spec.rng i × σ,
-        ProbComp.expect (simulate impl₀ (k ys.1) ys.2) (fun r => if bad r.2 then 0 else G r) =
-          if bad ys.2 then 0 else
-            ProbComp.expect (simulate impl₁ (k ys.1) ys.2)
-              (fun r => if bad r.2 then 0 else G r) := by
-      intro ys
-      by_cases hb : bad ys.2
-      · rw [if_pos hb, hz impl₀ hstick₀ ys hb]
-      · rw [if_neg hb, ih ys.1 hb]
-    have h1 : ∀ ys : spec.rng i × σ,
-        ProbComp.expect (simulate impl₁ (k ys.1) ys.2) (fun r => if bad r.2 then 0 else G r) =
-          if bad ys.2 then 0 else
-            ProbComp.expect (simulate impl₁ (k ys.1) ys.2)
-              (fun r => if bad r.2 then 0 else G r) := by
-      intro ys
-      by_cases hb : bad ys.2
-      · rw [if_pos hb, hz impl₁ hstick₁ ys hb]
-      · rw [if_neg hb]
-    rw [funext h0, hagree i x s hs, ← funext h1]
-
-end UntilBad
-
 /-! ### Chunk maps -/
 
 section Chunks
@@ -308,16 +73,17 @@ theorem chunkEmit_eq (c : PolyExpr) (f : List Bool → List Bool → List Bool)
 
 /-- **The chunk map** of `f` with chunk length `c`, on `x = ⟨ctx, w⟩` with `ctx = ⟨1^n, _⟩`: the
 concatenation of `f ctx` over the consecutive `c(n)`-bit chunks of `w`, computed by `|x| + 1`
-rounds of `chunkStep`: `chunkMap c f x = (List.range (|x| + 1)).flatMap fun i =>
-chunkEmit c f (chunkStep c)^[i] x`. -/
+rounds of `chunkStep` (iterate and emit, `Games.iterEmit`): `chunkMap c f x =
+(List.range (|x| + 1)).flatMap fun i => chunkEmit c f (chunkStep c)^[i] x`. -/
 def chunkMap (c : PolyExpr) (f : List Bool → List Bool → List Bool) (x : List Bool) : List Bool :=
-  (List.range (x.length + 1)).flatMap fun i => chunkEmit c f ((chunkStep c)^[i] x)
+  iterEmit (chunkStep c) (chunkEmit c f) (x.length + 1) x
 
-/-- `chunkMap c f x = (List.range (|x| + 1)).flatMap fun i => chunkEmit c f (chunkStep c)^[i] x`. -/
+/-- `chunkMap c f x = (List.range (|x| + 1)).flatMap fun i => chunkEmit c f (chunkStep c)^[i] x`
+(`Games.iterEmit_eq`). -/
 theorem chunkMap_eq (c : PolyExpr) (f : List Bool → List Bool → List Bool) (x : List Bool) :
     chunkMap c f x =
-      (List.range (x.length + 1)).flatMap fun i => chunkEmit c f ((chunkStep c)^[i] x) :=
-  rfl
+      (List.range (x.length + 1)).flatMap fun i => chunkEmit c f ((chunkStep c)^[i] x) := by
+  rw [chunkMap, iterEmit_eq]
 
 /-- One step never makes a word longer than `max |x| 2` (a malformed word becomes `⟨[], []⟩`). -/
 private theorem length_chunkStep_le (c : PolyExpr) (x : List Bool) :
@@ -332,24 +98,14 @@ private theorem length_chunkStep_le (c : PolyExpr) (x : List Bool) :
       length_pairEncode]
     omega
 
-/-- The iterated step keeps words within `|x| + 2` bits. -/
-private theorem length_iterate_chunkStep_le (c : PolyExpr) (x : List Bool) (i : ℕ) :
-    ((chunkStep c)^[i] x).length ≤ x.length + 2 := by
-  suffices h : ((chunkStep c)^[i] x).length ≤ max x.length 2 by omega
-  induction i with
-  | zero => exact le_max_left _ _
-  | succ i ih =>
-    rw [Function.iterate_succ_apply']
-    exact (length_chunkStep_le c _).trans (max_le ih (le_max_right _ _))
-
 /-- **Chunk maps are polynomial-time** when `f` is, read as a function of `⟨ctx, chunk⟩`
-(`Complexity.polyTimeComputable_iterateEmit` with the step `chunkStep`, which never lengthens a
-word, and `|x|` rounds).
+(`Games.polyTimeComputable_iterEmit` with the step `chunkStep`, which never makes a word longer
+than `max |x| 2`).
 
 **Proof sketch.** The step (keep `ctx`, drop `c(n)` bits) and the emission (`[]` on an empty
 rest, else `f ctx` of the next `c(n)` bits) are polynomial-time by the pair readers,
-`pairTakePoly`/`pairDropPoly` and `polyTimeComputable_ite`. The iterates stay within `|x| + 2`
-bits (`length_iterate_chunkStep_le`), so `polyTimeComputable_iterateEmit` gives `chunkMap_eq`. -/
+`pairTakePoly`/`pairDropPoly` and `polyTimeComputable_ite`; one step never lengthens a word beyond
+`max |x| 2` (`length_chunkStep_le`), so `polyTimeComputable_iterEmit` applies. -/
 theorem polyTimeComputable_chunkMap (c : PolyExpr) {f : List Bool → List Bool → List Bool}
     (hf : PolyTimeComputable fun z => f (pairFstD z) (pairSndD z)) :
     PolyTimeComputable (chunkMap c f) := by
@@ -370,66 +126,24 @@ theorem polyTimeComputable_chunkMap (c : PolyExpr) {f : List Bool → List Bool
     polyTimeComputable_ite (polyTimeComputable_isNil.comp hD) (polyTimeComputable_const [])
       ((hf.comp (hF.pairEncode htake)).congr fun x => by
         simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode])
-  exact (polyTimeComputable_iterateEmit hstep hemit .var (.add .var (.const 2))
-    (fun x i _ => by
-      rw [PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_const]
-      exact length_iterate_chunkStep_le c x i)).congr
-    fun x => by rw [PolyExpr.eval_var, chunkMap_eq]
-
-/-- Reading the suffixes of a list within at least its length many steps (DL-30–36 overlap: the
-general form of `Forward`'s private `flatMap_range_drop`, with the reading of a nonempty suffix
-assumed only for the list's members). -/
-private theorem flatMap_range_drop {β : Type} (F : List β → List Bool) (g : β → List Bool)
-    (hnil : F [] = []) :
-    ∀ (l : List β), (∀ e ∈ l, ∀ t, F (e :: t) = g e) → ∀ m : ℕ, l.length ≤ m →
-      ((List.range m).flatMap fun i => F (l.drop i)) = l.flatMap g := by
-  intro l
-  induction l with
-  | nil =>
-    intro _ m _
-    rw [List.flatMap_nil]
-    refine List.flatMap_eq_nil_iff.2 fun i _ => ?_
-    rw [List.drop_nil, hnil]
-  | cons e t ih =>
-    intro hcons m hm
-    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by rw [List.length_cons] at hm; omega⟩
-    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, List.drop_zero,
-      hcons e List.mem_cons_self, List.flatMap_cons]
-    congr 1
-    simp only [List.drop_succ_cons]
-    exact ih (fun e' he' => hcons e' (List.mem_cons_of_mem _ he')) m'
-      (by rw [List.length_cons] at hm; omega)
+  exact (polyTimeComputable_iterEmit hstep hemit 2 (length_chunkStep_le c)).congr
+    fun x => by rw [chunkMap]
 
 /-- **The chunk map of a concatenation of chunks:** if every chunk has `c(n) > 0` bits, the chunk
 map of `⟨⟨1^n, e⟩, chunks.flatten⟩` is the concatenation of `f ⟨1^n, e⟩` over the chunks.
 
-**Proof sketch.** The `i`-th step leaves `(chunks.drop i).flatten` (dropping a first chunk of
-`c(n)` bits), whose emission is `f` of the `i`-th chunk while chunks remain and `[]` afterwards;
-there are at most `|x| + 1` chunks since each has a bit. -/
+**Proof sketch.** `Games.iterEmit_encode` with the encoding `l ↦ ⟨ctx, l.flatten⟩`: a step drops a
+first chunk of `c(n)` bits and fixes `⟨ctx, []⟩`; the emission is `f ctx` of the first chunk while
+chunks remain and `[]` afterwards; there are at most `|x| + 1` chunks since each has a bit. -/
 theorem chunkMap_flatten (c : PolyExpr) (f : List Bool → List Bool → List Bool) (n : ℕ)
     (e : List Bool) (chunks : List (List Bool)) (hlen : ∀ ch ∈ chunks, ch.length = c.eval n)
     (hpos : 0 < c.eval n) :
     chunkMap c f (pairEncode (pairEncode (List.replicate n true) e) chunks.flatten) =
       (chunks.map (f (pairEncode (List.replicate n true) e))).flatten := by
   set ctx := pairEncode (List.replicate n true) e
-  have hit : ∀ i, (chunkStep c)^[i] (pairEncode ctx chunks.flatten) =
-      pairEncode ctx (chunks.drop i).flatten := by
-    intro i
-    induction i with
-    | zero => rfl
-    | succ i ih =>
-      rw [Function.iterate_succ_apply', ih, chunkStep_eq, pairFstD_pairEncode,
-        pairSndD_pairEncode, pairFstD_pairEncode, List.length_replicate, ← List.tail_drop]
-      cases h : chunks.drop i with
-      | nil => rw [List.flatten_nil, List.drop_nil, List.tail_nil, List.flatten_nil]
-      | cons ch rest =>
-        have hch : ch.length = c.eval n :=
-          hlen ch (List.mem_of_mem_drop (h ▸ List.mem_cons_self))
-        rw [List.flatten_cons, List.tail_cons, ← hch, List.drop_left]
   have hlen' : chunks.length ≤ (pairEncode ctx chunks.flatten).length + 1 := by
     have : chunks.length ≤ chunks.flatten.length := by
       rw [List.length_flatten]
-      clear hit
       induction chunks with
       | nil => exact le_rfl
       | cons ch rest ih =>
@@ -439,21 +153,28 @@ theorem chunkMap_flatten (c : PolyExpr) (f : List Bool → List Bool → List Bo
         omega
     rw [length_pairEncode]
     omega
-  rw [chunkMap_eq]
-  simp only [hit]
-  rw [flatMap_range_drop (fun l => chunkEmit c f (pairEncode ctx l.flatten)) (f ctx)
-    (by
-      show chunkEmit c f (pairEncode ctx ([] : List (List Bool)).flatten) = []
-      rw [List.flatten_nil, chunkEmit_eq, pairSndD_pairEncode, if_pos (decide_eq_true rfl)])
-    chunks (fun ch hch t => ?_) _ hlen', List.flatMap_def]
-  have hl := hlen ch hch
-  have hne : ch ++ t.flatten ≠ [] := fun h => by
-    rw [List.append_eq_nil_iff] at h
-    rw [h.1, List.length_nil] at hl
-    omega
-  show chunkEmit c f (pairEncode ctx (ch :: t).flatten) = f ctx ch
-  rw [chunkEmit_eq, pairSndD_pairEncode, pairFstD_pairEncode, pairFstD_pairEncode,
-    List.length_replicate, List.flatten_cons, if_neg (by simpa using hne), ← hl, List.take_left]
+  have hstep_nil : chunkStep c (pairEncode ctx ([] : List (List Bool)).flatten) =
+      pairEncode ctx ([] : List (List Bool)).flatten := by
+    rw [List.flatten_nil, chunkStep_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.drop_nil]
+  have hstep : ∀ ch ∈ chunks, ∀ t : List (List Bool),
+      chunkStep c (pairEncode ctx (ch :: t).flatten) = pairEncode ctx t.flatten := by
+    intro ch hch t
+    rw [chunkStep_eq, pairFstD_pairEncode, pairSndD_pairEncode, pairFstD_pairEncode,
+      List.length_replicate, List.flatten_cons, ← hlen ch hch, List.drop_left]
+  have hnil : chunkEmit c f (pairEncode ctx ([] : List (List Bool)).flatten) = [] := by
+    rw [List.flatten_nil, chunkEmit_eq, pairSndD_pairEncode, if_pos (decide_eq_true rfl)]
+  have hcons : ∀ ch ∈ chunks, ∀ t : List (List Bool),
+      chunkEmit c f (pairEncode ctx (ch :: t).flatten) = f ctx ch := by
+    intro ch hch t
+    have hl := hlen ch hch
+    have hne : ch ++ t.flatten ≠ [] := fun h => by
+      rw [List.append_eq_nil_iff] at h
+      rw [h.1, List.length_nil] at hl
+      omega
+    rw [chunkEmit_eq, pairSndD_pairEncode, pairFstD_pairEncode, pairFstD_pairEncode,
+      List.length_replicate, List.flatten_cons, if_neg (by simpa using hne), ← hl, List.take_left]
+  rw [chunkMap, iterEmit_encode (chunkStep c) (chunkEmit c f) (fun l => pairEncode ctx l.flatten)
+    (f ctx) chunks hstep_nil hstep hnil hcons _ hlen', List.flatMap_def]
 
 end Chunks
 
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Hybrid.lean b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Hybrid.lean
index cd298ca10..82e2d1ac1 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Hybrid.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Hybrid.lean
@@ -34,7 +34,7 @@ function `hist` and its length `hl`), on the lengths that T2 machines use (`snmD
 * `NMSim.snmDin`, `NMSim.snmDout`: the oracle lengths as polynomials.
 * `NMSim.drawWith`, `NMSim.histWith`, `NMSim.encWith`: `M(a; ρ)`, `h(m)` and `Enc_pk(m; re)`.
 * `NMSim.rImpl`: the hybrid oracle; `NMSim.histImpl`: the history oracle.
-* `NMSim.chunkAt`, `NMSim.entryL`, `NMSim.realView`, `NMSim.idealView`.
+* `NMSim.entryL`, `NMSim.realView`, `NMSim.idealView`.
 * `NMSim.realAcc`, `NMSim.idealAcc`, `NMSim.hybAcc`.
 
 ## Main results
@@ -45,8 +45,11 @@ function `hist` and its length `hl`), on the lengths that T2 machines use (`snmD
 * `NMSim.rImpl_eq_of_msgLen_eq_zero`: with empty messages the two hybrids coincide.
 * `NMSim.expect_simulate_rImpl_eager`: the encryption coins may be drawn in advance.
 * `NMSim.rImpl_false_coins`, `NMSim.histImpl_coins`: coins that are not read.
-* Blocks of strings: `NMSim.ofFn_block`, `ofFn_natAdd_eq_drop`, `take_eq_flatten_chunkAt`,
-  `chunkAt_flatten_append`, `map_chunkAt_flatten`, and their lengths.
+* Blocks of strings: `NMSim.take_eq_flatten_chunkAt` (the first `r` segments `coinBlock`) and
+  `NMSim.drop_flatten_append`. The other block lemmas first proved here are now beside `coinBlock`
+  (`ofFn_block_eq_coinBlock`, `coinBlock_flatten_append`, `map_coinBlock_flatten`) and in
+  `Foundations/BitLists.lean` (`ofFn_natAdd_eq_drop`, `ofFn_eq_map_range`, `decide_map_ofFn`,
+  `length_flatten_map_const`, `length_flatten_map_range`).
 * `NMSim.realAcc_eq_hybAcc`, `NMSim.hybAcc_true_eq_false`: `H_false` is the real experiment, and
   the hybrids coincide when `msgLen(n) = 0`.
 
@@ -259,8 +262,8 @@ theorem rImpl_allOutputs_isSome (atk : Attack) (b : Bool) (samp : NUPPT) (pl hl
 
 /-- **The encryption coins may be drawn in advance:** for every computation `c` and function `G`,
 the run against the hybrid oracle with sampled coins has the law of the runs with coins `re`
-drawn in advance, averaged over `re` (`expect_simulate_eager`; the coins are spent at the first
-challenge). -/
+drawn in advance, averaged over `re` (`Games.expect_simulate_eager`; the coins are spent at the
+first challenge). -/
 theorem expect_simulate_rImpl_eager (atk : Attack) (b : Bool) (samp : NUPPT) (pl hl : PolyExpr)
     (hist : List Bool → List Bool) (n : ℕ) (pk sk : List Bool) (ρ ρ' : samp.Coins n) {α : Type}
     (c : OracleComp (bitSpecAt (snmDin S pl) (snmDout S hl) n) α)
@@ -360,131 +363,20 @@ theorem histImpl_coins (samp : NUPPT) (pl hl : PolyExpr) (hist : List Bool → L
 
 /-! ### Blocks of fixed-length strings -/
 
-/-- Block `i` of `k` bits of a string: `chunkAt k i w = (w.drop (i·k)).take k`. -/
-def chunkAt (k i : ℕ) (w : List Bool) : List Bool := (w.drop (i * k)).take k
-
-/-- `chunkAt k i w = (w.drop (i·k)).take k`. -/
-theorem chunkAt_eq (k i : ℕ) (w : List Bool) : chunkAt k i w = (w.drop (i * k)).take k := rfl
-
-/-- A block inside the string has `k` bits: `|chunkAt k i w| = k` when `(i + 1)·k ≤ |w|`. -/
-theorem length_chunkAt (k i : ℕ) (w : List Bool) (h : (i + 1) * k ≤ w.length) :
-    (chunkAt k i w).length = k := by
-  rw [chunkAt_eq, List.length_take, List.length_drop, Nat.succ_mul] at *
-  omega
-
-/-- **The first `r` blocks:** `w.take (r·k) = (chunkAt k 0 w ++ ⋯ ++ chunkAt k (r-1) w)`. -/
+/-- **The first `r` blocks:** `w.take (r·k) = (coinBlock k 0 w ++ ⋯ ++ coinBlock k (r-1) w)`. -/
 theorem take_eq_flatten_chunkAt (k r : ℕ) (w : List Bool) :
-    w.take (r * k) = ((List.range r).map fun i => chunkAt k i w).flatten := by
+    w.take (r * k) = ((List.range r).map fun i => coinBlock k i w).flatten := by
   induction r with
   | zero => rw [Nat.zero_mul, List.take_zero, List.range_zero, List.map_nil, List.flatten_nil]
   | succ r ih =>
     rw [Nat.succ_mul, List.take_add, ih, List.range_succ, List.map_append, List.flatten_append,
-      List.map_singleton, List.flatten_singleton, chunkAt_eq]
-
-/-- `r` blocks of `k` bits have `r·k` bits. -/
-theorem length_flatten_map_range (k r : ℕ) (g : ℕ → List Bool) (hg : ∀ i < r, (g i).length = k) :
-    ((List.range r).map g).flatten.length = r * k := by
-  induction r with
-  | zero => rw [List.range_zero, List.map_nil, List.flatten_nil, List.length_nil, Nat.zero_mul]
-  | succ r ih =>
-    rw [List.range_succ, List.map_append, List.flatten_append, List.length_append,
-      ih fun i hi => hg i (by omega), List.map_singleton, List.flatten_singleton,
-      hg r (by omega), Nat.succ_mul]
-
-/-- Blocks of `k` bits, one per element: `|(l.map g).flatten| = |l|·k` when every `g x` has
-`k` bits. -/
-theorem length_flatten_map_const {α β : Type} (l : List α) (g : α → List β) (k : ℕ)
-    (hg : ∀ x, (g x).length = k) : (l.map g).flatten.length = l.length * k := by
-  induction l with
-  | nil => rw [List.map_nil, List.flatten_nil, List.length_nil, List.length_nil, Nat.zero_mul]
-  | cons x t ih => rw [List.map_cons, List.flatten_cons, List.length_append, ih, hg,
-      List.length_cons, Nat.succ_mul, Nat.add_comm]
-
-/-- **Reading back the blocks:** if `g 0, …, g (r-1)` have `k` bits each, block `i < r` of
-`g 0 ++ ⋯ ++ g (r-1) ++ t` is `g i`. -/
-theorem chunkAt_flatten_append (k r : ℕ) (g : ℕ → List Bool) (hg : ∀ i < r, (g i).length = k)
-    (t : List Bool) (i : ℕ) (hi : i < r) :
-    chunkAt k i (((List.range r).map g).flatten ++ t) = g i := by
-  induction r generalizing t with
-  | zero => exact absurd hi (Nat.not_lt_zero _)
-  | succ r ih =>
-    rw [List.range_succ, List.map_append, List.flatten_append, List.map_singleton,
-      List.flatten_singleton, List.append_assoc]
-    by_cases h : i < r
-    · exact ih (fun j hj => hg j (by omega)) _ h
-    · have hir : i = r := by omega
-      subst hir
-      rw [chunkAt_eq, List.drop_append_of_le_length (by
-          rw [length_flatten_map_range k i g fun j hj => hg j (by omega)]),
-        List.drop_of_length_le (by rw [length_flatten_map_range k i g fun j hj => hg j (by omega)]),
-        List.nil_append, List.take_left' (hg i (by omega))]
+      List.map_singleton, List.flatten_singleton, coinBlock_eq]
 
 /-- The tail after `r` blocks of `k` bits: `(g 0 ++ ⋯ ++ g (r-1) ++ t).drop (r·k) = t`. -/
 theorem drop_flatten_append (k r : ℕ) (g : ℕ → List Bool) (hg : ∀ i < r, (g i).length = k)
     (t : List Bool) : (((List.range r).map g).flatten ++ t).drop (r * k) = t :=
   List.drop_left' (length_flatten_map_range k r g hg)
 
-/-- **The blocks of a concatenation of `k`-bit blocks:** if every block of `cs` has `k` bits,
-mapping `F` over `chunkAt k i cs.flatten` for `i < |cs|` is mapping `F` over `cs`. -/
-theorem map_chunkAt_flatten {α : Type} (k : ℕ) (F : List Bool → α) :
-    ∀ cs : List (List Bool), (∀ c ∈ cs, c.length = k) →
-      (List.range cs.length).map (fun i => F (chunkAt k i cs.flatten)) = cs.map F := by
-  intro cs
-  induction cs with
-  | nil => intro _; rfl
-  | cons c t ih =>
-    intro hc
-    have hck : c.length = k := hc c List.mem_cons_self
-    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.map_cons,
-      List.flatten_cons, ← ih fun c' hc' => hc c' (List.mem_cons_of_mem _ hc')]
-    congr 1
-    · rw [chunkAt_eq, Nat.zero_mul, List.drop_zero, List.take_left' hck]
-    · refine List.map_congr_left fun i _ => ?_
-      rw [Function.comp_apply, chunkAt_eq, chunkAt_eq, Nat.succ_mul, Nat.add_comm,
-        ← List.drop_drop, List.drop_left' hck]
-
-/-- **Block `i` of a string of `r` blocks of `k` bits and a tail:**
-`⟦j ↦ w (castAdd sl (finProdFinEquiv (i, j)))⟧ = chunkAt k i ⟦w⟧`. -/
-theorem ofFn_block {r k sl : ℕ} (w : Fin (r * k + sl) → Bool) (i : Fin r) :
-    List.ofFn (fun j : Fin k => w (Fin.castAdd sl (finProdFinEquiv (i, j)))) =
-      chunkAt k i (List.ofFn w) := by
-  have hle : (i : ℕ) * k + k ≤ r * k := by
-    have := Nat.mul_le_mul_right k (Nat.succ_le_of_lt i.isLt)
-    rw [Nat.succ_mul] at this
-    exact this
-  rw [chunkAt_eq]
-  refine List.ext_getElem ?_ fun j h₁ h₂ => ?_
-  · simp only [List.length_ofFn, List.length_take, List.length_drop]
-    omega
-  · rw [List.getElem_ofFn, List.getElem_take, List.getElem_drop, List.getElem_ofFn]
-    refine congrArg w (Fin.ext ?_)
-    rw [Fin.coe_castAdd, finProdFinEquiv_apply_val]
-    show j + k * i = i * k + j
-    rw [Nat.mul_comm]
-    omega
-
-/-- **The tail of a string:** `⟦j ↦ w (natAdd k j)⟧ = ⟦w⟧.drop k`. -/
-theorem ofFn_natAdd_eq_drop {k sl : ℕ} (w : Fin (k + sl) → Bool) :
-    List.ofFn (fun j : Fin sl => w (Fin.natAdd k j)) = (List.ofFn w).drop k := by
-  rw [List.ofFn_add, List.drop_left' List.length_ofFn]
-
-/-- A list of `r` values is a map over `List.range r`: if `f i = g i` for `i < r`, then
-`List.ofFn f = (List.range r).map g`. -/
-theorem ofFn_eq_map_range {α : Type} {r : ℕ} (f : Fin r → α) (g : ℕ → α)
-    (h : ∀ i : Fin r, f i = g i) : List.ofFn f = (List.range r).map g := by
-  refine List.ext_getElem (by rw [List.length_ofFn, List.length_map, List.length_range])
-    fun i h₁ h₂ => ?_
-  rw [List.getElem_ofFn, List.getElem_map, List.getElem_range]
-  exact h _
-
-/-- Comparing strings is comparing their lists:
-`decide (o.map ofFn = some ⟦c⟧) = decide (o = some c)`. -/
-theorem decide_map_ofFn {k : ℕ} (o : Option (Fin k → Bool)) (c : Fin k → Bool) :
-    decide (o.map List.ofFn = some (List.ofFn c)) = decide (o = some c) := by
-  cases o with
-  | none => simp
-  | some c' => simp [List.ofFn_inj]
-
 /-! ### The experiments' outputs as strings -/
 
 /-- **An entry `d_i` as a string:** `COPY` (`true` followed by `msgLen(n) + 1` falses) if `copy`,
@@ -519,8 +411,8 @@ def realView (samp : NUPPT) (pl : PolyExpr) (n r : ℕ) (sk : List Bool) (ρ : s
   List.ofFn ((s.map Prod.snd).getD (zeroBits _)) ++
     List.ofFn (drawWith samp (S.msgLen.eval n) n ((s.map Prod.snd).getD (zeroBits _)) ρ) ++
     ((List.range r).map fun i => entryL S n sk
-      (decide ((s.map Prod.fst).map List.ofFn = some (chunkAt (S.ctLen.eval n) i w)))
-      (chunkAt (S.ctLen.eval n) i w)).flatten ++
+      (decide ((s.map Prod.fst).map List.ofFn = some (coinBlock (S.ctLen.eval n) i w)))
+      (coinBlock (S.ctLen.eval n) i w)).flatten ++
     w.drop (r * S.ctLen.eval n)
 
 /-- `realView … w s = ⟦a⟧ ++ ⟦M(a; ρ)⟧ ++ (d_0 ++ ⋯ ++ d_{r-1}) ++ σ` as defined. -/
@@ -530,8 +422,8 @@ theorem realView_eq (samp : NUPPT) (pl : PolyExpr) (n r : ℕ) (sk : List Bool)
       List.ofFn ((s.map Prod.snd).getD (zeroBits _)) ++
         List.ofFn (drawWith samp (S.msgLen.eval n) n ((s.map Prod.snd).getD (zeroBits _)) ρ) ++
         ((List.range r).map fun i => entryL S n sk
-          (decide ((s.map Prod.fst).map List.ofFn = some (chunkAt (S.ctLen.eval n) i w)))
-          (chunkAt (S.ctLen.eval n) i w)).flatten ++
+          (decide ((s.map Prod.fst).map List.ofFn = some (coinBlock (S.ctLen.eval n) i w)))
+          (coinBlock (S.ctLen.eval n) i w)).flatten ++
         w.drop (r * S.ctLen.eval n) := rfl
 
 /-- **The ideal experiment's output** `(a, m, (d_i)_i, σ)` as a string, from the simulator's output
@@ -543,8 +435,8 @@ def idealView (samp : NUPPT) (pl : PolyExpr) (n r : ℕ) (sk : List Bool) (ρ :
   List.ofFn (sa.getD (zeroBits _)) ++
     List.ofFn (drawWith samp (S.msgLen.eval n) n (sa.getD (zeroBits _)) ρ) ++
     ((List.range r).map fun i => entryL S n sk
-      ((chunkAt (S.ctLen.eval n + 1) i w).headD false)
-      (chunkAt (S.ctLen.eval n + 1) i w).tail).flatten ++
+      ((coinBlock (S.ctLen.eval n + 1) i w).headD false)
+      (coinBlock (S.ctLen.eval n + 1) i w).tail).flatten ++
     w.drop (r * (S.ctLen.eval n + 1))
 
 /-- `idealView … w sa = ⟦a⟧ ++ ⟦M(a; ρ)⟧ ++ (d_0 ++ ⋯ ++ d_{r-1}) ++ σ` as defined. -/
@@ -554,8 +446,8 @@ theorem idealView_eq (samp : NUPPT) (pl : PolyExpr) (n r : ℕ) (sk : List Bool)
       List.ofFn (sa.getD (zeroBits _)) ++
         List.ofFn (drawWith samp (S.msgLen.eval n) n (sa.getD (zeroBits _)) ρ) ++
         ((List.range r).map fun i => entryL S n sk
-          ((chunkAt (S.ctLen.eval n + 1) i w).headD false)
-          (chunkAt (S.ctLen.eval n + 1) i w).tail).flatten ++
+          ((coinBlock (S.ctLen.eval n + 1) i w).headD false)
+          (coinBlock (S.ctLen.eval n + 1) i w).tail).flatten ++
         w.drop (r * (S.ctLen.eval n + 1)) := rfl
 
 /-! ### The acceptance rates of the experiments -/
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/IndSim.lean b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/IndSim.lean
index dedbe2166..2af86c6db 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/IndSim.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/IndSim.lean
@@ -39,6 +39,7 @@ None: this module only proves results. `B`'s handler parameters `nmParams` and t
 namespace TCSlib.Cryptography.Composability.NMSim
 
 open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
+open TCSlib.Cryptography.EnsembleLemmas (seedEquiv seedEquivPoly ofFn_padFin_eq_padL)
 
 variable (S : FixedLengthPKScheme) (samp : NUPPT) (pl hl : PolyExpr)
   (hist : List Bool → List Bool) (hist_poly : PolyTimeComputable hist) (r sl : PolyExpr)
@@ -197,7 +198,7 @@ theorem nmRun_eq (B₀ : NUPPT) (n : ℕ)
           none)
         (fun p => if X.distinguisherL n (realView S samp pl n (r.eval n)
           (pairSndD (S.gen.runAt n [] rg)) ρ (List.ofFn p.1) p.2) rX = true then 1 else 0) := by
-  have hct := ctLen_pos S n rg re hL
+  have hct := S.ctLen_pos n rg re hL
   have hdα : ((r.mul S.ctLen).add sl).eval n = r.eval n * S.ctLen.eval n + sl.eval n := by
     rw [PolyExpr.eval_add, PolyExpr.eval_mul]
   have hfin : ∀ (z : List Bool)
@@ -248,9 +249,9 @@ budget `qB` such that for every distinguisher `X`, every `n` with `msgLen(n) > 0
 the hybrid `H_b`.
 
 **Proof sketch.** `B₀` is T2's machine of the NM adversary's handler and `B` hard-wires
-`M.advice n` (`exists_withAdviceOn`). Reindex `B`'s coins as `(ρ ‖ ρ̃ ‖ re, rA)` (`coinsCongr`, `φ`,
-`seedEquivPoly`, `seedEquiv`, `expect_sample_prod`) and the distinguisher's as `X`'s; pointwise
-this is
+`M.advice n` (`NUPPT.exists_withAdviceOn`). Reindex `B`'s coins as `(ρ ‖ ρ̃ ‖ re, rA)`
+(`coinsCongr`, `φ`, `seedEquivPoly`, `seedEquiv`, `expect_sample_prod`) and the distinguisher's
+as `X`'s; pointwise this is
 `nmRun_eq`, which does not read `re` (`expect_const`). -/
 theorem exists_nmAdversary : ∃ (B : NUPPT) (qB : PolyExpr), ∀ (X : NUPPT) (n : ℕ) (b : Bool),
     0 < S.msgLen.eval n →
@@ -259,7 +260,7 @@ theorem exists_nmAdversary : ∃ (B : NUPPT) (qB : PolyExpr), ∀ (X : NUPPT) (n
   obtain ⟨B₀, hT2⟩ := exists_interactiveHandlerMachine A q (snmDin S pl) (snmDout S hl)
     (snmDin S (S.msgLen.add S.msgLen)) (snmDout S (.const 0)) ((r.mul S.ctLen).add sl)
     (chalHandler (nmParams S samp pl hl hist hist_poly r sl))
-  obtain ⟨B, hc, hB⟩ := NMCCA2.exists_withAdviceOn B₀ samp.advice samp.adv samp.advice_length
+  obtain ⟨B, hc, hB⟩ := NUPPT.exists_withAdviceOn B₀ samp.advice samp.adv samp.advice_length
   refine ⟨B, (q.mul (chalHandler (nmParams S samp pl hl hist hist_poly r sl)).perCall).add
     (chalHandler (nmParams S samp pl hl hist hist_poly r sl)).finCall, fun X n b hL => ?_⟩
   obtain ⟨φ, hφ⟩ := hT2 n
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Recover.lean b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Recover.lean
index cec3ef93d..f3e646fe3 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Recover.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Recover.lean
@@ -42,22 +42,12 @@ of the challenge). The distinguisher `recDist S D` reads back the SIM experiment
 namespace TCSlib.Cryptography.Composability.NMSim
 
 open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
-open NMCCA2 (guessBit guessBit_eq guessBit_valid guessBit_refused)
+open NMCCA2 (guessBit guessBit_eq guessBit_valid guessBit_refused polyTimeComputable_guessBit)
 
 variable (S : FixedLengthPKScheme)
 
 /-! ### Reading the view -/
 
-/-- `guessBit` is polynomial-time (DL-30–36 overlap: the content of the private
-`polyTimeComputable_guessFun` of `Indistinguishability/Encrypt.lean`, on the bare string). -/
-theorem polyTimeComputable_guessBit : PolyTimeComputable fun w => [guessBit w] :=
-  (polyTimeComputable_ite polyTimeComputable_headD
-    (polyTimeComputable_headD.comp polyTimeComputable_tail)
-    (polyTimeComputable_not
-      (polyTimeComputable_headD.comp BinArith.polyTimeComputable_reverse))).congr fun w => by
-    rw [guessBit_eq]
-    split <;> rfl
-
 /-- **An entry read back** from the decryptions `v ‖ v₁ ‖ v₂` (`msgLen(n) + 1` bits each) of a
 ciphertext and the encoding of its copy flag, on the context `⟨1^n, _⟩`: `COPY` if
 `guessBit (v₁ ‖ v₂)`,
@@ -258,7 +248,7 @@ theorem recDist_distinguisherL (n : ℕ) (u : List Bool) (rD : D.Coins n) :
 
 /-- **The decryptions of concatenated ciphertexts:** for `ℓ` ciphertexts `cs` of `ctLen(n)` bits,
 `nmOutput sk s' (padFin _ cs.flatten)` is the concatenation of the entries' tails
-`(entryL … [c is the challenge] c).drop 1` (`nmOutput_eq_entryTails`, `map_chunkAt_flatten`). -/
+`(entryL … [c is the challenge] c).drop 1` (`nmOutput_eq_entryTails`, `map_coinBlock_flatten`). -/
 theorem nmOutput_flatten (n ℓ : ℕ) (sk : List Bool) (s' : Option (Fin (S.ctLen.eval n) → Bool))
     (cs : List (List Bool)) (hℓ : cs.length = ℓ) (hc : ∀ c ∈ cs, c.length = S.ctLen.eval n) :
     S.nmOutput sk s' (padFin (ℓ * S.ctLen.eval n) cs.flatten) =
@@ -268,26 +258,11 @@ theorem nmOutput_flatten (n ℓ : ℕ) (sk : List Bool) (s' : Option (Fin (S.ctL
     have : cs.map List.length = cs.map fun _ => S.ctLen.eval n := List.map_congr_left hc
     rw [this, List.map_const', List.sum_replicate, smul_eq_mul]
   rw [nmOutput_eq_entryTails S n ℓ sk s' _ hlen, ← hℓ,
-    map_chunkAt_flatten (S.ctLen.eval n) (fun c => (entryL S n sk
+    map_coinBlock_flatten (S.ctLen.eval n) (fun c => (entryL S n sk
       (decide (s'.map List.ofFn = some c)) c).drop 1) cs hc]
 
 variable (samp : NUPPT)
 
-/-- **The ciphertexts are not empty** when the messages are not: with `msgLen(n) > 0`, correctness
-gives `ctLen(n) > 0` (two different messages cannot both decrypt from the empty ciphertext). -/
-theorem ctLen_pos (n : ℕ) (rg : S.gen.Coins n) (re : S.enc.Coins n) (hL : 0 < S.msgLen.eval n) :
-    0 < S.ctLen.eval n := by
-  by_contra h
-  have h0 : S.ctLen.eval n = 0 := by omega
-  have hnil : ∀ m : Fin (S.msgLen.eval n) → Bool,
-      S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) (List.ofFn m)) re = [] := fun m =>
-    List.eq_nil_of_length_eq_zero ((S.enc_length n rg m re).trans h0)
-  have h₁ := S.correct n (fun _ => true) rg re
-  have h₂ := S.correct n (fun _ => false) rg re
-  rw [hnil] at h₁ h₂
-  have := congrFun (Option.some.inj (h₁.symm.trans h₂)) ⟨0, hL⟩
-  exact absurd this (by decide)
-
 /-- **The encoding of a bit is read back** from its decryptions: under generated keys, with
 `msgLen(n) > 0`, for the context `⟨1^n, ⟨z, ⟨ω, st⟩⟩⟩` with `pk = fst z` and the tape `re` after
 `2·coins(n)` bits of `ω`, `guessBit (v(Enc_pk(x^{msgLen})) ‖ v(Enc_pk((¬x)^{msgLen}))) = x`, where
@@ -368,18 +343,18 @@ theorem recView_nmOutL (n : ℕ) (rg : S.gen.Coins n) (hL : 0 < S.msgLen.eval n)
         (padFin ((nmLen S pl r sl).eval n * S.ctLen.eval n) (nmOutL S samp r n
           (pairEncode (List.replicate n true) (pairEncode z (pairEncode ω st))) a aP mP))) =
       aP ++ mP ++ ((List.range (r.eval n)).map fun i => entryL S n (pairSndD (S.gen.runAt n [] rg))
-        (decide (s'.map List.ofFn = some (chunkAt (S.ctLen.eval n) i a)))
-        (chunkAt (S.ctLen.eval n) i a)).flatten ++ a.drop (r.eval n * S.ctLen.eval n) := by
+        (decide (s'.map List.ofFn = some (coinBlock (S.ctLen.eval n) i a)))
+        (coinBlock (S.ctLen.eval n) i a)).flatten ++ a.drop (r.eval n * S.ctLen.eval n) := by
   set sk := pairSndD (S.gen.runAt n [] rg) with hsk
   set ctx := pairEncode (List.replicate n true) (pairEncode z (pairEncode ω st)) with hctx
   set v : List Bool → List Bool := fun c =>
     (entryL S n sk (decide (s'.map List.ofFn = some c)) c).drop 1 with hvdef
   set f : ℕ → Bool := fun i => st.headD false &&
-    decide (chunkAt (S.ctLen.eval n) i a = (st.drop 1).take (S.ctLen.eval n)) with hfdef
+    decide (coinBlock (S.ctLen.eval n) i a = (st.drop 1).take (S.ctLen.eval n)) with hfdef
   set bits := aP ++ mP ++ a.drop (r.eval n * S.ctLen.eval n) with hbits
-  have hct := ctLen_pos S n rg re hL
-  have hci : ∀ i < r.eval n, (chunkAt (S.ctLen.eval n) i a).length = S.ctLen.eval n := fun i hi =>
-    length_chunkAt _ _ _ (by
+  have hct := S.ctLen_pos n rg re hL
+  have hci : ∀ i < r.eval n, (coinBlock (S.ctLen.eval n) i a).length = S.ctLen.eval n := fun i hi =>
+    length_coinBlock (by
       rw [ha]
       have := Nat.mul_le_mul_right (S.ctLen.eval n) (show i + 1 ≤ r.eval n from hi)
       omega)
@@ -389,7 +364,8 @@ theorem recView_nmOutL (n : ℕ) (rg : S.gen.Coins n) (hL : 0 < S.msgLen.eval n)
   have he : ∀ x, (encBit S samp ctx x).length = S.ctLen.eval n := fun x =>
     length_encBit S samp n _ x
   set cs : List (List Bool) := ((List.range (r.eval n)).map fun i =>
-      [chunkAt (S.ctLen.eval n) i a, encBit S samp ctx (f i), encBit S samp ctx (!f i)]).flatten ++
+      [coinBlock (S.ctLen.eval n) i a, encBit S samp ctx (f i),
+        encBit S samp ctx (!f i)]).flatten ++
     (bits.map fun x => [encBit S samp ctx x, encBit S samp ctx (!x)]).flatten with hcs
   have hW : nmOutL S samp r n ctx a aP mP = cs.flatten := by
     rw [nmOutL_eq, hcs, List.flatten_append, List.flatten_flatten, List.flatten_flatten,
@@ -406,7 +382,7 @@ theorem recView_nmOutL (n : ℕ) (rg : S.gen.Coins n) (hL : 0 < S.msgLen.eval n)
     rw [hcs, List.length_append, List.length_flatten, List.length_flatten, List.map_map,
       List.map_map]
     have h3 : (List.map (List.length ∘ fun i =>
-        [chunkAt (S.ctLen.eval n) i a, encBit S samp ctx (f i), encBit S samp ctx (!f i)])
+        [coinBlock (S.ctLen.eval n) i a, encBit S samp ctx (f i), encBit S samp ctx (!f i)])
         (List.range (r.eval n))) = List.replicate (r.eval n) 3 := by
       rw [List.eq_replicate_iff, List.length_map, List.length_range]
       refine ⟨rfl, fun b hb => ?_⟩
@@ -440,7 +416,7 @@ theorem recView_nmOutL (n : ℕ) (rg : S.gen.Coins n) (hL : 0 < S.msgLen.eval n)
       · exact he _
   rw [hW, nmOutput_flatten S n _ sk s' cs hcs_len hcs_ct]
   have hP : (cs.map v).flatten =
-      ((List.range (r.eval n)).map fun i => v (chunkAt (S.ctLen.eval n) i a) ++
+      ((List.range (r.eval n)).map fun i => v (coinBlock (S.ctLen.eval n) i a) ++
         (v (encBit S samp ctx (f i)) ++ v (encBit S samp ctx (!f i)))).flatten ++
       (bits.map fun x => v (encBit S samp ctx x) ++ v (encBit S samp ctx (!x))).flatten := by
     rw [hcs, List.map_append, List.flatten_append, List.map_flatten, List.map_flatten,
@@ -461,12 +437,12 @@ theorem recView_nmOutL (n : ℕ) (rg : S.gen.Coins n) (hL : 0 < S.msgLen.eval n)
     rw [PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const, PolyExpr.eval_const]
   have h1 : (S.msgLen.add (.const 1)).eval n = S.msgLen.eval n + 1 := by
     rw [PolyExpr.eval_add, PolyExpr.eval_const]
-  have hg3 : ∀ i < r.eval n, (v (chunkAt (S.ctLen.eval n) i a) ++
+  have hg3 : ∀ i < r.eval n, (v (coinBlock (S.ctLen.eval n) i a) ++
       (v (encBit S samp ctx (f i)) ++ v (encBit S samp ctx (!f i)))).length =
       ((PolyExpr.const 3).mul (S.msgLen.add (.const 1))).eval n := fun i _ => by
     rw [List.length_append, List.length_append, hv, hv, hv, h3]
     ring
-  have hP1 : (((List.range (r.eval n)).map fun i => v (chunkAt (S.ctLen.eval n) i a) ++
+  have hP1 : (((List.range (r.eval n)).map fun i => v (coinBlock (S.ctLen.eval n) i a) ++
       (v (encBit S samp ctx (f i)) ++ v (encBit S samp ctx (!f i)))).flatten).length =
       (r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval n := by
     rw [length_flatten_map_range _ _ _ hg3]
@@ -493,19 +469,19 @@ theorem recView_nmOutL (n : ℕ) (rg : S.gen.Coins n) (hL : 0 < S.msgLen.eval n)
       | cons x t ih => rw [List.map_cons, List.flatten_cons, ih]; rfl
     rw [List.map_congr_left (fun x _ => hx x), hfl]
   have hE : (List.range (r.eval n)).map (entF S (pairEncode (List.replicate n true) []) ∘ fun i =>
-      v (chunkAt (S.ctLen.eval n) i a) ++
+      v (coinBlock (S.ctLen.eval n) i a) ++
         (v (encBit S samp ctx (f i)) ++ v (encBit S samp ctx (!f i)))) =
       (List.range (r.eval n)).map fun i => entryL S n sk
-        (decide (s'.map List.ofFn = some (chunkAt (S.ctLen.eval n) i a)))
-        (chunkAt (S.ctLen.eval n) i a) := by
+        (decide (s'.map List.ofFn = some (coinBlock (S.ctLen.eval n) i a)))
+        (coinBlock (S.ctLen.eval n) i a) := by
     refine List.map_congr_left fun i _ => ?_
     have hg : guessBit (v (encBit S samp ctx (f i)) ++ v (encBit S samp ctx (!f i))) = f i := by
       rw [hvdef]
       exact guessBit_encPair S samp n rg s' hL z ω st hz re hω (f i)
-    have hf : f i = decide (s'.map List.ofFn = some (chunkAt (S.ctLen.eval n) i a)) := hflag _
+    have hf : f i = decide (s'.map List.ofFn = some (coinBlock (S.ctLen.eval n) i a)) := hflag _
     rw [Function.comp_apply, entF_eq, pairFstD_pairEncode, List.length_replicate, h1,
       List.drop_left' (hv _), List.take_left' (hv _), hg, hf, entryL_eq]
-    by_cases hc : s'.map List.ofFn = some (chunkAt (S.ctLen.eval n) i a)
+    by_cases hc : s'.map List.ofFn = some (coinBlock (S.ctLen.eval n) i a)
     · rw [if_pos (decide_eq_true hc), if_pos (decide_eq_true hc)]
     · rw [if_neg (by simpa using hc), if_neg (by simpa using hc), hvdef]
       simp only [hc, decide_false, entryL_eq, Bool.false_eq_true, ↓reduceIte, List.drop_one,
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Reduction.lean b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Reduction.lean
index 61d805562..a034e821a 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Reduction.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Reduction.lean
@@ -46,7 +46,13 @@ oracles, its run is `A`'s run against the hybrid oracle `rImpl … b …` (`nmCo
 namespace TCSlib.Cryptography.Composability.NMSim
 
 open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
-open NMCCA2 (finU finZ finW finA fields_finInput polyTimeComputable_finFields)
+open TCSlib.Cryptography.Games.InteractiveHandler (rU rZ rW rS rI rX rL rAns finA)
+open TCSlib.Cryptography.EnsembleLemmas (seedEquiv seedEquivPoly seedEquiv_ofFn seedEquivPoly_ofFn
+  ofFn_padFin_eq_padL)
+open TCSlib.Cryptography.Games.InteractiveHandler (rU_input rZ_input rW_input rX_input rAns_input
+  rU_finInput rZ_finInput rW_finInput rS_finInput finA_finInput polyTimeComputable_rU
+  polyTimeComputable_rZ polyTimeComputable_rW polyTimeComputable_rS polyTimeComputable_rX
+  polyTimeComputable_rAns polyTimeComputable_finA)
 
 variable (S : FixedLengthPKScheme) (samp : NUPPT)
 
@@ -55,25 +61,28 @@ variable (S : FixedLengthPKScheme) (samp : NUPPT)
 /-- The second message `m̃ = M(a; ρ̃)` read in a round `w`: as `simMsg`, with the coins `ρ̃` after
 the first `coins(n)` bits of the seed. -/
 def altMsg (w : List Bool) : List Bool :=
-  EnsembleLemmas.padL (S.msgLen.eval (rdU w).length)
-    (samp.output (NUPPT.layout (rdU w) (rdQuery w) (pairSndD (rdZ w))
-      (((rdW w).drop (samp.coins.eval (rdU w).length)).take (samp.coins.eval (rdU w).length))))
+  EnsembleLemmas.padL (S.msgLen.eval (rU w).length)
+    (samp.output (NUPPT.layout (rU w) (rX w) (pairSndD (rZ w))
+      (((rW w).drop (samp.coins.eval (rU w).length)).take (samp.coins.eval (rU w).length))))
 
 /-- `altMsg S samp w = padL msgLen(n) (M.output (layout 1^n a α ρ̃))`. -/
 theorem altMsg_eq (w : List Bool) :
-    altMsg S samp w = EnsembleLemmas.padL (S.msgLen.eval (rdU w).length)
-      (samp.output (NUPPT.layout (rdU w) (rdQuery w) (pairSndD (rdZ w))
-        (((rdW w).drop (samp.coins.eval (rdU w).length)).take
-          (samp.coins.eval (rdU w).length)))) := rfl
+    altMsg S samp w = EnsembleLemmas.padL (S.msgLen.eval (rU w).length)
+      (samp.output (NUPPT.layout (rU w) (rX w) (pairSndD (rZ w))
+        (((rW w).drop (samp.coins.eval (rU w).length)).take
+          (samp.coins.eval (rU w).length)))) := rfl
 
 /-- The second message is polynomial-time. -/
 theorem polyTimeComputable_altMsg : PolyTimeComputable (altMsg S samp) := by
-  obtain ⟨hU, hZ, hW, -, -, hQ, -, -⟩ := polyTimeComputable_rd
-  have hd : PolyTimeComputable fun w => (rdW w).drop (samp.coins.eval (rdU w).length) :=
+  have hU := polyTimeComputable_rU
+  have hZ := polyTimeComputable_rZ
+  have hW := polyTimeComputable_rW
+  have hQ := polyTimeComputable_rX
+  have hd : PolyTimeComputable fun w => (rW w).drop (samp.coins.eval (rU w).length) :=
     ((polyTimeComputable_pairDropPoly samp.coins).comp (hU.pairEncode hW)).congr fun w => by
       simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
   have hρ : PolyTimeComputable fun w =>
-      ((rdW w).drop (samp.coins.eval (rdU w).length)).take (samp.coins.eval (rdU w).length) :=
+      ((rW w).drop (samp.coins.eval (rU w).length)).take (samp.coins.eval (rU w).length) :=
     ((polyTimeComputable_pairTakePoly samp.coins).comp (hU.pairEncode hd)).congr fun w => by
       simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
   exact EnsembleLemmas.polyTimeComputable_padL S.msgLen hU (samp.polyTimeComputable_output.comp
@@ -189,14 +198,14 @@ variable (pl hl : PolyExpr)
 `A`'s output `a` (`r(n)` ciphertexts, then `σ`), the recorded parameter `aP` and the message `mP`:
 `encF ctx c_i` for each ciphertext, then `encPair ctx x` for each bit `x` of `aP ‖ mP ‖ σ`. -/
 def nmOutL (r : PolyExpr) (n : ℕ) (ctx a aP mP : List Bool) : List Bool :=
-  ((List.range (r.eval n)).map fun i => encF S samp ctx (chunkAt (S.ctLen.eval n) i a)).flatten ++
+  ((List.range (r.eval n)).map fun i => encF S samp ctx (coinBlock (S.ctLen.eval n) i a)).flatten ++
     ((aP ++ mP ++ a.drop (r.eval n * S.ctLen.eval n)).map fun x => encPair S samp ctx x).flatten
 
 /-- `nmOutL S samp r n ctx a aP mP = (encF ctx c_i)_i ++ (encPair ctx x)_{x ∈ aP ‖ mP ‖ σ}`. -/
 theorem nmOutL_eq (r : PolyExpr) (n : ℕ) (ctx a aP mP : List Bool) :
     nmOutL S samp r n ctx a aP mP =
       ((List.range (r.eval n)).map fun i =>
-        encF S samp ctx (chunkAt (S.ctLen.eval n) i a)).flatten ++
+        encF S samp ctx (coinBlock (S.ctLen.eval n) i a)).flatten ++
         ((aP ++ mP ++ a.drop (r.eval n * S.ctLen.eval n)).map fun x =>
           encPair S samp ctx x).flatten := rfl
 
@@ -225,16 +234,16 @@ no outer query. -/
 def nmFin (r : PolyExpr) (w : List Bool) : List Bool :=
   pairEncode [true]
     (chunkMap S.ctLen (encF S samp)
-        (pairEncode (pairEncode (finU w) (pairEncode (finZ w) (pairEncode (finW w) (finSt w))))
-          ((finA w).take ((r.mul S.ctLen).eval (finU w).length))) ++
+        (pairEncode (pairEncode (rU w) (pairEncode (rZ w) (pairEncode (rW w) (rS w))))
+          ((finA w).take ((r.mul S.ctLen).eval (rU w).length))) ++
       chunkMap (.const 1) (bitF S samp)
-        (pairEncode (pairEncode (finU w) (pairEncode (finZ w) (pairEncode (finW w) (finSt w))))
-          ((finSt w).drop (((PolyExpr.const 1).add (S.ctLen.add hl)).eval (finU w).length) ++
-            EnsembleLemmas.padL (S.msgLen.eval (finU w).length)
-              (samp.output (NUPPT.layout (finU w)
-                ((finSt w).drop (((PolyExpr.const 1).add (S.ctLen.add hl)).eval (finU w).length))
-                (pairSndD (finZ w)) ((finW w).take (samp.coins.eval (finU w).length)))) ++
-            (finA w).drop ((r.mul S.ctLen).eval (finU w).length))))
+        (pairEncode (pairEncode (rU w) (pairEncode (rZ w) (pairEncode (rW w) (rS w))))
+          ((rS w).drop (((PolyExpr.const 1).add (S.ctLen.add hl)).eval (rU w).length) ++
+            EnsembleLemmas.padL (S.msgLen.eval (rU w).length)
+              (samp.output (NUPPT.layout (rU w)
+                ((rS w).drop (((PolyExpr.const 1).add (S.ctLen.add hl)).eval (rU w).length))
+                (pairSndD (rZ w)) ((rW w).take (samp.coins.eval (rU w).length)))) ++
+            (finA w).drop ((r.mul S.ctLen).eval (rU w).length))))
 
 /-- `nmFin S samp hl r w = ⟨[true], E ‖ B⟩`, with `E = chunkMap ctLen encF ⟨ctx, a.take (r·ctLen)⟩`
 and `B = chunkMap 1 bitF ⟨ctx, aP ‖ M(aP; ρ) ‖ a.drop (r·ctLen)⟩`, where
@@ -243,42 +252,45 @@ and `B = chunkMap 1 bitF ⟨ctx, aP ‖ M(aP; ρ) ‖ a.drop (r·ctLen)⟩`, whe
 theorem nmFin_eq (r : PolyExpr) (w : List Bool) :
     nmFin S samp hl r w = pairEncode [true]
       (chunkMap S.ctLen (encF S samp)
-          (pairEncode (pairEncode (finU w) (pairEncode (finZ w) (pairEncode (finW w) (finSt w))))
-            ((finA w).take ((r.mul S.ctLen).eval (finU w).length))) ++
+          (pairEncode (pairEncode (rU w) (pairEncode (rZ w) (pairEncode (rW w) (rS w))))
+            ((finA w).take ((r.mul S.ctLen).eval (rU w).length))) ++
         chunkMap (.const 1) (bitF S samp)
-          (pairEncode (pairEncode (finU w) (pairEncode (finZ w) (pairEncode (finW w) (finSt w))))
-            ((finSt w).drop (((PolyExpr.const 1).add (S.ctLen.add hl)).eval (finU w).length) ++
-              EnsembleLemmas.padL (S.msgLen.eval (finU w).length)
-                (samp.output (NUPPT.layout (finU w)
-                  ((finSt w).drop (((PolyExpr.const 1).add (S.ctLen.add hl)).eval (finU w).length))
-                  (pairSndD (finZ w)) ((finW w).take (samp.coins.eval (finU w).length)))) ++
-              (finA w).drop ((r.mul S.ctLen).eval (finU w).length)))) := rfl
+          (pairEncode (pairEncode (rU w) (pairEncode (rZ w) (pairEncode (rW w) (rS w))))
+            ((rS w).drop (((PolyExpr.const 1).add (S.ctLen.add hl)).eval (rU w).length) ++
+              EnsembleLemmas.padL (S.msgLen.eval (rU w).length)
+                (samp.output (NUPPT.layout (rU w)
+                  ((rS w).drop (((PolyExpr.const 1).add (S.ctLen.add hl)).eval (rU w).length))
+                  (pairSndD (rZ w)) ((rW w).take (samp.coins.eval (rU w).length)))) ++
+              (finA w).drop ((r.mul S.ctLen).eval (rU w).length)))) := rfl
 
 /-- The finalization round is polynomial-time.
 
-**Proof sketch.** From the polynomial-time field readers (`polyTimeComputable_finFields`,
-`polyTimeComputable_finSt`): the context by `pairEncode`; the cuts of `a` at `r·ctLen`, the
+**Proof sketch.** From the polynomial-time field readers (`polyTimeComputable_rU`,
+…, `polyTimeComputable_finA`): the context by `pairEncode`; the cuts of `a` at `r·ctLen`, the
 parameter `aP` and the coins `ρ` by `pairTakePoly`/`pairDropPoly`; the message by
 `polyTimeComputable_padL` of `M`'s output on `layout`. The two chunk maps are
 `polyTimeComputable_chunkMap` of `encF` and `bitF`, joined by `append` and `pairEncode`. -/
 theorem polyTimeComputable_nmFin (r : PolyExpr) : PolyTimeComputable (nmFin S samp hl r) := by
-  obtain ⟨hU, hZ, hW, hA, -⟩ := polyTimeComputable_finFields
-  have hS := polyTimeComputable_finSt
+  have hU := polyTimeComputable_rU
+  have hZ := polyTimeComputable_rZ
+  have hW := polyTimeComputable_rW
+  have hA := polyTimeComputable_finA
+  have hS := polyTimeComputable_rS
   have hctx : PolyTimeComputable fun w =>
-      pairEncode (finU w) (pairEncode (finZ w) (pairEncode (finW w) (finSt w))) :=
+      pairEncode (rU w) (pairEncode (rZ w) (pairEncode (rW w) (rS w))) :=
     hU.pairEncode (hZ.pairEncode (hW.pairEncode hS))
-  have htake : PolyTimeComputable fun w => (finA w).take ((r.mul S.ctLen).eval (finU w).length) :=
+  have htake : PolyTimeComputable fun w => (finA w).take ((r.mul S.ctLen).eval (rU w).length) :=
     ((polyTimeComputable_pairTakePoly (r.mul S.ctLen)).comp (hU.pairEncode hA)).congr fun w => by
       simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
-  have hdrop : PolyTimeComputable fun w => (finA w).drop ((r.mul S.ctLen).eval (finU w).length) :=
+  have hdrop : PolyTimeComputable fun w => (finA w).drop ((r.mul S.ctLen).eval (rU w).length) :=
     ((polyTimeComputable_pairDropPoly (r.mul S.ctLen)).comp (hU.pairEncode hA)).congr fun w => by
       simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
   have haP : PolyTimeComputable fun w =>
-      (finSt w).drop (((PolyExpr.const 1).add (S.ctLen.add hl)).eval (finU w).length) :=
+      (rS w).drop (((PolyExpr.const 1).add (S.ctLen.add hl)).eval (rU w).length) :=
     ((polyTimeComputable_pairDropPoly ((PolyExpr.const 1).add (S.ctLen.add hl))).comp
       (hU.pairEncode hS)).congr fun w => by
         simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
-  have hρ : PolyTimeComputable fun w => (finW w).take (samp.coins.eval (finU w).length) :=
+  have hρ : PolyTimeComputable fun w => (rW w).take (samp.coins.eval (rU w).length) :=
     ((polyTimeComputable_pairTakePoly samp.coins).comp (hU.pairEncode hW)).congr fun w => by
       simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
   have hm := EnsembleLemmas.polyTimeComputable_padL S.msgLen hU (samp.polyTimeComputable_output.comp
@@ -292,9 +304,9 @@ theorem polyTimeComputable_nmFin (r : PolyExpr) : PolyTimeComputable (nmFin S sa
 /-- **The finalization round on a finalization input** (for `A`'s output of `r·ctLen + sl` bits, and
 `ctLen(n) > 0`) returns `⟨[true], nmOutL …⟩`.
 
-**Proof sketch.** Read the fields of the input in `nmFin_eq` (`fields_finInput`,
-`finSt_finInput`). Cut `a.take (r·ctLen)` into its `r` chunks of `ctLen(n) > 0` bits
-(`take_eq_flatten_chunkAt`, `length_chunkAt`), so the first chunk map is `encF` over them
+**Proof sketch.** Read the fields of the input in `nmFin_eq` (`rU_finInput`,
+…, `finA_finInput`). Cut `a.take (r·ctLen)` into its `r` chunks of `ctLen(n) > 0` bits
+(`take_eq_flatten_chunkAt`, `length_coinBlock`), so the first chunk map is `encF` over them
 (`chunkMap_flatten`). Write `aP ‖ M(aP; ρ) ‖ σ` as the flatten of its singletons, so the second,
 with chunk length `1`, is `bitF` over its bits; both match `nmOutL_eq`. -/
 theorem nmFin_finInput (r sl : PolyExpr) (n : ℕ) (z ω s a L : List Bool)
@@ -303,13 +315,16 @@ theorem nmFin_finInput (r sl : PolyExpr) (n : ℕ) (z ω s a L : List Bool)
       pairEncode [true] (nmOutL S samp r n
         (pairEncode (List.replicate n true) (pairEncode z (pairEncode ω s))) a (stParam S hl n s)
         (finMsg S samp n (pairSndD z) ω (stParam S hl n s))) := by
-  obtain ⟨hU, hZ, hW, hA, -⟩ := fields_finInput n z ω s a L
+  have hU := rU_finInput n z ω s a L
+  have hZ := rZ_finInput n z ω s a L
+  have hW := rW_finInput n z ω s a L
+  have hA := finA_finInput n z ω s a L
   have hbits : ∀ l : List Bool, l = (l.map fun x => [x]).flatten := by
     intro l
     induction l with
     | nil => rfl
     | cons x t ih => rw [List.map_cons, List.flatten_cons, ← ih]; rfl
-  rw [nmFin_eq, hU, hZ, hW, hA, finSt_finInput, List.length_replicate, PolyExpr.eval_mul,
+  rw [nmFin_eq, hU, hZ, hW, hA, rS_finInput, List.length_replicate, PolyExpr.eval_mul,
     take_eq_flatten_chunkAt,
     chunkMap_flatten _ _ n _ _ (fun ch hch => ?_) hct, List.map_map, nmOutL_eq, stParam_eq,
     finMsg_eq]
@@ -321,7 +336,7 @@ theorem nmFin_finInput (r sl : PolyExpr) (n : ℕ) (z ω s a L : List Bool)
       rw [PolyExpr.eval_const, List.length_singleton]
   · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hch
     rw [List.mem_range] at hi
-    refine length_chunkAt _ _ _ ?_
+    refine length_coinBlock ?_
     rw [ha]
     have := Nat.mul_le_mul_right (S.ctLen.eval n) (show i + 1 ≤ r.eval n from hi)
     omega
@@ -355,17 +370,17 @@ def nmParams (r sl : PolyExpr) :
   advIn ctx := pairFstD (pairFstD (pairSndD ctx))
   advIn_poly := polyTimeComputable_pairFstD.comp
     (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
-  qry w := EnsembleLemmas.padL ((S.msgLen.add S.msgLen).eval (rdU w).length)
+  qry w := EnsembleLemmas.padL ((S.msgLen.add S.msgLen).eval (rU w).length)
     (simMsg S samp w ++ altMsg S samp w)
-  qry_poly := EnsembleLemmas.polyTimeComputable_padL _ polyTimeComputable_rd.1
+  qry_poly := EnsembleLemmas.polyTimeComputable_padL _ polyTimeComputable_rU
     ((polyTimeComputable_simMsg S samp).append (polyTimeComputable_altMsg S samp))
   qry_len w := by rw [EnsembleLemmas.length_padL, snmDin_one]
-  ansY w := EnsembleLemmas.padL (S.ctLen.eval (rdU w).length) (rdAns w)
-  ansY_poly := EnsembleLemmas.polyTimeComputable_padL _ polyTimeComputable_rd.1
-    polyTimeComputable_rd.2.2.2.2.2.2.2
+  ansY w := EnsembleLemmas.padL (S.ctLen.eval (rU w).length) (rAns w)
+  ansY_poly := EnsembleLemmas.polyTimeComputable_padL _ polyTimeComputable_rU
+    polyTimeComputable_rAns
   ansY_len _ := EnsembleLemmas.length_padL _ _
-  ansH w := EnsembleLemmas.padL (hl.eval (rdU w).length) (hist (simMsg S samp w))
-  ansH_poly := EnsembleLemmas.polyTimeComputable_padL _ polyTimeComputable_rd.1
+  ansH w := EnsembleLemmas.padL (hl.eval (rU w).length) (hist (simMsg S samp w))
+  ansH_poly := EnsembleLemmas.polyTimeComputable_padL _ polyTimeComputable_rU
     (hist_poly.comp (polyTimeComputable_simMsg S samp))
   ansH_len _ := EnsembleLemmas.length_padL _ _
   outLen := (nmLen S pl r sl).mul S.ctLen
@@ -421,7 +436,7 @@ theorem length_nmOutL (e a aP mP : List Bool)
   · rw [encPair_eq, List.length_append, length_encBit, length_encBit]
     ring
   · rw [encF_eq, encPair_eq, List.length_append, List.length_append, length_encBit,
-      length_encBit, length_chunkAt _ _ _ (by
+      length_encBit, length_coinBlock (by
         rw [ha]
         have := Nat.mul_le_mul_right (S.ctLen.eval n) (show i + 1 ≤ r.eval n from hi)
         omega)]
@@ -441,7 +456,7 @@ theorem nmFinish (z : List Bool)
         (finMsg S samp n (pairSndD z) (List.ofFn ω) (stParam S hl n (List.ofFn s))))) := by
   have ha : (List.ofFn a).length = r.eval n * S.ctLen.eval n + sl.eval n := by
     rw [List.length_ofFn, hd]
-  refine finish_of_ret _ n z ω s a _ ?_ ?_
+  refine InteractiveHandler.finish_of_ret_padFin _ n z ω s a _ ?_ ?_
   · have hs : (List.ofFn s).length = 1 + (S.ctLen.eval n + hl.eval n) + pl.eval n := by
       rw [List.length_ofFn, chalHandler_stateLen_eval]
     rw [nmParams_outLen_eval, length_nmOutL S samp pl r sl n _ _ _ _ ha ?_ ?_]
@@ -488,7 +503,13 @@ theorem nmMsgs_input (pk : List Bool) (ρ ρ' : samp.Coins n) (re : S.enc.Coins
     altMsg S samp (InteractiveHandler.input n (pairEncode pk (samp.advice n))
         (List.ofFn (nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re)) s i xs L) =
       List.ofFn (drawWith samp (S.msgLen.eval n) n (padFin (pl.eval n) xs) ρ') := by
-  obtain ⟨hU, hZ, hW, -, -, hQ, -⟩ := fields_input n (pairEncode pk (samp.advice n))
+  have hU := rU_input n (pairEncode pk (samp.advice n))
+    (List.ofFn (nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re)) s i xs L
+  have hZ := rZ_input n (pairEncode pk (samp.advice n))
+    (List.ofFn (nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re)) s i xs L
+  have hW := rW_input n (pairEncode pk (samp.advice n))
+    (List.ofFn (nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re)) s i xs L
+  have hQ := rX_input n (pairEncode pk (samp.advice n))
     (List.ofFn (nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re)) s i xs L
   have hρ := length_ofFn_coins samp n ρ
   have hρ' := length_ofFn_coins samp n ρ'
@@ -588,7 +609,7 @@ theorem nmComp_abs (pk sk : List Bool) (ρ ρ' : samp.Coins n) (re : S.enc.Coins
       intro s' L
       obtain ⟨hm, hm'⟩ := nmMsgs_input S samp pl hl hist hist_poly r sl n pk ρ ρ' re s' 1
         (List.ofFn x) L hxl
-      rw [nmParams_qry, (fields_input (k := 2) n _ _ s' 1 _ L).1, List.length_replicate, hm, hm',
+      rw [nmParams_qry, rU_input (k := 2) n _ _ s' 1 _ L, List.length_replicate, hm, hm',
         nmPair_eq, ofFn_padFin_eq_padL]
     have hH : ∀ (s' q t : List Bool), (nmParams S samp pl hl hist hist_poly r sl).ansH
         (InteractiveHandler.input n (pairEncode pk (samp.advice n))
@@ -599,7 +620,7 @@ theorem nmComp_abs (pk sk : List Bool) (ρ ρ' : samp.Coins n) (re : S.enc.Coins
         List.ofFn (histWith hist (hl.eval n)
           (drawWith samp (S.msgLen.eval n) n (padFin (pl.eval n) (List.ofFn x)) ρ)) := by
       intro s' q t
-      rw [nmParams_ansH, (fields_input (k := 2) n _ _ s' 1 _ _).1, List.length_replicate,
+      rw [nmParams_ansH, rU_input (k := 2) n _ _ s' 1 _ _, List.length_replicate,
         (nmMsgs_input S samp pl hl hist hist_poly r sl n pk ρ ρ' re s' 1 (List.ofFn x) _ hxl).1,
         histWith_eq, ofFn_padFin_eq_padL]
     have hY : ∀ (s' q t : List Bool), (nmParams S samp pl hl hist hist_poly r sl).ansY
@@ -610,8 +631,8 @@ theorem nmComp_abs (pk sk : List Bool) (ρ ρ' : samp.Coins n) (re : S.enc.Coins
             [])) =
         EnsembleLemmas.padL (S.ctLen.eval n) t := by
       intro s' q t
-      rw [nmParams_ansY, (fields_input (k := 2) n _ _ s' 1 _ _).1, List.length_replicate,
-        rdAns_input]
+      rw [nmParams_ansY, rU_input (k := 2) n _ _ s' 1 _ _, List.length_replicate,
+        rAns_input]
     have hdraw : ∀ re' : S.enc.Coins n, encWith S n pk (drawWith (halfSamp S) (S.msgLen.eval n) n
         (nmPair S samp pl n ρ ρ' (padFin (pl.eval n) (List.ofFn x))) ((halfCoins S n).symm b)) re' =
         encWith S n pk (drawWith samp (S.msgLen.eval n) n (padFin (pl.eval n) (List.ofFn x))
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Rounds.lean b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Rounds.lean
index 0bd479f47..44fb61832 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Rounds.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Rounds.lean
@@ -9,31 +9,23 @@ set_option relaxedAutoImplicit false
 set_option autoImplicit false
 
 /-!
-# Rounds of interactive handlers
+# Coin strings of the IND ⇒ SIM machines
 
-Generic facts about T2's interactive handlers (`Games.InteractiveHandler`), used by the two
-machines of direction IND ⇒ SIM of [PS10, Theorem 174.8] (the simulator and the NM adversary).
+A local fact used by the two machines of direction IND ⇒ SIM of [PS10, Theorem 174.8] (the
+simulator and the NM adversary): a machine's coin string has `coins(n)` bits
+(`length_ofFn_coins`).
 
-* **Readers of a round input** `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩` (`rdU`, `rdZ`, `rdW`,
-  `rdState`,
-  `rdIdx`, `rdQuery`, `rdLog`, `rdAns`), with their values (`fields_input`) and their
-  polynomial-time bounds.
-* **One call** whose first round returns (`impl_of_ret`), or asks one outer query and returns in its
-  second round (`impl_of_query`); a finalization whose first round returns (`finish_of_ret`).
-* **Costs with a one-shot oracle** (`simulate_costBoundedBy_once`): if the calls are free except one
-  call, of cost at most one, that marks the state as used, the whole simulation costs at most one.
-
-## Main definitions
-
-* `NMSim.rdU`, `rdZ`, `rdW`, `rdState`, `rdIdx`, `rdQuery`, `rdLog`, `rdAns`.
-* `NMSim.seedEquiv`, `NMSim.seedEquivPoly`: seeds made of coins.
+The generic facts first proved here now live in shared modules: the readers of a round input are
+`Games.InteractiveHandler.rU`, …, `rAns`; the calls and finalizations whose rounds return at once
+or after one outer query are `Games.InteractiveHandler.impl_of_ret_padFin`,
+`impl_of_query_padFin` and `finish_of_ret_padFin`; the cost of a one-shot oracle is
+`Games.simulate_costBoundedBy_once`; the split of a padded concatenation is
+`Games.padFin_append_split`; the seeds made of coins are `EnsembleLemmas.seedEquiv` and
+`EnsembleLemmas.seedEquivPoly`.
 
 ## Main results
 
-* `NMSim.fields_input`, `NMSim.rdAns_input`, `NMSim.polyTimeComputable_rd`.
-* `NMSim.buildComp_of_ret`, `NMSim.impl_of_ret`, `NMSim.impl_of_query`, `NMSim.finish_of_ret`.
-* `NMSim.seedEquiv_ofFn`, `NMSim.seedEquivPoly_ofFn`, `NMSim.ofFn_padFin_eq_padL`.
-* `NMSim.costBoundedBy_bind_of_allOutputs`, `NMSim.simulate_costBoundedBy_once`.
+* `NMSim.length_ofFn_coins`.
 
 ## References
 
@@ -45,312 +37,9 @@ namespace TCSlib.Cryptography.Composability.NMSim
 
 open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
 
-/-! ### Readers of a round input -/
-
-/-- The parameter `1^n` of a round input `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`. -/
-def rdU (w : List Bool) : List Bool := pairFstD (pairFstD w)
-
-/-- `rdU w = pairFstD (pairFstD w)`. -/
-theorem rdU_eq (w : List Bool) : rdU w = pairFstD (pairFstD w) := rfl
-
-/-- The reduction input `z` of a round input. -/
-def rdZ (w : List Bool) : List Bool := pairFstD (pairSndD (pairFstD w))
-
-/-- `rdZ w = pairFstD (pairSndD (pairFstD w))`. -/
-theorem rdZ_eq (w : List Bool) : rdZ w = pairFstD (pairSndD (pairFstD w)) := rfl
-
-/-- The seed `ω` of a round input. -/
-def rdW (w : List Bool) : List Bool := pairSndD (pairSndD (pairFstD w))
-
-/-- `rdW w = pairSndD (pairSndD (pairFstD w))`. -/
-theorem rdW_eq (w : List Bool) : rdW w = pairSndD (pairSndD (pairFstD w)) := rfl
-
-/-- The state `s` of a round input. -/
-def rdState (w : List Bool) : List Bool := pairFstD (pairSndD w)
-
-/-- `rdState w = pairFstD (pairSndD w)`. -/
-theorem rdState_eq (w : List Bool) : rdState w = pairFstD (pairSndD w) := rfl
-
-/-- The oracle index `1^i` of a round input. -/
-def rdIdx (w : List Bool) : List Bool := pairFstD (pairFstD (pairSndD (pairSndD w)))
-
-/-- `rdIdx w = pairFstD (pairFstD (pairSndD (pairSndD w)))`. -/
-theorem rdIdx_eq (w : List Bool) : rdIdx w = pairFstD (pairFstD (pairSndD (pairSndD w))) := rfl
-
-/-- The query `x` of a round input. -/
-def rdQuery (w : List Bool) : List Bool := pairSndD (pairFstD (pairSndD (pairSndD w)))
-
-/-- `rdQuery w = pairSndD (pairFstD (pairSndD (pairSndD w)))`. -/
-theorem rdQuery_eq (w : List Bool) : rdQuery w = pairSndD (pairFstD (pairSndD (pairSndD w))) :=
-  rfl
-
-/-- The outer log `L` of the call so far. -/
-def rdLog (w : List Bool) : List Bool := pairSndD (pairSndD (pairSndD w))
-
-/-- `rdLog w = pairSndD (pairSndD (pairSndD w))`. -/
-theorem rdLog_eq (w : List Bool) : rdLog w = pairSndD (pairSndD (pairSndD w)) := rfl
-
-/-- The outer answer `y` of the first entry `⟨1^j, ⟨x, y⟩⟩` of the outer log. -/
-def rdAns (w : List Bool) : List Bool := pairSndD (pairSndD (pairFstD (rdLog w)))
-
-/-- `rdAns w = pairSndD (pairSndD (pairFstD (rdLog w)))`. -/
-theorem rdAns_eq (w : List Bool) : rdAns w = pairSndD (pairSndD (pairFstD (rdLog w))) := rfl
-
-section Fields
-
-variable {k : ℕ}
-
-/-- **The fields of a round input** (DL-30–36 overlap: the round-input readers of
-`Indistinguishability/Forward.lean`, here with the context): on
-`input n z ω s i x L = ⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩` the readers return `1^n`, `z`, `ω`,
-`s`, `1^i`, `x` and `L`. -/
-theorem fields_input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
-    rdU (InteractiveHandler.input n z ω s i x L) = List.replicate n true ∧
-      rdZ (InteractiveHandler.input n z ω s i x L) = z ∧
-      rdW (InteractiveHandler.input n z ω s i x L) = ω ∧
-      rdState (InteractiveHandler.input n z ω s i x L) = s ∧
-      rdIdx (InteractiveHandler.input n z ω s i x L) = List.replicate i true ∧
-      rdQuery (InteractiveHandler.input n z ω s i x L) = x ∧
-      rdLog (InteractiveHandler.input n z ω s i x L) = L := by
-  simp only [InteractiveHandler.input_eq, rdU, rdZ, rdW, rdState, rdIdx, rdQuery, rdLog,
-    pairFstD_pairEncode, pairSndD_pairEncode, and_self]
-
-/-- The answer of a one-entry outer log: `rdAns` of a round input with the log
-`⟨⟨1^j, ⟨x', y⟩⟩, t⟩` is `y`. -/
-theorem rdAns_input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x : List Bool) (j : ℕ)
-    (x' y t : List Bool) :
-    rdAns (InteractiveHandler.input n z ω s i x
-      (pairEncode (pairEncode (List.replicate j true) (pairEncode x' y)) t)) = y := by
-  rw [rdAns, (fields_input n z ω s i x _).2.2.2.2.2.2, pairFstD_pairEncode, pairSndD_pairEncode,
-    pairSndD_pairEncode]
-
-end Fields
-
-/-- The round-input readers are polynomial-time: `rdU`, `rdZ`, `rdW`, `rdState`, `rdIdx`,
-`rdQuery`, `rdLog` and `rdAns`. -/
-theorem polyTimeComputable_rd :
-    PolyTimeComputable rdU ∧ PolyTimeComputable rdZ ∧ PolyTimeComputable rdW ∧
-      PolyTimeComputable rdState ∧ PolyTimeComputable rdIdx ∧ PolyTimeComputable rdQuery ∧
-      PolyTimeComputable rdLog ∧ PolyTimeComputable rdAns := by
-  have hF := polyTimeComputable_pairFstD
-  have hD := polyTimeComputable_pairSndD
-  have hL : PolyTimeComputable rdLog := hD.comp (hD.comp hD)
-  exact ⟨hF.comp hF, hF.comp (hD.comp hF), hD.comp (hD.comp hF), hF.comp hD,
-    hF.comp (hF.comp (hD.comp hD)), hD.comp (hF.comp (hD.comp hD)), hL,
-    hD.comp (hD.comp (hF.comp hL))⟩
-
-/-! ### Calls and finalizations -/
-
-/-- A final output is the computation at every budget: if `next hist = ret a`, then
-`buildComp next t q hist = pure a`. -/
-theorem buildComp_of_ret {ι α : Type} {spec : OracleSpec ι} {next : QueryLog spec → Move spec α}
-    {t : α} {q : ℕ} {hist : QueryLog spec} {a : α} (h : next hist = .ret a) :
-    buildComp next t q hist = .pure a := by
-  cases q with
-  | zero => exact buildComp_zero_of_ret h
-  | succ q => exact buildComp_succ_of_ret h
-
-/-- The two parts of a padded concatenation: if `|u| = d₁`, the first `d₁` bits of
-`padFin (d₁ + d₂) (u ++ v)` are `padFin d₁ u` and the rest `padFin d₂ v`. -/
-theorem padFin_append_split {d₁ d₂ : ℕ} (u v : List Bool) (hu : u.length = d₁) :
-    (fun j : Fin d₁ => padFin (d₁ + d₂) (u ++ v) (Fin.castAdd d₂ j)) = padFin d₁ u ∧
-      (fun j : Fin d₂ => padFin (d₁ + d₂) (u ++ v) (Fin.natAdd d₁ j)) = padFin d₂ v := by
-  refine ⟨funext fun j => ?_, funext fun j => ?_⟩
-  · rw [padFin_apply, padFin_apply, Fin.coe_castAdd, List.getD_append _ _ _ _ (by omega)]
-  · rw [padFin_apply, padFin_apply, Fin.coe_natAdd, List.getD_append_right _ _ _ _ (by omega)]
-    congr 1
-    omega
-
-section Calls
-
-variable {k k' : ℕ} {din dout : Fin k → PolyExpr} {din' dout' : Fin k' → PolyExpr}
-  (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
-  (ω : Fin (H.seedLen.eval n) → Bool)
-
-/-- **A call that returns at once:** if the first round on the inner query `x` to oracle `i` in
-state `s` returns `⟨[true], u ‖ v⟩` with `|u| = dout i`, `|v| = stateLen`, the call answers
-`padFin _ u` with the new state `padFin _ v`, asking nothing. -/
-theorem impl_of_ret (i : Fin k) (x : Fin ((din i).eval n) → Bool)
-    (s : Fin (H.stateLen.eval n) → Bool) (u v : List Bool) (hu : u.length = (dout i).eval n)
-    (hv : v.length = H.stateLen.eval n)
-    (hrun : H.run (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x) []) =
-      pairEncode [true] (u ++ v)) :
-    H.impl n z ω i x s = .pure (padFin _ u, padFin _ v) := by
-  have hw : u ++ v = List.ofFn (padFin ((dout i).eval n + H.stateLen.eval n) (u ++ v)) :=
-    (ofFn_padFin_of_length (by rw [List.length_append, hu, hv])).symm
-  rw [InteractiveHandler.impl_apply, InteractiveHandler.call_eq,
-    buildComp_of_ret (a := padFin ((dout i).eval n + H.stateLen.eval n) (u ++ v)) (by
-      rw [MachineCodec.encodeLog_nil, hrun]
-      exact (congrArg (fun w => decodeBitMove _ _ _ (pairEncode [true] w)) hw).trans
-        (decodeBitMove_ret _ _ _ _)), OracleComp.pure_bind]
-  obtain ⟨h₁, h₂⟩ := padFin_append_split (d₂ := H.stateLen.eval n) u v hu
-  rw [h₁, h₂]
-
-/-- **A call with one outer query:** if the first round asks the outer query `x'` to oracle `j`,
-and the second round, with the answer `y` in the outer log, returns `⟨[true], u y ‖ v y⟩`, then
-(with `perCall ≥ 1`) the call is `query j x' (fun y => pure (padFin _ (u y), padFin _ (v y)))`.
-
-**Proof sketch.** Unfold the call (`impl_apply`, `call_eq`) at the budget `perCall = p + 1`. The
-first round decodes to the query (`decodeBitMove_query`), which `buildComp_succ_of_query` asks.
-After the answer `y` the log encodes as in `hrun₁` (`bitCodec_encodeEntry`), the second round
-decodes to the return of `padFin _ (u y ‖ v y)` (`buildComp_of_ret`, `decodeBitMove_ret`), and
-`padFin_append_split` splits it into the answer and the state. -/
-theorem impl_of_query (i : Fin k) (x : Fin ((din i).eval n) → Bool)
-    (s : Fin (H.stateLen.eval n) → Bool) (j : Fin k') (x' : Fin ((din' j).eval n) → Bool)
-    (u v : (Fin ((dout' j).eval n) → Bool) → List Bool)
-    (hu : ∀ y, (u y).length = (dout i).eval n) (hv : ∀ y, (v y).length = H.stateLen.eval n)
-    (hpc : 1 ≤ H.perCall.eval n)
-    (hrun₀ : H.run (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x) []) =
-      pairEncode [false] (pairEncode (List.replicate j true) (List.ofFn x')))
-    (hrun₁ : ∀ y, H.run (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x)
-      (pairEncode (pairEncode (List.replicate j true) (pairEncode (List.ofFn x') (List.ofFn y)))
-        [])) = pairEncode [true] (u y ++ v y)) :
-    H.impl n z ω i x s = .query j x' fun y => .pure (padFin _ (u y), padFin _ (v y)) := by
-  obtain ⟨p, hp⟩ : ∃ p, H.perCall.eval n = p + 1 := ⟨H.perCall.eval n - 1, by omega⟩
-  rw [InteractiveHandler.impl_apply, InteractiveHandler.call_eq, hp,
-    buildComp_succ_of_query (i := j) (x := x') (by
-      rw [MachineCodec.encodeLog_nil, hrun₀]
-      exact decodeBitMove_query (fun j => (din' j).eval n) (fun j => (dout' j).eval n) _ j x'),
-    OracleComp.query_bind]
-  congr 1
-  funext y
-  have hlog : (bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog
-      ([] ++ [⟨j, x', y⟩]) = pairEncode (pairEncode (List.replicate j true)
-        (pairEncode (List.ofFn x') (List.ofFn y))) [] := by
-    rw [List.nil_append, MachineCodec.encodeLog_cons, MachineCodec.encodeLog_nil,
-      bitCodec_encodeEntry]
-  have hw : u y ++ v y = List.ofFn (padFin ((dout i).eval n + H.stateLen.eval n) (u y ++ v y)) :=
-    (ofFn_padFin_of_length (by rw [List.length_append, hu, hv])).symm
-  rw [buildComp_of_ret (a := padFin ((dout i).eval n + H.stateLen.eval n) (u y ++ v y)) (by
-      rw [hlog, hrun₁]
-      exact (congrArg (fun w => decodeBitMove _ _ _ (pairEncode [true] w)) hw).trans
-        (decodeBitMove_ret _ _ _ _)), OracleComp.pure_bind]
-  obtain ⟨h₁, h₂⟩ := padFin_append_split (d₂ := H.stateLen.eval n) (u y) (v y) (hu y)
-  rw [h₁, h₂]
-
-/-- **A finalization that returns at once:** if its first round returns `⟨[true], b⟩` with
-`|b| = outLen(n)`, the finalization is `pure (padFin _ b)`, asking nothing. -/
-theorem finish_of_ret (s : Fin (H.stateLen.eval n) → Bool) {d : ℕ} (a : Fin d → Bool)
-    (b : List Bool) (hb : b.length = H.outLen.eval n)
-    (hrun : H.finRun (InteractiveHandler.finInput n z (List.ofFn ω) (List.ofFn s) (List.ofFn a)
-      []) = pairEncode [true] b) :
-    H.finish n z ω s a = .pure (padFin _ b) := by
-  rw [InteractiveHandler.finish_eq]
-  refine buildComp_of_ret ?_
-  rw [MachineCodec.encodeLog_nil, hrun]
-  exact (congrArg (fun w => decodeBitMove _ _ _ (pairEncode [true] w))
-    (ofFn_padFin_of_length hb).symm).trans (decodeBitMove_ret _ _ _ _)
-
-end Calls
-
-/-! ### Seeds and padding -/
-
-/-- **A seed of two machines' coins:** for `L = A.coins + B.coins`,
-`A.Coins n × B.Coins n ≃ {0,1}^{L(n)}`, concatenating the two coin strings (`seedEquiv_ofFn`). -/
-def seedEquiv {A B : NUPPT} {L : PolyExpr} (h : L = A.coins.add B.coins) (n : ℕ) :
-    A.Coins n × B.Coins n ≃ (Fin (L.eval n) → Bool) :=
-  ((NUPPT.coinsEquivPoly rfl n).prodCongr (NUPPT.coinsEquivPoly rfl n)).trans
-    (EnsembleLemmas.coinsEquiv (by rw [h, PolyExpr.eval_add]))
-
-/-- The seed is the concatenation of the coins: `⟦seedEquiv h n (r₁, r₂)⟧ = ⟦r₁⟧ ++ ⟦r₂⟧`. -/
-theorem seedEquiv_ofFn {A B : NUPPT} {L : PolyExpr} (h : L = A.coins.add B.coins) (n : ℕ)
-    (c : A.Coins n × B.Coins n) :
-    List.ofFn (seedEquiv h n c) = List.ofFn c.1 ++ List.ofFn c.2 := by
-  rw [seedEquiv, Equiv.trans_apply, EnsembleLemmas.ofFn_coinsEquiv, Equiv.prodCongr_apply,
-    Prod.map_fst, Prod.map_snd, NUPPT.coinsEquivPoly_ofFn, NUPPT.coinsEquivPoly_ofFn]
-
-/-- **A seed of a machine's coins and a string:** for `L = A.coins + L₂`,
-`A.Coins n × {0,1}^{L₂(n)} ≃ {0,1}^{L(n)}`, concatenating (`seedEquivPoly_ofFn`). -/
-def seedEquivPoly {A : NUPPT} {L L₂ : PolyExpr} (h : L = A.coins.add L₂) (n : ℕ) :
-    A.Coins n × (Fin (L₂.eval n) → Bool) ≃ (Fin (L.eval n) → Bool) :=
-  ((NUPPT.coinsEquivPoly rfl n).prodCongr (Equiv.refl _)).trans
-    (EnsembleLemmas.coinsEquiv (by rw [h, PolyExpr.eval_add]))
-
-/-- The seed is the concatenation: `⟦seedEquivPoly h n (r, w)⟧ = ⟦r⟧ ++ ⟦w⟧`. -/
-theorem seedEquivPoly_ofFn {A : NUPPT} {L L₂ : PolyExpr} (h : L = A.coins.add L₂) (n : ℕ)
-    (c : A.Coins n × (Fin (L₂.eval n) → Bool)) :
-    List.ofFn (seedEquivPoly h n c) = List.ofFn c.1 ++ List.ofFn c.2 := by
-  rw [seedEquivPoly, Equiv.trans_apply, EnsembleLemmas.ofFn_coinsEquiv, Equiv.prodCongr_apply,
-    Prod.map_fst, Prod.map_snd, NUPPT.coinsEquivPoly_ofFn, Equiv.refl_apply]
-
 /-- A machine's coins have `coins(n)` bits: `|⟦r⟧| = A.coins.eval n`. -/
 theorem length_ofFn_coins (A : NUPPT) (n : ℕ) (r : A.Coins n) :
     (List.ofFn r).length = A.coins.eval n := by
   rw [List.length_ofFn, NUPPT.coinLen_eq]
 
-/-- `⟦padFin k a⟧ = padL k a` (DL-30–36 overlap: the private `ofFn_padFin_eq_padL` of
-`AdaptiveCPA/Handler.lean`, from the public `ofFn_padFin_eq_take`). -/
-theorem ofFn_padFin_eq_padL (k : ℕ) (a : List Bool) :
-    List.ofFn (padFin k a) = EnsembleLemmas.padL k a := by
-  rw [EnsembleLemmas.padL_eq, ofFn_padFin_eq_take]
-
-/-! ### Costs with a one-shot oracle -/
-
-section Cost
-
-variable {ι ι' σ α β : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
-
-/-- **Costs add under sequencing, on the possible outputs:** if `c` fits in `q₁`, every possible
-output of `c` satisfies `P`, and `f a` fits in `q₂` for every `a` with `P a`, then `c` followed by
-`f` fits in `q₁ + q₂`. -/
-theorem costBoundedBy_bind_of_allOutputs {cost : ι → ℕ} {c : OracleComp spec α}
-    {f : α → OracleComp spec β} {P : α → Prop} {q₁ q₂ : ℕ} (hc : c.CostBoundedBy cost q₁)
-    (hP : c.AllOutputs P) (hf : ∀ a, P a → (f a).CostBoundedBy cost q₂) :
-    (c.bind f).CostBoundedBy cost (q₁ + q₂) := by
-  induction c generalizing q₁ with
-  | pure a =>
-    rw [OracleComp.pure_bind]
-    exact (hf a (OracleComp.allOutputs_pure.1 hP)).mono (Nat.le_add_left _ _)
-  | query i x k ih =>
-    obtain ⟨hi, hk⟩ := (OracleComp.costBoundedBy_query _ _ _ _ _).1 hc
-    rw [OracleComp.query_bind]
-    refine (OracleComp.costBoundedBy_query _ _ _ _ _).2
-      ⟨Nat.le_trans hi (Nat.le_add_right _ _), fun y => ?_⟩
-    rw [Nat.sub_add_comm hi]
-    exact ih y (hk y) (OracleComp.allOutputs_query.1 hP y)
-
-/-- **A one-shot oracle costs at most one query in total.** Let `good` be an invariant of the
-states and `used` mark the states after the costly call. If from a good used state every call is
-free and keeps the state good and used, and from a good unused state every call is either free and
-keeps the state good and unused, or costs at most `1` and leaves it good and used, then the
-simulation of any computation from a good state costs at most `0` (used) or `1` (unused).
-
-**Proof sketch.** Induction on the computation; at a query, `costBoundedBy_bind_of_allOutputs`
-with the call's cost and the continuation's (`0 + 0`, `0 + 1` or `1 + 0`). -/
-theorem simulate_costBoundedBy_once (impl : QueryImpl spec σ spec') (cost : ι' → ℕ)
-    (good used : σ → Prop) [DecidablePred used]
-    (hused : ∀ i x s, good s → used s →
-      (impl i x s).CostBoundedBy cost 0 ∧ (impl i x s).AllOutputs fun p => good p.2 ∧ used p.2)
-    (hfresh : ∀ i x s, good s → ¬ used s →
-      ((impl i x s).CostBoundedBy cost 0 ∧
-          (impl i x s).AllOutputs fun p => good p.2 ∧ ¬ used p.2) ∨
-        ((impl i x s).CostBoundedBy cost 1 ∧ (impl i x s).AllOutputs fun p => good p.2 ∧ used p.2))
-    (c : OracleComp spec α) :
-    ∀ s, good s → (simulate impl c s).CostBoundedBy cost (if used s then 0 else 1) := by
-  induction c with
-  | pure a =>
-    intro s _
-    rw [simulate_pure]
-    exact OracleComp.costBoundedBy_pure _ _ _
-  | query i x k ih =>
-    intro s hs
-    rw [simulate_query]
-    by_cases hu : used s
-    · obtain ⟨h₀, hP⟩ := hused i x s hs hu
-      have := costBoundedBy_bind_of_allOutputs h₀ hP fun p hp => by
-        have h := ih p.1 p.2 hp.1
-        rwa [if_pos hp.2] at h
-      rwa [if_pos hu]
-    · rw [if_neg hu]
-      rcases hfresh i x s hs hu with ⟨h₀, hP⟩ | ⟨h₁, hP⟩
-      · have := costBoundedBy_bind_of_allOutputs h₀ hP fun p hp => by
-          have h := ih p.1 p.2 hp.1
-          rwa [if_neg hp.2] at h
-        rwa [Nat.zero_add] at this
-      · exact costBoundedBy_bind_of_allOutputs h₁ hP fun p hp => by
-          have h := ih p.1 p.2 hp.1
-          rwa [if_pos hp.2] at h
-
-end Cost
-
 end TCSlib.Cryptography.Composability.NMSim
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/SimIND.lean b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/SimIND.lean
index 3e06a04d2..eec9b449c 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/SimIND.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/SimIND.lean
@@ -293,15 +293,16 @@ theorem accept_nmGame_eq_rImpl (atk : Attack) (A : NUPPT) (q ℓ : ℕ) (D : NUP
 
 /-! ### The SIM adversary -/
 
-open NMCCA2 (fwdHandler fwdHandler_finRun fwdHandler_finCall fwdHandler_advIn
-  simulate_fwdHandler_impl fields_finInput polyTimeComputable_finFields finA)
+open NMCCA2 (simulate_fwdHandler_impl)
+open TCSlib.Cryptography.Games.InteractiveHandler (rU rZ rW rS rI rX rL rAns finA)
+open TCSlib.Cryptography.Games.InteractiveHandler (finA_finInput polyTimeComputable_finA)
 
 /-- The SIM adversary's finalization round: output the adversary's output, `⟨[true], a⟩`. -/
 private def copyFin (w : List Bool) : List Bool := pairEncode [true] (finA w)
 
 /-- The finalization round is polynomial-time. -/
 private theorem polyTimeComputable_copyFin : PolyTimeComputable copyFin :=
-  (polyTimeComputable_const [true]).pairEncode polyTimeComputable_finFields.2.2.2.1
+  (polyTimeComputable_const [true]).pairEncode polyTimeComputable_finA
 
 /-- The adversary's input is the reduction input. -/
 private theorem polyTimeComputable_copyAdvIn :
@@ -309,7 +310,7 @@ private theorem polyTimeComputable_copyAdvIn :
   polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
 
 /-- **The SIM adversary's handler** (on the real experiment's oracles with parameter length `pl`
-and history length `hl`): it forwards every query (`NMCCA2.fwdHandler`), runs the adversary on the
+and history length `hl`): it forwards every query (`Games.fwdHandler`), runs the adversary on the
 reduction input, asks nothing in finalization, and outputs the adversary's `outLen(n)`-bit
 output. -/
 def copyHandler (pl hl outLen : PolyExpr) :
@@ -328,7 +329,7 @@ theorem copyHandler_advInput (pl hl outLen : PolyExpr) (n : ℕ) (z : List Bool)
 /-- The SIM adversary outputs `outLen(n)` bits: `(copyHandler S pl hl outLen).outLen = outLen`. -/
 theorem copyHandler_outLen (pl hl outLen : PolyExpr) :
     (copyHandler S pl hl outLen).outLen = outLen := by
-  rw [copyHandler, NMCCA2.fwdHandler_outLen]
+  rw [copyHandler, fwdHandler_outLen]
 
 /-- **The handler forwards** (`simulate_fwdHandler_impl`). -/
 theorem simulate_copyHandler_impl (pl hl outLen : PolyExpr) (n : ℕ) (z : List Bool)
@@ -356,7 +357,7 @@ theorem copyHandler_finish (pl hl outLen : PolyExpr) (n : ℕ) (z : List Bool)
   rw [InteractiveHandler.finish_eq, hfc, PolyExpr.eval_const]
   refine buildComp_zero_of_ret ?_
   show decodeBitMove _ _ _ ((copyHandler S pl hl outLen).finRun _) = _
-  rw [hfin, copyFin, (fields_finInput _ _ _ _ _ _).2.2.2.1]
+  rw [hfin, copyFin, finA_finInput _ _ _ _ _ _]
   have hw : List.ofFn (padFin ((copyHandler S pl hl outLen).outLen.eval n) (List.ofFn a)) =
       List.ofFn a := ofFn_padFin_of_length (by rw [List.length_ofFn, hol, hd])
   exact (congrArg (fun w => decodeBitMove _ _ _ (pairEncode [true] w)) hw).symm.trans
@@ -615,24 +616,24 @@ theorem nmOutput_eq_entryTails (n ℓ : ℕ) (sk : List Bool)
     (w : List Bool) (hw : w.length = ℓ * S.ctLen.eval n) :
     S.nmOutput sk s' (padFin (ℓ * S.ctLen.eval n) w) =
       ((List.range ℓ).map fun i => (entryL S n sk
-        (decide (s'.map List.ofFn = some (chunkAt (S.ctLen.eval n) i w)))
-        (chunkAt (S.ctLen.eval n) i w)).drop 1).flatten := by
+        (decide (s'.map List.ofFn = some (coinBlock (S.ctLen.eval n) i w)))
+        (coinBlock (S.ctLen.eval n) i w)).drop 1).flatten := by
   rw [S.nmOutput_eq]
   congr 1
   refine List.ext_getElem (by rw [List.length_ofFn, List.length_map, List.length_range])
     fun i h₁ h₂ => ?_
   rw [List.getElem_ofFn, List.getElem_map, List.getElem_range, entryL_drop_one, S.nmDecrypt_eq]
   have hc : List.ofFn (S.nthCt (padFin (ℓ * S.ctLen.eval n) w) ⟨i, by
-      rw [List.length_ofFn] at h₁; exact h₁⟩) = chunkAt (S.ctLen.eval n) i w := by
-    rw [S.ofFn_nthCt, ofFn_padFin_of_length hw, chunkAt_eq]
+      rw [List.length_ofFn] at h₁; exact h₁⟩) = coinBlock (S.ctLen.eval n) i w := by
+    rw [S.ofFn_nthCt, ofFn_padFin_of_length hw, coinBlock_eq]
   have hcopy : (s' = some (S.nthCt (padFin (ℓ * S.ctLen.eval n) w) ⟨i, by
       rw [List.length_ofFn] at h₁; exact h₁⟩)) ↔
-      s'.map List.ofFn = some (chunkAt (S.ctLen.eval n) i w) := by
+      s'.map List.ofFn = some (coinBlock (S.ctLen.eval n) i w) := by
     rw [← hc]
     cases s' with
     | none => simp
     | some c => simp [List.ofFn_inj]
-  by_cases h : s'.map List.ofFn = some (chunkAt (S.ctLen.eval n) i w)
+  by_cases h : s'.map List.ofFn = some (coinBlock (S.ctLen.eval n) i w)
   · rw [if_pos (hcopy.2 h), decide_eq_true h, if_pos rfl, ofFn_zeroBits]
   · rw [if_neg (fun h' => h (hcopy.1 h')), decide_eq_false h, if_neg Bool.false_ne_true, hc]
 
@@ -689,11 +690,11 @@ private def badHalves (s : Option ((Fin (S.ctLen.eval n) → Bool) ×
 private instance : DecidablePred (badHalves S n) := fun _ => instDecidableNot
 
 /-- **The coupling of the two coins:** `𝔼[G · 1_{m₀ = m₁}]` is the same with the sampler's coin
-`0` and `1` (`expect_eq_until_bad`): the oracles agree while the recorded parameter has equal
-halves, and a bad parameter stays recorded.
+`0` and `1` (`Games.expect_eq_until_bad`): the oracles agree while the recorded parameter has
+equal halves, and a bad parameter stays recorded.
 
-**Proof sketch.** `expect_eq_until_bad` with the bad event `badHalves`. The empty state is good
-(its parameter reads `0`, `ofFn_zeroBits`), and a recorded state stays recorded (`rImpl_dec`,
+**Proof sketch.** `Games.expect_eq_until_bad` with the bad event `badHalves`. The empty state is
+good (its parameter reads `0`, `ofFn_zeroBits`), and a recorded state stays recorded (`rImpl_dec`,
 `rImpl_some`), so bad is sticky. From a good state the two oracles agree: `Dec` and repeated
 challenges do not read the coin (the history is empty), and on a first challenge, after the same
 encryption coins, the new state is bad on both sides or `m₀ = m₁` and the two draws coincide
@@ -816,11 +817,11 @@ theorem real_identity (D : NUPPT) (rD : D.Coins n) (ρ'' : (halfDist S).Coins n)
         S.msgLen.eval n := List.length_ofFn
     have hes : ((List.range ℓ).map fun i => entryL S n sk
         (decide ((p.2.map Prod.fst).map List.ofFn =
-          some (chunkAt (S.ctLen.eval n) i (List.ofFn p.1))))
-        (chunkAt (S.ctLen.eval n) i (List.ofFn p.1))) =
+          some (coinBlock (S.ctLen.eval n) i (List.ofFn p.1))))
+        (coinBlock (S.ctLen.eval n) i (List.ofFn p.1))) =
         (((List.range ℓ).map fun i => Prod.mk (decide ((p.2.map Prod.fst).map List.ofFn =
-          some (chunkAt (S.ctLen.eval n) i (List.ofFn p.1))))
-          (chunkAt (S.ctLen.eval n) i (List.ofFn p.1))).map
+          some (coinBlock (S.ctLen.eval n) i (List.ofFn p.1))))
+          (coinBlock (S.ctLen.eval n) i (List.ofFn p.1))).map
           fun e : Bool × List Bool => entryL S n sk e.1 e.2) := by
       rw [List.map_map]
       rfl
@@ -829,8 +830,8 @@ theorem real_identity (D : NUPPT) (rD : D.Coins n) (ρ'' : (halfDist S).Coins n)
       List.map_map]
     have hnm : ((List.range ℓ).map ((fun e : Bool × List Bool => (entryL S n sk e.1 e.2).drop 1) ∘
         fun i => Prod.mk (decide ((p.2.map Prod.fst).map List.ofFn =
-          some (chunkAt (S.ctLen.eval n) i (List.ofFn p.1))))
-          (chunkAt (S.ctLen.eval n) i (List.ofFn p.1)))).flatten =
+          some (coinBlock (S.ctLen.eval n) i (List.ofFn p.1))))
+          (coinBlock (S.ctLen.eval n) i (List.ofFn p.1)))).flatten =
         S.nmOutput sk (p.2.map Prod.fst) (padFin (ℓ * S.ctLen.eval n) (List.ofFn p.1)) := by
       rw [nmOutput_eq_entryTails S n ℓ sk _ _ List.length_ofFn, Option.map_map]
       rfl
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Simulator.lean b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Simulator.lean
index 2e67f7489..ef14ff53d 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Simulator.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Simulator.lean
@@ -44,45 +44,53 @@ hybrid's view of `A`'s (`idealView_simOut`).
 namespace TCSlib.Cryptography.Composability.NMSim
 
 open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
-open NMCCA2 (finU finA fields_finInput polyTimeComputable_finFields)
+open TCSlib.Cryptography.Games.InteractiveHandler (rU rZ rW rS rI rX rL rAns finA)
+open TCSlib.Cryptography.EnsembleLemmas (seedEquiv seedEquiv_ofFn ofFn_padFin_eq_padL)
+open TCSlib.Cryptography.Games.InteractiveHandler (rU_input rZ_input rW_input rX_input rAns_input
+  rU_finInput rS_finInput finA_finInput polyTimeComputable_rU polyTimeComputable_rZ
+  polyTimeComputable_rW polyTimeComputable_rS polyTimeComputable_rX polyTimeComputable_rAns
+  polyTimeComputable_finA)
 
 variable (S : FixedLengthPKScheme) (samp : NUPPT)
 
 /-! ### The dummy challenge -/
 
-/-- The dummy message `m̃ = M(a; ρ̃)` read in a round `w`: with `n = |rdU w|`, `a = rdQuery w`, the
-advice `α = snd (rdZ w)` and `ρ̃` the first `coins(n)` bits of the seed, `padL msgLen(n)` of `M`'s
+/-- The dummy message `m̃ = M(a; ρ̃)` read in a round `w`: with `n = |rU w|`, `a = rX w`, the
+advice `α = snd (rZ w)` and `ρ̃` the first `coins(n)` bits of the seed, `padL msgLen(n)` of `M`'s
 output on `layout 1^n a α ρ̃`. -/
 def simMsg (w : List Bool) : List Bool :=
-  EnsembleLemmas.padL (S.msgLen.eval (rdU w).length)
-    (samp.output (NUPPT.layout (rdU w) (rdQuery w) (pairSndD (rdZ w))
-      ((rdW w).take (samp.coins.eval (rdU w).length))))
+  EnsembleLemmas.padL (S.msgLen.eval (rU w).length)
+    (samp.output (NUPPT.layout (rU w) (rX w) (pairSndD (rZ w))
+      ((rW w).take (samp.coins.eval (rU w).length))))
 
 /-- `simMsg S samp w = padL msgLen(n) (M.output (layout 1^n a α ρ̃))`. -/
 theorem simMsg_eq (w : List Bool) :
-    simMsg S samp w = EnsembleLemmas.padL (S.msgLen.eval (rdU w).length)
-      (samp.output (NUPPT.layout (rdU w) (rdQuery w) (pairSndD (rdZ w))
-        ((rdW w).take (samp.coins.eval (rdU w).length)))) := rfl
+    simMsg S samp w = EnsembleLemmas.padL (S.msgLen.eval (rU w).length)
+      (samp.output (NUPPT.layout (rU w) (rX w) (pairSndD (rZ w))
+        ((rW w).take (samp.coins.eval (rU w).length)))) := rfl
 
-/-- The dummy challenge `ỹ = Enc_pk(m̃; re)` read in a round `w`: `pk = fst (rdZ w)`, `re` the seed
+/-- The dummy challenge `ỹ = Enc_pk(m̃; re)` read in a round `w`: `pk = fst (rZ w)`, `re` the seed
 after `ρ̃`, `padL ctLen(n)` of `Enc`'s output on `⟨⟨⟨1^n, ⟨pk, m̃⟩⟩, []⟩, re⟩`. -/
 def simCt (w : List Bool) : List Bool :=
-  EnsembleLemmas.padL (S.ctLen.eval (rdU w).length)
-    (S.enc.output (pairEncode (pairEncode (pairEncode (rdU w)
-      (pairEncode (pairFstD (rdZ w)) (simMsg S samp w))) [])
-      ((rdW w).drop (samp.coins.eval (rdU w).length))))
+  EnsembleLemmas.padL (S.ctLen.eval (rU w).length)
+    (S.enc.output (pairEncode (pairEncode (pairEncode (rU w)
+      (pairEncode (pairFstD (rZ w)) (simMsg S samp w))) [])
+      ((rW w).drop (samp.coins.eval (rU w).length))))
 
 /-- `simCt S samp w = padL ctLen(n) (Enc.output ⟨⟨⟨1^n, ⟨pk, m̃⟩⟩, []⟩, re⟩)`. -/
 theorem simCt_eq (w : List Bool) :
-    simCt S samp w = EnsembleLemmas.padL (S.ctLen.eval (rdU w).length)
-      (S.enc.output (pairEncode (pairEncode (pairEncode (rdU w)
-        (pairEncode (pairFstD (rdZ w)) (simMsg S samp w))) [])
-        ((rdW w).drop (samp.coins.eval (rdU w).length)))) := rfl
+    simCt S samp w = EnsembleLemmas.padL (S.ctLen.eval (rU w).length)
+      (S.enc.output (pairEncode (pairEncode (pairEncode (rU w)
+        (pairEncode (pairFstD (rZ w)) (simMsg S samp w))) [])
+        ((rW w).drop (samp.coins.eval (rU w).length)))) := rfl
 
 /-- The dummy message is polynomial-time. -/
 theorem polyTimeComputable_simMsg : PolyTimeComputable (simMsg S samp) := by
-  obtain ⟨hU, hZ, hW, -, -, hQ, -, -⟩ := polyTimeComputable_rd
-  have hρ : PolyTimeComputable fun w => (rdW w).take (samp.coins.eval (rdU w).length) :=
+  have hU := polyTimeComputable_rU
+  have hZ := polyTimeComputable_rZ
+  have hW := polyTimeComputable_rW
+  have hQ := polyTimeComputable_rX
+  have hρ : PolyTimeComputable fun w => (rW w).take (samp.coins.eval (rU w).length) :=
     ((polyTimeComputable_pairTakePoly samp.coins).comp (hU.pairEncode hW)).congr fun w => by
       simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
   exact EnsembleLemmas.polyTimeComputable_padL S.msgLen hU (samp.polyTimeComputable_output.comp
@@ -90,8 +98,10 @@ theorem polyTimeComputable_simMsg : PolyTimeComputable (simMsg S samp) := by
 
 /-- The dummy challenge is polynomial-time. -/
 theorem polyTimeComputable_simCt : PolyTimeComputable (simCt S samp) := by
-  obtain ⟨hU, hZ, hW, -, -, -, -, -⟩ := polyTimeComputable_rd
-  have hre : PolyTimeComputable fun w => (rdW w).drop (samp.coins.eval (rdU w).length) :=
+  have hU := polyTimeComputable_rU
+  have hZ := polyTimeComputable_rZ
+  have hW := polyTimeComputable_rW
+  have hre : PolyTimeComputable fun w => (rW w).drop (samp.coins.eval (rU w).length) :=
     ((polyTimeComputable_pairDropPoly samp.coins).comp (hU.pairEncode hW)).congr fun w => by
       simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
   exact EnsembleLemmas.polyTimeComputable_padL S.ctLen hU (S.enc.polyTimeComputable_output.comp
@@ -101,21 +111,6 @@ theorem polyTimeComputable_simCt : PolyTimeComputable (simCt S samp) := by
 
 /-! ### The finalization -/
 
-/-- The state `s` of a finalization input `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩`. -/
-def finSt (w : List Bool) : List Bool := pairFstD (pairSndD w)
-
-/-- `finSt w = pairFstD (pairSndD w)`. -/
-theorem finSt_eq (w : List Bool) : finSt w = pairFstD (pairSndD w) := rfl
-
-/-- The state of a finalization input: `finSt (finInput n z ω s a L) = s`. -/
-theorem finSt_finInput (n : ℕ) (z ω s a L : List Bool) :
-    finSt (InteractiveHandler.finInput n z ω s a L) = s := by
-  rw [finSt, InteractiveHandler.finInput_eq, pairSndD_pairEncode, pairFstD_pairEncode]
-
-/-- The state reader is polynomial-time. -/
-theorem polyTimeComputable_finSt : PolyTimeComputable finSt :=
-  polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
-
 /-- **The flagged entry** of a ciphertext `c`, on the context `⟨1^n, s⟩` with the state
 `s = [flag] ‖ ỹ ‖ …`: `[flag ∧ c = ỹ]` followed by `c`. -/
 def flagF (ctx c : List Bool) : List Bool :=
@@ -148,14 +143,14 @@ theorem polyTimeComputable_flagF :
 (`r(n)` ciphertexts, then `σ`): the flagged entries `flagF ⟨1^n, st⟩ c_i`, then `σ`. -/
 def simOutL (r : PolyExpr) (n : ℕ) (st a : List Bool) : List Bool :=
   ((List.range (r.eval n)).map fun i =>
-    flagF S (pairEncode (List.replicate n true) st) (chunkAt (S.ctLen.eval n) i a)).flatten ++
+    flagF S (pairEncode (List.replicate n true) st) (coinBlock (S.ctLen.eval n) i a)).flatten ++
   a.drop (r.eval n * S.ctLen.eval n)
 
 /-- `simOutL S r n st a = (flagF ⟨1^n, st⟩ c_0 ++ ⋯ ++ flagF ⟨1^n, st⟩ c_{r-1}) ++ σ`. -/
 theorem simOutL_eq (r : PolyExpr) (n : ℕ) (st a : List Bool) :
     simOutL S r n st a =
       ((List.range (r.eval n)).map fun i =>
-        flagF S (pairEncode (List.replicate n true) st) (chunkAt (S.ctLen.eval n) i a)).flatten ++
+        flagF S (pairEncode (List.replicate n true) st) (coinBlock (S.ctLen.eval n) i a)).flatten ++
       a.drop (r.eval n * S.ctLen.eval n) := rfl
 
 /-- **The simulator's finalization round**: `⟨[true], F ‖ a.drop (r·ctLen)⟩`, with no outer query,
@@ -164,32 +159,33 @@ where `F` is `chunkMap ctLen flagF ⟨⟨1^n, s⟩, a.take (r·ctLen)⟩` (the f
 equal to `ỹ`). -/
 def simFin (r : PolyExpr) (w : List Bool) : List Bool :=
   pairEncode [true]
-    ((if decide (List.replicate (S.ctLen.eval (finU w).length) true = []) then
-        (if (finSt w).headD false then List.replicate (r.eval (finU w).length) true
-          else List.replicate (r.eval (finU w).length) false)
-      else chunkMap S.ctLen (flagF S) (pairEncode (pairEncode (finU w) (finSt w))
-        ((finA w).take ((r.mul S.ctLen).eval (finU w).length)))) ++
-    (finA w).drop ((r.mul S.ctLen).eval (finU w).length))
+    ((if decide (List.replicate (S.ctLen.eval (rU w).length) true = []) then
+        (if (rS w).headD false then List.replicate (r.eval (rU w).length) true
+          else List.replicate (r.eval (rU w).length) false)
+      else chunkMap S.ctLen (flagF S) (pairEncode (pairEncode (rU w) (rS w))
+        ((finA w).take ((r.mul S.ctLen).eval (rU w).length)))) ++
+    (finA w).drop ((r.mul S.ctLen).eval (rU w).length))
 
 /-- `simFin S r w = ⟨[true], F ‖ a.drop (r·ctLen)⟩`, with `F = flag^r` if `ctLen(n) = 0` and
 `F = chunkMap ctLen flagF ⟨⟨1^n, s⟩, a.take (r·ctLen)⟩` otherwise. -/
 theorem simFin_eq (r : PolyExpr) (w : List Bool) :
     simFin S r w = pairEncode [true]
-      ((if decide (List.replicate (S.ctLen.eval (finU w).length) true = []) then
-          (if (finSt w).headD false then List.replicate (r.eval (finU w).length) true
-            else List.replicate (r.eval (finU w).length) false)
-        else chunkMap S.ctLen (flagF S) (pairEncode (pairEncode (finU w) (finSt w))
-          ((finA w).take ((r.mul S.ctLen).eval (finU w).length)))) ++
-      (finA w).drop ((r.mul S.ctLen).eval (finU w).length)) := rfl
+      ((if decide (List.replicate (S.ctLen.eval (rU w).length) true = []) then
+          (if (rS w).headD false then List.replicate (r.eval (rU w).length) true
+            else List.replicate (r.eval (rU w).length) false)
+        else chunkMap S.ctLen (flagF S) (pairEncode (pairEncode (rU w) (rS w))
+          ((finA w).take ((r.mul S.ctLen).eval (rU w).length)))) ++
+      (finA w).drop ((r.mul S.ctLen).eval (rU w).length)) := rfl
 
 /-- The finalization round is polynomial-time. -/
 theorem polyTimeComputable_simFin (r : PolyExpr) : PolyTimeComputable (simFin S r) := by
-  obtain ⟨hU, -, -, hA, -⟩ := polyTimeComputable_finFields
-  have hS := polyTimeComputable_finSt
-  have htake : PolyTimeComputable fun w => (finA w).take ((r.mul S.ctLen).eval (finU w).length) :=
+  have hU := polyTimeComputable_rU
+  have hA := polyTimeComputable_finA
+  have hS := polyTimeComputable_rS
+  have htake : PolyTimeComputable fun w => (finA w).take ((r.mul S.ctLen).eval (rU w).length) :=
     ((polyTimeComputable_pairTakePoly (r.mul S.ctLen)).comp (hU.pairEncode hA)).congr fun w => by
       simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
-  have hdrop : PolyTimeComputable fun w => (finA w).drop ((r.mul S.ctLen).eval (finU w).length) :=
+  have hdrop : PolyTimeComputable fun w => (finA w).drop ((r.mul S.ctLen).eval (rU w).length) :=
     ((polyTimeComputable_pairDropPoly (r.mul S.ctLen)).comp (hU.pairEncode hA)).congr fun w => by
       simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
   exact (polyTimeComputable_const [true]).pairEncode
@@ -210,22 +206,24 @@ returns `⟨[true], simOutL …⟩`.
 **Proof sketch.** Read the fields of the input in `simFin_eq` and split on `ctLen(n)`. If
 `ctLen(n) = 0`, every chunk is empty and equals `ỹ`, so every flagged entry is `[flag]` and the
 `r` entries flatten to `flag^r`. Otherwise cut `a.take (r·ctLen)` into its `r` chunks of
-`ctLen(n)` bits (`take_eq_flatten_chunkAt`, `length_chunkAt`); `chunkMap_flatten` maps
+`ctLen(n)` bits (`take_eq_flatten_chunkAt`, `length_coinBlock`); `chunkMap_flatten` maps
 `flagF` over them, which is `simOutL_eq`. -/
 theorem simFin_finInput (r sl : PolyExpr) (n : ℕ) (z ω s a L : List Bool)
     (ha : a.length = r.eval n * S.ctLen.eval n + sl.eval n) :
     simFin S r (InteractiveHandler.finInput n z ω s a L) =
       pairEncode [true] (simOutL S r n s a) := by
-  obtain ⟨hU, -, -, hA, -⟩ := fields_finInput n z ω s a L
-  rw [simFin_eq, hU, hA, finSt_finInput, List.length_replicate, PolyExpr.eval_mul, simOutL_eq]
+  have hU := rU_finInput n z ω s a L
+  have hA := finA_finInput n z ω s a L
+  rw [simFin_eq, hU, hA, rS_finInput, List.length_replicate, PolyExpr.eval_mul, simOutL_eq]
   congr 2
   by_cases hct : S.ctLen.eval n = 0
   · rw [if_pos (by rw [hct, List.replicate_zero]; rfl)]
-    have hent : ∀ i, flagF S (pairEncode (List.replicate n true) s) (chunkAt (S.ctLen.eval n) i a) =
-        [s.headD false] := by
+    have hent : ∀ i,
+        flagF S (pairEncode (List.replicate n true) s) (coinBlock (S.ctLen.eval n) i a) =
+          [s.headD false] := by
       intro i
       rw [flagF_eq, pairSndD_pairEncode, pairFstD_pairEncode, List.length_replicate, hct,
-        chunkAt_eq, List.take_zero, List.take_zero, decide_eq_true rfl, Bool.and_true]
+        coinBlock_eq, List.take_zero, List.take_zero, decide_eq_true rfl, Bool.and_true]
     have hrep : ∀ (b : Bool) (m : ℕ), ((List.range m).map fun _ => [b]).flatten =
         List.replicate m b := by
       intro b m
@@ -242,7 +240,7 @@ theorem simFin_finInput (r sl : PolyExpr) (n : ℕ) (z ω s a L : List Bool)
     · rfl
     · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hch
       rw [List.mem_range] at hi
-      refine length_chunkAt _ _ _ ?_
+      refine length_coinBlock ?_
       rw [ha]
       have := Nat.mul_le_mul_right (S.ctLen.eval n) (show i + 1 ≤ r.eval n from hi)
       omega
@@ -263,16 +261,16 @@ def simParams (r sl : PolyExpr) : ChalParams S pl hl 1 (fun _ => pl) (fun _ => h
   advIn ctx := pairFstD (pairFstD (pairSndD ctx))
   advIn_poly := polyTimeComputable_pairFstD.comp
     (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
-  qry w := EnsembleLemmas.padL (pl.eval (rdU w).length) (rdQuery w)
-  qry_poly := EnsembleLemmas.polyTimeComputable_padL pl polyTimeComputable_rd.1
-    polyTimeComputable_rd.2.2.2.2.2.1
+  qry w := EnsembleLemmas.padL (pl.eval (rU w).length) (rX w)
+  qry_poly := EnsembleLemmas.polyTimeComputable_padL pl polyTimeComputable_rU
+    polyTimeComputable_rX
   qry_len _ := EnsembleLemmas.length_padL _ _
   ansY := simCt S samp
   ansY_poly := polyTimeComputable_simCt S samp
   ansY_len _ := EnsembleLemmas.length_padL _ _
-  ansH w := EnsembleLemmas.padL (hl.eval (rdU w).length) (rdAns w)
-  ansH_poly := EnsembleLemmas.polyTimeComputable_padL hl polyTimeComputable_rd.1
-    polyTimeComputable_rd.2.2.2.2.2.2.2
+  ansH w := EnsembleLemmas.padL (hl.eval (rU w).length) (rAns w)
+  ansH_poly := EnsembleLemmas.polyTimeComputable_padL hl polyTimeComputable_rU
+    polyTimeComputable_rAns
   ansH_len _ := EnsembleLemmas.length_padL _ _
   outLen := (r.mul (S.ctLen.add (.const 1))).add sl
   finCall := .const 1
@@ -315,12 +313,12 @@ theorem simFinish (z : List Bool)
       .pure (padFin _ (simOutL S r n (List.ofFn s) (List.ofFn a))) := by
   have ha : (List.ofFn a).length = r.eval n * S.ctLen.eval n + sl.eval n := by
     rw [List.length_ofFn, hd]
-  refine finish_of_ret _ n z ω s a _ ?_ ?_
+  refine InteractiveHandler.finish_of_ret_padFin _ n z ω s a _ ?_ ?_
   · rw [simParams_outLen_eval, simOutL_eq, List.length_append, List.length_drop, ha,
       length_flatten_map_range (S.ctLen.eval n + 1) _ _ fun i hi => ?_]
     · rw [Nat.mul_add, Nat.mul_one]
       omega
-    · rw [length_flagF, length_chunkAt _ _ _ (by
+    · rw [length_flagF, length_coinBlock (by
         rw [ha]
         have := Nat.mul_le_mul_right (S.ctLen.eval n) (show i + 1 ≤ r.eval n from hi)
         omega)]
@@ -376,7 +374,16 @@ theorem simCt_input (pk : List Bool) (ρ' : samp.Coins n) (re : S.enc.Coins n) (
         (1 : Fin 2) (List.ofFn x) L) =
       List.ofFn (encWith S n pk (drawWith samp (S.msgLen.eval n) n
         (padFin (pl.eval n) (List.ofFn x)) ρ') re) := by
-  obtain ⟨hU, hZ, hW, -, -, hQ, -⟩ := fields_input (k := 2) n (pairEncode pk (samp.advice n))
+  have hU := rU_input (k := 2) n (pairEncode pk (samp.advice n))
+    (List.ofFn (seedEquiv (simParams_seedLen_handler S samp pl hl r sl) n (ρ', re))) s 1
+    (List.ofFn x) L
+  have hZ := rZ_input (k := 2) n (pairEncode pk (samp.advice n))
+    (List.ofFn (seedEquiv (simParams_seedLen_handler S samp pl hl r sl) n (ρ', re))) s 1
+    (List.ofFn x) L
+  have hW := rW_input (k := 2) n (pairEncode pk (samp.advice n))
+    (List.ofFn (seedEquiv (simParams_seedLen_handler S samp pl hl r sl) n (ρ', re))) s 1
+    (List.ofFn x) L
+  have hQ := rX_input (k := 2) n (pairEncode pk (samp.advice n))
     (List.ofFn (seedEquiv (simParams_seedLen_handler S samp pl hl r sl) n (ρ', re))) s 1
     (List.ofFn x) L
   have hxl : (List.ofFn x).length = pl.eval n := by
@@ -431,8 +438,8 @@ theorem simComp_abs (pk sk : List Bool) (ρ ρ' : samp.Coins n) (re : S.enc.Coin
           (List.ofFn (seedEquiv (simParams_seedLen_handler S samp pl hl r sl) n (ρ', re))) s'
           (1 : Fin 2) (List.ofFn x) L) = List.ofFn (padFin (pl.eval n) (List.ofFn x)) := by
       intro s' L
-      rw [simParams_qry, (fields_input (k := 2) n _ _ s' 1 _ L).1,
-        (fields_input (k := 2) n _ _ s' 1 _ L).2.2.2.2.2.1, List.length_replicate,
+      rw [simParams_qry, rU_input (k := 2) n _ _ s' 1 _ L,
+        rX_input (k := 2) n _ _ s' 1 _ L, List.length_replicate,
         ofFn_padFin_eq_padL]
     have hH : ∀ (s' q : List Bool) (y : Fin (hl.eval n) → Bool),
         (simParams S samp pl hl r sl).ansH
@@ -441,8 +448,8 @@ theorem simComp_abs (pk sk : List Bool) (ρ ρ' : samp.Coins n) (re : S.enc.Coin
           (1 : Fin 2) (List.ofFn x) (pairEncode (pairEncode (List.replicate 0 true)
             (pairEncode q (List.ofFn y))) [])) = List.ofFn y := by
       intro s' q y
-      rw [simParams_ansH, (fields_input (k := 2) n _ _ s' 1 _ _).1, List.length_replicate,
-        rdAns_input, EnsembleLemmas.padL_eq]
+      rw [simParams_ansH, rU_input (k := 2) n _ _ s' 1 _ _, List.length_replicate,
+        rAns_input, EnsembleLemmas.padL_eq]
       exact List.take_left' List.length_ofFn
     rw [simAbs_none, chalHandler_impl_none, simulate_query, histImpl_eq, OracleComp.pure_bind,
       simulate_pure, OracleComp.pure_bind, rImpl_none_eager, OracleComp.pure_bind, simAbs_some,
@@ -459,9 +466,10 @@ output `a` (`r·ctLen + sl` bits) and the hybrid's final state `s`, `idealView`
 output (flags from the abstracted state) with the history oracle's state is `realView` of `a` and
 `s`.
 
-**Proof sketch.** Entry `i` of the output is `flagF ⟨1^n, st⟩ c_i` (`chunkAt_flatten_append`), whose
-flag is `[c_i = y]` for the recorded `y` and `false` without a challenge (`headD_ofFn_chalState`,
-`ofFn_chalState_some`), as `realView`'s copy test; `σ` is the tail (`drop_flatten_append`). -/
+**Proof sketch.** Entry `i` of the output is `flagF ⟨1^n, st⟩ c_i` (`coinBlock_flatten_append`),
+whose flag is `[c_i = y]` for the recorded `y` and `false` without a challenge
+(`headD_ofFn_chalState`, `ofFn_chalState_some`), as `realView`'s copy test; `σ` is the tail
+(`drop_flatten_append`). -/
 theorem idealView_simOut (sk : List Bool) (ρ : samp.Coins n)
     (s : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool))) (a : List Bool)
     (ha : a.length = r.eval n * S.ctLen.eval n + sl.eval n) :
@@ -471,13 +479,13 @@ theorem idealView_simOut (sk : List Bool) (ρ : samp.Coins n)
         (simAbs S samp pl hl hist r sl n ρ s).2 =
       realView S samp pl n (r.eval n) sk ρ a s := by
   set st := List.ofFn (simAbs S samp pl hl hist r sl n ρ s).1 with hst
-  have hc : ∀ i < r.eval n, (chunkAt (S.ctLen.eval n) i a).length = S.ctLen.eval n := fun i hi =>
-    length_chunkAt _ _ _ (by
+  have hc : ∀ i < r.eval n, (coinBlock (S.ctLen.eval n) i a).length = S.ctLen.eval n := fun i hi =>
+    length_coinBlock (by
       rw [ha]
       have := Nat.mul_le_mul_right (S.ctLen.eval n) (show i + 1 ≤ r.eval n from hi)
       omega)
   have hg : ∀ i < r.eval n, (flagF S (pairEncode (List.replicate n true) st)
-      (chunkAt (S.ctLen.eval n) i a)).length = S.ctLen.eval n + 1 := fun i hi => by
+      (coinBlock (S.ctLen.eval n) i a)).length = S.ctLen.eval n + 1 := fun i hi => by
     rw [length_flagF, hc i hi]
   have hlen : (simOutL S r n st a).length =
       (chalHandler (simParams S samp pl hl r sl)).outLen.eval n := by
@@ -489,7 +497,7 @@ theorem idealView_simOut (sk : List Bool) (ρ : samp.Coins n)
   congr 3
   refine List.map_congr_left fun i hi => ?_
   rw [List.mem_range] at hi
-  rw [chunkAt_flatten_append _ _ _ hg _ _ hi, flagF_eq, List.headD_cons, List.tail_cons,
+  rw [coinBlock_flatten_append _ _ _ hg _ _ hi, flagF_eq, List.headD_cons, List.tail_cons,
     pairSndD_pairEncode, pairFstD_pairEncode, List.length_replicate]
   congr 1
   cases s with
@@ -518,7 +526,7 @@ oracle (coins `ρ`) is the law of `F(realView)` over `A`'s run (coins `rA`) agai
 `rImpl … true … ρ ρ̃ (some re)`.
 
 **Proof sketch.** Transport the output length (`expect_toCompOn_outLen`); the run at budget `1` is
-the run at T2's budget (`toCompOn_budget_eq`: the handler asks at most one query,
+the run at T2's budget (`NUPPT.toCompOn_budget_eq`: the handler asks at most one query,
 `chalHandler_costBoundedBy`, and its finalization none, `simFinish`); T2's equation; the
 composition of the two simulations (`simulate_bind`, `simulate_comp`) is the hybrid's run through
 the abstraction (`simulate_eq_of_abs`, `simComp_abs`); the views agree (`idealView_simOut`). -/
@@ -566,7 +574,7 @@ theorem simRun_eq (Sim₀ : NUPPT) (n : ℕ)
       (chalHandler (simParams S samp pl hl r sl)).finCall.eval n := by
     rw [chalHandler_finCall, simParams_finCall, PolyExpr.eval_const]
     omega
-  rw [toCompOn_budget_eq Sim₀ _ n 1 _ z (φ (ω, rA)) hK (by
+  rw [NUPPT.toCompOn_budget_eq Sim₀ _ n 1 _ z (φ (ω, rA)) hK (by
     rw [← hφ z ω rA, chalHandler_init]
     refine OracleComp.CostBoundedBy.bind (q₁ := 1) (q₂ := 0) (chalHandler_costBoundedBy _ n z ω _)
       fun res => ?_
@@ -593,7 +601,7 @@ ideal acceptance rate (budget `1`) is, for every distinguisher and every `n`, th
 (under CPA).
 
 **Proof sketch.** `Sim₀` is T2's machine of the simulator's handler and `Sim` hard-wires
-`M.advice n` as the second input component (`exists_withAdviceOn`). Reindex `Sim`'s coins as
+`M.advice n` as the second input component (`NUPPT.exists_withAdviceOn`). Reindex `Sim`'s coins as
 `(ρ̃ ‖ re, rA)` (`coinsCongr`, `φ`, `seedEquiv`, `expect_sample_prod`), draw the hybrid's encryption
 coins in advance (`expect_simulate_rImpl_eager`) and reorder the samples (`expect_sample_comm`);
 pointwise this is `simRun_eq`. -/
@@ -603,7 +611,7 @@ theorem exists_simulator : ∃ Sim : NUPPT, ∀ (X : NUPPT) (n : ℕ),
   obtain ⟨Sim₀, hT2⟩ := exists_interactiveHandlerMachine A q (snmDin S pl) (snmDout S hl)
     (fun _ : Fin 1 => pl) (fun _ => hl) ((r.mul S.ctLen).add sl)
     (chalHandler (simParams S samp pl hl r sl))
-  obtain ⟨Sim, hc, hSim⟩ := NMCCA2.exists_withAdviceOn Sim₀ samp.advice samp.adv
+  obtain ⟨Sim, hc, hSim⟩ := NUPPT.exists_withAdviceOn Sim₀ samp.advice samp.adv
     samp.advice_length
   refine ⟨Sim, fun X n => ?_⟩
   obtain ⟨φ, hφ⟩ := hT2 n
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity.lean b/TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity.lean
index ad93fad9b..ca469fb1a 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity.lean
@@ -56,6 +56,9 @@ Security is stated for each admissible `L`; a larger `L` admits longer `Dec` que
 * `PublicKeyScheme.exists_padBound`, `BitPublicKeyScheme.exists_padBound`: padding bounds exist.
 * `FixedLengthPKScheme.indCodec_eq_bitCodec`: the adversary codec is a bit codec;
   `PublicKeyScheme.padded_enc_runAt`, `padded_enc_coins`: the padded encryptor.
+* `FixedLengthPKScheme.ctLen_pos`: nonempty messages force nonempty ciphertexts;
+  `FixedLengthPKScheme.indImpl_eq_of_msgLen_eq_zero`: with empty messages the two oracles of the
+  IND game coincide.
 
 The claim after Definition 171.5, `BitPublicKeyScheme.SingleBitSecure.padded_cpa` (single-bit
 security gives CPA security), and its eager-coins lemma `expect_simulate_indImpl_cpa` are in
@@ -718,6 +721,45 @@ theorem INDSecure_iff (atk : Attack) :
       ∀ n, advantage (S.indGame atk A (q.eval n) false n)
         (S.indGame atk A (q.eval n) true n) ≤ ε n := Iff.rfl
 
+/-! ### Nonempty ciphertexts, empty messages -/
+
+/-- **The ciphertexts are not empty** when the messages are not: with `msgLen(n) > 0`, correctness
+gives `ctLen(n) > 0` (two different messages cannot both decrypt from the empty ciphertext). -/
+theorem ctLen_pos (n : ℕ) (rg : S.gen.Coins n) (re : S.enc.Coins n) (hL : 0 < S.msgLen.eval n) :
+    0 < S.ctLen.eval n := by
+  by_contra h
+  have h0 : S.ctLen.eval n = 0 := by omega
+  have hnil : ∀ m : Fin (S.msgLen.eval n) → Bool,
+      S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) (List.ofFn m)) re = [] := fun m =>
+    List.eq_nil_of_length_eq_zero ((S.enc_length n rg m re).trans h0)
+  have h₁ := S.correct n (fun _ => true) rg re
+  have h₂ := S.correct n (fun _ => false) rg re
+  rw [hnil] at h₁ h₂
+  have := congrFun (Option.some.inj (h₁.symm.trans h₂)) ⟨0, hL⟩
+  exact absurd this (by decide)
+
+/-- **With empty messages the two CCA2 oracles coincide:** if `msgLen(n) = 0`, then
+`S.indImpl atk false n pk sk = S.indImpl atk true n pk sk` (both halves of a challenge are the
+empty message).
+
+**Proof sketch.** Compare query by query through the published equations: decryption does not
+depend on the bit (`indImpl_dec_onSpec`), a repeated challenge repeats the record
+(`indImpl_challenge_repeat_onSpec`), and a first challenge encrypts a half of the query
+(`indImpl_challenge_none_onSpec`), whose string is `[]` either way. -/
+theorem indImpl_eq_of_msgLen_eq_zero (atk : Attack) (n : ℕ) (pk sk : List Bool)
+    (h : S.msgLen.eval n = 0) : S.indImpl atk false n pk sk = S.indImpl atk true n pk sk := by
+  have h0 : ∀ f : Fin (S.msgLen.eval n) → Bool, List.ofFn f = [] := fun f =>
+    List.eq_nil_of_length_eq_zero (by rw [List.length_ofFn, h])
+  funext i x s
+  match i with
+  | 0 => rw [S.indImpl_dec_onSpec, S.indImpl_dec_onSpec]
+  | 1 =>
+    cases s with
+    | some c => rw [S.indImpl_challenge_repeat_onSpec, S.indImpl_challenge_repeat_onSpec]
+    | none =>
+      rw [S.indImpl_challenge_none_onSpec, S.indImpl_challenge_none_onSpec]
+      simp only [h0]
+
 end FixedLengthPKScheme
 
 end TCSlib.Cryptography.Composability
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity/ChallengeSim.lean b/TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity/ChallengeSim.lean
index cefc63457..eb14428a6 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity/ChallengeSim.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity/ChallengeSim.lean
@@ -5,6 +5,7 @@ Released under Apache 2.0 license as described in the file LICENSE.
 import TCSlib.Cryptography.Games.BitCodec
 import TCSlib.Cryptography.Games.Machines
 import TCSlib.Cryptography.Games.Probability
+import TCSlib.Cryptography.Games.Hopping
 import TCSlib.Cryptography.Games.Bridges.Experiments
 
 set_option maxHeartbeats 0
@@ -138,11 +139,12 @@ sampling `re` and answering (and recording) `padFin d (g mm re)`; the state hold
 strings, `d = outs 1`, read through the cast `e`. Then for every `G`,
 `𝔼[G ∘ fst] (simulate impl c s) = 𝔼_{re} G (chRun (fun mm => g mm re) c (s.map (cast e))).1`.
 
-**Proof sketch.** Substitute `d = outs 1`, so that the casts are identities. Induction on the
-computation: decryption queries and repeated challenges are deterministic in both; at the first
-challenge the lazy side samples `re` and continues from the recorded answer, by the induction
-hypothesis an average over coins `re'` on which the recorded run does not depend
-(`chRun_some_congr`), so `re'` marginalizes out (`expect_const`). -/
+**Proof sketch.** Substitute `d = outs 1`, so that the casts are identities. With the coins `re`
+fixed, `impl` becomes the deterministic oracle `OE re`, whose simulation is the run
+`chRun (fun mm => g mm re)` (induction on the computation). From the unchallenged state,
+`Games.expect_simulate_eager` (the coins are spent at the first challenge, after which the state
+is recorded) averages `OE re` over `re`. From a recorded state `impl` is already deterministic,
+so its simulation is the run for any `re`, which does not depend on `re` (`chRun_some_congr`). -/
 theorem expect_simulate_eager {ins outs : Fin 2 → ℕ} {d : ℕ} (hd : outs 1 = d)
     (e : (Fin d → Bool) = (Fin (outs 1) → Bool)) {R : Type} [Fintype R] [Nonempty R]
     (impl : QueryImpl (bitSpec ins outs) (Option (Fin d → Bool)) unifSpec)
@@ -161,32 +163,84 @@ theorem expect_simulate_eager {ins outs : Fin 2 → ℕ} {d : ℕ} (hd : outs 1
     cases s <;> simp
   simp only [hc] at hrep hnew
   simp only [hmap]
-  induction c generalizing s with
-  | pure a =>
-    rw [simulate_pure, expect_pure]
-    simp only [chRun_pure]
-    exact (expect_const _ _).symm
-  | query i x k ih =>
-    match i, x, k, ih with
-    | 0, x, k, ih =>
-      rw [simulate_query, h0, OracleComp.pure_bind]
-      simp only [chRun_query_zero]
-      exact ih _ s
-    | 1, x, k, ih =>
-      cases s with
-      | some C =>
-        rw [simulate_query, hrep, OracleComp.pure_bind]
-        simp only [chRun_query_one_some]
+  -- The oracle with the coins `re` fixed in advance.
+  let OE : R → QueryImpl (bitSpec ins outs) (Option (Fin (outs 1) → Bool)) unifSpec :=
+    fun re i x s => match i, x, s with
+      | 0, _, s => .pure (zeroBits _, s)
+      | 1, mm, none => .pure (padFin _ (g mm re), some (padFin _ (g mm re)))
+      | 1, _, some c => .pure (c, some c)
+  -- Its simulation is the run with the answer `g · re`.
+  have hdet : ∀ (re : R) (c : OracleComp (bitSpec ins outs) α) (s : Option (Fin (outs 1) → Bool)),
+      simulate (OE re) c s = .pure (chRun (fun mm => g mm re) c s) := by
+    intro re c
+    induction c with
+    | pure a => exact fun s => by rw [simulate_pure, chRun_pure]
+    | query i x k ih =>
+      intro s
+      match i, x, k, ih, s with
+      | 0, x, k, ih, s =>
+        rw [simulate_query, chRun_query_zero]
+        show (OracleComp.pure (zeroBits _, s)).bind (fun p => simulate (OE re) (k p.1) p.2) = _
+        rw [OracleComp.pure_bind]
+        exact ih _ s
+      | 1, x, k, ih, none =>
+        rw [simulate_query, chRun_query_one_none]
+        show (OracleComp.pure (padFin _ (g x re), some (padFin _ (g x re)))).bind
+          (fun p => simulate (OE re) (k p.1) p.2) = _
+        rw [OracleComp.pure_bind]
+        exact ih _ _
+      | 1, x, k, ih, some C =>
+        rw [simulate_query, chRun_query_one_some]
+        show (OracleComp.pure (C, some C)).bind (fun p => simulate (OE re) (k p.1) p.2) = _
+        rw [OracleComp.pure_bind]
         exact ih _ _
-      | none =>
-        rw [simulate_query, hnew, OracleComp.bind_assoc, expect_bind]
-        refine congrArg _ (funext fun re => ?_)
-        rw [OracleComp.pure_bind, ih, chRun_query_one_none]
-        dsimp only
-        exact (congrArg _ (funext fun re' =>
-          congrArg (fun p : α × Option (Fin (outs 1) → Bool) => G p.1)
-            (chRun_some_congr (fun mm => g mm re') (fun mm => g mm re) _ _))).trans
-          (expect_const _ _)
+  -- From a recorded state, `impl` is the oracle with any coins fixed.
+  have hsome : ∀ (re : R) (c : OracleComp (bitSpec ins outs) α) (C : Fin (outs 1) → Bool),
+      simulate impl c (some C) = simulate (OE re) c (some C) := by
+    intro re c
+    induction c with
+    | pure a => exact fun C => by rw [simulate_pure, simulate_pure]
+    | query i x k ih =>
+      intro C
+      match i, x, k, ih with
+      | 0, x, k, ih =>
+        rw [simulate_query, simulate_query, h0, OracleComp.pure_bind]
+        show _ = (OracleComp.pure (zeroBits _, some C)).bind
+          (fun p => simulate (OE re) (k p.1) p.2)
+        rw [OracleComp.pure_bind]
+        exact ih _ C
+      | 1, x, k, ih =>
+        rw [simulate_query, simulate_query, hrep, OracleComp.pure_bind]
+        show _ = (OracleComp.pure (C, some C)).bind (fun p => simulate (OE re) (k p.1) p.2)
+        rw [OracleComp.pure_bind]
+        exact ih _ C
+  cases s with
+  | none =>
+    rw [Games.expect_simulate_eager impl OE (fun s => s.isSome = true)
+      (fun re i x s hs => ?_) (fun i x s hs => ?_) (fun i x s hs => ?_) c (fun p => G p.1)
+      (by simp)]
+    · refine congrArg _ (funext fun re => ?_)
+      rw [hdet, expect_pure]
+    · obtain ⟨C, rfl⟩ := Option.isSome_iff_exists.1 hs
+      match i, x with
+      | 0, x => exact (h0 x _).symm
+      | 1, x => exact (hrep x C).symm
+    · obtain ⟨C, rfl⟩ := Option.isSome_iff_exists.1 hs
+      match i, x with
+      | 0, x => rw [h0]; exact OracleComp.allOutputs_pure.2 rfl
+      | 1, x => rw [hrep]; exact OracleComp.allOutputs_pure.2 rfl
+    · obtain rfl : s = none := by simpa using hs
+      match i, x with
+      | 0, x =>
+        exact .inl fun re => ⟨(h0 x none).symm, by
+          rw [h0]
+          exact OracleComp.allOutputs_pure.2 (by simp)⟩
+      | 1, x => exact .inr ⟨hnew x, fun re => OracleComp.allOutputs_pure.2 rfl⟩
+  | some C =>
+    rw [hsome (Classical.arbitrary R), hdet, expect_pure]
+    refine (Eq.trans ?_ (expect_const (ProbComp.sample R) _)).symm
+    refine congrArg _ (funext fun re => ?_)
+    rw [chRun_some_congr (fun mm => g mm re) (fun mm => g mm (Classical.arbitrary R))]
 
 /-- **First-challenge congruence:** if `g` and `g'` agree at the first challenge query of `c`
 (vacuous when there is none), the runs from the unchallenged state agree:
diff --git a/TCSlib/Cryptography/Foundations/BitLists.lean b/TCSlib/Cryptography/Foundations/BitLists.lean
index 54e270a2e..a8d70ef50 100644
--- a/TCSlib/Cryptography/Foundations/BitLists.lean
+++ b/TCSlib/Cryptography/Foundations/BitLists.lean
@@ -5,6 +5,7 @@ Released under Apache 2.0 license as described in the file LICENSE.
 import Mathlib.Data.List.OfFn
 import Mathlib.Data.List.GetD
 import Mathlib.Logic.Equiv.Prod
+import Mathlib.Data.Fintype.Basic
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
@@ -31,6 +32,11 @@ an association list. They depend on Mathlib only.
 * `TCSlib.Cryptography.xorPerm_apply`: `xorPerm v y = y ⊕ v`.
 * `TCSlib.Cryptography.mem_keys_of_lookup_isSome`: a key with a value in an association list is
   one of its keys.
+* `TCSlib.Cryptography.ofFn_eq_map_range`, `ofFn_natAdd_eq_drop`, `decide_map_ofFn`: lists of
+  tuples as maps over ranges, tails of tuples, comparing optional tuples through their lists.
+* `TCSlib.Cryptography.length_flatten_map_const`, `length_flatten_map_range`: the length of a
+  concatenation of equal-length blocks.
+* `TCSlib.Cryptography.flatMap_range_drop`: reading the successive suffixes of a list.
 
 ## References
 
@@ -102,4 +108,72 @@ theorem mem_keys_of_lookup_isSome {α β : Type} [DecidableEq α] (T : List (α
   obtain ⟨p, hp, hx⟩ := List.lookup_isSome_iff.1 h
   exact List.mem_map.2 ⟨p, hp, (beq_iff_eq.1 hx).symm⟩
 
+/-! ### Lists indexed by ranges, tails and blocks of lists -/
+
+/-- A list of `r` values is a map over `List.range r`: if `f i = g i` for every `i : Fin r`, then
+`List.ofFn f = (List.range r).map g` (both have `r` entries, entry `i` is `f i = g i`). -/
+theorem ofFn_eq_map_range {α : Type*} {r : ℕ} (f : Fin r → α) (g : ℕ → α)
+    (h : ∀ i : Fin r, f i = g i) : List.ofFn f = (List.range r).map g := by
+  refine List.ext_getElem (by rw [List.length_ofFn, List.length_map, List.length_range])
+    fun i h₁ h₂ => ?_
+  rw [List.getElem_ofFn, List.getElem_map, List.getElem_range]
+  exact h _
+
+/-- **The tail of a string:** `⟦j ↦ w (natAdd k j)⟧ = ⟦w⟧.drop k` (`List.ofFn_add`). -/
+theorem ofFn_natAdd_eq_drop {k sl : ℕ} (w : Fin (k + sl) → Bool) :
+    List.ofFn (fun j : Fin sl => w (Fin.natAdd k j)) = (List.ofFn w).drop k := by
+  rw [List.ofFn_add, List.drop_left' List.length_ofFn]
+
+/-- Comparing strings is comparing their lists:
+`decide (o.map ofFn = some ⟦c⟧) = decide (o = some c)` (`List.ofFn_inj`). -/
+theorem decide_map_ofFn {k : ℕ} (o : Option (Fin k → Bool)) (c : Fin k → Bool) :
+    decide (o.map List.ofFn = some (List.ofFn c)) = decide (o = some c) := by
+  cases o with
+  | none => simp
+  | some c' => simp [List.ofFn_inj]
+
+/-- Blocks of `k` entries, one per element: `|(l.map g).flatten| = |l|·k` when every `g x` has
+`k` entries (`List.length_flatten`, a sum of the constant `k`). -/
+theorem length_flatten_map_const {α β : Type*} (l : List α) (g : α → List β) (k : ℕ)
+    (hg : ∀ x, (g x).length = k) : (l.map g).flatten.length = l.length * k := by
+  rw [List.length_flatten, List.map_map, show (List.length ∘ g) = fun _ => k from funext hg,
+    List.map_const', List.sum_replicate_nat]
+
+/-- `r` blocks of `k` entries have `r·k` entries: `|((range r).map g).flatten| = r·k` when
+`g 0, …, g (r-1)` have `k` entries each (`List.length_flatten`, a sum of the constant `k`). -/
+theorem length_flatten_map_range {β : Type*} (k r : ℕ) (g : ℕ → List β)
+    (hg : ∀ i < r, (g i).length = k) : ((List.range r).map g).flatten.length = r * k := by
+  rw [List.length_flatten, List.map_map,
+    List.map_congr_left (f := List.length ∘ g) (g := fun _ => k)
+      fun i hi => hg i (List.mem_range.1 hi),
+    List.map_const', List.sum_replicate_nat, List.length_range]
+
+/-- **Reading the suffixes of a list within at least its length many steps:** if `F [] = []`
+and `F` reads only the first element of a nonempty suffix, `F (e :: t) = g e` for the members `e`
+of `l`, then `(List.range m).flatMap (fun i => F (l.drop i)) = l.flatMap g` for every
+`m ≥ |l|`.
+
+**Proof sketch.** Induction on `l`: the first suffix is `l` itself, read as `g e`; the others are
+the suffixes of the tail, within `m - 1` steps; the empty suffixes read `[]`. -/
+theorem flatMap_range_drop {β γ : Type*} (F : List β → List γ) (g : β → List γ)
+    (hnil : F [] = []) :
+    ∀ (l : List β), (∀ e ∈ l, ∀ t, F (e :: t) = g e) → ∀ m : ℕ, l.length ≤ m →
+      ((List.range m).flatMap fun i => F (l.drop i)) = l.flatMap g := by
+  intro l
+  induction l with
+  | nil =>
+    intro _ m _
+    rw [List.flatMap_nil]
+    refine List.flatMap_eq_nil_iff.2 fun i _ => ?_
+    rw [List.drop_nil, hnil]
+  | cons e t ih =>
+    intro hcons m hm
+    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by rw [List.length_cons] at hm; omega⟩
+    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, List.drop_zero,
+      hcons e List.mem_cons_self, List.flatMap_cons]
+    congr 1
+    simp only [List.drop_succ_cons]
+    exact ih (fun e' he' => hcons e' (List.mem_cons_of_mem _ he')) m'
+      (by rw [List.length_cons] at hm; omega)
+
 end TCSlib.Cryptography
diff --git a/TCSlib/Cryptography/Games.lean b/TCSlib/Cryptography/Games.lean
index bed038ad7..fb3115e91 100644
--- a/TCSlib/Cryptography/Games.lean
+++ b/TCSlib/Cryptography/Games.lean
@@ -8,6 +8,7 @@ import TCSlib.Cryptography.Games.Simulate
 import TCSlib.Cryptography.Games.Advantage
 import TCSlib.Cryptography.Games.Hopping
 import TCSlib.Cryptography.Games.Protocols
+import TCSlib.Cryptography.Games.Forwarding
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
@@ -42,6 +43,8 @@ the interaction model `Strategy`.
 * `TCSlib.Cryptography.Games.Protocols`: parties, the message exchange, executions in a
   coroutine model that contains D8's (bridge B4), and traced executions recording received
   messages and coin draws.
+* `TCSlib.Cryptography.Games.Forwarding`: the forwarding handler, the call lemmas of interactive
+  handlers read on lists, and hard-wiring a second input component (S2b layer).
 
 ## References
 
diff --git a/TCSlib/Cryptography/Games/BitCodec.lean b/TCSlib/Cryptography/Games/BitCodec.lean
index 3fa41a97b..ab6e953a4 100644
--- a/TCSlib/Cryptography/Games/BitCodec.lean
+++ b/TCSlib/Cryptography/Games/BitCodec.lean
@@ -5,6 +5,8 @@ Released under Apache 2.0 license as described in the file LICENSE.
 import TCSlib.Cryptography.Games.Machines
 import TCSlib.Cryptography.Asymptotic.Adversary
 import TCSlib.Cryptography.Games.Probability
+import TCSlib.Complexity.ClassNP.PolyTimeBlockLoop
+import Mathlib.Data.List.GetD
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
@@ -36,6 +38,8 @@ It is the shared codec of every prong's statements, and the T0 definitions of th
 * `Games.encodeBitMove`: the canonical word of a move.
 * `Games.bitCodec din dout dα`: the codec.
 * `Games.castImpl`: an implementation of bit-string oracles read along equal length functions.
+* `Games.cntRead`, `Games.ansRead`: the per-entry readings of an encoded log (one token for a
+  nonempty log; the answer of the first entry).
 
 ## Main results
 
@@ -46,8 +50,11 @@ It is the shared codec of every prong's statements, and the T0 definitions of th
 * `Games.decodeBitMove_of_not_canonical`: every other word decodes to the all-`false` output.
 * `Games.padFin_ofFn_zeroBits`, `Games.padFin_replicate_false`, `Games.padFin_nil`,
   `Games.decodeFin_nil_getD`: all-`false` strings and the empty answer read as `zeroBits`.
+* `Games.padFin_append_split`: the two parts of a padded concatenation.
 * `Games.simulate_castImpl_toCompOn`, `Games.expect_simulate_castImpl_toCompOn`: transport of a
   machine's run between two codecs with equal lengths.
+* `Games.polyTimeComputable_cntRead`, `Games.polyTimeComputable_ansRead`: the per-entry readings
+  are polynomial-time.
 
 ## References
 
@@ -143,6 +150,18 @@ theorem padFin_replicate_false (d m : ℕ) : padFin d (List.replicate m false) =
 /-- The empty list reads as the all-`false` vector: `padFin d [] = zeroBits d`. -/
 theorem padFin_nil (d : ℕ) : padFin d [] = zeroBits d := padFin_replicate_false d 0
 
+/-- **The two parts of a padded concatenation:** if `|u| = d₁`, the first `d₁` bits of
+`padFin (d₁ + d₂) (u ++ v)` are `padFin d₁ u` and the rest `padFin d₂ v` (`padFin_apply`,
+`List.getD_append`, `List.getD_append_right`). -/
+theorem padFin_append_split {d₁ d₂ : ℕ} (u v : List Bool) (hu : u.length = d₁) :
+    (fun j : Fin d₁ => padFin (d₁ + d₂) (u ++ v) (Fin.castAdd d₂ j)) = padFin d₁ u ∧
+      (fun j : Fin d₂ => padFin (d₁ + d₂) (u ++ v) (Fin.natAdd d₁ j)) = padFin d₂ v := by
+  refine ⟨funext fun j => ?_, funext fun j => ?_⟩
+  · rw [padFin_apply, padFin_apply, Fin.coe_castAdd, List.getD_append _ _ _ _ (by omega)]
+  · rw [padFin_apply, padFin_apply, Fin.coe_natAdd, List.getD_append_right _ _ _ _ (by omega)]
+    congr 1
+    omega
+
 /-- An empty answer decodes to all-`false` at every length:
 `(decodeFin ℓ []).getD (zeroBits ℓ) = zeroBits ℓ`. -/
 theorem decodeFin_nil_getD (ℓ : ℕ) : (decodeFin ℓ []).getD (zeroBits ℓ) = zeroBits ℓ := by
@@ -327,6 +346,32 @@ theorem encodeBitMove_injective (din dout : Fin k → ℕ) (dα : ℕ) :
     Function.Injective (encodeBitMove din dout dα) := fun m m' h => by
   rw [← decodeBitMove_encodeBitMove din dout dα m, h, decodeBitMove_encodeBitMove]
 
+/-! ### Readings of a log entry -/
+
+/-- One token for a nonempty log and nothing for the empty one:
+`cntRead v = if v = [] then [] else [true]`. Applied to the successive suffixes of an encoded log,
+it counts the entries. -/
+def cntRead (v : List Bool) : List Bool := if decide (v = []) then [] else [true]
+
+/-- `cntRead v = if v = [] then [] else [true]`. -/
+theorem cntRead_eq (v : List Bool) : cntRead v = if decide (v = []) then [] else [true] := rfl
+
+/-- The token reading is polynomial-time: `PolyTimeComputable cntRead`. -/
+theorem polyTimeComputable_cntRead : PolyTimeComputable cntRead :=
+  polyTimeComputable_ite polyTimeComputable_isNil (polyTimeComputable_const [])
+    (polyTimeComputable_const [true])
+
+/-- The answer `y` of the first entry `⟨1^i, ⟨x, y⟩⟩` of an encoded log:
+`ansRead v = pairSndD (pairSndD (pairFstD v))`. -/
+def ansRead (v : List Bool) : List Bool := pairSndD (pairSndD (pairFstD v))
+
+/-- `ansRead v = pairSndD (pairSndD (pairFstD v))`. -/
+theorem ansRead_eq (v : List Bool) : ansRead v = pairSndD (pairSndD (pairFstD v)) := rfl
+
+/-- The answer reading is polynomial-time: `PolyTimeComputable ansRead`. -/
+theorem polyTimeComputable_ansRead : PolyTimeComputable ansRead :=
+  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD)
+
 /-! ### Transport along equal lengths -/
 
 section Transport
diff --git a/TCSlib/Cryptography/Games/Efficiency.lean b/TCSlib/Cryptography/Games/Efficiency.lean
index c17489bb6..ab33eae60 100644
--- a/TCSlib/Cryptography/Games/Efficiency.lean
+++ b/TCSlib/Cryptography/Games/Efficiency.lean
@@ -91,8 +91,10 @@ handler, the reduction's output. This bounds every history, which the guarded st
   times per inner query, and its semantics as a `QueryImpl` of the inner oracles by the outer ones;
   `InteractiveHandler.advInput` and `InteractiveHandler.finish`: the adversary's input and the
   finalization, with up to `finCall(n)` outer queries.
-* `Games.InteractiveHandler.rU`, `rZ`, `rW`, `rS`, `rI`, `rX`, `rL`, `rCnt`: the fields of a
-  round input `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩` (and the first component of the state).
+* `Games.InteractiveHandler.rU`, `rZ`, `rW`, `rS`, `rI`, `rX`, `rL`, `rCnt`, `rAns`: the fields of
+  a round input `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩` (and the first component of the state, and
+  the answer of the first entry of the outer log); `Games.InteractiveHandler.finA`: the adversary's
+  output in a finalization input `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩`.
 
 ## Main results
 
@@ -103,11 +105,15 @@ handler, the reduction's output. This bounds every history, which the guarded st
   `q(n) · perCall(n) + finCall(n)`, whose computation is exactly the simulation followed by the
   finalization. The reductions that forward or answer queries with their own oracle need it (the
   PRF MAC's distinguisher, hash-and-sign's forger, the CPA and CCA reductions).
-* `Games.InteractiveHandler.rU_input`, …, `rCnt_input`: the readers of a round input on
-  `InteractiveHandler.input`; `Games.InteractiveHandler.impl_of_ret`: a call whose first round
-  returns.
+* `Games.InteractiveHandler.rU_input`, …, `rCnt_input`, `rAns_input`: the readers of a round
+  input on `InteractiveHandler.input`; `rU_finInput`, `rZ_finInput`, `rW_finInput`, `rS_finInput`,
+  `rL_finInput`, `finA_finInput`: the readers of a finalization input on `finInput`;
+  `Games.InteractiveHandler.impl_of_ret`, `Games.InteractiveHandler.impl_of_query`: a call whose
+  first round returns, or asks one outer query and returns in its second round;
+  `Games.InteractiveHandler.finish_of_ret`: a finalization whose first round returns.
 * `Games.exists_toCompOn_of_toComp` (the fill's target): a machine without input is a machine
   with an input that it ignores, with the same coins.
+* `Games.expect_toCompOn_outLen`: a machine's output length may be changed along an equality.
 * `Games.exists_toOracleAdversary_of_bitCodec` (T4, the fill's target): an oracle machine
   against one `bitCodec` oracle with a one-bit output, on the empty input, evaluates as a
   next-query machine of the ch. 2–4 layer.
@@ -452,7 +458,8 @@ theorem input_eq (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
 The fields of a round input `w = ⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`, read with `pairFstD` and
 `pairSndD`, as a handler's round function reads them; on `input n z ω s i x L` they return the
 field (`rU_input`, …), and each is polynomial-time (`polyTimeComputable_rU`, …). `rCnt` reads the
-first component of the state, the call count `1^j` of the handlers that keep one there. -/
+first component of the state, the call count `1^j` of the handlers that keep one there; `rAns`
+reads the answer of the first entry of the outer log. -/
 
 /-- The parameter `1^n` of a round input: `rU w = pairFstD (pairFstD w)`. -/
 def rU (w : List Bool) : List Bool := pairFstD (pairFstD w)
@@ -472,6 +479,12 @@ def rL (w : List Bool) : List Bool := pairSndD (pairSndD (pairSndD w))
 /-- The first component `pairFstD s` of the state of a round input:
 `rCnt w = pairFstD (rS w)`. -/
 def rCnt (w : List Bool) : List Bool := pairFstD (rS w)
+/-- The outer answer `y` of the first entry `⟨1^j, ⟨x', y⟩⟩` of the outer log of a round input:
+`rAns w = pairSndD (pairSndD (pairFstD (rL w)))`. -/
+def rAns (w : List Bool) : List Bool := pairSndD (pairSndD (pairFstD (rL w)))
+
+/-- `rAns w = pairSndD (pairSndD (pairFstD (rL w)))`. -/
+theorem rAns_eq (w : List Bool) : rAns w = pairSndD (pairSndD (pairFstD (rL w))) := rfl
 
 /-- `rU (input n z ω s i x L) = 1^n`. -/
 theorem rU_input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
@@ -513,6 +526,14 @@ theorem rCnt_input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool)
     rCnt (input n z ω s i x L) = pairFstD s := by
   rw [rCnt, rS_input]
 
+/-- The answer of the first entry of the outer log:
+`rAns (input n z ω s i x ⟨⟨1^j, ⟨x', y⟩⟩, t⟩) = y`. -/
+theorem rAns_input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x : List Bool) (j : ℕ)
+    (x' y t : List Bool) :
+    rAns (input n z ω s i x
+      (pairEncode (pairEncode (List.replicate j true) (pairEncode x' y)) t)) = y := by
+  rw [rAns, rL_input, pairFstD_pairEncode, pairSndD_pairEncode, pairSndD_pairEncode]
+
 /-- `rU` is polynomial-time: `PolyTimeComputable rU`. -/
 theorem polyTimeComputable_rU : PolyTimeComputable rU :=
   polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD
@@ -547,6 +568,11 @@ theorem polyTimeComputable_rL : PolyTimeComputable rL :=
 theorem polyTimeComputable_rCnt : PolyTimeComputable rCnt :=
   polyTimeComputable_pairFstD.comp polyTimeComputable_rS
 
+/-- `rAns` is polynomial-time: `PolyTimeComputable rAns`. -/
+theorem polyTimeComputable_rAns : PolyTimeComputable rAns :=
+  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp
+    (polyTimeComputable_pairFstD.comp polyTimeComputable_rL))
+
 /-- The adversary's input at parameter `n`, for the reduction input `z` and the seed `ω`: `advIn`
 of the context `⟨1^n, ⟨z, ω⟩⟩`. -/
 def advInput (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
@@ -642,6 +668,49 @@ theorem impl_of_ret (H : InteractiveHandler k din dout k' din' dout') (n : ℕ)
       rw [MachineCodec.encodeLog_nil, h, ← List.ofFn_fin_append]
       exact decodeBitMove_ret _ _ _ _), OracleComp.pure_bind, hy, hs]
 
+/-- **A call with one outer query:** if the first round asks the outer query `x'` to oracle `j`,
+and the second round, with the answer `y` in the outer log, returns `⟦y' y⟧ ‖ ⟦s' y⟧`, then (with
+`perCall(n) ≥ 1`) `H.impl n z ω i x s = query j x' (fun y => pure (y' y, s' y))`.
+
+**Proof sketch.** Unfold the call (`impl_apply`, `call_eq`) at the budget `perCall = p + 1`. The
+first round decodes to the query (`decodeBitMove_query`), which `buildComp_succ_of_query` asks.
+After the answer `y` the log encodes as in `h₁` (`bitCodec_encodeEntry`), the second round decodes
+to the return of `y' y ‖ s' y` (`buildComp_of_ret`, `decodeBitMove_ret`), which `impl` splits back
+(`Fin.append_left`, `Fin.append_right`). -/
+theorem impl_of_query (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
+    (ω : Fin (H.seedLen.eval n) → Bool) {i : Fin k} (x : Fin ((din i).eval n) → Bool)
+    (s : Fin (H.stateLen.eval n) → Bool) (j : Fin k') (x' : Fin ((din' j).eval n) → Bool)
+    (y' : (Fin ((dout' j).eval n) → Bool) → Fin ((dout i).eval n) → Bool)
+    (s' : (Fin ((dout' j).eval n) → Bool) → Fin (H.stateLen.eval n) → Bool)
+    (hpc : 1 ≤ H.perCall.eval n)
+    (h₀ : H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x) []) =
+      pairEncode [false] (pairEncode (List.replicate j true) (List.ofFn x')))
+    (h₁ : ∀ y, H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x)
+      (pairEncode (pairEncode (List.replicate j true) (pairEncode (List.ofFn x') (List.ofFn y)))
+        [])) = pairEncode [true] (List.ofFn (y' y) ++ List.ofFn (s' y))) :
+    H.impl n z ω i x s = .query j x' fun y => .pure (y' y, s' y) := by
+  obtain ⟨p, hp⟩ : ∃ p, H.perCall.eval n = p + 1 := ⟨H.perCall.eval n - 1, by omega⟩
+  rw [impl_apply, call_eq, hp,
+    buildComp_succ_of_query (i := j) (x := x') (by
+      rw [MachineCodec.encodeLog_nil, h₀]
+      exact decodeBitMove_query (fun j => (din' j).eval n) (fun j => (dout' j).eval n) _ j x'),
+    OracleComp.query_bind]
+  congr 1
+  funext y
+  have hlog : (bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog
+      ([] ++ [⟨j, x', y⟩]) = pairEncode (pairEncode (List.replicate j true)
+        (pairEncode (List.ofFn x') (List.ofFn y))) [] := by
+    rw [List.nil_append, MachineCodec.encodeLog_cons, MachineCodec.encodeLog_nil,
+      bitCodec_encodeEntry]
+  rw [buildComp_of_ret (a := Fin.append (y' y) (s' y)) (by
+      rw [hlog, h₁, ← List.ofFn_fin_append]
+      exact decodeBitMove_ret _ _ _ _), OracleComp.pure_bind]
+  congr 2
+  · funext l
+    exact Fin.append_left (y' y) (s' y) l
+  · funext l
+    exact Fin.append_right (y' y) (s' y) l
+
 /-- The input string of one round of the finalization: `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩`, with the
 final state `s`, the adversary's output `a` and the outer log `L` of the finalization so far. -/
 def finInput (n : ℕ) (z ω s a L : List Bool) : List Bool :=
@@ -653,6 +722,45 @@ theorem finInput_eq (n : ℕ) (z ω s a L : List Bool) :
     finInput n z ω s a L = pairEncode (seedIn n z ω) (pairEncode s (pairEncode a L)) :=
   rfl
 
+/-! #### Readers of a finalization input
+
+A finalization input `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩` has the shape of a round input, so the
+round-input readers `rU`, `rZ`, `rW`, `rS` and `rL` read its parameter, reduction input, seed,
+state and outer log (`rU_finInput`, …); `finA` reads the adversary's output. -/
+
+/-- `rU (finInput n z ω s a L) = 1^n`. -/
+theorem rU_finInput (n : ℕ) (z ω s a L : List Bool) :
+    rU (finInput n z ω s a L) = List.replicate n true := by
+  simp only [rU, finInput_eq, seedIn_eq, pairFstD_pairEncode]
+
+/-- `rZ (finInput n z ω s a L) = z`. -/
+theorem rZ_finInput (n : ℕ) (z ω s a L : List Bool) : rZ (finInput n z ω s a L) = z := by
+  simp only [rZ, finInput_eq, seedIn_eq, pairFstD_pairEncode, pairSndD_pairEncode]
+
+/-- `rW (finInput n z ω s a L) = ω`. -/
+theorem rW_finInput (n : ℕ) (z ω s a L : List Bool) : rW (finInput n z ω s a L) = ω := by
+  simp only [rW, finInput_eq, seedIn_eq, pairFstD_pairEncode, pairSndD_pairEncode]
+
+/-- `rS (finInput n z ω s a L) = s`. -/
+theorem rS_finInput (n : ℕ) (z ω s a L : List Bool) : rS (finInput n z ω s a L) = s := by
+  simp only [rS, finInput_eq, pairFstD_pairEncode, pairSndD_pairEncode]
+
+/-- `rL (finInput n z ω s a L) = L`. -/
+theorem rL_finInput (n : ℕ) (z ω s a L : List Bool) : rL (finInput n z ω s a L) = L := by
+  simp only [rL, finInput_eq, pairSndD_pairEncode]
+
+/-- The adversary's output `a` of a finalization input `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩`:
+`finA w = pairFstD (pairSndD (pairSndD w))`. -/
+def finA (w : List Bool) : List Bool := pairFstD (pairSndD (pairSndD w))
+
+/-- `finA (finInput n z ω s a L) = a`. -/
+theorem finA_finInput (n : ℕ) (z ω s a L : List Bool) : finA (finInput n z ω s a L) = a := by
+  simp only [finA, finInput_eq, pairFstD_pairEncode, pairSndD_pairEncode]
+
+/-- `finA` is polynomial-time: `PolyTimeComputable finA`. -/
+theorem polyTimeComputable_finA : PolyTimeComputable finA :=
+  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
+
 /-- **The finalization** in the final state `s`, after the adversary's output `a`: the
 reduction's `outLen(n)`-bit output, computed with at most `finCall(n)` outer queries, in at most
 `finCall(n) + 1` rounds of `finRun`. A malformed round output is the all-`false` output
@@ -682,6 +790,20 @@ theorem finish_eq (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z
         (zeroBits _) (H.finCall.eval n) [] :=
   rfl
 
+/-- **A finalization whose first round returns `b`** outputs `b`, asking nothing: if
+`H.finRun (finInput n z ⟦ω⟧ ⟦s⟧ ⟦a⟧ []) = ⟨[true], ⟦b⟧⟩`, then `H.finish n z ω s a = pure b`
+(`finish_eq`, `decodeBitMove_ret`, `buildComp_of_ret`). -/
+theorem finish_of_ret (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
+    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) {d : ℕ}
+    (a : Fin d → Bool) (b : Fin (H.outLen.eval n) → Bool)
+    (h : H.finRun (finInput n z (List.ofFn ω) (List.ofFn s) (List.ofFn a) []) =
+      pairEncode [true] (List.ofFn b)) :
+    H.finish n z ω s a = .pure b := by
+  rw [finish_eq]
+  refine buildComp_of_ret ?_
+  rw [MachineCodec.encodeLog_nil, h]
+  exact decodeBitMove_ret _ _ _ _
+
 end InteractiveHandler
 
 /-- **T2 (the efficiency fill's target; interactive handlers).** For a machine adversary `A`
@@ -793,6 +915,19 @@ theorem exists_toCompOn_of_toComp (A : NUPPT) :
     rw [NUPPT.runAt_coinsCongr, hA', pairSndD_pairEncode, id_eq, ← NUPPT.runAt_eq]
   rw [NUPPT.toCompOn_eq, NUPPT.toComp_eq, hnext]
 
+/-- **Changing a machine's output length along `d = d'`** keeps the law of its output read as a
+list: `𝔼[G (⟦p.1⟧, p.2)]` over the runs through `bitCodec ins outs d` and `bitCodec ins outs d'`
+agree (substitute `d = d'`). -/
+theorem expect_toCompOn_outLen {ins outs : Fin k → ℕ} {σ : Type}
+    (O : QueryImpl (bitSpec ins outs) σ unifSpec) (A : NUPPT) (n q : ℕ) (x : List Bool)
+    (r : A.Coins n) (s : σ) {d d' : ℕ} (hd : d = d') (G : List Bool × σ → ℝ) :
+    ProbComp.expect (simulate O (A.toCompOn (bitCodec ins outs d) n q x r) s)
+        (fun p => G (List.ofFn p.1, p.2)) =
+      ProbComp.expect (simulate O (A.toCompOn (bitCodec ins outs d') n q x r) s)
+        (fun p => G (List.ofFn p.1, p.2)) := by
+  subst hd
+  rfl
+
 /-- **T4 (the efficiency fill's target; the bridge to pseudorandom functions).** An oracle
 machine `B` against one `bitCodec` oracle (`ℓ₁(n)`-bit queries, `ℓ₂(n)`-bit answers) with a
 one-bit output, run on the empty input, is a next-query machine of the ch. 2–4 layer: there is a
diff --git a/TCSlib/Cryptography/Games/Efficiency/OracleBridge.lean b/TCSlib/Cryptography/Games/Efficiency/OracleBridge.lean
index ddd335704..5b3d541fc 100644
--- a/TCSlib/Cryptography/Games/Efficiency/OracleBridge.lean
+++ b/TCSlib/Cryptography/Games/Efficiency/OracleBridge.lean
@@ -28,10 +28,16 @@ needs the parameter.
 
 ## Main definitions
 
+* `Games.iterEmit`: iterate and emit, the generic construction of `relabel`, `NMCCA2.logEmit`
+  and `NMSim.chunkMap`.
 * `EffFill.relabelEmit`, `EffFill.relabel`, `EffFill.bridgePre`, `EffFill.bridgePost`.
 
 ## Main results
 
+* `Games.polyTimeComputable_iterEmit`, `Games.iterEmit_encode`, `Games.length_iterate_le_add`:
+  iterate and emit is polynomial-time and reads a list encoding element by element.
+* `EffFill.relabelN_eq_iterEmit`, `EffFill.relabel_eq_iterEmit`: the history translator is an
+  instance.
 * `EffFill.bridgePre_encodeHist`: the history of a log translates to the log.
 * `EffFill.bridgePost_spec`: the translated move is the decoded move.
 * `EffFill.eval_buildTree_bridge`: the two computations evaluate alike against every oracle.
@@ -42,6 +48,85 @@ needs the parameter.
   Definition 96.1 (oracle indistinguishability against oracle machines).
 -/
 
+namespace TCSlib.Cryptography.Games
+
+open Complexity Turing
+
+/-! ### Iterate and emit
+
+`iterEmit step emit m x` runs `m` rounds of `step` from `x` and concatenates the emissions of the
+visited words. On the words `enc l` of a list encoding whose step drops the first element, it reads
+the elements one by one (`iterEmit_encode`); with polynomial-time `step` and `emit` and `|x| + 1`
+rounds, it is polynomial-time when `step` never lengthens a word beyond a constant
+(`polyTimeComputable_iterEmit`). The history translator below (`EffFill.relabel`), the log readings
+`NMCCA2.logEmit` and the chunk maps `NMSim.chunkMap` are instances. -/
+
+/-- **Iterate and emit:** the emissions of the first `m` iterates of `step` from `x`,
+concatenated: `iterEmit step emit m x = (List.range m).flatMap fun i => emit (step^[i] x)`. -/
+def iterEmit (step emit : List Bool → List Bool) (m : ℕ) (x : List Bool) : List Bool :=
+  (List.range m).flatMap fun i => emit (step^[i] x)
+
+/-- `iterEmit step emit m x = (List.range m).flatMap fun i => emit (step^[i] x)`. -/
+theorem iterEmit_eq (step emit : List Bool → List Bool) (m : ℕ) (x : List Bool) :
+    iterEmit step emit m x = (List.range m).flatMap fun i => emit (step^[i] x) :=
+  rfl
+
+/-- **The orbit stays short:** if one step never makes a word longer than `max |y| c`, the
+iterates of `x` have at most `|x| + c` bits: `|step^[i] x| ≤ |x| + c`. -/
+theorem length_iterate_le_add {step : List Bool → List Bool} (c : ℕ)
+    (h : ∀ y, (step y).length ≤ max y.length c) (x : List Bool) (i : ℕ) :
+    (step^[i] x).length ≤ x.length + c := by
+  suffices hmax : (step^[i] x).length ≤ max x.length c by omega
+  induction i with
+  | zero => exact le_max_left _ _
+  | succ i ih =>
+    rw [Function.iterate_succ_apply']
+    exact (h _).trans (max_le ih (le_max_right _ _))
+
+/-- **Iterate and emit is polynomial-time** for `|x| + 1` rounds, when `step` and `emit` are and
+one step never makes a word longer than `max |y| c`:
+`PolyTimeComputable fun x => iterEmit step emit (|x| + 1) x`.
+
+**Proof sketch.** `Complexity.polyTimeComputable_iterateEmit` with `|x|` rounds and the orbit
+bound `|x| + c` (`length_iterate_le_add`). -/
+theorem polyTimeComputable_iterEmit {step emit : List Bool → List Bool}
+    (hstep : PolyTimeComputable step) (hemit : PolyTimeComputable emit) (c : ℕ)
+    (h : ∀ y, (step y).length ≤ max y.length c) :
+    PolyTimeComputable fun x => iterEmit step emit (x.length + 1) x :=
+  (polyTimeComputable_iterateEmit hstep hemit .var (.add .var (.const c))
+    (fun x i _ => by
+      rw [PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_const]
+      exact length_iterate_le_add c h x i)).congr
+    fun x => by rw [PolyExpr.eval_var, iterEmit_eq]
+
+/-- **Iterate and emit reads a list encoding element by element.** Let `enc` encode lists of `β`
+so that `step` drops the first element of the encoded list of `l` (`step (enc (e :: t)) = enc t`
+for the elements `e` of `l`) and fixes `enc []`, and let `emit` read nothing from `enc []` and `g e`
+from `enc (e :: t)`. Then `m ≥ |l|` rounds from `enc l` emit `l.flatMap g`:
+`iterEmit step emit m (enc l) = l.flatMap g`.
+
+**Proof sketch.** The `i`-th iterate is `enc (l.drop i)` (induction on `i`); the readings of the
+successive suffixes are `TCSlib.Cryptography.flatMap_range_drop`. -/
+theorem iterEmit_encode {β : Type} (step emit : List Bool → List Bool) (enc : List β → List Bool)
+    (g : β → List Bool) (l : List β) (hstep_nil : step (enc []) = enc [])
+    (hstep : ∀ e ∈ l, ∀ t, step (enc (e :: t)) = enc t) (hnil : emit (enc []) = [])
+    (hcons : ∀ e ∈ l, ∀ t, emit (enc (e :: t)) = g e) (m : ℕ) (hm : l.length ≤ m) :
+    iterEmit step emit m (enc l) = l.flatMap g := by
+  have hit : ∀ i, step^[i] (enc l) = enc (l.drop i) := by
+    intro i
+    induction i with
+    | zero => rfl
+    | succ i ih =>
+      rw [Function.iterate_succ_apply', ih, ← List.tail_drop]
+      cases hd : l.drop i with
+      | nil => rw [List.tail_nil, hstep_nil]
+      | cons e t => rw [List.tail_cons, hstep e (List.mem_of_mem_drop (hd ▸ List.mem_cons_self))]
+  rw [iterEmit_eq]
+  simp only [hit]
+  exact flatMap_range_drop (fun l' => emit (enc l')) g hnil l hcons m hm
+
+end TCSlib.Cryptography.Games
+
 namespace TCSlib.Cryptography.Games.EffFill
 
 open Complexity Turing
@@ -67,12 +152,24 @@ theorem relabelN_eq (m : ℕ) (w : List Bool) :
     relabelN m w = (List.range m).flatMap fun i => relabelEmit (pairSndD^[i] w) :=
   rfl
 
+/-- `relabelN` is iterate-and-emit with the step `pairSndD`:
+`relabelN m w = iterEmit pairSndD relabelEmit m w`. -/
+theorem relabelN_eq_iterEmit (m : ℕ) (w : List Bool) :
+    relabelN m w = iterEmit pairSndD relabelEmit m w := by
+  rw [relabelN_eq, iterEmit_eq]
+
 /-- **The history translator's body:** the pieces of the first `|x| + 1` suffixes of `x`. -/
 def relabel (x : List Bool) : List Bool := relabelN (x.length + 1) x
 
 /-- `relabel x = relabelN (|x| + 1) x`. -/
 theorem relabel_eq (x : List Bool) : relabel x = relabelN (x.length + 1) x := rfl
 
+/-- `relabel` is iterate-and-emit for `|x| + 1` rounds:
+`relabel x = iterEmit pairSndD relabelEmit (|x| + 1) x`. -/
+theorem relabel_eq_iterEmit (x : List Bool) :
+    relabel x = iterEmit pairSndD relabelEmit (x.length + 1) x := by
+  rw [relabel_eq, relabelN_eq_iterEmit]
+
 /-- **The history translator:** `bridgePre x = ⟨[], relabel x⟩`. -/
 def bridgePre (x : List Bool) : List Bool := pairEncode [] (relabel x)
 
@@ -163,21 +260,13 @@ theorem relabelEmit_poly : PolyTimeComputable relabelEmit :=
     · rw [if_neg h, decide_eq_false h]
       rfl
 
-/-- **The history translator is polynomial-time** (`Complexity.polyTimeComputable_iterateEmit`
-with the step `pairSndD`, `|x| + 1` rounds and the orbit bound `|x|`). -/
+/-- **The history translator is polynomial-time** (`polyTimeComputable_iterEmit` with the step
+`pairSndD`, which never lengthens a word, through `relabel_eq_iterEmit`). -/
 theorem bridgePre_poly : PolyTimeComputable bridgePre := by
-  have horbit : ∀ (x : List Bool) (i : ℕ), i ≤ PolyExpr.var.eval x.length →
-      (pairSndD^[i] x).length ≤ PolyExpr.var.eval x.length := by
-    intro x i _
-    clear * -
-    rw [PolyExpr.eval_var]
-    induction i with
-    | zero => exact le_rfl
-    | succ i ih => rw [Function.iterate_succ_apply']; exact (length_pairSndD_le _).trans ih
-  have h := polyTimeComputable_iterateEmit polyTimeComputable_pairSndD relabelEmit_poly .var .var
-    horbit
+  have h := polyTimeComputable_iterEmit polyTimeComputable_pairSndD relabelEmit_poly 0
+    fun y => (length_pairSndD_le y).trans (le_max_left _ _)
   refine ((polyTimeComputable_const []).pairEncode h).congr fun x => ?_
-  rw [bridgePre_eq, relabel_eq, relabelN_eq, PolyExpr.eval_var]
+  rw [bridgePre_eq, relabel_eq_iterEmit]
 
 /-! ### The move translator -/
 
diff --git a/TCSlib/Cryptography/Games/Forwarding.lean b/TCSlib/Cryptography/Games/Forwarding.lean
new file mode 100644
index 000000000..46160bc7d
--- /dev/null
+++ b/TCSlib/Cryptography/Games/Forwarding.lean
@@ -0,0 +1,212 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Games.Efficiency
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Forwarding handlers, calls read on lists, and hard-wired input components
+
+Generic tools for the reductions built with T2 (`Games.exists_interactiveHandlerMachine`) that
+were first proved for [PS10, Theorems 174.8 and 175.9].
+
+* **Calls read on lists.** The call lemmas of `Games.InteractiveHandler` (`impl_of_ret`,
+  `impl_of_query`, `finish_of_ret`) take the answer and the state as fixed-length vectors. A round
+  function usually builds them as lists `u`, `v` of the right lengths; the `_padFin` forms take
+  those lists and return `padFin _ u`, `padFin _ v`.
+* **The forwarding handler** (`fwdHandler`): a reduction that runs its adversary once against its
+  own oracles forwards every query unchanged to the outer oracle of the same index, with one
+  outer call per inner query and an empty state; only the finalization differs. Its answers are
+  the outer oracle's (`fwdHandler_impl`). Its round reads the round input through the published
+  readers `InteractiveHandler.rS`, `rI`, `rX`, `rL` and `rAns`.
+* **Hard-wiring a second input component** (`NUPPT.exists_withAdviceOn`): a reduction that
+  receives advice as the second component of its input is a machine with that advice built in.
+
+## Main definitions
+
+* `Games.fwdHandler`: the forwarding handler with a given seed, adversary input and finalization.
+
+## Main results
+
+* `Games.InteractiveHandler.impl_of_ret_padFin`, `impl_of_query_padFin`, `finish_of_ret_padFin`:
+  the call lemmas with list-valued answers, states and outputs.
+* `Games.fwdHandler_impl`: the forwarding handler forwards.
+* `Complexity.NUPPT.exists_withAdviceOn`: hard-wiring a second input component.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §2.1 (non-uniform machines), Theorems 174.8 and 175.9 (book pp. 174–175).
+-/
+
+namespace TCSlib.Cryptography.Games
+
+open Complexity Turing
+
+variable {k : ℕ}
+
+/-! ### Calls read on lists -/
+
+namespace InteractiveHandler
+
+section Calls
+
+variable {k' : ℕ} {din dout : Fin k → PolyExpr} {din' dout' : Fin k' → PolyExpr}
+  (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
+  (ω : Fin (H.seedLen.eval n) → Bool)
+
+/-- **A call that returns at once, on lists:** if the first round on the inner query `x` to
+oracle `i` in state `s` returns `⟨[true], u ‖ v⟩` with `|u| = dout i`, `|v| = stateLen`, the call
+answers `padFin _ u` with the new state `padFin _ v`, asking nothing (`impl_of_ret`, with
+`ofFn_padFin_of_length`). -/
+theorem impl_of_ret_padFin (i : Fin k) (x : Fin ((din i).eval n) → Bool)
+    (s : Fin (H.stateLen.eval n) → Bool) (u v : List Bool) (hu : u.length = (dout i).eval n)
+    (hv : v.length = H.stateLen.eval n)
+    (hrun : H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x) []) =
+      pairEncode [true] (u ++ v)) :
+    H.impl n z ω i x s = .pure (padFin _ u, padFin _ v) :=
+  H.impl_of_ret n z ω x s _ _ (by rw [ofFn_padFin_of_length hu, ofFn_padFin_of_length hv, hrun])
+
+/-- **A call with one outer query, on lists:** if the first round asks the outer query `x'` to
+oracle `j`, and the second round, with the answer `y` in the outer log, returns
+`⟨[true], u y ‖ v y⟩` with `|u y| = dout i`, `|v y| = stateLen`, then (with `perCall ≥ 1`) the
+call is `query j x' (fun y => pure (padFin _ (u y), padFin _ (v y)))` (`impl_of_query`, with
+`ofFn_padFin_of_length`). -/
+theorem impl_of_query_padFin (i : Fin k) (x : Fin ((din i).eval n) → Bool)
+    (s : Fin (H.stateLen.eval n) → Bool) (j : Fin k') (x' : Fin ((din' j).eval n) → Bool)
+    (u v : (Fin ((dout' j).eval n) → Bool) → List Bool)
+    (hu : ∀ y, (u y).length = (dout i).eval n) (hv : ∀ y, (v y).length = H.stateLen.eval n)
+    (hpc : 1 ≤ H.perCall.eval n)
+    (hrun₀ : H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x) []) =
+      pairEncode [false] (pairEncode (List.replicate j true) (List.ofFn x')))
+    (hrun₁ : ∀ y, H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x)
+      (pairEncode (pairEncode (List.replicate j true) (pairEncode (List.ofFn x') (List.ofFn y)))
+        [])) = pairEncode [true] (u y ++ v y)) :
+    H.impl n z ω i x s = .query j x' fun y => .pure (padFin _ (u y), padFin _ (v y)) :=
+  H.impl_of_query n z ω x s j x' _ _ hpc hrun₀ fun y => by
+    rw [ofFn_padFin_of_length (hu y), ofFn_padFin_of_length (hv y), hrun₁]
+
+/-- **A finalization that returns at once, on lists:** if its first round returns `⟨[true], b⟩`
+with `|b| = outLen(n)`, the finalization is `pure (padFin _ b)`, asking nothing
+(`finish_of_ret`, with `ofFn_padFin_of_length`). -/
+theorem finish_of_ret_padFin (s : Fin (H.stateLen.eval n) → Bool) {d : ℕ} (a : Fin d → Bool)
+    (b : List Bool) (hb : b.length = H.outLen.eval n)
+    (hrun : H.finRun (finInput n z (List.ofFn ω) (List.ofFn s) (List.ofFn a) []) =
+      pairEncode [true] b) :
+    H.finish n z ω s a = .pure (padFin _ b) :=
+  H.finish_of_ret n z ω s a _ (by rw [ofFn_padFin_of_length hb, hrun])
+
+end Calls
+
+end InteractiveHandler
+
+/-! ### The forwarding handler -/
+
+open InteractiveHandler in
+/-- **One forwarding round.** With an empty outer log, ask the outer oracle `i` the query `x`;
+with the outer answer `y` in the log, return `y` and keep the state. -/
+private def fwdRun (w : List Bool) : List Bool :=
+  if decide (rL w = []) then pairEncode [false] (pairEncode (rI w) (rX w))
+  else pairEncode [true] (rAns w ++ rS w)
+
+open InteractiveHandler in
+/-- The forwarding round is polynomial-time. -/
+private theorem polyTimeComputable_fwdRun : PolyTimeComputable fwdRun :=
+  polyTimeComputable_ite (polyTimeComputable_isNil.comp polyTimeComputable_rL)
+    ((polyTimeComputable_const [false]).pairEncode
+      (polyTimeComputable_rI.pairEncode polyTimeComputable_rX))
+    ((polyTimeComputable_const [true]).pairEncode
+      (polyTimeComputable_rAns.append polyTimeComputable_rS))
+
+/-- **The forwarding handler** for `k` bit-string oracles with lengths `din`, `dout`, inner and
+outer alike: empty state, the seed of `seedLen(n)` bits, one outer call per inner query, which
+forwards the query to the outer oracle of the same index and returns its answer; the adversary's
+input `advIn`, and the finalization `finRun` with `outLen(n)`-bit output and at most `finCall(n)`
+outer queries. -/
+def fwdHandler (din dout : Fin k → PolyExpr) (seedLen : PolyExpr)
+    (advIn : List Bool → List Bool) (advIn_poly : PolyTimeComputable advIn)
+    (outLen finCall : PolyExpr) (finRun : List Bool → List Bool)
+    (finRun_poly : PolyTimeComputable finRun) : InteractiveHandler k din dout k din dout where
+  stateLen := .const 0
+  seedLen := seedLen
+  perCall := .const 1
+  init _ := zeroBits _
+  run := fwdRun
+  poly := polyTimeComputable_fwdRun
+  advIn := advIn
+  advIn_poly := advIn_poly
+  outLen := outLen
+  finCall := finCall
+  finRun := finRun
+  finRun_poly := finRun_poly
+
+attribute [simps (config := { isSimp := false }) stateLen seedLen perCall init advIn outLen finCall
+  finRun] fwdHandler
+
+section Forward
+
+variable (din dout : Fin k → PolyExpr) (seedLen : PolyExpr) (advIn : List Bool → List Bool)
+  (advIn_poly : PolyTimeComputable advIn) (outLen finCall : PolyExpr)
+  (finRun : List Bool → List Bool) (finRun_poly : PolyTimeComputable finRun)
+
+/-- **The forwarding handler forwards:** the inner query `x` to oracle `i` in state `s` is the
+outer query `x` to oracle `i`, answered with the outer answer `y` and the state kept:
+`H.impl n z ω i x s = query i x (fun y => pure (y, s))`.
+
+**Proof sketch.** `InteractiveHandler.impl_of_query` with `perCall = 1`: the call's first round
+has an empty outer log (`rL_input`), so it asks the query `⟨1^i, x⟩` (`rI_input`, `rX_input`);
+its second round reads the answer `y` from the one-entry log (`rAns_input`) and returns `y ‖ s`
+(`rS_input`). -/
+theorem fwdHandler_impl (n : ℕ) (z : List Bool)
+    (ω : Fin ((fwdHandler din dout seedLen advIn advIn_poly outLen finCall finRun
+      finRun_poly).seedLen.eval n) → Bool) (i : Fin k) (x : Fin ((din i).eval n) → Bool)
+    (s : Fin ((fwdHandler din dout seedLen advIn advIn_poly outLen finCall finRun
+      finRun_poly).stateLen.eval n) → Bool) :
+    (fwdHandler din dout seedLen advIn advIn_poly outLen finCall finRun finRun_poly).impl n z ω
+        i x s = .query i x fun y => .pure (y, s) := by
+  refine InteractiveHandler.impl_of_query _ n z ω x s i x (fun y => y) (fun _ => s)
+    (by rw [fwdHandler_perCall, PolyExpr.eval_const]) ?_ fun y => ?_
+  · show fwdRun _ = _
+    rw [fwdRun, InteractiveHandler.rL_input, InteractiveHandler.rI_input,
+      InteractiveHandler.rX_input, if_pos (decide_eq_true rfl)]
+  · show fwdRun _ = _
+    rw [fwdRun, InteractiveHandler.rL_input, InteractiveHandler.rAns_input,
+      InteractiveHandler.rS_input, if_neg (fun h => pairEncode_ne_nil _ _ (of_decide_eq_true h))]
+
+end Forward
+
+/-! ### Hard-wiring a second input component -/
+
+/-- **Hard-wiring a second input component** [PS10, §2.1, implicit]: for a machine `B` and a
+polynomially bounded family `β n` there is a machine `B'` with the same coins (`h`) whose
+computation on the input `x` is `B`'s on `⟨x, β n⟩`, for every codec and budget:
+`B'.toCompOn codec n q x (coinsCongr h n r) = B.toCompOn codec n q ⟨x, β n⟩ r`.
+
+**Proof sketch.** `B₁ := NUPPT.exists_comp B` with the re-pairing
+`⟨⟨x, L⟩, β⟩ ↦ ⟨⟨x, β⟩, L⟩`, then `B' := NUPPT.exists_withAdvice B₁ β`; on `⟨x, L⟩` (the input
+and the encoded log) `B'` runs `B` on `⟨⟨x, β n⟩, L⟩`. -/
+theorem _root_.Complexity.NUPPT.exists_withAdviceOn (B : NUPPT) (β : ℕ → List Bool)
+    (b : PolyExpr) (hβ : ∀ n, (β n).length ≤ b.eval n) :
+    ∃ (B' : NUPPT) (h : B.coins = B'.coins), ∀ (n : ℕ) {ι α : Type} {spec : OracleSpec ι}
+      (codec : MachineCodec spec α) (q : ℕ) (x : List Bool) (r : B.Coins n),
+      B'.toCompOn codec n q x (NUPPT.coinsCongr h n r) =
+        B.toCompOn codec n q (pairEncode x (β n)) r := by
+  have hpre : PolyTimeComputable fun w : List Bool =>
+      pairEncode (pairEncode (pairFstD (pairFstD w)) (pairSndD w)) (pairSndD (pairFstD w)) :=
+    ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD).pairEncode
+      polyTimeComputable_pairSndD).pairEncode
+      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD)
+  obtain ⟨B₁, hc₁, -, -, hB₁⟩ := NUPPT.exists_comp B hpre polyTimeComputable_id
+  obtain ⟨B', hc', hB'⟩ := NUPPT.exists_withAdvice B₁ β b hβ
+  refine ⟨B', (hc'.trans hc₁).symm, fun n ι α spec codec q x r => ?_⟩
+  rw [NUPPT.toCompOn_eq, NUPPT.toCompOn_eq]
+  congr 1
+  funext hist
+  rw [NUPPT.runAt_coinsCongr, hB', hB₁, NUPPT.runAt_eq]
+  simp only [pairFstD_pairEncode, pairSndD_pairEncode, id_eq]
+
+end TCSlib.Cryptography.Games
diff --git a/TCSlib/Cryptography/Games/Hopping.lean b/TCSlib/Cryptography/Games/Hopping.lean
index 5fc1e5184..42306c1ab 100644
--- a/TCSlib/Cryptography/Games/Hopping.lean
+++ b/TCSlib/Cryptography/Games/Hopping.lean
@@ -32,8 +32,8 @@ The hybrid argument itself is `advantage_hybrid` (`TCSlib.Cryptography.Games.Adv
 
 ## Main results
 
-* `ProbComp.prob_eq_one_of_allOutputs`, `ProbComp.expect_mono_of_allOutputs`: reasoning on the
-  possible outputs only.
+* `ProbComp.prob_eq_one_of_allOutputs`, `ProbComp.expect_mono_of_allOutputs`,
+  `ProbComp.expect_congr_of_allOutputs`: reasoning on the possible outputs only.
 * `ProbComp.abs_prob_sub_le_of_agree`: the difference lemma [Sho04, §1.1, Lemma 1].
 * `ProbComp.prob_mem_le`: the collision bound; `ProbComp.expect_sample_mem_le`, its form for a
   uniform sample and a fixed list.
@@ -41,7 +41,9 @@ The hybrid argument itself is `advantage_hybrid` (`TCSlib.Cryptography.Games.Adv
 * `ProbComp.prob_bad_le`: the per-query potential bound `Pr[bad] ≤ q · (size + q) · δ`.
 * `Games.prob_eq_until_bad`, `Games.identical_until_bad`, `Games.identical_until_bad_init`: the
   code-based fundamental lemma [BR06], in semantic form, from a fixed or a sampled initial
-  state; `Games.hagree_of_eq` recovers the syntactic hypothesis.
+  state; `Games.hagree_of_eq` recovers the syntactic hypothesis; `Games.expect_eq_until_bad`, the
+  expectation form for functions of the output and the final state.
+* `Games.expect_simulate_eager`: one-shot coins may be drawn in advance.
 
 ## References
 
@@ -93,6 +95,14 @@ theorem expect_mono_of_allOutputs {c : ProbComp α} {P : α → Prop} (hc : c.Al
     exact mul_le_mul_of_nonneg_left
       (sum_le_sum fun j _ => ih j (OracleComp.allOutputs_query.1 hc j)) (by positivity)
 
+/-- Two functions that agree on every possible output have the same expectation: if
+`c.AllOutputs P` and `f a = g a` whenever `P a`, then `𝔼_c f = 𝔼_c g` (`expect_mono_of_allOutputs`
+both ways). -/
+theorem expect_congr_of_allOutputs {c : ProbComp α} {P : α → Prop} (hc : c.AllOutputs P)
+    {f g : α → ℝ} (h : ∀ a, P a → f a = g a) : expect c f = expect c g :=
+  le_antisymm (expect_mono_of_allOutputs hc fun a ha => (h a ha).le)
+    (expect_mono_of_allOutputs hc fun a ha => (h a ha).ge)
+
 /-- An event holding at every possible output has probability one. -/
 theorem prob_eq_one_of_allOutputs {c : ProbComp α} {p : α → Prop} (hc : c.AllOutputs p) :
     prob c p = 1 := by
@@ -178,21 +188,57 @@ theorem simulate_allOutputs_bad {spec : OracleSpec ι} {impl : QueryImpl spec σ
     rw [simulate_query]
     exact OracleComp.AllOutputs.bind (hstick i x s hs) fun ys hys => ih ys.1 hys
 
-/-- Splitting an expectation on a predicate: on `b` the function is `1`, elsewhere `f`. -/
-private theorem expect_ite_one_split {γ : Type} (c : ProbComp γ) (b : γ → Prop) [DecidablePred b]
-    (f : γ → ℝ) :
-    ProbComp.expect c (fun y => if b y then 1 else f y) =
-      (1 - ProbComp.expect c (fun y => if b y then 0 else 1)) +
-        ProbComp.expect c (fun y => if b y then 0 else f y) := by
-  have h : (fun y => if b y then (1 : ℝ) else f y) =
-      fun y => (1 + (-1) * (if b y then (0 : ℝ) else 1)) + (if b y then 0 else f y) := by
-    funext y
-    by_cases hy : b y <;> simp [hy]
-  rw [h, ProbComp.expect_add c (fun y => 1 + (-1) * (if b y then (0 : ℝ) else 1))
-      (fun y => if b y then 0 else f y),
-    ProbComp.expect_add c (fun _ => (1 : ℝ)) (fun y => (-1) * (if b y then (0 : ℝ) else 1)),
-    ProbComp.expect_const, ProbComp.expect_const_mul]
-  ring
+/-- **Equal until bad, in expectation, for functions of the output and the final state.** Let two
+implementations give, from every good state, the same law to good successors, and let each keep
+bad states bad. Then from a good state, for every function `G` of the output and the final state,
+`𝔼[G · 1_{good}]` is the same under both simulations:
+`𝔼[fun r => if bad r.2 then 0 else G r] (simulate impl₀ c s) =
+𝔼[fun r => if bad r.2 then 0 else G r] (simulate impl₁ c s)`.
+
+**Proof sketch.** Induction on the computation. From a bad successor the continuation's value is
+`0` on both sides (`simulate_allOutputs_bad`); from a good one the two values agree by induction;
+so both expectations only see the values at good successors, which `hagree` equates. -/
+theorem expect_eq_until_bad {spec : OracleSpec ι} {impl₀ impl₁ : QueryImpl spec σ unifSpec}
+    (bad : σ → Prop) [DecidablePred bad]
+    (hagree : ∀ i x s, ¬ bad s → ∀ g : spec.rng i × σ → ℝ,
+      ProbComp.expect (impl₀ i x s) (fun ys => if bad ys.2 then 0 else g ys) =
+        ProbComp.expect (impl₁ i x s) (fun ys => if bad ys.2 then 0 else g ys))
+    (hstick₀ : ∀ i x s, bad s → (impl₀ i x s).AllOutputs fun ys => bad ys.2)
+    (hstick₁ : ∀ i x s, bad s → (impl₁ i x s).AllOutputs fun ys => bad ys.2)
+    (c : OracleComp spec α) (G : α × σ → ℝ) {s : σ} (hs : ¬ bad s) :
+    ProbComp.expect (simulate impl₀ c s) (fun r => if bad r.2 then 0 else G r) =
+      ProbComp.expect (simulate impl₁ c s) (fun r => if bad r.2 then 0 else G r) := by
+  induction c generalizing s with
+  | pure a => rw [simulate_pure, simulate_pure]
+  | query i x k ih =>
+    simp only [simulate_query, ProbComp.expect_bind]
+    have hz : ∀ (impl : QueryImpl spec σ unifSpec),
+        (∀ i x s, bad s → (impl i x s).AllOutputs fun ys => bad ys.2) →
+        ∀ ys : spec.rng i × σ, bad ys.2 →
+          ProbComp.expect (simulate impl (k ys.1) ys.2) (fun r => if bad r.2 then 0 else G r) =
+            0 := by
+      intro impl hst ys hb
+      rw [ProbComp.expect_congr_of_allOutputs (simulate_allOutputs_bad bad hst _ hb)
+        (g := fun _ => 0) fun r hr => if_pos hr, ProbComp.expect_const]
+    have h0 : ∀ ys : spec.rng i × σ,
+        ProbComp.expect (simulate impl₀ (k ys.1) ys.2) (fun r => if bad r.2 then 0 else G r) =
+          if bad ys.2 then 0 else
+            ProbComp.expect (simulate impl₁ (k ys.1) ys.2)
+              (fun r => if bad r.2 then 0 else G r) := by
+      intro ys
+      by_cases hb : bad ys.2
+      · rw [if_pos hb, hz impl₀ hstick₀ ys hb]
+      · rw [if_neg hb, ih ys.1 hb]
+    have h1 : ∀ ys : spec.rng i × σ,
+        ProbComp.expect (simulate impl₁ (k ys.1) ys.2) (fun r => if bad r.2 then 0 else G r) =
+          if bad ys.2 then 0 else
+            ProbComp.expect (simulate impl₁ (k ys.1) ys.2)
+              (fun r => if bad r.2 then 0 else G r) := by
+      intro ys
+      by_cases hb : bad ys.2
+      · rw [if_pos hb, hz impl₁ hstick₁ ys hb]
+      · rw [if_neg hb]
+    rw [funext h0, hagree i x s hs, ← funext h1]
 
 /-- **Equal until bad:** let two implementations give, from every good state, the same law to good
 successors (they may differ arbitrarily on bad successors, including in the call that makes the
@@ -200,11 +246,9 @@ state bad), and let each keep bad states bad. Then, from a good state, the two s
 the same probability to "`Q` holds and the final state is good", and the same probability to "the
 final state is bad".
 
-**Proof sketch.** Induction on the computation. At a query from a good state, write `F_b` for the
-continuation's probability of the event. On a bad successor `F_b` is `0` (for "good at the end")
-or `1` (for "bad at the end") on both sides (`simulate_allOutputs_bad`). So each expectation only
-depends on `F_b` at good successors, where `F₀ = F₁` by induction; and the two implementations give
-good successors the same law (`hagree`, once with `g := F₁` and once with `g := 1`). -/
+**Proof sketch.** Both are expectations of functions that vanish on bad final states:
+"`Q` and good" is `𝔼[if bad then 0 else 1_Q]`, and "bad" is `1 − 𝔼[if bad then 0 else 1]`
+(`prob_not`). Both are equal under the two simulations by `expect_eq_until_bad`. -/
 theorem prob_eq_until_bad {spec : OracleSpec ι} {impl₀ impl₁ : QueryImpl spec σ unifSpec}
     (bad : σ → Prop) [DecidablePred bad]
     (hagree : ∀ i x s, ¬ bad s → ∀ g : spec.rng i × σ → ℝ,
@@ -217,56 +261,29 @@ theorem prob_eq_until_bad {spec : OracleSpec ι} {impl₀ impl₁ : QueryImpl sp
         ProbComp.prob (simulate impl₁ c s) (fun r => Q r.1 ∧ ¬ bad r.2) ∧
       ProbComp.prob (simulate impl₀ c s) (fun r => bad r.2) =
         ProbComp.prob (simulate impl₁ c s) (fun r => bad r.2) := by
-  induction c generalizing s with
-  | pure a => simp only [simulate_pure, and_self]
-  | query i x k ih =>
-    simp only [simulate_query, ProbComp.prob_bind]
-    constructor
-    · -- "`Q` and good at the end"
-      have h0 : ∀ ys : spec.rng i × σ,
-          ProbComp.prob (simulate impl₀ (k ys.1) ys.2) (fun r => Q r.1 ∧ ¬ bad r.2) =
-            if bad ys.2 then 0 else
-              ProbComp.prob (simulate impl₁ (k ys.1) ys.2) (fun r => Q r.1 ∧ ¬ bad r.2) := by
-        intro ys
-        by_cases hb : bad ys.2
-        · rw [if_pos hb]
-          exact ProbComp.prob_eq_zero_of_allOutputs
-            ((simulate_allOutputs_bad bad hstick₀ _ hb).mono fun r hr h => h.2 hr)
-        · rw [if_neg hb]
-          exact (ih ys.1 hb).1
-      have h1 : ∀ ys : spec.rng i × σ,
-          ProbComp.prob (simulate impl₁ (k ys.1) ys.2) (fun r => Q r.1 ∧ ¬ bad r.2) =
-            if bad ys.2 then 0 else
-              ProbComp.prob (simulate impl₁ (k ys.1) ys.2) (fun r => Q r.1 ∧ ¬ bad r.2) := by
-        intro ys
-        by_cases hb : bad ys.2
-        · rw [if_pos hb]
-          exact ProbComp.prob_eq_zero_of_allOutputs
-            ((simulate_allOutputs_bad bad hstick₁ _ hb).mono fun r hr h => h.2 hr)
-        · rw [if_neg hb]
-      rw [funext h0, hagree i x s hs, ← funext h1]
-    · -- "bad at the end"
-      have h0 : ∀ ys : spec.rng i × σ,
-          ProbComp.prob (simulate impl₀ (k ys.1) ys.2) (fun r => bad r.2) =
-            if bad ys.2 then 1 else
-              ProbComp.prob (simulate impl₁ (k ys.1) ys.2) (fun r => bad r.2) := by
-        intro ys
-        by_cases hb : bad ys.2
-        · rw [if_pos hb]
-          exact ProbComp.prob_eq_one_of_allOutputs (simulate_allOutputs_bad bad hstick₀ _ hb)
-        · rw [if_neg hb]
-          exact (ih ys.1 hb).2
-      have h1 : ∀ ys : spec.rng i × σ,
-          ProbComp.prob (simulate impl₁ (k ys.1) ys.2) (fun r => bad r.2) =
-            if bad ys.2 then 1 else
-              ProbComp.prob (simulate impl₁ (k ys.1) ys.2) (fun r => bad r.2) := by
-        intro ys
-        by_cases hb : bad ys.2
-        · rw [if_pos hb]
-          exact ProbComp.prob_eq_one_of_allOutputs (simulate_allOutputs_bad bad hstick₁ _ hb)
-        · rw [if_neg hb]
-      rw [funext h0, expect_ite_one_split, hagree i x s hs (fun _ => 1), hagree i x s hs,
-        ← expect_ite_one_split, ← funext h1]
+  classical
+  have hgood : ∀ c' : ProbComp (α × σ), ProbComp.prob c' (fun r => Q r.1 ∧ ¬ bad r.2) =
+      ProbComp.expect c' (fun r => if bad r.2 then 0 else if Q r.1 then 1 else 0) := by
+    intro c'
+    rw [ProbComp.prob_eq_expect]
+    congr 1
+    funext r
+    by_cases hb : bad r.2 <;> by_cases hq : Q r.1 <;> simp [hb, hq]
+  have hbad : ∀ c' : ProbComp (α × σ), ProbComp.prob c' (fun r => bad r.2) =
+      1 - ProbComp.expect c' (fun r => if bad r.2 then 0 else 1) := by
+    intro c'
+    have h := ProbComp.prob_not c' (fun r => bad r.2)
+    have e : ProbComp.prob c' (fun r => ¬ bad r.2) =
+        ProbComp.expect c' (fun r => if bad r.2 then 0 else 1) := by
+      rw [ProbComp.prob_eq_expect]
+      congr 1
+      funext r
+      by_cases hb : bad r.2 <;> simp [hb]
+    linarith
+  refine ⟨?_, ?_⟩
+  · rw [hgood, hgood]
+    exact expect_eq_until_bad bad hagree hstick₀ hstick₁ c _ hs
+  · rw [hbad, hbad, expect_eq_until_bad bad hagree hstick₀ hstick₁ c (fun _ => 1) hs]
 
 /-- **Identical until bad** (the code-based fundamental lemma): let two implementations of the
 same oracles give, from every good state, the same law to good successors, and let each keep `bad`
@@ -442,4 +459,66 @@ theorem expect_sample_mem_le {T : Type} [Fintype T] [Nonempty T] [DecidableEq T]
 
 end ProbComp
 
+/-! ### One-shot coins drawn in advance -/
+
+section Eager
+
+variable {spec : OracleSpec ι} {T : Type} [Fintype T] [Nonempty T]
+
+/-- From a used state, an implementation that agrees with `O` there simulates like `O`. -/
+private theorem simulate_eq_of_used (O O' : QueryImpl spec σ unifSpec) (used : σ → Prop)
+    (hused : ∀ i x s, used s → O' i x s = O i x s)
+    (hstick : ∀ i x s, used s → (O i x s).AllOutputs fun p => used p.2)
+    (c : OracleComp spec α) {s : σ} (hs : used s) : simulate O' c s = simulate O c s := by
+  induction c generalizing s with
+  | pure a => rw [simulate_pure, simulate_pure]
+  | query i x k ih =>
+    rw [simulate_query, simulate_query, hused i x s hs]
+    exact OracleComp.bind_congr_of_allOutputs (hstick i x s hs) fun p hp => ih p.1 hp
+
+/-- **One-shot coins drawn in advance.** Let `O` be an implementation and `OE t` its variants with
+coins `t ∈ T` fixed in advance, and let `used` mark the states after the coins are spent:
+- from a used state, `OE t` is `O`, and `O` keeps the state used;
+- from an unused state, a call either does not use the coins (`OE t` is `O` for every `t`, and the
+  state stays unused), or it is the one that spends them (`O` samples `t` and runs `OE t`, and
+  every successor is used).
+
+Then from an unused state, `O`'s simulation has the law of `OE t`'s, averaged over `t`:
+`𝔼[G(simulate O c s)] = 𝔼_{t ← T} 𝔼[G(simulate (OE t) c s)]`.
+
+**Proof sketch.** Induction on `c`. From used states the two simulations coincide
+(`simulate_eq_of_used`). At a query from an unused state: in the first case, rewrite the call,
+apply the induction hypothesis at the (unused) successors and exchange the expectations
+(`ProbComp.expect_expect_sample`); in the second, expand `O`'s sample and conclude from the
+coincidence at the (used) successors. -/
+theorem expect_simulate_eager (O : QueryImpl spec σ unifSpec) (OE : T → QueryImpl spec σ unifSpec)
+    (used : σ → Prop) (hused : ∀ t i x s, used s → OE t i x s = O i x s)
+    (hstick : ∀ i x s, used s → (O i x s).AllOutputs fun p => used p.2)
+    (hfresh : ∀ i x s, ¬ used s →
+      (∀ t, OE t i x s = O i x s ∧ (O i x s).AllOutputs fun p => ¬ used p.2) ∨
+      (O i x s = (ProbComp.sample T).bind (fun t => OE t i x s) ∧
+        ∀ t, (OE t i x s).AllOutputs fun p => used p.2))
+    (c : OracleComp spec α) (G : α × σ → ℝ) {s : σ} (hs : ¬ used s) :
+    ProbComp.expect (simulate O c s) G =
+      ProbComp.expect (ProbComp.sample T) fun t => ProbComp.expect (simulate (OE t) c s) G := by
+  induction c generalizing s with
+  | pure a =>
+    simp only [simulate_pure, ProbComp.expect_pure]
+    exact (ProbComp.expect_const _ _).symm
+  | query i x k ih =>
+    simp only [simulate_query, ProbComp.expect_bind]
+    rcases hfresh i x s hs with h | ⟨h, hu⟩
+    · have hO : ∀ t, OE t i x s = O i x s := fun t => (h t).1
+      have hun : (O i x s).AllOutputs fun p => ¬ used p.2 :=
+        (h (Classical.arbitrary T)).2
+      simp only [hO]
+      rw [ProbComp.expect_congr_of_allOutputs hun fun p hp => ih p.1 hp,
+        ProbComp.expect_expect_sample]
+    · rw [h, ProbComp.expect_bind]
+      refine congrArg _ (funext fun t => ?_)
+      refine ProbComp.expect_congr_of_allOutputs (hu t) fun p hp => ?_
+      rw [simulate_eq_of_used O (OE t) used (hused t) hstick _ hp]
+
+end Eager
+
 end TCSlib.Cryptography.Games
diff --git a/TCSlib/Cryptography/Games/Machines.lean b/TCSlib/Cryptography/Games/Machines.lean
index 3bc7de065..d738c0ed6 100644
--- a/TCSlib/Cryptography/Games/Machines.lean
+++ b/TCSlib/Cryptography/Games/Machines.lean
@@ -42,6 +42,9 @@ result, stated in a later module.
 
 * `Games.buildComp_costBoundedBy`, `NUPPT.toComp_costBoundedBy`: the computation makes at most `q`
   queries.
+* `Games.buildComp_of_ret`: a final output is the computation at every budget.
+* `Games.buildComp_budget_eq`, `NUPPT.toCompOn_budget_eq`: a computation at budget `K ≥ j` that
+  makes at most `j` queries is the computation at budget `j`.
 
 ## References
 
@@ -146,6 +149,14 @@ theorem buildComp_succ_of_query {q : ℕ} {i : ι} {x : spec.dom i} (h : next hi
       .query i x (fun y => buildComp next timeout q (hist ++ [⟨i, x, y⟩])) := by
   rw [buildComp, h]
 
+/-- A final output is the computation at every budget: if `next hist = ret a`, then
+`buildComp next timeout q hist = pure a`. -/
+theorem buildComp_of_ret {q : ℕ} {a : α} (h : next hist = .ret a) :
+    buildComp next timeout q hist = .pure a := by
+  cases q with
+  | zero => exact buildComp_zero_of_ret h
+  | succ q => exact buildComp_succ_of_ret h
+
 end BuildComp
 
 /-- The computation built with budget `q` makes at most `q` queries, from every log. -/
@@ -164,6 +175,46 @@ theorem buildComp_costBoundedBy {spec : OracleSpec ι} (next : QueryLog spec →
       exact (OracleComp.costBoundedBy_query _ _ _ _ _).2
         ⟨Nat.le_add_left 1 q, fun y => buildComp_costBoundedBy next timeout q _⟩
 
+/-- **Budget reduction for `buildComp`.** If the computation of `next` at budget `K` from the log
+`hist` makes at most `j ≤ K` queries on every path, it is the computation at budget `j`:
+`buildComp next t j hist = buildComp next t K hist`.
+
+**Proof sketch.** Induction on `j`. A final output is the same at every budget. A query at budget
+`K` costs `1 ≤ j`, so `j = j' + 1` and `K = K' + 1`; both computations ask the same query and
+continue with the same log, at budgets `j'` and `K' ≥ j'`, and the continuation makes at most `j'`
+queries. At `j = 0` a query is impossible unless `K = 0`, where both give `timeout`. -/
+theorem buildComp_budget_eq {spec : OracleSpec ι} (next : QueryLog spec → Move spec α) (t : α) :
+    ∀ (j K : ℕ) (hist : QueryLog spec), j ≤ K →
+      (buildComp next t K hist).CostBoundedBy (fun _ => 1) j →
+      buildComp next t j hist = buildComp next t K hist := by
+  intro j
+  induction j with
+  | zero =>
+    intro K hist _ hc
+    cases h : next hist with
+    | ret a =>
+      cases K with
+      | zero => rfl
+      | succ K => rw [buildComp_zero_of_ret h, buildComp_succ_of_ret h]
+    | query i x =>
+      cases K with
+      | zero => rfl
+      | succ K =>
+        rw [buildComp_succ_of_query h, OracleComp.costBoundedBy_query] at hc
+        exact absurd hc.1 (by omega)
+  | succ j ih =>
+    intro K hist hK hc
+    obtain ⟨K, rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
+    cases h : next hist with
+    | ret a => rw [buildComp_succ_of_ret h, buildComp_succ_of_ret h]
+    | query i x =>
+      rw [buildComp_succ_of_query h] at hc ⊢
+      rw [buildComp_succ_of_query h]
+      rw [OracleComp.costBoundedBy_query] at hc
+      congr 1
+      funext y
+      exact ih K _ (by omega) (by simpa using hc.2 y)
+
 /-- The oracle computation of the machine `D` at parameter `n`, with coins `r` and query budget
 `q`: the machine's next-move function is one activation of `D` on the encoded log.
 [PS10, Definition 96.1], generalized to oracle families and arbitrary outputs. -/
@@ -213,4 +264,15 @@ theorem _root_.Complexity.NUPPT.toCompOn_costBoundedBy {spec : OracleSpec ι} (D
     (D.toCompOn codec n q x r).CostBoundedBy (fun _ => 1) q :=
   buildComp_costBoundedBy _ _ q []
 
+/-- **Budget reduction for a machine:** if `D`'s computation on `x` at budget `K ≥ j` makes at
+most `j` queries on every path, it is `D`'s computation at budget `j`:
+`D.toCompOn codec n j x r = D.toCompOn codec n K x r` (`buildComp_budget_eq`). -/
+theorem _root_.Complexity.NUPPT.toCompOn_budget_eq {spec : OracleSpec ι} (D : NUPPT) {β : Type}
+    (codec : MachineCodec spec β) (n j K : ℕ) (x : List Bool) (r : D.Coins n) (hjK : j ≤ K)
+    (hc : (D.toCompOn codec n K x r).CostBoundedBy (fun _ => 1) j) :
+    D.toCompOn codec n j x r = D.toCompOn codec n K x r := by
+  rw [NUPPT.toCompOn_eq] at hc ⊢
+  rw [NUPPT.toCompOn_eq]
+  exact buildComp_budget_eq _ _ j K [] hjK hc
+
 end TCSlib.Cryptography.Games
diff --git a/TCSlib/Cryptography/Games/OracleComp.lean b/TCSlib/Cryptography/Games/OracleComp.lean
index c8f91d04b..4bcb13622 100644
--- a/TCSlib/Cryptography/Games/OracleComp.lean
+++ b/TCSlib/Cryptography/Games/OracleComp.lean
@@ -48,6 +48,8 @@ layer ([Gar26]); the bridge between the two is in the S2b layer.
 * `Games.OracleComp.CostBoundedBy.bind`: costs add under sequencing.
 * `Games.OracleComp.costBoundedBy_liftLeft`, `costBoundedBy_liftRight`: lifting into a union of
   specifications keeps the cost.
+* `Games.OracleComp.bind_congr_of_allOutputs`, `Games.OracleComp.CostBoundedBy.bind_of_allOutputs`:
+  sequencing needs the continuation only on the possible outputs.
 
 ## References
 
@@ -326,6 +328,44 @@ theorem AllOutputs.bind {spec : OracleSpec ι} {P : α → Prop} {Q : β → Pro
   | pure a => exact hf a hc
   | query i x k ih => exact fun y => ih y (hc y)
 
+/-- Two continuations that agree on every possible output give the same computation:
+`c.bind f = c.bind g` when `f a = g a` whenever `P a`, and `c.AllOutputs P`. -/
+theorem bind_congr_of_allOutputs {spec : OracleSpec ι} {c : OracleComp spec α}
+    {P : α → Prop} (hc : c.AllOutputs P) {f g : α → OracleComp spec β}
+    (h : ∀ a, P a → f a = g a) : c.bind f = c.bind g := by
+  induction c with
+  | pure a =>
+    rw [OracleComp.pure_bind, OracleComp.pure_bind]
+    exact h a (OracleComp.allOutputs_pure.1 hc)
+  | query i x k ih =>
+    rw [OracleComp.query_bind, OracleComp.query_bind]
+    congr 1
+    funext y
+    exact ih y (OracleComp.allOutputs_query.1 hc y)
+
+/-- **Costs add under sequencing, on the possible outputs:** if `c` fits in `q₁`, every possible
+output of `c` satisfies `P`, and `f a` fits in `q₂` for every `a` with `P a`, then `c` followed by
+`f` fits in `q₁ + q₂` (`CostBoundedBy.bind` with the continuations restricted to the possible
+outputs).
+
+**Proof sketch.** As for `CostBoundedBy.bind`, by induction on `c`; at a return `a` the
+hypothesis on `f a` applies since `P a`. -/
+theorem CostBoundedBy.bind_of_allOutputs {cost : ι₁ → ℕ} {c : OracleComp spec α}
+    {f : α → OracleComp spec β} {P : α → Prop} {q₁ q₂ : ℕ} (hc : c.CostBoundedBy cost q₁)
+    (hP : c.AllOutputs P) (hf : ∀ a, P a → (f a).CostBoundedBy cost q₂) :
+    (c.bind f).CostBoundedBy cost (q₁ + q₂) := by
+  induction c generalizing q₁ with
+  | pure a =>
+    rw [OracleComp.pure_bind]
+    exact (hf a (OracleComp.allOutputs_pure.1 hP)).mono (Nat.le_add_left _ _)
+  | query i x k ih =>
+    obtain ⟨hi, hk⟩ := (OracleComp.costBoundedBy_query _ _ _ _ _).1 hc
+    rw [OracleComp.query_bind]
+    refine (OracleComp.costBoundedBy_query _ _ _ _ _).2
+      ⟨Nat.le_trans hi (Nat.le_add_right _ _), fun y => ?_⟩
+    rw [Nat.sub_add_comm hi]
+    exact ih y (hk y) (OracleComp.allOutputs_query.1 hP y)
+
 end OracleComp
 
 end TCSlib.Cryptography.Games
diff --git a/TCSlib/Cryptography/Games/Probability.lean b/TCSlib/Cryptography/Games/Probability.lean
index 3ffd71753..c27939a16 100644
--- a/TCSlib/Cryptography/Games/Probability.lean
+++ b/TCSlib/Cryptography/Games/Probability.lean
@@ -46,6 +46,7 @@ information-theory layer, so statistical distance and closeness (`EpsClose`) app
 * `ProbComp.expect_sample_equiv`, `expect_sample_comm`, `expect_sample_unique`,
   `expect_sample_update`, `expect_sample_coord`: reindexing, exchanging and resampling uniform
   samples; `expect_sub`, `abs_expect_sub_le`: subtraction and pointwise closeness.
+* `ProbComp.expect_expect_sample`: exchanging an expectation with a uniform sample (Fubini).
 
 ## References
 
@@ -317,6 +318,17 @@ theorem expect_sample_comm [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
   refine sum_congr rfl fun b _ => sum_congr rfl fun a _ => ?_
   ring
 
+/-- **Fubini for a uniform sample:** `𝔼_c[𝔼_{t ← T}[h a t]] = 𝔼_{t ← T}[𝔼_c[h a t]]`.
+
+**Proof sketch.** The inner sample is a uniform average (`expect_sample`); pull the constant
+factor and the finite sum out of the outer expectation (`expect_const_mul`, `expect_sum`). -/
+theorem expect_expect_sample (c : ProbComp α) (T : Type) [Fintype T] [Nonempty T]
+    (h : α → T → ℝ) :
+    expect c (fun a => expect (sample T) (h a)) =
+      expect (sample T) fun t => expect c fun a => h a t := by
+  simp only [expect_sample]
+  rw [expect_const_mul, expect_sum]
+
 /-- **Sampling a singleton type** returns its element: `𝔼_{a ← α} g a = g default`. -/
 theorem expect_sample_unique [Fintype α] [Unique α] (g : α → ℝ) :
     expect (sample α) g = g default := by
diff --git a/TCSlib/Cryptography/Games/Simulate.lean b/TCSlib/Cryptography/Games/Simulate.lean
index cb906962a..93da9a335 100644
--- a/TCSlib/Cryptography/Games/Simulate.lean
+++ b/TCSlib/Cryptography/Games/Simulate.lean
@@ -44,6 +44,8 @@ queried" are predicates on that log. Logging never changes the computation
 * `Games.simulate_costBoundedBy`: if each query of `c` to oracle `i` is answered by a computation
   of cost at most `b i`, and `c` is cost-bounded by `q` when oracle `i` costs `b i`, then the
   simulation is cost-bounded by `q`.
+* `Games.simulate_costBoundedBy_once`: an implementation whose only costly call (of cost at most
+  one) marks the state as used costs at most one query in total.
 * `Games.simulate_eq_of_abs`, `Games.simulate_eq_of_abs_bounded`: simulation through an
   abstraction of the state, on every run or along runs with a query budget.
 
@@ -275,6 +277,51 @@ theorem simulate_costBoundedBy {spec : OracleSpec ι} {spec' : OracleSpec ι'}
     rw [simulate_query]
     exact h
 
+/-- **A one-shot oracle costs at most one query in total.** Let `good` be an invariant of the
+states and `used` mark the states after the costly call. If from a good used state every call is
+free and keeps the state good and used, and from a good unused state every call is either free and
+keeps the state good and unused, or costs at most `1` and leaves it good and used, then the
+simulation of any computation from a good state `s` costs at most `0` (used) or `1` (unused):
+`(simulate impl c s).CostBoundedBy cost (if used s then 0 else 1)`.
+
+**Proof sketch.** Induction on the computation; at a query,
+`OracleComp.CostBoundedBy.bind_of_allOutputs` with the call's cost and the continuation's
+(`0 + 0`, `0 + 1` or `1 + 0`). -/
+theorem simulate_costBoundedBy_once {spec : OracleSpec ι} {spec' : OracleSpec ι'}
+    (impl : QueryImpl spec σ spec') (cost : ι' → ℕ)
+    (good used : σ → Prop) [DecidablePred used]
+    (hused : ∀ i x s, good s → used s →
+      (impl i x s).CostBoundedBy cost 0 ∧ (impl i x s).AllOutputs fun p => good p.2 ∧ used p.2)
+    (hfresh : ∀ i x s, good s → ¬ used s →
+      ((impl i x s).CostBoundedBy cost 0 ∧
+          (impl i x s).AllOutputs fun p => good p.2 ∧ ¬ used p.2) ∨
+        ((impl i x s).CostBoundedBy cost 1 ∧ (impl i x s).AllOutputs fun p => good p.2 ∧ used p.2))
+    (c : OracleComp spec α) :
+    ∀ s, good s → (simulate impl c s).CostBoundedBy cost (if used s then 0 else 1) := by
+  induction c with
+  | pure a =>
+    intro s _
+    rw [simulate_pure]
+    exact OracleComp.costBoundedBy_pure _ _ _
+  | query i x k ih =>
+    intro s hs
+    rw [simulate_query]
+    by_cases hu : used s
+    · obtain ⟨h₀, hP⟩ := hused i x s hs hu
+      have := OracleComp.CostBoundedBy.bind_of_allOutputs h₀ hP fun p hp => by
+        have h := ih p.1 p.2 hp.1
+        rwa [if_pos hp.2] at h
+      rwa [if_pos hu]
+    · rw [if_neg hu]
+      rcases hfresh i x s hs hu with ⟨h₀, hP⟩ | ⟨h₁, hP⟩
+      · have := OracleComp.CostBoundedBy.bind_of_allOutputs h₀ hP fun p hp => by
+          have h := ih p.1 p.2 hp.1
+          rwa [if_neg hp.2] at h
+        rwa [Nat.zero_add] at this
+      · exact OracleComp.CostBoundedBy.bind_of_allOutputs h₁ hP fun p hp => by
+          have h := ih p.1 p.2 hp.1
+          rwa [if_pos hp.2] at h
+
 /-! ### Simulation through a state abstraction -/
 
 /-- **Simulation through an abstraction of the state:** if every call of `impl₁` from the
diff --git a/TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Evaluator.lean b/TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Evaluator.lean
index 44dfcefd8..d62076975 100644
--- a/TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Evaluator.lean
+++ b/TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Evaluator.lean
@@ -50,22 +50,11 @@ theorem eq_blocks_divNat_modNat {q ℓ : ℕ} (w : Fin (q * ℓ) → Bool) (k :
     _ = FunFamily.blocks q ℓ w k.divNat k.modNat := FunFamily.blocks_symm_apply q ℓ _ k
 
 /-- Block `k` of the encoding of a `q`-tuple of `ℓ`-bit strings (positions `ℓk, …, ℓk + ℓ − 1`)
-is the encoding of the `k`-th component, read through `FunFamily.blocks`. -/
+is the encoding of the `k`-th component, read through `FunFamily.blocks` (the block window
+`FunFamily.ofFn_blocks`, read backwards). -/
 theorem drop_take_ofFn_blocks (q ℓ : ℕ) (w : Fin (q * ℓ) → Bool) {k : ℕ} (hk : k < q) :
     ((List.ofFn w).drop (ℓ * k)).take ℓ = List.ofFn (FunFamily.blocks q ℓ w ⟨k, hk⟩) := by
-  have hlen : ℓ * k + ℓ ≤ q * ℓ := by
-    have : (k + 1) * ℓ ≤ q * ℓ := Nat.mul_le_mul_right ℓ hk
-    nlinarith
-  refine List.ext_getElem ?_ fun j hj₁ hj₂ => ?_
-  · simp only [List.length_take, List.length_drop, List.length_ofFn]
-    omega
-  · simp only [List.length_take, List.length_drop, List.length_ofFn] at hj₁
-    simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]
-    have hℓ : 0 < ℓ := by omega
-    rw [eq_blocks_divNat_modNat w]
-    refine congrArg₂ _ (Fin.ext ?_) (Fin.ext ?_)
-    · rw [Fin.coe_divNat, Nat.mul_add_div hℓ, Nat.div_eq_of_lt (by omega), Nat.add_zero]
-    · rw [Fin.coe_modNat, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
+  rw [Nat.mul_comm ℓ k, FunFamily.ofFn_blocks]
 
 /-- The encoding of the `i`-bit prefix `prefixAt x i` (`i ≤ n`) is the first `i` bits of the
 encoding of `x`. -/
diff --git a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean
index 8b77f6bb7..fdbfde4c4 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean
@@ -63,16 +63,6 @@ theorem getD_ofFn_lt' {α : Type*} {c : ℕ} (t : Fin c → α) {i : ℕ} (hi :
   rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
   simp [hi]
 
-/-- The list of a tuple given by a function on `ℕ` is the map over `List.range`. -/
-theorem ofFn_eq_map_range {α : Type*} : ∀ {k : ℕ} (f : Fin k → α) (g : ℕ → α),
-    (∀ t : Fin k, f t = g t) → List.ofFn f = List.map g (List.range k)
-  | 0, _, _, _ => by simp
-  | k + 1, f, g, h => by
-    rw [List.ofFn_succ_last, List.range_succ, List.map_append, List.map_singleton,
-      ofFn_eq_map_range (fun t => f t.castSucc) g (fun t => by
-        show f t.castSucc = g t
-        rw [h, Fin.coe_castSucc]), h, Fin.val_last]
-
 /-- In a verifier-first execution of `2k` moves each party has received exactly `k` messages. -/
 theorem exec_vfirst_length (P' V : Strategy) (x zP zV rP rV : List Bool) :
     ∀ k, (exec P' V true x zP zV rP rV (2 * k)).1.length = k ∧
diff --git a/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines.lean b/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines.lean
index 7b0a16dab..6304cd020 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines.lean
@@ -915,15 +915,6 @@ theorem encodeMsgs_eq_flatMap (l : List (List Bool)) :
   | nil => rw [Strategy.encodeMsgs_nil]; rfl
   | cons m h ih => rw [Strategy.encodeMsgs_cons, List.flatMap_cons, ih, pairEncode_eq_append_nil]
 
-/-- `List.ofFn f` is the image of `range n` under any `ℕ`-indexed extension of `f`. -/
-theorem ofFn_eq_map_range {α : Type*} {n : ℕ} (f : Fin n → α) (F : ℕ → α)
-    (h : ∀ (k : ℕ) (hk : k < n), f ⟨k, hk⟩ = F k) : List.ofFn f = (List.range n).map F := by
-  apply List.ext_getElem
-  · simp
-  · intro i h1 h2
-    rw [List.getElem_ofFn, List.getElem_map, List.getElem_range]
-    exact h i (by simpa using h1)
-
 /-- The `i`-th second projection of an encoded history drops its first `i` messages. -/
 theorem iterate_pairSndD_encodeMsgs (hist : List (List Bool)) :
     ∀ i, pairSndD^[i] (Strategy.encodeMsgs hist) = Strategy.encodeMsgs (hist.drop i) := by
@@ -996,7 +987,7 @@ theorem histLen_poly : PolyTimeComputable fun M => List.replicate (histLen M) tr
 theorem encodeMsgs_ofFn_eq_flatMap {n : ℕ} (f : Fin n → List Bool) (F : ℕ → List Bool)
     (h : ∀ (k : ℕ) (hk : k < n), f ⟨k, hk⟩ = F k) :
     Strategy.encodeMsgs (List.ofFn f) = (List.range n).flatMap (fun i => pairEncode (F i) []) := by
-  rw [ofFn_eq_map_range f F h, encodeMsgs_eq_flatMap, List.flatMap_map]
+  rw [ofFn_eq_map_range f F fun t => h t t.isLt, encodeMsgs_eq_flatMap, List.flatMap_map]
 
 /-- With at least one edge, `edgeAt G e` is the edge of index `e mod |E|`. -/
 theorem edgeAt_eq_some_of_pos {n : ℕ} (G : Graph n) (hm : 0 < edgeCount G) (e : ℕ) :

## ===== TCSlib/Cryptography/Games/Forwarding.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Efficiency

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Forwarding handlers, calls read on lists, and hard-wired input components

Generic tools for the reductions built with T2 (`Games.exists_interactiveHandlerMachine`) that
were first proved for [PS10, Theorems 174.8 and 175.9].

* **Calls read on lists.** The call lemmas of `Games.InteractiveHandler` (`impl_of_ret`,
  `impl_of_query`, `finish_of_ret`) take the answer and the state as fixed-length vectors. A round
  function usually builds them as lists `u`, `v` of the right lengths; the `_padFin` forms take
  those lists and return `padFin _ u`, `padFin _ v`.
* **The forwarding handler** (`fwdHandler`): a reduction that runs its adversary once against its
  own oracles forwards every query unchanged to the outer oracle of the same index, with one
  outer call per inner query and an empty state; only the finalization differs. Its answers are
  the outer oracle's (`fwdHandler_impl`). Its round reads the round input through the published
  readers `InteractiveHandler.rS`, `rI`, `rX`, `rL` and `rAns`.
* **Hard-wiring a second input component** (`NUPPT.exists_withAdviceOn`): a reduction that
  receives advice as the second component of its input is a machine with that advice built in.

## Main definitions

* `Games.fwdHandler`: the forwarding handler with a given seed, adversary input and finalization.

## Main results

* `Games.InteractiveHandler.impl_of_ret_padFin`, `impl_of_query_padFin`, `finish_of_ret_padFin`:
  the call lemmas with list-valued answers, states and outputs.
* `Games.fwdHandler_impl`: the forwarding handler forwards.
* `Complexity.NUPPT.exists_withAdviceOn`: hard-wiring a second input component.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §2.1 (non-uniform machines), Theorems 174.8 and 175.9 (book pp. 174–175).
-/

namespace TCSlib.Cryptography.Games

open Complexity Turing

variable {k : ℕ}

/-! ### Calls read on lists -/

namespace InteractiveHandler

section Calls

variable {k' : ℕ} {din dout : Fin k → PolyExpr} {din' dout' : Fin k' → PolyExpr}
  (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
  (ω : Fin (H.seedLen.eval n) → Bool)

/-- **A call that returns at once, on lists:** if the first round on the inner query `x` to
oracle `i` in state `s` returns `⟨[true], u ‖ v⟩` with `|u| = dout i`, `|v| = stateLen`, the call
answers `padFin _ u` with the new state `padFin _ v`, asking nothing (`impl_of_ret`, with
`ofFn_padFin_of_length`). -/
theorem impl_of_ret_padFin (i : Fin k) (x : Fin ((din i).eval n) → Bool)
    (s : Fin (H.stateLen.eval n) → Bool) (u v : List Bool) (hu : u.length = (dout i).eval n)
    (hv : v.length = H.stateLen.eval n)
    (hrun : H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x) []) =
      pairEncode [true] (u ++ v)) :
    H.impl n z ω i x s = .pure (padFin _ u, padFin _ v) :=
  H.impl_of_ret n z ω x s _ _ (by rw [ofFn_padFin_of_length hu, ofFn_padFin_of_length hv, hrun])

/-- **A call with one outer query, on lists:** if the first round asks the outer query `x'` to
oracle `j`, and the second round, with the answer `y` in the outer log, returns
`⟨[true], u y ‖ v y⟩` with `|u y| = dout i`, `|v y| = stateLen`, then (with `perCall ≥ 1`) the
call is `query j x' (fun y => pure (padFin _ (u y), padFin _ (v y)))` (`impl_of_query`, with
`ofFn_padFin_of_length`). -/
theorem impl_of_query_padFin (i : Fin k) (x : Fin ((din i).eval n) → Bool)
    (s : Fin (H.stateLen.eval n) → Bool) (j : Fin k') (x' : Fin ((din' j).eval n) → Bool)
    (u v : (Fin ((dout' j).eval n) → Bool) → List Bool)
    (hu : ∀ y, (u y).length = (dout i).eval n) (hv : ∀ y, (v y).length = H.stateLen.eval n)
    (hpc : 1 ≤ H.perCall.eval n)
    (hrun₀ : H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x) []) =
      pairEncode [false] (pairEncode (List.replicate j true) (List.ofFn x')))
    (hrun₁ : ∀ y, H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x)
      (pairEncode (pairEncode (List.replicate j true) (pairEncode (List.ofFn x') (List.ofFn y)))
        [])) = pairEncode [true] (u y ++ v y)) :
    H.impl n z ω i x s = .query j x' fun y => .pure (padFin _ (u y), padFin _ (v y)) :=
  H.impl_of_query n z ω x s j x' _ _ hpc hrun₀ fun y => by
    rw [ofFn_padFin_of_length (hu y), ofFn_padFin_of_length (hv y), hrun₁]

/-- **A finalization that returns at once, on lists:** if its first round returns `⟨[true], b⟩`
with `|b| = outLen(n)`, the finalization is `pure (padFin _ b)`, asking nothing
(`finish_of_ret`, with `ofFn_padFin_of_length`). -/
theorem finish_of_ret_padFin (s : Fin (H.stateLen.eval n) → Bool) {d : ℕ} (a : Fin d → Bool)
    (b : List Bool) (hb : b.length = H.outLen.eval n)
    (hrun : H.finRun (finInput n z (List.ofFn ω) (List.ofFn s) (List.ofFn a) []) =
      pairEncode [true] b) :
    H.finish n z ω s a = .pure (padFin _ b) :=
  H.finish_of_ret n z ω s a _ (by rw [ofFn_padFin_of_length hb, hrun])

end Calls

end InteractiveHandler

/-! ### The forwarding handler -/

open InteractiveHandler in
/-- **One forwarding round.** With an empty outer log, ask the outer oracle `i` the query `x`;
with the outer answer `y` in the log, return `y` and keep the state. -/
private def fwdRun (w : List Bool) : List Bool :=
  if decide (rL w = []) then pairEncode [false] (pairEncode (rI w) (rX w))
  else pairEncode [true] (rAns w ++ rS w)

open InteractiveHandler in
/-- The forwarding round is polynomial-time. -/
private theorem polyTimeComputable_fwdRun : PolyTimeComputable fwdRun :=
  polyTimeComputable_ite (polyTimeComputable_isNil.comp polyTimeComputable_rL)
    ((polyTimeComputable_const [false]).pairEncode
      (polyTimeComputable_rI.pairEncode polyTimeComputable_rX))
    ((polyTimeComputable_const [true]).pairEncode
      (polyTimeComputable_rAns.append polyTimeComputable_rS))

/-- **The forwarding handler** for `k` bit-string oracles with lengths `din`, `dout`, inner and
outer alike: empty state, the seed of `seedLen(n)` bits, one outer call per inner query, which
forwards the query to the outer oracle of the same index and returns its answer; the adversary's
input `advIn`, and the finalization `finRun` with `outLen(n)`-bit output and at most `finCall(n)`
outer queries. -/
def fwdHandler (din dout : Fin k → PolyExpr) (seedLen : PolyExpr)
    (advIn : List Bool → List Bool) (advIn_poly : PolyTimeComputable advIn)
    (outLen finCall : PolyExpr) (finRun : List Bool → List Bool)
    (finRun_poly : PolyTimeComputable finRun) : InteractiveHandler k din dout k din dout where
  stateLen := .const 0
  seedLen := seedLen
  perCall := .const 1
  init _ := zeroBits _
  run := fwdRun
  poly := polyTimeComputable_fwdRun
  advIn := advIn
  advIn_poly := advIn_poly
  outLen := outLen
  finCall := finCall
  finRun := finRun
  finRun_poly := finRun_poly

attribute [simps (config := { isSimp := false }) stateLen seedLen perCall init advIn outLen finCall
  finRun] fwdHandler

section Forward

variable (din dout : Fin k → PolyExpr) (seedLen : PolyExpr) (advIn : List Bool → List Bool)
  (advIn_poly : PolyTimeComputable advIn) (outLen finCall : PolyExpr)
  (finRun : List Bool → List Bool) (finRun_poly : PolyTimeComputable finRun)

/-- **The forwarding handler forwards:** the inner query `x` to oracle `i` in state `s` is the
outer query `x` to oracle `i`, answered with the outer answer `y` and the state kept:
`H.impl n z ω i x s = query i x (fun y => pure (y, s))`.

**Proof sketch.** `InteractiveHandler.impl_of_query` with `perCall = 1`: the call's first round
has an empty outer log (`rL_input`), so it asks the query `⟨1^i, x⟩` (`rI_input`, `rX_input`);
its second round reads the answer `y` from the one-entry log (`rAns_input`) and returns `y ‖ s`
(`rS_input`). -/
theorem fwdHandler_impl (n : ℕ) (z : List Bool)
    (ω : Fin ((fwdHandler din dout seedLen advIn advIn_poly outLen finCall finRun
      finRun_poly).seedLen.eval n) → Bool) (i : Fin k) (x : Fin ((din i).eval n) → Bool)
    (s : Fin ((fwdHandler din dout seedLen advIn advIn_poly outLen finCall finRun
      finRun_poly).stateLen.eval n) → Bool) :
    (fwdHandler din dout seedLen advIn advIn_poly outLen finCall finRun finRun_poly).impl n z ω
        i x s = .query i x fun y => .pure (y, s) := by
  refine InteractiveHandler.impl_of_query _ n z ω x s i x (fun y => y) (fun _ => s)
    (by rw [fwdHandler_perCall, PolyExpr.eval_const]) ?_ fun y => ?_
  · show fwdRun _ = _
    rw [fwdRun, InteractiveHandler.rL_input, InteractiveHandler.rI_input,
      InteractiveHandler.rX_input, if_pos (decide_eq_true rfl)]
  · show fwdRun _ = _
    rw [fwdRun, InteractiveHandler.rL_input, InteractiveHandler.rAns_input,
      InteractiveHandler.rS_input, if_neg (fun h => pairEncode_ne_nil _ _ (of_decide_eq_true h))]

end Forward

/-! ### Hard-wiring a second input component -/

/-- **Hard-wiring a second input component** [PS10, §2.1, implicit]: for a machine `B` and a
polynomially bounded family `β n` there is a machine `B'` with the same coins (`h`) whose
computation on the input `x` is `B`'s on `⟨x, β n⟩`, for every codec and budget:
`B'.toCompOn codec n q x (coinsCongr h n r) = B.toCompOn codec n q ⟨x, β n⟩ r`.

**Proof sketch.** `B₁ := NUPPT.exists_comp B` with the re-pairing
`⟨⟨x, L⟩, β⟩ ↦ ⟨⟨x, β⟩, L⟩`, then `B' := NUPPT.exists_withAdvice B₁ β`; on `⟨x, L⟩` (the input
and the encoded log) `B'` runs `B` on `⟨⟨x, β n⟩, L⟩`. -/
theorem _root_.Complexity.NUPPT.exists_withAdviceOn (B : NUPPT) (β : ℕ → List Bool)
    (b : PolyExpr) (hβ : ∀ n, (β n).length ≤ b.eval n) :
    ∃ (B' : NUPPT) (h : B.coins = B'.coins), ∀ (n : ℕ) {ι α : Type} {spec : OracleSpec ι}
      (codec : MachineCodec spec α) (q : ℕ) (x : List Bool) (r : B.Coins n),
      B'.toCompOn codec n q x (NUPPT.coinsCongr h n r) =
        B.toCompOn codec n q (pairEncode x (β n)) r := by
  have hpre : PolyTimeComputable fun w : List Bool =>
      pairEncode (pairEncode (pairFstD (pairFstD w)) (pairSndD w)) (pairSndD (pairFstD w)) :=
    ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD).pairEncode
      polyTimeComputable_pairSndD).pairEncode
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD)
  obtain ⟨B₁, hc₁, -, -, hB₁⟩ := NUPPT.exists_comp B hpre polyTimeComputable_id
  obtain ⟨B', hc', hB'⟩ := NUPPT.exists_withAdvice B₁ β b hβ
  refine ⟨B', (hc'.trans hc₁).symm, fun n ι α spec codec q x r => ?_⟩
  rw [NUPPT.toCompOn_eq, NUPPT.toCompOn_eq]
  congr 1
  funext hist
  rw [NUPPT.runAt_coinsCongr, hB', hB₁, NUPPT.runAt_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, id_eq]

end TCSlib.Cryptography.Games

## ===== TCSlib/Cryptography/Games/Efficiency.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.BitCodec
import TCSlib.Cryptography.Games.Probability
import TCSlib.Cryptography.Games.Bridges.Machines
import TCSlib.Cryptography.Games.Efficiency.Strings
import TCSlib.Cryptography.Games.Efficiency.Replay
import TCSlib.Cryptography.Games.Efficiency.Handler
import TCSlib.Cryptography.Games.Efficiency.OracleBridge
import TCSlib.Cryptography.Games.Efficiency.Interactive
import TCSlib.Cryptography.Games.Efficiency.InteractiveSpec

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The efficiency of reductions

A reduction runs a machine adversary `A` and answers `A`'s queries with a polynomial-time
**handler**. Proved once, the targets below say that the result is again a machine, so the
hardness assumptions, which quantify over machines (`Complexity.NUPPT`), apply to it. The route is
`briefs/pass-shelat-ch5-8/design/S2b-efficiency.md`. The template is Frederick Dehmel's GGM
reduction machine (`Asymptotic/GGMReduction*.lean`), whose loop `GGMRed.stateLoopFun` is reused.

**Status: proved.** The definitions (T0) are final. The statements of T1, T2 and T4 and of the
companion `exists_toCompOn_of_toComp` were frozen at the issue of the fill brief
(`briefs/pass-shelat-ch5-8/fills/efficiency/`); the efficiency fill (`s2b-efficiency`) proved them,
with the helper modules below (namespace `TCSlib.Cryptography.Games.EffFill`).

## Contents

* `Games.Efficiency.Strings`: the string layer (log append, fixed-length decoding, the canonical
  decoder, the activation loop over `GGMRed.stateLoopFun`, the machine glue).
* `Games.Efficiency.Replay`: replaying a computation with a next-move function; cost scaling.
* `Games.Efficiency.Handler`: the machine of a non-interactive handler (T1).
* `Games.Efficiency.OracleBridge`: the translators to next-query machines (T4).
* `Games.Efficiency.Interactive`: the replay machine of an interactive handler (T2).
* `Games.Efficiency.InteractiveSpec`: its functional equation (T2).

## The shape of a reduction

A handler describes everything a reduction does around one run of the adversary. At parameter
`n` the reduction has an input `z` and a seed `ω` (its own coins). Every function of the handler
reads them from the **context** `⟨1^n, ⟨z, ω⟩⟩` (`seedIn`):
1. **the adversary's input** is a polynomial-time function of the context (`advIn`), for example
   a public key built from `z` and `ω`; the adversary runs as `A.toCompOn` on it;
2. **each query** of the adversary is answered from the handler's state, by the handler alone
   (`PolyHandler`) or with queries to the reduction's own oracles (`InteractiveHandler`);
3. **the reduction's output** is computed from the context, the final state and the adversary's
   output: by a polynomial-time function (`PolyHandler.out`), or by a last phase that may itself
   query the reduction's oracles, within its own budget (`InteractiveHandler.finish`).

## Fixed lengths

Every length is an explicit polynomial in the parameter `n`: queries and answers (`din i`,
`dout i`), the adversary's output (`dα`), the handler's state and seed, and, for an interactive
handler, the reduction's output. This bounds every history, which the guarded state loop needs.

## Scope

* **Covered:** a reduction that runs one adversary once, on an input computed from its own,
  answers the adversary's queries with or without its own oracles, and post-processes the final
  state and the adversary's output (with further oracle queries if it is interactive). T1 makes
  the machine's output exactly the finalized output; T2 makes the machine's computation exactly
  the simulation followed by the finalization, with the budgets added.
* **Adversaries without input** are adversaries with an input they ignore
  (`exists_toCompOn_of_toComp`).
* **Reductions to a pseudorandom function** reach `OracleEnsemble.Indist` through T4: an oracle
  machine against one bit-string oracle with a one-bit output is, on evaluations, a next-query
  machine of the ch. 2–4 layer (`NUPPT.toOracleAdversary`).
* **Non-uniform handlers** (for example one that runs a non-uniform distinguisher) receive their
  advice through the input `z`; it is hard-wired into the machine afterwards
  (`NUPPT.exists_withAdvice`, with `NUPPT.exists_comp` to re-pair the input).
* **Not covered:** reductions that rewind the adversary or run it more than once, and variable
  lengths.

## Main definitions

* `Games.seedIn n z ω`: the context `⟨1^n, ⟨z, ω⟩⟩`.
* `Games.PolyHandler k din dout`: a polynomial-time handler for `k` bit-string oracles, with its
  state and seed lengths, initial state, adversary input and finalization.
* `Games.PolyHandler.answer`, `Games.PolyHandler.impl`: its answers, and its semantics as a
  stateful `QueryImpl` that asks no oracle, at parameter `n`, reduction input `z` and seed `ω`;
  `PolyHandler.advInput` and `PolyHandler.result`: the adversary's input and the reduction's
  output.
* `Games.InteractiveHandler`, `InteractiveHandler.call`, `InteractiveHandler.impl`: a
  polynomial-time handler that may itself query outer bit-string oracles, up to `perCall(n)`
  times per inner query, and its semantics as a `QueryImpl` of the inner oracles by the outer ones;
  `InteractiveHandler.advInput` and `InteractiveHandler.finish`: the adversary's input and the
  finalization, with up to `finCall(n)` outer queries.
* `Games.InteractiveHandler.rU`, `rZ`, `rW`, `rS`, `rI`, `rX`, `rL`, `rCnt`, `rAns`: the fields of
  a round input `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩` (and the first component of the state, and
  the answer of the first entry of the outer log); `Games.InteractiveHandler.finA`: the adversary's
  output in a finalization input `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩`.

## Main results

* `Games.exists_handlerMachine` (T1, the fill's target): a reduction with a polynomial-time
  handler is a machine, whose output is exactly the finalized output of the simulation.
* `Games.exists_interactiveHandlerMachine` (T2, the fill's target): a reduction with an
  interactive handler is an oracle machine against the outer oracles, with budget
  `q(n) · perCall(n) + finCall(n)`, whose computation is exactly the simulation followed by the
  finalization. The reductions that forward or answer queries with their own oracle need it (the
  PRF MAC's distinguisher, hash-and-sign's forger, the CPA and CCA reductions).
* `Games.InteractiveHandler.rU_input`, …, `rCnt_input`, `rAns_input`: the readers of a round
  input on `InteractiveHandler.input`; `rU_finInput`, `rZ_finInput`, `rW_finInput`, `rS_finInput`,
  `rL_finInput`, `finA_finInput`: the readers of a finalization input on `finInput`;
  `Games.InteractiveHandler.impl_of_ret`, `Games.InteractiveHandler.impl_of_query`: a call whose
  first round returns, or asks one outer query and returns in its second round;
  `Games.InteractiveHandler.finish_of_ret`: a finalization whose first round returns.
* `Games.exists_toCompOn_of_toComp` (the fill's target): a machine without input is a machine
  with an input that it ignores, with the same coins.
* `Games.expect_toCompOn_outLen`: a machine's output length may be changed along an equality.
* `Games.exists_toOracleAdversary_of_bitCodec` (T4, the fill's target): an oracle machine
  against one `bitCodec` oracle with a one-bit output, on the empty input, evaluates as a
  next-query machine of the ch. 2–4 layer.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010:
  every reduction of ch. 5–8 (for example the proofs of Thms 135.4 and 168.2).
-/

namespace TCSlib.Cryptography.Games

open Complexity Turing

variable {k : ℕ}

/-- The bit-string oracles at parameter `n`, with polynomial lengths. -/
abbrev bitSpecAt (din dout : Fin k → PolyExpr) (n : ℕ) : OracleSpec (Fin k) :=
  bitSpec (fun i => (din i).eval n) (fun i => (dout i).eval n)

/-- The bit-string oracles at parameter `n` are `bitSpec` of the evaluated lengths:
`bitSpecAt din dout n = bitSpec (fun i => (din i).eval n) (fun i => (dout i).eval n)`. -/
theorem bitSpecAt_eq (din dout : Fin k → PolyExpr) (n : ℕ) :
    bitSpecAt din dout n = bitSpec (fun i => (din i).eval n) (fun i => (dout i).eval n) :=
  rfl

/-- The **context** of a reduction at parameter `n`, with the reduction's input `z` and its seed
`ω`: the string `⟨1^n, ⟨z, ω⟩⟩`. Every function of a handler reads it. -/
def seedIn (n : ℕ) (z ω : List Bool) : List Bool :=
  pairEncode (List.replicate n true) (pairEncode z ω)

/-- The context is `⟨1^n, ⟨z, ω⟩⟩`:
`seedIn n z ω = pairEncode (List.replicate n true) (pairEncode z ω)`. -/
theorem seedIn_eq (n : ℕ) (z ω : List Bool) :
    seedIn n z ω = pairEncode (List.replicate n true) (pairEncode z ω) :=
  rfl

/-- A **polynomial-time handler** for `k` bit-string oracles with query lengths `din` and answer
lengths `dout`: a reduction that runs the adversary once and answers its queries by itself. Its
three functions are polynomial-time, and each reads the context `⟨1^n, ⟨z, ω⟩⟩` (`seedIn`: the
parameter, the reduction's input `z` and its seed `ω`):
- `advIn` maps the context to the adversary's input;
- `run` answers one query: on `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨1^i, x⟩⟩⟩` (the context, the state `s`, and
  the query `x` to oracle `i`), it returns `⟨y, s'⟩`, the answer and the new state;
- `out` maps `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, a⟩⟩` (the context, the final state and the adversary's output)
  to the reduction's output. -/
structure PolyHandler (k : ℕ) (din dout : Fin k → PolyExpr) where
  /-- The length of the state. -/
  stateLen : PolyExpr
  /-- The length of the seed (the handler's own coins). -/
  seedLen : PolyExpr
  /-- The initial state at each parameter. -/
  init : ∀ n, Fin (stateLen.eval n) → Bool
  /-- The handler as a string function. -/
  run : List Bool → List Bool
  /-- It is polynomial-time computable. -/
  poly : PolyTimeComputable run
  /-- The adversary's input, as a function of the context `⟨1^n, ⟨z, ω⟩⟩` (for example a public
  key built from `z` and the seed). For an adversary without input it is ignored. -/
  advIn : List Bool → List Bool
  /-- The adversary's input is polynomial-time computable. -/
  advIn_poly : PolyTimeComputable advIn
  /-- The finalization: the reduction's output, as a function of `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, a⟩⟩` (the
  context, the final state `s` and the adversary's output `a`). -/
  out : List Bool → List Bool
  /-- The finalization is polynomial-time computable. -/
  out_poly : PolyTimeComputable out

namespace PolyHandler

variable {din dout : Fin k → PolyExpr}

/-- The handler's input string for the query `x` to oracle `i` in state `s`. -/
def input (n : ℕ) (z : List Bool) (ω : List Bool) (s : List Bool) (i : Fin k) (x : List Bool) :
    List Bool :=
  pairEncode (pairEncode (List.replicate n true) (pairEncode z ω))
    (pairEncode s (pairEncode (List.replicate i true) x))

/-- The handler's input string is `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨1^i, x⟩⟩⟩`. -/
theorem input_eq (n : ℕ) (z ω s : List Bool) (i : Fin k) (x : List Bool) :
    input n z ω s i x =
      pairEncode (pairEncode (List.replicate n true) (pairEncode z ω))
        (pairEncode s (pairEncode (List.replicate i true) x)) :=
  rfl

/-- The adversary's input at parameter `n`, for the reduction input `z` and the seed `ω`: `advIn`
of the context `⟨1^n, ⟨z, ω⟩⟩`. -/
def advInput (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) : List Bool :=
  H.advIn (seedIn n z (List.ofFn ω))

/-- The adversary's input is `advIn` of the context:
`H.advInput n z ω = H.advIn (seedIn n z (List.ofFn ω))`. -/
theorem advInput_eq (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) :
    H.advInput n z ω = H.advIn (seedIn n z (List.ofFn ω)) :=
  rfl

/-- The reduction's output at parameter `n`, for the reduction input `z` and the seed `ω`, when
the final state is `s` and the adversary's output is `a`: `out` of
`⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, a⟩⟩`. -/
def result (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) {d : ℕ}
    (a : Fin d → Bool) : List Bool :=
  H.out (pairEncode (seedIn n z (List.ofFn ω)) (pairEncode (List.ofFn s) (List.ofFn a)))

/-- The reduction's output is `out` of the context, the final state and the adversary's output:
`H.result n z ω s a = H.out (pairEncode (seedIn n z (List.ofFn ω))
(pairEncode (List.ofFn s) (List.ofFn a)))`. -/
theorem result_eq (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) {d : ℕ}
    (a : Fin d → Bool) :
    H.result n z ω s a =
      H.out (pairEncode (seedIn n z (List.ofFn ω)) (pairEncode (List.ofFn s) (List.ofFn a))) :=
  rfl

/-- The handler's answer and new state, decoded with fixed lengths. If `run`'s output is not a
pair, both are all-`false`; otherwise each component of the wrong length is replaced by
all-`false` independently (a total default; well-behaved handlers never produce one). An
interactive handler defaults jointly instead (`InteractiveHandler`). -/
def answer (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) (i : Fin k)
    (x : Fin ((din i).eval n) → Bool) :
    (Fin ((dout i).eval n) → Bool) × (Fin (H.stateLen.eval n) → Bool) :=
  match pairDecode (H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x))) with
  | some (yw, sw) =>
    ((decodeFin _ yw).getD (zeroBits _), (decodeFin _ sw).getD (zeroBits _))
  | none => (zeroBits _, zeroBits _)

section Answer

variable (H : PolyHandler k din dout) {n : ℕ} {z : List Bool} {ω : Fin (H.seedLen.eval n) → Bool}
  {s : Fin (H.stateLen.eval n) → Bool} {i : Fin k} {x : Fin ((din i).eval n) → Bool}

/-- If `run`'s output is not a pair, the answer and the new state are all-`false`. -/
theorem answer_of_pairDecode_eq_none
    (h : pairDecode (H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x))) = none) :
    H.answer n z ω s i x = (zeroBits _, zeroBits _) := by
  unfold answer
  rw [h]

/-- If `run`'s output is the pair `⟨yw, sw⟩`, the answer is `yw` and the new state `sw`, each
decoded with its fixed length and all-`false` if that length is wrong:
`H.answer n z ω s i x = ((decodeFin _ yw).getD (zeroBits _), (decodeFin _ sw).getD (zeroBits _))`.
-/
theorem answer_of_pairDecode_eq_some {yw sw : List Bool}
    (h : pairDecode (H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x))) =
      some (yw, sw)) :
    H.answer n z ω s i x =
      ((decodeFin _ yw).getD (zeroBits _), (decodeFin _ sw).getD (zeroBits _)) := by
  unfold answer
  rw [h]

/-- **A well-formed output:** if `run` returns `⟨y, s'⟩` with `y` and `s'` of the fixed lengths,
the answer is `y` and the new state `s'`. -/
theorem answer_of_run_eq {y : Fin ((dout i).eval n) → Bool} {s' : Fin (H.stateLen.eval n) → Bool}
    (h : H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x)) =
      pairEncode (List.ofFn y) (List.ofFn s')) :
    H.answer n z ω s i x = (y, s') := by
  have h' : pairDecode (H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x))) =
      some (List.ofFn y, List.ofFn s') := by
    rw [h, pairDecode_pairEncode]
  rw [answer_of_pairDecode_eq_some H h', decodeFin_ofFn, decodeFin_ofFn, Option.getD_some,
    Option.getD_some]

end Answer

/-- The handler as an implementation of the bit-string oracles at parameter `n`, for the
reduction input `z` and seed `ω`: it keeps its state and asks no oracle (the non-interactive
case). -/
def impl (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) :
    QueryImpl (bitSpecAt din dout n) (Fin (H.stateLen.eval n) → Bool) unifSpec :=
  fun i x s => .pure (H.answer n z ω s i x)

/-- The handler answers the query `x` to oracle `i` in state `s` with no coins and no queries:
`H.impl n z ω i x s = pure (H.answer n z ω s i x)`. -/
theorem impl_apply (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (i : Fin k) (x : Fin ((din i).eval n) → Bool)
    (s : Fin (H.stateLen.eval n) → Bool) :
    H.impl n z ω i x s = .pure (H.answer n z ω s i x) :=
  rfl

end PolyHandler

/-- **T1 (the efficiency fill's target; non-interactive handlers).** For a machine adversary `A`
with query budget `q` and `dα`-bit outputs against `k` bit-string oracles, and a polynomial-time
handler `H`, there is a machine `B` and, at every parameter, a bijection `φ` from (the handler's
seed, `A`'s coins) to `B`'s coins, with the following property. Run `A` on the input
`H.advInput n z ω`, answer its queries by `H` (input `z`, seed `ω`) from `H`'s initial state, and
let `a` be `A`'s output and `s` the final state. Then `B`'s output on input `z` with coins
`φ (ω, r)` is exactly the reduction's output `H.result n z ω s a`.

**Proof sketch** (the fill's; route note §"T1").
1. `B`'s raw function is the activation loop `EffFill.hRaw` (`GGMRed.stateLoopFun` through
   `EffFill.actLoop`) on the layout `⟨⟨⟨1^n, ⟨z, ω⟩⟩, ⟨α_A, s₀⟩⟩, r⟩`. The initial state
   `s₀ = H.init n` is part of the advice, beside `A`'s advice `α_A`, since `init` is an arbitrary
   function of `n`; so `B` is non-uniform even when `A` is uniform. The loop state is
   `⟨L, ⟨s, 1^t⟩⟩` (`A`'s encoded log, `H`'s state, the answered queries); the context
   `seedIn n z ω` and `A`'s input are recomputed in every round.
2. A round runs `A` on `⟨A's input, L⟩` (`NUPPT.polyTimeComputable_output`) and reads its move
   through the canonical decoder `EffFill.canonWord`, which returns the canonical word of
   `decodeBitMove`'s move on every word (`EffFill.canonWord_eq`, canonicity tested by re-encoding).
   It stops with `H.out ⟨ctx, ⟨s, a⟩⟩` on an output `a`, and with `H.out ⟨ctx, ⟨s, 0^{dα(n)}⟩⟩` on a
   query when `t = q(n)`. Otherwise it feeds the query to `H.run`, decodes the answer and the new
   state componentwise (`EffFill.fixLen`, `EffFill.ofFn_getD_decodeFin` and the `answer` lemmas),
   and appends the entry to `L` (`EffFill.encodeLog_append_single`).
3. At most `q(n) + 1` rounds, with states of polynomial length (all lengths are fixed), so the raw
   function is polynomial-time (`EffFill.hRaw_poly`, from `GGMRed.stateLoopFun_poly`).
4. The functional equation (`EffFill.hRaw_spec`): by induction on the remaining budget, the loop's
   state after `t` rounds encodes the simulation after `t` queries (`toCompOn_eq`, `buildComp`'s
   case lemmas, `simulate_query`, `PolyHandler.impl_apply`); `GGMRed.stateLoopFun_eval` reads off
   the output (`EffFill.runsTo_stop`), and `result_eq` and `seedIn_eq` identify it.
5. `B` is `NUPPT.ofPolyTime` of the raw function followed by `NUPPT.exists_split` with
   `p = H.seedLen` (`EffFill.exists_splitMachine`); `φ` appends the seed and the coins. -/
theorem exists_handlerMachine (A : NUPPT) (q : PolyExpr) (din dout : Fin k → PolyExpr)
    (dα : PolyExpr) (H : PolyHandler k din dout) :
    ∃ B : NUPPT, ∀ n : ℕ, ∃ φ : (Fin (H.seedLen.eval n) → Bool) × A.Coins n ≃ B.Coins n,
      ∀ (z : List Bool) (ω : Fin (H.seedLen.eval n) → Bool) (r : A.Coins n),
        ∃ (a : Fin (dα.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool),
          simulate (H.impl n z ω)
              (A.toCompOn
                (bitCodec (fun i => (din i).eval n) (fun i => (dout i).eval n) (dα.eval n))
                n (q.eval n) (H.advInput n z ω) r) (H.init n) = .pure (a, s) ∧
            B.runAt n z (φ (ω, r)) = H.result n z ω s a := by
  -- The machine: the handler loop of `EffFill.hRaw`, with `⟨A.advice n, s₀⟩` as advice and the
  -- seed passed as data.
  obtain ⟨B, hB⟩ := EffFill.exists_splitMachine A
    (EffFill.hRaw_poly A q dα din dout H.stateLen H.poly H.advIn_poly H.out_poly)
    (.add (.add (.mul (.const 2) A.adv) (.const 2)) H.stateLen)
    (fun n => pairEncode (A.advice n) (List.ofFn (H.init n))) (fun n => by
      rw [length_pairEncode, List.length_ofFn]
      simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
      have := A.advice_length n
      omega) H.seedLen
  refine ⟨B, fun n => ?_⟩
  obtain ⟨φ, hφ⟩ := hB n
  refine ⟨φ, fun z ω r => ?_⟩
  -- The handler's answers are `run`'s output decoded componentwise.
  have hans : ∀ (i : Fin k) (x : Fin ((din i).eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool),
      List.ofFn (H.answer n z ω s i x).1 = EffFill.fixLen ((dout i).eval n) (pairFstD (H.run
        (pairEncode (pairEncode (List.replicate n true) (pairEncode z (List.ofFn ω)))
          (pairEncode (List.ofFn s) (pairEncode (List.replicate i true) (List.ofFn x)))))) ∧
      List.ofFn (H.answer n z ω s i x).2 = EffFill.fixLen (H.stateLen.eval n) (pairSndD (H.run
        (pairEncode (pairEncode (List.replicate n true) (pairEncode z (List.ofFn ω)))
          (pairEncode (List.ofFn s) (pairEncode (List.replicate i true) (List.ofFn x)))))) := by
    intro i x s
    rw [← PolyHandler.input_eq]
    cases h : pairDecode (H.run (PolyHandler.input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x)))
      with
    | none =>
      rw [PolyHandler.answer_of_pairDecode_eq_none H h, pairFstD_of_pairDecode_eq_none h,
        pairSndD_of_pairDecode_eq_none h, EffFill.fixLen_nil, EffFill.fixLen_nil, ofFn_zeroBits,
        ofFn_zeroBits]
      exact ⟨rfl, rfl⟩
    | some p =>
      obtain ⟨yw, sw⟩ := p
      rw [PolyHandler.answer_of_pairDecode_eq_some H h, eq_pairEncode_of_pairDecode _ _ _ h,
        pairFstD_pairEncode, pairSndD_pairEncode, EffFill.ofFn_getD_decodeFin,
        EffFill.ofFn_getD_decodeFin]
      exact ⟨rfl, rfl⟩
  obtain ⟨a, s, hsim, hraw⟩ := EffFill.hRaw_spec A q dα din dout H.stateLen H.run H.advIn H.out
    (spec' := unifSpec) n z (List.ofFn ω) r (H.init n) (fun i x s => H.answer n z ω s i x) hans
  refine ⟨a, s, ?_, ?_⟩
  · have himpl : H.impl n z ω = fun i x s => OracleComp.pure (H.answer n z ω s i x) := by
      funext i x s
      exact H.impl_apply n z ω i x s
    rw [himpl, PolyHandler.advInput_eq, seedIn_eq]
    exact hsim
  · rw [hφ, hraw, PolyHandler.result_eq, seedIn_eq]

/-! ### Interactive handlers (T2) -/

variable {k' : ℕ}

/-- A **polynomial-time interactive handler** for `k` inner bit-string oracles that may itself
query `k'` outer bit-string oracles. Like `PolyHandler`, it computes the adversary's input from
the context `⟨1^n, ⟨z, ω⟩⟩` (`advIn`); it answers the adversary's queries (`run`), and computes the
reduction's output in a last phase (`finRun`), both with outer queries.

One inner query `x` to oracle `i` is answered with at most `perCall(n)` outer queries, in at most
`perCall(n) + 1` rounds of `run` (the last returns the answer; a further query after the budget
is spent is cut off with the default). In each round, `run` sees `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`, where `L` is
the outer log of the call so far (encoded as `bitCodec` encodes logs), and returns a move in
`bitCodec`'s format: a query `⟨[false], ⟨1^j, x'⟩⟩` to outer oracle `j`, or the answer
`⟨[true], y ‖ s'⟩` (the inner answer, then the new state). A malformed round output, including a
payload `y ‖ s'` of the wrong total length, gives the all-`false` answer and state together (a
joint default, unlike `PolyHandler.answer`, which defaults each component separately).

The finalization works the same way on `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩` (the final state, the
adversary's output and the outer log of the finalization so far), with at most `finCall(n)` outer
queries; it returns the reduction's `outLen(n)`-bit output as `⟨[true], b⟩`, the all-`false`
output on a malformed round output or on a further query after the budget is spent. (A return at
zero remaining budget is accepted: only a query then hits the timeout.) -/
structure InteractiveHandler (k : ℕ) (din dout : Fin k → PolyExpr) (k' : ℕ)
    (din' dout' : Fin k' → PolyExpr) where
  /-- The length of the state. -/
  stateLen : PolyExpr
  /-- The length of the seed. -/
  seedLen : PolyExpr
  /-- The bound on outer queries per inner query. -/
  perCall : PolyExpr
  /-- The initial state at each parameter. -/
  init : ∀ n, Fin (stateLen.eval n) → Bool
  /-- One round of the handler, as a string function. -/
  run : List Bool → List Bool
  /-- It is polynomial-time computable. -/
  poly : PolyTimeComputable run
  /-- The adversary's input, as a function of the context `⟨1^n, ⟨z, ω⟩⟩`. For an adversary
  without input it is ignored. -/
  advIn : List Bool → List Bool
  /-- The adversary's input is polynomial-time computable. -/
  advIn_poly : PolyTimeComputable advIn
  /-- The length of the reduction's output. -/
  outLen : PolyExpr
  /-- The bound on the outer queries of the finalization. -/
  finCall : PolyExpr
  /-- One round of the finalization, as a string function: on `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩` it
  returns an outer query `⟨[false], ⟨1^j, x'⟩⟩` or the reduction's output `⟨[true], b⟩`. -/
  finRun : List Bool → List Bool
  /-- The finalization's round is polynomial-time computable. -/
  finRun_poly : PolyTimeComputable finRun

namespace InteractiveHandler

variable {din dout : Fin k → PolyExpr} {din' dout' : Fin k' → PolyExpr}

/-- The handler's input string for one round. -/
def input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) : List Bool :=
  pairEncode (pairEncode (List.replicate n true) (pairEncode z ω))
    (pairEncode s (pairEncode (pairEncode (List.replicate i true) x) L))

/-- The handler's input string for one round is `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`. -/
theorem input_eq (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
    input n z ω s i x L =
      pairEncode (pairEncode (List.replicate n true) (pairEncode z ω))
        (pairEncode s (pairEncode (pairEncode (List.replicate i true) x) L)) :=
  rfl

/-! #### Readers of a round input

The fields of a round input `w = ⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`, read with `pairFstD` and
`pairSndD`, as a handler's round function reads them; on `input n z ω s i x L` they return the
field (`rU_input`, …), and each is polynomial-time (`polyTimeComputable_rU`, …). `rCnt` reads the
first component of the state, the call count `1^j` of the handlers that keep one there; `rAns`
reads the answer of the first entry of the outer log. -/

/-- The parameter `1^n` of a round input: `rU w = pairFstD (pairFstD w)`. -/
def rU (w : List Bool) : List Bool := pairFstD (pairFstD w)
/-- The reduction input `z` of a round input: `rZ w = pairFstD (pairSndD (pairFstD w))`. -/
def rZ (w : List Bool) : List Bool := pairFstD (pairSndD (pairFstD w))
/-- The seed `ω` of a round input: `rW w = pairSndD (pairSndD (pairFstD w))`. -/
def rW (w : List Bool) : List Bool := pairSndD (pairSndD (pairFstD w))
/-- The state `s` of a round input: `rS w = pairFstD (pairSndD w)`. -/
def rS (w : List Bool) : List Bool := pairFstD (pairSndD w)
/-- The oracle index `1^i` of a round input:
`rI w = pairFstD (pairFstD (pairSndD (pairSndD w)))`. -/
def rI (w : List Bool) : List Bool := pairFstD (pairFstD (pairSndD (pairSndD w)))
/-- The query `x` of a round input: `rX w = pairSndD (pairFstD (pairSndD (pairSndD w)))`. -/
def rX (w : List Bool) : List Bool := pairSndD (pairFstD (pairSndD (pairSndD w)))
/-- The outer log `L` of a round input: `rL w = pairSndD (pairSndD (pairSndD w))`. -/
def rL (w : List Bool) : List Bool := pairSndD (pairSndD (pairSndD w))
/-- The first component `pairFstD s` of the state of a round input:
`rCnt w = pairFstD (rS w)`. -/
def rCnt (w : List Bool) : List Bool := pairFstD (rS w)
/-- The outer answer `y` of the first entry `⟨1^j, ⟨x', y⟩⟩` of the outer log of a round input:
`rAns w = pairSndD (pairSndD (pairFstD (rL w)))`. -/
def rAns (w : List Bool) : List Bool := pairSndD (pairSndD (pairFstD (rL w)))

/-- `rAns w = pairSndD (pairSndD (pairFstD (rL w)))`. -/
theorem rAns_eq (w : List Bool) : rAns w = pairSndD (pairSndD (pairFstD (rL w))) := rfl

/-- `rU (input n z ω s i x L) = 1^n`. -/
theorem rU_input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
    rU (input n z ω s i x L) = List.replicate n true := by
  simp only [rU, input_eq, pairFstD_pairEncode]

/-- `rZ (input n z ω s i x L) = z`. -/
theorem rZ_input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
    rZ (input n z ω s i x L) = z := by
  simp only [rZ, input_eq, pairFstD_pairEncode, pairSndD_pairEncode]

/-- `rW (input n z ω s i x L) = ω`. -/
theorem rW_input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
    rW (input n z ω s i x L) = ω := by
  simp only [rW, input_eq, pairFstD_pairEncode, pairSndD_pairEncode]

/-- `rS (input n z ω s i x L) = s`. -/
theorem rS_input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
    rS (input n z ω s i x L) = s := by
  simp only [rS, input_eq, pairFstD_pairEncode, pairSndD_pairEncode]

/-- `rI (input n z ω s i x L) = 1^i`. -/
theorem rI_input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
    rI (input n z ω s i x L) = List.replicate i true := by
  simp only [rI, input_eq, pairFstD_pairEncode, pairSndD_pairEncode]

/-- `rX (input n z ω s i x L) = x`. -/
theorem rX_input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
    rX (input n z ω s i x L) = x := by
  simp only [rX, input_eq, pairFstD_pairEncode, pairSndD_pairEncode]

/-- `rL (input n z ω s i x L) = L`. -/
theorem rL_input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
    rL (input n z ω s i x L) = L := by
  simp only [rL, input_eq, pairSndD_pairEncode]

/-- `rCnt (input n z ω s i x L) = pairFstD s`. -/
theorem rCnt_input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
    rCnt (input n z ω s i x L) = pairFstD s := by
  rw [rCnt, rS_input]

/-- The answer of the first entry of the outer log:
`rAns (input n z ω s i x ⟨⟨1^j, ⟨x', y⟩⟩, t⟩) = y`. -/
theorem rAns_input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x : List Bool) (j : ℕ)
    (x' y t : List Bool) :
    rAns (input n z ω s i x
      (pairEncode (pairEncode (List.replicate j true) (pairEncode x' y)) t)) = y := by
  rw [rAns, rL_input, pairFstD_pairEncode, pairSndD_pairEncode, pairSndD_pairEncode]

/-- `rU` is polynomial-time: `PolyTimeComputable rU`. -/
theorem polyTimeComputable_rU : PolyTimeComputable rU :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD

/-- `rZ` is polynomial-time: `PolyTimeComputable rZ`. -/
theorem polyTimeComputable_rZ : PolyTimeComputable rZ :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD)

/-- `rW` is polynomial-time: `PolyTimeComputable rW`. -/
theorem polyTimeComputable_rW : PolyTimeComputable rW :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD)

/-- `rS` is polynomial-time: `PolyTimeComputable rS`. -/
theorem polyTimeComputable_rS : PolyTimeComputable rS :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD

/-- `rI` is polynomial-time: `PolyTimeComputable rI`. -/
theorem polyTimeComputable_rI : PolyTimeComputable rI :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))

/-- `rX` is polynomial-time: `PolyTimeComputable rX`. -/
theorem polyTimeComputable_rX : PolyTimeComputable rX :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))

/-- `rL` is polynomial-time: `PolyTimeComputable rL`. -/
theorem polyTimeComputable_rL : PolyTimeComputable rL :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-- `rCnt` is polynomial-time: `PolyTimeComputable rCnt`. -/
theorem polyTimeComputable_rCnt : PolyTimeComputable rCnt :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_rS

/-- `rAns` is polynomial-time: `PolyTimeComputable rAns`. -/
theorem polyTimeComputable_rAns : PolyTimeComputable rAns :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp
    (polyTimeComputable_pairFstD.comp polyTimeComputable_rL))

/-- The adversary's input at parameter `n`, for the reduction input `z` and the seed `ω`: `advIn`
of the context `⟨1^n, ⟨z, ω⟩⟩`. -/
def advInput (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) : List Bool :=
  H.advIn (seedIn n z (List.ofFn ω))

/-- The adversary's input is `advIn` of the context:
`H.advInput n z ω = H.advIn (seedIn n z (List.ofFn ω))`. -/
theorem advInput_eq (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) :
    H.advInput n z ω = H.advIn (seedIn n z (List.ofFn ω)) :=
  rfl

/-- **One call** of the handler on the inner query `x` to oracle `i` in state `s`: at most
`perCall(n)` outer queries, in at most `perCall(n) + 1` rounds of `run`. A malformed round output
is the all-`false` answer and state (`decodeBitMove`'s default), and so is a further query after
the budget is spent (a return at zero remaining budget is accepted). -/
def call (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) (i : Fin k)
    (x : Fin ((din i).eval n) → Bool) :
    OracleComp (bitSpecAt din' dout' n) (Fin ((dout i).eval n + H.stateLen.eval n) → Bool) :=
  buildComp (fun L => decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n) _
      (H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x)
        ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L))))
    (zeroBits _) (H.perCall.eval n) []

/-- One call is `buildComp` of the handler's rounds, from the empty outer log, with budget
`perCall(n)` and the all-`false` result on a query after it is spent: `H.call n z ω s i x =
buildComp (fun L => decodeBitMove _ _ _ (H.run (input … L))) (zeroBits _) (H.perCall.eval n) []`.
-/
theorem call_eq (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) (i : Fin k)
    (x : Fin ((din i).eval n) → Bool) :
    H.call n z ω s i x =
      buildComp (fun L => decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
          ((dout i).eval n + H.stateLen.eval n)
          (H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x)
            ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L))))
        (zeroBits _) (H.perCall.eval n) [] :=
  rfl

/-- The interactive handler as an implementation of the inner oracles by the outer ones, at
parameter `n`, reduction input `z` and seed `ω`: one `call` per inner query, its result split
into the answer and the new state. -/
def impl (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) :
    QueryImpl (bitSpecAt din dout n) (Fin (H.stateLen.eval n) → Bool) (bitSpecAt din' dout' n) :=
  fun i x s => (H.call n z ω s i x).bind fun w =>
    .pure (fun j => w (Fin.castAdd _ j), fun j => w (Fin.natAdd _ j))

/-- The inner query `x` to oracle `i` in state `s` is answered by one `call`, whose result is
split into the answer (its first `dout i` bits) and the new state (the rest):
`H.impl n z ω i x s = (H.call n z ω s i x).bind fun w =>
pure (fun j => w (Fin.castAdd _ j), fun j => w (Fin.natAdd _ j))`. -/
theorem impl_apply (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (i : Fin k) (x : Fin ((din i).eval n) → Bool)
    (s : Fin (H.stateLen.eval n) → Bool) :
    H.impl n z ω i x s =
      (H.call n z ω s i x).bind fun w =>
        .pure (fun j => w (Fin.castAdd _ j), fun j => w (Fin.natAdd _ j)) :=
  rfl

/-- **A call whose first round returns `y ‖ s'`** is answered `y` with the new state `s'`: if
`H.run (input n z ⟦ω⟧ ⟦s⟧ i ⟦x⟧ []) = ⟨[true], ⟦y⟧ ++ ⟦s'⟧⟩`, then
`H.impl n z ω i x s = pure (y, s')`.

**Proof sketch.** One call is `buildComp` of the rounds from the empty log (`call_eq`). The first
round decodes as the final output `y ‖ s'` (`decodeBitMove_ret`), which stops the computation at
every budget (`buildComp_zero_of_ret`, `buildComp_succ_of_ret`); the output splits back into `y`
and `s'` (`Fin.append_left`, `Fin.append_right`). -/
theorem impl_of_ret (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) {i : Fin k} (x : Fin ((din i).eval n) → Bool)
    (s : Fin (H.stateLen.eval n) → Bool) (y : Fin ((dout i).eval n) → Bool)
    (s' : Fin (H.stateLen.eval n) → Bool)
    (h : H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x) []) =
      pairEncode [true] (List.ofFn y ++ List.ofFn s')) :
    H.impl n z ω i x s = .pure (y, s') := by
  rw [impl_apply, call_eq]
  have hy : (fun j => Fin.append y s' (Fin.castAdd (H.stateLen.eval n) j)) = y :=
    funext fun j => Fin.append_left y s' j
  have hs : (fun j => Fin.append y s' (Fin.natAdd ((dout i).eval n) j)) = s' :=
    funext fun j => Fin.append_right y s' j
  generalize H.perCall.eval n = q
  cases q with
  | zero =>
    rw [buildComp_zero_of_ret (a := Fin.append y s') (by
      show decodeBitMove _ _ _ (H.run _) = _
      rw [MachineCodec.encodeLog_nil, h, ← List.ofFn_fin_append]
      exact decodeBitMove_ret _ _ _ _), OracleComp.pure_bind, hy, hs]
  | succ q =>
    rw [buildComp_succ_of_ret (a := Fin.append y s') (by
      show decodeBitMove _ _ _ (H.run _) = _
      rw [MachineCodec.encodeLog_nil, h, ← List.ofFn_fin_append]
      exact decodeBitMove_ret _ _ _ _), OracleComp.pure_bind, hy, hs]

/-- **A call with one outer query:** if the first round asks the outer query `x'` to oracle `j`,
and the second round, with the answer `y` in the outer log, returns `⟦y' y⟧ ‖ ⟦s' y⟧`, then (with
`perCall(n) ≥ 1`) `H.impl n z ω i x s = query j x' (fun y => pure (y' y, s' y))`.

**Proof sketch.** Unfold the call (`impl_apply`, `call_eq`) at the budget `perCall = p + 1`. The
first round decodes to the query (`decodeBitMove_query`), which `buildComp_succ_of_query` asks.
After the answer `y` the log encodes as in `h₁` (`bitCodec_encodeEntry`), the second round decodes
to the return of `y' y ‖ s' y` (`buildComp_of_ret`, `decodeBitMove_ret`), which `impl` splits back
(`Fin.append_left`, `Fin.append_right`). -/
theorem impl_of_query (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) {i : Fin k} (x : Fin ((din i).eval n) → Bool)
    (s : Fin (H.stateLen.eval n) → Bool) (j : Fin k') (x' : Fin ((din' j).eval n) → Bool)
    (y' : (Fin ((dout' j).eval n) → Bool) → Fin ((dout i).eval n) → Bool)
    (s' : (Fin ((dout' j).eval n) → Bool) → Fin (H.stateLen.eval n) → Bool)
    (hpc : 1 ≤ H.perCall.eval n)
    (h₀ : H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x) []) =
      pairEncode [false] (pairEncode (List.replicate j true) (List.ofFn x')))
    (h₁ : ∀ y, H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x)
      (pairEncode (pairEncode (List.replicate j true) (pairEncode (List.ofFn x') (List.ofFn y)))
        [])) = pairEncode [true] (List.ofFn (y' y) ++ List.ofFn (s' y))) :
    H.impl n z ω i x s = .query j x' fun y => .pure (y' y, s' y) := by
  obtain ⟨p, hp⟩ : ∃ p, H.perCall.eval n = p + 1 := ⟨H.perCall.eval n - 1, by omega⟩
  rw [impl_apply, call_eq, hp,
    buildComp_succ_of_query (i := j) (x := x') (by
      rw [MachineCodec.encodeLog_nil, h₀]
      exact decodeBitMove_query (fun j => (din' j).eval n) (fun j => (dout' j).eval n) _ j x'),
    OracleComp.query_bind]
  congr 1
  funext y
  have hlog : (bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog
      ([] ++ [⟨j, x', y⟩]) = pairEncode (pairEncode (List.replicate j true)
        (pairEncode (List.ofFn x') (List.ofFn y))) [] := by
    rw [List.nil_append, MachineCodec.encodeLog_cons, MachineCodec.encodeLog_nil,
      bitCodec_encodeEntry]
  rw [buildComp_of_ret (a := Fin.append (y' y) (s' y)) (by
      rw [hlog, h₁, ← List.ofFn_fin_append]
      exact decodeBitMove_ret _ _ _ _), OracleComp.pure_bind]
  congr 2
  · funext l
    exact Fin.append_left (y' y) (s' y) l
  · funext l
    exact Fin.append_right (y' y) (s' y) l

/-- The input string of one round of the finalization: `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩`, with the
final state `s`, the adversary's output `a` and the outer log `L` of the finalization so far. -/
def finInput (n : ℕ) (z ω s a L : List Bool) : List Bool :=
  pairEncode (seedIn n z ω) (pairEncode s (pairEncode a L))

/-- The input string of one round of the finalization is `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩`:
`finInput n z ω s a L = pairEncode (seedIn n z ω) (pairEncode s (pairEncode a L))`. -/
theorem finInput_eq (n : ℕ) (z ω s a L : List Bool) :
    finInput n z ω s a L = pairEncode (seedIn n z ω) (pairEncode s (pairEncode a L)) :=
  rfl

/-! #### Readers of a finalization input

A finalization input `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩` has the shape of a round input, so the
round-input readers `rU`, `rZ`, `rW`, `rS` and `rL` read its parameter, reduction input, seed,
state and outer log (`rU_finInput`, …); `finA` reads the adversary's output. -/

/-- `rU (finInput n z ω s a L) = 1^n`. -/
theorem rU_finInput (n : ℕ) (z ω s a L : List Bool) :
    rU (finInput n z ω s a L) = List.replicate n true := by
  simp only [rU, finInput_eq, seedIn_eq, pairFstD_pairEncode]

/-- `rZ (finInput n z ω s a L) = z`. -/
theorem rZ_finInput (n : ℕ) (z ω s a L : List Bool) : rZ (finInput n z ω s a L) = z := by
  simp only [rZ, finInput_eq, seedIn_eq, pairFstD_pairEncode, pairSndD_pairEncode]

/-- `rW (finInput n z ω s a L) = ω`. -/
theorem rW_finInput (n : ℕ) (z ω s a L : List Bool) : rW (finInput n z ω s a L) = ω := by
  simp only [rW, finInput_eq, seedIn_eq, pairFstD_pairEncode, pairSndD_pairEncode]

/-- `rS (finInput n z ω s a L) = s`. -/
theorem rS_finInput (n : ℕ) (z ω s a L : List Bool) : rS (finInput n z ω s a L) = s := by
  simp only [rS, finInput_eq, pairFstD_pairEncode, pairSndD_pairEncode]

/-- `rL (finInput n z ω s a L) = L`. -/
theorem rL_finInput (n : ℕ) (z ω s a L : List Bool) : rL (finInput n z ω s a L) = L := by
  simp only [rL, finInput_eq, pairSndD_pairEncode]

/-- The adversary's output `a` of a finalization input `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩`:
`finA w = pairFstD (pairSndD (pairSndD w))`. -/
def finA (w : List Bool) : List Bool := pairFstD (pairSndD (pairSndD w))

/-- `finA (finInput n z ω s a L) = a`. -/
theorem finA_finInput (n : ℕ) (z ω s a L : List Bool) : finA (finInput n z ω s a L) = a := by
  simp only [finA, finInput_eq, pairFstD_pairEncode, pairSndD_pairEncode]

/-- `finA` is polynomial-time: `PolyTimeComputable finA`. -/
theorem polyTimeComputable_finA : PolyTimeComputable finA :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-- **The finalization** in the final state `s`, after the adversary's output `a`: the
reduction's `outLen(n)`-bit output, computed with at most `finCall(n)` outer queries, in at most
`finCall(n) + 1` rounds of `finRun`. A malformed round output is the all-`false` output
(`decodeBitMove`'s default), and so is a further query after the budget is spent (a return at
zero remaining budget is accepted). -/
def finish (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) {d : ℕ}
    (a : Fin d → Bool) : OracleComp (bitSpecAt din' dout' n) (Fin (H.outLen.eval n) → Bool) :=
  buildComp (fun L => decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
      (H.outLen.eval n)
      (H.finRun (finInput n z (List.ofFn ω) (List.ofFn s) (List.ofFn a)
        ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L))))
    (zeroBits _) (H.finCall.eval n) []

/-- The finalization is `buildComp` of its rounds, from the empty outer log, with budget
`finCall(n)` and the all-`false` output on a query after it is spent: `H.finish n z ω s a =
buildComp (fun L => decodeBitMove _ _ _ (H.finRun (finInput … L))) (zeroBits _)
(H.finCall.eval n) []`. -/
theorem finish_eq (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) {d : ℕ}
    (a : Fin d → Bool) :
    H.finish n z ω s a =
      buildComp (fun L => decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
          (H.outLen.eval n)
          (H.finRun (finInput n z (List.ofFn ω) (List.ofFn s) (List.ofFn a)
            ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L))))
        (zeroBits _) (H.finCall.eval n) [] :=
  rfl

/-- **A finalization whose first round returns `b`** outputs `b`, asking nothing: if
`H.finRun (finInput n z ⟦ω⟧ ⟦s⟧ ⟦a⟧ []) = ⟨[true], ⟦b⟧⟩`, then `H.finish n z ω s a = pure b`
(`finish_eq`, `decodeBitMove_ret`, `buildComp_of_ret`). -/
theorem finish_of_ret (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) {d : ℕ}
    (a : Fin d → Bool) (b : Fin (H.outLen.eval n) → Bool)
    (h : H.finRun (finInput n z (List.ofFn ω) (List.ofFn s) (List.ofFn a) []) =
      pairEncode [true] (List.ofFn b)) :
    H.finish n z ω s a = .pure b := by
  rw [finish_eq]
  refine buildComp_of_ret ?_
  rw [MachineCodec.encodeLog_nil, h]
  exact decodeBitMove_ret _ _ _ _

end InteractiveHandler

/-- **T2 (the efficiency fill's target; interactive handlers).** For a machine adversary `A`
with query budget `q` and `dα`-bit outputs against `k` bit-string oracles, and an interactive
handler `H` answering them through `k'` outer oracles, there is an oracle machine `B` against the
outer oracles, with budget `q(n) · perCall(n) + finCall(n)`, and at every parameter a bijection
`φ` from (`H`'s seed, `A`'s coins) to `B`'s coins, with the following property. `B` on input `z`
with coins `φ (ω, r)` is, as an oracle computation, exactly the reduction: `A` run on the input
`H.advInput n z ω`, its queries answered by `H` (input `z`, seed `ω`) from `H`'s initial state,
followed by `H`'s finalization on the final state and `A`'s output.

**Proof sketch** (the fill's; route note §"T2", with the log replay).
1. `B`'s next-move function, on `⟨z, O⟩` (`O` its encoded outer log) with the seed `ω`, `A`'s coins
   `r` and the advice `⟨α_A, s₀⟩` (`s₀ = H.init n`, as in T1), is the activation loop
   `EffFill.iRaw`, which **replays** the whole reduction, one activation per round: a round of `A`
   opens a call (a query within budget) or the finalization (an output, or a query at budget `0`
   with the all-`false` output); a round of a call reruns `H.run` on
   `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`, its answer (or the joint default at budget `0`) appending
   the entry to `A`'s log; a round of the finalization reruns `H.finRun`. An outer query within
   budget is answered by the next entry of `O`; when `O` is exhausted it is `B`'s next move, its
   canonical word (`EffFill.canonWord_eq`), and so is the finalization's output.
2. At most `2 + finCall(n) + q(n)(perCall(n) + 2)` rounds, with states of polynomial length
   (the unreplayed part of `O` is bounded by the input), so the raw function is polynomial-time
   (`EffFill.iRaw_poly`, from `GGMRed.stateLoopFun_poly`).
3. The reduction tree makes at most `q(n) · perCall(n) + finCall(n)` queries
   (`toCompOn_costBoundedBy`, `buildComp_costBoundedBy`, `EffFill.costBoundedBy_mul`,
   `simulate_costBoundedBy`, `CostBoundedBy.bind`), so `B`'s budget never cuts the replay short.
4. The functional equation (`EffFill.iRaw_spec`): `B`'s next-move function replays the reduction
   tree from the empty log (`EffFill.ReplaysFrom`), by induction along the phases
   (`EffFill.adv_phase`, `call_phase`, `fin_phase`) on every branch, since the outer answers are
   arbitrary; then `EffFill.buildComp_of_replaysFrom` gives the equality of trees. The handler's
   calls and finalization are read through `impl_apply`, `call_eq`, `input_eq`, `finish_eq` and
   `finInput_eq`.
5. Coins and advice as in T1 (`EffFill.exists_splitMachine`). -/
theorem exists_interactiveHandlerMachine (A : NUPPT) (q : PolyExpr)
    (din dout : Fin k → PolyExpr) (din' dout' : Fin k' → PolyExpr) (dα : PolyExpr)
    (H : InteractiveHandler k din dout k' din' dout') :
    ∃ B : NUPPT, ∀ n : ℕ, ∃ φ : (Fin (H.seedLen.eval n) → Bool) × A.Coins n ≃ B.Coins n,
      ∀ (z : List Bool) (ω : Fin (H.seedLen.eval n) → Bool) (r : A.Coins n),
        (simulate (H.impl n z ω)
            (A.toCompOn (bitCodec (fun i => (din i).eval n) (fun i => (dout i).eval n) (dα.eval n))
              n (q.eval n) (H.advInput n z ω) r) (H.init n)).bind
            (fun res => H.finish n z ω res.2 res.1) =
          B.toCompOn
            (bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) (H.outLen.eval n))
            n (q.eval n * H.perCall.eval n + H.finCall.eval n) z (φ (ω, r)) := by
  -- The machine: the replay loop of `EffFill.iRaw`, with `⟨A.advice n, s₀⟩` as advice and the
  -- seed passed as data.
  obtain ⟨B, hB⟩ := EffFill.exists_splitMachine A
    (EffFill.iRaw_poly A q dα din dout din' H.stateLen H.perCall H.outLen H.finCall dout' H.poly
      H.advIn_poly H.finRun_poly)
    (.add (.add (.mul (.const 2) A.adv) (.const 2)) H.stateLen)
    (fun n => pairEncode (A.advice n) (List.ofFn (H.init n))) (fun n => by
      rw [length_pairEncode, List.length_ofFn]
      simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
      have := A.advice_length n
      omega) H.seedLen
  refine ⟨B, fun n => ?_⟩
  obtain ⟨φ, hφ⟩ := hB n
  refine ⟨φ, fun z ω r => ?_⟩
  -- The handler's calls and finalization are the raw ones of `EffFill`.
  have himpl : H.impl n z ω =
      EffFill.iImpl din dout din' dout' H.stateLen H.perCall H.run n z (List.ofFn ω) := by
    funext i x s
    rw [InteractiveHandler.impl_apply, EffFill.iImpl_apply, InteractiveHandler.call_eq,
      EffFill.iCall_eq]
    simp only [InteractiveHandler.input_eq]
  have hfin : ∀ (s : Fin (H.stateLen.eval n) → Bool) (a : Fin (dα.eval n) → Bool),
      H.finish n z ω s a =
        EffFill.iFinish din' dout' H.stateLen H.outLen H.finCall H.finRun n z (List.ofFn ω) s a :=
            by
    intro s a
    rw [InteractiveHandler.finish_eq, EffFill.iFinish_eq]
    simp only [InteractiveHandler.finInput_eq, seedIn_eq]
  rw [himpl, InteractiveHandler.advInput_eq, seedIn_eq]
  simp only [hfin]
  rw [← EffFill.iRaw_spec A q dα din dout din' dout' H.stateLen H.perCall H.outLen H.finCall H.run
    H.advIn H.finRun n z (List.ofFn ω) r (H.init n), NUPPT.toCompOn_eq, bitCodec_timeout]
  congr 1
  funext O
  rw [bitCodec_decodeMove, hφ, EffFill.iX_eq]

/-! ### Companions: adversaries without input, and the bridge to pseudorandom functions (T4) -/

/-- **A machine without input is a machine with an input that it ignores.** For every machine
`A` there is a machine `A'` with the same coins whose computation on any input `x` is `A`'s
computation, for every codec and budget, the coins related by a bijection `φ`. So T1 and T2,
stated for adversaries with input, cover adversaries without one.

**Proof sketch.** `A'` is `NUPPT.exists_comp` of `A` with `pre = pairSndD` and `post = id`, so
`A'.coins = A.coins` and `A'.runAtL n ⟨x, L⟩ r = A.runAtL n L r` (`pairSndD_pairEncode`). The
bijection `φ` is `NUPPT.coinsCongr`, which transports the coins along the equal coin polynomials
and keeps the coin string (`NUPPT.runAt_coinsCongr`); with `runAt_eq` the next-move functions of
`A'.toCompOn codec n q x (φ r)` and `A.toComp codec n q r` agree on every log, and
`toCompOn_eq`, `toComp_eq` conclude. -/
theorem exists_toCompOn_of_toComp (A : NUPPT) :
    ∃ A' : NUPPT, A'.coins = A.coins ∧ ∀ n : ℕ, ∃ φ : A.Coins n ≃ A'.Coins n,
      ∀ {ι α : Type} {spec : OracleSpec ι} (codec : MachineCodec spec α) (q : ℕ)
        (x : List Bool) (r : A.Coins n),
        A'.toCompOn codec n q x (φ r) = A.toComp codec n q r := by
  obtain ⟨A', hc, -, -, hA'⟩ :=
    NUPPT.exists_comp A polyTimeComputable_pairSndD polyTimeComputable_id
  refine ⟨A', hc, fun n => ⟨NUPPT.coinsCongr hc.symm n, ?_⟩⟩
  intro ι α spec codec q x r
  have hnext : (fun hist => codec.decodeMove
      (A'.runAt n (pairEncode x (codec.encodeLog hist)) (NUPPT.coinsCongr hc.symm n r))) =
      fun hist => codec.decodeMove (A.runAt n (codec.encodeLog hist) r) := by
    funext hist
    rw [NUPPT.runAt_coinsCongr, hA', pairSndD_pairEncode, id_eq, ← NUPPT.runAt_eq]
  rw [NUPPT.toCompOn_eq, NUPPT.toComp_eq, hnext]

/-- **Changing a machine's output length along `d = d'`** keeps the law of its output read as a
list: `𝔼[G (⟦p.1⟧, p.2)]` over the runs through `bitCodec ins outs d` and `bitCodec ins outs d'`
agree (substitute `d = d'`). -/
theorem expect_toCompOn_outLen {ins outs : Fin k → ℕ} {σ : Type}
    (O : QueryImpl (bitSpec ins outs) σ unifSpec) (A : NUPPT) (n q : ℕ) (x : List Bool)
    (r : A.Coins n) (s : σ) {d d' : ℕ} (hd : d = d') (G : List Bool × σ → ℝ) :
    ProbComp.expect (simulate O (A.toCompOn (bitCodec ins outs d) n q x r) s)
        (fun p => G (List.ofFn p.1, p.2)) =
      ProbComp.expect (simulate O (A.toCompOn (bitCodec ins outs d') n q x r) s)
        (fun p => G (List.ofFn p.1, p.2)) := by
  subst hd
  rfl

/-- **T4 (the efficiency fill's target; the bridge to pseudorandom functions).** An oracle
machine `B` against one `bitCodec` oracle (`ℓ₁(n)`-bit queries, `ℓ₂(n)`-bit answers) with a
one-bit output, run on the empty input, is a next-query machine of the ch. 2–4 layer: there is a
machine `B'` with the same coins whose oracle adversary `B'.toOracleAdversary`, run against any
`f`, returns the bit of `B`'s computation evaluated with `f`, the coins related by a bijection
`φ`. So `OracleEnsemble.Indist`, and with it `PRF`, applies to the machines of T2 with one outer
oracle and a one-bit output (through `oracleDist_apply` and `Bridge.eval_eq_evalFn`).

**Proof sketch.**
1. `B'` is `NUPPT.exists_comp` of `B` with two polynomial-time translators, so `B'.coins = B.coins`:
   - `EffFill.bridgePre` maps the history `⟨⟨x₁, y₁⟩, ⟨…, []⟩⟩` (`encodeHist`) to
     `⟨[], ⟨⟨[], ⟨x₁, y₁⟩⟩, ⟨…, []⟩⟩⟩`, `B`'s empty input and its log (`bitCodec_encodeEntry` with
     `1^0 = []`), by emitting one piece per suffix (`Complexity.polyTimeComputable_iterateEmit` with
     the step `pairSndD`; `EffFill.bridgePre_encodeHist`);
   - `EffFill.bridgePost` maps a canonical query word `⟨[false], ⟨[], x⟩⟩` (tested by re-encoding)
     to `⟨[false], x⟩`, the word `⟨[true], [true]⟩` to the verdict `[true, true]`, and every other
     word to `[true, false]`; then `decodeOracleMove` and `decodeBitMove` read corresponding moves
     (`EffFill.bridgePost_spec`, from `decodeBitMove_query`, `decodeBitMove_ret`,
     `decodeBitMove_of_not_canonical` and the case lemmas of `decodeOracleMove`), a payload of the
     wrong length included.
2. Both trees branch on corresponding moves, so by induction on the budget
   (`EffFill.eval_buildTree_bridge`: `buildTree`'s and `buildComp`'s case lemmas) their
   evaluations against `f` and `fun _ => f` agree (`QueryTree.eval_query`,
   `OracleComp.evalFn_query`); at the timeout the verdict `false` is bit `0` of `zeroBits 1`
   (`zeroBits_apply`). `toOracleAdversary_eq` and `toCompOn_eq` unfold the two sides.
3. `φ` is `NUPPT.coinsCongr`, as in `exists_toCompOn_of_toComp`. -/
theorem exists_toOracleAdversary_of_bitCodec (B : NUPPT) (ℓ₁ ℓ₂ : PolyExpr) :
    ∃ B' : NUPPT, B'.coins = B.coins ∧ ∀ n : ℕ, ∃ φ : B.Coins n ≃ B'.Coins n,
      ∀ (q : ℕ) (r : B.Coins n) (f : (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)),
        (B'.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) q (φ r)).eval f =
          (B.toCompOn (bitCodec (fun _ : Fin 1 => ℓ₁.eval n) (fun _ => ℓ₂.eval n) 1) n q []
              r).evalFn (fun _ => f) 0 := by
  obtain ⟨B', hc, -, -, hB'⟩ :=
    NUPPT.exists_comp B EffFill.bridgePre_poly EffFill.bridgePost_poly
  refine ⟨B', hc, fun n => ⟨NUPPT.coinsCongr hc.symm n, fun q r f => ?_⟩⟩
  have hnext : (fun hist : List ((Fin (ℓ₁.eval n) → Bool) × (Fin (ℓ₂.eval n) → Bool)) =>
      decodeOracleMove (ℓ₁.eval n)
      (B'.runAt n (encodeHist hist) (NUPPT.coinsCongr hc.symm n r))) =
      fun hist => decodeOracleMove (ℓ₁.eval n)
        (EffFill.bridgePost (B.runAt n (EffFill.bridgePre (encodeHist hist)) r)) := by
    funext hist
    rw [NUPPT.runAt_coinsCongr, hB', ← NUPPT.runAt_eq]
  have h := EffFill.eval_buildTree_bridge (ℓ₁.eval n) (ℓ₂.eval n) (fun y => B.runAt n y r) f q []
  rw [EffFill.logHist_eq, List.map_nil] at h
  rw [NUPPT.toOracleAdversary_eq, hnext, NUPPT.toCompOn_eq]
  simp only [bitCodec_decodeMove, bitCodec_timeout]
  exact h

end TCSlib.Cryptography.Games

## ===== TCSlib/Cryptography/Games/BitCodec.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Machines
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Games.Probability
import TCSlib.Complexity.ClassNP.PolyTimeBlockLoop
import Mathlib.Data.List.GetD

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bit-string oracles and their machine codec

The security games of [PS10] ch. 5–8 give machine adversaries a finite family of oracles on
fixed-length bit strings: a tagging oracle, a signing oracle, encryption and decryption oracles,
and so on. At parameter `n` oracle `i` takes `din i` bits and answers with `dout i` bits
(`bitSpec`). This file fixes the codec through which a next-move machine (`NUPPT.toComp`) plays
against such a family, and through which it returns a fixed-length output (`bitCodec`):
- **a query** to oracle `i` on `x` is the output `⟨[false], ⟨1^i, x⟩⟩`;
- **a final output** `a` is `⟨[true], a⟩`;
- **anything else**, a malformed or wrong-length string, decodes to the all-`false` output (the
  ch. 2–4 layer's convention D7: ill-formed outputs count as a fixed default);
- **a log entry** `(i, x, y)` is encoded as `⟨1^i, ⟨x, y⟩⟩`;
- **when the query budget runs out**, the output is the all-`false` string.

It is the shared codec of every prong's statements, and the T0 definitions of the efficiency fill
(`briefs/pass-shelat-ch5-8/fills/efficiency/`).

## Main definitions

* `Games.bitSpec din dout`: `k` oracles on fixed-length bit strings.
* `Games.decodeIdx`, `Games.decodeBitMove`: decoding of an oracle index and of a machine output as
  a move.
* `Games.encodeBitMove`: the canonical word of a move.
* `Games.bitCodec din dout dα`: the codec.
* `Games.castImpl`: an implementation of bit-string oracles read along equal length functions.
* `Games.cntRead`, `Games.ansRead`: the per-entry readings of an encoded log (one token for a
  nonempty log; the answer of the first entry).

## Main results

* `Games.decodeIdx_replicate`, `Games.decodeBitMove_query`, `Games.decodeBitMove_ret`: the
  well-formed encodings decode as intended.
* `Games.decodeIdx_eq_some_iff`, `Games.decodeBitMove_eq_query_iff`: only the canonical words
  decode as an index or a query.
* `Games.decodeBitMove_of_not_canonical`: every other word decodes to the all-`false` output.
* `Games.padFin_ofFn_zeroBits`, `Games.padFin_replicate_false`, `Games.padFin_nil`,
  `Games.decodeFin_nil_getD`: all-`false` strings and the empty answer read as `zeroBits`.
* `Games.padFin_append_split`: the two parts of a padded concatenation.
* `Games.simulate_castImpl_toCompOn`, `Games.expect_simulate_castImpl_toCompOn`: transport of a
  machine's run between two codecs with equal lengths.
* `Games.polyTimeComputable_cntRead`, `Games.polyTimeComputable_ansRead`: the per-entry readings
  are polynomial-time.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §3.8.1 (oracle machines) and Definitions 134.2, 136.2 and 168.1 (oracle adversaries).
-/

namespace TCSlib.Cryptography.Games

open Complexity Turing

variable {k : ℕ}

/-- **`k` oracles on fixed-length bit strings:** oracle `i` takes `din i` bits and answers with
`dout i` bits. -/
abbrev bitSpec (din dout : Fin k → ℕ) : OracleSpec (Fin k) :=
  ⟨fun i => Fin (din i) → Bool, fun i => Fin (dout i) → Bool⟩

/-- Oracle `i` of `bitSpec din dout` takes `din i`-bit strings. -/
theorem bitSpec_dom (din dout : Fin k → ℕ) (i : Fin k) :
    (bitSpec din dout).dom i = (Fin (din i) → Bool) :=
  rfl

/-- Oracle `i` of `bitSpec din dout` answers with `dout i`-bit strings. -/
theorem bitSpec_rng (din dout : Fin k → ℕ) (i : Fin k) :
    (bitSpec din dout).rng i = (Fin (dout i) → Bool) :=
  rfl

/-- Decoding of an oracle index written in unary: `1^i` with `i < k` is `i`; every other word
(one containing `false`, or of length at least `k`) is `none`. -/
def decodeIdx (k : ℕ) (iw : List Bool) : Option (Fin k) :=
  if h : iw.length < k ∧ iw = List.replicate iw.length true then some ⟨iw.length, h.1⟩ else none

/-- The unary code of an index decodes to it. -/
theorem decodeIdx_replicate (i : Fin k) : decodeIdx k (List.replicate i true) = some i := by
  unfold decodeIdx
  have h : (List.replicate (i : ℕ) true).length < k ∧
      List.replicate (i : ℕ) true =
        List.replicate (List.replicate (i : ℕ) true).length true := by
    simp
  rw [dif_pos h]
  exact congrArg some (Fin.ext (by simp))

/-- **Exactly the unary codes decode**, each to its index:
`decodeIdx k iw = some i ↔ iw = 1^i`. -/
theorem decodeIdx_eq_some_iff {iw : List Bool} {i : Fin k} :
    decodeIdx k iw = some i ↔ iw = List.replicate i true := by
  refine ⟨fun h => ?_, fun h => h ▸ decodeIdx_replicate i⟩
  unfold decodeIdx at h
  split_ifs at h with hw
  rw [Option.some.injEq] at h
  rw [← h]
  exact hw.2

/-- **Every other word is rejected:** `decodeIdx k iw = none` exactly when `iw` is the unary code
of no index below `k`. -/
theorem decodeIdx_eq_none_iff {iw : List Bool} :
    decodeIdx k iw = none ↔ ∀ i : Fin k, iw ≠ List.replicate i true := by
  constructor
  · intro h i hi
    rw [decodeIdx_eq_some_iff.2 hi] at h
    exact Option.some_ne_none i h
  · intro h
    cases hd : decodeIdx k iw with
    | none => rfl
    | some i => exact absurd (decodeIdx_eq_some_iff.1 hd) (h i)

/-- The default output: the all-`false` string. -/
def zeroBits (d : ℕ) : Fin d → Bool := fun _ => false

/-- Every bit of the default output is `false`: `zeroBits d j = false`. -/
theorem zeroBits_apply (d : ℕ) (j : Fin d) : zeroBits d j = false :=
  rfl

/-- The default output, written as a string, is `d` copies of `false`:
`List.ofFn (zeroBits d) = List.replicate d false`. -/
theorem ofFn_zeroBits (d : ℕ) : List.ofFn (zeroBits d) = List.replicate d false := by
  rw [show zeroBits d = fun _ => false from rfl, List.ofFn_const]

/-- The all-`false` answer, read at any width, is all-`false`:
`padFin d ⟦zeroBits m⟧ = zeroBits d`. -/
theorem padFin_ofFn_zeroBits (d m : ℕ) : padFin d (List.ofFn (zeroBits m)) = zeroBits d := by
  funext i
  rw [padFin_apply, ofFn_zeroBits, zeroBits_apply, List.getD_eq_getElem?_getD,
    List.getElem?_replicate]
  split <;> rfl

/-- An all-`false` list reads as the all-`false` vector at every width:
`padFin d (List.replicate m false) = zeroBits d`. -/
theorem padFin_replicate_false (d m : ℕ) : padFin d (List.replicate m false) = zeroBits d := by
  rw [← ofFn_zeroBits, padFin_ofFn_zeroBits]

/-- The empty list reads as the all-`false` vector: `padFin d [] = zeroBits d`. -/
theorem padFin_nil (d : ℕ) : padFin d [] = zeroBits d := padFin_replicate_false d 0

/-- **The two parts of a padded concatenation:** if `|u| = d₁`, the first `d₁` bits of
`padFin (d₁ + d₂) (u ++ v)` are `padFin d₁ u` and the rest `padFin d₂ v` (`padFin_apply`,
`List.getD_append`, `List.getD_append_right`). -/
theorem padFin_append_split {d₁ d₂ : ℕ} (u v : List Bool) (hu : u.length = d₁) :
    (fun j : Fin d₁ => padFin (d₁ + d₂) (u ++ v) (Fin.castAdd d₂ j)) = padFin d₁ u ∧
      (fun j : Fin d₂ => padFin (d₁ + d₂) (u ++ v) (Fin.natAdd d₁ j)) = padFin d₂ v := by
  refine ⟨funext fun j => ?_, funext fun j => ?_⟩
  · rw [padFin_apply, padFin_apply, Fin.coe_castAdd, List.getD_append _ _ _ _ (by omega)]
  · rw [padFin_apply, padFin_apply, Fin.coe_natAdd, List.getD_append_right _ _ _ _ (by omega)]
    congr 1
    omega

/-- An empty answer decodes to all-`false` at every length:
`(decodeFin ℓ []).getD (zeroBits ℓ) = zeroBits ℓ`. -/
theorem decodeFin_nil_getD (ℓ : ℕ) : (decodeFin ℓ []).getD (zeroBits ℓ) = zeroBits ℓ := by
  rw [decodeFin_eq]
  split
  · next h =>
    subst h
    funext i
    exact absurd i.isLt (Nat.not_lt_zero _)
  · rfl

/-- Decoding of a machine output as a move against `bitSpec din dout` with `dα`-bit outputs:
`⟨[false], ⟨1^i, x⟩⟩` with `i < k` and `|x| = din i` is the query `x` to oracle `i`;
`⟨[true], a⟩` with `|a| = dα` is the output `a`; anything else is the output `zeroBits dα`. -/
def decodeBitMove (din dout : Fin k → ℕ) (dα : ℕ) (w : List Bool) :
    Move (bitSpec din dout) (Fin dα → Bool) :=
  match pairDecode w with
  | some ([false], rest) =>
    match pairDecode rest with
    | some (iw, xw) =>
      match decodeIdx k iw with
      | some i =>
        match decodeFin (din i) xw with
        | some x => .query i x
        | none => .ret (zeroBits dα)
      | none => .ret (zeroBits dα)
    | none => .ret (zeroBits dα)
  | some ([true], aw) =>
    match decodeFin dα aw with
    | some a => .ret a
    | none => .ret (zeroBits dα)
  | _ => .ret (zeroBits dα)

/-- **The canonical word of a move:** the query `x` to oracle `i` is `⟨[false], ⟨1^i, x⟩⟩`, and
the output `a` is `⟨[true], a⟩`. `decodeBitMove` inverts it (`decodeBitMove_encodeBitMove`). -/
def encodeBitMove (din dout : Fin k → ℕ) (dα : ℕ) :
    Move (bitSpec din dout) (Fin dα → Bool) → List Bool
  | .query i x => pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x))
  | .ret a => pairEncode [true] (List.ofFn a)

/-- The canonical word of a query:
`encodeBitMove din dout dα (query i x) = ⟨[false], ⟨1^i, x⟩⟩`. -/
theorem encodeBitMove_query (din dout : Fin k → ℕ) (dα : ℕ) (i : Fin k)
    (x : Fin (din i) → Bool) :
    encodeBitMove din dout dα (.query i x) =
      pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x)) :=
  rfl

/-- The canonical word of an output: `encodeBitMove din dout dα (ret a) = ⟨[true], a⟩`. -/
theorem encodeBitMove_ret (din dout : Fin k → ℕ) (dα : ℕ) (a : Fin dα → Bool) :
    encodeBitMove din dout dα (.ret a) = pairEncode [true] (List.ofFn a) :=
  rfl

/-- **The codec of bit-string oracles:** moves decoded by `decodeBitMove`, a log entry
`(i, x, y)` encoded as `⟨1^i, ⟨x, y⟩⟩`, and the all-`false` output when the budget runs out. -/
def bitCodec (din dout : Fin k → ℕ) (dα : ℕ) :
    MachineCodec (bitSpec din dout) (Fin dα → Bool) where
  decodeMove := decodeBitMove din dout dα
  encodeEntry e :=
    pairEncode (List.replicate e.1 true) (pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2))
  timeout := zeroBits dα

/-- The codec decodes moves with `decodeBitMove`: `(bitCodec din dout dα).decodeMove w =
decodeBitMove din dout dα w`. -/
theorem bitCodec_decodeMove (din dout : Fin k → ℕ) (dα : ℕ) (w : List Bool) :
    (bitCodec din dout dα).decodeMove w = decodeBitMove din dout dα w :=
  rfl

/-- The codec encodes the log entry `(i, x, y)` as `⟨1^i, ⟨x, y⟩⟩`. -/
theorem bitCodec_encodeEntry (din dout : Fin k → ℕ) (dα : ℕ)
    (e : Σ i, (bitSpec din dout).dom i × (bitSpec din dout).rng i) :
    (bitCodec din dout dα).encodeEntry e =
      pairEncode (List.replicate e.1 true) (pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2)) :=
  rfl

/-- When the budget runs out, the codec's output is all-`false`:
`(bitCodec din dout dα).timeout = zeroBits dα`. -/
theorem bitCodec_timeout (din dout : Fin k → ℕ) (dα : ℕ) :
    (bitCodec din dout dα).timeout = zeroBits dα :=
  rfl

/-- The codec's log encoding does not depend on the output length: `bitCodec din dout dα` and
`bitCodec din dout dα'` encode every log alike. -/
theorem encodeLog_bitCodec (din dout : Fin k → ℕ) (dα dα' : ℕ) (h : QueryLog (bitSpec din dout)) :
    (bitCodec din dout dα).encodeLog h = (bitCodec din dout dα').encodeLog h := by
  induction h with
  | nil => rw [MachineCodec.encodeLog_nil, MachineCodec.encodeLog_nil]
  | cons e h ih =>
    rw [MachineCodec.encodeLog_cons, MachineCodec.encodeLog_cons, ih, bitCodec_encodeEntry,
      bitCodec_encodeEntry]

/-- A well-formed query decodes as the query. -/
theorem decodeBitMove_query (din dout : Fin k → ℕ) (dα : ℕ) (i : Fin k)
    (x : Fin (din i) → Bool) :
    decodeBitMove din dout dα
        (pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x))) = .query i x := by
  simp [decodeBitMove, pairDecode_pairEncode, decodeIdx_replicate, decodeFin_ofFn]

/-- A well-formed output decodes as the output. -/
theorem decodeBitMove_ret (din dout : Fin k → ℕ) (dα : ℕ) (a : Fin dα → Bool) :
    decodeBitMove din dout dα (pairEncode [true] (List.ofFn a)) = .ret a := by
  simp [decodeBitMove, pairDecode_pairEncode, decodeFin_ofFn]

/-- **Only the canonical query word decodes as a query:** `decodeBitMove din dout dα w` is the
query `x` to oracle `i` exactly when `w = ⟨[false], ⟨1^i, x⟩⟩` (the converse of
`decodeBitMove_query`).

**Proof sketch.** Follow `decodeBitMove`'s branches: only the branch in which the tag is `[false]`,
the rest parses as a pair, the index word decodes and the payload has the right length returns a
query. There, each successful parse determines its input: a parsed pair is the pairing of its parts
(`eq_pairEncode_of_pairDecode`), a decoded index word is `1^i` (`decodeIdx_eq_some_iff`), and a
decoded payload is `List.ofFn x`. -/
theorem decodeBitMove_eq_query_iff {din dout : Fin k → ℕ} {dα : ℕ} {w : List Bool} {i : Fin k}
    {x : Fin (din i) → Bool} :
    decodeBitMove din dout dα w = .query i x ↔
      w = pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x)) := by
  refine ⟨fun h => ?_, fun h => h ▸ decodeBitMove_query din dout dα i x⟩
  unfold decodeBitMove at h
  split at h
  · rename_i rest hw
    split at h
    · rename_i iw xw hr
      split at h
      · rename_i j hj
        split at h
        · rename_i x' hx
          cases h
          rw [eq_pairEncode_of_pairDecode _ _ _ hw, eq_pairEncode_of_pairDecode _ _ _ hr,
            decodeIdx_eq_some_iff.1 hj, (decodeFin_eq_some_iff _ _ _).1 hx]
        · cases h
      · cases h
    · cases h
  · split at h <;> cases h
  · cases h

/-- **The default:** a word that is neither a canonical query `⟨[false], ⟨1^i, x⟩⟩` nor a
canonical output `⟨[true], a⟩` decodes to the output `zeroBits dα`. With `decodeBitMove_query`
and `decodeBitMove_ret` this determines `decodeBitMove` on every word.

**Proof sketch.** Follow `decodeBitMove`'s branches. Every branch but two returns `zeroBits dα`.
In the query branch, the successful parses make `w` a canonical query word, as in
`decodeBitMove_eq_query_iff`, against `hq`; in the output branch, they make `w` a canonical output
word, against `hr`. -/
theorem decodeBitMove_of_not_canonical {din dout : Fin k → ℕ} {dα : ℕ} {w : List Bool}
    (hq : ∀ (i : Fin k) (x : Fin (din i) → Bool),
      w ≠ pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x)))
    (hr : ∀ a : Fin dα → Bool, w ≠ pairEncode [true] (List.ofFn a)) :
    decodeBitMove din dout dα w = .ret (zeroBits dα) := by
  unfold decodeBitMove
  split
  · rename_i rest hw
    split
    · rename_i iw xw hr'
      split
      · rename_i j hj
        split
        · rename_i x hx
          refine absurd ?_ (hq j x)
          rw [eq_pairEncode_of_pairDecode _ _ _ hw, eq_pairEncode_of_pairDecode _ _ _ hr',
            decodeIdx_eq_some_iff.1 hj, (decodeFin_eq_some_iff _ _ _).1 hx]
        · rfl
      · rfl
    · rfl
  · rename_i aw hw
    split
    · rename_i a ha
      refine absurd ?_ (hr a)
      rw [eq_pairEncode_of_pairDecode _ _ _ hw, (decodeFin_eq_some_iff _ _ _).1 ha]
    · rfl
  · rfl

/-- **Canonical words decode to their move:** `decodeBitMove (encodeBitMove m) = m`. -/
theorem decodeBitMove_encodeBitMove (din dout : Fin k → ℕ) (dα : ℕ)
    (m : Move (bitSpec din dout) (Fin dα → Bool)) :
    decodeBitMove din dout dα (encodeBitMove din dout dα m) = m := by
  cases m with
  | query i x => exact decodeBitMove_query din dout dα i x
  | ret a => exact decodeBitMove_ret din dout dα a

/-- Distinct moves have distinct canonical words. -/
theorem encodeBitMove_injective (din dout : Fin k → ℕ) (dα : ℕ) :
    Function.Injective (encodeBitMove din dout dα) := fun m m' h => by
  rw [← decodeBitMove_encodeBitMove din dout dα m, h, decodeBitMove_encodeBitMove]

/-! ### Readings of a log entry -/

/-- One token for a nonempty log and nothing for the empty one:
`cntRead v = if v = [] then [] else [true]`. Applied to the successive suffixes of an encoded log,
it counts the entries. -/
def cntRead (v : List Bool) : List Bool := if decide (v = []) then [] else [true]

/-- `cntRead v = if v = [] then [] else [true]`. -/
theorem cntRead_eq (v : List Bool) : cntRead v = if decide (v = []) then [] else [true] := rfl

/-- The token reading is polynomial-time: `PolyTimeComputable cntRead`. -/
theorem polyTimeComputable_cntRead : PolyTimeComputable cntRead :=
  polyTimeComputable_ite polyTimeComputable_isNil (polyTimeComputable_const [])
    (polyTimeComputable_const [true])

/-- The answer `y` of the first entry `⟨1^i, ⟨x, y⟩⟩` of an encoded log:
`ansRead v = pairSndD (pairSndD (pairFstD v))`. -/
def ansRead (v : List Bool) : List Bool := pairSndD (pairSndD (pairFstD v))

/-- `ansRead v = pairSndD (pairSndD (pairFstD v))`. -/
theorem ansRead_eq (v : List Bool) : ansRead v = pairSndD (pairSndD (pairFstD v)) := rfl

/-- The answer reading is polynomial-time: `PolyTimeComputable ansRead`. -/
theorem polyTimeComputable_ansRead : PolyTimeComputable ansRead :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD)

/-! ### Transport along equal lengths -/

section Transport

open ProbComp

variable {σ : Type}

/-- **An implementation read along length functions:** answer the query `x` to oracle `i` of
`bitSpec ins outs` by asking `O` the query `padFin (ins' i) ⟦x⟧` and reading its answer `y` as
`padFin (outs i) ⟦y⟧`. When `ins = ins'` and `outs = outs'` this is `O` itself
(`castImpl_self`). -/
def castImpl {ins ins' outs outs' : Fin k → ℕ} (O : QueryImpl (bitSpec ins' outs') σ unifSpec) :
    QueryImpl (bitSpec ins outs) σ unifSpec :=
  fun i x s => (O i (padFin (ins' i) (List.ofFn x)) s).bind fun p =>
    .pure (padFin (outs i) (List.ofFn p.1), p.2)

/-- The defining equation of `castImpl`: `castImpl O i x s =
(O i (padFin (ins' i) ⟦x⟧) s).bind fun p => pure (padFin (outs i) ⟦p.1⟧, p.2)`. -/
theorem castImpl_eq {ins ins' outs outs' : Fin k → ℕ}
    (O : QueryImpl (bitSpec ins' outs') σ unifSpec) (i : Fin k) (x : Fin (ins i) → Bool)
    (s : σ) :
    castImpl (ins := ins) (outs := outs) O i x s =
      (O i (padFin (ins' i) (List.ofFn x)) s).bind fun p =>
        .pure (padFin (outs i) (List.ofFn p.1), p.2) :=
  rfl

/-- Read along the same lengths, an implementation is unchanged: `castImpl O = O`. -/
theorem castImpl_self {ins outs : Fin k → ℕ} (O : QueryImpl (bitSpec ins outs) σ unifSpec) :
    castImpl (ins := ins) (outs := outs) O = O := by
  funext i x s
  rw [castImpl_eq, padFin_ofFn]
  simp only [padFin_ofFn]
  exact OracleComp.bind_pure _

/-- **Transport of a machine's run:** if `ins = ins'`, `outs = outs'` and `d = d'`, simulating
`castImpl O` on the run of `M` through `bitCodec ins outs d` gives, with outputs read as lists,
the simulation of `O` on the run of `M` through `bitCodec ins' outs' d'`.

**Proof sketch.** Substitute the equalities; then `castImpl O = O` (`castImpl_self`). -/
theorem simulate_castImpl_toCompOn {ins ins' outs outs' : Fin k → ℕ} {d d' : ℕ}
    (hi : ins = ins') (ho : outs = outs') (hd : d = d')
    (O : QueryImpl (bitSpec ins' outs') σ unifSpec) (M : NUPPT) (n q : ℕ) (x : List Bool)
    (r : M.Coins n) (s : σ) :
    (simulate (castImpl (ins := ins) (outs := outs) O)
        (M.toCompOn (bitCodec ins outs d) n q x r) s).bind
        (fun p => .pure (List.ofFn p.1, p.2)) =
      (simulate O (M.toCompOn (bitCodec ins' outs' d') n q x r) s).bind
        (fun p => .pure (List.ofFn p.1, p.2)) := by
  subst hi ho hd
  rw [castImpl_self]

/-- **Transport of a machine's run, in expectation:** for every function `G` of the output (read
as a list) and the final state, `simulate_castImpl_toCompOn` in the form
`𝔼[G (⟦p.1⟧, p.2)]` over the two simulations. -/
theorem expect_simulate_castImpl_toCompOn {ins ins' outs outs' : Fin k → ℕ} {d d' : ℕ}
    (hi : ins = ins') (ho : outs = outs') (hd : d = d')
    (O : QueryImpl (bitSpec ins' outs') σ unifSpec) (M : NUPPT) (n q : ℕ) (x : List Bool)
    (r : M.Coins n) (s : σ) (G : List Bool × σ → ℝ) :
    expect (simulate (castImpl (ins := ins) (outs := outs) O)
        (M.toCompOn (bitCodec ins outs d) n q x r) s) (fun p => G (List.ofFn p.1, p.2)) =
      expect (simulate O (M.toCompOn (bitCodec ins' outs' d') n q x r) s)
        (fun p => G (List.ofFn p.1, p.2)) := by
  have h := congrArg (fun c => expect c G) (simulate_castImpl_toCompOn hi ho hd O M n q x r s)
  simp only [expect_bind, expect_pure] at h
  exact h

end Transport

end TCSlib.Cryptography.Games

## ===== TCSlib/Cryptography/Games/Hopping.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Simulate
import TCSlib.Cryptography.Games.Advantage

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Game hopping

The steps of a game-based security proof, proved once:
- **the difference lemma**: two events that agree unless a "bad" event happens differ in
  probability by at most the probability of the bad event;
- **identical until bad**: two oracle implementations that give the same law to good successors
  until a flag in their state is raised, and never lower it, give simulations whose outputs differ
  in probability by at most the probability that the flag is raised;
- **a collision bound**: one fresh uniform sample lands in a list of at most `q` values fixed
  before it with probability at most `q / |T|`. The adaptive repeated-nonce event of
  [PS10, Thm 168.2] (later nonces hitting an earlier one) is a union of such steps; its lemma is
  scheduled with the statement phase.

The hybrid argument itself is `advantage_hybrid` (`TCSlib.Cryptography.Games.Advantage`).

## Main definitions

* `Games.OracleComp.AllOutputs P c` (in `TCSlib.Cryptography.Games.OracleComp`): every possible
  output of `c` satisfies `P`.

## Main results

* `ProbComp.prob_eq_one_of_allOutputs`, `ProbComp.expect_mono_of_allOutputs`,
  `ProbComp.expect_congr_of_allOutputs`: reasoning on the possible outputs only.
* `ProbComp.abs_prob_sub_le_of_agree`: the difference lemma [Sho04, §1.1, Lemma 1].
* `ProbComp.prob_mem_le`: the collision bound; `ProbComp.expect_sample_mem_le`, its form for a
  uniform sample and a fixed list.
* `ProbComp.expect_simulate_congr`: implementations with the same laws simulate alike.
* `ProbComp.prob_bad_le`: the per-query potential bound `Pr[bad] ≤ q · (size + q) · δ`.
* `Games.prob_eq_until_bad`, `Games.identical_until_bad`, `Games.identical_until_bad_init`: the
  code-based fundamental lemma [BR06], in semantic form, from a fixed or a sampled initial
  state; `Games.hagree_of_eq` recovers the syntactic hypothesis; `Games.expect_eq_until_bad`, the
  expectation form for functions of the output and the final state.
* `Games.expect_simulate_eager`: one-shot coins may be drawn in advance.

## References

* [BR06] M. Bellare, P. Rogaway, *The security of triple encryption and a framework for
  code-based game-playing proofs*, EUROCRYPT 2006; full version IACR ePrint 2004/331 (the
  fundamental lemma of game playing).
* [Sho04] V. Shoup, *Sequences of games: a tool for taming complexity in security proofs*,
  IACR ePrint 2004/332, revision of 18 January 2006 (https://www.shoup.net/papers/games.pdf),
  §1.1, Lemma 1 (the difference lemma).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Thm 168.2 (proof sketch: the bad events of the CPA analysis).
* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
-/

namespace TCSlib.Cryptography.Games

open Finset

variable {ι : Type} {α β σ : Type}

namespace ProbComp

/-- An event splits by a second event: `Pr[A] = Pr[A ∧ ¬F] + Pr[A ∧ F]`. -/
theorem prob_split (c : ProbComp α) (A F : α → Prop) :
    prob c A = prob c (fun a => A a ∧ ¬ F a) + prob c (fun a => A a ∧ F a) := by
  classical
  rw [prob_eq_expect, prob_eq_expect, prob_eq_expect, ← expect_add]
  congr 1
  funext a
  by_cases hA : A a <;> by_cases hF : F a <;> simp [hA, hF]

/-- If every possible output of `c` satisfies `P`, and `f ≤ g` at every output satisfying `P`,
then the expectation of `f` over `c` is at most that of `g`. -/
theorem expect_mono_of_allOutputs {c : ProbComp α} {P : α → Prop} (hc : c.AllOutputs P)
    {f g : α → ℝ} (h : ∀ a, P a → f a ≤ g a) : expect c f ≤ expect c g := by
  induction c with
  | pure a =>
    rw [expect_pure, expect_pure]
    exact h a (OracleComp.allOutputs_pure.1 hc)
  | query m x k ih =>
    simp only [expect_query]
    exact mul_le_mul_of_nonneg_left
      (sum_le_sum fun j _ => ih j (OracleComp.allOutputs_query.1 hc j)) (by positivity)

/-- Two functions that agree on every possible output have the same expectation: if
`c.AllOutputs P` and `f a = g a` whenever `P a`, then `𝔼_c f = 𝔼_c g` (`expect_mono_of_allOutputs`
both ways). -/
theorem expect_congr_of_allOutputs {c : ProbComp α} {P : α → Prop} (hc : c.AllOutputs P)
    {f g : α → ℝ} (h : ∀ a, P a → f a = g a) : expect c f = expect c g :=
  le_antisymm (expect_mono_of_allOutputs hc fun a ha => (h a ha).le)
    (expect_mono_of_allOutputs hc fun a ha => (h a ha).ge)

/-- An event holding at every possible output has probability one. -/
theorem prob_eq_one_of_allOutputs {c : ProbComp α} {p : α → Prop} (hc : c.AllOutputs p) :
    prob c p = 1 := by
  classical
  refine le_antisymm (prob_le_one c p) ?_
  rw [prob_eq_expect]
  calc (1 : ℝ) = expect c (fun _ => 1) := (expect_const c 1).symm
    _ ≤ _ := expect_mono_of_allOutputs hc fun a ha => by simp [ha]

/-- An event failing at every possible output has probability zero. -/
theorem prob_eq_zero_of_allOutputs {c : ProbComp α} {p : α → Prop}
    (hc : c.AllOutputs fun a => ¬ p a) : prob c p = 0 := by
  have h := prob_not c p
  rw [prob_eq_one_of_allOutputs hc] at h
  linarith

/-- **The difference lemma:** if the events `A` and `B` agree at every output where `F` fails,
their probabilities differ by at most the probability of `F`. [Sho04, §1.1, Lemma 1]

**Proof sketch.** Pointwise, the indicators of `A` and `B` differ by at most the indicator of
`F`; take expectations in both directions (linearity and monotonicity). -/
theorem abs_prob_sub_le_of_agree (c : ProbComp α) {A B F : α → Prop}
    (h : ∀ a, ¬ F a → (A a ↔ B a)) : |prob c A - prob c B| ≤ prob c F := by
  classical
  have key : ∀ (A B : α → Prop), (∀ a, ¬ F a → (A a ↔ B a)) →
      prob c A ≤ prob c B + prob c F := by
    intro A B hAB
    rw [prob_eq_expect, prob_eq_expect, prob_eq_expect, ← expect_add]
    exact expect_mono c fun a => by
      by_cases hF : F a
      · by_cases hA : A a <;> by_cases hB : B a <;> simp [hA, hB, hF]
      · have := hAB a hF
        by_cases hA : A a
        · simp [hA, this.1 hA, hF]
        · simp [hA, hF]; split_ifs <;> norm_num
  rw [abs_le]
  constructor
  · linarith [key B A fun a ha => (h a ha).symm]
  · linarith [key A B h]

/-- **The collision bound:** if every possible output list has length at most `q`, one fresh
uniform element of `T`, drawn after the list, lies in it with probability at most `q / |T|`.
A standard union-bound fact behind the bad events of [PS10, Thm 168.2]'s proof sketch; the
adaptive repeated-nonce event is a union of such steps.

**Proof sketch.** By total probability over the list, it suffices that a fixed list `L` of length
at most `q` is hit with probability `#{t ∈ L} / |T| ≤ q / |T|`; average over the possible lists
with `expect_mono_of_allOutputs`. -/
theorem prob_mem_le {T : Type} [Fintype T] [Nonempty T] [DecidableEq T] (c : ProbComp (List T))
    {q : ℕ} (hc : c.AllOutputs fun L => L.length ≤ q) :
    prob (c.bind fun L => (sample T).bind fun t => .pure (L, t)) (fun p => p.2 ∈ p.1) ≤
      q / Fintype.card T := by
  have hT : (0 : ℝ) < Fintype.card T := by exact_mod_cast Fintype.card_pos
  rw [prob_bind]
  calc expect c (fun L => prob ((sample T).bind fun t => .pure (L, t)) (fun p => p.2 ∈ p.1))
      ≤ expect c (fun _ => (q : ℝ) / Fintype.card T) := by
        refine expect_mono_of_allOutputs hc fun L hL => ?_
        rw [prob_bind, expect_sample]
        have hsum : ∑ t : T, prob (OracleComp.pure (L, t)) (fun p : List T × T => p.2 ∈ p.1) =
            (L.toFinset.card : ℝ) := by
          simp only [prob_pure, Finset.sum_boole]
          congr 2
          ext t
          simp
        rw [hsum, inv_mul_eq_div]
        refine div_le_div_of_nonneg_right ?_ hT.le
        exact_mod_cast (List.toFinset_card_le L).trans hL
    _ = q / Fintype.card T := expect_const c _

end ProbComp

/-- From a bad state, every possible final state of the simulation is bad, when the
implementation never leaves a bad state. -/
theorem simulate_allOutputs_bad {spec : OracleSpec ι} {impl : QueryImpl spec σ unifSpec}
    (bad : σ → Prop) (hstick : ∀ i x s, bad s → (impl i x s).AllOutputs fun ys => bad ys.2)
    (c : OracleComp spec α) {s : σ} (hs : bad s) :
    (simulate impl c s).AllOutputs fun r => bad r.2 := by
  induction c generalizing s with
  | pure a =>
    rw [simulate_pure, OracleComp.allOutputs_pure]
    exact hs
  | query i x k ih =>
    rw [simulate_query]
    exact OracleComp.AllOutputs.bind (hstick i x s hs) fun ys hys => ih ys.1 hys

/-- **Equal until bad, in expectation, for functions of the output and the final state.** Let two
implementations give, from every good state, the same law to good successors, and let each keep
bad states bad. Then from a good state, for every function `G` of the output and the final state,
`𝔼[G · 1_{good}]` is the same under both simulations:
`𝔼[fun r => if bad r.2 then 0 else G r] (simulate impl₀ c s) =
𝔼[fun r => if bad r.2 then 0 else G r] (simulate impl₁ c s)`.

**Proof sketch.** Induction on the computation. From a bad successor the continuation's value is
`0` on both sides (`simulate_allOutputs_bad`); from a good one the two values agree by induction;
so both expectations only see the values at good successors, which `hagree` equates. -/
theorem expect_eq_until_bad {spec : OracleSpec ι} {impl₀ impl₁ : QueryImpl spec σ unifSpec}
    (bad : σ → Prop) [DecidablePred bad]
    (hagree : ∀ i x s, ¬ bad s → ∀ g : spec.rng i × σ → ℝ,
      ProbComp.expect (impl₀ i x s) (fun ys => if bad ys.2 then 0 else g ys) =
        ProbComp.expect (impl₁ i x s) (fun ys => if bad ys.2 then 0 else g ys))
    (hstick₀ : ∀ i x s, bad s → (impl₀ i x s).AllOutputs fun ys => bad ys.2)
    (hstick₁ : ∀ i x s, bad s → (impl₁ i x s).AllOutputs fun ys => bad ys.2)
    (c : OracleComp spec α) (G : α × σ → ℝ) {s : σ} (hs : ¬ bad s) :
    ProbComp.expect (simulate impl₀ c s) (fun r => if bad r.2 then 0 else G r) =
      ProbComp.expect (simulate impl₁ c s) (fun r => if bad r.2 then 0 else G r) := by
  induction c generalizing s with
  | pure a => rw [simulate_pure, simulate_pure]
  | query i x k ih =>
    simp only [simulate_query, ProbComp.expect_bind]
    have hz : ∀ (impl : QueryImpl spec σ unifSpec),
        (∀ i x s, bad s → (impl i x s).AllOutputs fun ys => bad ys.2) →
        ∀ ys : spec.rng i × σ, bad ys.2 →
          ProbComp.expect (simulate impl (k ys.1) ys.2) (fun r => if bad r.2 then 0 else G r) =
            0 := by
      intro impl hst ys hb
      rw [ProbComp.expect_congr_of_allOutputs (simulate_allOutputs_bad bad hst _ hb)
        (g := fun _ => 0) fun r hr => if_pos hr, ProbComp.expect_const]
    have h0 : ∀ ys : spec.rng i × σ,
        ProbComp.expect (simulate impl₀ (k ys.1) ys.2) (fun r => if bad r.2 then 0 else G r) =
          if bad ys.2 then 0 else
            ProbComp.expect (simulate impl₁ (k ys.1) ys.2)
              (fun r => if bad r.2 then 0 else G r) := by
      intro ys
      by_cases hb : bad ys.2
      · rw [if_pos hb, hz impl₀ hstick₀ ys hb]
      · rw [if_neg hb, ih ys.1 hb]
    have h1 : ∀ ys : spec.rng i × σ,
        ProbComp.expect (simulate impl₁ (k ys.1) ys.2) (fun r => if bad r.2 then 0 else G r) =
          if bad ys.2 then 0 else
            ProbComp.expect (simulate impl₁ (k ys.1) ys.2)
              (fun r => if bad r.2 then 0 else G r) := by
      intro ys
      by_cases hb : bad ys.2
      · rw [if_pos hb, hz impl₁ hstick₁ ys hb]
      · rw [if_neg hb]
    rw [funext h0, hagree i x s hs, ← funext h1]

/-- **Equal until bad:** let two implementations give, from every good state, the same law to good
successors (they may differ arbitrarily on bad successors, including in the call that makes the
state bad), and let each keep bad states bad. Then, from a good state, the two simulations give
the same probability to "`Q` holds and the final state is good", and the same probability to "the
final state is bad".

**Proof sketch.** Both are expectations of functions that vanish on bad final states:
"`Q` and good" is `𝔼[if bad then 0 else 1_Q]`, and "bad" is `1 − 𝔼[if bad then 0 else 1]`
(`prob_not`). Both are equal under the two simulations by `expect_eq_until_bad`. -/
theorem prob_eq_until_bad {spec : OracleSpec ι} {impl₀ impl₁ : QueryImpl spec σ unifSpec}
    (bad : σ → Prop) [DecidablePred bad]
    (hagree : ∀ i x s, ¬ bad s → ∀ g : spec.rng i × σ → ℝ,
      ProbComp.expect (impl₀ i x s) (fun ys => if bad ys.2 then 0 else g ys) =
        ProbComp.expect (impl₁ i x s) (fun ys => if bad ys.2 then 0 else g ys))
    (hstick₀ : ∀ i x s, bad s → (impl₀ i x s).AllOutputs fun ys => bad ys.2)
    (hstick₁ : ∀ i x s, bad s → (impl₁ i x s).AllOutputs fun ys => bad ys.2)
    (c : OracleComp spec α) (Q : α → Prop) {s : σ} (hs : ¬ bad s) :
    ProbComp.prob (simulate impl₀ c s) (fun r => Q r.1 ∧ ¬ bad r.2) =
        ProbComp.prob (simulate impl₁ c s) (fun r => Q r.1 ∧ ¬ bad r.2) ∧
      ProbComp.prob (simulate impl₀ c s) (fun r => bad r.2) =
        ProbComp.prob (simulate impl₁ c s) (fun r => bad r.2) := by
  classical
  have hgood : ∀ c' : ProbComp (α × σ), ProbComp.prob c' (fun r => Q r.1 ∧ ¬ bad r.2) =
      ProbComp.expect c' (fun r => if bad r.2 then 0 else if Q r.1 then 1 else 0) := by
    intro c'
    rw [ProbComp.prob_eq_expect]
    congr 1
    funext r
    by_cases hb : bad r.2 <;> by_cases hq : Q r.1 <;> simp [hb, hq]
  have hbad : ∀ c' : ProbComp (α × σ), ProbComp.prob c' (fun r => bad r.2) =
      1 - ProbComp.expect c' (fun r => if bad r.2 then 0 else 1) := by
    intro c'
    have h := ProbComp.prob_not c' (fun r => bad r.2)
    have e : ProbComp.prob c' (fun r => ¬ bad r.2) =
        ProbComp.expect c' (fun r => if bad r.2 then 0 else 1) := by
      rw [ProbComp.prob_eq_expect]
      congr 1
      funext r
      by_cases hb : bad r.2 <;> simp [hb]
    linarith
  refine ⟨?_, ?_⟩
  · rw [hgood, hgood]
    exact expect_eq_until_bad bad hagree hstick₀ hstick₁ c _ hs
  · rw [hbad, hbad, expect_eq_until_bad bad hagree hstick₀ hstick₁ c (fun _ => 1) hs]

/-- **Identical until bad** (the code-based fundamental lemma): let two implementations of the
same oracles give, from every good state, the same law to good successors, and let each keep `bad`
once it holds (every possible new state of a bad state is bad). Then, from a good state, for any
computation `c` and event `p` on its output, the probabilities of `p` under the two simulations
differ by at most the probability that the first simulation ends in a bad state.
[BR06] (the fundamental lemma)

**Deviation:** [BR06] assumes the two games' code is syntactically identical up to `bad ← true`.
Here the hypothesis is semantic: from a good state the two implementations give the same law to
good successors, and may differ arbitrarily on bad ones, including in the call that raises the
flag. Stickiness is required; without it the bound fails.

**Proof sketch.**
1. *Sticky:* from a bad state, every possible final state of either simulation is bad
   (`simulate_allOutputs_bad`).
2. *Equal until bad:* `prob_eq_until_bad`.
3. Write each probability of `p` as "`p` and good" plus at most "bad", and conclude with the
   difference lemma's arithmetic. -/
theorem identical_until_bad {spec : OracleSpec ι}
    {impl₀ impl₁ : QueryImpl spec σ unifSpec} (bad : σ → Prop) [DecidablePred bad]
    (hagree : ∀ i x s, ¬ bad s → ∀ g : spec.rng i × σ → ℝ,
      ProbComp.expect (impl₀ i x s) (fun ys => if bad ys.2 then 0 else g ys) =
        ProbComp.expect (impl₁ i x s) (fun ys => if bad ys.2 then 0 else g ys))
    (hstick₀ : ∀ i x s, bad s → (impl₀ i x s).AllOutputs fun ys => bad ys.2)
    (hstick₁ : ∀ i x s, bad s → (impl₁ i x s).AllOutputs fun ys => bad ys.2)
    (c : OracleComp spec α) (p : α → Prop) {s : σ} (hs : ¬ bad s) :
    |ProbComp.prob (simulate impl₀ c s) (fun r => p r.1) -
        ProbComp.prob (simulate impl₁ c s) (fun r => p r.1)| ≤
      ProbComp.prob (simulate impl₀ c s) (fun r => bad r.2) := by
  obtain ⟨h1, h2⟩ := prob_eq_until_bad bad hagree hstick₀ hstick₁ c p hs
  rw [ProbComp.prob_split (simulate impl₀ c s) (fun r => p r.1) (fun r => bad r.2),
    ProbComp.prob_split (simulate impl₁ c s) (fun r => p r.1) (fun r => bad r.2), h1]
  have a0 := ProbComp.prob_nonneg (simulate impl₀ c s) (fun r => p r.1 ∧ bad r.2)
  have a1 := ProbComp.prob_nonneg (simulate impl₁ c s) (fun r => p r.1 ∧ bad r.2)
  have b0 := ProbComp.prob_mono (simulate impl₀ c s) (p := fun r => p r.1 ∧ bad r.2)
    (q := fun r => bad r.2) fun r h => h.2
  have b1 := ProbComp.prob_mono (simulate impl₁ c s) (p := fun r => p r.1 ∧ bad r.2)
    (q := fun r => bad r.2) fun r h => h.2
  rw [abs_le]
  constructor <;> linarith

/-- Equal implementations on good states give the same law to good successors: the hypothesis of
`identical_until_bad` in its syntactic form. -/
theorem hagree_of_eq {spec : OracleSpec ι} {impl₀ impl₁ : QueryImpl spec σ unifSpec}
    (bad : σ → Prop) [DecidablePred bad] (h : ∀ i x s, ¬ bad s → impl₀ i x s = impl₁ i x s) :
    ∀ i x s, ¬ bad s → ∀ g : spec.rng i × σ → ℝ,
      ProbComp.expect (impl₀ i x s) (fun ys => if bad ys.2 then 0 else g ys) =
        ProbComp.expect (impl₁ i x s) (fun ys => if bad ys.2 then 0 else g ys) :=
  fun i x s hs _ => by rw [h i x s hs]

/-- **Identical until bad, from a sampled initial state:** if every possible initial state is
good, the bound of `identical_until_bad` holds for the games that first sample the state.

**Proof sketch.** Total probability over the initial state, the pointwise bound at every possible
(good) initial state (`identical_until_bad`), and monotonicity and linearity of expectation. -/
theorem identical_until_bad_init {spec : OracleSpec ι}
    {impl₀ impl₁ : QueryImpl spec σ unifSpec} (bad : σ → Prop) [DecidablePred bad]
    (hagree : ∀ i x s, ¬ bad s → ∀ g : spec.rng i × σ → ℝ,
      ProbComp.expect (impl₀ i x s) (fun ys => if bad ys.2 then 0 else g ys) =
        ProbComp.expect (impl₁ i x s) (fun ys => if bad ys.2 then 0 else g ys))
    (hstick₀ : ∀ i x s, bad s → (impl₀ i x s).AllOutputs fun ys => bad ys.2)
    (hstick₁ : ∀ i x s, bad s → (impl₁ i x s).AllOutputs fun ys => bad ys.2)
    (c : OracleComp spec α) (p : α → Prop) (init : ProbComp σ)
    (hinit : init.AllOutputs fun s => ¬ bad s) :
    |ProbComp.prob (init.bind fun s => simulate impl₀ c s) (fun r => p r.1) -
        ProbComp.prob (init.bind fun s => simulate impl₁ c s) (fun r => p r.1)| ≤
      ProbComp.prob (init.bind fun s => simulate impl₀ c s) (fun r => bad r.2) := by
  rw [ProbComp.prob_bind, ProbComp.prob_bind, ProbComp.prob_bind]
  have key := fun s (hs : ¬ bad s) =>
    abs_le.1 (identical_until_bad bad hagree hstick₀ hstick₁ c p hs)
  have u := ProbComp.expect_mono_of_allOutputs hinit
    (f := fun s => ProbComp.prob (simulate impl₀ c s) (fun r => p r.1))
    (g := fun s => ProbComp.prob (simulate impl₁ c s) (fun r => p r.1) +
      ProbComp.prob (simulate impl₀ c s) (fun r => bad r.2))
    (fun s hs => by linarith [(key s hs).2])
  have v := ProbComp.expect_mono_of_allOutputs hinit
    (f := fun s => ProbComp.prob (simulate impl₁ c s) (fun r => p r.1))
    (g := fun s => ProbComp.prob (simulate impl₀ c s) (fun r => p r.1) +
      ProbComp.prob (simulate impl₀ c s) (fun r => bad r.2))
    (fun s hs => by linarith [(key s hs).1])
  rw [ProbComp.expect_add] at u v
  rw [abs_le]
  constructor <;> linarith

namespace ProbComp

/-! ### Simulation congruence and a bad-event potential -/

/-- **Implementations with the same laws simulate alike:** if every call of `impl₀` and `impl₁`
has the same expectation of every function `g` of the answer and the new state, the simulations
of every computation have the same expectation of every function `G` of the output and the final
state: `𝔼[G] (simulate impl₀ c s) = 𝔼[G] (simulate impl₁ c s)`.

**Proof sketch.** Induction on `c`; at a query, both sides are the expectation over the call of the
continuation's expectation (`simulate_query`, `expect_bind`), equal by induction and the
hypothesis. -/
theorem expect_simulate_congr {ι : Type} {spec : OracleSpec ι} {σ α : Type}
    (impl₀ impl₁ : QueryImpl spec σ unifSpec)
    (h : ∀ i x s (g : spec.rng i × σ → ℝ), expect (impl₀ i x s) g = expect (impl₁ i x s) g)
    (c : OracleComp spec α) (s : σ) (G : α × σ → ℝ) :
    expect (simulate impl₀ c s) G = expect (simulate impl₁ c s) G := by
  induction c generalizing s with
  | pure a => rw [simulate_pure, simulate_pure]
  | query i x k ih =>
    rw [simulate_query, simulate_query, expect_bind, expect_bind, h]
    exact congrArg _ (funext fun p => ih p.1 p.2)

/-- **A bad event raised a little at each query:** if from a good state each query raises `bad`
with probability at most `(sz s + 1) · δ` and grows the size `sz` by at most one, then from a good
state `s` a computation making at most `m` queries ends in a bad state with probability at most
`m · (sz s + m) · δ`: `Pr[bad (simulate impl c s).2] ≤ m · (sz s + m) · δ`.

**Proof sketch.** Induction on the computation. At a query, a bad successor contributes at most
its probability; a good successor `s'` has `sz s' ≤ sz s + 1` and, by induction, contributes at
most `(m - 1) · (sz s + m) · δ`. Add `(sz s + 1) · δ ≤ (sz s + m) · δ`. -/
theorem prob_bad_le {ι : Type} {spec : OracleSpec ι} {σ : Type} {impl : QueryImpl spec σ unifSpec}
    (bad : σ → Prop) [DecidablePred bad]
    (sz : σ → ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hstep : ∀ i x s, ¬ bad s → prob (impl i x s) (fun ys => bad ys.2) ≤ (sz s + 1) * δ)
    (hgrow : ∀ i x s, (impl i x s).AllOutputs fun ys => sz ys.2 ≤ sz s + 1)
    {α : Type} (c : OracleComp spec α) (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m) (s : σ)
    (hs : ¬ bad s) :
    prob (simulate impl c s) (fun r => bad r.2) ≤ m * (sz s + m) * δ := by
  induction c generalizing m s with
  | pure a =>
    rw [simulate_pure, prob_pure, if_neg hs]
    exact mul_nonneg (by positivity) hδ
  | query i x k ih =>
    obtain ⟨hm, hk⟩ := (OracleComp.costBoundedBy_query _ _ _ _ _).1 hc
    have hm1 : 1 ≤ m := hm
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hk' : ∀ y, (k y).CostBoundedBy (fun _ => 1) m' := fun y => by
      simpa using hk y
    have hm0 : (0 : ℝ) ≤ m' := Nat.cast_nonneg m'
    set K : ℝ := m' * (sz s + (m' + 1)) * δ with hK
    have hK0 : 0 ≤ K := mul_nonneg (by positivity) hδ
    rw [simulate_query, prob_bind]
    calc expect (impl i x s) (fun ys => prob (simulate impl (k ys.1) ys.2) (fun r => bad r.2))
        ≤ expect (impl i x s) (fun ys => (if bad ys.2 then (1 : ℝ) else 0) + K) := by
          refine expect_mono_of_allOutputs (hgrow i x s) fun ys hys => ?_
          by_cases hb : bad ys.2
          · rw [if_pos hb]
            have h1 := prob_le_one (simulate impl (k ys.1) ys.2) (fun r => bad r.2)
            linarith
          · rw [if_neg hb, zero_add]
            refine (ih ys.1 m' (hk' ys.1) ys.2 hb).trans ?_
            have hys' : (sz ys.2 : ℝ) ≤ sz s + 1 := by exact_mod_cast hys
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hm0) hδ
      _ = prob (impl i x s) (fun ys => bad ys.2) + K := by
          rw [expect_add (impl i x s) (fun ys => if bad ys.2 then (1 : ℝ) else 0) (fun _ => K),
            expect_const, prob_eq_expect]
      _ ≤ ((m' + 1 : ℕ) : ℝ) * (sz s + ((m' + 1 : ℕ) : ℝ)) * δ := by
          have h3 := hstep i x s hs
          have h4 : ((sz s : ℝ) + 1) * δ ≤ (sz s + (m' + 1)) * δ :=
            mul_le_mul_of_nonneg_right (by linarith) hδ
          have e : ((m' : ℝ) + 1) * (sz s + (m' + 1)) * δ = K + (sz s + (m' + 1)) * δ := by
            rw [hK]; ring
          push_cast
          linarith

/-- **Hitting a list with a uniform sample:** a uniform element of `T` lies in a list `L` with
probability at most `|L| / |T|`: `𝔼_{t ← T} [t ∈ L] ≤ |L| / |T|` (`prob_mem_le` for a fixed
list). -/
theorem expect_sample_mem_le {T : Type} [Fintype T] [Nonempty T] [DecidableEq T] (L : List T) :
    expect (sample T) (fun t => if t ∈ L then (1 : ℝ) else 0) ≤ L.length / Fintype.card T := by
  have h := prob_mem_le (OracleComp.pure L : ProbComp (List T)) (q := L.length)
    (OracleComp.allOutputs_pure.2 le_rfl)
  rw [prob_bind, expect_pure, prob_bind] at h
  refine Eq.trans_le ?_ h
  refine congrArg _ (funext fun t => ?_)
  rw [prob_pure]

end ProbComp

/-! ### One-shot coins drawn in advance -/

section Eager

variable {spec : OracleSpec ι} {T : Type} [Fintype T] [Nonempty T]

/-- From a used state, an implementation that agrees with `O` there simulates like `O`. -/
private theorem simulate_eq_of_used (O O' : QueryImpl spec σ unifSpec) (used : σ → Prop)
    (hused : ∀ i x s, used s → O' i x s = O i x s)
    (hstick : ∀ i x s, used s → (O i x s).AllOutputs fun p => used p.2)
    (c : OracleComp spec α) {s : σ} (hs : used s) : simulate O' c s = simulate O c s := by
  induction c generalizing s with
  | pure a => rw [simulate_pure, simulate_pure]
  | query i x k ih =>
    rw [simulate_query, simulate_query, hused i x s hs]
    exact OracleComp.bind_congr_of_allOutputs (hstick i x s hs) fun p hp => ih p.1 hp

/-- **One-shot coins drawn in advance.** Let `O` be an implementation and `OE t` its variants with
coins `t ∈ T` fixed in advance, and let `used` mark the states after the coins are spent:
- from a used state, `OE t` is `O`, and `O` keeps the state used;
- from an unused state, a call either does not use the coins (`OE t` is `O` for every `t`, and the
  state stays unused), or it is the one that spends them (`O` samples `t` and runs `OE t`, and
  every successor is used).

Then from an unused state, `O`'s simulation has the law of `OE t`'s, averaged over `t`:
`𝔼[G(simulate O c s)] = 𝔼_{t ← T} 𝔼[G(simulate (OE t) c s)]`.

**Proof sketch.** Induction on `c`. From used states the two simulations coincide
(`simulate_eq_of_used`). At a query from an unused state: in the first case, rewrite the call,
apply the induction hypothesis at the (unused) successors and exchange the expectations
(`ProbComp.expect_expect_sample`); in the second, expand `O`'s sample and conclude from the
coincidence at the (used) successors. -/
theorem expect_simulate_eager (O : QueryImpl spec σ unifSpec) (OE : T → QueryImpl spec σ unifSpec)
    (used : σ → Prop) (hused : ∀ t i x s, used s → OE t i x s = O i x s)
    (hstick : ∀ i x s, used s → (O i x s).AllOutputs fun p => used p.2)
    (hfresh : ∀ i x s, ¬ used s →
      (∀ t, OE t i x s = O i x s ∧ (O i x s).AllOutputs fun p => ¬ used p.2) ∨
      (O i x s = (ProbComp.sample T).bind (fun t => OE t i x s) ∧
        ∀ t, (OE t i x s).AllOutputs fun p => used p.2))
    (c : OracleComp spec α) (G : α × σ → ℝ) {s : σ} (hs : ¬ used s) :
    ProbComp.expect (simulate O c s) G =
      ProbComp.expect (ProbComp.sample T) fun t => ProbComp.expect (simulate (OE t) c s) G := by
  induction c generalizing s with
  | pure a =>
    simp only [simulate_pure, ProbComp.expect_pure]
    exact (ProbComp.expect_const _ _).symm
  | query i x k ih =>
    simp only [simulate_query, ProbComp.expect_bind]
    rcases hfresh i x s hs with h | ⟨h, hu⟩
    · have hO : ∀ t, OE t i x s = O i x s := fun t => (h t).1
      have hun : (O i x s).AllOutputs fun p => ¬ used p.2 :=
        (h (Classical.arbitrary T)).2
      simp only [hO]
      rw [ProbComp.expect_congr_of_allOutputs hun fun p hp => ih p.1 hp,
        ProbComp.expect_expect_sample]
    · rw [h, ProbComp.expect_bind]
      refine congrArg _ (funext fun t => ?_)
      refine ProbComp.expect_congr_of_allOutputs (hu t) fun p hp => ?_
      rw [simulate_eq_of_used O (OE t) used (hused t) hstick _ hp]

end Eager

end TCSlib.Cryptography.Games

## ===== TCSlib/Cryptography/Games/Efficiency/OracleBridge.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Efficiency.Strings
import TCSlib.Cryptography.Games.Bridges.QueryTree
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# From one-oracle `bitCodec` machines to next-query machines (efficiency fill, T4)

The translators behind `Games.exists_toOracleAdversary_of_bitCodec` (route note
`briefs/pass-shelat-ch5-8/design/S2b-efficiency.md`, §"T4"). A machine `B` against one
`bitCodec` oracle with a one-bit output reads `⟨[], log⟩` and writes `bitCodec` moves; a
next-query machine of the ch. 2–4 layer reads a history (`encodeHist`) and writes
`decodeOracleMove` moves. Two polynomial-time maps translate:
- `bridgePre` turns the history `⟨⟨x₁, y₁⟩, ⟨…, []⟩⟩` into `⟨[], ⟨⟨[], ⟨x₁, y₁⟩⟩, ⟨…, []⟩⟩⟩`,
  the empty input followed by the `bitCodec` log (the index of the only oracle is `1^0 = []`);
- `bridgePost` turns a canonical query word `⟨[false], ⟨[], x⟩⟩` into `⟨[false], x⟩`, the word
  `⟨[true], [true]⟩` into the verdict `[true, true]`, and every other word into `[true, false]`.

Both decoders check the payload length `ℓ₁(n)` themselves and agree on it, so neither map
needs the parameter.

## Main definitions

* `Games.iterEmit`: iterate and emit, the generic construction of `relabel`, `NMCCA2.logEmit`
  and `NMSim.chunkMap`.
* `EffFill.relabelEmit`, `EffFill.relabel`, `EffFill.bridgePre`, `EffFill.bridgePost`.

## Main results

* `Games.polyTimeComputable_iterEmit`, `Games.iterEmit_encode`, `Games.length_iterate_le_add`:
  iterate and emit is polynomial-time and reads a list encoding element by element.
* `EffFill.relabelN_eq_iterEmit`, `EffFill.relabel_eq_iterEmit`: the history translator is an
  instance.
* `EffFill.bridgePre_encodeHist`: the history of a log translates to the log.
* `EffFill.bridgePost_spec`: the translated move is the decoded move.
* `EffFill.eval_buildTree_bridge`: the two computations evaluate alike against every oracle.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Definition 96.1 (oracle indistinguishability against oracle machines).
-/

namespace TCSlib.Cryptography.Games

open Complexity Turing

/-! ### Iterate and emit

`iterEmit step emit m x` runs `m` rounds of `step` from `x` and concatenates the emissions of the
visited words. On the words `enc l` of a list encoding whose step drops the first element, it reads
the elements one by one (`iterEmit_encode`); with polynomial-time `step` and `emit` and `|x| + 1`
rounds, it is polynomial-time when `step` never lengthens a word beyond a constant
(`polyTimeComputable_iterEmit`). The history translator below (`EffFill.relabel`), the log readings
`NMCCA2.logEmit` and the chunk maps `NMSim.chunkMap` are instances. -/

/-- **Iterate and emit:** the emissions of the first `m` iterates of `step` from `x`,
concatenated: `iterEmit step emit m x = (List.range m).flatMap fun i => emit (step^[i] x)`. -/
def iterEmit (step emit : List Bool → List Bool) (m : ℕ) (x : List Bool) : List Bool :=
  (List.range m).flatMap fun i => emit (step^[i] x)

/-- `iterEmit step emit m x = (List.range m).flatMap fun i => emit (step^[i] x)`. -/
theorem iterEmit_eq (step emit : List Bool → List Bool) (m : ℕ) (x : List Bool) :
    iterEmit step emit m x = (List.range m).flatMap fun i => emit (step^[i] x) :=
  rfl

/-- **The orbit stays short:** if one step never makes a word longer than `max |y| c`, the
iterates of `x` have at most `|x| + c` bits: `|step^[i] x| ≤ |x| + c`. -/
theorem length_iterate_le_add {step : List Bool → List Bool} (c : ℕ)
    (h : ∀ y, (step y).length ≤ max y.length c) (x : List Bool) (i : ℕ) :
    (step^[i] x).length ≤ x.length + c := by
  suffices hmax : (step^[i] x).length ≤ max x.length c by omega
  induction i with
  | zero => exact le_max_left _ _
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact (h _).trans (max_le ih (le_max_right _ _))

/-- **Iterate and emit is polynomial-time** for `|x| + 1` rounds, when `step` and `emit` are and
one step never makes a word longer than `max |y| c`:
`PolyTimeComputable fun x => iterEmit step emit (|x| + 1) x`.

**Proof sketch.** `Complexity.polyTimeComputable_iterateEmit` with `|x|` rounds and the orbit
bound `|x| + c` (`length_iterate_le_add`). -/
theorem polyTimeComputable_iterEmit {step emit : List Bool → List Bool}
    (hstep : PolyTimeComputable step) (hemit : PolyTimeComputable emit) (c : ℕ)
    (h : ∀ y, (step y).length ≤ max y.length c) :
    PolyTimeComputable fun x => iterEmit step emit (x.length + 1) x :=
  (polyTimeComputable_iterateEmit hstep hemit .var (.add .var (.const c))
    (fun x i _ => by
      rw [PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_const]
      exact length_iterate_le_add c h x i)).congr
    fun x => by rw [PolyExpr.eval_var, iterEmit_eq]

/-- **Iterate and emit reads a list encoding element by element.** Let `enc` encode lists of `β`
so that `step` drops the first element of the encoded list of `l` (`step (enc (e :: t)) = enc t`
for the elements `e` of `l`) and fixes `enc []`, and let `emit` read nothing from `enc []` and `g e`
from `enc (e :: t)`. Then `m ≥ |l|` rounds from `enc l` emit `l.flatMap g`:
`iterEmit step emit m (enc l) = l.flatMap g`.

**Proof sketch.** The `i`-th iterate is `enc (l.drop i)` (induction on `i`); the readings of the
successive suffixes are `TCSlib.Cryptography.flatMap_range_drop`. -/
theorem iterEmit_encode {β : Type} (step emit : List Bool → List Bool) (enc : List β → List Bool)
    (g : β → List Bool) (l : List β) (hstep_nil : step (enc []) = enc [])
    (hstep : ∀ e ∈ l, ∀ t, step (enc (e :: t)) = enc t) (hnil : emit (enc []) = [])
    (hcons : ∀ e ∈ l, ∀ t, emit (enc (e :: t)) = g e) (m : ℕ) (hm : l.length ≤ m) :
    iterEmit step emit m (enc l) = l.flatMap g := by
  have hit : ∀ i, step^[i] (enc l) = enc (l.drop i) := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [Function.iterate_succ_apply', ih, ← List.tail_drop]
      cases hd : l.drop i with
      | nil => rw [List.tail_nil, hstep_nil]
      | cons e t => rw [List.tail_cons, hstep e (List.mem_of_mem_drop (hd ▸ List.mem_cons_self))]
  rw [iterEmit_eq]
  simp only [hit]
  exact flatMap_range_drop (fun l' => emit (enc l')) g hnil l hcons m hm

end TCSlib.Cryptography.Games

namespace TCSlib.Cryptography.Games.EffFill

open Complexity Turing

/-! ### The history translator -/

/-- The piece emitted for the suffix `w` of an encoded history: `⟨⟨[], fst w⟩, []⟩` for a
non-empty suffix, nothing for the empty one. -/
def relabelEmit (w : List Bool) : List Bool :=
  if w = [] then [] else pairEncode (pairEncode [] (pairFstD w)) []

/-- `relabelEmit w = if w = [] then [] else ⟨⟨[], fst w⟩, []⟩`. -/
theorem relabelEmit_eq (w : List Bool) :
    relabelEmit w = if w = [] then [] else pairEncode (pairEncode [] (pairFstD w)) [] :=
  rfl

/-- The pieces of the first `m` suffixes `w, snd w, snd (snd w), …`, concatenated. -/
def relabelN (m : ℕ) (w : List Bool) : List Bool :=
  (List.range m).flatMap fun i => relabelEmit (pairSndD^[i] w)

/-- `relabelN m w = ⋃_{i < m} relabelEmit (snd^i w)`. -/
theorem relabelN_eq (m : ℕ) (w : List Bool) :
    relabelN m w = (List.range m).flatMap fun i => relabelEmit (pairSndD^[i] w) :=
  rfl

/-- `relabelN` is iterate-and-emit with the step `pairSndD`:
`relabelN m w = iterEmit pairSndD relabelEmit m w`. -/
theorem relabelN_eq_iterEmit (m : ℕ) (w : List Bool) :
    relabelN m w = iterEmit pairSndD relabelEmit m w := by
  rw [relabelN_eq, iterEmit_eq]

/-- **The history translator's body:** the pieces of the first `|x| + 1` suffixes of `x`. -/
def relabel (x : List Bool) : List Bool := relabelN (x.length + 1) x

/-- `relabel x = relabelN (|x| + 1) x`. -/
theorem relabel_eq (x : List Bool) : relabel x = relabelN (x.length + 1) x := rfl

/-- `relabel` is iterate-and-emit for `|x| + 1` rounds:
`relabel x = iterEmit pairSndD relabelEmit (|x| + 1) x`. -/
theorem relabel_eq_iterEmit (x : List Bool) :
    relabel x = iterEmit pairSndD relabelEmit (x.length + 1) x := by
  rw [relabel_eq, relabelN_eq_iterEmit]

/-- **The history translator:** `bridgePre x = ⟨[], relabel x⟩`. -/
def bridgePre (x : List Bool) : List Bool := pairEncode [] (relabel x)

/-- `bridgePre x = ⟨[], relabel x⟩`. -/
theorem bridgePre_eq (x : List Bool) : bridgePre x = pairEncode [] (relabel x) := rfl

/-- The empty word has no pieces: `relabelN m [] = []`. -/
theorem relabelN_nil (m : ℕ) : relabelN m [] = [] := by
  rw [relabelN_eq, List.flatMap_eq_nil_iff]
  intro i _
  have h : ∀ j, pairSndD^[j] ([] : List Bool) = [] := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih]
      exact pairSndD_of_pairDecode_eq_none Turing.pairDecode_nil
  rw [h, relabelEmit_eq, if_pos rfl]

/-- One more suffix: `relabelN (m + 1) w = relabelEmit w ++ relabelN m (snd w)`. -/
theorem relabelN_succ (m : ℕ) (w : List Bool) :
    relabelN (m + 1) w = relabelEmit w ++ relabelN m (pairSndD w) := by
  rw [relabelN_eq, relabelN_eq, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
  rfl

/-- The history of a one-oracle `bitCodec` log, as (query, answer) pairs. -/
def logHist {ℓ₁ ℓ₂ : ℕ} (L : QueryLog (bitSpec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂))) :
    List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) :=
  L.map fun e => (e.2.1, e.2.2)

/-- `logHist L` maps each entry `⟨0, x, y⟩` to `(x, y)`. -/
theorem logHist_eq {ℓ₁ ℓ₂ : ℕ} (L : QueryLog (bitSpec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂))) :
    logHist L = L.map fun e => (e.2.1, e.2.2) :=
  rfl

/-- **The pieces of an encoded history form the `bitCodec` log:** for every `m ≥ |L|`,
`relabelN m (encodeHist (logHist L)) = encodeLog L`.

**Proof sketch.** Induction on `L`. The empty history is `[]`, which has no pieces
(`relabelN_nil`). A non-empty history `⟨⟨x, y⟩, rest⟩` emits `⟨⟨[], ⟨x, y⟩⟩, []⟩` and continues
with `rest` (`relabelN_succ`, `encodeHist_cons`); the piece is the entry's `bitCodec` encoding
(`bitCodec_encodeEntry`, the index of the only oracle being `1^0 = []`), and the concatenation is
the nested pair (`GGMRed.pairEncode_append_right`, `encodeLog_cons`). -/
theorem relabelN_encodeHist {ℓ₁ ℓ₂ : ℕ} (dα : ℕ) :
    ∀ (L : QueryLog (bitSpec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂))) (m : ℕ), L.length ≤ m →
      relabelN m (encodeHist (logHist L)) =
        (bitCodec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) dα).encodeLog L
  | [], m, _ => by
    rw [logHist_eq, List.map_nil, encodeHist_nil, relabelN_nil, MachineCodec.encodeLog_nil]
  | e :: L, m, hm => by
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by rw [List.length_cons] at hm; omega⟩
    rw [logHist_eq, List.map_cons, ← logHist_eq, encodeHist_cons, relabelN_succ,
      pairSndD_pairEncode, relabelN_encodeHist dα L m (by rw [List.length_cons] at hm; omega),
      relabelEmit_eq, if_neg (pairEncode_ne_nil _ _), pairFstD_pairEncode,
      MachineCodec.encodeLog_cons, bitCodec_encodeEntry, ← GGMRed.pairEncode_append_right,
      List.nil_append, Fin.fin_one_eq_zero e.1, Fin.val_zero, List.replicate_zero]

/-- An encoded history has at least as many bits as entries. -/
theorem length_le_length_encodeHist {ℓ₁ ℓ₂ : ℕ} :
    ∀ h : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)), h.length ≤ (encodeHist h).length
  | [] => Nat.zero_le _
  | p :: h => by
    rw [encodeHist_cons, length_pairEncode, List.length_cons]
    have := length_le_length_encodeHist h
    omega

/-- **The history translator on a history:** `bridgePre (encodeHist (logHist L)) =
⟨[], encodeLog L⟩`. -/
theorem bridgePre_encodeHist {ℓ₁ ℓ₂ : ℕ} (dα : ℕ)
    (L : QueryLog (bitSpec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂))) :
    bridgePre (encodeHist (logHist L)) =
      pairEncode [] ((bitCodec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) dα).encodeLog L) := by
  rw [bridgePre_eq, relabel_eq, relabelN_encodeHist dα L _]
  have h1 := length_le_length_encodeHist (logHist L)
  rw [logHist_eq, List.length_map] at h1
  rw [logHist_eq]
  omega

/-- The emitted piece is polynomial-time. -/
theorem relabelEmit_poly : PolyTimeComputable relabelEmit :=
  (polyTimeComputable_ite polyTimeComputable_isNil (polyTimeComputable_const [])
    (((polyTimeComputable_const []).pairEncode polyTimeComputable_pairFstD).pairEncode
      (polyTimeComputable_const []))).congr fun w => by
    rw [relabelEmit_eq]
    by_cases h : w = []
    · rw [if_pos h, decide_eq_true h]
      rfl
    · rw [if_neg h, decide_eq_false h]
      rfl

/-- **The history translator is polynomial-time** (`polyTimeComputable_iterEmit` with the step
`pairSndD`, which never lengthens a word, through `relabel_eq_iterEmit`). -/
theorem bridgePre_poly : PolyTimeComputable bridgePre := by
  have h := polyTimeComputable_iterEmit polyTimeComputable_pairSndD relabelEmit_poly 0
    fun y => (length_pairSndD_le y).trans (le_max_left _ _)
  refine ((polyTimeComputable_const []).pairEncode h).congr fun x => ?_
  rw [bridgePre_eq, relabel_eq_iterEmit]

/-! ### The move translator -/

/-- **The move translator:** a canonical query word `⟨[false], ⟨[], x⟩⟩` becomes `⟨[false], x⟩`,
the output word `⟨[true], [true]⟩` becomes `[true, true]`, and every other word `[true, false]`. -/
def bridgePost (w : List Bool) : List Bool :=
  if w = pairEncode [false] (pairEncode [] (pairSndD (pairSndD w))) then
    pairEncode [false] (pairSndD (pairSndD w))
  else if w = pairEncode [true] [true] then [true, true] else [true, false]

/-- The defining equation of `bridgePost`. -/
theorem bridgePost_eq (w : List Bool) :
    bridgePost w =
      if w = pairEncode [false] (pairEncode [] (pairSndD (pairSndD w))) then
        pairEncode [false] (pairSndD (pairSndD w))
      else if w = pairEncode [true] [true] then [true, true] else [true, false] :=
  rfl

/-- **The move translator is polynomial-time** (`eq_poly` for the two tests). -/
theorem bridgePost_poly : PolyTimeComputable bridgePost := by
  have hx := polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD
  have h1 := eq_poly polyTimeComputable_id ((polyTimeComputable_const [false]).pairEncode
    ((polyTimeComputable_const []).pairEncode hx))
  have h2 := eq_poly polyTimeComputable_id (polyTimeComputable_const (pairEncode [true] [true]))
  refine (polyTimeComputable_ite h1 ((polyTimeComputable_const [false]).pairEncode hx)
    (polyTimeComputable_ite h2 (polyTimeComputable_const [true, true])
      (polyTimeComputable_const [true, false]))).congr fun w => ?_
  rw [bridgePost_eq]
  simp only [id_eq, decide_eq_true_eq]

/-- **The translated move is the decoded move.** For every word `w`, either `decodeBitMove`
reads the query `x` (to the only oracle) and `decodeOracleMove` reads the query `x` off
`bridgePost w`, or `decodeBitMove` reads an output `a` and `decodeOracleMove` the verdict `a 0`.

**Proof sketch.** Three cases on `w`. A word `⟨[false], ⟨[], x⟩⟩` becomes `⟨[false], x⟩`: if
`|x| = ℓ₁` both decoders read the query (`decodeBitMove_query`,
`decodeOracleMove_pairEncode_ofFn`); otherwise both read the default, the all-`false` output and
the verdict `false` (`decodeBitMove_of_not_canonical`,
`decodeOracleMove_pairEncode_false_of_length_ne`). The word `⟨[true], [true]⟩` reads the output
`1` on both sides (`decodeBitMove_ret`, `decodeOracleMove_true_two`). Every other word becomes
`[true, false]`, the verdict `false`; `decodeBitMove` reads either the output `0` (the word
`⟨[true], [false]⟩`) or the default (`decodeBitMove_of_not_canonical`); its query words are all
of the first form, since `1^i = []` for `i : Fin 1`. -/
theorem bridgePost_spec (ℓ₁ ℓ₂ : ℕ) (w : List Bool) :
    (∃ x : Fin ℓ₁ → Bool,
      decodeBitMove (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1 w = .query 0 x ∧
        decodeOracleMove ℓ₁ (bridgePost w) = .query x) ∨
    (∃ a : Fin 1 → Bool,
      decodeBitMove (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1 w = .ret a ∧
        decodeOracleMove ℓ₁ (bridgePost w) = .ret (a 0)) := by
  by_cases hq : w = pairEncode [false] (pairEncode [] (pairSndD (pairSndD w)))
  · rw [bridgePost_eq, if_pos hq]
    set xw := pairSndD (pairSndD w)
    by_cases hx : xw.length = ℓ₁
    · obtain ⟨x, hxe⟩ := exists_ofFn_eq hx
      refine Or.inl ⟨x, ?_, ?_⟩
      · rw [hq, ← hxe]
        exact decodeBitMove_query (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1 0 x
      · rw [← hxe]
        exact decodeOracleMove_pairEncode_ofFn ℓ₁ x
    · refine Or.inr ⟨zeroBits 1, ?_, ?_⟩
      · refine decodeBitMove_of_not_canonical (fun i x h => hx ?_) (fun a h => ?_)
        · rw [hq, Fin.fin_one_eq_zero i, Fin.val_zero, List.replicate_zero] at h
          have h' := congrArg (fun v => pairSndD (pairSndD v)) h
          simp only [pairSndD_pairEncode] at h'
          rw [h', List.length_ofFn]
        · rw [hq] at h
          have h' := congrArg pairFstD h
          simp only [pairFstD_pairEncode] at h'
          exact absurd h' (by decide)
      · rw [decodeOracleMove_pairEncode_false_of_length_ne ℓ₁ hx, zeroBits_apply]
  · by_cases hr : w = pairEncode [true] [true]
    · refine Or.inr ⟨fun _ => true, ?_, ?_⟩
      · rw [hr]
        exact decodeBitMove_ret (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1 (fun _ => true)
      · rw [bridgePost_eq, if_neg hq, if_pos hr]
        exact decodeOracleMove_true_two ℓ₁ true
    · rw [bridgePost_eq, if_neg hq, if_neg hr, decodeOracleMove_true_two]
      by_cases hf : w = pairEncode [true] [false]
      · refine Or.inr ⟨fun _ => false, ?_, rfl⟩
        rw [hf]
        exact decodeBitMove_ret (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1 (fun _ => false)
      · refine Or.inr ⟨zeroBits 1, ?_, by rw [zeroBits_apply]⟩
        refine decodeBitMove_of_not_canonical (fun i x h => hq ?_) (fun a h => ?_)
        · rw [h, Fin.fin_one_eq_zero i, Fin.val_zero, List.replicate_zero, pairSndD_pairEncode,
            pairSndD_pairEncode]
        · have ha : List.ofFn a = [a 0] := by rw [List.ofFn_succ, List.ofFn_zero]
          rw [ha] at h
          cases h0 : a 0
          · rw [h0] at h; exact hf h
          · rw [h0] at h; exact hr h

/-! ### Evaluation -/

/-- **The two computations evaluate alike.** For a string function `D` (a machine with fixed coins),
the ch. 2–4 tree of the next-move function `h ↦ decodeOracleMove ℓ₁ (bridgePost (D (bridgePre
(encodeHist h))))` from the history of a log `L`, evaluated against `f`, is bit `0` of the
`bitCodec` computation of `L ↦ decodeBitMove (D ⟨[], encodeLog L⟩)` from `L`, evaluated against
`f` at the only oracle; for every budget.

**Proof sketch.** Induction on the budget, generalizing the log. The history translates to the
log (`bridgePre_encodeHist`), so both next moves come from the same word, and `bridgePost_spec`
gives corresponding moves. An output `a` gives the leaf `a 0` against the leaf `a`
(`buildTree_*_of_ret`, `buildComp_*_of_ret`). A query with the budget spent gives the verdict
`false` against `zeroBits 1`, whose bit `0` is `false`. A query `x` within budget asks `f x` on
both sides (`QueryTree.eval_query`, `OracleComp.evalFn_query`), and the continuations agree by
induction, since the history of `L ++ [⟨0, x, f x⟩]` is that of `L` followed by `(x, f x)`. -/
theorem eval_buildTree_bridge (ℓ₁ ℓ₂ : ℕ) (D : List Bool → List Bool)
    (f : (Fin ℓ₁ → Bool) → (Fin ℓ₂ → Bool)) :
    ∀ (q : ℕ) (L : QueryLog (bitSpec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂))),
      (buildTree (fun h => decodeOracleMove ℓ₁ (bridgePost (D (bridgePre (encodeHist h))))) q
          (logHist L)).eval f =
        (buildComp (fun L => decodeBitMove (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1
            (D (pairEncode [] ((bitCodec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1).encodeLog L))))
          (zeroBits 1) q L).evalFn (fun _ => f) 0 := by
  intro q
  induction q with
  | zero =>
    intro L
    rcases bridgePost_spec ℓ₁ ℓ₂ (D (pairEncode []
        ((bitCodec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1).encodeLog L))) with
      ⟨x, hb, ho⟩ | ⟨a, hb, ho⟩
    · rw [buildTree_zero_of_query (x := x) (by rw [bridgePre_encodeHist 1 L]; exact ho),
        buildComp_zero_of_query hb, QueryTree.eval_ret, OracleComp.evalFn_pure, zeroBits_apply]
    · rw [buildTree_zero_of_ret (b := a 0) (by rw [bridgePre_encodeHist 1 L]; exact ho),
        buildComp_zero_of_ret hb, QueryTree.eval_ret, OracleComp.evalFn_pure]
  | succ q ih =>
    intro L
    rcases bridgePost_spec ℓ₁ ℓ₂ (D (pairEncode []
        ((bitCodec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1).encodeLog L))) with
      ⟨x, hb, ho⟩ | ⟨a, hb, ho⟩
    · rw [buildTree_succ_of_query (x := x) (by rw [bridgePre_encodeHist 1 L]; exact ho),
        buildComp_succ_of_query hb, QueryTree.eval_query, OracleComp.evalFn_query]
      have hh : logHist L ++ [(x, f x)] = logHist (L ++ [⟨0, x, f x⟩]) := by
        rw [logHist_eq, logHist_eq, List.map_append, List.map_singleton]
      rw [hh]
      exact ih (L ++ [⟨0, x, f x⟩])
    · rw [buildTree_succ_of_ret (b := a 0) (by rw [bridgePre_encodeHist 1 L]; exact ho),
        buildComp_succ_of_ret hb, QueryTree.eval_ret, OracleComp.evalFn_pure]

end TCSlib.Cryptography.Games.EffFill

## ===== TCSlib/Cryptography/Foundations/BitLists.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.GetD
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Fintype.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bit lists and bit vectors

Generic facts about lists, lists of bits and bit vectors `Fin n → Bool`, shared by the
cryptographic developments: heads of suffixes, flattening singleton blocks, the bit of a one-bit
vector, cancellation of exclusive-or, exclusive-or with a fixed vector as a permutation, and keys of
an association list. They depend on Mathlib only.

## Main definitions

* `TCSlib.Cryptography.xorPerm v`: exclusive-or with the vector `v`, as a permutation.

## Main results

* `TCSlib.Cryptography.headD_drop`: the head of a suffix is an entry.
* `TCSlib.Cryptography.flatten_ofFn_one`, `flatten_ofFn_singleton`: flattening one-element blocks.
* `TCSlib.Cryptography.headD_ofFn_one`: the bit of a one-bit vector is the head of its string.
* `TCSlib.Cryptography.zipWith_xor_cancel_left`: `(a ⊕ c) ⊕ a = c`.
* `TCSlib.Cryptography.xorPerm_apply`: `xorPerm v y = y ⊕ v`.
* `TCSlib.Cryptography.mem_keys_of_lookup_isSome`: a key with a value in an association list is
  one of its keys.
* `TCSlib.Cryptography.ofFn_eq_map_range`, `ofFn_natAdd_eq_drop`, `decide_map_ofFn`: lists of
  tuples as maps over ranges, tails of tuples, comparing optional tuples through their lists.
* `TCSlib.Cryptography.length_flatten_map_const`, `length_flatten_map_range`: the length of a
  concatenation of equal-length blocks.
* `TCSlib.Cryptography.flatMap_range_drop`: reading the successive suffixes of a list.

## References

Generic list facts; no textbook counterpart.
-/

namespace TCSlib.Cryptography

/-- The head of a dropped list is the element at the dropping index:
`(l.drop i).headD d = l.getD i d`. -/
theorem headD_drop {α : Type*} (l : List α) (i : ℕ) (d : α) : (l.drop i).headD d = l.getD i d := by
  rw [List.headD_eq_head?, List.head?_drop, List.getD_eq_getElem?_getD]

/-- **Flattening one-element blocks:** concatenating the one-bit blocks `g j` gives their bits,
`(List.ofFn fun j => List.ofFn (g j)).flatten = List.ofFn fun j => g j 0` when the blocks have
length `l = 1`.

**Proof sketch.** Induction on the number `k` of blocks (`List.ofFn_succ`, `List.flatten_cons`). -/
theorem flatten_ofFn_one {k l : ℕ} (hl : l = 1) (g : Fin k → Fin l → Bool) :
    (List.ofFn fun j => List.ofFn (g j)).flatten = List.ofFn fun j => g j ⟨0, by omega⟩ := by
  subst hl
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.ofFn_succ, List.flatten_cons, ih (fun j => g j.succ), List.ofFn_succ (n := k)]
    simp

/-- Flattening singletons: `(List.ofFn fun i => List.ofFn fun _ : Fin p => f i).flatten =
List.ofFn f` when `p = 1` (`flatten_ofFn_one` with constant blocks). -/
theorem flatten_ofFn_singleton {p : ℕ} (hp : p = 1) :
    ∀ {k : ℕ} (f : Fin k → Bool),
      (List.ofFn fun i => List.ofFn fun _ : Fin p => f i).flatten = List.ofFn f :=
  fun f => flatten_ofFn_one hp fun i _ => f i

/-- The bit of a one-bit output is the head of its string: `⟦f⟧.headD false = f 0`. -/
theorem headD_ofFn_one (f : Fin 1 → Bool) : (List.ofFn f).headD false = f 0 := by
  rw [List.ofFn_succ, List.headD_cons]

/-- Exclusive-or with the same list twice cancels: `(a ⊕ c) ⊕ a = c` for `|a| = |c|`. -/
theorem zipWith_xor_cancel_left {a c : List Bool} (h : a.length = c.length) :
    List.zipWith xor (List.zipWith xor a c) a = c := by
  apply List.ext_getElem
  · simp [h]
  · intro i h₁ h₂
    simp only [List.getElem_zipWith]
    cases a[i] <;> cases c[i] <;> rfl

section XorPerm

variable {n : ℕ}

/-- Exclusive-or with a fixed vector `v`, as a permutation of `{0,1}ⁿ`: `xorPerm v y = y ⊕ v`. -/
def xorPerm (v : Fin n → Bool) : Equiv.Perm (Fin n → Bool) :=
  Function.Involutive.toPerm (fun y i => xor (y i) (v i)) fun y => funext fun i => by
    simp

/-- `xorPerm v y = y ⊕ v`. -/
theorem xorPerm_apply (v y : Fin n → Bool) : xorPerm v y = fun i => xor (y i) (v i) := rfl

end XorPerm

/-- A key with a value in an association list is one of its keys:
`(T.lookup x).isSome → x ∈ T.map Prod.fst`.

**Proof sketch.** Core's `List.lookup_isSome_iff` gives a pair `p ∈ T` with `x == p.1`, so `x`
is the first component of an element of `T` (`List.mem_map`). -/
theorem mem_keys_of_lookup_isSome {α β : Type} [DecidableEq α] (T : List (α × β)) (x : α)
    (h : (T.lookup x).isSome = true) : x ∈ T.map Prod.fst := by
  obtain ⟨p, hp, hx⟩ := List.lookup_isSome_iff.1 h
  exact List.mem_map.2 ⟨p, hp, (beq_iff_eq.1 hx).symm⟩

/-! ### Lists indexed by ranges, tails and blocks of lists -/

/-- A list of `r` values is a map over `List.range r`: if `f i = g i` for every `i : Fin r`, then
`List.ofFn f = (List.range r).map g` (both have `r` entries, entry `i` is `f i = g i`). -/
theorem ofFn_eq_map_range {α : Type*} {r : ℕ} (f : Fin r → α) (g : ℕ → α)
    (h : ∀ i : Fin r, f i = g i) : List.ofFn f = (List.range r).map g := by
  refine List.ext_getElem (by rw [List.length_ofFn, List.length_map, List.length_range])
    fun i h₁ h₂ => ?_
  rw [List.getElem_ofFn, List.getElem_map, List.getElem_range]
  exact h _

/-- **The tail of a string:** `⟦j ↦ w (natAdd k j)⟧ = ⟦w⟧.drop k` (`List.ofFn_add`). -/
theorem ofFn_natAdd_eq_drop {k sl : ℕ} (w : Fin (k + sl) → Bool) :
    List.ofFn (fun j : Fin sl => w (Fin.natAdd k j)) = (List.ofFn w).drop k := by
  rw [List.ofFn_add, List.drop_left' List.length_ofFn]

/-- Comparing strings is comparing their lists:
`decide (o.map ofFn = some ⟦c⟧) = decide (o = some c)` (`List.ofFn_inj`). -/
theorem decide_map_ofFn {k : ℕ} (o : Option (Fin k → Bool)) (c : Fin k → Bool) :
    decide (o.map List.ofFn = some (List.ofFn c)) = decide (o = some c) := by
  cases o with
  | none => simp
  | some c' => simp [List.ofFn_inj]

/-- Blocks of `k` entries, one per element: `|(l.map g).flatten| = |l|·k` when every `g x` has
`k` entries (`List.length_flatten`, a sum of the constant `k`). -/
theorem length_flatten_map_const {α β : Type*} (l : List α) (g : α → List β) (k : ℕ)
    (hg : ∀ x, (g x).length = k) : (l.map g).flatten.length = l.length * k := by
  rw [List.length_flatten, List.map_map, show (List.length ∘ g) = fun _ => k from funext hg,
    List.map_const', List.sum_replicate_nat]

/-- `r` blocks of `k` entries have `r·k` entries: `|((range r).map g).flatten| = r·k` when
`g 0, …, g (r-1)` have `k` entries each (`List.length_flatten`, a sum of the constant `k`). -/
theorem length_flatten_map_range {β : Type*} (k r : ℕ) (g : ℕ → List β)
    (hg : ∀ i < r, (g i).length = k) : ((List.range r).map g).flatten.length = r * k := by
  rw [List.length_flatten, List.map_map,
    List.map_congr_left (f := List.length ∘ g) (g := fun _ => k)
      fun i hi => hg i (List.mem_range.1 hi),
    List.map_const', List.sum_replicate_nat, List.length_range]

/-- **Reading the suffixes of a list within at least its length many steps:** if `F [] = []`
and `F` reads only the first element of a nonempty suffix, `F (e :: t) = g e` for the members `e`
of `l`, then `(List.range m).flatMap (fun i => F (l.drop i)) = l.flatMap g` for every
`m ≥ |l|`.

**Proof sketch.** Induction on `l`: the first suffix is `l` itself, read as `g e`; the others are
the suffixes of the tail, within `m - 1` steps; the empty suffixes read `[]`. -/
theorem flatMap_range_drop {β γ : Type*} (F : List β → List γ) (g : β → List γ)
    (hnil : F [] = []) :
    ∀ (l : List β), (∀ e ∈ l, ∀ t, F (e :: t) = g e) → ∀ m : ℕ, l.length ≤ m →
      ((List.range m).flatMap fun i => F (l.drop i)) = l.flatMap g := by
  intro l
  induction l with
  | nil =>
    intro _ m _
    rw [List.flatMap_nil]
    refine List.flatMap_eq_nil_iff.2 fun i _ => ?_
    rw [List.drop_nil, hnil]
  | cons e t ih =>
    intro hcons m hm
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by rw [List.length_cons] at hm; omega⟩
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, List.drop_zero,
      hcons e List.mem_cons_self, List.flatMap_cons]
    congr 1
    simp only [List.drop_succ_cons]
    exact ih (fun e' he' => hcons e' (List.mem_cons_of_mem _ he')) m'
      (by rw [List.length_cons] at hm; omega)

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Asymptotic/Adversary.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.PPT
import TCSlib.Cryptography.Foundations.Experiments
import TCSlib.Cryptography.HardcoreBit.Basic
import TCSlib.Cryptography.Foundations.BitLists

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machines as adversaries of the concrete experiments

The bridge between the machine layer (`Complexity.NUPPT`, strings `List Bool`) and the
concrete security experiments of `TCSlib.Cryptography.Foundations.Experiments` (typed
inputs `Fin m → Bool`, adversaries as functions of the input and of a uniform coin string).
An `NUPPT` `A` activated at parameter `n` becomes

* an *inverter* `A.inverter n ℓ m : (Fin m → Bool) → A.Coins n → Option (Fin ℓ → Bool)`
  [PS10, Definitions 27.3, 28.4]: `A(1^n, y)` with the output decoded as an `ℓ`-bit string;
* its literal variant `A.inverterLit ℓ m` for [PS10, Definition 26.1] (`A(f(x))`, activation
  at the input length `m`, no `1^n`);
* a *distinguisher* / *predictor* `A.distinguisher n m`, `A.predictor n m`
  [PS10, Definitions 69.4, 75.2, 78.3]: `A(1^n, t) = 1`, i.e. the output is the string `[true]`;
  `A.distinguisherL n` takes an untyped sample.

Inversion with a possibly failing decoder is `invProbOpt` (the probability that the decoded
output is a preimage); it is bridged to the concrete `invProb` by `invProbOpt_le_invProb`
(any default for a failure can only increase the probability) and `invProbOpt_some` (a total
inverter has the same probability). Foundation decision D5: inverses are sought in the
domain at the current parameter, and a wrong-length output counts as failure.

The file also records that "computes `f` with probability one" [PS10, Definition 24.6]
is, on the finite uniform coin space, the same as "for every coin string"
(`Complexity.NUPPT.computes_iff_uprob`), which justifies the frozen form of
`Complexity.NUPPT.Computes`.

**Deviation:** `inverter`: wrong-length output = failure (D5); verdict `= [true]` (normalisable
by `ifEq`).

## Main definitions

* `TCSlib.Cryptography.coinBlock` — the common indexed coin-tape segment.
* `TCSlib.Cryptography.decodeFin` — decode a string as an `ℓ`-bit string, failure on a wrong
  length; `TCSlib.Cryptography.padFin` — pad/truncate (for samplers).
* `TCSlib.Cryptography.blocksEquivX`, `TCSlib.Cryptography.FunFamily.blocks` — the canonical
  block bijection `(Fin (q·ℓ) → X) ≃ (Fin q → Fin ℓ → X)` and its Bool form, with the readers
  `blocksEquivX_apply`, `blocksEquivX_symm_apply`, `FunFamily.blocks_apply`,
  `FunFamily.blocks_symm_apply`.
* `Complexity.NUPPT.inverter`, `Complexity.NUPPT.inverterLit` — an `NUPPT` as an inverter
  (with `1^n`, and literal).
* `Complexity.NUPPT.distinguisher`, `Complexity.NUPPT.distinguisherL`,
  `Complexity.NUPPT.predictor` — an `NUPPT` as a distinguisher / predictor.
* `TCSlib.Cryptography.invProbOpt` — inversion probability of a possibly failing inverter.

## Main results

* `TCSlib.Cryptography.coinBlock_eq`, `TCSlib.Cryptography.length_coinBlock` — the segment
  equation and its full-length condition; `coinBlock_flatten`, `map_coinBlock_flatten`,
  `coinBlock_flatten_append` — the segments of a concatenation of equal-length blocks;
  `ofFn_block_eq_coinBlock` — block `i` of a string of blocks and a tail is segment `i`.
* `TCSlib.Cryptography.decodeFin_ofFn`, `TCSlib.Cryptography.padFin_ofFn` — decoding and
  padding invert `List.ofFn`; `TCSlib.Cryptography.decodeFin_eq_some_iff` — decoding succeeds
  exactly on the encoding; `TCSlib.Cryptography.ofFn_padFin_of_length` — padding a string of the
  right length keeps it.
* `TCSlib.Cryptography.ofFn_cast`, `TCSlib.Cryptography.ofFn_arrowCongr_finCongr` — a bit vector
  read across an equality of widths keeps its string.
* `TCSlib.Cryptography.FunFamily.ofFn_blocks` — block `j` of a string is its `j`-th window.
* `TCSlib.Cryptography.invProbOpt_le_invProb`, `TCSlib.Cryptography.invProbOpt_some` — the
  bridges to the concrete `invProb`.
* `TCSlib.Cryptography.invProbOpt_nonneg`, `TCSlib.Cryptography.invProbOpt_le_one` — bounds.
* `Complexity.NUPPT.computes_iff_uprob` — probability one is every coin string
  [PS10, Definition 24.6].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.1–2.2: Definitions 24.6, 26.1, 27.3; §3.1–3.3: Definitions 69.4, 75.2, 78.3.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Definitions 2.1, 2.3, 3.2–3.4 (the concrete experiments).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-- The `i`-th segment of `B` bits of a coin string; a short final segment is truncated. -/
def coinBlock (B i : ℕ) (r : List Bool) : List Bool := (r.drop (i * B)).take B

/-- The defining equation of `coinBlock`: `coinBlock B i r = (r.drop (i·B)).take B`. -/
theorem coinBlock_eq (B i : ℕ) (r : List Bool) : coinBlock B i r = (r.drop (i * B)).take B := rfl

/-- A coin segment has exactly `B` bits when its end lies within the input tape. -/
theorem length_coinBlock {B i : ℕ} {r : List Bool} (h : (i + 1) * B ≤ r.length) :
    (coinBlock B i r).length = B := by
  simp only [coinBlock_eq, List.length_take, List.length_drop]
  rw [Nat.add_mul, Nat.one_mul] at h
  omega

/-- **The blocks of a concatenation of `B`-bit blocks:** if every block of `l` has `B` bits,
segment `i < |l|` of `l.flatten` is `l[i]`.

**Proof sketch.** Induction on `l`: segment `0` is the first block (`List.take_left'`), and
segment `i + 1` drops the first block (`List.drop_append`) and is segment `i` of the rest. -/
theorem coinBlock_flatten {B : ℕ} : ∀ (l : List (List Bool)), (∀ c ∈ l, c.length = B) →
    ∀ (i : ℕ) (hi : i < l.length), coinBlock B i l.flatten = l[i]
  | [], _, _, hi => by simp at hi
  | c :: cs, hl, 0, _ => by
    have hc : c.length = B := hl c (by simp)
    simp [coinBlock_eq, ← hc]
  | c :: cs, hl, i + 1, hi => by
    have hc : c.length = B := hl c (by simp)
    have hrest := coinBlock_flatten cs (fun d hd => hl d (by simp [hd])) i (by simpa using hi)
    simp only [List.getElem_cons_succ, ← hrest, coinBlock_eq, List.flatten_cons]
    rw [show (i + 1) * B = c.length + i * B by rw [hc, Nat.succ_mul]; ring, List.drop_append,
      List.drop_eq_nil_of_le (by omega), List.nil_append, Nat.add_sub_cancel_left]

/-- **The blocks of a concatenation, mapped:** if every block of `cs` has `k` bits, mapping `F`
over the segments `coinBlock k i cs.flatten` for `i < |cs|` is mapping `F` over `cs`
(`coinBlock_flatten`, entry by entry). -/
theorem map_coinBlock_flatten {α : Type} (k : ℕ) (F : List Bool → α) :
    ∀ cs : List (List Bool), (∀ c ∈ cs, c.length = k) →
      (List.range cs.length).map (fun i => F (coinBlock k i cs.flatten)) = cs.map F := by
  intro cs hc
  refine List.ext_getElem (by rw [List.length_map, List.length_range, List.length_map])
    fun i h₁ h₂ => ?_
  rw [List.getElem_map, List.getElem_range, List.getElem_map,
    coinBlock_flatten cs hc i (by rw [List.length_map, List.length_range] at h₁; exact h₁)]

/-- **Reading back the blocks before a tail:** if `g 0, …, g (r-1)` have `k` bits each, segment
`i < r` of `g 0 ++ ⋯ ++ g (r-1) ++ t` is `g i`.

**Proof sketch.** Induction on `r`: for `i < r` the last block and the tail form the new tail;
for `i = r` the segment starts right after the first `r·k` bits (`length_flatten_map_range`). -/
theorem coinBlock_flatten_append (k r : ℕ) (g : ℕ → List Bool) (hg : ∀ i < r, (g i).length = k)
    (t : List Bool) (i : ℕ) (hi : i < r) :
    coinBlock k i (((List.range r).map g).flatten ++ t) = g i := by
  induction r generalizing t with
  | zero => exact absurd hi (Nat.not_lt_zero _)
  | succ r ih =>
    rw [List.range_succ, List.map_append, List.flatten_append, List.map_singleton,
      List.flatten_singleton, List.append_assoc]
    by_cases h : i < r
    · exact ih (fun j hj => hg j (by omega)) _ h
    · have hir : i = r := by omega
      subst hir
      rw [coinBlock_eq, List.drop_append_of_le_length (by
          rw [length_flatten_map_range k i g fun j hj => hg j (by omega)]),
        List.drop_of_length_le (by rw [length_flatten_map_range k i g fun j hj => hg j (by omega)]),
        List.nil_append, List.take_left' (hg i (by omega))]

/-- Decode a string as an `ℓ`-bit string: `some` of its bits if the length is exactly `ℓ`,
`none` otherwise (a wrong-length answer of an inverter is a failure, D5). -/
def decodeFin (ℓ : ℕ) (w : List Bool) : Option (Fin ℓ → Bool) :=
  if h : w.length = ℓ then some (fun i => w.get (Fin.cast h.symm i)) else none

/-- The defining equation of `decodeFin`: `decodeFin ℓ w` is `some` of the bits of `w` when
`|w| = ℓ`, and `none` otherwise. -/
theorem decodeFin_eq (ℓ : ℕ) (w : List Bool) :
    decodeFin ℓ w = if h : w.length = ℓ then some (fun i => w.get (Fin.cast h.symm i)) else none :=
  rfl

/-- Pad with `false` or truncate a string to exactly `ℓ` bits (the output convention of
samplers, where no failure is possible). -/
def padFin (ℓ : ℕ) (w : List Bool) : Fin ℓ → Bool := fun i => w.getD i false

/-- The defining equation of `padFin`: `padFin ℓ w = fun i => w.getD i false`. -/
theorem padFin_def (ℓ : ℕ) (w : List Bool) :
    padFin ℓ w =
      (fun i => w.getD i false :
        Fin ℓ → Bool) := rfl

/-- Bit `i` of `padFin ℓ w` is bit `i` of `w`, default `false`. -/
theorem padFin_apply (ℓ : ℕ) (w : List Bool) (i : Fin ℓ) : padFin ℓ w i = w.getD i false :=
  rfl

/-- Decoding the encoding of an `ℓ`-bit string returns it. -/
theorem decodeFin_ofFn {ℓ : ℕ} (x : Fin ℓ → Bool) : decodeFin ℓ (List.ofFn x) = some x := by
  simp [decodeFin]

/-- A decoded string has exactly the decoded length. -/
theorem length_eq_of_decodeFin_eq_some {ℓ : ℕ} {w : List Bool} {x : Fin ℓ → Bool}
    (h : decodeFin ℓ w = some x) : w.length = ℓ := by
  by_contra hw
  simp [decodeFin, hw] at h

/-- **Decoding succeeds exactly on the encoding**: `decodeFin ℓ w = some x ↔ w = List.ofFn x`,
for every width `ℓ` (`ℓ = 0` included) and every string `w`.

**Proof sketch.** A successful decoding has `|w| = ℓ` (`length_eq_of_decodeFin_eq_some`); after
substituting the width, `w = List.ofFn (w.get ·)` (`List.ofFn_get`) decodes to the bits of `w`
(`decodeFin_ofFn`), which are therefore `x`. Conversely `decodeFin_ofFn`. -/
theorem decodeFin_eq_some_iff (ℓ : ℕ) (w : List Bool) (x : Fin ℓ → Bool) :
    decodeFin ℓ w = some x ↔ w = List.ofFn x := by
  constructor
  · intro h
    have hw := length_eq_of_decodeFin_eq_some h
    subst hw
    have h' := decodeFin_ofFn (fun j : Fin w.length => w.get j)
    rw [List.ofFn_get, h, Option.some.injEq] at h'
    rw [h']
    exact (List.ofFn_get w).symm
  · rintro rfl
    exact decodeFin_ofFn x

/-- Padding the encoding of an `ℓ`-bit string returns it. -/
theorem padFin_ofFn {ℓ : ℕ} (x : Fin ℓ → Bool) : padFin ℓ (List.ofFn x) = x := by
  funext i
  simp [padFin]

/-- The encoding of `padFin L w` is `w` when `|w| = L`: `List.ofFn (padFin L w) = w`. -/
theorem ofFn_padFin_of_length {L : ℕ} {w : List Bool} (hw : w.length = L) :
    List.ofFn (padFin L w) = w := by
  refine List.ext_getElem (by simp [hw]) fun j hj₁ hj₂ => ?_
  simp [padFin_def, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj₂]

/-! ### Bit vectors across equal widths -/

/-- Reading a bit vector across an equality of widths keeps its string:
`⟦cast h f⟧ = ⟦f⟧` when `a = b`. -/
theorem ofFn_cast {a b : ℕ} (hab : a = b) (h : (Fin a → Bool) = (Fin b → Bool))
    (f : Fin a → Bool) : List.ofFn (cast h f) = List.ofFn f := by
  subst hab
  rfl

/-- Reading a vector at an equal width keeps its word:
`⟦(arrowCongr (finCongr h) (refl Bool)) v⟧ = ⟦v⟧`. -/
theorem ofFn_arrowCongr_finCongr {a b : ℕ} (h : a = b) (v : Fin a → Bool) :
    List.ofFn ((Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)) v) = List.ofFn v := by
  subst h
  rfl

/-! ### Blocks of a flat tuple -/

/-- A tuple of `q · ℓ` entries with values in an arbitrary type `X` as `q` consecutive blocks of
`ℓ` entries: block `i`, position `j` is entry `finProdFinEquiv (i, j) = j + ℓ·i` (Mathlib's
`finProdFinEquiv` and `Equiv.curry`). All `q`, `ℓ` (zero included). -/
def blocksEquivX (q ℓ : ℕ) (X : Type*) : (Fin (q * ℓ) → X) ≃ (Fin q → Fin ℓ → X) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl X)).trans (Equiv.curry _ _ _)

/-- The forward reader of `blocksEquivX`: block `i`, position `j` of `x` is entry
`finProdFinEquiv (i, j)` of `x`. -/
theorem blocksEquivX_apply (q ℓ : ℕ) {X : Type*} (x : Fin (q * ℓ) → X) (i : Fin q) (j : Fin ℓ) :
    blocksEquivX q ℓ X x i j = x (finProdFinEquiv (i, j)) := rfl

/-- The inverse of `blocksEquivX` reads block `p.divNat`, position `p.modNat`. -/
theorem blocksEquivX_symm_apply (q ℓ : ℕ) {X : Type*} (t : Fin q → Fin ℓ → X) (p : Fin (q * ℓ)) :
    (blocksEquivX q ℓ X).symm t p = t p.divNat p.modNat := rfl

/-- A string of `q · ℓ` bits as `q` consecutive blocks of `ℓ` bits (block `i` occupies the
positions `ℓ·i, …, ℓ·i + ℓ - 1`): the encoding of the tuple `(x₁, …, x_q)` of
[PS10, Theorem 35.1] as the `q·ℓ`-bit concatenation; the Bool specialization of
`blocksEquivX`. -/
def FunFamily.blocks (q ℓ : ℕ) : (Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool) :=
  blocksEquivX q ℓ Bool

/-- The defining equation of `blocks`: block `i`, position `j` is position `ℓ·i + j` of `x`. -/
theorem FunFamily.blocks_apply (q ℓ : ℕ) (x : Fin (q * ℓ) → Bool) (i : Fin q) (j : Fin ℓ) :
    FunFamily.blocks q ℓ x i j = x (finProdFinEquiv (i, j)) :=
  blocksEquivX_apply q ℓ x i j

/-- The inverse of `blocks` reads block `k.divNat`, position `k.modNat`. -/
theorem FunFamily.blocks_symm_apply (q ℓ : ℕ) (t : Fin q → Fin ℓ → Bool) (k : Fin (q * ℓ)) :
    (FunFamily.blocks q ℓ).symm t k = t k.divNat k.modNat :=
  blocksEquivX_symm_apply q ℓ t k

/-- **Block `j` is the `j`-th window of the string:**
`⟦FunFamily.blocks q ℓ ω j⟧ = (⟦ω⟧.drop (j·ℓ)).take ℓ`.

**Proof sketch.** Block `j` ends within the string, `j·ℓ + ℓ ≤ q·ℓ`, so both sides have `ℓ` bits.
Position `k` of block `j` is position `finProdFinEquiv (j, k) = k + ℓ·j` of `ω`
(`FunFamily.blocks_apply`), which is position `k` of the window. -/
theorem FunFamily.ofFn_blocks (q ℓ : ℕ) (ω : Fin (q * ℓ) → Bool) (j : Fin q) :
    List.ofFn (FunFamily.blocks q ℓ ω j) = ((List.ofFn ω).drop (j * ℓ)).take ℓ := by
  have hle : (j : ℕ) * ℓ + ℓ ≤ q * ℓ := by
    have := Nat.mul_le_mul_right ℓ (Nat.succ_le_of_lt j.isLt)
    rw [Nat.succ_mul] at this
    exact this
  refine List.ext_getElem ?_ fun k h₁ h₂ => ?_
  · simp only [List.length_ofFn, List.length_take, List.length_drop]
    omega
  · rw [List.getElem_ofFn, List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    refine (FunFamily.blocks_apply q ℓ ω j ⟨k, _⟩).trans ?_
    congr 1
    refine Fin.ext ?_
    rw [finProdFinEquiv_apply_val]
    show k + ℓ * j = j * ℓ + k
    rw [Nat.mul_comm]
    omega

/-- **Block `i` of a string of `r` blocks of `k` bits and a tail** is segment `i`:
`⟦j ↦ w (castAdd sl (finProdFinEquiv (i, j)))⟧ = coinBlock k i ⟦w⟧`.

**Proof sketch.** The block is block `i` of the first `r·k` bits (`FunFamily.blocks_apply`),
whose word is the window `(⟦w⟧.take (r·k)).drop (i·k)).take k` (`FunFamily.ofFn_blocks`,
`List.ofFn_add`); the tail does not reach the window since `i·k + k ≤ r·k`. -/
theorem ofFn_block_eq_coinBlock {r k sl : ℕ} (w : Fin (r * k + sl) → Bool) (i : Fin r) :
    List.ofFn (fun j : Fin k => w (Fin.castAdd sl (finProdFinEquiv (i, j)))) =
      coinBlock k i (List.ofFn w) := by
  have hle : (i : ℕ) * k + k ≤ r * k := by
    have := Nat.mul_le_mul_right k (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at this
    exact this
  have hblk : (fun j : Fin k => w (Fin.castAdd sl (finProdFinEquiv (i, j)))) =
      FunFamily.blocks r k (fun p => w (Fin.castAdd sl p)) i :=
    funext fun j => (FunFamily.blocks_apply r k (fun p => w (Fin.castAdd sl p)) i j).symm
  have hx : (List.ofFn fun p : Fin (r * k) => w (Fin.castAdd sl p)).length = r * k :=
    List.length_ofFn
  have hw : List.ofFn w = List.ofFn (fun p : Fin (r * k) => w (Fin.castAdd sl p)) ++
      List.ofFn (fun j : Fin sl => w (Fin.natAdd (r * k) j)) := List.ofFn_add
  rw [hblk, FunFamily.ofFn_blocks, coinBlock_eq, hw,
    List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by
      rw [List.length_drop]; omega)]

/-- `A(1^n, y)` as an inverter: output decoded as an `ℓ`-bit string, wrong length = failure
[PS10, Definitions 27.3 and 28.4, the experiment `f(A(1^n, y)) = y`].

**Deviation:** wrong-length output = failure (D5). For a typed family this loses nothing. For
a string function `f : {0,1}* → {0,1}*` the text's experiment also accepts a preimage of
another length, so the typed experiment can count fewer successes and typed one-wayness is
implied by, but weaker than, the text's, unless `|f(x)|` determines `|x|` (length-regular `f`
whose output length is a non-constant `PolyExpr`, hence injective in the input length; with
constant output length neither notion is satisfiable). The proviso is stated where string functions enter the typed world,
`FunFamily.ofString` (`Asymptotic/OneWay.lean`; gate 03a, note 15). -/
def _root_.Complexity.NUPPT.inverter (A : NUPPT) (n ℓ m : ℕ) :
    (Fin m → Bool) → A.Coins n → Option (Fin ℓ → Bool) :=
  fun y r => decodeFin ℓ (A.runAt n (List.ofFn y) r)

/-- The defining equation of `NUPPT.inverter`: the output of `A(1^n, y; r)` decoded as an
`ℓ`-bit string, `A.inverter n ℓ m y r = decodeFin ℓ (A.runAt n (List.ofFn y) r)`. -/
theorem _root_.Complexity.NUPPT.inverter_def (A : NUPPT) (n ℓ m : ℕ) (y : Fin m → Bool)
    (r : A.Coins n) : A.inverter n ℓ m y r = decodeFin ℓ (A.runAt n (List.ofFn y) r) := rfl

/-- The literal inverter `A(y)` of [PS10, Definition 26.1]: activation at parameter `|y| = m`
(the text gives the adversary `f(x)` only; the `1^{|y|}` prefix carries no information). -/
def _root_.Complexity.NUPPT.inverterLit (A : NUPPT) (ℓ m : ℕ) :
    (Fin m → Bool) → A.Coins m → Option (Fin ℓ → Bool) :=
  fun y r => decodeFin ℓ (A.runAt m (List.ofFn y) r)

/-- `A(1^n, t)` as a distinguisher: accepts iff the output is the string `[true]`
[PS10, Definition 69.4]. -/
def _root_.Complexity.NUPPT.distinguisher (A : NUPPT) (n m : ℕ) :
    (Fin m → Bool) → A.Coins n → Bool :=
  fun t r => decide (A.runAt n (List.ofFn t) r = [true])

/-- `A(1^n, w)` as a distinguisher of untyped samples (ciphertexts, views, histories). -/
def _root_.Complexity.NUPPT.distinguisherL (A : NUPPT) (n : ℕ) : List Bool → A.Coins n → Bool :=
  fun w r => decide (A.runAt n w r = [true])

/-- The defining equation of `distinguisherL`:
`A.distinguisherL n w r = decide (A.runAt n w r = [true])`. -/
theorem _root_.Complexity.NUPPT.distinguisherL_eq (A : NUPPT) (n : ℕ) (w : List Bool)
    (r : A.Coins n) : A.distinguisherL n w r = decide (A.runAt n w r = [true]) := rfl

/-- `A(1^n, y)` as a predictor of a bit: the same verdict convention as a distinguisher
[PS10, Definitions 75.2 and 78.3]. -/
def _root_.Complexity.NUPPT.predictor (A : NUPPT) (n m : ℕ) :
    (Fin m → Bool) → A.Coins n → Bool :=
  A.distinguisher n m

/-- The literal inverter is the inverter at parameter `m`. -/
theorem _root_.Complexity.NUPPT.inverterLit_eq (A : NUPPT) (ℓ m : ℕ) :
    A.inverterLit ℓ m = A.inverter m ℓ m := rfl

/-- The typed distinguisher is the untyped one on `List.ofFn t`. -/
theorem _root_.Complexity.NUPPT.distinguisher_eq (A : NUPPT) (n m : ℕ) (t : Fin m → Bool)
    (r : A.Coins n) : A.distinguisher n m t r = A.distinguisherL n (List.ofFn t) r := rfl

/-- The predictor is the distinguisher. -/
theorem _root_.Complexity.NUPPT.predictor_eq (A : NUPPT) (n m : ℕ) :
    A.predictor n m = A.distinguisher n m := rfl

/-- The inverter succeeds on `(y, r)` iff the machine's output is the encoding of some `x'`. -/
theorem _root_.Complexity.NUPPT.inverter_eq_some_iff (A : NUPPT) (n ℓ m : ℕ) (y : Fin m → Bool)
    (r : A.Coins n) (x' : Fin ℓ → Bool) :
    A.inverter n ℓ m y r = some x' ↔ A.runAt n (List.ofFn y) r = List.ofFn x' := by
  constructor
  · intro h
    have hw : (A.runAt n (List.ofFn y) r).length = ℓ := length_eq_of_decodeFin_eq_some h
    simp only [NUPPT.inverter, decodeFin, dif_pos hw, Option.some.injEq] at h
    subst h
    refine List.ext_get (by simp [hw]) fun i h₁ h₂ => ?_
    simp
  · intro h
    show decodeFin ℓ _ = _
    rw [h, decodeFin_ofFn]

/-- The probability that a possibly failing inverter `A`, given `f x` for uniform `x` and
uniform coins, outputs `some x'` with `f x' = f x` (the typed experiment of
[PS10, Definition 27.3] with a wrong-length output counted as failure, D5). -/
noncomputable def invProbOpt {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : α → β)
    (A : β → ρ → Option α) : ℝ :=
  uprob fun z : α × ρ => ∃ x', A (f z.1) z.2 = some x' ∧ f x' = f z.1

/-- The defining equation of `invProbOpt`:
`invProbOpt f A = Pr_{(x, r)}[∃ x', A(f x, r) = some x' ∧ f x' = f x]`, over uniform
`(x, r) ∈ α × ρ`. -/
theorem invProbOpt_def {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : α → β)
    (A : β → ρ → Option α) :
    invProbOpt f A = uprob fun z : α × ρ => ∃ x', A (f z.1) z.2 = some x' ∧ f x' = f z.1 := rfl

/-- Replacing a failure by any default can only increase the inversion probability: the
bridge from `invProbOpt` to the concrete `invProb` [Gar26, Definition 2.1]. -/
theorem invProbOpt_le_invProb {α β ρ : Type*} [Fintype α] [Fintype ρ] [Inhabited α] (f : α → β)
    (A : β → ρ → Option α) :
    invProbOpt f A ≤ invProb f (fun y r => (A y r).getD default) := by
  rw [invProbOpt_def, invProb_def]
  refine uprob_mono ?_
  rintro ⟨x, r⟩ ⟨x', hx', hf⟩
  simp [hx', hf]

/-- A total inverter has the same probability under both conventions. -/
theorem invProbOpt_some {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : α → β) (A : β → ρ → α) :
    invProbOpt f (fun y r => some (A y r)) = invProb f A := by
  unfold invProbOpt
  simp only [invProb_def]
  congr 1
  funext z
  simp

/-- The inversion probability is nonnegative. -/
theorem invProbOpt_nonneg {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : α → β)
    (A : β → ρ → Option α) : 0 ≤ invProbOpt f A :=
  uprob_nonneg _

/-- The inversion probability is at most one. -/
theorem invProbOpt_le_one {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : α → β)
    (A : β → ρ → Option α) : invProbOpt f A ≤ 1 :=
  uprob_le_one _

/-- **"With probability one" is "for every coin string"** [PS10, Definition 24.6]: `A`
computes `f` in the frozen sense (`Complexity.NUPPT.Computes`, equality for every coin
string) iff at every parameter and argument the event `A(1^n, y; r) = f(⟨1^n, y⟩)` has
probability one over the uniform coins. (On a finite uniform space an event of probability
one is the whole space, `HardcoreBit.forall_of_uprob_eq_one`.) -/
theorem _root_.Complexity.NUPPT.computes_iff_uprob (A : NUPPT) (f : List Bool → List Bool) :
    A.Computes f ↔
      ∀ n y, uprob (fun r : A.Coins n => A.runAt n y r = f (NUPPT.advInput n y)) = 1 := by
  rw [NUPPT.computes_iff]
  constructor
  · intro h n y
    have hp : (fun r : A.Coins n => A.runAt n y r = f (NUPPT.advInput n y)) = fun _ => True :=
      funext fun r => propext ⟨fun _ => trivial, fun _ => h n y r⟩
    rw [hp, uprob_true]
  · intro h n y r
    exact HardcoreBit.forall_of_uprob_eq_one (h n y) r

end TCSlib.Cryptography
