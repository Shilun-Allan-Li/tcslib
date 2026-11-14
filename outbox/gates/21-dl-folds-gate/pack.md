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
