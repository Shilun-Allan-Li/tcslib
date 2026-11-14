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
