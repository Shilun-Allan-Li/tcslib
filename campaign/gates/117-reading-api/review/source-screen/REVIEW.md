# Gate 117: independent source, lint, copy screen and reuse search

Reviewer: Codex maintainer subagent `/root/review_mig1_brief`. This is a bounded pre-dispatch review; it does not close gate 117 or certify a replay.

**Result: no blocker, major or minor source change requested.** The proposed source matches the 23 approved API additions. No surviving source is changed, no new copy pair appears, and the fresh branch/delivery source search finds no competing exact source declaration or configuration-field generation site.

## Pins and scope

- Base: `e3adffac67377a8b6e23bed74bfdbb44a123dd86`.
- PR 230 head: `1160c18f03fd318f0dec25738790935fa61379d4`.
- Approval: `campaign/gates/117-reading-api/user-ruling.json`, all 23 scopes. Earlier proposal documents that called readers unapproved are historical, not the current ruling.
- Exact archives: `archives/base.tar` and `archives/head.tar`; eight inert extracted `.lean.txt` files on each side. Full commit/tree/blob pins and SHA256 receipts are in `source-pins.json`.

The five changed homes are Encoding, Simulation, Composition, Build/Wrappers and Build/Primitives. The full copy-screen population additionally contains Configuration, Deterministic and Finite. `POPULATION.md` and `population.txt` fixed that population before execution. The metadata reviewer independently confirmed those eight cover the foreign definition/model homes reached by the proposed API and published-consumer probes; Simulation also owns bufferTape and the agreement theorem. Neither population nor pair output is capped.

## Source recovery and exact approval scope

Removing only the approved insertion text from each fresh head file recovers the entire corresponding base file **byte for byte**. Thus all surviving declarations, private helpers, headers, visibility, order, imports, executable definitions and old proof bodies remain unchanged. The independent comment-aware source census agrees: eight explicit public theorem additions; no public removal, private addition/removal, visibility change, or surviving definition/proof/header change. The raw byte check is stronger than that parser's header classification.

| Home | Explicit source additions | Generated field additions |
| --- | --- | --- |
| Encoding | `CodeTM.toFinTM_eq` | 0 |
| Simulation | `branchTM_k`, `branchTM_State`, `branchTM_runFrom_independent` | Five fields each for `leftCfg`, `rightCfg` |
| Composition | `idTM_spaceUsed`, `constTM_spaceUsed` | 0 |
| Build/Primitives | `prependTM_spaceUsed`, `pairValidTM_spaceUsed` | 0 |
| Build/Wrappers | 0 | Five fields for `captureCfg` |

All field families are the approved `state`, `inputPos`, `workTapes`, `workTapePos`, `output`. The only three added simps commands specify `isSimp := false` and fully qualified definition names. There are no new imports, public definitions, or source `[simp]` attributes. The explicit-source census is 198 to 206 public declarations and 270 to 270 private declarations over the changed homes. This source count excludes compiler-generated field theorems and generated auxiliary declarations. Their exact names, attributes and axioms must be read from the separate compiled metadata receipt, not inferred from this source count.

## Mathematical and documentation review

1. **Coded bundle equation.** The whole constructor equality exposes precisely the existing one-tape count, finite state type and underlying machine, with no changed code interpretation or computation/space claim. Its same-home reflexive proof reads the definition it owns. The existing `CodeTM.toFinTM_k` remains available unchanged.
2. **Configuration readers.** `leftCfg` and `rightCfg` retain arbitrary tape/frame/head data and their existing sum embeddings; the readers are unconditional field equations for those configurations. The capture readers preserve the distinction between the physical output `out₀` and the buffered word `pre ++ c.output`. In particular, state uses the return-state fallback, the extra capture tape stores that buffered word, and its head is at the buffered length. These are readers for the definitions, not stronger run simulation claims.
3. **Branch API.** The tape-count and state-type equalities reveal only the common sum carriers. `branchTM_runFrom_independent` compares runs from one fixed common configuration after explicit transport into those carriers. It does not compare the machines' different native initial configurations. Its proof reuses the existing public `runFrom_eq_of_agreeOn` with the universal agreement set; same-home transition agreement is reflexive because the Boolean changes only the native initial-state selection. It is placed after the published agreement API, so there is no forward-reference dependency. The complete statement and proof were inspected manually: the generic source parser stops at the statement's type-level `let view :=` and does not itself recover that whole header.
4. **Four exact zero-space facts.** They hold for every input and every time, including time zero and after halting. They specialize the public zero-tape space theorem to the existing zero-tape canonical machines. They do not require their separate computation-specification theorems, including any inherited admitted theorem. Reading each canonical machine's own tape count occurs in its own home, not a foreign consumer.
5. **Documentation and boundaries.** The new docstrings describe these operational contracts and the branch transport. The short proof bodies introduce no new policy-lint finding. Old module/long-file/proof-sketch findings are preserved and reported below; this review neither repairs them nor records a new debt acknowledgment. The published-probe/reducibility/axiom checks are separate sibling evidence. No Lean was executed in this review.

## Lint: actual before/head runs

Canonical lint implementations were read and executed unchanged through their functions, with the root redirected to each inert archive and exactly the five changed homes supplied. Logs retain `.lean.txt` labels.

| Check | Base | Head | Disposition |
| --- | --- | --- | --- |
| `style_lint.py` | 40 findings, exit 1 | 40 findings, exit 1 | Exact diagnostic multiset unchanged after normalizing line positions and whole-file line counts only |
| `campaign_style_lint.py`, check 8b enabled | 0 FAIL / 8 WARN / 8 INFO, exit 0 | 0 FAIL / 7 WARN / 8 INFO, exit 0 | Field-reader coverage improves; no new warning family |

The unchanged style findings include inherited oversized files, old proof sketches/module sections, and the linter's old prose false positives `lemma (source` / `axiom axiom:`. The campaign linter drops Encoding's missing toFinTM field-equation warning and removes leftCfg/rightCfg/captureCfg from existing missing-reader lists. It still reports unrelated existing missing-reader and size findings. Changes in whole-file line counts are additions at the approved homes, not evidence that a size warning disappeared. Logs, script hashes and normalized comparison are under `lint/` and `source-and-lint.json`.

## Copy screen: actual complete runs and candidate disposition

The unchanged `copy-text-screen-v3.py` ran serially under `$TCSLIB_SCRATCH/locks/screen`, with `nice -n 10`, on all eight full archived files on each side. Both runs exited zero and the lock was released; timestamps, complete commands and raw-log hashes are in `screen/receipt.json`.

| Metric | Base | Head |
| --- | --- | --- |
| Declarations screened | 416 | 417 |
| Directional candidate pairs | 309 | 307 |
| Reproduced text | 84,786 chars | 84,634 chars |
| New directional pairs | — | **0** |
| Changed measurements among retained pairs | — | **0** |

Every head pair is therefore an unchanged baseline candidate. The target-file accounting is: Primitives 226 pairs / 99 target declarations; Simulation 33 / 16; Composition 26 / 12; Configuration 6 / 3; Deterministic 4 / 4; Encoding 2 / 2; Wrappers 10 / 4; Finite 0. This accounts for all 307 head pairs. It records raw inherited candidates, not 307 new debt approvals or a fresh adjudication of the old duplication ledger. The exact old proof/definition bytes are unchanged, so no retained family is introduced by this API PR.

The two lost pairs are `Composition.controlCfg -> Simulation.rightCfg` and `Simulation.leftCfg -> Simulation.rightCfg`. They were 68/130 (52%) and 84/130 (65%) respectively. The screen's source chunk for the preceding rightCfg now includes standalone simps commands, enlarging its denominator until the next declaration. The rightCfg definition itself is byte-identical. These two losses are a source-chunk boundary artifact: **no copy family or proof debt is claimed retired**. Generated field theorems have no new source proof body for this screen. Full raw pairs and independently parsed deltas are in `screen/`.

## Fresh name and statement-shape search

The read-only local inventory contains 395 refs and 126 worktree HEAD rows, resolving to 317 complete commit objects and 245 distinct TCSlib subtrees. Full commit, root-tree, TCSlib-subtree and alias pins are recorded; objects were checked, and each distinct TCSlib subtree was searched once. This includes the two current open campaign PRs 215 and 230, prepared landing branches/worktrees, all locally available delivery refs, and cp07 delivery `refs/remotes/deliver/mig1-mega-cp07` at `cbfdba8102e6a5d956a1fdd2be7518b490a5abac`. A fresh read-only GitHub open-PR response is summarized in `search/open-prs.json`. No refs were fetched, created or moved by this reviewer.

- The broad source-name query returns nine lines: precisely the eight intended explicit declarations and one internal use, all from the PR230 source tree. No competing explicit source declaration with these names was observed.
- Statement-shape enumeration examines 235 candidate source blobs, producing 293 candidate records / 39 distinct header groups. All 39 groups were inspected and dispositioned in `search/candidate-inspection.json`; there are no parser exceptions. The complete new branch statement was separately read because of the known type-level-let header limitation.
- Existing public `spaceUsed_zero_tapes_eq_zero` and `runFrom_eq_of_agreeOn` are the intended generic reuse paths, not missing reuse. Existing `CodeTM.toFinTM_k` reveals only the count; existential code/behavior theorems do not replace a constructor equality. Public capture space/visits and oracle reaching theorems require run/agreement/liveness hypotheses and do not provide the unconditional five-field configuration readers. Remaining hits are instance-specific private simulations/ledger helpers or unrelated universal-machine behavior statements. No competing public contract was identified among these candidates.
- Source generation sites were checked separately across all 245 pinned TCSlib trees, covering 102 distinct family-using source blobs and 30 family-definition prefix records. The only matching standalone simps commands are the three new approved PR230 commands. The three distinct definition prefixes have no attached simps attributes. This checks source generation sites, **not 245 historical compiled namespaces**. The exact current-head 15 generated field names and absence of simp attributes belong to the separate compiled census. No claim of compiled-name absence across every historical branch is made here.

The primary ref search completed successfully despite its default-sandbox `nice` wrapper warning (`setpriority: Operation not permitted`); its Python enumeration continued with exit zero. That warning is preserved in `search/execution-note.txt`, and reduced priority is not claimed for that search. The actual copy-screen commands and receipts are distinct.

## Remaining external checks

No source/API/import/design change is requested by this review. The external Codex gate, root's fresh 394-module replay, and the sibling compiled metadata/paired sealed-consumer controls are outside this receipt and remain root-owned. This report does not claim any of those executions, merge clearance, or gate closure.
