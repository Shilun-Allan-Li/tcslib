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
