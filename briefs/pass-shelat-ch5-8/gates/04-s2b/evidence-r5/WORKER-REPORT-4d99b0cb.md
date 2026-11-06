#195's 26 files now have zero rule-10 exclusions, stacked on #210's final head 286aee54. Every file passes the seal with no named entry, the source scan finds nothing, and the replay, axiom and lint checks are clean. Nothing is pushed.

`PolyExpr.eval` is handled under ruling Q1: it is never sealed. `tools/unsealable.py` drops it from the head and base candidate lists (7 rows each, listed in `candidates/unsealable-dropped.tsv`).

## Head and commits
Head: `4d99b0cb7241b1f431476e1b7cf2f5a551d57d62` on `wip/g04r6`, worktree `$SP/wt-g04r4`, clean. Commits since #195's head 40553944 (first parent):
- `849b86b82bd19731aa70b4039252761d68d2fff2` — merge of #210 at a4eb21ae. One conflict, in ZeroKnowledge/Interaction.lean: both sides added a theorem right after `viewV` (`viewV_eq` from #195, `viewV_withV` from #210). I resolved it as the verbatim union of both sides; please check that is acceptable.
- `7df2f35c96397fa22c9ca13be905d6a6665d90a6` — re-points the reads to #210's equations and adds equations beside #195's own definitions.
- `7855f30623073d42026d8380dfda050f0ec597fc` — `FunFamily.blocks` reads re-proved through `blocks_symm_apply`.
- `bfa9082cf8b7b8d286652ce04205e03d526b23f7` — one proof rewritten as a calc.
- `40321a28a25408b40254173a20f182075e510188` — interim merge of #210 at 16a7d02d (clean).
- `f2dd0d1cd383ad29067806101d20810d9175a212` — `prfScheme` coin reads through `coinsEquiv_ofPolyTimeUniform`.
- `c24df1daa0534098e0aaa03ae0d10ba112b8866a` — interim merge of #210 at a7dec12c (clean).
- `c6ef011faf0b1729bdd50061e41199e3d394b4d7` — re-points to `oneBit_secure_iff`, `expand_stretch`, `ggmRedMachine_coinsEquiv` and `pairSndD_of_pairDecode_eq_none`.
- `e42c4f37a62ba3bd7b8b2ec678d8c83a15b8af60` — merge of #210 final 286aee54 (clean).
- `865b2ba0cb28175e210dfe791d261c418bddc68d` — `PRG.doubling_apply` through `PRG.expand_G_stretch`.
- `4d99b0cb7241b1f431476e1b7cf2f5a551d57d62` — `prfScheme_coinsEquiv_ofFn`, and a proof sketch for `prfScheme_multiEncDist`.

## Remaining entries
None. `exclusions.md` has no unseal entries (`unseal.json` is `{}`, derived from an empty seed over all 26 files), no other reads, and no explicit-unfold rows.

## Restatements (old → new, and why the meaning is unchanged)
1. **`NUPPT.runAt_preComp`** (PRFLemmas):
   - Old: `… = A.runAt n (pre …) r`.
   - New: `… = A.runAt n (pre …) (A.preComp_coinsEquiv hpre n r)`.
   - The old `r` only typechecked by reducing `coinLen` and `ofPolyTime`. The equivalence (built on `coinsCongr`) keeps the coin string (`preComp_coinsEquiv_ofFn`), so the activation is the same.
2. **`prfScheme_multiEncDist`** (MultiMessage):
   - Old: `= encodeTuple (prfEncReal (F n) m r)`.
   - New: `= encodeTuple (prfEncReal (F n) m (prfScheme_coinsEquiv … r))`.
   - The equivalence is built from `NUPPT.coinsEquiv_ofPolyTimeUniform` and keeps every coin string (`prfScheme_coinsEquiv_ofFn`). The only consumer, `prfScheme_multiMessageSecure`, removes it with `acceptProb_comp_equiv`.
3. **Definition bodies:**
   - `PRG.doubling`: the index passes through `Fin.cast` along `PRG.expand_stretch`. The value is unchanged, because `Fin.cast` keeps the index.
   - `prfScheme.correct` (a proof inside the definition) reads the coins through the published equivalences.

Statement diff against the first merge 849b86b8 (`stmtdiff-vs-merge.txt`): only these two statement changes and their docstrings, plus additions. `withV_vCoinsEquiv` and `withV_vCoinsEquiv_ofFn` in that file are #210's additions.

## Equations added beside #195's definitions (public, not @[simp])
- GGM.lean: `ggm_apply`, `prefixAt_apply`, `splitHalves_apply_fst`, `splitHalves_apply_snd`, `ggmBits_def`.
- PRF.lean: `decodeOracleMove_pairEncode_false`, `decodeOracleMove_true_two`, `encodeHist_eq_histEnc`, plus the private helper `pairDecode_true_two`.
- PRFLemmas.lean: `NUPPT.preComp_coinsEquiv` (+ `_ofFn`), and `eq_blocks_divNat_modNat` (derived from `FunFamily.blocks_symm_apply`).
- MultiMessage.lean: `prfScheme_coinsEquiv` (+ `_ofFn`).

## #210's final-sweep rows tagged 195 (`sweep-rows.tsv`)
All 16 rows pass the final seal with no entry, and the $BASE control fails at every one of them:
- `prfScheme` and `prfScheme_multiEncDist`: `coinLen` and `ofPolyTimeUniform` are sealed. `ofPolyTime` is not a candidate, because it is only reachable by unfolding the sealed `ofPolyTimeUniform`.
- `PRG.doubling`: `PRG.expand` is sealed.
- `runAt_preComp`: `coinLen` and `ofPolyTime` are sealed.
- Hopping (5), Protocols (6) and `QueryImpl.sum`: `QueryImpl` and `OracleSpec.add` are reducible abbreviations (R-04-4), so they are not seal candidates.

## Seal, control, scan
- Seal at the head (`seal-evidence.log`): 26/26 PASS, no named entries.
- Plain seal (`seal-plain.log`): 26/26 PASS.
- $BASE control (`seal-control-base.log`, 27ae72da against its rebuilt tree): 10 PASS, 16 FAIL. The 16 are MultiMessage, MultiMessageLemmas, PRF, PRFLemmas, Bridges/QueryTree, Bridges/Strategies, Efficiency, Hopping, Games/Probability, Protocols, Simulate, Defs, GGM, LazySampling, SubHybrids and Interaction.
- Source scan at the head (`scan.log`): 0 lemma-list hits, 0 show/change steps at seal failures, 0 proof-term equation-lemma refs. At $BASE: 84 / 5 / 21.
- Supplementary round-3 union check (`seal-r3union.log`): 5/5 PASS.
- Per-file table: `seal-table.md`.

## Checks
- **Replay:**
  - Full replay at 865b2ba0 (`replay-865b2ba0.log`): 226 modules, all rc=0 with no errors.
  - Increment at 4d99b0cb (`replay-final.log`): MultiMessage, the Asymptotic facade and `audits/pass-shelat/Checks`, all rc=0.
  - Sorry counts on the 144 modules also replayed at the merge are unchanged (`replay-cmp.txt`); the 26 files and Checks have no sorry.
- **Axioms** (`axioms.log`): 198 public theorems in the 8 files changed since 40553944, all within propext, Classical.choice and Quot.sound; no sorryAx; 0 errors.
- **Lint** (`lint.log`):
  - style_lint: 0 findings in each changed file and over all 26.
  - check8b: 0 FAIL in Asymptotic, Pseudorandom/Functions, Foundations and Games.
  - ZeroKnowledge shows 9 FAIL, all facade-import rows in GraphIsomorphism*/ThreeColoring facades, outside the 26. The same 9 appear at the merge commit, so they are not from this round.
  - No file grows past 1000 lines; the largest is PRF.lean at 867, so no size exception is needed.
- **Classifier** (`declchanges.tsv`, against merge base a3c5fa8b): SAME 279, ADDED 210, CHANGED 152, INDUCED 4. With no exclusions, no CHANGED or ADDED declaration carries one.

## Not done / issues
- Earlier in this round I stopped processes with `pkill -f tools/exclude.py` and `pkill -f tools/seal.py`, three times before your hygiene note. The patterns were not specific to my paths, so they could have hit another worker's same-named tool. Since your note I only stop recorded PIDs (`$G/pids/`).
- I also once briefly checked out 849b86b8 in my own worktree to compare lint at the merge, and restored `wip/g04r6` straight away. That derivation run was discarded and redone.
- If #210's round 6 lands, the re-merge should be trivial. Nothing in this evidence depends on Factoring, HardCorePermutation, Commitment or Universal.

Evidence and tools are in `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/g04r6/`. The main files are `exclusions.md`, `unseal.json`, `sweep-rows.tsv` and `stmtdiff-vs-merge.txt`; superseded runs are in `intermediate/`. New tools there: `closure.py`, `replay.sh`, `collect_head.sh`, `unsealable.py`, `exclusions6.py`, `stmtdiff.py`, `sweeprows.py`, `sealone.sh`, `build.sh`, `leanerr.sh`.
