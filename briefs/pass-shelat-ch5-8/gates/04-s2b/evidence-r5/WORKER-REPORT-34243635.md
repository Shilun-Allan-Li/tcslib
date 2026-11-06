# #195 re-merge on #210 final (head 34243635)

#210's final head 037075b0 is merged into `wip/g04r6`. The seal still passes 26/26 with no entries. Nothing is pushed.

**New head:** `34243635fff25eeb75633bb2419235ab822edd00`. It is a merge commit with parents 4d99b0cb7241b1f431476e1b7cf2f5a551d57d62 (previous head) and 037075b01ca348266d50735cd22526a96fc131bf (#210 final, a fast-forward of 286aee54). The worktree `$SP/wt-g04r4` is clean.

## Conflict resolution
The only conflict was the expected one, in ZeroKnowledge/Interaction.lean (2 hunks):
- **`Protocol.transcriptWith_eq` and `Protocol.outV_eq`:** both sides added each one beside its definition.
  - The statements are identical: same binders and same equation; only the line breaks differ.
  - The docstrings differ. #195 restated the formula; #210 says "The defining equation of …".
  - I kept #210's text and dropped #195's copies. Uses refer to the same names, so nothing needed re-pointing.
- **`Strategy.out_eq`** (#195 only) stays.
- **No other overlap:** the duplicate-name check over the merged files shows no new duplicates. The one hit, `pkEncDist` in PublicKey.lean, is two different namespaces and was already there at 4d99b0cb.
- **Round-5 additions #210 dropped** (`PermFamily.toFunFamily_inLen`/`outLen`, `toFunFamily_codEquiv_symm_ofFn`, `OneWayPermutation.toStrongOneWay`, `NUPPT.wrap_coinLen`): none of the 26 files or Checks uses them.

## Re-run at 34243635
All evidence is in `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/g04r6/`. The previous head's copies are in `at-4d99b0cb/`.
- **Replay** (`r7/replay.log`, `r7/replay-cmp.txt`): the 78 modules of the closure changed since 4d99b0cb, including Checks, all rc=0 with no errors. Sorry counts are unchanged against the previous replay; the 26 files and Checks have no sorry.
- **Seal:**
  - Derivation from an empty seed: `unseal.json` = `{}`, all 26 files resolved.
  - Head seal (`seal-evidence.log`): 26/26 PASS, no named entries.
  - Plain seal (`seal-plain.log`): 26/26 PASS.
  - `PolyExpr.eval` is still dropped from every candidate list (Q1).
- **$BASE control** (`seal-control-base.log`): 10 PASS, 16 FAIL, the same files as before.
- **#210's sweep rows tagged 195** (`sweep-rows.tsv`): all 16 pass the head seal with no entry, and the control fails at each of them.
- **Scan:** head (`scan.log`) has 0 lemma-list hits, 0 show/change steps at seal failures and 0 proof-term equation-lemma references. $BASE (`scan-base.log`) has 84 / 5 / 21.
- **Union check** (`seal-r3union.log`): 5/5 PASS.
- **`exclusions.md`:** no entries in either section.
- **Axioms** (`axioms.log`): 198 public theorems in the 8 files changed since 40553944. All use only propext, Classical.choice and Quot.sound; no sorryAx, 0 errors.
- **Lint** (`lint.log`):
  - style_lint: 0 findings in each changed file and over all 26.
  - check8b: 0 FAIL in Asymptotic, Pseudorandom/Functions, Foundations and Games.
  - ZeroKnowledge shows 9 FAIL. They are the same 9 facade-import rows as at the merge commit, in GraphIsomorphism*/ThreeColoring facades outside the 26.
  - The largest file is PRF.lean at 867 lines, so no size exception is needed.
- **Classifier** (`declchanges.tsv`, against merge base a3c5fa8b): SAME 279, ADDED 210, CHANGED 152, INDUCED 4 — the same counts as at 4d99b0cb.
- **Statement diff against 4d99b0cb** (`r7/stmtdiff-vs-4d99b0cb.txt`): only the two docstring changes on `transcriptWith_eq` and `outV_eq` from the resolution. There are no statement changes, additions or removals.

I stopped no processes this round. All recorded PIDs (`pids/`) have exited.
