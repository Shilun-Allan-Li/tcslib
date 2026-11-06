## #210 round 6c: report

Round 6c is done. Across all 70 files #210 now changes, there are no (a) hits left: (a) = 0, (b) = 764. The (b) rows cover 468 untouched declarations.

**New head of `wip/eqlemmas`: `3436321ba28042549bead976dc654aab3d661f10`.** It is one commit on top of 6b (`037075b0…`), and it is not pushed (the branch shows `ahead 1`).

**The PR now has 70 files, not 68.** Round 6c put new equation lemmas into two files #210 had not touched before: `HardcoreBit/PairwiseIndependence.lean` (`subsetSum_eq`) and `ZeroKnowledge/GraphIsomorphism.lean` (`giProtocol_eq`, `giProver_coins`). All counts below are over the 70 files. Measured against `05fe903f`, 547 declarations are touched.

**Final evidence at `3436321b`:**
- **Proof seal:** the whole-file seal, proofs included, ran on all 70 files with `PolyExpr.eval` left unsealed. No error lands in a touched declaration.
- **Explicit-unfold scan:** it covers 446 `unfold`/`rw`/`simp` hits and 53 references to generated equation lemmas. None is in a touched declaration.
- **The two DL proofs are (b):** #210 doesn't touch either one.
  - Concrete `primesPairEquiv_apply_val`: seal error at line 338.
  - DiscreteLog `ExpGroupGen.FullLength.exists_fullLengthExcept`: seal errors at lines 442–443.
- **Control:** I ran the same seal on the 6b copies of the 18 files 6c changed. It finds 26 (a) hits there, and all 26 are gone at head. Examples: the Closure `exists_*` lemmas, `OneWay.glPad`, the PublicKey `tdp*` lemmas, GI `sim_ofFn_eq`, `viewV_encode`, `statClose_real_ideal`, and 3-colouring `exists_colSimRed_ge` / `exists_hybRed_ge`.
- **Replay:** all 81 modules downstream of the 18 changed files rebuilt, plus `audits/pass-shelat/Checks`. Every module returned rc=0 with 0 errors. Sorry counts match the previous replay. Every warning other than sorry was already there in 6b.
- **Axioms:** I checked the 47 public declarations 6c added or changed. All use only the standard axioms, with no `sorryAx` and no errors.
- **Statement diff:**
  - Against 16a7d02d: 112 ADDED, 37 CHANGED, 2 REMOVED.
  - Against 05fe903f: 367 ADDED, 58 CHANGED, 2 REMOVED.
  - Against 6b: 17 ADDED. The only CHANGED entry is `glNeed`, which went from `def` to `abbrev` with the same statement.
- **Lint:**
  - `style_lint`: the only findings are the two approved oversize files, Collections (1141 lines) and PublicKey (1070). `GraphIsomorphism.lean` is at 993 lines.
  - `check8b`: no new findings, and five "def without a lemma" lists got shorter.
  - No added line is over 100 characters.

**What 6c changed:**
- **New published lemmas, each beside its definition:**
  - `guessRecover_apply`, `guessCoinsCongr` (+ `_apply`), `guessRecover_coinsCongr`
  - `glPad_apply`, `glInverter_apply`, `subsetSum_eq`, `invProbOpt_def`, `glPredictorOf_apply`
  - `hybStd_eq`, `hybGen_eq`, `giProtocol_eq`, `giProver_coins`, `GIZK.sim_eq`
  - `Collection.evalSampled_iff`, `Collection.glPad_index`, `Collection.glPad_invProbAt`
- **Proofs fixed:** the (a) proofs in Closure, Concrete, Collections, HardCoreGL/GLColl/GLFamily, HardCoreCollection, PublicKey, and the GI and 3-colouring ZK files. They now go through published lemmas such as `Computes.runAt_eq`, `layout_eq`, `distAdv_def`, `acceptProb_def`, `predProb_def`, `negligible_iff`, `sampleClose_iff`, `hardCore_iff`, `oneWay_iff`, `blockLen_eq` and `withV_vCoinsEquiv_ofFn`.
- **Unused-variable warnings:** I added `omit [Fintype …] in` to 6c's new lemmas and to three 6b equation lemmas (`guessInverter_eq`, `perfectInverter_eq`, `majorityInverter_eq`). Each of those lost an instance argument it never used.
- **One extra file:** fixing those warnings also touched `HardcoreBit/ThreeQuarters.lean`.

**I fixed three bugs in my own tools, and they change the counts:**
- **Declaration comparison:** a trailing `variable … in` or `end …` line was being counted as part of the declaration above it. Seven declarations were therefore wrongly marked as touched. They match the base exactly and are now (b): `glPad_decD_eq` (its `unfold glPadDecode` is now a (b) row), `TrapdoorCollection.OneWay.glPad_hardCore`, `PermFamily.toFunFamily_f`, `yaoB`, Concrete `default`, `prodFun` and `yaoTry`.
- **Name matching:** the (a)/(b) step now matches exact namespace-qualified names. Before, it matched on name suffix, so `PermCollection.OneWay.glPad` counted as touched because `OneWay.glPad` was.
- **Error attribution:** an error reported at a docstring now goes to the declaration that docstring documents. Before, an `adv_ofPolyTime` error was being attributed to `coinsEquiv_ofPolyTime_ofFn`.

**Ruling question:** I made `glNeed` (HardCoreGL) an `abbrev`, reading it as notation for a length abbreviation, like `PolyExpr.eval`. Without that, a coin type in `invProbOpt_glFam_eq` needs `glNeed` to reduce. If that reading isn't accepted, it needs an equation and a coin equivalence instead.

I left the untracked `Probe/` directory in the worktree alone; I didn't create it. Every process I started has finished or was stopped by its recorded PID.

Everything is in `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/e1/final6c/`:
- `final-checks.log`, `classified.tsv`
- `cleanup-b.tsv`, `cleanup-b-decls.tsv` (the (b) clean-up list)
- `proofseal/all.out`, `scan.log`, `touched.tsv`
- `control/` (the 6b control run)
- `replay-head.log`, `full-head/`
- `probes/Axioms6c.log`
- `decls.tsv`, `decls-vs-05fe903f.tsv`, `decls-6c.tsv`
- `style-lint-head.log`, `check8b-diff.log`
