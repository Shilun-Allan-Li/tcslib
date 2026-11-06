## E1a report (equation-lemma PR, gate 07)

The work is committed on `wip/eqlemmas-e1a` in `$SP/wt-e1a`, on base `05fe903fc736ac8036c161ad159dc8bdddcd6ee2`. Nothing is pushed. The replay passes with 0 errors and the sorry-warning counts are unchanged. Two problems need a decision from you:

- **`Collections.lean` is over the size limit.** Commit `68de669d…` adds the remaining collection lemmas and takes the file from 997 to 1071 lines. The style lint fails anything over 1000 lines ("must split"). That commit can be dropped on its own.
- **No `TrapdoorCollection.toCollection` constant exists.** The domain-equivalence request named it, but it is the parent projection, so `T.toCollection.D i` and `T.D i` are the same term.

### Commits (oldest first)
1. `aacc40fbc5b59f0d80810920f845f52b03722793`: the equation lemmas, the Closure re-pointing, and the docstring-only 3-colouring lint fixes (19 findings plus the `colProtocol_sound` sketch). Every file stays under the size limit.
2. `d7216c92dc985e98626f96efe1e337b30fe1ae7c`: domain equivalences and field equations for the padded collections in `HardCoreCollection.lean`.
3. `68de669d0b8ac16b74db39a05339b60ad265865a`: the over-limit `Collections.lean` additions:
   - `Collection.hardCore_iff`, `PermCollection.oneWay_iff`, `TrapdoorCollection.oneWay_iff`;
   - `TrapdoorCollection.toCollection_domEquiv` and its `_apply`;
   - `FunFamily.toCollection_domEquiv` with its field equations and `_apply`.
4. `6a4908636a155de6678c68fc4fd04d938571828d`: `glPad_domEquiv_apply` for Collection, PermCollection and TrapdoorCollection. It does not depend on commit 3.
5. `7e259a08781c7a22499bbc55ff623e242ce40aa7`: restates my `Ensemble.uniform_X` as `X n x = cast (uniform_σ ℓ n) x`. The first form, `X n x = x`, only elaborated by reducing the seed type, which the seal probe caught.

The full replay ran on content equal to commits 1–4, and Ensembles' downstream (40 modules) was replayed after commit 5. Commits 1, 2, 4, 5 without commit 3 were not replayed as a separate tree; nothing in the library uses commit 3's lemmas.

### Added declarations
There are 83 in all, every row ADDED in the statement diff. None carries `@[simp]`, all are public, and the proofs are `rfl` / `Iff.rfl` or short same-file proofs. The full one-line statements with file:line are in `$SP/e1/e1a/added-table.md`; raw rows are in `$SP/e1/e1a/decls.tsv`.

| Lemmas | File | Asked for by |
|---|---|---|
| `NUPPT.coinLen_eq`, `advInput_eq`, `runAtL_eq` | `Complexity/Randomized/PPT.lean` | 3col P9, DL, factoring P5, clean-up C, gate 04 §D |
| `NUPPT.layout_eq`, `inParam_eq`, `inArg_eq`, `inAdvice_eq`, `inCoins_eq` | `Complexity/Randomized/Closure.lean` | factoring P5, gate 04 §B/§D |
| `NUPPT.distinguisherL_eq`, `decodeFin_eq` | `Asymptotic/Adversary.lean` | 3col P8, DL, gate 04 §B |
| `statClose_iff`, `firstHit_eq` | `Asymptotic/Sampling.lean` | DL, factoring P3 |
| `Collection.index_eq`, `sampleClose_iff`, `invProbAt_eq` | `Asymptotic/Collections.lean` (commit 1) | factoring P1, DL |
| `Collection.hardCore_iff`, `TrapdoorCollection.oneWay_iff`, `PermCollection.oneWay_iff` (the last is the twin, not requested) | `Asymptotic/Collections.lean` (commit 3) | DL, factoring P2 |
| `FunFamily.easy_iff` | `Asymptotic/OneWay.lean` | factoring P4 |
| `OneWay.yaoTry_eq`, `OneWay.prodFun_apply` | `OneWayFunctions/Amplification.lean` | factoring P8 |
| `Strategy.coinLen_eq`, `Strategy.efficient_iff`, `View.encode_mk`, `Protocol.viewV_withV` | `ZeroKnowledge/Interaction.lean` (additions only) | 3col P4, P12, P6 |
| `ZK_iff` | `ZeroKnowledge/Defs.lean` | 3col P5 |
| `encColoring_eq`, `getD_encColoring`, `getD_encColoring_two_mul`, `getD_encColoring_two_mul_add_one` | `ZeroKnowledge/Encoding.lean` | 3col P3 |
| `ProperColoring_iff`, `R3COL_iff`, `sampleIdx_eq_rejectionSample`, `sampleIdx_ofFn_eq_rejectionSample` (the public tape lemma, proved by the private `sampleIdx_ofFn`) | `ThreeColoring/Language.lean` | 3col P1, P2, P11 |
| `colCommit_eq`, `colOpen_eq`, `colCoinSlice_eq`, `colIterations_eq` | `ThreeColoring/Protocol.lean` | 3col P10 |
| `colProver_coins`, `colProtocol_P`, `colProtocol_V`, `colProtocol_rounds`, `colProtocol_verifierFirst` | `ThreeColoring/Protocol.lean` | 3col P10 |
| `colProver_next_nil`, `colProver_next_cons` (public forms, proved by the private `_of` lemmas), `colProver_next_cons_of_edgeCount_eq_zero` (the edgeless case col-b step 6 needs) | `ThreeColoring/Protocol.lean` | 3col P10 |
| `prgAdv_eq` | `Pseudorandom/Generators.lean` | gate 04 §A/§D |
| `negligible_iff` | `Foundations/Negligible.lean` | gate 04 §A |
| `HardcoreBit.pushesUniform_iff` | `HardcoreBit/Basic.lean` | gate 04 §A |
| `Ensemble.uniform_σ`, `uniform_X`, `pseudorandom_iff` | `Asymptotic/Ensembles.lean` | gate 04 §A |
| `GGMRed.queryOf_eq`, `verdictOf_eq`, `histEnc_eq` | `Asymptotic/GGMReduction.lean` | gate 04 §A/§B |
| `GGMRed.coinStr_eq` | `Asymptotic/GGMReductionEval.lean` | gate 04 §A/§B |
| `PrivateKeyScheme.encodeList_nil`, `multiEncDist_apply`, `multiMessageSecure_iff` | `Asymptotic/Encryption.lean` | gate 04 §A/§B |
| `statDist_eq` | `InformationTheory/StatisticalDistance.lean` | gate 04 §B |
| `Collection.glPad_domEquiv` (a `def`, `Equiv.refl`) with `_apply`, `glPad_encD`, `glPad_decD`, `glPad_f_domEquiv`, `glPad_sample`, `glPad_eval` | `Asymptotic/HardCoreCollection.lean` | domain-equivalence ruling |
| `PermCollection.glPad_domEquiv` with `_apply`, `PermCollection.glPad_perm` | `Asymptotic/HardCoreCollection.lean` | domain-equivalence ruling |
| `TrapdoorCollection.glPad_domEquiv` with `_apply`, `TrapdoorCollection.glPad_inv` | `Asymptotic/HardCoreCollection.lean` | domain-equivalence ruling |
| `FunFamily.toCollection_domEquiv` with `_apply`, `toCollection_encD`, `toCollection_decD`, `toCollection_f`, `toCollection_gen`, `toCollection_sample_eq` (`toCollection_sample` was already taken), `toCollection_eval`; `TrapdoorCollection.toCollection_domEquiv` with `_apply` | `Asymptotic/Collections.lean` (commit 3) | domain-equivalence ruling |

**Re-pointing (proof-only).** In `Closure.lean`, every `simp [runAtL, advInput, coinLen, …]` site now uses the `_eq` lemmas. That covers `exists_compParam`, `exists_comp`, `exists_reparam`, `exists_reparam_advice`, `exists_withAdvice`, `exists_split`, `exists_seq` and `Computes.polyTimeComputable`. `runAtL_eq_output_layout` changed from `rfl` to `rw [runAtL_eq, advInput_eq]; rfl`. Same-file reads of `layout` and `in*` were left as they were.

**Naming.** I used the 3-colouring brief's exact names `ZK_iff`, `R3COL_iff` and `ProperColoring_iff`, even though neighbouring files use lowercase (`proverBounded_iff`). The name `sampleIdx_eq` was already taken by `ColSimMachine.sampleIdx_eq`, so the new lemmas use `_eq_rejectionSample` names.

### Existing lemmas reused (nothing added)
- `NUPPT.runAt_eq` (typed to untyped activation) and `distinguisher_eq`.
- `ofPolyTime` / `ofPolyTimeUniform`: their `coins_`, `adv_`, `advice_`, `output_`, `runAtL_` and `_uniform` lemmas.
- `PolyExpr.eval_var/const/add/mul/pow/normal/subst`.
- `pairEncode_eq`, `pairEncode_eq_dbl`, `pairDecode_pairEncode`, `dbl_nil`, `dbl_cons`, `pairFstD_pairEncode`, `pairSndD_pairEncode`, and `pairFstD_nil` (`ClassNP/PolyTimeBlockLoop.lean`).
- `FunFamily.blocks_apply` and `blocks_symm_apply`.
- `PRG.easy_iff`, `secure_iff`, `ensemble_X`, `ensemble_σ`, `PRG.expand_G`, `PRG.oneBit_stretch`, `PRG.oneBit_G`.
- `GGMRed.coins_ggmRedMachine` and `runAt_ggmRedMachine` (machine contract).
- `PrivateKeyScheme.encodeList_cons`.
- `Collection.glPad_gen` and `glPad_f`; `PermCollection.glPad_toCollection`; `TrapdoorCollection.glPad_toPermCollection`.
- `distAdv_def` does not exist.

### Not done, and why
- **In #195's files, out of scope:**
  - `distAdv_eq` (3col P7, DL), `predProb_eq`, `invProb_eq`, `acceptProb` (`Foundations/Experiments.lean`);
  - `uexp` (`Foundations/Probability.lean`);
  - `NUPPT.toOracleAdversary`, `buildTree`, `decodeOracleMove` (clean-up item D), `encodeHist` (`Asymptotic/PRF.lean`);
  - `QueryTree.eval` (`Pseudorandom/Functions/OracleAdversary.lean`);
  - `ggmBits`, `prefixAt`, `splitHalves` (`Pseudorandom/Functions/GGM.lean`);
  - `prfAdv`, `randomFunction` (`Pseudorandom/Functions/Defs.lean`);
  - re-proving the §A/§B/§D consumer proofs that live in #195's files, including `Interaction.lean`'s `pairFstD_encodeMsgs`.
- **For E1b (Candidates / NumberTheory):**
  - `divModStr_pairEncode`, `xgcdStr_pairEncode`, `sizeStr_eq`, `natToList_eq` (`Candidates/Arithmetic.lean`);
  - `dlP_eq`, `dlM_eq`, `dlG_eq`, `expValid_iff`, `wellFormedIndex_iff`, `safePrimeValid_iff`, `ExpGroupGen.fullLengthExcept_iff`, `dlHard_iff`, `dlProb_eq`, `expF_eq`, and the `expCollection` field equations (`DiscreteLog.lean`);
  - factoring P6 `encodeDistinctPrimes_eq`, `DistinctPrimes.p_eq/q_eq/default_p/default_q` (`Concrete.lean`);
  - factoring P7 `NumberTheory.chunk_apply`;
  - factoring P9–P12 (Arithmetic, Factoring, RSA).
- **For E1b, the generic bridge:** `TrapdoorCollection.toCollection_domEquiv (T) (i) : T.toCollection.D i ≃ T.D i := Equiv.refl _`, with `_apply`. It is in commit 3, so it goes if commit 3 is dropped.
- **About the requested `TrapdoorCollection.toCollection` field equations:** I did not add them. Because `toCollection` is the parent projection, they would restate `T.f`, `T.encD` and so on as themselves. The concrete instance in my files is `FunFamily.toCollection`, and its equivalence and field equations are in commit 3.
- **Kept out of commit 1 by the size limit:** `Collection.hardCore_iff` and `TrapdoorCollection.oneWay_iff` could not fit under 1000 lines (`Collections.lean` was at 982), so they are in commit 3. `Protocol.lean` ends at 999 and `Machines.lean` at 997; I wrote their new docstrings compactly to stay under.
- **Not touched:** the 6 pre-existing facade FAILs on `ThreeColoring.lean` (outside my brief).

### Existing statements that only elaborate because a domain `D` reduces
These were found by re-elaborating the files with the definitions marked irreducible. I did not restate them.
- **`PublicKey.lean` (cross-file reads):** `TrapdoorCollection.OneWay.glPad_tdpBitScheme_singleBitSecure` and `TrapdoorCollection.OneWay.exists_glPad_singleBitSecure`. Both state `(T.glPad m henc).toCollection.PredEvaluator T.glBit`, where `T.glBit` is typed on `T.D i × …`.
- **`HardCoreCollection.lean` (the defining file):** `Collection.OneWay.glPad_hardCore`, `goldreich_levin_coll`, `PermCollection.OneWay.glPad_hardCore`, `TrapdoorCollection.OneWay.glPad_hardCore` (`… .HardCore F.glBit`). `glPad_f` and `glPad_decD_eq` also have statements that read `z.1` / `Option (F.D i × …)` on the padded domain.
- **`FunFamily.toCollection`:** none outside its own file, and no existing statement in the file depends on it.

### Check results (logs in `$SP/e1/e1a/`)
1. **Replay.** All 116 downstream modules plus `audits/pass-shelat/Checks` pass with 0 errors (`replay.log`; the Ensembles re-replay is `replay2.log`). Sorry warnings appear only where the base has them. In the changed files the `sorry` tokens are equal to the base (only `Protocol.lean`, 2 = 2; `sorry-tokens.log`). Base counts for unchanged modules come from identical source, not from a separate base build.
2. **Axioms.** All 83 new declarations print only standard axioms (`[propext, Classical.choice, Quot.sound]` or a subset, or none); there is no `sorryAx` (`axioms.log`).
3. **Lint.**
   - `style_lint.py` on the 24 changed files goes from 24 findings at base to 5 at head (`lint.log`). Four are the pre-existing `StatisticalDistance` docstring findings, shifted 3 lines; the fifth is the new `Collections.lean: 1072 lines` from commit 3.
   - `campaign_style_lint.py --check8b`: no new FAIL; check-8 WARN lists only shrink. The 4 `Machines.lean` FAILs are gone. The one new WARN is `Collections.lean` over 1000 lines, from commit 3 (`check8b-diff.log`).
4. **Statement diff.** `decls.py` shows 83 ADDED rows, 0 CHANGED, 0 REMOVED (`decls.tsv`). There are no new duplicate full names (`dup-base.txt` and `dup-head.txt` are identical).
5. **Seal probes (`probes/`).**
   - `Seal.lean`: 50 sealed readings across 16 groups pass through the new lemmas (`probe-Seal.log`, rc 0).
   - `Control.lean`: all 51 controls (unfold by `rfl`, anonymous constructor or direct application) fail sealed, 55 errors (`probe-Control.log`).
   - `ControlOpen.lean`: the same controls pass unsealed (`probe-ControlOpen.log`, rc 0).
   - `SealClosure.lean`: head `Closure.lean` compiles with `runAtL`, `advInput`, `coinLen`, `runAt` sealed (rc 0). The base copy fails at the `runAtL_eq_output_layout` `rfl` (`probe-SealClosureBase.log`).
   - Domain probes (`probes/dom/*.lean` and `.log`, tool `probes/domprobe.py`) produced the statement list above.

### Changes to existing declarations
Only those authorized: docstrings for the 19 3-colouring lint findings (adding `## Main definitions`, **Proof sketch.** paragraphs, and docstrings for `countTrue_zero/succ` and `natOfBits_zero/succ`), the `colProtocol_sound` sketch, and the proof-only re-pointing in `Closure.lean`.
