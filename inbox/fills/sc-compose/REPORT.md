# Fill `sc-compose` · checkpoint 2 · `hbcSecure_compose`, sketch steps 1–2

**Worker** Claude. **Unit** `sc-compose` ([Gol04, §7.3.1, Theorem 7.3.3], the semi-honest composition
theorem). **Issue base** `107f1e8c218733eac12d6b9bee6fece441271317` (`cryptography/pass-shelat-ch2-4`), read from the
exchange at `2b9270ad095e993b020cb5e447d5a0043496802a` (pack 7/7 and SOURCE 152/152 verified:
`evidence/logs/inputs-check.log`). **Proof branch** `fill/sc-compose` (local), eight commits over the base:

| commit | content |
|---|---|
| `a3cb219da2a068f36661608e5019086c313bc021` … `32f837d9edcd5ae1991f6bef39a5ad69e1af77f5` | checkpoint 1 (four commits, delivered at exchange `419c4ceb9`) |
| `2d99291eb5a7ccec799c7fe41e00ca03fcef159e` | eight helper modules: the simulators, the output clause, the statistical switch |
| `5b90f0dac8283702801915460ff1eae51bd036df` | reuse the published `acceptProb_fst`, `uprob_fst`, `uexp_mono`, `uexp_const`, `pushesUniform_eval` (my restatements removed; found by the overlap search) |
| `687f64a9166c4659e5fd49e128f4fbd2780e3be7` | the `## Contents` line of `Probability.lean` |
| `392a95ecb62936dc09a91e11037a20840e64ef5a` | `_eq` readers of `appendCoins`, `blocksCoins`, `splitCoins` (lint check 8) |

## Status of the targets

| target | status |
|---|---|
| `composeP_efficient` | **proved** (checkpoint 1; `propext`, `Classical.choice`, `Quot.sound`) |
| `composeV_efficient` | **proved** (checkpoint 1; same axioms) |
| `hbcSecure_compose` | open at this checkpoint (`sorry`, statement unchanged): steps 1–2 delivered here as helper lemmas; steps 3–5 and the assembly come with the final delivery |

No statement was changed; no ℓ-output PRF is built or needed.

## Changed files

| file | base | now | change |
|---|---|---|---|
| `SecureComputation/ComposeSecurity.lean` (owned) | 382 | 429 | imports the eight new helpers; `## Contents` lists them. Title, sketches and statement prose unchanged at this checkpoint (the title keeps "(statement phase)" until `hbcSecure_compose` is proved) |
| `ComposeSecurity/Probability.lean` (new) | — | 123 | the statistical switch, fixing coordinates, negligible times polynomial |
| `ComposeSecurity/Reductions.lean` (new) | — | 106 | machines with advice-dependent pre-/post-processing and extra coins |
| `ComposeSecurity/Assembly.lean` (new) | — | 284 | the assembled view of the composed protocol from run views (`asmView`, word form `asmW`) |
| `ComposeSecurity/Runs.lean` (new) | — | 604 | the coins run by run (`composeCoins`), `GoodRuns`, the real samples under `GoodRuns` |
| `ComposeSecurity/Bounds.lean` (new) | — | 96 | lengths of encodings, transcripts, machine outputs |
| `ComposeSecurity/Sim.lean` (new) | — | 249 | the post-processing `Φ` (`phiV`, `phiD`), the simulator and the reduction to the hybrid model |
| `ComposeSecurity/Accept.lean` (new) | — | 192 | coin splittings, acceptance with pre-/post-processing, test machines |
| `ComposeSecurity/Correct.lean` (new) | — | 204 | the output clause: correctness of a secure protocol, the union bound over the runs |

## Steps 1–2 of the proof

1. **The simulator** (`ComposeSim.exists_simulator`, `Sim.lean`). `phiV` reads the hybrid simulator's output as a
   view `⟨⟨1^n, ⟨x, a⟩⟩, ⟨r_main, me⟩⟩` of `main`, recomputes the call inputs `fcall ⟨1^n, ⟨x, ⟨r_main, 1^j⟩⟩⟩` for
   `j < calls(n)` (the `callA`/`callB` clause of `H.PolyTime`), runs `S^ρ` on each with the `j`-th
   `G.outA(n)`-bit block of `a` and the `j`-th coin block (`simV`, `vlW`), and assembles the view of `H.compose ρ`
   (`asmView`: the `main`-tape followed by the run tapes cut or padded to `ρ`'s coin length, the run messages at
   the pairs where the other party moves with fillers, the leading fillers, the main phase). `phiV` is
   polynomial-time (`polyTimeComputable_phiV`), and `exists_post` (`Reductions.lean`) packages
   `S^H` followed by `phiV` as a non-uniform PPT with coins `S^H.coins + calls · S^ρ.coins` and advice
   `⟨S^H.advice, S^ρ.advice⟩`. `phiV_view` evaluates `phiV` on a view of `main` with common input `1^n`.
   The same `phiD` before a distinguisher is the reduction to the hybrid model (`exists_dPhi`, used at step 4).
2. **The output clause with worst-case advice** (`ComposeProb.exists_correct`, `Correct.lean`). For each `n` the
   inputs `w_n` maximizing `Pr_t[ρ.outP ≠ ⟦f_A⟧]` are chosen, and the test machine `exists_test` with advice
   `⟦f_A(w_n)⟧` (`G.outA(n)` bits) accepts a sample exactly when its second component is the advice
   (`BinArith.eqW`). On Bob's ideal sample at `w_n` it accepts with probability 1; on the real one with
   `Pr[outP = ⟦f_A(w_n)⟧]` (`acceptProb_test`). So `Pr_t[outP ≠ ⟦f_A⟧] ≤ 1 − Pr[outP(w_n) = ⟦f_A(w_n)⟧] ≤ ε_A(n)`
   for all inputs (uniformity: one machine, `ε` before the inputs). Likewise for `outV` through Alice's
   samples; `ε_c = ε_A + ε_B`.
3. **The statistical switch** (`ComposeProb.distAdv_le_uprob_of_eq`, `HybridProtocol.uprob_not_goodRuns_le`,
   `realA_compose_eq`, `realB_compose_eq`). The composed coins are the `main`-tapes and one pair of `ρ`-tapes per
   call (`composeCoins`, an equivalence). `GoodRuns m t` says every run's outputs on the call inputs and the
   tapes `t j` are the ideal answers. Under it, the honest answers are the ideal ones (`answersRealA_eq_answersA`,
   `padFin` read back by `ofFn_padFin`, `padTo_of_length`), the main phase is the hybrid execution on the
   `main`-tapes (`mainExec_composeCoins`), and Alice's real sample is
   `⟨asmView … (real run views) …, Bob's output in main⟩` (`realA_compose_eq`, with `compose_viewP`,
   `compose_outV` and `hM`); Bob's likewise with the leading fillers (`realB_compose_eq`). The tape cut is exact
   on real views, so `asmView` reproduces the real tape. `¬ GoodRuns` has probability at most
   `calls(n) · ε_c(n)` (union bound over the calls; each run's event concerns `t j` only:
   `HardcoreBit.pushesUniform_eval`, `uprob_prod`, `uexp_mono`, `uexp_const`): this is the brief's
   `2L(n)ε₁(n)` with `ε_c = ε_A + ε_B`.

Edge cases: `L(n) = 0` (empty concatenations; the union bound is `0`); `ρ.rounds(n) = 0` (empty run chunks:
`segW` over `range 0`); the fillers (`segW` puts `⟨[], []⟩` at the pairs of the receiving party, `asmView`
inserts `encodeMsgs [[]]^lead`); the tape cut lengths (exact on real views, `padTo_of_length`); `hM` (used in
`realA_compose_eq`/`realB_compose_eq` through `compose_outV`/`compose_outP`).

## New declarations (checkpoint 2)

- `Probability.lean` (`ComposeProb`): `abs_uprob_sub_le`, `distAdv_le_uprob_of_eq`, `acceptProb_eq_uexp_sections`,
  `exists_abs_uexp_sub_le`, `exists_abs_sub_le_sections`, `negligible_polyExpr_mul`.
- `Reductions.lean` (`ComposeSim`): `exists_pre`, `exists_post`.
- `Assembly.lean` (`ComposeSim`): `moverIsV_beq_iff`, `length_filter_mod_two`, `length_filter_mover`,
  `getD_filter_map_mover`, `padTo_of_length`, `flatMap_range_congr`, `segW` (+`segW_eq`), `segW_encodeMsgs`,
  `asmView` (+`asmView_eq`), `asmView_congr`, `asmW` (+`asmW_eq`), `asmW_pairEncode`, `polyTimeComputable_segW`,
  `polyTimeComputable_asmW`.
- `Runs.lean`: `ComposeSim.splitCoins` (+`splitCoins_eq`), `ofFn_blocks_symm`, `ofFn_splitCoins`,
  `take_ofFn_splitCoins`, `runTape_ofFn_splitCoins`, `flatMap_range_mul`; `HybridProtocol.composeP_coinLen_eq`,
  `composeV_coinLen_eq`, `composeCoins`, `composeCoins_fst`, `_snd`, `ofFn_composeCoins_fst`, `_snd`, `inA`
  (+`inA_eq`), `inB` (+`inB_eq`), `ofFn_callA_congr`, `ofFn_callB_congr`, `runInputA_composeCoins`,
  `runInputB_composeCoins`, `runExec_composeCoins`, `runMsg_composeCoins`, `GoodRuns` (+`goodRuns_iff`),
  `answersRealA_eq_answersA`, `answersRealB_eq_answersB`, `mainExec_composeCoins`, `realViewA` (+`_eq`),
  `realViewB` (+`_eq`), `realA_compose_eq`, `realB_compose_eq`.
- `Bounds.lean` (`ComposeBound`): `length_transcriptWith_fst_le`, `_snd_le`, `length_encodeMsgs_le`,
  `length_layout`, `length_runAt_le`, `Efficient.length_next_le`, `length_ilayout`.
- `Sim.lean` (`ComposeSim`): `simV` (+`simV_pairEncode`), `vlW` (+`vlW_eq`), `phiV` (+`phiV_eq`), `phiV_view`,
  `phiD` (+`phiD_pairEncode`), `polyTimeComputable_simV`, `_vlW`, `_phiV`, `_phiD`, `exists_simulator`, `exists_dPhi`.
- `Accept.lean` (`ComposeProb`): `appendCoins` (+`appendCoins_eq`), `ofFn_appendCoins`, `take_ofFn_appendCoins`,
  `drop_ofFn_appendCoins`, `blocksCoins` (+`blocksCoins_eq`), `ofFn_blocksCoins`, `coinBlock_blocksCoins`,
  `acceptProb_pre`, `acceptProb_post_pre`, `acceptProb_test`, `exists_test`.
- `Correct.lean`: `ComposeProb.exists_correct`; `HybridProtocol.inA_val`, `inB_val`, `uprob_not_goodRuns_le`.

Every new public `def` has its `_eq` reader (the defining equation, or the evaluation lemma `simV_pairEncode`,
`phiD_pairEncode` for the word functions); every new declaration has a docstring with its formula; no `@[simp]`.

## Overlap and reuse

Searches: `evidence/overlap/dupsearch-base-cp2.log` (tool `evidence/tools/dupsearch.sh`, patterns for every new
name and statement shape, run on a checkout of the issue base), plus a scan of the published lemma lists of the
modules in the permitted import closure (`Foundations/Probability`, `Experiments`, `Asymptotic/Sampling`,
`Adversary`, `HardcoreBit/Basic`, `OneWayFunctions/Basic`, `Pseudorandom/Indistinguishability`). That scan found
four published equivalents of lemmas I had written; commit `5b90f0dac` removed mine and uses the published ones:
`acceptProb_fst` (`Pseudorandom/Indistinguishability.lean:73`, was my `acceptProb_seed_fst`), `uprob_fst`
(`Foundations/Probability.lean:175`, was my alias `uprob_fst_eq`), `HardcoreBit.uexp_mono`/`uexp_const`
(`HardcoreBit/Basic.lean:83,71`, was my `uexp_le_of_le`), `HardcoreBit.pushesUniform_eval` with
`PushesUniform.uprob_eq` (`HardcoreBit/Basic.lean:250,184`, was my `uprob_coord`).

Reused rather than restated (besides those): `coinBlock`, `coinBlock_flatten`, `FunFamily.blocks`,
`FunFamily.blocks_symm_apply`, `ofFn_arrowCongr_finCongr`, `padFin`/`ofFn_padFin` (`Asymptotic/Adversary.lean`),
`acceptProb_comp_equiv`, `uprob_prod`, `uprob_exists_le`, `uprob_or_le`, `uprob_not`, `BinArith.eqW`,
`BinArith.length_encWords_le`, `NUPPT.ofPolyTime` and the layout projections (`Closure.lean`),
`GI.coinSlice_poly`, `GI.ilayout`, `Negligible.mul_pow`/`const_mul`/`add`, `PolyExpr.eval_le`.

| new declaration | nearest relative | relation, and why not reused |
|---|---|---|
| `abs_uprob_sub_le`, `distAdv_le_uprob_of_eq` | `FromPRF/HybridLemmas.lean:61` `abs_uexp_sub_le_uprob`; `Asymptotic/Sampling.lean:138,249` `StatClose.abs_uprob_sub_le`, `distAdv_le_of_statClose` | same idea ("agree off `E`") for averages of `[0,1]`-valued functions; `FromPRF*` is named frozen and outside the permitted imports. `StatClose` needs a distance bound for every test; here the bound is the bad event of one seed space. New. |
| `acceptProb_eq_uexp_sections`, `exists_abs_sub_le_sections`, `exists_abs_uexp_sub_le` | `ZeroKnowledge/CommitmentLemmas.lean:79,92` `exists_abs_uexp_le`, `acceptProb_eq_uexp_fst`; `Pseudorandom/Indistinguishability.lean:91` `acceptProb_bind` | the averaging over a fixed seed factor (Commitment: over a coin factor; mine: over the first seed factor; `exists_abs_uexp_le` is the one-function form). `CommitmentLemmas` is outside the permitted imports. Restated. |
| `negligible_polyExpr_mul` | `Asymptotic/ReductionSupport.lean:267` `Negligible.polyExpr_mul`; `Asymptotic/EnsemblesLemmas.lean:377` `negligible_polyExpr_mul` | same statement; neither module is in the permitted closure. Restated (promotion request below). |
| `exists_pre`, `exists_post` | `Complexity/Randomized/Closure.lean:272,358,390,421` `exists_comp`, `exists_withAdvice`, `exists_split`, `exists_seq`; `Asymptotic/ReductionSupport.lean:148,318` `wrap`, `preComp` | the closure catalogue gives the pieces; these combine advice-dependent pre/post-processing with extra coins in one `ofPolyTime` of the layout, as `ReductionSupport.wrap` does (not importable). New. |
| `splitCoins`, `appendCoins` (+ readers) | `Asymptotic/EnsemblesLemmas.lean:141` `coinsEquiv` (= `appendCoins`); `ZeroKnowledge/Encryption.lean:201` (the same split inline) | not importable; restated. `splitCoins` is `appendCoins` after `blocks` on the second factor (two of my declarations, in two files because `Accept.lean` imports `Runs.lean`). |
| `ofFn_blocks_symm`, `blocksCoins`, `ofFn_blocksCoins`, `coinBlock_blocksCoins` | `Asymptotic/OneWay.lean:380` `FunFamily.ofFn_blocks_symm` (same statement); `EnsemblesLemmas.lean:433`; `Adversary.lean:277` `FunFamily.ofFn_blocks` (the forward direction, importable); `Authentication/Signatures/Lamport.lean:132` `coinBlock_flatten_ofFn` | `OneWay`, `EnsemblesLemmas`, `Lamport` are outside the permitted closure; the importable `FunFamily.ofFn_blocks` is the other direction. Restated (promotion request). |
| `flatMap_range_mul` | `ZeroKnowledge/ThreeColoring/Machines.lean:516` (`range (n·3)`) | specialization there; not importable. New general form. |
| `acceptProb_pre`, `acceptProb_post_pre` | `Pseudorandom/Indistinguishability.lean:91` `acceptProb_bind`; `Encryption/PublicKey/HybridMachine.lean:397` `acceptProb_distinguisherL_coins`; `ReductionSupport.lean:221`, `EnsemblesLemmas.lean:85` `acceptProb_coins_equiv` | the coin relabelling plus `acceptProb_bind`'s reassociation for a machine whose coins split as `p(n) + D.coins`; the relatives are not importable except `acceptProb_bind` (whose distinguisher coins are already a product). New. |
| `acceptProb_test`, `exists_test` | `Adversary.lean:440` `computes_iff_uprob` | different statement (deterministic output with probability 1). New. |
| `exists_correct`, `uprob_not_goodRuns_le` | none found (`rg 'outP.*≠|outV.*≠|correct'`) | new. |
| `length_encodeMsgs_le` | `BinArith.length_encWords_le` (`ClassP/BinaryArith/Words.lean:81`) | proved from it through `encodeMsgs_eq_flatMap` (the history encoding is `encWords`). |
| `length_runAt_le`, `Efficient.length_next_le` | `NUPPT.output_length_le`, `PolyTimeComputable.output_length_le` | instances on the activation layouts. |
| `length_transcriptWith_fst_le`, `_snd_le`, `length_layout`, `length_ilayout` | `PPT.lean:217` `length_advInput` | none for these; new. |
| `padTo_of_length` | `Adversary.lean:216` `ofFn_padFin_of_length` | the same fact for my `padTo` (checkpoint 1). |
| `moverIsV_beq_iff`, `length_filter_*`, `getD_filter_map_mover`, `segW`, `asmView`, `asmW`, `simV`, `vlW`, `phiV`, `phiD`, `composeCoins`, `GoodRuns`, `realView*`, `inA`, `inB` and their lemmas | `Compose.exec_eq_map`, `compose_viewP`, `compose_outV` (read through) | new (the composition-specific layer). |

## Scope requests

None.

## Promotion requests (in addition to checkpoint 1's)

- `negligible_polyExpr_mul`: one copy for the library (three now: `ReductionSupport`, `EnsemblesLemmas`, here), in
  `Foundations/Negligible.lean`.
- `appendCoins`/`blocksCoins`/`ofFn_blocks_symm`/`coinBlock_blocksCoins`: beside `FunFamily.blocks` in
  `Asymptotic/Adversary.lean` (and let `EnsemblesLemmas.coinsEquiv` and `OneWay`'s `FunFamily.ofFn_blocks_symm` use
  them).
- `distAdv_le_uprob_of_eq`, `exists_abs_sub_le_sections`, `acceptProb_pre`, `acceptProb_test`: to
  `Foundations/Experiments.lean` / `Asymptotic/Adversary.lean` beside `acceptProb_comp_equiv` and `distinguisherL`.

## Checks

- **Order** (`evidence/cp2/order-cp2.txt`, `reorder.log`): `order.txt` with the ten helpers inserted before their
  consumers (162 modules).
- **Sweep** (`evidence/cp2/`): **162/162 exit 0, 0 error diagnostics** (`sweep-errors.txt`, counted with
  `^\S+\.lean:\d+:\d+: error[:(]`; `sweep.tsv`, logs `sweep/`). History in `sweep-run.log`: started at
  `2d99291eb`; I stopped it after 34 rows (modules no commit touches) for the reuse commits and resumed at
  `687f64a91`; after it finished, the lint's check 8 asked for the `_eq` readers of `392a95ecb`, so the rows of
  `Runs` and of the six modules after it were moved to `sweep-superseded.tsv` (their logs to
  `sweep-superseded/`) and re-checked at `392a95ecb`. Every row's module is identical at `392a95ecb`.
- **Sorry census** (`evidence/cp2/sorry-census-cp2.txt`): 29 declarations in 14 modules; the only change from the
  base census is the removal of `composeP_efficient` and `composeV_efficient` (unchanged since checkpoint 1).
- **Axioms** (`evidence/axioms/axioms-cp2.log`): all 191 stored constants of the owned file and the ten helpers use
  only `propext`, `Classical.choice`, `Quot.sound`, except `hbcSecure_compose` (`sorryAx`, open);
  `composeP_efficient`, `composeV_efficient`, `polyTime_compose`: `[Classical.choice, Quot.sound, propext]`.
- **Statement check** (`evidence/headers/headers-cp2.txt`): 11 → 11 base declarations, headers, `omit … in` lines
  and statement prose byte-identical: **0 differences**; control (`control-cp2.txt`): one altered character →
  exactly one difference.
- **Width and size** (`evidence/checks/widths-cp2.txt`): no line over 100 characters; files ≤ 1000 lines.
- **Sketches** (`evidence/checks/sketches-cp2.txt`): every proof of 15 lines or more has a `**Proof sketch.**`
  paragraph; the one flag is the definition `runW` (a body, as at checkpoint 1).
- **Lint** (`evidence/lint/lint-cp2.txt`, `lintdiff-cp2.txt`): 92 FAIL / 101 WARN, line sets equal to the base's:
  **no new FAIL, no new WARN, none gone**.
- Seals, controls and the unfold scan come with the final delivery (base and final).

## Next

Final: steps 3–5 (the hybrid argument over the runs with the worst-case template as advice, the reduction to
`H.HBCSecure F` through `Φ`, the total `L(n)(ε_c(n) + ε₂(n)) + ε₃(n)`). They are written and compile locally
(five more helpers), with `hbcSecure_compose` proved from Alice's and Bob's sides on the standard axioms; the
final delivery brings them with the full evidence.

## Patches and reproduction

`patches/0001…0008-*.patch` and `patches/COMMITS.tsv`; a scratch clone at the issue base applies the series with
`git am`, the committer of each row set from `COMMITS.tsv`, and reproduces every hash and the tree
(`evidence/amcheck/amcheck-cp2.log`).

## Evidence

`evidence/SHA256SUMS` covers every evidence file (inputs, raw logs, tools, probe sources); the top-level
`SHA256SUMS` covers every delivered file except itself; both checked against the delivered paths.
