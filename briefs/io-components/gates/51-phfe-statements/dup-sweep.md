# Gate 51 · duplication sweep (maintainer, static)

Static sweep of the io-phfe checkpoint-0 statements (`inbox/fills/io-phfe/src/` at exchange
`1e77173a7032b57aa22260787711c6c7a1b7596e`, source HEAD `70b85f9ba83f27393d98fa5bf88505aea3d22a8d`)
against TCSlib at the base `5ed465f62e4ae0f93ded1a1ba49e807591b589eb` and Mathlib `029db123`.
No Lean was run: the sweep is by name, by `git grep` of the base and by reading. The gate confirms
it with `exact?`/`apply?` probes where it doubts a row. `FE/` is
`TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/`.

The rule (prompt §8; `briefs/pass-shelat-ch5-8/duplication-ledger.md`): an undisclosed re-proof or
restatement of a public TCSlib or Mathlib lemma, including an inline re-derivation, is a **major**.
A disclosed near-copy with a promotion request is a minor at most.

## 0. Searches

- Declarations: the 1,171 written declarations of `evidence/logs/m0-decls2-final.tsv` (1,003 short
  names) against the 29,724 short names declared under `TCSlib/` at the base. 34 short names
  coincide (`Commitment`, `Correct`, `encode`, `setup`, `keyGen`, `realView`, `run`, `shift`,
  `xhat`, …); all are in different namespaces, and the delivery's clash scan
  (`evidence/clash-m0-final/clash.tsv`) finds no full-name clash. No unqualified use was found to
  change resolution (the new files `open` only their own namespaces and `Complexity`, `Turing`,
  `Games`, `Pairing`, `CoinSampling`).
- Concepts, by `git grep` at the base: `DLIN|dlin|MDDH|mddh|MatrixDH` (none outside a comment in
  `Asymptotic/Realization.lean:76`); `runDet|evalDet|detRun|detImpl` (none in `Games/`; unrelated
  `runWith` in circuit and TM files); `first : NUPPT|second : NUPPT|TwoStage` (none);
  `PartialGarbling|pgb|semi.?adaptive|SASim` (none); `PublicParams|GroupDescription|g ≠ 1`
  (only the inline `{x // x ≠ 1}` draw of `BilinearGen.dbdhGame`, `Pairing/Assumptions.lean:225`);
  `foldr pairEncode` (four base uses, and `EnsembleSecurity.encodeList`).

## 1. Must-reuse items (`duplication-sweep-r2.md` as amended by `-r3.md`)

| Item | Used | Remark |
|---|---|---|
| `Complexity.NUPPT.RealizesOn` and readers; `exists_realizesOn_of_preTarget_id` | yes (60 uses; the latter in `mddhRealizable_of_preTarget`) | no local variant |
| `CoinSampling.SamplesEfficiently` (`DrawSamplable`, `CoreComputable`) | yes (30 uses) | no local `SamplerEfficiency.lean`; `UniformSampler`/`CoinSampler` reached only through the contract; no sampler built |
| `Foundations/Subexponential` (`SubexpSmall`, `SubexpHard`, `Negligible.add`) | yes | `SubexpSimSecureWith.simSecureWith` etc. are glue over `SubexpSmall.negligible` (sketches say so) |
| `bitSpec`, `bitCodec`, `MachineCodec`, `buildComp`, `toCompOn`, `decAnswer` | yes | `saSpec`/`saCodec` instantiate them; `toSAAdv_run` relates to `toCompOn` |
| `IBEScheme.sidImpl` pattern (case lemmas, `_onSpec`) | yes (pattern) | `saImpl_zero_onSpec`, `saImpl_one_onSpec` |
| `expect_simulate_rel` | yes | `prob_simulate_rel`, `expect_sample_rel` unused so far (proof stage) |
| `exists_expect_sample_le`, `abs_expect_sub_le_expect` | yes | imported from `Authentication/Signatures/Lamport/Averaging` |
| `ProbComp.expect_sample_equiv`, `Equiv.addRight` | yes | layered privacy, Lemma 3 |
| `Fin.snoc`, `Fin.init`, `finFunctionFinEquiv`, `finSigmaFinEquiv`, `finProdFinEquiv`, `finSumFinEquiv` | yes | `tupleCoord` is a named alias of `finFunctionFinEquiv` (glue, `rfl` reader) |
| `Matrix.kroneckerMap`, `Matrix.card_GL_field` | yes | |
| `Encoding.Modular.encodeVector`/`encodeMatrix`, `ModularDecode.decodeVector` | yes | `decodeResidues` wraps `decodeVector` |
| Not to use: `PolyHandler`, `exists_handlerMachine`, `BB1Machine.draw`, `Games.Closeness`, other `CoinSampling` modules, `Pairing/Assumptions` | not used | `BB1Machine.order_le_two_pow` is used (S1) |

## 2. Items

| # | Where (delivery) | Nearest existing | Disclosed? | Grade |
|---|---|---|---|---|
| **S1** | `Pairing/MatrixDH/SelfReduction.lean:11` imports `AdvancedEncryption/IdentityBased/BonehBoyenMachine/Draws` for `BB1Machine.order_le_two_pow` (base `Draws.lean:156`) | the lemma itself (reused, not copied) | yes, REPORT.md:414, promotion requested | minor (layering: a Pairing module depends on an IBE construction) |
| **S2** | `Pairing/Exponents.lean:182` `pow_val_add_GT`, `:189` `pow_val_neg_GT` | base `Pairing/Group.lean:254` `pow_val_add`, `:260` `pow_val_neg` (source group only; `pow_val_mul_GT` exists at `:222`) | yes, REPORT.md:410, "near-copy" | minor; promote to `Pairing/Group.lean` |
| **S3** | 21 inline `(…).foldr pairEncode []` (`FE/Simulation/Games.lean` ×4, `FE/Defs/Simulator.lean` ×2, `FE/Wee20/WireDraws.lean` ×14, `FE/Wee20/PHFE/Simulator.lean` ×1) | `Encryption/PrivateKey/EnsembleSecurity.lean:103` `encodeList` (same nested-pair encoding) | no | minor (an encoding, not a lemma) |
| **S4** | `FE/Run.lean:48` `detImpl`, `:60` `runDet`, `simulate_buildComp_detImpl_eq_pure` | `Games.buildComp` (`Games/Machines.lean:112`); `QueryImpl.ofComp` with pure answers (`Games/Bridges/QueryTree.lean:85`) is stateless | yes (prompt required the search; REPORT "Overlap and reuse") | note: generic `Games` glue in the FE namespace; promotion candidate |
| **S5** | `FE/Wee20/LinearSecurity/*` and `FE/Wee20/QuadraticSecurity/*` protocol handlers and advice codecs | each other | yes, REPORT.md:425, "near-copies" over different typed families | note |
| **S6** | `Pairing/MatrixDH/Parameters.lean:56` `PublicParams`, `GeneratorDraw`, `publicParamsGen` | `BilinearGen.dbdhGame`'s inline g ← G* draw (`Pairing/Assumptions.lean:225`) | n/a (new structure) | note: the parallel io-sprg job uses the same groups; its public-parameter type should be this one, or the two must be unified before landing |
| **S7** | `Pairing/Exponents.lean` `groupDot`, `groupMulVec`, `groupVecMul`, `groupMatMul`, `matMulGroup`, `expVec`, `expMat`, `pairVec`, `pairMat`, `pairTensor` and their algebra (20 `sorry`s) | none in TCSlib; Mathlib's `Matrix.mulVec`/`vecMul` need a module structure on the group, which `BilinearGroup` does not provide | yes | none: new API; the gate checks the proofs will reuse `pow_val_add`, `pow_val_mul`, `bilinear_pow`, Mathlib's `Finset.prod_*` and `kroneckerMap` lemmas, as sketched |
| **S8** | `Pairing/Linear.lean` DLIN, `dlinMatrix…`; `Pairing/MatrixDH/*` MDDH and `dlinToMddh` | none at the base (no DLIN/MDDH) | n/a | none |
| **S9** | `FE/PartialGarbling/*` | Yao garbling `SecureComputation/Garbling*` (false friend) | n/a | none: not reused, no name clash |
| **S10** | `FE/Classes.lean` `BidegreeAtMost`, `pad_one` | Mathlib `MvPolynomial.totalDegree`, `degreeOf` (no block-separated bidegree) | yes (REPORT.md:420) | none |
| **S11** | `FE/Wee20/LinearSecurity/Slack.lean` rank loss | `Matrix.card_GL_field` (reused) | yes | none |

## 3. For the gate

- Run `exact?`/`apply?` (one slot) on `pow_val_add_GT`, `pow_val_neg_GT`, `expVec_add`,
  `expVec_neg`, `Classes.phfeEval_sum`, `Layered.forward_root`, `Layered.auxCount_add_one`,
  `Layered.nodeBound_eval` and `Linear.dlinMatrix_mulVec`. A hit that closes a statement outright is
  a restatement: grade it (major if undisclosed).
- Check that no sketch plans to re-prove a public lemma inline (prompt §8). For example, the
  `expect_simGame_eq_saGame` sketch (`FE/SemiAdaptive/FromTwoStage.lean:261`) should commute draws
  with the base's `ProbComp.expect_sample_comm` and `expect_expect_sample`
  (`Games/Probability.lean:313`, `:326`) and reindex with `expect_sample_equiv`, not by hand.
- Grade S1–S3 and say whether S6 needs a coordination ruling with the io-sprg job.
