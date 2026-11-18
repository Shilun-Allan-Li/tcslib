# io-phfe: duplication sweep r3, a delta over r2

Static sweep, refreshed 2026-11-18 for pack r3. **`duplication-sweep-r2.md` stands** except as
amended here; this file adds rows.

**Base.** `<BASE>` stacks #374 (`cbce64d1`), `foundations/realization` (`cdc0934f`) and #378
(`foundations/coin-sampling` `51dc7672`). Each adds only new files and facade lines over
`cbce64d1`:
- realization: `Asymptotic/Realization.lean` and `Asymptotic.lean` +4;
- coin-sampling: `CoinSampling/*`, `Games/Closeness.lean`, `TCSlib.lean` +1, `Games.lean` +3.

So every r2 row holds at `<BASE>`. New TCSlib rows were read at `foundations/realization` head
`cdc0934f` (identical to `cbce64d1` outside the new file). Mathlib is pinned at `029db123`, as
r2.

Reuse column as r2:
- **must**: use it, never restate it;
- **must (pattern)**: follow its form, copy no proof;
- **if needed**: use it rather than re-prove it, should the route need the fact;
- **no**: listed to prevent a false match;
- **Phase B**: not for this job.

## Amended r2 rows

| r2 row | r2 | r3 |
|---|---|---|
| § 8 "`Complexity.NUPPT.RealizesOn` … expected at `<BASE>`" | must if present, else a local file | **present: must** (§ 0b). No `FunctionalEncryption/Realization.lean`, no variant |
| § 8 "`TCSlib/Cryptography/CoinSampling/` … not needed" | not needed | **at `<BASE>`**. Rule 15 (design-r3 § 1E) needs only the **type** `UniformSampler` (`CoinSampling/Efficiency.lean:93`) and `CoinSampler.fail` (`Basic.lean:106`): **must (type only)** in the efficiency fields, never instantiated. Everything else in `CoinSampling` and `Games/Closeness.lean`: not imported |
| `SamplesEfficiently` (Q-E1 (A): `CoinSampling/Contract.lean`, if at `<BASE>`) | — | **must when present**; otherwise a local `FunctionalEncryption/SamplerEfficiency.lean` with the same declaration |
| § 4a `PolyTimeComputable`, `NUPPT.Uniform`/`Computes`, `FinTM.ComputesInTime`; § 1 `BilinearGen.gen_uniform`, `BilinearGen.Ops` (`_poly` fields) | must for the written `Prop`s | **must for the efficiency fields and targets** (rule 15); the generator and `Ops` already carry efficiency, so PPGen and group operations need no new field |
| § 4a `Complexity.NUPPT.exists_reparam_pre_post` | Phase B | Phase B, now through `exists_realizesOn_of_preTarget_id` (§ 0b) for the L1 (DLIN ⇒ MDDH) realisers |
| § 3 `MachineCodec`, `NUPPT.toComp`, `toCompOn`; § 2 `IBEScheme.sidImpl` … `SIDSecure` | must / must (pattern) | **central**: the semi-adaptive adversary is an oracle NUPPT (`toCompOn` with `bitCodec`), as `sidGame` (§ 3b) |
| § 3 `PolyHandler`, `exists_handlerMachine` (T1), `InteractiveHandler` | must | **Phase B** for the L2 realisers; Phase A builds no machine. `PolyHandler.impl` is NR for `runDet` |
| § 5a `Matrix.det_of_upperTriangular`, `det_of_lowerTriangular` | if needed (partial-garbling privacy) | **no**: the layered instance is proved by path sums, without determinants (design-r3 § 4.7) |
| § 7 Yao garbling, `BranchingProgram` | false friends | unchanged; also, **no ABP datatype** is introduced in r3 |

## 0b. The shared realisation API (`TCSlib/Cryptography/Asymptotic/Realization.lean`, at `<BASE>`)

Names are `Complexity.NUPPT.*`, declared with `_root_` in `namespace TCSlib.Cryptography`. The
body is `B.coins = c ∧ ∀ m x r, r.length = c.eval m → B.runAtL m (enc m x) r = R m x r`: only
encoded challenges and coin strings of length `c(m)` are constrained.

| Name | Line | Reuse | For |
|---|---|---|---|
| `RealizesOn` | 96 | must | every realiser hypothesis, at both levels |
| `realizesOn_iff`, `RealizesOn.coins_eq`, `RealizesOn.runAtL_eq` | 103, 113, 118 | must | readers (never unfold `RealizesOn`) |
| `RealizesOn.runAt_eq`, `RealizesOn.distinguisherL_eq` | 124, 132 | must | transfer lemmas: a realiser's MDDH/DLIN advantage is the reduction function's |
| `RealizesOn.runAt_coinsEquivPoly_symm` | 141 | must (if needed) | sums over `B.Coins m` as sums over bit vectors |
| `realizesOn_of_forall`, `RealizesOn.congr` | 149, 157 | must (if needed) | matching shapes |
| `realizesOn_self`, `realizesOn_self_take` | 167, 179 | must | the non-vacuity table |
| `exists_realizesOn_of_preTarget_id` | 239 | Phase B | L1 realisers of `dlinToMddh` (single activation, φ = id) |
| `exists_realizesOn_of_preTarget`, `exists_realizesOn_reparam_pre_post` | 220, 198 | no (Phase A); Phase B if a φ ≠ id appears | |

## 3b. Adaptive (semi-adaptive) games and deterministic runs

| Name | Where | Reuse | For |
|---|---|---|---|
| `Games.Move`, `MachineCodec` (+ `encodeLog`) | `Games/Machines.lean:69`, `:79` | must | the oracle adversary's next-move form |
| `Games.buildComp` (+ case lemmas `buildComp_zero_of_ret`, `_of_query`, `buildComp_succ_of_ret`, …) | `Games/Machines.lean:112`, `:128`– | must | `runDet` mirrors it; the `simulate … = pure (runDet …)` reader is proved by its case lemmas |
| `Complexity.NUPPT.toCompOn` (+ `_eq`, `_costBoundedBy`) | `Games/Machines.lean:257` | must | `NUPPT.toSAAdv` (the adversary on input ⟨pp, mpk⟩) |
| `bitSpec`, `bitCodec`, `zeroBits` | `Games/BitCodec.lean:73`, `:220`, `:126` | must | `saSpec`, `saCodec` |
| `IBEScheme.sidSpec`, `sidImpl` (+ case lemmas, `_onSpec`), `oracleImpl`, `sidCodec`, `sidGame`, `SIDSecure` | `AdvancedEncryption/IdentityBased/Defs.lean:232`, `:258`–`:340`, `:352`, `:520`, `:529`, `:550` | must (pattern) | the shape of `saImpl`, `saGame`, `SASimSecure` (∀ A q) |
| `FixedLengthScheme.decAnswer` | `Encryption/PrivateKey/OracleSecurity.lean:161` | must | ⊥ answers (keys before the challenge, repeated challenges) |
| `expect_simulate_rel`, `prob_simulate_rel`, `expect_sample_rel` | `Games/Relational.lean:85`, `:111`, `:130` | must | per-query couplings (Π Lemmas 3, 5; the outer hops) |
| `simulate`, `simulate_bind`, `simulate_call`, `QueryImpl.comp`, `simulate_comp` | `Games/Simulate.lean:83`–`:199` | must | unrolling the q + 1 queries of `TwoStage.toSA` (`simAdv_eq_saSimAdv`) |
| `Games.PolyHandler`, `PolyHandler.impl`, `impl_apply` | `Games/Efficiency.lean:163`, `:287`, `:294` | no (NR for `runDet`) | do not build a `PolyHandler` (Phase B) |
| `Games.exists_handlerMachine` (T1) | `Games/Efficiency.lean:332` | Phase B | L2 realisers: handler seed 0, ω* in `init` |
| `NUPPT.coinsCongr` (+ `_ofFn`) | `Complexity/Randomized/PPT.lean:256`, `:260` | if needed | moving between equal coin polynomials (`TwoStage.toSA`'s coins) |
| a deterministic oracle interpreter (`runDet`, `evalDet`, `detRun`, `runWith`) | none at `cdc0934f` (`git grep`) | — | the job may add `runDet`, disclosed with its searches |

## 5b. Mathlib for the layered partial garbling and Π's adaptive Lemma 3 (pinned `029db123`)

| Name | Where | Reuse | For |
|---|---|---|---|
| `Fin.snoc`, `Fin.init`, `Fin.init_snoc`, `Fin.snoc_castSucc`, `Fin.snoc_last` | `Mathlib/Data/Fin/Tuple/Basic.lean:495`, `:486`, `:500`, `:506`, `:519` | must | children u·a of a node; forward values ∏ x̂(u i) |
| `Fin.snocEquiv`, `Fin.consEquiv` | `Data/Fin/Tuple/Basic.lean:701`, `:169` | must (if needed) | reindexing sums over tuples of length k + 1 |
| `Fin.prod_univ_castSucc`, `Fin.prod_univ_succ` (and their `sum` forms) | `Mathlib/Algebra/BigOperators/Fin.lean:80`, `:72` | must | the forward recurrence d_{u·a} = d_u x̂_a |
| `Fintype.prod_sigma` / `Finset.prod_sigma` (and `sum` forms) | `Mathlib/Data/Fintype/BigOperators.lean:144`; `Mathlib/Algebra/BigOperators/Group/Finset/Sigma.lean:34` | must | sums over `MIdx = Σ k, (Fin k → Fin (ℓ+1))` (the telescoping) |
| `Fin.elim0` | Mathlib core | must | the source node `⟨0, Fin.elim0⟩` |
| `ProbComp.expect_sample_equiv` | `Games/Probability.lean:304` | must | exact privacy by translation; Lemma 3's bijection |
| `Equiv.addRight` | `Mathlib/Algebra/Group/Units/Equiv.lean:116` (r2 § 5) | must | t ↦ t − s; U ↦ U + a^⊥Δ (with the public part fixed) |
| `Matrix.kroneckerMap`, `mul_kronecker_mul`, `kronecker_mulVec_vec` | r2 § 5a | must | L₁(x^⊤ ⊗ I_m) and (I_n ⊗ R)(x^⊤ ⊗ I_m) = (x^⊤ ⊗ I_k)R |
| `Matrix.card_GL_field` | `Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Card.lean:82` | if needed | the exact full-rank probability of (A \| c) (Π's slack) |
| `Matrix.det_of_upperTriangular`, IK-style determinant lemmas | — | no | the determinant route is not taken |

## Searches re-run for r3

- `git grep -n 'RealizesOn'` at `cdc0934f`: only `Asymptotic/Realization.lean` and its facade.
- `git grep -niE 'partial.?garbl|PartialGarbling|pgb'` under `TCSlib/`: none (new work).
- `git grep -niE 'semi.?adaptive|saGame|SASim'` under `TCSlib/`: none (new work; IBE's selective
  `sidGame` is the pattern).
- `git grep -nE 'def (runDet|evalDet|detRun|runWith)'` under `TCSlib/Cryptography/Games`: none.
- `#378`'s files: nothing on FE, garbling or pairings (samplers only).
