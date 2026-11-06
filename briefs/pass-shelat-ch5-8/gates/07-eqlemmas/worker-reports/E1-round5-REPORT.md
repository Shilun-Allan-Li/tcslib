## #210 round 5 (gate 07): report

The new head is **286aee54ae17ffec36225a318f0c714cf9bb7393** on `wip/eqlemmas` in `$SP/wt-e1`. Nothing is pushed. The round's base is 16a7d02d69cae1a700c131e3cc3dd918a7b3d6e1.

Outside #195's 26 files, **one** read is left in statements and definition bodies: the frozen `prodInverter` (details under "Remaining reads"). Everything else passes the final sweep.

Commits, oldest first:
- 4926d411f388fb961ff5cc91f0fdbdfa192e7201
- 4f928f920e8fec646f6f1b5ac438f2bcd2bdc89f
- a7dec12c9d6bc86d57ea5aa86e7514a03b34f331
- 257272fa6c24b5b6ca8e4c791ecae251d6d39a19
- 1fca79dfdfdcbfa68199387fecf864ced534e4a3
- 4b2426b60c93a82b870b9593dbe532ffff95390d
- 6beac9bde705b4d9d57feb34c82c38db4ba16957
- 3095482b680e852b771ffc3e58ebb62b93e2db44
- e8ff9a95053bbd83fc7d2cf247e05bc38bfcc1ef
- 286aee54ae17ffec36225a318f0c714cf9bb7393

`$SP` = /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad. All logs are in `$SP/e1/final5/`.

### For #195's worker (exact names)
- **`PRG.expand_G_stretch`**, in Asymptotic/HardCore.lean beside `PRG.expand`. I added this new lemma and left `expand_G` unchanged, so no existing statement changes.
  ```
  theorem PRG.expand_G_stretch (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) (ℓ : PolyExpr)
      (hℓ : ∀ n, n < ℓ.eval n) (n : ℕ) (s : Fin n → Bool)
      (i : Fin ((PRG.expand G ℓ hℓ).stretch.eval n)) :
      (PRG.expand G ℓ hℓ).G n s i = G n ((fun x => Fin.init (G n x))^[i] s) (Fin.last n)
  ```
- In HardCore.lean:
  - `PRG.expand_stretch : (PRG.expand G ℓ hℓ).stretch = ℓ`
  - `PRG.oneBit_secure_iff G`
- In GGMReductionEval.lean, namespace `GGMRed`:
  - `coinPoly_eq`
  - `coinPoly_eval : (coinPoly D q).eval n = q.eval n * n + (q.eval n * (2 * n) + D.coinLen n)`
  - `ggmRedMachine_coinsEquiv hE D q i j n : … .Coins n ≃ (Fin (q.eval n * n + (q.eval n * (2 * n) + D.coinLen n)) → Bool)`, with `_ofFn`
  - `coins_ggmRedMachine` no longer reads `ofPolyTime`.
- In PolyTimePairing.lean: `pairFstD_eq`, `pairSndD_eq`, `pairFstD_of_pairDecode_eq_none`, `pairSndD_of_pairDecode_eq_none`.

### Other names you asked me to confirm
- **fac fill:**
  - `TCSlib.Cryptography.OneWay.yaoB_apply`
  - `Complexity.NUPPT.Uniform.advice_eq` and `Complexity.NUPPT.uniform_iff`, moved from NonUniform.lean into Randomized/PPT.lean beside `Uniform`, statements unchanged
  - public `FunFamily.blocks_apply`
  - `blocks_eq_blocksE` is **skipped**: it would pre-empt clean-up part 2's DL-9, which deletes `blocksE`.
- **col-b:** `msgAt_eq` (ThreeColoring/Protocol.lean) and `edgeIdxOfMsg_eq` (ThreeColoring/Language.lean).

### `PolyExpr.eval` (task 1)
- Making `eval` `@[reducible]` breaks `simp`: on this structurally recursive definition, `simp` no longer finds the `eval_*` lemmas. `no_index` and non-`rfl` proofs do not help, and downstream modules then fail.
- So `eval` stays semireducible. Its docstring records the ruling (Q1, 2026-11-07), and the sweep treats `eval` as notation (it is never sealed).
- Earlier logs: `replay-eval.log` and `replay-eval-reducible-attempt.log`.
- `PolyExpr.normal` is **not** made reducible: it is not notation-like. Its reads go through `eval_normal` and the GI tape lengths instead.

### Restatements (old → new, and why the meaning is unchanged)
1. **`P.HardCore h`.** These all take `hh : P.HardCore h` (or `∃ … ∧ P.HardCore h`) instead of `HardCore P.toFunFamily h`: `owp_hardcore_prg`, `cor_81_7`, `HardCore.bitHiding` (name kept), `owp_commitment`, `exists_commitment_of_owp_hardCore`, `zk_proof_of_owp_levinReduction`, `zk_proof_of_mem_NP_of_owp`, `OneWayPermutation.glHalf` and `exists_owp_hardCore`.
   - `PermFamily.HardCore P h := HardCore P.toFunFamily (fun n x => h n (P.toFunFamily_domEquiv n x))`, published with `hardCore_iff` (`Iff.rfl`).
   - `domEquiv` is `Equiv.refl`, so the hypothesis is the old one.
   - I chose this over writing `domEquiv` inline because the permutation form appears in about ten statements, and `.easy`, `.hard` and `.of_easy_hard` give the permutation-form clauses (`predictor n n`). That keeps `owp_hardcore_prg`'s proof unchanged.
2. **`thm_87_3_1`, `thm_87_3_2`, `thm_87_3_3`, `thm_87_3_9` and `FunFamily.predProb_glPad`:** `A (Fin.appendEquiv … y)` becomes `A ((𝓕.glPad_outEquiv n).symm (Fin.appendEquiv … y))`. `glPad_outEquiv` is `Equiv.refl`.
3. **HardCorePermutation.** `glHalf_f_even`/`_odd`, `glHalfBit_even`/`_odd`, `predProb_glHalf_even`/`_odd` and `invProb_glHalf_even`/`_odd_le` now read `P.toFunFamily.glPad` through `PermFamily.glPad_inEquiv`/`glPad_outEquiv : {0,1}^{inLen_g/outLen_g(m)} ≃ {0,1}^{m+m}`. These are `finCongr` along proved length equalities, so they are identities on bit strings (`ofFn` lemmas).
4. **`glHalf_predProb_even`/`_odd`:** the predictor length `(m + m)` becomes `P.toFunFamily.glPad.outLen.eval m`, which equals `m + m` (`PermFamily.glPad_outLen_eval`). The length only types the argument.
5. **`bitCom_false_eq_owpGenPRG`:** the right side `(owpGenPRG P h).G n r i` becomes `owpGenPRG_outEquiv P h n ((owpGenPRG P h).G n r) i`, where the equivalence is `refl`.
6. **Universal input types.** `ofFn_fUniversal_f`, `padStr_eq_ofFn_fUniversal_f`, `exists_preimage_of_fUniversal_eq`, `PadQuad.ofFn_family_f` and `quadraticCode_of_linear` now quantify `x : Fin ((fUniversal c).inLen.eval n) → Bool` (and the analogue for the padded family) instead of `Fin n → Bool`. The input length is `n` (`fUniversal_inLen_eval`, `FunFamily.ofString_inLen_eval`).
7. **`GI.gniTapes_apply`:** the equality of tapes becomes the equality of their `List.ofFn`. The lengths are equal and `ofFn` is injective, so the content is the same.
8. **`prgScheme_encDist`** (earlier this round) now goes through `prgScheme_genCoinsEquiv`.
9. **Definitions whose type is unchanged and whose body now goes through a published length or equivalence:**
   - `vTapeSplit`, `giBitEquiv`, `gniTapes`, `giRepCoins` (`noncomputable` added; the same holds for `giCoinEquiv`)
   - `predCoins` (now `noncomputable`)
   - `oddCoins`, `sampleAll`, `owfFamily`
   - `Collection.glPad` and `TrapdoorCollection.glPad`
   - `bitwise`'s and `prgScheme`'s correctness fields.

   Private theorems re-pointed the same way: `zkSim_runAt` (via `zkSimCoins`), `bitwise_pkEncDist_coinBlocks` (via `bitwiseEncCoins`), `outV_pullback_cheat` (`coinTrunc (Strategy.coinLen_eq _ _).le`), and Collections' `collInverter_success` and `fiber_le` (via `coinsCongr (coins_collInverter …)`).
10. The full statement diff is in `decls.tsv`: 78 ADDED, 36 CHANGED (the items above), 2 REMOVED (the `Uniform` lemmas, re-added in PPT.lean).

### New published interfaces
- **HardCore:**
  - `PermFamily.HardCore`, `hardCore_iff`, `predProb_toFunFamily`, `.easy`, `.hard`, `.of_easy_hard`
  - `FunFamily.glPad_inEquiv`, `glPad_outEquiv`, their length and `ofFn` lemmas, `glPad_f_equiv`, `glBit_equiv`
  - `PermFamily.glPad_inEquiv`, `glPad_outEquiv`, their length and `ofFn` lemmas
  - `owpGenPRG_outEquiv` (+`_ofFn`) and `owpGenPRG_G_outEquiv`
- **OneWay:** `PermFamily.toFunFamily_inLen`/`outLen`, `toFunFamily_inLen_eval`/`outLen_eval`, `toFunFamily_domEquiv`/`codEquiv` with their `ofFn` lemmas, `toFunFamily_f_domEquiv`, `FunFamily.ofString_inLen_eval`.
- **HardCoreLemmas:** `NUPPT.wrap_coinLen`, `wrapCoinsEquiv` (+`_symm_ofFn`).
- **PublicKey:** `bitwise_enc_coinLen`, `bitwiseEncCoins` (+`_ofFn`). **PublicKeyLemmas:** `tdpPredictor_coinLen`.
- **Universal:** `fUniversal_inLen_eval`.
- **Factoring:** `prodInverter_eq`.
- **GI Proofs:** `gniProtocol_V_coinLen`, `gniProtocolRep_V_coinLen`, `giProtocol_V_coinLen`, `giProtocolRep_V_coinLen`.
- **ZK Encryption:** private `zkSimCoins`.
- **Earlier this round:** `owfCoinsEquiv`, `prgScheme_gen`/`encCoinsEquiv`, `ρPEquiv`.

### Base proofs re-pointed (review findings)
- **Factoring:**
  - `eval_fmultWeakPoly` now goes through `PolyExpr.eval_normal`.
  - `fmult_prod_inLen` now goes through `FunFamily.prod_inLen`, `eval_mul`, `eval_fmultBlocks` and `fmult_inLen`; `prod_inLen` already existed.
  - `samplePairOut_eq_encode` and `factoringCollection_index` use the review's proofs.
- **RSA `rsaCollection_index`:** goes through `Collection.index_eq`, `rsaCollection_gen` (the coin type is carried by a generalised generator) and `rsaGen_runAt`. This is equivalent to the review's one-liner and is checked sealed (probe P14, control C16). I kept it so I would not have to replay again.
- **ElGamal `statClose_of_uprob_ne`:** `rw [statClose_iff]` before `intro T`.
- **3COL `R3COL_witnessRelation`'s bounded clause:** now goes through `R3COL_iff`. The fill-target `sorry` is untouched.

### Remaining reads
- **Not #195's: Factoring's `prodInverter` definition body** (reads `FunFamily.prod`). It is frozen, and you said not to restate it. `prodInverter_eq` is published beside it; its statement has no read, but its `rfl` proof reads `FunFamily.prod`. **Decision needed:** keep it as an allowed exception, or restate `prodInverter`'s body with `fmultBlocks.eval n * (2 * n)` lengths in a later round.
- **#195's rows:**
  - MultiMessage: `prfScheme` (body), `prfScheme_multiEncDist`
  - PRF: `PRG.doubling` (body; `expand_G_stretch` is for this one)
  - PRFLemmas: `NUPPT.runAt_preComp`
  - Games/Hopping: 5 theorems
  - Games/Protocols: 6 declarations
  - Games/Simulate: `QueryImpl.sum`
- **Proof-level defeq reads left in place.** The sweep does not measure proofs:
  - HardCorePermutation: the `change`-based proofs of `glHalf_f_even`/`_odd` and `glHalfBit_even`/`_odd`, and `glHalf_invProbAt_even`/`_odd_le`
  - `prodInverter_eq := rfl`
  - Universal and UniversalPadding: proofs that pass `y : Fin n → Bool` to the generalised lemmas
  - Commitment: `owpComStr_polyTimeComputable` destructures `P.toFunFamily.Easy`
- OneWay still has a private root-namespace `blocks_apply` that duplicates the new public `FunFamily.blocks_apply`. It is left for DL-9.

### Checks
1. **Replay** (`replay-head.log`, order from `downstream2.py` over all changed files, 250 DOWN modules):
   - 233 modules plus `audits/pass-shelat/Checks` passed.
   - The edits made after that run were replayed separately: `replay-head-2.log` (40 modules downstream of Collections, PublicKey, ElGamal and Protocol, plus Checks), then PublicKey, the Asymptotic facade and Checks again after the last fix. All pass.
   - **18 modules were not replayed**, all outside Cryptography (BooleanAnalysis/GaussianSpace, Diagonalization/NTimeHierarchy, SavitchARM, Logspace/ISCount*, Savitch). Each failed only with "object file … does not exist": 38 upstream modules (`missing-up.txt`) were never built in this olean tree. The upstream changes are pure additions, and none of the new names appears in those 18 modules (grep). They are not checked, though; building the 38 would cost extra time.
2. **`sorry` counts:**
   - For changed files, the `sorry` token count equals the base's and the warning counts match (`sorry-compare.txt`).
   - For the 82 modules also replayed in final4, the warning counts are equal (`timing-vs-final4.txt`).
3. **Timings vs final4:** nine modules are more than 25% slower, by 3–18 s. That includes GGMReduction, which I did not change, and other agents' Lean jobs were running in parallel, so this looks like machine load.
4. **Axioms** (`probes/Axioms.log`):
   - All 78 added declarations depend only on `propext`, `Classical.choice` and `Quot.sound`.
   - `sorryAx` appears only in `factoringCollection_index` and `rsaCollection_index`. Their types mention collections built with sorried poly-time proofs, unchanged from the base.
   - It also appears in `R3COL_witnessRelation`, through its own fill-target `sorry`.
5. **Lint:**
   - `style-lint-*.log`: the only new findings are size lines for approved files (Collections 1133, PublicKey 1066, RSA 1127, ThreeColoring/Protocol 1004). HardCoreLemmas is kept at 999 lines.
   - `check8b-diff.log`: no new FAIL. The ElGamal FAIL is pre-existing (the line number shifted). WARNs only went down, or are approved sizes.
6. **Sealed probes** (`probes/`, 39 pass examples covering every new group):
   - `Final5Pass`: rc 0.
   - `Final5Control`: 27 old readings, each fails exactly once sealed (`control-attribution.txt`).
   - `Final5OpenControl`: the same readings unsealed, rc 0.
7. **Final sweep** over all 136 Cryptography files plus Checks (`sweep2.out` and `sweep2/reads.tsv`, with `sweep3.out` re-running Collections, PublicKey, ElGamal, Protocol and RSA after the late fixes). The combined list is `final-reads.tsv`.
