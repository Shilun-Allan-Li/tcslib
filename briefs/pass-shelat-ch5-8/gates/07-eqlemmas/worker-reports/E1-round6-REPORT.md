## #210 round 6: report

The new head is **c304994ed7a25108db7f019cf2e258a972db9b12** on `wip/eqlemmas` in `$SP/wt-e1`, unpushed and with a clean tree. All four items are done. No proof-level read is left in a declaration this PR adds or changes. 173 such reads remain in proofs the PR does not touch; they are the (b) list for clean-up.

`$SP` = /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad. All logs are in `$SP/e1/final6/`.

Commits on top of 286aee54:
- db071063c79a74838c02b9f0047aa1ec2bf92879 — `prodInverter`
- 455d19ce6896ead31d4fca59eca04d4c589780c2 — proof-level reads
- 4ba1abe89d2a120edcfb93413f01cb5740a105ee — last three proof reads
- c304994ed7a25108db7f019cf2e258a972db9b12 — file sizes, proof sketches, relocations

### 1. `prodInverter`
- **Body.** It now calls `A.inverter n (fmultBlocks.eval n * (2 * n)) (fmultBlocks.eval n * (2 * n)) …`. It reads no other file's definition, and its type is unchanged. The meaning is the same: both lengths of `fmult.prod fmultBlocks` at `n` equal `m_n · 2n`, by `fmult_prod_inLen` and the new `fmult_prod_outLen`.
- **`prodInverter_eq`** is now the defining equation, proved by `rfl` on the own-file definition. It no longer reads `FunFamily.prod`.
- **fac fill, checked in a scratch copy** (`facscratch/`). I took the `fill/fac` head (e932cd15eb564917ca7bc091df0c17d41cc6c046) with the review's `landing-edits.diff` and `conditional-210-edits.diff`, three-way merged it onto my head with no conflicts, and elaborated it against the final oleans. `fill/fac` itself is not edited.
  - **`fac_strong_key`** elaborates unchanged.
  - **`fac_prodInverter_eq_yaoB`** fails at its `rcases`, which names the old lengths.
  - **Minimal landing edit** (`facscratch/landing-edit-round6.diff`), one line:
    ```
    rcases hx : A.inverter n (fmultBlocks.eval n * (2 * n)) (fmultBlocks.eval n * (2 * n))
        ((FunFamily.blocks (fmultBlocks.eval n) (2 * n)).symm Y) r with _ | x
    ```
  - With that edit the whole file elaborates both unsealed and with `FunFamily.prod` sealed for the whole file (rc 0, `merged-edited*.final.log`). The review's finding 2 (the `FunFamily.prod` read) is gone.

### 2. Proof-level reads
**How I found them.** `proofseal/proofseal.py` seals the whole file: proofs are included, every foreign plain definition reachable from types, definition values and proof values is made irreducible (except `PolyExpr.eval`), and each error is attributed to its declaration. `touched.py` then splits the errors into declarations the PR adds or changes (a) and the rest (b).

| Run | (a) | (b) |
|---|---|---|
| Before the fixes (`proofseal/round1-*.tsv`) | 20 | 169 |
| Final run at head (`proofseal/final.out`, `final-b.tsv`) | **0** | 173 |

Round 1 is the sealed control: the old proofs fail under the same seal. The full replay is the unsealed control.

**(a) fixes**, all through published lemmas:
- **HardCorePermutation:**
  - `glHalf_f_even`/`_odd` and `glHalfBit_even`/`_odd` go through the new `PermFamily.glPad_f_append`, `glBit_append` and `glPad_inEquiv_symm_append`.
  - `glHalf_invProbAt_even`/`_odd_le` are re-proved through the domain, range, `glPad` and coin equivalences.
  - `OneWayPermutation.glHalf` goes through `oneWayPermutation_iff` and `OneWayPermutation.evaluator`.
- **HardCore:** `owp_hardcore_prg` (`PRG.secure_iff`, `easy_iff`, `prgAdv_eq`, `distAdv_def`, `owpPredictorSnoc_eq`, `owpPredictor_apply`); `PRG.expand_G_stretch` (via `expand_G`); `predProb_glPad`.
- **HardCoreClaims:** `thm_87_3_1`/`_2`/`_9` use the new `perfectInverter_eq`, `majorityInverter_eq` and `guessInverter_eq`.
- **Universal and UniversalPadding:** `ofFn_fUniversal_f`, `padStr_eq_ofFn_fUniversal_f`, `exists_preimage_of_fUniversal_eq`, `ofFn_family_f` and `quadraticCode_of_linear`. They use the new `ofString_f_apply`, `ofString_outLen_eval` and `ofFn_ofString_apply`, `exists_ofFn_eq_of_length`, and `computesFunInTime_iff`.
- **Collections:** `owfFamily_easy`, and `fiber_le` (private; its existential is now over `Fin ((G.owfFamily L).inLen.eval n)`).
- **Commitment:** `HardCore.bitHiding`, `owp_commitment`.
- **Others:** NP `outV_pullback_cheat`; ZK Encryption `zkSim_runAt`; GI `ofFn_giBitEquiv` and `gniTapes_apply`.

**(b) rows: 173, in untouched proofs across the 34 PR files** (`proofseal/final-b.tsv`, one row per file and declaration). By file:
- PublicKey 14, SoundnessRepGI 13, PPT 12, ThreeColoring/Protocol 11, HardCore 11, OneWay 10
- NonUniform 8; SoundnessRep, HardCoreLemmas, HardCoreCollection, GGMReductionEval and Collections 7 each
- Universal, UniversalPadding and PolyTimePairing 6 each; NP, Commitment and PublicKeyLemmas 5 each
- the rest 1–4 each

Examples:
- Commitment `owpComStr_polyTimeComputable` (destructures `P.toFunFamily.Easy`)
- HardCorePermutation `PermFamily.glHalf_easy` and `Negligible.comp_div_two`
- Universal `fUniversal_easy`
- NP `LevinReduction.efficientProverProofErr` (`coinTrunc le_rfl`)
- HardCore `StrongOneWay.glPad`/`glPad_hardCore` and `PRG.expand_G`

Some rows may be cascades of a sealed failure earlier in the same file; `PPT.ofPolyTime`'s body is one source.

**Not covered by the seal:** explicit `simp only`/`unfold` of other files' definitions through their equation lemmas pass the seal, so they are not on the (b) list. One is left in a declaration the PR touches: `outV_pullback_cheat`'s `simp only [Protocol.outV, …]`.

### 3. Replay gap
- Disk had 13 GB free.
- The first pass built the 38 listed upstream modules (`build-missing.log`), but the 18 skipped modules still failed: they needed 118 further upstream modules that were also absent, mostly GaussianSpace, Hypercontractivity and Logspace.
- The second pass built that whole closure from sources, in order: 136 modules, all rc 0, about 13 minutes of Lean (`build-missing2.log`).
- **All 18 skipped modules now pass.** Their `sorry` warnings come from their own unchanged sources: UniqueGames 8, MaxCutAlgorithm 2, Savitch 1.

### 4. Final evidence
- **Replay:** downstream of every file changed in round 6 (69 modules plus `audits/pass-shelat/Checks`): all rc 0 at c304994ed7a25108db7f019cf2e258a972db9b12 (`replay-head.log`).
- **Axioms** (`probes/Axioms.log`, 129 new and changed declarations): all standard. `sorryAx` appears only where it did before: `zk_proof_of_mem_NP_of_owp` and `zk_proof_of_owp_levinReduction` (same in the base evidence logs), `rsaCollection_index` (sorried collection in its type), and `R3COL_witnessRelation` (fill-target `sorry`).
- **Lint:**
  - The only new style findings are size lines for approved files: Collections, PublicKey, RSA, ThreeColoring/Protocol.
  - HardCore was 1020 lines; I moved the `PermFamily` `glPad` interface and `HardcoreBit.ip_eq_of_ofFn` to HardCorePermutation, their only consumer.
  - OneWay was 1034 lines; I removed an unused private duplicate `blocks_apply`, dropped unused `toFunFamily_inLen`/`outLen`, `toFunFamily_codEquiv_symm_ofFn` and `OneWayPermutation.toStrongOneWay`, and shortened docstrings. It is now exactly 1000.
  - New proof sketches for `glHalf_invProbAt_even`/`_odd_le`.
  - check8b: FAIL count unchanged (9).
- **Statement diff:**
  - Against 16a7d02d69cae1a700c131e3cc3dd918a7b3d6e1 (`decls.tsv`): 89 ADDED, 36 CHANGED, 2 REMOVED. The two removed are the `Uniform` lemmas, moved to PPT.lean.
  - The old → new list for gate 07 round 2 is `statement-changes.tsv`; it is the round-5 restatement table and no statement changed in round 6.
  - Against 286aee54 (`decls-round6.tsv`): 22 ADDED. 11 REMOVED, of which 8 are the `PermFamily.glPad_*` lemmas moved with the same names and 3 are the dropped unused lemmas above. 1 CHANGED: `ofString_inLen_eval`'s binder types are now inferred, same statement.
  - Restated without a statement change: the `prodInverter` body and private `fiber_le`'s existential type.
- **Sweep** over the 17 files changed in round 6 (`sweep.out`): all PASS, 0 reads. Factoring's `prodInverter` read is gone.
- **Sealed probes** (`probes/`):
  - `Final6Pass`: 47 examples, rc 0.
  - `Final6Control`: 30 old readings, each fails exactly once sealed (including the old `prodInverter` lengths, `hP.easy` in permutation form, and the inverter/`owpPredictor` equations by `rfl`).
  - `Final6OpenControl`: the same 30 unsealed, rc 0.

### New published lemmas this round
- **OneWay:** `oneWayPermutation_iff`, `OneWayPermutation.evaluator`, `FunFamily.ofString_outLen_eval`, `ofString_f_apply`, `ofFn_ofString_apply`.
- **HardcoreBit:** `perfectInverter_eq`, `majorityInverter_eq`, `guessInverter_eq`.
- **GeneratorFromPermutation:** `owpPredictor_apply`.
- **Factoring:** `fmult_prod_outLen`.
- **HardCorePermutation:** `PermFamily.glPad_inEquiv_symm_append`, `glPad_f_append`, `glBit_append`, `HardcoreBit.ip_eq_of_ofFn`.

I killed no processes; none of mine are still running.
