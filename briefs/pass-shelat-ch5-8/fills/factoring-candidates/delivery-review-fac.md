# Delivery review: fill unit fac (the factoring candidates)

- **Delivery:** `inbox/fills/fac/` on `exchange/pass-shelat-ch5-8` at
  `b6269a58fbe222d346cc20c8fed54de03f900ba0` (REPORT.md, 10 patches, `src/`, `evidence/`).
- **Worker branch:** `fill/fac`, head `e932cd15eb564917ca7bc091df0c17d41cc6c046`, base
  `16a7d02d69cae1a700c131e3cc3dd918a7b3d6e1` (the issue commit; it is also the branch's merge base).
- **Brief:** `brief-issued.md`, unit fac. **Policy:** `policy.md`.
- **Reviewed:** 2026-11-06. This was an independent run:
  - the patches were replayed in a fresh scratch worktree;
  - Lean was re-run against a copy of the worker's olean tree, one process at a time, never
    `lake build`;
  - the seal names were collected from the elaborated terms, the statements they use and the
    source, not from the worker's list.

## Verdict: **land after edits**

All ten targets are filled and sorry-free. Every one of the 70 public constants of `Factoring.lean`
prints only `[propext, Classical.choice, Quot.sound]`, so the file is sorry-free: the headlines
`factoringCollection_oneWay`, `fmult_weakOneWay` and `fmult_prod_strongOneWay` are, and so are
`factoringSampler_spec` and the collection itself.

The other checks pass:
- the statements are frozen;
- the downstream modules elaborate, and RSA and Rabin keep exactly their own sorries;
- no private host was built: the planting machine is the proved Yao round, and S1 is the proved
  `SamplePrime` machine.

There are **no blockers and no majors**.

The rule-10 seal holds under this review's 66-name seal after classification. Six names have to
stay unsealed:
- **Reported by the worker (2):** `OneWay.yaoB` and `NUPPT.Uniform` (finding 3).
- **Notation (1):** `PolyExpr.eval`, under ruling Q1.
- **Not reported or mischaracterized (3).** These are all minors:
  - `YaoMachine.ρP` and `NUPPT.coinLen` are read by defeq at four sites; three of them are
    avoidable (finding 1, edit E1);
  - `FunFamily.prod` is read by defeq at two sites, forced by the frozen base definition
    `prodInverter` (finding 2).

The edits are minor and proof-only, except one sketch sentence that syncs E1:
- **E1** routes three of the four `ρP` sites through the published `YaoMachine.ρP_eval`.
- **E2** removes an in-file duplication: `fac_uprob_primes_le` is derived from
  `fac_statClose_diag`.
- **E3/E4** (conditional) switch the two reported readings to #210's next-round lemmas once they
  land.

The disclosure ledger is amended (D1).

## Checks

| # | Check | Result |
|---|---|---|
| 1 | Integrity | `git am` of the 10 patches onto `16a7d02d` in a fresh worktree: clean (`am.log`). The result's tree `a76ea781…` is identical to the tree of `e932cd15`. The owned file matches `src/` and the `fill/fac` head byte for byte (`cmp`); `src/` holds only that file. The diff touches only `Candidates/Factoring.lean` (`1 file changed, 1052 insertions(+), 54 deletions(-)`). The 54 removed lines are the ten `  sorry` plus the two replaced **Proof sketch** paragraphs (`exists_plantFactorer`, 27 lines; `polyTimeComputable_samplePairRaw`, 17 lines). |
| 2 | Statement freeze | Own declaration-level comparison (`declfreeze_rev.py`, `declfreeze-rev.log`): all 64 base declarations are present with byte-identical headers. Docstrings changed only for `exists_plantFactorer` and `polyTimeComputable_samplePairRaw`, both brief-authorized sketch rewrites. Only the ten targets' bodies changed, and no non-target proof or definition body changed. The 41 new declarations are all `private` with the prefix `fac_`. The diff adds no `open`, `set_option`, `attribute`, `section` or `@[simp]`. Base sorries: 10; at the head: 0. |
| 3 | Elaboration | `scripts/lean_check_tree.sh` with `TCSLIB_OLEANS` set to a copy (`$SP/review-fac/oleans`), in order (`module-checks.log`): `Candidates/Factoring` 10 s, `RSA` 9 s, `Rabin` 9 s, the facade `Candidates` 3 s, `audits/pass-shelat/Checks` 129 s. All exit 0, with 0 errors. `Factoring` has 0 warnings. Sorry warnings: RSA 10 and Rabin 19, exactly their own targets. |
| 3 | Axioms | `#print axioms` for the ten targets: each is `[propext, Classical.choice, Quot.sound]` (`axioms.log`). A sweep (`collectAxioms` over every public constant of the module) finds 0 non-standard among the 70 constants of `Factoring`. The RSA/Rabin `sorryAx` (43 + 57 constants) cannot come from fac. `Checks` prints the same for the fac rows, including `factoringSampler_spec`. |
| 4 | Rule 10 under this review's seal | See findings 1–4. The names were collected by a meta probe over the 78 own constants (the `fac_*` helpers, the targets and their auxiliaries): the TCSlib definitions of other modules, non-reducible and non-instance, in their elaborated types and values. A wide pass adds the statements of every constant used and the bodies of own-file definitions (`collect.log`): **66 names, no foreign compiler-generated matcher**. A lexical pass resolves the 860 tokens of the added source (`lex.log`); it adds nothing sealable (`DistinctPrimes` and `Primes` are reducible abbreviations, and one hit is a local `P`). None of the 66 is a `@[simp]` definition. Against the worker's 51-name list, this adds `Uniform`, `yaoB`, `ρP`, `coinLen`, `PolyExpr.eval`, `PolyExpr.normal`, `FunFamily.prod`, `ofPolyTime`, `ofPolyTimeUniform`, `NUPPT.output`, `PolyTimeComputable`, `pairFstD`, `pairSndD`, `samplePrimeCoins` and `Turing.pairEncode`. **Region seal** (as in dl-a): the seven fill regions (every `fac_*` and target, docstrings included) are wrapped in `section revSeal … attribute [local irreducible] …` (`seal/mkregion.py`). Results by number of names sealed: **60** (all but the six names below): 0 errors, 0 warnings (`RevSealedRegions60.out`). **65** (all but `PolyExpr.eval`): exactly 9 errors, all classified (`RevSealedRegions.out`): `fac_yaoB_apply` (yaoB), `fac_uniform_advice` (Uniform), `fac_prodInverter_eq_yaoB` ×2 and `fac_strong_key` (FunFamily.prod), and `exists_plantFactorer` ×4 (ρP, coinLen). Sealing `PolyExpr.eval` breaks the frozen base statements themselves (`fmult` is typed by `Fin (inLen.eval n)`), so Q1's notation ruling is the only workable reading (`RevSealedFactoring.out`). A **whole-file seal** additionally fails in base declarations only: `eval_fmultWeakPoly` (`PolyExpr.normal`), `fmult_prod_inLen` and `prodInverter` (`FunFamily.prod`), and the worker's two, `samplePairOut_eq_encode` and `factoringCollection_index` (`RevSealedFactoring2.out`). **Controls** (`seal/RevControl.lean`): seven readings close unsealed and fail under the same 65-name line (yaoB by its body, `hA n` for Uniform, `ρP_eval` by `rfl`, `coinLen_eq` by `rfl`, `fmult_prod_inLen` by `rfl`, `natToList` and `encodeDistinctPrimes` by their bodies). **Explicit unfolds:** 182 `simp`/`rw`/`dsimp` lists and 16 `unfold`s in the added code; no foreign definition is used as a rule, and every `unfold` names an own-file definition (`fmultNat`, `prodInverter`, `plantFactor`, `samplePrimeL`, `samplePairRaw`, `samplePairOut`, `factoringSampler`, `fac_pairDec`) (`grep-foreign.txt`). The five new bare `simp`/`simpa`, run through `simp?`, use core and Mathlib lemmas only (`simpq.log`). |
| 5 | Duplication | See findings 5 and 6. |
| 6 | Routes and sketches | See finding 7. |
| 7 | Docstrings and policy | All 41 new declarations have docstrings. `scripts/style_lint.py` (policy checklist 4–5): base 0 findings; head exactly 1, the size line (`style-lint-head.log`). Every private proof over 20 lines carries a **Proof sketch.**: `fac_weak_key` 75 lines, `fac_strong_key` 105, `fac_uprob_primes_le` 27, `fac_statClose_diag` 25, `fac_statClose_samplePrimeL` 23. `campaign_style_lint.py --check8b TCSlib/Cryptography/Candidates` reproduces the REPORT: no FAIL row for Factoring, a size WARN, and the check-8 WARN `fmultBlocks, fmultWeakPoly, plantFactor, prodInverter, samplePairRaw, samplePrimeL` (base definitions only) (`campaign-lint-head.log`). Size: 1868 lines (870 at the base); approved, noted only (finding 9). |

## Findings

1. **minor: `YaoMachine.ρP` and `NUPPT.coinLen` are read by defeq at four sites of
   `exists_plantFactorer`; three are avoidable.**

   **Where.** The fill takes the coins of `A''` as `ce r : Fin ((ρP D).eval n) → Bool`
   (`NUPPT.coinsEquiv_ofPolyTime`) and passes them where `Fin (n·M + (M·k + A.coinLen n))` is
   expected:
   - `S (ce r)` in the statement of `hround`;
   - the binder of `hfp`;
   - `S (ce r)` inside the proof of `hfp`;
   - `key := rfl`.

   Each identification unfolds `ρP` and `coinLen`. With both sealed, these four sites fail and
   nothing else does.

   **The forced reading.** `ans_layout` itself is published with `rc : Fin ((ρP D).eval n) → Bool`
   fed to `roundSample` (`OneWayYao.lean`, the `Round` section). So one identification is forced
   at the `ans_layout` call. The REPORT's exception 3 ("through the coin types in the published
   statements of `ans_layout` and `roundSample`; `coinLen_eq` and `ρP_eval` cover them") is
   right about that call, but the fill uses neither lemma.

   **E1.** It composes `ce` with the published `ρP_eval` cast, so the other three sites read
   typed round coins. With E1:
   - the file compiles sealed with `ρP` and `coinLen` included, except exactly the one forced
     argument at `ans_layout` (`FactoringEditedSealed62.out`, 1 error);
   - the remainder is clean (`FactoringEditedSealed60.out`).

   **Library request (for #210's next round or the OneWayYao owner).** State `ans_layout` with
   `rc : Fin (n·M + (M·k + c)) → Bool`, or through `ρP_eval`. That removes the last site.

2. **minor: an undisclosed `FunFamily.prod` defeq, forced by the frozen base.**
   - **The base definition.** `prodInverter`'s body (frozen) passes
     `(FunFamily.blocks …).symm ys : Fin (m·2n) → Bool` to `A.inverter n
     ((fmult.prod m).inLen.eval n) ((fmult.prod m).outLen.eval n)`. That body typechecks only
     through `FunFamily.prod`'s definition. The base `fmult_prod_inLen := rfl` does the same.
   - **Where the fill meets it.** `fac_prodInverter_eq_yaoB` restates that body in its
     `rcases hx :`. In `fac_strong_key`, `hB` identifies the `m·inLen`/`m·outLen` lengths of
     `invProbAt_prod_eq` with `prodInverter`'s. Sealing `FunFamily.prod` fails exactly there.
   - **Not avoidable in the fill.** The published `FunFamily.prod_inLen`/`prod_outLen` cannot
     rewrite inside the dependent argument type. No published reading of `prodInverter` exists.
     The worker's seal omitted the name, and the REPORT does not list the reading.
   - **Remedy.** Disclose it (D1). At the next statement window, either restate `prodInverter`
     with `fmultBlocks.eval n * (2 * n)` lengths, or publish a `prodInverter_eq` beside it. Then
     re-point `fmult_prod_inLen` by `FunFamily.prod_inLen`, `PolyExpr.eval_mul` and
     `eval_fmultBlocks`.

3. **note: the two reported readings, confirmed.**
   - **`OneWay.yaoB`.** It is read once, by `rfl`, in `fac_yaoB_apply`. Its only user is
     `fac_prodInverter_eq_yaoB`. There is no published equation (`OneWayYao.lean` line 544).
     **Replacement:** `OneWay.yaoB_apply`, beside `yaoB`, with `fac_yaoB_apply`'s statement.
   - **`NUPPT.Uniform`.** It is read once, in `fac_uniform_advice` (`hA n`). Its only user is S1.
     The published readings `NUPPT.Uniform.advice_eq` and `NUPPT.uniform_iff` are in
     `Randomized/NonUniform.lean` (lines 94, 112), outside the closure. **Replacement:** the
     reachable reading from #210's next round, `NUPPT.Uniform.advice_eq` (or `uniform_iff`).
   - **The conditional edit.** **E3/E4** delete both helpers and cite those lemmas. They were
     checked against stub lemmas with exactly those statements (`FactoringEditedNextStub.lean`):
     0 errors and 0 warnings unsealed, and 0 errors sealed with 62 names, `yaoB` and `Uniform`
     included (`FactoringEditedNextStubSealed62.out`). If the round publishes other names, the
     two citation lines change and nothing else. With E1–E4 the only unsealed foreign names are:
     - `PolyExpr.eval` (notation, Q1);
     - `FunFamily.prod` (finding 2);
     - the single `ans_layout` argument (finding 1).

4. **note: base proofs that fail sealed (not fac's to edit).** The worker's two are confirmed.
   The replacements below were checked sealed with all 65 names (`probe/BaseRepoint.lean`,
   `base-repoint.log`, rc 0):
   - **`samplePairOut_eq_encode`** (`rfl` through `encodeDistinctPrimes`): in the accepting
     branch, replace `rfl` by
     `by rw [encodeDistinctPrimes_eq, DistinctPrimes.p_eq, DistinctPrimes.q_eq]` (P6). The else
     branch `⟨_, rfl⟩` reads nothing.
   - **`factoringCollection_index`** (`simp [factoringCollection, factoringGen, …]`): replace by
     `rw [Collection.index_eq]` and then
     `exact (congrArg pairFstD (factoringGen_runAt n r)).trans (pairFstD_pairEncode _ _)`. The
     coin type passes through the own-file `factoringCollection`; `rw [factoringCollection_gen]`
     fails on the dependent coin type.

   The review also found three base readings the worker did not seal, so they are not in the
   REPORT. They go on the same re-point list as finding 2:
   - `eval_fmultWeakPoly := rfl`, through `PolyExpr.normal`. The published `PolyExpr.eval_normal`
     re-points it.
   - `fmult_prod_inLen := rfl` and `prodInverter`, through `FunFamily.prod` (finding 2).

5. **minor: in-file duplication.** Two private helpers each prove the diagonal bound
   `Pr[p = q] ≤ 2n/2^n`, the `hd` block of `fac_uprob_primes_le` and the `hd` block of
   `fac_statClose_diag`:
   - their 10-line proofs are verbatim the same;
   - their conditioning arguments are parallel.

   `fac_uprob_primes_le` is the one-sided, auxiliary-coin form of `fac_statClose_diag`. **E2**
   moves `fac_statClose_diag` (unchanged) above `fac_uprob_primes_le` and proves the latter in two
   lines, by `StatClose.abs_uprob_sub_le_prod` on `G`. That deletes the copy, a net 29 lines.

6. **minor: the duplication disclosure is incomplete.** The REPORT's three near-duplicates are
   confirmed:
   - `fac_arrowCongr`/`_ofFn`: the `finCongr` cast;
   - `fac_chunkEquiv`;
   - `fac_blocks_eq_blocksE`: `FunFamily.blocks` and `OneWay.blocksE` are library-side copies of
     one definition.

   Not disclosed (`neardup.log` and greps; none is a verbatim copy):
   - **`fac_chunkEquiv`.** It is a third construction of the block bijection: `chunk T n r =
     FunFamily.blocks T n r` pointwise (probe, 6 lines via `chunk_apply` and `blocksE_apply`). It
     could be `FunFamily.blocks` plus that equation. The REPORT's reason (the `chunk` facts are
     private) does not apply.
   - **`fac_arrowCongr`/`_ofFn`.** These are the public `finCastEquiv`/`ofFn_finCastEquiv`
     (`Asymptotic/HardCoreLemmas.lean`, outside the closure, so the copy is forced). The same
     cast is also written inline in 7 places in `Asymptotic/`.
   - **`fac_ofFn_halves`.** Its inner `h` re-proves the private `ofFn_blocks_two_symm`
     (`Asymptotic/OneWay.lean`). Its second half is the public `OneWay.ofFn_block_eq_take_drop` at
     `q = 2` (probe).
   - **`fac_listToNat_inj`.** It is the private `listToNat_inj` of `Asymptotic/Sampling.lean`. The
     public `bitsToNat_injective` is its typed consequence.
   - **Cross-unit (ledger only).** Small numeral facts are proved again in each parallel fill:
     - `listToNat [true] = 1`: `hone` in `fac_polyTimeComputable_isOne`, and `rsa_listToNat_one`;
     - `listToNat [] = 0`: `rsa_listToNat_nil` and `dla_listToNat_nil`;
     - leading zeros: `fac_natToList_lead` and dl-a's `dla_drop_natToList_zero_append`.

     A shared `Arithmetic.lean` set (`listToNat_one`, `listToNat_nil`,
     `natToList_add_length_listToNat`) would retire all of them.

   Mathlib has no `List.foldl_replicate`, so `fac_foldl_replicate_false` is not a reuse miss.

   **D1** lists all of these. Replacing them is optional except E2.

7. **note: routes and sketches.**
   - **`polyTimeComputable_samplePairRaw` (rewritten sketch).** The sketch matches the proof
     step for step. Each point checked:
     - the cut at `samplePrimeCoins`;
     - both halves from S1;
     - `hP` twice, through `primeStr_eq`;
     - the negated `pairEq` with `fac_listToNat_inj`;
     - the range checks from `listToNat_lt_two_pow`;
     - `n ≥ 2` on acceptance, so the output is `⟨a, b⟩`;
     - the default `⟨(0^n).drop 2 ++ 10, (0^n).drop 2 ++ 11⟩` by `fac_encode_default`, built from
       `zerosPoly`, `pairDropPoly (const 2)` and `append`.

     The claim "a prime read from an `n`-bit word forces `n ≥ 2`" is right (`2 ≤ v < 2^n`).
   - **`exists_plantFactorer` (rewritten sketch).** The sketch matches, and the soundness checks
     pass:
     - **Machine.** It is `NUPPT.ofPolyTime` of the first `n` bits of `YaoMachine.ans`, with
       coins `ρP` and advice `adv`/`advP`.
     - **Round identity.** `hround` is `ans_layout` with `fac_ofFn_halves`.
     - **Inverter comparison.** `hideal` uses `fac_prodInverter_eq_yaoB`. A factor is prime, so
       it is nonzero, so `A` answered with the right length.
     - **Coin law.** `statClose_roundSample` gives `(1 − m/2^k)^n ≤ (1/2)^n` from
       `lt_two_pow_kkOf`/`two_pow_kkOf_le`, and `abs_uprob_sub_le_prod` finishes.
     - **The bound.** LHS `− (1/2)^n ≤ Pr_ideal[P] − (1/2)^n ≤ Pr_sampled[P] = factorProb A'' n`
       for `n ≥ 1` (`0 < 4n³`).

     The sketch's trial layout (the first `n·k` of `n·m` position bits) is
     `OneWay.exists_posMachine`'s own, which the brief prescribes. The REPORT disclosed the
     departure from the `Bp`-block plan. Two nits:
     - the unrewritten preamble says the position uses `k n := Nat.size (m n)` bits, while the
       sketch says `kkOf m = ⌊log₂ m⌋ + 1`; these are equal for `m > 0`;
     - E1 adds "(with `YaoMachine.ρP_eval`)" to the sketch's functional-identity sentence.
   - **`fmult_weakOneWay`.** The closing step differs from the sketch and is sound:
     - negligibility of `factorProb (oneCallFactorer A)` at `c = 2` (`negligible_iff`, published,
       `Iff.rfl`) gives `n₁`;
     - for `n ≥ max n₁ 6`, a violation `1 − 1/q(n) < invProbAt` gives
       `factorProb ≥ 1/2 − 2n/2^n ≥ 1/4` (`fac_weak_key`, `fac_eight_mul_le`);
     - but `factorProb < 1/n² ≤ 1/36`.

     This proves the eventual bound directly. The frozen sketch argues "infinitely often … by
     `not_negligible_iff` (`c = 1`)". Its chain (conditioning, Claim 34.1, `primesPairEquiv`, the
     diagonal) is exactly `fac_weak_key`'s. Only the outer logic is contraposed.
   - **`fmult_prod_strongOneWay`.** The closing step differs from the sketch and is sound.
     `fac_strong_key` gives
     `invProbAt ≤ (1/2)^n + 4n³(factorProb A'' + (1/2)^n + 2n/2^n)`. The rearranged right side
     `2⁻¹^n + 4n³·factorProb + 4n³·2⁻¹^n + 8n⁴·2⁻¹^n` is negligible term by term
     (`negligible_two_pow_neg`, `mul_pow`, `const_mul`, `add`; the identity `e` is checked by
     `field_simp; ring`), and `Negligible.mono` from `n = 2` closes. The frozen sketch's
     contradiction is this inequality rearranged (its `factorProb A'' n ≥ (1/n^c − (1/2)^n)/(4n³)
     − 2n/2^n − (1/2)^n`).

     Both frozen sketches remain true at the level they describe. No edit is proposed; they can be
     refreshed at the next docstring window, which needs authorization, as in dl-a finding 7.
   - **Other frozen sketches (nits).**
     - **S1.** Its sketch builds the fallback `natToList n 2` from `unaryPoly`/`blockMap` with two
       constant branches. The proof uses one uniform string, `(0^n ++ 10).drop 2`
       (`fac_natToList_two`; `zerosPoly`, `append`, `pairDropPoly`). This was disclosed.
     - **`fmult_easy`.** Likewise for the numeral of `1`, `(0^{2n} ++ 1).drop 1`. This was
       disclosed.
     - **`factoringCollection_sampleClose`.** Its sketch describes S2's internals; the proof cites
       S2.

     The other target sketches match.

8. **nit: the REPORT's D11 line.** It says "`H.prime`: in S1". S1 and `samplePairRaw` take
   `hP : PolyTimeComputable primeStr`, which is `H.prime` only at its use in `factoringSampler`.
   `H.le` and `H.mul` are as stated. No missing operation.

9. **note: file size.** `Factoring.lean` is 1868 lines (1846 with E1–E2, 1832 with E1–E4; `wc -l`). That is
   over the 1000-line split threshold (`style_lint.py`: "must split"). The size is approved for this
   delivery and noted only. The REPORT's request (a size exception like RSA/Rabin, or a post-fill
   split) is the maintainer's to record.

10. **note: REPORT claims verified.** These are confirmed by this review's own runs:
    - all ten targets are filled, and there are no escalations;
    - 41 private `fac_` helpers;
    - no statement change;
    - the sweep tail (Factoring 0 / RSA 10 / Rabin 19 / facade 0 sorry warnings);
    - all axiom prints standard (so the absent `SorrySources.lean` was not needed);
    - the lint lines;
    - the worker's three seal controls and its two seal results (main and exceptions).

    The two departures from the REPORT are findings 1 and 2: the `ρP`/`coinLen` characterization
    and the undisclosed `FunFamily.prod`.

## Landing edits (exact)

The patch is `$SP/review-fac/edits/landing-edits.diff` (E1, E2). `git apply --check` is clean on
the head, and applying it reproduces `edits/FactoringEdited.lean` byte for byte.
- **Scope.** It touches only `TCSlib/Cryptography/Candidates/Factoring.lean` and changes no
  statement; the declfreeze comparison against the base is unchanged (`declfreeze-edited.log`).
  The one docstring change is a sentence in `exists_plantFactorer`'s sketch, which the brief
  already authorized the fill to rewrite.
- **Unsealed.** The edited file elaborates with 0 errors and 0 warnings (`FactoringEdited.out`).
- **Sealed.** With 60 names it gives 0 errors (`FactoringEditedSealed60.out`). With 62 names
  (`ρP` and `coinLen` added) it gives exactly the one forced `ans_layout` argument
  (`FactoringEditedSealed62.out`).
- **Lint.** `style_lint.py` reports only the size line (`style-lint-edited.log`, `style-lint-edited-next.log`).
- **Downstream.** The edits are private-helper and proof-only, and downstream modules read
  statements only, so they were not rebuilt against the edited file.

**E1** (finding 1), in `exists_plantFactorer`. Replace

```lean
  set ce := NUPPT.coinsEquiv_ofPolyTime hpoly (OneWay.YaoMachine.ρP D) (OneWay.YaoMachine.advP D)
    (OneWay.YaoMachine.adv D) (OneWay.YaoMachine.adv_length D) n with hce
```
by
```lean
  -- the coins of `A''` as the coins of a round (`NUPPT.coinsEquiv_ofPolyTime`, `ρP_eval`)
  set ce := (NUPPT.coinsEquiv_ofPolyTime hpoly (OneWay.YaoMachine.ρP D) (OneWay.YaoMachine.advP D)
    (OneWay.YaoMachine.adv D) (OneWay.YaoMachine.adv_length D) n).trans
    (Equiv.arrowCongr (finCongr (OneWay.YaoMachine.ρP_eval D n)) (Equiv.refl Bool)) with hce
  have hce_ofFn : ∀ r, List.ofFn (ce r) = List.ofFn r := fun r => by
    rw [hce, Equiv.trans_apply, ← NUPPT.coinsEquiv_ofPolyTime_ofFn hpoly _ _ _ _ n r]
    exact (List.ofFn_congr (OneWay.YaoMachine.ρP_eval D n) _).symm
```

Then make three more changes in the same proof:
- In `hround`, replace `← NUPPT.coinsEquiv_ofPolyTime_ofFn hpoly _ _ _ _ n r, ← hce,` by
  `← hce_ofFn r,`.
- In the binders of `hfp` and `key`, replace `(Fin ((OneWay.YaoMachine.ρP D).eval n) → Bool)` by
  `(Fin (n * fmultBlocks.eval n + (fmultBlocks.eval n * fmult.inLen.eval n + A.coinLen n)) → Bool)`.
- Replace the comment above `key` by `-- unfold the local abbreviation `S``.

In the sketch, replace "the coin identification `NUPPT.coinsEquiv_ofPolyTime` and the round
identity" by "the coin identification `NUPPT.coinsEquiv_ofPolyTime` (with `YaoMachine.ρP_eval`) and
the round identity", reflowed.

**E2** (finding 5). Move `fac_statClose_diag`, with its docstring and proof unchanged, to just
before `fac_uprob_primes_le`. Then replace `fac_uprob_primes_le`'s docstring and proof by

```lean
/-- **From uniform prime pairs to uniform distinct prime pairs**: for any event `G` of the two
primes and auxiliary coins, `Pr_{Π_n × Π_n}[G] ≤ Pr_{distinct}[G] + 2n/2^n`
(`fac_statClose_diag` tested on `G`, the auxiliary coins carried along:
`StatClose.abs_uprob_sub_le_prod`). -/
private theorem fac_uprob_primes_le {ρ : Type*} [Fintype ρ] [Nonempty ρ] (n : ℕ) (hn : 2 ≤ n)
    (G : ℕ → ℕ → ρ → Prop) :
    uprob (fun z : (Primes n × Primes n) × ρ =>
        G ((z.1.1 : Fin (2 ^ n)) : ℕ) ((z.1.2 : Fin (2 ^ n)) : ℕ) z.2) ≤
      uprob (fun z : DistinctPrimes n × ρ => G z.1.p z.1.q z.2) + 2 * n / 2 ^ n := by
  have h := (fac_statClose_diag n hn).abs_uprob_sub_le_prod fun v r => G v.1 v.2 r
  exact sub_le_iff_le_add'.1 (abs_sub_le_iff.1 h).1
```

The statement is unchanged; the old sketch goes because the proof no longer needs one.

**E3/E4** (finding 3; **conditional on #210's next round landing with these names**). The patch is
`$SP/review-fac/edits/conditional-210-edits.diff`, to apply on top of E1–E2 (clean, and it
reproduces `edits/FactoringEditedNext.lean`):
- **E3.** Delete `fac_yaoB_apply`, with its docstring. In `fac_prodInverter_eq_yaoB`, replace
  `rw [fac_yaoB_apply]` by `rw [OneWay.yaoB_apply]`.
- **E4.** Delete `fac_uniform_advice`, with its docstring. In `polyTimeComputable_samplePrimeL`,
  replace `fac_uniform_advice hAu (pairFstD z).length` by `hAu.advice_eq (pairFstD z).length`. If
  the round publishes `NUPPT.uniform_iff` instead, use `NUPPT.uniform_iff.1 hAu (pairFstD z).length`.

These were checked against stubs of exactly those statements, inserted before the namespace in a
test copy: unsealed 0/0 and sealed (62 names, `yaoB` and `Uniform` included) 0 errors. Recheck
against the real lemmas when they land. If #210's round lands first, apply E3/E4 at landing.
Otherwise land E1–E2 and keep `fac_yaoB_apply`/`fac_uniform_advice` as the recorded exceptions.

**D1** (findings 2 and 6; ledger, no code). Add to the integration ledger for `Factoring.lean`:
- **The rule-10 reading of `FunFamily.prod`.** It is forced by the frozen `prodInverter`, at
  `fac_prodInverter_eq_yaoB` and `fac_strong_key`. It joins the base re-point list with
  `eval_fmultWeakPoly` (`PolyExpr.eval_normal`), `fmult_prod_inLen` (`FunFamily.prod_inLen`),
  `samplePairOut_eq_encode` and `factoringCollection_index` (finding 4).
- **The forced `ρP`/`coinLen` reading.** It is the single `ans_layout` argument; the remedy is to
  restate `ans_layout`'s `rc`.
- **The near-duplicates.** Each with the source it copies:
  - `fac_chunkEquiv` (`FunFamily.blocks`/`OneWay.blocksE`);
  - `fac_arrowCongr`/`_ofFn` (`HardCoreLemmas.finCastEquiv`/`ofFn_finCastEquiv`);
  - `fac_ofFn_halves` (private `ofFn_blocks_two_symm`; `OneWay.ofFn_block_eq_take_drop`);
  - `fac_listToNat_inj` (private `Sampling.listToNat_inj`; `bitsToNat_injective`);
  - `fac_statClose_diag`/`fac_uprob_primes_le`, unless E2 lands.
- **The cross-unit numeral facts** of finding 6, as a request for a shared `Arithmetic.lean` set.

These come in addition to the REPORT's rows. Its requests are endorsed:
- `OneWay.yaoB_apply`;
- a reachable `NUPPT.Uniform` reading;
- `FunFamily.blocks_eq_blocksE` and a public `FunFamily.blocks_apply`.

## Logs (`$SP/review-fac/`, `SP=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`)

- **Replay and freeze:**
  - `am.log`: the `git am` replay (clean);
  - `fac.diff`: the reviewed diff;
  - `Factoring.base.lean`, `Factoring.head.lean`: the two sides;
  - `declfreeze_rev.py`, `declfreeze-rev.log`, `declfreeze-edited.log`: the freeze comparison.
- **Elaboration and axioms:**
  - `module-checks.log`: the five module checks with start times and durations; `run-checks.sh`
    is the driver;
  - `axioms.log`: the ten target prints and the per-module axiom sweep (`probe/Axioms.lean`).
- **Seal-name collection:**
  - `collect.log`: term-based and wide, with `SEALROW` lines;
  - `collect-names.txt`: the 66 names;
  - `lex.log`, `lex-defs.txt`: the lexical pass;
  - probe sources: `probe/Collect.lean`, `probe/Lex.lean`, `probe/lex-tokens.txt`; `probe/run1.sh`
    runs a probe against the olean copy.
- **`seal/`:**
  - generators `mkseal.py` (whole file) and `mkregion.py` (fill regions);
  - name lists `sealed-names-{all,65,62,62next,61,61e,60}.txt`;
  - whole-file seals `RevSealedFactoring{,2}.lean`/`.out` (66 and 65 names);
  - region seals `RevSealedRegions{,61,60}.lean`/`.out` (65, 61 and 60 names; the 61 run shows
    `coinLen` alongside `ρP`);
  - controls `RevControl.lean`/`.out`.
- **Rewrite rules and `simp?`:** `grep-foreign.txt` (foreign names in rewrite and unfold lists:
  none as a rule); `simpq.log` (`simp?` on the five bare `simp`s; `probe/SimpQ.lean`).
- **Duplication:** `neardup.log` (`probe/NearDup.lean`): the `chunk = FunFamily.blocks` and
  block-window reproofs, and `#check`s.
- **Base re-points:** `base-repoint.log` (`probe/BaseRepoint.lean`): the two base re-points,
  sealed.
- **Lint:** `style-lint-head.log`, `style-lint-edited.log`, `style-lint-edited-next.log`,
  `campaign-lint-head.log`.
- **`edits/`:**
  - the diffs `landing-edits.diff` (E1–E2) and `conditional-210-edits.diff` (E3/E4);
  - `FactoringEdited.lean`/`.out` (E1–E2, unsealed);
  - `FactoringEditedSealed{65,62,61,60}.lean`/`.out`. The 65 run is E1 only; the 62, 61 and 60
    runs are E1–E2;
  - `FactoringEditedNext.lean` (E1–E4);
  - `FactoringEditedNextStub{,Sealed62}.lean`/`.out` (E1–E4 against the stub lemmas).

The olean copy `$SP/review-fac/oleans` was deleted after the runs; recreate it from
`$SP/fill-fac-oleans` to replay. The scratch worktree `$SP/wt-rev-fac` was removed.
