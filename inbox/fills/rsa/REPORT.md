# Fill report: unit rsa (`TCSlib/Cryptography/Candidates/RSA.lean`)

**Status: final. 10 of 10 targets filled; 0 partial; 0 escalated.** No statement changed; no
`sorry` and no `axiom` added. The owned file checks with 0 errors and 0 warnings.

## Base, environment, preflight

- Base: `16a7d02d69cae1a700c131e3cc3dd918a7b3d6e1` (`git rev-parse`). Local branch `fill/rsa`,
  head `35c1abee23ef6a677af2e55313f7477594589587` (10 commits). It was never pushed and never
  rebased.
- I ran as an **internal worker under `issue/internal-env.md`**: the worktree, the
  `.lake/packages` link and the olean tree `fill-rsa-oleans` were provided. There was no
  preflight floor, no cache fetch and no bootstrap. Never `lake build`; one Lean process at a time.
- Machine at start (`evidence/logs/preflight.log`): `nproc` 4; MemTotal 16.5 GB; MemAvailable
  14.9 GB; 5.9 GB free on `/` (shared machine).
- Module checks go through `scripts/lean_check_tree.sh` with `TCSLIB_OLEANS=$OL`
  (`evidence/logs/module-checks.log`: every check with its start time and duration). The owned
  module takes 10–31 s per check. A few checks took 120–1250 s: these were failed experiments
  with a slow elaboration (see "Findings", item 1). The 1252 s run was a runaway that I killed.
  Scratch probes were compiled with plain `lean` against the same `LEAN_PATH` (no `-o`), from
  `$SP/fillwork-rsa/`.
- **The provided olean tree lacked** `Candidates/DiscreteLog`, `DiscreteLogHardcore`, `ElGamal`
  and the facade `Candidates`. I built those four unchanged base modules into `$OL` for the
  facade check (`evidence/logs/sweep.log`).

## Targets (brief order)

| # | Target | State | Route |
|---|---|---|---|
| 1 | `rsaSampler_spec` | filled | Follows the sketch, with a private activation lemma `rsa_sampler_runAt` (`NUPPT.runAtL_ofPolyTimeUniform`, the P5 equations). `rsaDec` accepts the sampler's numeral (`rsa_dec_unitSampleStr`). The evaluator clause is `rsaEnc_of_rsaDec` with `rsaEval_spec`, so I did not compute the decoded unit's value. |
| 2 | `statClose_sampleUnitL` (S3) | filled | Follows the sketch: `statClose_rejectBlocksL` with the default `1 % N`; the bijection `{v < 2^k ∣ v < N ∧ gcd = 1} ≃ (ZMod N)ˣ` (`rsa_unitsEquiv`, `StatClose.comp_equiv_right`); acceptance `Φ(N)/2^k` (`rsa_uprob_units`); `2^k ≤ Φ(N)(4n+8)` (`rsa_two_pow_size_le`: `Nat.size_le`, `Nat.pow_log_le_self`, `le_totient_mul_log_succ`); then `one_sub_one_div_pow_le_exp_neg`. |
| 3 | `rsaCollection_sampleClose` | filled | `δ n = 1` for `n < 2` and `e^{-n}` otherwise, as sketched. A generated modulus fits the blocks at every `n` (`2·max(n,2) ≤ 2(n+2)`), so both branches use S3: the `n < 2` branch takes S3 with `StatClose.mono`, `e^{-n} ≤ 1`, and P3 (`statClose_iff`) was not needed. The rest is `Collection.sampleClose_iff`, `rsaCollection_index`, `_sample`, `_decD`, `_domEquiv`, `NUPPT.coinsEquivPoly`, and `StatClose.map` through `rsaDec` (`rsa_statClose_dec`). |
| 4 | `polyTimeComputable_unitSampleStr` | filled | **Sketch rewritten** (a Correction target); see "Machines" below. |
| 5 | `polyTimeComputable_rsaGenRaw` | filled | **Sketch rewritten** (route "from S1"); see "Machines" below. |
| 6 | `polyTimeComputable_rsaFromFactorRaw` | filled | Sketch **not** rewritten (not a marked target), but the proof departs from it; see "Machines" below. |
| 7 | `rsaCollection_invProbAt_le` | filled | Follows the repaired (F05) sketch: a conditional expectation over `z`. Its Correction allows edits, and I only re-pointed clauses (i) and (ii) to S3 and S2. See "The reduction" below. |
| 8 | `factorProb_le_rsaProb` | filled | As sketched: `factorProb_eq`, `uprob_prod`, a coordinate reordering (`uprob_comp_equiv`, `uprob_fst`), `NUPPT.inverter_eq_some_iff`, `modulusBits_eq`, `rsaFromFactorer_runAt` (coins read through `rsaFromFactorer_coinsEquiv`), `rsaFromFactorStep_correct`. |
| 9a | `rsaCollection_oneWay` | filled | As sketched (`rsaAssumption_iff`, `Negligible.add`, `Negligible.mono`, `Collection.invProbAt_nonneg`). |
| 9b | `rsa_imp_factoring` | filled | As sketched, through `factoringAssumption_iff` (P14) and `rsaAssumption_iff`. |

### Machines (targets 4–6)

None of them builds a machine by hand. Every loop is the public repetition host
`Complexity.polyTimeComputable_iterateFind`, and every arithmetic step is a field of
`ArithmeticFP`.

- **`unitSampleStr`** (the brief's Correction is followed):
  - **Loop.** The host runs on the state `⟨⟨1^{B(n)}, ⟨1^k, w⟩⟩, ⟨counter, coins⟩⟩`. It starts
    with the counter `1^{T(n)}`; `1^k` comes from `H.size` and the unary values from
    `polyTimeComputable_unaryPoly`.
  - **Trial.** Each trial reads `k` bits (`pairTakePoly var`) and drops `B(n)` bits
    (`pairDropPoly var`).
  - **Test.** A trial is accepted iff the counter is nonempty and `¬ N ≤ v` (`H.le`), and the
    `|w|`-bit gcd numeral from `xgcdStr` reads `≤ 1` and `≥ 1` (two `H.le` tests against
    `[true]`). The counter is needed because the host searches `|x| + 1 ≥ T(n)` rounds (the same
    issue as in dl-a).
  - **Output width.** The output is the remainder of `H.divMod ⟨b, w⟩`. Here `b` is the accepted
    block, or `[true]` when no trial is accepted (`isNil`, `ite`). An accepted `v < N` is its own
    remainder, and `[true]` gives the fallback `1 mod N`. So no zero padding is needed: the
    brief's `dropPrefixByLength`/`blockMap` padding is replaced by one `H.divMod`.
  - **Order of declarations.** The proof lives in the private `rsa_ptc_unitSampleStr`, placed
    before `polyTimeComputable_rsaGenRaw` because the generator uses it. The public theorem keeps
    its position and is `by exact rsa_ptc_unitSampleStr H hf`.
- **`rsaGenRaw`:**
  - **`m = max n 2`.** The word `1^m` is `1^n`, or `11` when `n ≤ 1` (`polyTimeComputable_lenLe`,
    `_ite`). The rest runs on `⟨1^m, r⟩`.
  - **Primes.** The two prime runs are S1 on `pairTakePoly`/`pairDropPoly samplePrimeCoins`.
  - **Validity test.** The test is built from `H.prime` twice, two `H.le` comparisons for `p ≠ q`,
    and two `H.le` comparisons with `⟦1^m⟧ = 2^m − 1` for `p, q < 2^m`. It avoids reading
    `samplePrimeL`'s body: P11 is not published.
  - **Fallback.** The fallback words are the constants `10` and `11`.
  - **Arithmetic.** `N`, `Φ` and `d` come from `H.mul`, `H.sub` and `H.xgcd`. The exponent `e` is
    `polyTimeComputable_unitSampleStr` on `layout 1^m ⟦Φ⟧ [] (r.drop 4m³)`, as the brief says.
  - **Output width.** Each `2m`-bit numeral is the remainder of `H.divMod` modulo the all-ones
    word `1^{2m}`. This is valid because `N, e, d < 2^{2m} − 1`.
  - **Correctness.** Correctness is `rsa_genCore_spec`.
- **`rsaFromFactorRaw`** departs from the frozen sketch in four ways (I suggest refreshing the
  sketch):
  1. The test `p'q' = N` is two `H.le` comparisons, as the brief says.
  2. The `2n`-bit output is a truncation `(⟦0⟧_{2n} ++ v).drop |v|`, with
     `⟦0⟧ = H.sub ⟨1^{2n}, 1^{2n}⟩` and `pairDropPoly var`. The sketch used
     `unaryPoly`/`blockMap`.
  3. **Degenerate inputs.** The `Φ` word gets one leading zero, and the modulus word given to
     `H.modExp` gets `|y| + 1` leading zeros. Without them, `xgcdStr`/`modExpStr` truncate at
     the word width, and the computation is wrong on degenerate inputs. The case is
     `N = 0` (then `Φ = 0`, `Z_0 = ℤ`, `d ≤ 1`, and `y^d mod 0 = y^d`).
  4. With these prefixes, every word reads exactly (`rsa_fOut_eq`).

### The reduction (target 7)

The chain is:

`invProbAt ≤ E_r g(N_r, e_r) = E_{s₁} E_{s₂} g(z(s₁), e(z(s₁), s₂)) ≤ E_{s₁} F(z(s₁)) + e^{-n} ≤ E_z F(z) + δ₂ + e^{-n} = rsaProb A' n + rsaGenErr n`.

1. **The inner event.** At one index, an inversion is an RSA success of `A' = rsaBreaker A` on the
   challenge `u^e`, with the coins `φ⁻¹ ω` (`rsa_inv_imp`, `rsa_inner_le`). It goes through
   `rsaCollection_domEquiv`, `rsaBreaker_runAt` (coins through `rsaBreaker_coinsEquiv`) and
   the injectivity of `rsaF`. The modulus moves from `rsaMod i` to `N` by `rsa_g_congr`.
2. **The coin split.** The generator's coins split as `(s₁, s₂)`, two prime segments followed by
   the exponent segment (`rsa_genCoinsEquiv`, `HardcoreBit.uexp_comp_equiv`). Then
   `rsa_genParams_z` and the selection `rsa_zOf` identify the primes (`rsa_g_split`).
3. **Step (i)** is S3 at the modulus `Φ(N)`, with `StatClose.abs_uprob_sub_le_prod`
   (`rsa_step_i`).
4. **Step (ii)** is S2 mapped through `rsa_zOf` (`rsa_zOf_self`). The average of `F` becomes a
   probability over a uniform family `ω ∈ Π_z Aux z` (`rsa_uprob_pi_eval`: `Equiv.piSplitAt`,
   `uprob_fst`), as in the sketch (`rsa_step_ii`).

## New private declarations (101, all `private` and `rsa_`-prefixed)

The full list is in `evidence/logs/declfreeze.log`. By role:

- **S3:**
  - `rsa_one_mod_spec`, `rsa_getD_spec`: the default `1 % N` is a unit;
  - `rsa_unitsEquiv`, `rsa_uprob_units`, `rsa_two_pow_size_le`.
- **Samplers:**
  - `rsa_sampler_runAt`, `rsa_dec_unitSampleStr`, `rsa_coins_sampler`;
  - `rsa_size_N_le`, `rsa_statClose_dec`.
- **Unit-sampler loop:**
  - `rsa_listToNat_one`, `rsa_listToNat_nil`, `rsa_findSome?_ite`, `rsa_find?_range_lt`,
    `rsa_unitTest_eq`;
  - the loop data `rsa_usStart`, `rsa_usStep`, `rsa_usBlock`, `rsa_usGcd`, `rsa_usAcc`,
    `rsa_usOut`, `rsa_usLoop`, which are data for the public host (no new host);
  - their polynomial time `rsa_*_poly`, the orbit lemmas `rsa_usStep_iterate` and
    `rsa_length_usStep_*`, the correctness `rsa_usFind_eq`, and `rsa_ptc_unitSampleStr`;
  - the combinators `rsa_comp` (applied composition), `rsa_le_poly`, `rsa_prime_poly`,
    `rsa_ptc_congr`.
- **Generator:**
  - `rsa_listToNat_ones`, `_two`, `_three`, `rsa_listToNat_mulStr`, `rsa_norm`;
  - the words `rsa_gP`, `rsa_gQ`, `rsa_gValid`, `rsa_gPw`, `rsa_gQw`, `rsa_gPhi`, `rsa_gE`,
    `rsa_gNorm`, `rsa_genCore`, with their `_poly` lemmas;
  - `rsa_genCore_spec`.
- **`A'`:**
  - `rsa_listToNat_append`, `rsa_listToNat_zeros_append`, `rsa_drop_zeros_append`,
    `rsa_subStr_self`, `rsa_val_inv_zero_le`;
  - the words `rsa_fS`, `rsa_fQ`, `rsa_fTest`, `rsa_fPhi`, `rsa_fD`, `rsa_fV`, `rsa_fOut`;
  - `rsa_fOut_poly`, `rsa_fOut_eq`.
- **Reduction:**
  - `rsa_neZero_N` (a private instance), `rsa_T`, `rsa_g`, `rsa_g_congr`, `rsa_rsaF_injective`;
  - `rsa_inv_imp`, `rsa_inner_le`;
  - `rsa_zsel`, `rsa_genParams_z`, `rsa_zOf`, `rsa_zOf_pq`, `rsa_zOf_self`;
  - `rsa_appendEquiv`, `rsa_genCoins_len`, `rsa_coins_gen`, `rsa_genCoinsEquiv`,
    `rsa_genCoinsEquiv_ofFn`, `rsa_pr`, `rsa_eNum`, `rsa_g_split`;
  - `rsa_F`, `rsa_rsaProb_eq`, `rsa_step_i`, `rsa_Aux`, `rsa_uprob_pi_eval`, `rsa_step_ii`.

Every private proof longer than about 20 lines has a **Proof sketch.** (`style_lint.py` finds
no missing sketch).

### Duplication disclosure (for approval)

The following are **copies of other units' private proofs** (dl-a's `DiscreteLog.lean`, in
dl-a's delivery, not landed and not in my imports), re-proved under my prefix:

| Copy | Source | Size |
|---|---|---|
| `rsa_findSome?_ite`, `rsa_find?_range_lt`, `rsa_listToNat_nil` | `dla_findSome?_ite`, `dla_find?_range_lt`, `dla_listToNat_nil` | about 40 lines |
| `rsa_listToNat_append` | `dla_listToNat_append`, itself a re-proof of the private `foldl_bits_eq` of `Asymptotic/Sampling.lean` | 12 lines |
| `rsa_drop_zeros_append` | `dla_drop_natToList_zero_append` | 20 lines |
| `rsa_usStep`, `_usBlock`, `_usOut`, `_usStep_poly`, `_usBlock_poly`, `_usStep_iterate`, `rsa_length_usStep_*` | the `dla_ss*` loop family (the same step, block and orbit bound) | about 70 lines |

The acceptance test, the payload handling and the correctness lemma `rsa_usFind_eq` are new;
the matcher handling (`split` into `Option.elim`) is new.

**Near-duplicates of the library:**
- `rsa_comp` is the private `ptc_comp` of `Randomized/Closure.lean` (also private in
  `Asymptotic/Collections.lean`, `UniversalLemmas.lean` and `EnsemblesLemmas.lean`).
- `rsa_unitsEquiv` and `rsa_two_pow_size_le` follow dl-a's `statClose_sampleBelowL` inline
  bijection and its bound `2^k ≤ 2m`.
- `rsa_uprob_pi_eval` is a generic probability fact; I found no TCSlib form of it.

**Mathlib first:** the number theory used is Mathlib's (`Nat.size_le`, `Nat.lt_size_self`,
`Nat.pow_log_le_self`, `Nat.totient_le`, `ZMod.card_units_eq_totient`, `ZMod.unitOfCoprime`,
`Int.natAbs_sign`, `Equiv.piSplitAt`, `List.ofFn_fin_append`), together with TCSlib's
`le_totient_mul_log_succ`.

### Requested shared lemmas

1. A public **block rejection loop**, `polyTimeComputable_rejectBlocksL` for a polynomial-time
   test, as the brief anticipates. rsa, rabin and dl-a each build it now (`rsa_us*`, `dla_ss*`).
2. `listToNat_append`, `listToNat_replicate_true` (`= 2^k − 1`) and the truncation lemma
   `(⟦0⟧_W ++ b).drop |b| = ⟦⟦b⟧⟧_W`, beside `listToNat`/`natToList`.
3. A public applied-form composition `PolyTimeComputable.comp'` (`x ↦ g (f x)`).
4. `uprob_pi_eval` (`Pr_{ω ∈ Π}[Q (ω c)] = Pr[Q]`) in `Foundations/Probability.lean`.

## Rule 10

- **Seal** (`evidence/seal/RSASealed.lean`, `evidence/logs/seal-main.log`; the list is
  `evidence/seal/seal-list.txt`, 49 names). I found the foreign definitions mentioned by the
  new code with a probe (`evidence/seal/ForeignDefsProbe.lean`, output
  `foreign-defs-mentioned.txt`) and added those read only through types or lemmas. The seal
  includes the compiler-generated matcher `Complexity.polyTimeComputable_iterateFind.match_1`;
  my proof reads it by `split`.
  - **Result:** all ten filled bodies and all 101 `rsa_` helpers elaborate sealed.
  - The only four errors are in frozen base proofs, not in targets: `eval_rsaBlock`,
    `eval_rsaTrials` and `eval_rsaSampleCoins` (`rfl` through `PolyExpr.eval`), and
    `rsaCollection_index` (`show` through `Collection.index`/`NUPPT.runAt`).
  - No foreign definition carries `@[simp]`, so no `[-simp]` was needed.
- **Not sealable:**
  - the reducible abbreviations `DistinctPrimes` and `NUPPT.Coins` (notation, per policy);
  - the structure projections `NUPPT.coins` and `NUPPT.advice`. They are never unfolded.
- **Controls** (`evidence/seal/SealControl.lean`, `evidence/logs/seal-control.log`): three
  readings by `rfl` (of `natToList`, `NUPPT.inParam` and `leStr`) close unsealed and fail
  sealed. That gives three errors, all in the sealed namespace.
- **Exceptions: none.** Every foreign TCSlib definition is read through a published lemma.
  Core and Mathlib reductions occur only in `rfl`/`show`:
  - `List.foldl` after `listToNat_eq`;
  - the application of `Equiv.prodComm`, `prodAssoc`, `prodCongr`, `arrowCongr` and
    `finCongr`;
  - the inverse and value in `ZMod 0` (`rsa_val_inv_zero_le`).
  - Own definitions such as `rsaGenParams` are read by `rfl`/`unfold`.

## D11

- **Fields used:**
  - `unitSampleStr`: `size`, `le`, `xgcd`, `divMod`;
  - `rsaGenRaw`: `prime` (S1 and the validity test), `le`, `mul`, `sub`, `xgcd`, `divMod`, and
    those of `unitSampleStr`;
  - `rsaFromFactorRaw`: `divMod`, `mul`, `le`, `sub`, `xgcd`, `modExp`.
- **Missing operations: none.**

## Checks

- **Owned file:** 0 errors, 0 warnings, no `sorry` (rc 0, 29–31 s).
- **Sweep** (`evidence/logs/sweep.log`): the owned file and every later module of `order.txt`
  that imports it, namely `Rabin` and the facade:
  ```
  == TCSlib/Cryptography/Candidates/RSA rc=0 secs=31 sorry-warnings=0 errors=0
  == TCSlib/Cryptography/Candidates/Rabin rc=0 secs=8 sorry-warnings=19 errors=0
  == TCSlib/Cryptography/Candidates rc=0 secs=4 sorry-warnings=0 errors=0
  ```
  Rabin keeps its 19 targets. The facade's first attempt failed only because the provided tree
  had no `DiscreteLog` olean. I built `DiscreteLog`, `DiscreteLogHardcore` and `ElGamal` (base
  versions, rc 0) and re-checked the facade (rc 0).
- **Axiom prints** (`evidence/logs/axioms.log`, probe `evidence/AxiomsRSA.lean` with the
  review's `#review_sorry` command; `preship/probes/SorrySources.lean` is not in the issue
  tree).
  - **No `sorryAx`:** `polyTimeComputable_unitSampleStr`, `polyTimeComputable_rsaFromFactorRaw`,
    `factorProb_le_rsaProb` and `rsa_imp_factoring` print `[propext, Classical.choice, Quot.sound]`.
  - **With `sorryAx`,** printing the triple plus `sorryAx`:

    | Target | Sources (`ALL`) |
    |---|---|
    | `statClose_sampleUnitL` | `statClose_rejectBlocksL` |
    | `polyTimeComputable_rsaGenRaw` | `polyTimeComputable_samplePrimeL` (S1) |
    | `rsaSampler_spec` | S1 |
    | `rsaCollection_sampleClose` | S1, `statClose_rejectBlocksL` |
    | `rsaCollection_invProbAt_le` | S1, `statClose_rejectBlocksL`, `statClose_samplePrimeL_pair` (S2) |
    | `rsaCollection_oneWay` | S1, `statClose_rejectBlocksL`, S2 |

    S1 is reached through the generator's type, since `rsaGen` carries
    `polyTimeComputable_rsaGenRaw`.
  - **D3: pass.** Every source is in rsa's permitted set (S1, S2 and `statClose_rejectBlocksL`),
    and no machine-layer declaration is reached. fac and dl-a report all three filled on their
    branches.
- **Lint:**
  - `style_lint.py` reports exactly one finding, the line count (2758 > 1000). This is the
    approved size exception, and the file is not split (`evidence/logs/style-lint.log`).
  - `campaign_style_lint.py --check8b` shows no FAIL row for `RSA.lean`. It shows the size WARN,
    and the check-8 WARN list is identical to the issue tree's 18 names, so there is no new
    public `def` (`evidence/logs/campaign-lint.log`, base run `campaign-lint-base.log`). The
    other files' rows are unchanged.
- **Statement freeze** (`evidence/logs/declfreeze.log`, script `evidence/declfreeze.py`):
  - all 117 base declarations keep their headers byte-identical, and every non-theorem body is
    identical; the result is PASS;
  - the 101 new declarations are all private and `rsa_`-prefixed;
  - docstrings changed only for `polyTimeComputable_unitSampleStr` (Correction),
    `polyTimeComputable_rsaGenRaw` (from S1) and `rsaCollection_invProbAt_le` (Correction).
    The changes are in their Proof sketch paragraphs;
  - the diff touches only the owned file.

## Findings and notes for the maintainer

1. **Unification can unfold bundle string functions, and the cost explodes.** An ascription such
   as `have hg : PolyTimeComputable rsa_usGcd := pairFstD.comp (H.xgcd.comp …)` or
   `polyTimeComputable_isNil.comp hL` took 120 s, or did not finish in 20 min. The cause is lazy
   delta, which unfolds `xgcdStr` or the loop's `List.find?` before `Function.comp`.
   - **Fix:** state each composite in applied form (`rsa_comp : PTC g → PTC f → PTC (x ↦ g (f x))`),
     give `polyTimeComputable_and`/`_ite` their tests explicitly, and fold into a definition only
     by `unfold`. The whole file then checks in 30 s.
   - The fill briefs could prescribe this pattern.
2. **The host's `match` cannot be rewritten** with a match written elsewhere, because the
   matchers differ. `rsa_usLoop_poly` converts it once into `Option.elim` by `split` (under the
   seal).
3. **The sketch of `polyTimeComputable_rsaFromFactorRaw` needs a refresh** at the next docstring
   window (see "Machines"). The sketch of `rsaCollection_sampleClose` mentions P3, which the
   proof does not need.
4. **The olean tree** for this unit lacked the three discrete-log modules and the facade.
5. **Size:** the file is 2758 lines, under the approved exception; it is not split.

## Delivery

`inbox/fills/rsa/` on `exchange/pass-shelat-ch5-8`:
- `REPORT.md`;
- `patches/` (`git format-patch 16a7d02d..fill/rsa`, 10 patches);
- `src/TCSlib/Cryptography/Candidates/RSA.lean`;
- `evidence/` (logs, seal files, probes, declfreeze script).

The pushes were `fill rsa: checkpoint 1` to `checkpoint 8`, then `fill rsa: final`.
