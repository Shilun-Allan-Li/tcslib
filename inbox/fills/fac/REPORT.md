# Fill report: unit fac (`TCSlib/Cryptography/Candidates/Factoring.lean`)

**Status: final. 10 of 10 targets filled; 0 partial; 0 escalated as false.** One finding needs a
maintainer decision: the file size (see "Findings").

## Base, environment, preflight

- Base: `16a7d02d69cae1a700c131e3cc3dd918a7b3d6e1` (`git rev-parse`; it is also
  `git merge-base fill/fac` of itself). The local branch is `fill/fac`, with head `e932cd15`. It
  was never pushed and never rebased.
- I ran as an **internal worker under `issue/internal-env.md`**. The worktree, the
  `.lake/packages` link and the olean tree were provided, so there was no preflight floor, no
  cache fetch and no bootstrap.
- Machine at start (`evidence/logs/preflight.log`): `nproc` 4; MemTotal 16.5 GB; MemAvailable
  15.5 GB; no cgroup `memory.max`. The scratch filesystem is ext4 with 7.7 GB free, on a shared
  machine.
- Module checks used `scripts/lean_check_tree.sh` with `TCSLIB_OLEANS=$OL`, one Lean process at a
  time. `evidence/logs/module-checks.log` has every check of the owned module, with its start
  time, end time and duration: 4–21 s each. I compiled scratch probes with plain `lean` against
  the same `LEAN_PATH` (no `-o`), from `$SP/fillwork-fac/`.

## Targets

| # | Target | State | Notes |
|---|---|---|---|
| 1 | `statClose_samplePrimeL_pair` (S2) | filled | Followed the sketch. |
| 2 | `factoringCollection_sampleClose` | filled | `δ n = 1` for `n < 2`, and `2(1/2)^n + 2n/2^n` otherwise. S2 is mapped through `samplePairOut`/`decodeDistinctPrimes` (`StatClose.map`). |
| 3 | `polyTimeComputable_samplePrimeL` (S1) | filled | Followed the sketch: the black box `exists_samplePrime_nuppt`, `padStr`, `lenEq` and `ite`. The fallback numeral is computed as `(0^n ++ 10).drop 2` for every `n`, so there is no three-way branch. |
| 4 | `polyTimeComputable_samplePairRaw` | filled | Each half comes from S1. **I rewrote the Proof sketch** (route "from S1"). On acceptance `n ≥ 2`, so no re-encoding is needed. The default pair is `⟨(0^n).drop 2 ++ 10, (0^n).drop 2 ++ 11⟩` for every `n`, so there is no branch on `n < 2`. |
| 5 | `fmult_easy` | filled | Followed the sketch. The numeral of `1` is `(0^{2n} ++ 1).drop 1`, built with `polyTimeComputable_zerosPoly` instead of `blockMap`. |
| 6 | `exists_plantFactorer` | filled | **I rewrote the Proof sketch** (route correction). See "Route of `exists_plantFactorer`". |
| 7 | `factoringCollection_invProbAt_le` | filled | Followed the sketch (`collectionFactorer_runAt`, with the coins read through `collectionFactorer_coinsEquiv`). |
| 8a | `factoringCollection_oneWay` | filled | As sketched. |
| 8b | `fmult_weakOneWay` | filled | Uses the sketch's chain. The contradiction is taken at each `n ≥ max n₁ 6` against `factorProb < 1/n²` (negligibility at `c = 2`), not through `not_negligible_iff`. |
| 8c | `fmult_prod_strongOneWay` | filled | Uses the sketch's chain as a **direct bound**, `invProbAt ≤ (1/2)^n + 4n³(factorProb A'' + (1/2)^n + 2n/2^n)`, which is negligible. The sketch argues by contradiction instead. |

No statement changed. No `sorry` and no `axiom` were added.

### Route of `exists_plantFactorer`

I followed the brief's route correction (the position from `OneWay.exists_posMachine`, the model
`OneWay.exists_yaoReduction`) by **reusing the proved one-round machine itself**:

- **Machine.** `A''` is `NUPPT.ofPolyTime` of the first `n` bits of `OneWay.YaoMachine.ans`. It
  is instantiated with the evaluator of `fmult_easy`, `OneWay.exists_prodEval`,
  `OneWay.exists_posMachine`, `m = fmultBlocks` and `A`. Its coins are `YaoMachine.ρP` and its
  advice is `YaoMachine.adv`.
- **Lemmas.** The round identity is `YaoMachine.ans_layout`. The coin law is
  `OneWay.statClose_roundSample`.
- **Trials.** Each trial is `k = OneWay.kkOf m` bits, read from the first `n·k` of the round's
  `n·m` position bits (the round's own layout). The sketch cut `Bp`-bit blocks with `blockMap`
  instead. `kkOf m = ⌊log₂ m⌋ + 1` satisfies `m ≤ 2^k ≤ 2m`, which is all the bound needs.
- **Inverter.** `ans_layout` is stated with the padded inverter `OneWay.yaoB`. The step from
  `prodInverter A n` to `yaoB` is `fac_prodInverter_eq_yaoB`: a success of `prodInverter` forces
  a right-length answer, and on such an answer both read the same block.

No machine was built by hand.

## New private declarations (41, all `private` and `fac_`-prefixed)

- **Numerals and blocks:**
  - leading zeros and small numerals: `fac_foldl_replicate_false`, `fac_natToList_lead`,
    `fac_natToList_one`, `fac_natToList_mod`, `fac_natToList_two`, `fac_natToList_small`;
  - words and their values: `fac_listToNat_inj`, `fac_length_samplePrimeL`,
    `fac_bitsToNat_false`;
  - block bijections: `fac_ofFn_halves` (the halves of a `2n`-bit string are its two blocks),
    `fac_blocks_eq_blocksE` (`FunFamily.blocks = OneWay.blocksE`), `fac_blocks_apply`;
  - coin casts: `fac_arrowCongr`, `fac_arrowCongr_ofFn`.
- **`fmult_easy`:** `fac_polyTimeComputable_isOne` (the test "reads as 1", by two `H.le`).
- **One-wayness chains:** `fac_PrimeBlocks` (the good set), `fac_halvesEquiv`,
  `fac_halvesEquiv_apply`, `fac_density`, `fac_goodEquiv`, `fac_goodEquiv_val`,
  `fac_uprob_primes_le` (from prime pairs to distinct prime pairs), `fac_fmultNat_of_prime`,
  `fac_weak_key`, `fac_eight_mul_le`, `fac_strong_key`.
- **Planting:** `fac_yaoB_apply` (rule-10 exception, below), `fac_prodInverter_eq_yaoB`.
- **S1, S2 and the sampler:**
  - `fac_uniform_advice` (rule-10 exception, below);
  - S2: `fac_chunkEquiv`, `fac_one_sub_pow_le_half_pow`, `fac_statClose_samplePrimeL`,
    `fac_statClose_diag`;
  - sampler decoding: `fac_encode_default`, `fac_pairDec`, `fac_decode_samplePairOut`,
    `fac_pairDec_pq`, `fac_statClose_decode`, `fac_negligible_delta`.
- **Collection reduction:** `fac_fmultNat_pq`, `fac_invProb_le`.

Every private proof longer than about 20 lines has a **Proof sketch.**, and the style lint finds
no missing sketch.

**Duplication disclosure.** No proved material was copied from another file. Three helpers are
near-duplicates of published patterns, written because the published form does not fit the
types:
- `fac_arrowCongr`/`_ofFn` is the `finCongr` coin cast of `NUPPT.coinsEquivPoly`/`coinsCongr`,
  here between two `Fin` lengths rather than two machines.
- `fac_chunkEquiv` packages `chunk` as an equivalence; the `chunk` facts in `Primality.lean` are
  private.
- `fac_blocks_eq_blocksE` exists because `FunFamily.blocks` and `OneWay.blocksE` are two copies
  of one definition.

**Requested shared lemmas.**
- `OneWay.yaoB_apply`, beside `OneWay.yaoB` (`Asymptotic/OneWayYao.lean`), with the statement of
  `fac_yaoB_apply`.
- `NUPPT.uniform_iff`/`Uniform.advice_eq`, reachable from `Randomized/PPT.lean`. They live in
  `Randomized/NonUniform.lean`, outside this module's imports.
- `FunFamily.blocks_eq_blocksE`, and a public `FunFamily.blocks_apply` (the current one is private
  in `OneWay.lean`).

## Rule 10

- **Seal** (`evidence/logs/seal-main.log`; the list is `evidence/seal-list.txt`, 51 definitions).
  I compiled a copy of the owned file with `attribute [local irreducible]` on every foreign
  definition that the filled bodies read. None of them carries `@[simp]`, so no `[-simp]` was
  needed.
  - **Result: all ten filled bodies and all `fac_` helpers elaborate sealed.**
  - The only two errors are in base proofs, which are frozen and not targets:
    `samplePairOut_eq_encode` (an `rfl` through `encodeDistinctPrimes`) and
    `factoringCollection_index` (`simp [factoringCollection, …]`).
- **Exception seal** (`evidence/logs/seal-exceptions.log`). The same seal plus `NUPPT.Uniform` and
  `OneWay.yaoB` gives exactly two further errors, at `fac_uniform_advice` and `fac_yaoB_apply`.
  These are the two isolated exception sites.
- **Controls** (`evidence/SealControl.lean`, `evidence/logs/seal-control.log`). Three readings by
  `rfl` (of `natToList`, `NUPPT.inParam` and `padFin`) close unsealed and fail sealed: three
  errors, all in the sealed namespace.
- **Exceptions** (readings that no published lemma covers):
  1. `OneWay.yaoB` has no published equation. It is read once, in `fac_yaoB_apply`, by `rfl`. The
     reading is needed because `YaoMachine.ans_layout` is stated with `yaoB`.
  2. `NUPPT.Uniform` is read once, in `fac_uniform_advice` (`hA n`). Its published reading is in
     `NonUniform.lean`, which this module does not import, and no import is authorized.
  3. Type-level readings left unsealed, inherited from frozen or published statements:
     - `PolyExpr.eval`, through the types of the frozen `fmult` and `fmult.prod`;
     - `NUPPT.coinLen` and `YaoMachine.ρP`, through the coin types in the published statements of
       `ans_layout` and `roundSample`. `coinLen_eq` and `ρP_eval` cover them, both by `rfl`.

## D11

- **Fields used:**
  - `H.le` and `H.mul`: in `fmult_easy`, through it in `exists_plantFactorer`, and in both
    one-wayness theorems;
  - `H.prime`: in S1, and as `hP` in `samplePairRaw`.
- **Missing operations:** none.

## Checks

- **Owned file:** 0 errors, 0 warnings and no `sorry` (`evidence/logs/module-checks.log`).
- **Sweep** (`evidence/logs/sweep.log`): the owned file and every later module of `order.txt`
  that imports it. The tail:
  ```
  == TCSlib/Cryptography/Candidates/Factoring rc=0 secs=12 sorry-warnings=0 errors=0
  == TCSlib/Cryptography/Candidates/RSA rc=0 secs=8 sorry-warnings=10 errors=0
  == TCSlib/Cryptography/Candidates/Rabin rc=0 secs=9 sorry-warnings=19 errors=0
  == TCSlib/Cryptography/Candidates rc=0 secs=3 sorry-warnings=0 errors=0
  SWEEP PASS
  ```
  RSA and Rabin keep their own unfilled targets, 10 and 19.
- **Axiom prints** (`evidence/logs/axioms.log`, at head `e932cd15`). All ten targets print
  `[propext, Classical.choice, Quot.sound]`. There is no `sorryAx`, so the sorry-source probe has
  nothing to list for any target. `preship/probes/SorrySources.lean` is not in the issue tree (it
  was a before-issue item), and it was not needed here.
- **Lint** (`evidence/logs/style-lint.log`, `evidence/logs/campaign-lint.log`):
  - `style_lint.py` reports exactly one finding for `Factoring.lean`: the line count (see
    Findings).
  - `campaign_style_lint.py --check8b` shows no FAIL row for `Factoring.lean`, and a size WARN.
  - Its check-8 WARN lists `fmultBlocks, fmultWeakPoly, plantFactor, prodInverter,
    samplePairRaw, samplePrimeL`. This is a subset of the issue tree's list, so there is no new
    public `def`.
- **Statement freeze** (`evidence/logs/declfreeze.log`, script `evidence/declfreeze.py`):
  - all 64 base declarations keep their headers byte-identical, and every non-theorem body is
    identical;
  - the 41 new declarations are all private and `fac_`-prefixed;
  - docstrings changed only for `polyTimeComputable_samplePairRaw` and `exists_plantFactorer`.
    Those are their Proof sketch paragraphs, and both are routes the brief corrects;
  - the diff touches only the owned file.

## Findings

1. **Size (needs a decision).** `Factoring.lean` grows from 870 to 1868 lines. The brief expects
   no `style_lint` finding for it, and ground rule 7 forbids splitting, so the fill is not split.
   I request the same size exception as RSA and Rabin, or a split at landing. Most of the growth
   (about 1000 lines including sketches) is the two one-wayness chains, the S1, S2 and sampler
   proofs, and the planting reduction.
2. The rule-10 exceptions 1 and 2 above, with their requested shared lemmas.
3. `SorrySources.lean` is absent from the issue tree. It was not needed, since no print shows
   `sorryAx`.

## Delivery

The delivery is `inbox/fills/fac/` on `exchange/pass-shelat-ch5-8`. It holds:
- `REPORT.md`;
- `patches/` (`git format-patch 16a7d02d..fill/fac`, 11 patches);
- `src/TCSlib/Cryptography/Candidates/Factoring.lean`;
- `evidence/`.

The pushes were `fill fac: checkpoint 1` to `checkpoint 8`, then `fill fac: final`.
