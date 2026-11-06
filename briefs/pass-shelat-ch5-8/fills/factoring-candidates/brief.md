# Fill brief: the factoring-based candidates (`Candidates/{Factoring, RSA, Rabin}`)

**Status: @ISSUED@.** Issue commit: `@ANCESTOR@`.

- **The statement gate is closed.** Gate 03f2 (`gates/03-ch2-4/03f2-pack.md`, findings
  `findings/gate03f2-findings.md`) closed at 0 blockers, 0 majors and 8 minors. It gave all 36
  `sorry`s a verdict: 13 (a), 23 (b), none (c). Minors F01 and F03–F08 were repaired in the merged
  batch PR #206 (commit `0701c7cc8a51bdbe7d755f81d15c2cf4d6941ccd`, docstrings and sketches only);
  F02 was a records fix. The sketches below are the repaired ones. In particular,
  `polyTimeComputable_samplePairRaw` (F08) and `rsaCollection_invProbAt_le` (F05) follow their
  rewritten sketches.
- **Ruled 2026-11-06:** fill all 36 targets. The three units run in parallel, because cross-file
  dependencies are on statements only.
- **Before issue (maintainer):**
  - the rule-10 prerequisites P1–P12 below, or a ruling that waives some of them;
  - decisions D1–D3 (shared statements, the Rabin split, the axiom criterion);
  - a review of this brief by a review sub-agent;
  - the issue commit (`@ANCESTOR@`). If it moves past `5f2771631fe853dae9c2aa44791ae5b0e09c95eb`,
    re-run the inputs and the probes of the pre-ship record.

The targets were written by Frederick Dehmel's campaign (run 2) and had the run-3a internal audit
and the 03f2 external audit. This campaign owns them.

## Repository, branch and delivery: read this before anything else

- Clone `https://github.com/Shilun-Allan-Li/tcslib` and check out `cryptography/pass-shelat-ch2-4`
  at the issue commit `@ANCESTOR@`.
- Work on a local branch `fill/<unit>` (`fill/fac`, `fill/rsa` or `fill/rabin`) created at
  `@ANCESTOR@`. **Never push it.** Record the base hash in `REPORT.md`, and never rebase.
- **Delivery is by the exchange protocol** (the exchange branch's `README.md`). Push the folder
  `inbox/fills/<unit>/` on the branch `exchange/pass-shelat-ch5-8`, from a separate checkout or
  worktree of that branch. The folder holds:
  - `REPORT.md`;
  - `patches/`: the whole series from `git format-patch @ANCESTOR@..fill/<unit>`;
  - `src/`: the owned file(s) at your head, under their repository paths;
  - `evidence/`: the logs this brief and the addendum require (preflight, cache, bootstrap,
    sweep, axiom prints, seal, lint).
- Push the folder at each checkpoint with the commit message `fill <unit>: checkpoint <n>`, and
  at the end with `fill <unit>: final`. If a session ends early, its last checkpoint is the
  delivery.
- Write only `inbox/fills/<unit>/`. Run `git pull --rebase origin exchange/pass-shelat-ch5-8`
  before each push. If a push is rejected, pull with rebase again and retry. Never force-push,
  and open no PRs. Never merge the exchange branch anywhere.
- **Source:** `Pass–Shelat.pdf` at the root of the campaign branch ([PS10], 3rd ed., January
  2010; book page = PDF page − 12). You need §2.3–§2.4 (pp. 29–38), §2.7 (Theorem 51.1), and
  §2.9–§2.12 (pp. 52–63).

## Units (disjoint file ownership; they may run in parallel)

| Unit | Owned file | Targets (`sorry`s) |
|---|---|---|
| **fac** | `TCSlib/Cryptography/Candidates/Factoring.lean` | `fmult_easy`, `fmult_weakOneWay`, `exists_plantFactorer`, `fmult_prod_strongOneWay`, `polyTimeComputable_samplePairRaw`, `factoringCollection_sampleClose`, `factoringCollection_invProbAt_le`, `factoringCollection_oneWay` (8) |
| **rsa** | `TCSlib/Cryptography/Candidates/RSA.lean` | `polyTimeComputable_rsaGenRaw`, `polyTimeComputable_unitSampleStr`, `rsaSampler_spec`, `rsaCollection_sampleClose`, `rsaCollection_invProbAt_le`, `rsaCollection_oneWay`, `polyTimeComputable_rsaFromFactorRaw`, `factorProb_le_rsaProb`, `rsa_imp_factoring` (9) |
| **rabin** | `TCSlib/Cryptography/Candidates/Rabin.lean` | `oddFactorProb_le`, `blumFactorProb_le`, `blumFactoring_of_factoring`, `polyTimeComputable_oddGenRaw`, `polyTimeComputable_blumGenRaw`, `rabinSampler_spec`, `rabinCollection_sampleClose`, `polyTimeComputable_rabinFactorRaw`, `rabinCollection_invProbAt_le`, `rabinCollection_oneWay`, `polyTimeComputable_blumInvRaw`, `blumInv_spec`, `blumSampler_spec`, `rabinBlumTrapdoor_sampleClose`, `rabinBlumTrapdoor_invProbAt_le`, `rabinBlumTrapdoor_oneWay`, `polyTimeComputable_rabinRootRaw`, `blumFactorProb_le_invProbAt`, `blumFactoring_of_rabinBlum_oneWay` (19) |

Under D1 (A), fac also owns S1 and S2, and rsa owns S3 (10, 10 and 19 targets).

**Cross-unit statements you may cite** (they are `sorry` while their owner works, and the
integration replay closes the chain):
- rsa cites fac's definitions `samplePrimeL`, `factorProb` and `modulusBits`, and, under D1 (A),
  fac's S1 and S2;
- rabin cites rsa's `unitSampleStr`, `sampleUnitL`, `rsaSampleCoins` and
  `polyTimeComputable_unitSampleStr`, and, under D1 (A), rsa's S3. It also cites fac's
  `factorProb` and `modulusBits`;
- rsa and rabin cite `statClose_rejectBlocksL` (`Candidates/Concrete.lean`), which is unit dl-a's
  target in the discrete-log fill.

Each target's docstring carries its proof sketch. **Follow it, or report why it fails.** The
routes below give each sketch's plan, with the corrections the pre-ship probes found.

## Decisions taken in this brief (maintainer to confirm before issue)

- **D1. Shared statements.**
  - The facts below are each needed in two units. A private proof in one unit cannot be cited by
    the other.
  - **(A, recommended)** Add three sorried public statements before issue, each with a sketch.
    They are drafted and elaborated in `preship/probes/Prereqs.lean`, and adding them needs a
    short 03f2 delta round:
    - **S1** `polyTimeComputable_samplePrimeL (hP : PolyTimeComputable primeStr) :
      PolyTimeComputable fun z => samplePrimeL (pairFstD z).length (pairSndD z)`, in
      `Factoring.lean`, owned by fac. Users: `polyTimeComputable_samplePairRaw` and
      `polyTimeComputable_rsaGenRaw`.
    - **S2** `statClose_samplePrimeL_pair (n) (hn : 2 ≤ n)`: the pair of values of
      `samplePrimeL n` on the two halves of `Fin (2 · 2n³)` coins is within
      `2·(1/2)^n + 2n/2^n` of `(z.p, z.q)` for a uniform `z : DistinctPrimes n`. In
      `Factoring.lean`, owned by fac. Users: `factoringCollection_sampleClose` and
      `rsaCollection_invProbAt_le` (ii).
    - **S3** `statClose_sampleUnitL (n N) [NeZero N] (hk : Nat.size N ≤ rsaBlock.eval n)`:
      `(sampleUnitL N (Nat.size N) (rsaBlock.eval n) (rsaTrials.eval n) (List.ofFn s)).getD (1 % N)`
      over `s : Fin (rsaSampleCoins.eval n) → Bool` is within `e^{-n}` of the residue of a
      uniform unit of `Z_N`. In `RSA.lean`, owned by rsa. Users: `rsaCollection_sampleClose`,
      `rsaCollection_invProbAt_le` (i), `rabinCollection_sampleClose`,
      `rabinBlumTrapdoor_sampleClose`, `rabinCollection_invProbAt_le` and
      `rabinBlumTrapdoor_invProbAt_le`.
  - **(B)** No new statements. rsa and rabin reprove these facts as private helpers, and each
    copy is disclosed for human approval (policy §1, Duplication). rsa then also needs
    `samplePrimeL_eq` (P11).
- **D2. Rabin: one unit (recommended), not two.** The 19 targets do split by theorem:
  - **rabin-a:** Theorems 61.7 and 61.8 (⇒), with the conditioning lemmas and both generators.
    That is lines 78–633 and 10 targets: `oddFactorProb_le`, `blumFactorProb_le`,
    `blumFactoring_of_factoring`, `polyTimeComputable_oddGenRaw`, `polyTimeComputable_blumGenRaw`,
    `rabinSampler_spec`, `rabinCollection_sampleClose`, `polyTimeComputable_rabinFactorRaw`,
    `rabinCollection_invProbAt_le`, `rabinCollection_oneWay`.
  - **rabin-b:** Theorem 63.10 and 61.8 (⇐). That is lines 634–997 and the other 9 targets.

  The split is not a helper module that `Rabin.lean` imports, because the Blum half reads
  `Rabin.lean`'s own definitions. A split would need three things:
  - moving lines 634–997 into a new downstream module `Candidates/RabinBlum.lean`, which imports
    `Candidates.Rabin` and keeps its names;
  - a shared statement in `Rabin.lean`: the law of `rabinGenParams P dflt n` is within
    `2e^{-n} + 4n/2^n` of a uniform distinct pair in the class `P`, under a density hypothesis.
    Both halves need it;
  - new rule-10 equations for the definitions the Blum half would then read from outside its
    file: `rabinErr`, `blumFactorProb`, `BlumDensity`, `rabinFactorStep`, `rabinGenOut`,
    `rabinGenParams` and `samplePrimePL`.

  That is a statement-gate delta and seven more prerequisites for a 9/10 split. Keep one unit,
  ordered as below. `Rabin.lean` is 999 lines, so filled it will pass the 1000-line threshold.
  Split it as a landing edit after the fill, when the move is mechanical.
- **D3. Axiom criterion.** Several definitions in these files are built from targets. For example,
  `rsaGen` uses `polyTimeComputable_rsaGenRaw`, and `rabinSampler` uses rsa's
  `polyTimeComputable_unitSampleStr`. A filled target that mentions such a definition prints
  `sorryAx` until that target is filled, possibly by another unit. The criterion is therefore: the
  standard triple, or `sorryAx` reached only through the permitted sorried statements listed for
  your unit (Environment and verification). The integration replay re-prints after all units
  land.

## Rule-10 prerequisites (equations missing at the issue tree)

The sketches read these foreign definitions, which have no published equation. Each lemma below
is stated and proved by `rfl`, `Iff.rfl` or a 2–4 line proof in `preship/probes/Prereqs.lean`.
`preship/seal-control.log` shows that, without them, sealed readings fail. They go beside their
definitions in one maintainer PR before issue. Use them by these names. If one is waived, the
reading is a reported rule-10 exception.

| # | Lemma (file) | Needed by |
|---|---|---|
| P1 | `Collection.sampleClose_iff`, `Collection.invProbAt_eq`, `Collection.index_eq` (`Asymptotic/Collections.lean`) | every `_sampleClose` and `_invProbAt_le` target (all units) |
| P2 | `TrapdoorCollection.oneWay_iff : T.OneWay ↔ T.toCollection.OneWay` (same) | `rabinBlumTrapdoor_oneWay`, `blumFactoring_of_rabinBlum_oneWay` |
| P3 | `statClose_iff` (`Asymptotic/Sampling.lean`) | the `δ n := 1` branch of the four `_sampleClose` targets |
| P4 | `FunFamily.easy_iff` (`Asymptotic/OneWay.lean`) | `fmult_easy` |
| P5 | `NUPPT.advInput_eq` (`Randomized/PPT.lean`); `NUPPT.inParam_eq`, `inArg_eq`, `inAdvice_eq`, `inCoins_eq` (`Randomized/Closure.lean`) | every activation after `NUPPT.runAtL_ofPolyTime(Uniform)`: `fmult_easy`, `exists_plantFactorer`, `rsaSampler_spec`, `rsaCollection_sampleClose`, `rabinSampler_spec`, `blumSampler_spec`, `blumInv_spec`, the Rabin `_sampleClose` targets |
| P6 | `encodeDistinctPrimes_eq`; `DistinctPrimes.p_eq`, `q_eq`, `default_p`, `default_q` (`Candidates/Concrete.lean`) | `polyTimeComputable_samplePairRaw`, `factoringCollection_sampleClose`, `factoringCollection_invProbAt_le`, `polyTimeComputable_rsaGenRaw`, `blumInv_spec`, the Rabin generators |
| P7 | `NumberTheory.chunk_apply : chunk T n r t i = r (finProdFinEquiv (t, i))` (`NumberTheory/Primality.lean`) | `factoringCollection_sampleClose` / S2 |
| P8 | `OneWay.yaoTry_eq`, `OneWay.prodFun_apply` (`OneWayFunctions/Amplification.lean`) | `exists_plantFactorer` |
| P9 | `xgcdStr_pairEncode`, `divModStr_pairEncode` (`Candidates/Arithmetic.lean`) | `polyTimeComputable_rsaGenRaw`, `_unitSampleStr`, `_rsaFromFactorRaw`, `_rabinFactorRaw`, `_blumInvRaw`, `_rabinRootRaw` |
| P10 | `factorProb_eq`, `modulusBits_eq` (`Candidates/Factoring.lean`) | `factorProb_le_rsaProb`, `oddFactorProb_le`, `blumFactorProb_le`, the three Rabin reductions |
| P11 | `samplePrimeL_eq` (`Candidates/Factoring.lean`) | rsa, only under D1 (B) |
| P12 | `unitSampleStr_eq`, `sampleUnitL_eq`, `eval_rsaBlock`, `eval_rsaTrials`, `eval_rsaSampleCoins` (`Candidates/RSA.lean`) | rabin: sampler specs, closeness, `rabinFactorer` |
| P13 | none for `blumSqrt` (no equation): the route of `blumInv_spec` below avoids its body | — |

Already published, and enough: `FunFamily.invProbAt_eq_uprob`, `invProbAt_prod_eq`,
`ofFn_blocks_symm`, `NUPPT.runAt_eq`, `runAtL_ofPolyTime(Uniform)`, `runAtL_eq_output_layout`,
`inverter_eq_some_iff`, `rejectBlocksL_eq`/`_spec`, `padFin_ofFn`, `ofFn_padFin_eq_take`,
`eval_samplePrimeCoins`, `mulStr_pairEncode`, `addStr_pairEncode`, `subStr_pairEncode`,
`leStr_pairEncode`, `modExpStr_pairEncode`, `length_sizeStr`, `primeStr_eq`, the
`natToList`/`listToNat`/`bitsToNat` lemmas of `Arithmetic.lean`, `mem_QR_iff`, `coe_sqTo`,
`crtUnits_fst`/`_snd`, and the `uprob`/`uexp`/`StatClose` lemma families. Each owned file's own
definitions may be unfolded in that file.

## Arithmetic bundle (decision D11)

Never prove an arithmetic operation polynomial-time yourself. Use the field of
`Candidates.ArithmeticFP`, and **report** a missing operation. Fields used:

| Target | Fields |
|---|---|
| `fmult_easy` | `le` (the tests `x = 1`, `y = 1`, both directions), `mul` |
| `exists_plantFactorer` | through `fmult_easy`'s evaluator (`le`, `mul`); the position needs no field (`OneWay.exists_posMachine`) |
| `polyTimeComputable_samplePairRaw` (and S1) | none: `hP` (it is `H.prime` at its use in `factoringSampler`) |
| `polyTimeComputable_rsaGenRaw` | `prime`, `le`, `mul`, `sub`, `size`, `xgcd` |
| `polyTimeComputable_unitSampleStr` | `size`, `le`, `xgcd`; `divMod` (or `le`) for the fallback `1 % N` |
| `polyTimeComputable_rsaFromFactorRaw` | `divMod`, `mul`, `le` (testing `p'q' = N` across widths), `sub`, `xgcd`, `modExp` |
| `polyTimeComputable_oddGenRaw` | `prime`, `divMod` (parity) or `le` (the test `≠ 2`), `mul` |
| `polyTimeComputable_blumGenRaw` | `prime`, `divMod` (mod 4), `mul` |
| `polyTimeComputable_rabinFactorRaw` | `modExp`, `divMod`, `sub`, `add`, `xgcd` (and those of `unitSampleStr`) |
| `polyTimeComputable_blumInvRaw` | `modExp`, `divMod`, `add`, `xgcd`, `mul` |
| `polyTimeComputable_rabinRootRaw` | `divMod`, `mul`, `le`, and those of `blumInvRaw` |

**Gaps: none found.** Converting a numeral to unary is not a bundle operation: the library has
it (`OneWay.exists_unaryOf`, `OneWay.exists_posMachine`). Padding and truncating to a width are
machine-layer operations: `polyTimeComputable_padStr`,
`Complexity.polyTimeComputable_takePrefixByLength`/`_dropPrefixByLength`,
`polyTimeComputable_unaryPoly` and `polyTimeComputable_blockMap`.

## Targets, in order, with routes

Order within each unit: samplers and closeness first, then polynomial time, then the
reductions and headlines. Every proof that mentions a generator or sampler of its own file
prints `sorryAx` until that file's polynomial-time targets are filled (D3).

### fac (`Factoring.lean`)

1. **S2** `statClose_samplePrimeL_pair` (D1 (A)). Use `samplePrimeL`'s body (own file) with
   `padFin_ofFn` and `chunk_apply` (P7). `chunk` pushes uniform coins to uniform blocks. Then
   apply `NumberTheory.statClose_samplePrime` (fallback `natToBits n 2`, `bitsToNat_natToBits`,
   `Nat.prime_two`) to each half, with `uprob_samplePrime_none_le_two_pow`'s bound `(1/2)^n`.
   Combine with `StatClose.prod`, then `StatClose.trans`, and finally drop the diagonal by
   `uprob_diag` and `one_div_card_primes_le`.
2. `factoringCollection_sampleClose`. Take `δ n := 1` for `n < 2` (P3) and
   `2(1/2)^n + 2n/2^n` otherwise. Rewrite with `Collection.sampleClose_iff` (P1). Then use
   `factoringSampler_runAt` and `factoringCollection_index`, map S2 through `samplePairOut` and
   `decodeDistinctPrimes` (`samplePairOut_eq_encode`, `decodeDistinctPrimes_encode`,
   `encodeDistinctPrimes_eq`, `DistinctPrimes.p_eq`), and apply `StatClose.map`. Negligibility
   uses `negligible_two_pow_neg`, `Negligible.mul_pow` and `Negligible.add`.
3. **S1** `polyTimeComputable_samplePrimeL` (D1 (A)). Use `NumberTheory.exists_samplePrime_nuppt
   hP` (via `primeStr_eq`) as a black box. Its machine computes
   `((samplePrime …).map List.ofFn).getD []` on `List.ofFn r`. So pad the coins to `2n³` bits
   (`polyTimeComputable_padStr`, `ofFn_padFin_eq_padStr`), run it through
   `NUPPT.polyTimeComputable_output`/`_layout`, and replace `[]` by the fallback numeral
   `natToList n 2`, a constant block of unary length (`polyTimeComputable_lenEq`, `_ite`). Do not
   re-derive the `iterateFind` loop.
4. `polyTimeComputable_samplePairRaw` (sketch as repaired, F08). Cut the coins at `1^{2n³}`
   (`polyTimeComputable_pairTakePoly`/`_pairDropPoly samplePrimeCoins`). Get each half from S1.
   The prime tests are `hP`, and the inequality test is `polyTimeComputable_pairEq` on the two
   `n`-bit words. Discharge the range checks from the widths (`listToNat_lt_two_pow`). Re-encode
   with `max n 2` bits by leading zeros. The default pair is `encodeDistinctPrimes_eq` with
   `default_p`/`default_q` (P6), so its numerals are `natToList (max n 2) 2`/`3`. PolyExprs have
   no `max`, so branch on `n < 2` (`polyTimeComputable_lenLe`).
5. `fmult_easy`. Use `FunFamily.easy_iff` (P4) and `NUPPT.advInput_eq` (P5), then follow the
   sketch: `pairTakePoly`/`pairDropPoly var`, two `H.le` tests per block, `polyTimeComputable_ite`
   and `H.mul` (`mulStr_natToList`).
6. `exists_plantFactorer`. **Route correction:**
   - **Position.** Sample the position with `OneWay.exists_posMachine`, which turns
     `n·kk` coin bits into `1^i` with `i = (rejectionSample M kk n …).getD 0`, for
     `kk = Nat.size M` (`2^kk ≤ 2M`, `Nat.lt_size`). Do not compare each trial with an advice
     numeral by `H.le`. `Nat.size M` is not a `PolyExpr`, so keep the sketch's `Bp`-bit blocks
     and take the first `kk` bits of each (`polyTimeComputable_blockMap`).
   - **Offset.** Get the unary offset `1^{i·2n}` from `computesFunInTime_unaryMul` as in the
     sketch.
   - **Evaluation.** Evaluate the fresh blocks with `OneWay.exists_prodEval` on `fmult_easy`'s
     evaluator.
   - **Model.** The whole machine follows `OneWay.exists_yaoReduction`
     (`Asymptotic/OneWayYao.lean`: `YaoMachine.off`, `planted`, `ofFn_blocksE_symm_update`).
   - **Functional identity.** It uses `OneWay.yaoTry_eq` and `prodFun_apply` (P8) and the P5
     equations.
   - **Probability.** As sketched: `statClose_rejectionSample` with
     `uprob_rejectionSample_none_le_half_pow`, then `StatClose.prod`, `comp_equiv_left` and
     `abs_uprob_sub_le_prod`.
7. `factoringCollection_invProbAt_le`. Follow the sketch with `Collection.invProbAt_eq` (P1),
   `OneWay.uexp_const`, `factoringCollection_index`, `encodeDistinctPrimes_of_decode` with
   `encodeDistinctPrimes_eq` (P6) for the first component, `natToList_injOn`,
   `fmultNat_eq_mul_prime` and `collectionFactorer_runAt`.
8. `factoringCollection_oneWay`, then `fmult_weakOneWay`, then `fmult_prod_strongOneWay`, as
   sketched.

### rsa (`RSA.lean`)

1. `rsaSampler_spec`. Follow the sketch, reading the activation with
   `NUPPT.runAtL_ofPolyTimeUniform` and the P5 equations (there is no `rsaSampler_runAt`; a
   private one is fine).
2. **S3** `statClose_sampleUnitL` (D1 (A)). Apply `statClose_rejectBlocksL` (default `1 % N`,
   `k = Nat.size N ≤ B(n)`) and transport `{v < 2^k | v < N ∧ gcd = 1} ≃ (ZMod N)ˣ`
   (`ZMod.unitOfCoprime`, `ZMod.val_lt`). The acceptance rate is
   `Φ(N)/2^k ≥ 1/(2k) ≥ 1/(4n+8)` (`Nat.lt_size_self`, `Nat.size_le`,
   `NumberTheory.le_totient_mul_log_succ`). Then `one_sub_one_div_pow_le_exp_neg`.
3. `rsaCollection_sampleClose`. Take `δ n := 1` for `n < 2` (P3) and `e^{-n}` otherwise. Use
   `rsaCollection_index`, `rsaValid_indexOf`, S3 at `N = pq` and `StatClose.map` through
   `rsaDec`.
4. `polyTimeComputable_unitSampleStr`. **Correction:** `xgcdStr` returns the gcd as a numeral of
   the modulus width, so test `gcd = 1` against that width's numeral of `1`, or by two `H.le`
   tests, not by `pairEq` with `[true]`. Read the trial bits with `pairTakePoly var` on
   `⟨1^k, block⟩`, using `H.size`. Pad the output to the width of `w` with leading zeros: a zero
   block of length `|w| − k` (`Complexity.polyTimeComputable_dropPrefixByLength` on unary
   lengths, mapped to zeros by `polyTimeComputable_blockMap`) prepended. `padStr` pads on the
   right, so it is for coins only. Use `xgcdStr_pairEncode` (P9) for the `convert`.
5. `polyTimeComputable_rsaGenRaw`. Follow the sketch, with the primes from S1. `1^{max n 2}` is
   not a `PolyExpr`, so branch on `n < 2`. `xgcdStr_pairEncode` gives `d`. The fallback pair is
   P6.
6. `polyTimeComputable_rsaFromFactorRaw`. Follow the sketch. Compare `p'q'` with `N` by `H.le`
   in both directions, because the widths differ. Use `divModStr_pairEncode` and
   `xgcdStr_pairEncode` (P9).
7. `rsaCollection_invProbAt_le` (sketch as repaired, F05: a conditional expectation over `z`, no
   single uniform product). **Correction:** `uexp_prod` is `HardcoreBit.uexp_prod`. Step (i) is S3
   with the modulus `Φ(N)`, where `1 % Φ = 1` because `Φ ≥ 2` (`DistinctPrimes.one_lt_totient`). Step (ii)
   is S2. Also use `Collection.invProbAt_eq` (P1).
8. `factorProb_le_rsaProb`. Use `factorProb_eq`, `modulusBits_eq` (P10),
   `rsaFromFactorer_runAt`, `rsaFromFactorStep_correct`, `uprob_prod`, `uprob_comp_equiv` and
   `uprob_mono`.
9. `rsaCollection_oneWay`, then `rsa_imp_factoring`, as sketched.

### rabin (`Rabin.lean`)

1. `rabinSampler_spec`, `blumSampler_spec`. Follow the sketches with the P5 and P12 equations.
2. `blumInv_spec`. **Route:** do not read `blumSqrt`'s body (P13). The CRT value `s` of
   `blumInvNat p q y.val` is a unit with `s mod p = y^{(p+1)/4}` and `s mod q = y^{(q+1)/4}`
   (`ZMod.coe_mul_inv_eq_one`, `crtUnits_fst`/`_snd`). So `s ∈ QR_N`
   (`pow_div_four_succ_mem_QR`, `mem_QR_mul_iff`) and `s² = y` (`sq_pow_div_four_succ`,
   `sq_crtUnits_symm`). Then `(blumPermAt i).symm y = s` follows from the injectivity of
   `Equiv.ofBijective`, or from `eq_blumSqrt_of_sq_eq`. The trapdoor is read by
   `encodeDistinctPrimes_eq` and `DistinctPrimes.p_eq` (P6).
3. `rabinCollection_sampleClose`, `rabinBlumTrapdoor_sampleClose`. Use S3 at `N = pq` (`δ n := 1`
   for `n < 3`, P3), then `StatClose.map` through `rabinDec`. For the Blum sampler, add
   `pushesUniform_sqTo`, `statClose_of_pushesUniform`, `sq_mem_QR` and `StatClose.trans`. Do not
   copy `rsaCollection_sampleClose`'s proof.
4. `oddFactorProb_le`, `blumFactorProb_le`. **Correction:** `uprob_eq_one_div_card` is
   `OneWay.uprob_eq_one_div_card`. Also use `factorProb_eq` (P10).
5. `polyTimeComputable_oddGenRaw`, `polyTimeComputable_blumGenRaw`.
   - The acceptance test must equal `decide (v.Prime ∧ P v)` on every word. For `P = (· ≠ 2)`,
     "prime and odd" is that predicate. Test parity with `H.divMod` by `[true, false]`, and the
     residue mod 4 likewise.
   - Each restricted prime loop is `Complexity.polyTimeComputable_iterateFind` over
     `rejectBlocksL` (`rejectBlocksL_eq`).
   - Write one private generic helper for both generators, under your prefix.
6. `polyTimeComputable_rabinFactorRaw`. **Correction:** `natToList n g` of the gcd, which has
   the modulus width, is its **low** `n` bits, so drop the first `|N| − n` bits
   (`_dropPrefixByLength`), not `pairTakePoly var`. `(x − z) mod N` is computed as the sketch
   says. Use P9.
7. `polyTimeComputable_blumInvRaw`, then `polyTimeComputable_rabinRootRaw`. Follow the sketches,
   with P9.
8. `rabinCollection_invProbAt_le`, `rabinBlumTrapdoor_invProbAt_le`,
   `blumFactorProb_le_invProbAt`.
   - **Correction:** `uexp_prod` is `HardcoreBit.uexp_prod`.
   - The unit sampler of `rabinFactorer` is S3. Each restricted prime sampler is
     `statClose_rejectBlocksL` with the class density: `two_pow_le_two_mul_card_primes` for odd
     primes, `hD` for Blum primes.
   - Prove the pair law once, as a private helper generic in `P`, and use it in all three.
   - Then `rabin_symmetry`, `gcd_sub_eq_prime_of_sq_eq_sq`, `rabinFactorer_runAt` and
     `rabinBlumInverter_runAt`, as sketched (P1, P10).
9. `blumFactoring_of_factoring`, `rabinCollection_oneWay`, `rabinBlumTrapdoor_oneWay` (P2),
   `blumFactoring_of_rabinBlum_oneWay` (P2), as sketched.

Seven Rabin targets have a short sketch without a "Proof sketch" paragraph (the AB lint's FAIL in
`preship/lint-base.log`): lines 145, 347, 532, 805, 892, 927 and 951. When you fill one, expand
its docstring into a sketch of the proof you wrote. Do not change its statement.

## Templates (cite; do not copy)

- **Machines:**
  - `NumberTheory.exists_samplePrime_nuppt` (`NumberTheory/Primality.lean`) is the proved
    `SamplePrime` machine and the model for every restricted loop;
  - `OneWay.exists_yaoReduction`, `exists_posMachine`, `exists_unaryOf` and `exists_prodEval`
    (`Asymptotic/OneWayYao.lean`, `OneWayLemmas.lean`);
  - `FunFamily.Easy.prod` (`Asymptotic/OneWay.lean`);
  - `polyTimeComputable_prgPadFun` (`Asymptotic/Encryption.lean`) and
    `polyTimeComputable_preFun`/`postFun`/`blockMapFun` (`Asymptotic/MultiMessageLemmas.lean`).
    These two files are outside your closure: read them as models, do not import them;
  - the closure calculus (`Randomized/Closure.lean`, `ClassNP/PolyTimePairing.lean`,
    `Randomized/Primitives.lean`, `Randomized/Repetition.lean`).
- **Samplers:**
  - `NumberTheory.statClose_samplePrime` and `statClose_firstHit`, `statClose_rejectionSample`
    (`Asymptotic/Sampling.lean`);
  - `statClose_permFromCoins` (`Asymptotic/Permutations.lean`, outside your closure: a model
    to read), a full worked instance.
- **Concrete steps** (`Candidates/Concrete.lean`, all proved):
  - `uprob_and_eq_mul_subtype`, `one_sub_div_le_uprob_subtype`, `uprob_le_uprob_subtype_add`,
    `uprob_subtype_prod_eq` and `uprob_diag`;
  - `invProb_prodFun_le_plant` and `claim_36_2_half_pow`;
  - `one_div_le_uprob_prime_pair_bits`, `primesPairEquiv` and `one_div_card_primes_le`.
- **Number theory** (`NumberTheory/{Units, QuadraticResidues}.lean`, all proved):
  - `rsa_pow_pow`, `rsa_pow_bijective` and `le_totient_mul_log_succ`;
  - `crtUnits`, `blumSqrt_*`, `eq_blumSqrt_of_sq_eq`, `sqTo_bijective_of_blum`,
    `pushesUniform_sqTo` and `gcd_sub_eq_prime_of_sq_eq_sq`.
- **Collections:** `FunFamily.StrongOneWay.toCollection_oneWay`
  (`Asymptotic/Collections.lean`), a one-wayness proof by reduction.

**Imports:** none is needed and none is authorized. Every name this brief cites for your unit is
in your owned module's closure (`preship/import-probe-*.log`), except the three template files
marked above. `TCSlib/Cryptography/RSA.lean` is an unrelated,
unimported textbook file: do not import it.

## Ground rules (binding)

1. **Statement freeze.** Every definition and target statement stays byte-identical. Only the
   bodies of your unit's targets change, plus new `private` helpers under your unit's prefix
   (`fac_`, `rsa_`, `rabin_`) and the docstring expansions above.
2. **Rule 10.** Read other files' definitions only through published equations: those listed
   above, and P1–P12 once they land. Never pass a foreign TCSlib definition to `unfold`, `simp`
   or `rw`. Core and Mathlib definitions may reduce only in `rfl`, `decide` or `show`. Self-check
   with a seal: compile a sealed copy of the owned file with `attribute [local irreducible]` on
   every foreign definition you read (and `attribute [-simp]` on the `@[simp]` ones), plus
   controls that close unsealed and fail sealed.
3. **D11.** Use the bundle's fields only. Report a missing operation; do not prove one.
4. **Reuse, not copy.** Cite another unit's statements, never its proofs. If a lemma you need is
   private elsewhere, request it in `REPORT.md` and prove a generic version under your prefix.
   Disclose every copy (policy §1, Duplication). Build no private host: cite the registered
   loops (`iterateFind`, `iterate`, `iterateEmit`, `blockMap`).
5. **Escalation.** A target that looks false or unprovable as stated is reported with the
   missing hypothesis or a counterexample, never patched. Gate 03f2 screened all 36, so a report
   is a finding against that gate.
6. **Budget.** Complete targets beat partial ones. Keep the order above.
7. **No split.** Do not split or move files. RSA and Rabin may exceed 1000 lines when filled.
   Record the size WARN in `REPORT.md`.

## Environment and verification

- **Environment:** the environment addendum v1 (`fills/fill-environment-addendum.md`), attached at
  dispatch. **Never `lake build`.** One Lean process at a time. Check modules with
  `scripts/lean_check_tree.sh <module path without .lean>`.
- **Inputs** (`inputs/<unit>/`, generated by `fillinputs.py` at
  `5f2771631fe853dae9c2aa44791ae5b0e09c95eb`, identical for the three units):
  - `order.txt` lists 94 modules. Your module's downstream closure includes the other two owned
    files and the facade `TCSlib/Cryptography/Candidates`;
  - `roots.txt` lists 75 Mathlib roots. Fetch the cache for these only;
  - `base-sorries.txt` lists 75 sorried declarations in 15 modules. Your file's entry is exactly
    your targets (8, 9 or 19).
- **Final checks:**
  - **The owned file:** zero errors, and no `sorry` warning for a filled target.
  - **Sweep:** the owned file, then every later module of `order.txt` that imports it. At your
    head the other units' files are unchanged, so this checks that your file still compiles
    under them.
  - **Axiom prints for every filled target:** the standard triple, or `sorryAx` reached only
    through the permitted statements:
    - fac: its own unfilled targets only;
    - rsa: `statClose_rejectBlocksL`, plus S1 and S2 under D1 (A);
    - rabin: `statClose_rejectBlocksL`, rsa's `polyTimeComputable_unitSampleStr` (through
      `rabinSampler`, `blumSampler` and `rabinFactorer`), plus S3 under D1 (A).

    In `REPORT.md`, name the permitted statement behind each `sorryAx` print.
  - **The rule-10 seal** with its controls.
  - **Lint:** `python3 -I scripts/style_lint.py <owned file>` reports 0 findings (it reports 0 at
    the issue tree), and `scripts/campaign_style_lint.py --check8b` shows no new public `def`.

## REPORT.md checklist

- [ ] The base hash (`@ANCESTOR@`, full, from `git rev-parse`), and the preflight figures.
- [ ] Each target: filled, partial (with its frontier), or escalated (with the reason).
- [ ] Every new `private`, with its role. Every disclosed copy (Duplication), and every requested
      shared lemma.
- [ ] Rule 10: the sealed definitions, the controls, and any exception (a waived P-lemma).
- [ ] D11: the fields used, and any missing operation.
- [ ] The final sweep tail, the axiom prints (with the permitted statement behind each
      `sorryAx`) and the lint lines.
- [ ] The diff touches only the owned file. Statements are byte-identical (a `declfreeze`-style
      comparison against `@ANCESTOR@`).
- [ ] The delivery folder `inbox/fills/<unit>/` as pushed, and its last checkpoint message.

## Pre-ship record (2026-11-06, at `5f2771631fe853dae9c2aa44791ae5b0e09c95eb`)

Checks run in a detached worktree of the issue tree, with the full olean tree for it, using
Lean 4.25.0 through `scripts/lean_check_tree.sh`, one process at a time. Probe files lived in
`Probe/` only, and no TCSlib source was edited. Logs and probe sources are under `preship/`.

| Check | Result | Log |
|---|---|---|
| Inputs per unit (`fillinputs.py`) | order 94, roots 75, base 75 sorried in 15 modules; Factoring 8, RSA 9, Rabin 19, each equal to the unit's targets | `inputs/{fac,rsa,rabin}/` |
| Import probe | fac 215, rsa 201, rabin 241 `#check`s. Absent as written and corrected: `uexp_prod` → `HardcoreBit.uexp_prod`, `uprob_eq_one_div_card` → `OneWay.uprob_eq_one_div_card`. No present-but-not-imported name. The QR and Euler names are in rabin's closure only, by design | `preship/import-probe-{fac,rsa,rabin}.log` |
| Duplication probe (`exact?` at 400000 heartbeats per target, on a copy of the owned file) | 0 hits out of 36 (11 timeouts); grep of TCSlib and Mathlib: no equivalent | `preship/dup-probe-{fac,rsa,rabin}.log` |
| Axioms of cited lemmas | 319 prints; no non-standard axiom. Outside the owned files, only `statClose_rejectBlocksL` uses `sorryAx` | `preship/axioms-cited.log` |
| Rule-10 prerequisites and S1–S3 | 29 equations proved by `rfl`-level proofs, and S1–S3 elaborate; rc 0 | `preship/prereqs.log`, `preship/probes/Prereqs.lean` |
| Seal control | 3 readings close unsealed and fail sealed | `preship/seal-control.log` |
| Remaining cited names | 13 `#check`s, 0 errors | `preship/brief-names.log` |
| Lint at the issue tree | `style_lint.py`: 0 findings in 3 files; AB lint: check-8 WARNs and 7 short Rabin sketches | `preship/lint-base.log` |

Not verified here: S1–S3 are only stated, not proved; their truth rests on the routes above.
Running the D1 (A) delta through gate 03f2, the P1–P12 PR, the review of this brief and the
choice of `@ANCESTOR@` remain to be done.
