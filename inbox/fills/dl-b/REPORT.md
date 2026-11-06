# Fill dl-b: REPORT (final)

Unit **dl-b** of `briefs/pass-shelat-ch5-8/fills/dl-candidates/brief-issued.md` (the discrete-log
candidates). Owned file: `TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean`.

- **Base:** `16a7d02d69cae1a700c131e3cc3dd918a7b3d6e1` (the issue commit, head of #210). Local branch
  `fill/dl-b`, created from the base, never rebased, never pushed.
- **Head of `fill/dl-b`:** `a5c54b0ed4e9aa388bd4497303233d3e044ce419` (8 commits; `patches/` is
  `git format-patch 16a7d02d..fill/dl-b`).
- **Environment.** Ran as an **internal worker** under the maintainer's environment note
  (`issue/internal-env.md`, which replaces the addendum's Part 1): no preflight floors, no cache
  fetch, no bootstrap. `.lake/packages` is the linked Mathlib tree; the olean tree
  `fill-dl-b-oleans` was a full build of the issue commit. At start: `nproc` = 4; 15 GiB memory,
  about 14 GiB available (`evidence/logs/start-resources.log`). Never `lake build`, never
  `lake exe cache get`; one Lean process at a time; every module check through
  `scripts/lean_check_tree.sh` (`evidence/logs/module-checks.log`, each check with its start time
  and duration: 17 s with the six concrete targets, 32–38 s with the headline).
- **Checkpoints:** `fill dl-b: checkpoint 1` (six concrete targets), `checkpoint 2` (all seven),
  then this final delivery.

## 1. Targets

All seven are **filled**. None partial, none blocked (E-API), none escalated.

| # | Target | Status | Route |
|---|---|---|---|
| 1 | `dlBits_pow` | filled | the sketch: induction on `k` generalizing `e`; `dlb_dlRoot_pow` (the root of `g^e` is `±g^{⌊e/2⌋}`: `pow_mem_QR_iff`, `sq_pow_div_four_succ`, `sq_eq_pow_two_mul_iff`), `dlb_keep` (the perfect oracle keeps `g^{⌊e/2⌋}`: `dlog_expo`, `neg_pow_eq`), parity of `e` for the recorded bit |
| 2 | `uprob_trial_ge` | filled | the sketch: `r ↦ e + r` (`uprob_comp_equiv`, `Equiv.addLeft`) turns the correct-prediction event into `predProb`; the disagreement set lies in `[h−d, h) ∪ [m−d, m)` (`dlb_window`, `m = 2h`, `e ∈ {d, h+d}`), at most `2s` values (`dlb_uprob_val_le`, `Finset.card_le_card_of_injOn`), probability `≤ ε/2`; union bound `uprob_or_le`. `ε ≤ 1/2` (`dlb_eps_le`) and `s ≥ 1` give `p − 1 ≥ 8`, so `p` is odd; an empty coin type makes `hA` infeasible |
| 3 | `uprob_majOracle_ne_le` | filled | the sketch: the votes are functions of the coordinates (`HardcoreBit.PairwiseUniform.pairwiseIndep`, `HardcoreBit.pairwiseUniform_eval`), each correct with probability `≥ 1/2 + ε/2` (`uprob_trial_ge` through `HardcoreBit.pushesUniform_eval`); `HardcoreBit.uprob_majority_fails_le` with `δ = ε/2`, and `HardcoreBit.two_mul_card_le_of_majority_ne` |
| 4 | `invProb_shiftInverter_ge` | filled | the sketch: `uprob_prod` over `x`; on each section the event "`t = ⌊x/s⌋` and `B₀` succeeds" (`dlb_shiftInverter_eq`: the output is then `x`) has probability `(1/T)·Pr[B₀ succeeds]` (`HardcoreBit.uprob_prod_and`, `OneWay.uprob_eq_one_div_card`); `T = 0` gives `0`. The hypothesis `hg` of the frozen statement is unused (the bound holds for every `g`), which leaves one `unused variable` linter warning |
| 5 | `invProb_dlInverter_ge` | filled | the gate review's perfect-path union bound: `invProb_shiftInverter_ge` with `δ = k/(ε²ℓ)`; `dlb_dlQueries_eq_perf` (an oracle correct at every perfect-path query follows the perfect path) with `dlLoop_eq_dlBits` and `dlBits_pow`; `dlb_perf_window` (every perfect-path query is `g^a` with `a` in the windows, since `ε ≤ 1/2` gives `s ≤ (p−1)/8`); `uprob_exists_le` over the `k` rounds, each round by `uprob_majOracle_ne_le` through `HardcoreBit.pushesUniform_eval` |
| 6 | `polyTimeComputable_halfStr` | filled | the sketch: `halfStr z = [¬(⌊p/2⌋ ≤ x)]` (`dlb_halfStr_eq`: `divModStr_pairEncode`, `leStr_pairEncode`), from `H.divMod`, `H.le`, `polyTimeComputable_headD`, `polyTimeComputable_not`. The constant `2` is the numeral `natToList 2 2` (a literal list would need `natToList` read by `decide`) |
| 7 | `fullDLCollection_hardCore` | filled | §1.1: the sketch's route with six engineering departures, each forced by a missing interface or chosen to avoid duplicating dl-a's private sampler loop |

### 1.1 The headline: what the proof does, and where it departs from the frozen sketch

**Structure** (in the owned file, all `private`, prefix `dlb_`, under the section header "The proof
of Lemma 84.1"):
1. **The machine `B`** (`dlb_B` = `NUPPT.ofPolyTime` of the string function `dlb_raw`, polynomial
   time by `dlb_raw_poly`). On `⟨⟨⟨1^n, ⟨i, y⟩⟩, ⟨A.advice n, ⟨⟦8n^c⟧_n, 1^κ⟩⟩⟩, coins⟩` it reads
   `p, g` from `i`, computes `p − 1` (`H.sub`), `s = ⌊(p−1)/(8n^c)⌋` (`H.divMod`), the guess `t`
   (the first `κ` coins), `ts` (`H.mul`) and `y₀ = y·(g^{ts})⁻¹ mod p` (`H.modExp`, `H.xgcd`,
   `H.mul`, `H.divMod`); then `n` rounds of Algorithm 84.2 (`dlb_outer`): Euler's test
   `y^{(p−1)/2} mod p = 1` (`H.modExp`, two `H.le`), `base = y` or `y·g⁻¹ mod p`, the root
   `base^{p/4+1} mod p` (`H.divMod`, `H.add`, `H.modExp`), the trial loop `dlb_inner` (`ℓ` trials: the
   collection's domain sampler on the index for `r`, `z = root·g^r mod p`, `A.output` on the layout
   `⟨⟨⟨1^n, ⟨i, z⟩⟩, A.advice n⟩, ρ⟩`, the vote `[A = 1] = halfStr ⟨i, r⟩` by
   `polyTimeComputable_pairEq` and `polyTimeComputable_halfStr`), the majority
   (`polyTimeComputable_majority`), `root` or `p − root` (`H.sub`), the parity bit prepended;
   finally `(bits + ts) mod (p−1)` (`H.add`, `H.divMod`). Both loops are guarded state loops on the
   public host `Complexity.StateLoop.gstep` with `Complexity.polyTimeComputable_iterate`, driven by
   unary counters `1^n` and `1^ℓ` (fixed lengths; the machine never iterates `T` times).
2. **The machine computes `dlInverter`** (`dlb_raw_sem`): at a well-formed full-group index whose
   sampler blocks all decode, the output is the `n`-bit numeral of
   `shiftInverter g (dlLoop g (majOracle g A_i ℓ) n) s 2^κ y (t, c)`, `c` the decoded rounds. Layers:
   the loops on strings (`dlb_inner_eq`, `dlb_oStep_shape`, `dlb_outer_eq`, through
   `StateLoop.gstep_iterate_eq` with genuine-orbit length bounds); one round on numerals of units
   (`dlb_qrF_eq` by `ZMod.euler_criterion_units`, `dlb_rootF_eq`, `dlb_vote_eq` through the field
   `encD_decD`, `fullDLCollection_encD`, `NUPPT.distinguisherL_eq`, `NUPPT.Uniform.runAt_eq`;
   `dlb_oStep_round`); and the induction `dlb_loop_sem` against `dlLoop_succ`.
3. **One good instance** (`dlb_instance`): `B`'s discrete-log success at the index is at least
   `invProb (expo g) (dlInverter g A_i s 2^κ ℓ n) − n·ℓ·δ` (`invProb_dlInverter_ge`; the predictor's
   success transported by `dlb_pred_eq` along `fullDLCollection_domEquiv` and
   `ZMod.ringEquivCongr`; `B`'s coins split by the bijection `dlb_split` (`List.ofFn_add`,
   `List.ofFn_mul`); the `n·ℓ` sampled exponents close by `dlb_statClose_pi`, `StatClose.prod` and
   `StatClose.abs_uprob_sub_le_prod`; the ideal experiment pushed onto `dlInverter`'s coins by
   `dlb_guess_pushesUniform` and `HardcoreBit.PushesUniform.prodMap`; `expo_injective`).
4. **The reduction** (`dlb_reduction`) and the headline: `Collection.hardCore_iff`. The easy part is
   `halfStr` with `polyTimeComputable_halfStr`, `halfStr_spec`, `fullDLCollection_encD`. For the hard
   part, `ε(n) = max(succ(n) − 1/2, 0)`; non-negligibility (`not_negligible_iff`) gives `c` with
   advantage `n^{−c}` infinitely often; the average moves to `G.gen`'s coins
   (`fullDLCollection_index`, `fullDLCollection_coinsEquiv_uexp`); `good_instances` with `2ε'`,
   `ε' = 1/(2n^c)`; the short-prime coins are removed (`ExpGroupGen.fullLengthExcept_iff`, `hbig`'s
   `δ(n) ≤ ε'/2`); `HardcoreBit.uprob_mul_le_uexp` over the good set gives
   `G.dlProb B n ≥ 3/(1024 n^{2c})` at every large such `n`, against `hDL B`
   (`fullDLAssumption_iff`, `negligible_iff`). `hbig` is used (ruling R-03f1-1 (A)).

**Departures from the frozen sketch** (the docstring is frozen; a sketch refresh is suggested at the
next docstring window):
1. **`T = 2^κ`, `κ = Nat.size (16 n^c)`, instead of `T = ⌈(p−1)/s⌉`.** Then `16n^c < T ≤ 32n^c`,
   `Ts ≥ p − 1` still holds (`dlb_window_params`), and the guess is the first `κ` coins, exactly
   uniform (`dlb_guess_pushesUniform`): no sampler for `t`, no ceiling. The ideal success is
   `≥ (3/4)/T ≥ 3/(128 n^c)` (`K(n) = 32 n^c`).
2. **The exponents `r_{j,i}` come from the collection's own domain sampler**
   `(fullDLCollection H G).sample`, called through its output function (field `sample_uniform`,
   `NUPPT.Uniform.runAt_eq`), with closeness `SampleClose δ_S` from
   `(fullDLCollection_oneWay H G hDL).sampleClose` (`δ_S` negligible), not `sampleBelowL` with
   `statClose_sampleBelowL`. Reason: the sketch's route needs the rejection sampler as a machine on
   `n·n` coins, and at the base no published lemma states `expSampleRaw`'s equation or
   `expSampler`'s coin count (§4); the alternative was a third private copy of the block-rejection
   loop (dl-a's private `dla_ss*` family). The coins are `n + n·ℓ·(S.coins + A.coins)`, `S` the
   domain sampler, and the sampling loss is `n·ℓ·δ_S(n)` (negligible) instead of
   `(1 + 16n^{2c+2})·2^{−n}`.
3. **`ℓ = 16 n^{2c+1} + 1` (odd)**, so `k/(ε²ℓ) < 1/4`. Reason: `HardcoreBit.majority` has no
   published equation, and the published `two_mul_card_le_of_majority_ne` determines it exactly only
   when ties are impossible (`dlb_majority_eq_of_odd`). See §4.
4. **No guard** ("output `0^n` unless `1 ≤ s` and `T < 2^n`"): the loops have fixed lengths from the
   unary counters, and the analysis lower-bounds the success by `0` off the good instances.
5. **Advice** `⟨A.advice n, ⟨⟦8n^c⟧_n, 1^κ⟩⟩`: the sketch's numeral of `8n^c` plus the unary `κ`.
6. **Constant:** `G.dlProb B n ≥ 3/(512 n^{2c}) − n·ℓ·δ_S(n) ≥ 3/(1024 n^{2c})` for large `n`.

The mathematics (good-set mass `ε'/2`, window `s`, `k = n`, `k/(ε²ℓ) ≤ 1/4`, the perfect-path
analysis of the concrete core) is the sketch's.

## 2. New private declarations (all `private`, prefix `dlb_`)

210 private declarations: 13 for the concrete targets, 197 for the headline. By section of the
owned file:

| Section | Declarations | Role |
|---|---|---|
| Algorithm 84.2 | `dlb_dlRoot_pow`, `dlb_halfOracle_pow_eq`, `dlb_halfOracle_pow`, `dlb_keep` | the root of `g^e`; the perfect oracle on powers; the kept root (`dlBits_pow`, reused by `invProb_dlInverter_ge`) |
| Majority test, range reduction | `dlb_uprob_val_le`, `dlb_window`, `dlb_pow_mul_pow_val`, `dlb_eps_le`, `dlb_shiftInverter_eq`, `dlb_perf`, `dlb_dlQueries_eq_perf`, `dlb_perf_window` | counting through residues; the windows in `ℕ`; `g^e·g^r = expo g (e + r)`; `ε ≤ 1/2`; the shift on a correct guess; the perfect path, the agreement lemma, its windows |
| Asymptotic form | `dlb_halfStr_eq` | `halfStr` as bundle operations |
| Numeral arithmetic | `dlb_ptc`; `dlb_one`, `dlb_two`, `dlb_four` and their values; `dlb_mulMod`, `dlb_powMod`, `dlb_invMod`, `dlb_quot`, `dlb_rem` with `_poly` and `_natToList` | modular operations from the bundle fields, their polynomial time, their values on numerals |
| Loop and list helpers | `dlb_take_poly`, `dlb_drop_poly`, `dlb_eq_poly`, `dlb_ite_poly`, `dlb_stateIterate_poly` | combinators in applied form; the guarded state iteration |
| Fixed data | `dlb_fix`, its projections `dlb_fu` … `dlb_fg` with `_poly`, `dlb_fix_proj` | the data the loops retain |
| One trial | `dlb_wS`, `dlb_zz`, `dlb_aBit`, `dlb_vote`, `dlb_vote_poly` | the vote of one trial |
| Trial loop | `dlb_iF` … `dlb_iRest`, `dlb_iStep`, `dlb_iStart`, `dlb_iB`, `dlb_inner` with `_poly` | the `ℓ`-trial loop (instance data of `StateLoop.gstep`) |
| Round loop | `dlb_oF` … `dlb_oNext`, `dlb_oStep`, `dlb_oB'`, `dlb_outer` with `_poly` | the `n`-round loop (instance data of `StateLoop.gstep`) |
| Raw function | `dlb_zi` … `dlb_zacc`, `dlb_raw` with `_poly` | the inverter's string function and its polynomial time |
| Closed forms | `dlb_blocksL`, `dlb_blocksL_cons`, `dlb_orbit_eq`, `dlb_iStep_cons`, `_nil`, `_iterate`, `_iterate_nil`, `dlb_length_blocksL_drop`, `dlb_length_fuL_le`, `dlb_inner_eq`; `dlb_roundsList`, `dlb_roundsL`, `dlb_roundsList_cons`, `dlb_qrF`, `dlb_rootF`, `dlb_oQr_eq`, `dlb_oRoot_eq`, `dlb_oStep_cons`, `_nil`, `_iterate_nil`, `_shape`, `dlb_outer_eq` | the loops on strings |
| Numeral semantics | `dlb_val_lt`, `dlb_qrF_eq`, `dlb_rootF_eq`; `dlb_foldl_bits`, `dlb_listToNat_cons`, `dlb_count_ofFn`, `dlb_majority_eq_of_odd`; `dlb_Ai`, `dlb_vote_eq`; `dlb_dec`, `dlb_Decodes`, `dlb_idealRound`, `dlb_vote_dec`, `dlb_oStep_round`, `dlb_roundsL_succ`, `dlb_loop_sem`; `dlb_raw_sem` | the machine computes `dlInverter` |
| Coins, machine | `dlb_split`, `dlb_ofFn_split`, `dlb_split_bijective`; `dlb_ℓP`, `dlb_coinsP`, `dlb_advice`, `dlb_advP`, `dlb_advice_length`, `dlb_B`, `dlb_B_runAt`, `dlb_B_coinLen` | `B` as an `NUPPT`; its coin decomposition |
| Probability | `dlb_statClose_pi`, `dlb_cut`, `dlb_guess_pushesUniform`; `dlb_isGenerator`, `dlb_expo_val`, `dlb_expOrd_eq`, `dlb_pred_eq`, `dlb_instance` | closeness of tuples; the uniform guess; one good instance |
| Reduction | `dlb_two_pow_size_le`, `dlb_window_params`, `dlb_eventually_pow_lt`, `dlb_arith_success`, `dlb_arith_loss`, `dlb_arith_final`, `dlb_succ`, `dlb_reduction` | parameters for large `n`; the reduction |

**No new host.** Both loops are instance data (step, start, bound) for the public state-loop host
`Complexity.StateLoop.gstep` with `Complexity.polyTimeComputable_iterate`, like dl-a's `dla_ss*`
family for `iterateFind`.

**Authorized re-points: none needed.** At the base `halfStr_spec` already reads
`rw [expEnc_eq]; unfold halfPred; rw [dlP_eq]; simp only [halfStr, …]` and `halfPred_eq` already uses
`((expValid_iff i).1 h).1.two_le`. No non-target proof was touched.

## 3. Reuse-not-copy screen (duplicated material, for approval)

| Helper | Relation | Request |
|---|---|---|
| `dlb_stateIterate_poly` | the 8-line body of `TCSlib.Cryptography.polyTimeComputable_stateIterate` (`Asymptotic/HardCoreLoops.lean`, public, outside this module's import closure) | move it into `Complexity.StateLoop` (`Randomized/Build/StateLoop.lean`), beside its ingredients |
| `dlb_count_ofFn` | the proof of `TCSlib.Cryptography.count_true_ofFn` (`Asymptotic/HardCoreGL.lean`, outside the closure), 8 lines | move it to a list/basic file |
| `dlb_foldl_bits`, `dlb_listToNat_cons` | the fold identity of the private `foldl_bits_eq` (`Asymptotic/Sampling.lean`) and of dl-a's `dla_listToNat_append` | publish `listToNat_cons` and `listToNat_append` beside `listToNat` (`NumberTheory/Primality.lean`) |
| `dlb_two_pow_size_le` | close to `TCSlib.Cryptography.two_pow_size_le` (`2^{size x} ≤ 2x + 1`, HardCoreGL, outside the closure) | promote one form |
| `dlb_cut`, `dlb_guess_pushesUniform` | relatives of dl-a's private `dla_pushesUniform_restrict` and of `pushesUniform_comp_injective` (`MultiMessage`) | dl-a's request (`HardcoreBit.pushesUniform_restrict`) covers it |
| `dlb_statClose_pi` | new: `StatClose` of `N` independent copies (`StatClose.prod`, `Fin.consEquiv`) | promote to `Asymptotic/Sampling.lean` as `StatClose.pi` |
| `dlb_ptc`, `dlb_take_poly`, `dlb_drop_poly`, `dlb_eq_poly`, `dlb_ite_poly` | applied-form wrappers of `PolyTimeComputable.comp`, `polyTimeComputable_pairTakePoly`/`DropPoly`, `polyTimeComputable_pairEq`, `polyTimeComputable_ite` (`dlb_ptc` is the private `ptc_comp` of `Randomized/Closure.lean`) | publish an applied-form `PolyTimeComputable.comp'` |
| `dlb_mulMod` … `dlb_rem` | composites of bundle fields; the RSA, Rabin and El Gamal fills need the same | a shared "modular numerals" layer beside `Candidates/Arithmetic.lean` |

**Mathlib first.** From Mathlib: `ZMod.euler_criterion_units`, `pow_mod_orderOf`, `ZMod.val_add`,
`val_mul`, `val_natCast`, `val_cast_of_lt`, `val_neg_of_ne_zero`, `ZMod.ringEquivCongr` and
`ringEquivCongr_val`, `Nat.card_zpowers`, `Subgroup.eq_top_of_card_eq`, `Nat.size_le`,
`Nat.lt_size_self`. No number-theoretic fact was re-proved.

## 4. Missing equations; name corrections

- **No E-API block.** Every foreign definition is read through a published lemma (§5.3).
- **Missing equation (worked around): `HardcoreBit.majority`** has no defining lemma
  (`PairwiseIndependence.lean` publishes only `two_mul_card_le_of_majority_ne`). Requested:
  `HardcoreBit.majority_eq (v : κ → Bool) : majority v = decide (Fintype.card κ < 2 * #{i | v i = true})`.
  With it `ℓ` could be even and `dlb_majority_eq_of_odd` would go.
- **Missing equation (worked around): the domain sampler.** No published lemma states
  `expSampleRaw`'s equation or `(expSampler H).coins`, so `expSampleRaw` cannot be run as a machine on
  `n·n` coins with `statClose_sampleBelowL`. Requested beside `expSampler` (dl-a's file):
  `expSampler_coins : (expSampler H).coins = .mul .var .var` and `expSampleRaw_eq`. The headline uses
  the collection's sampler and `SampleClose` instead (§1.1, item 2).
- **Name corrections:** the brief's table, plus `HardcoreBit.uprob_prod_and` (the sketch's
  "`OneWay.uprob_and_le_mul`-style product") and `HardcoreBit.pushesUniform_equiv`.
- **Notes for the maintainer (elaboration).**
  - The dl-a lesson recurred: `rw [← fullDLCollection_coinsEquiv_uexp …]` without its function
    argument matched the *collection's* average by unfolding the coin types (it produced
    `G.gen.runAt n [] r` with `r` a collection coin). The proof uses an explicit `calc` with the
    function given.
  - In long tactic proofs, `have h : PolyTimeComputable (constant) := combinator …` and `congr 1`
    triggered expensive defeq checks (`whnf` timeouts at 200k heartbeats in scratch); the proofs use
    one lemma per component and `congrArg … (funext …)`.

## 5. Checks

### 5.1 Owned file and sweep

- The owned file checks with **0 errors and no `sorry`**; its only warning is the unused `hg` of the
  frozen statement of `invProb_shiftInverter_ge` (§1, row 4). `evidence/logs/module-checks.log`.
- **Sweep** of the whole order list (`inputs/dl-b/order.txt`, 94 modules, in order, through
  `scripts/lean_check_tree.sh`): **SWEEP OK**, all 94 modules passed with 0 errors (start 2026-11-06T14:23:56Z, `SWEEP OK: all modules passed, end 2026-11-06T14:33:20Z`). The sweep ran on the working tree that is the final head: the log's header shows `ff22c944` because the seal fixes (`a5c54b0e`) were committed right after it; the owned file was rechecked at the final head (`module-checks.log`). Log: `evidence/logs/sweep.log`.
- **Sorry census from the sweep** (`evidence/logs/sweep-sorry-census.txt`) against
  `inputs/dl-b/base-sorries.txt`: **71 sorries in 14 modules**: the base's 78 in 15 minus exactly this unit's 7 (the `Candidates/DiscreteLogHardcore` row is gone); every other row equals its base count (Concrete 1, DiscreteLog 6, ElGamal 7, Factoring 10, RSA 10, Rabin 19, and the eight non-candidate rows).

### 5.2 Axiom prints (`evidence/logs/axioms.log`)

```
'TCSlib.Cryptography.Candidates.dlBits_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.uprob_trial_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.uprob_majOracle_ne_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.invProb_shiftInverter_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.invProb_dlInverter_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_halfStr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.fullDLCollection_hardCore' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
```

The headline's `sorryAx` comes only from `fullDLCollection_oneWay`, that is dl-a's
`expCollection_oneWay` (sorried at the base, filled on `fill/dl-a`); the other library lemmas the
headline's machine uses print the standard triple (`evidence/logs/axioms-deps.log`). **Integration replay** (`evidence/logs/integration-replay.log`, script `evidence/integ.sh`): in a scratch copy of the olean tree, dl-a's `Concrete.lean` and `DiscreteLog.lean` at `fill/dl-a` head `b62c34ee813eeccbaa8a7cbf9964d2356fedbf14` (read from its worktree) and this head's file, with every order-list module from `Concrete` to `DiscreteLogHardcore` recompiled in order (26 modules, 0 errors): **all seven targets, the headline included, print the standard triple `[propext, Classical.choice, Quot.sound]`.**

### 5.3 Rule-10 seal (`evidence/seal/`, `evidence/logs/seal.log`)

- **Sealed copy** `SealedDiscreteLogHardcore.lean` (made by `evidence/seal/mkseal.py`): the whole
  owned file with `attribute [local irreducible]` on every other-file TCSlib definition the proofs
  mention, right after the file's `open` line. A whole-file seal compiles, so no sectioning was
  needed.
- **Sealed names** (63; full names in `evidence/seal/sealed-names.txt`): `uprob uexp predProb invProb
  Negligible HardcoreBit.majority HardcoreBit.PushesUniform HardcoreBit.PairwiseIndep
  NumberTheory.QR NumberTheory.listToNat natToList natToBits mulStr addStr subStr divModStr xgcdStr
  modExpStr leStr dlP dlM dlG dlW WellFormedIndex ExpValid expOrd expUnit expEnc expDec expF
  ExpGroupGen.FullLengthExcept ExpGroupGen.dlProb ExpGroupGen.DLHard expCollection
  Collection.HardCore Collection.index Collection.SampleClose StatClose bitsToNat bitsEquiv decodeFin
  NUPPT.distinguisherL NUPPT.coinLen NUPPT.runAt NUPPT.runAtL NUPPT.output NUPPT.advInput
  NUPPT.ofPolyTime NUPPT.Uniform NUPPT.layout NUPPT.inParam NUPPT.inArg NUPPT.inAdvice NUPPT.inCoins
  NUPPT.coinsEquivPoly PolyTimeComputable pairFstD pairSndD Turing.pairEncode PolyExpr.eval
  StateLoop.gstep StateLoop.orbit StateLoop.gstepBound`. None is `@[simp]`; `NUPPT.Coins` is a
  reducible `abbrev` (notation, policy §1).
- **Result:** the sealed copy compiles with **0 errors** (the one `hg` warning).
- **The seal found real definitional reads, all fixed before delivery** (commit `a5c54b0e`):
  `PolyExpr.var.eval` and `id` read by defeq in `dlb_stateIterate_poly` (now `PolyExpr.eval_var`,
  `id_eq`); `StateLoop.orbit … 0` by `rfl` in `dlb_orbit_eq` (now `StateLoop.orbit_zero`);
  `StatClose` entered by `intro` (now `statClose_iff`); `Negligible` applied as a function three
  times (now `negligible_iff`); `Collection.SampleClose` applied as a function (now
  `Collection.sampleClose_iff`).
- **Controls** (`evidence/seal/controls.out`, `ControlUnsealed.lean`, `ControlSealed.lean`):
  `dlP i = listToNat (pairFstD i) := rfl` and `PolyExpr.var.eval n = n := rfl`, inside the file's
  namespace, **close unsealed and fail sealed** ("Type mismatch: rfl").
- **Grep of the diff** for foreign definition names inside `simp`, `simp only`, `rw`, `unfold`,
  `dsimp` and `delta` lists (`evidence/seal/grep-foreign.txt`, `evidence/seal/grepforeign.py`): 410
  tactic lists scanned; **no foreign definition is used as a rewrite or unfold rule**. The one
  lexical hit is `pairSndD` as the `start` *argument* of the lemma `StateLoop.gstep_iterate_eq`.
  Every `unfold` names an own-file definition.

### 5.4 Lint (`evidence/logs/lint.log`)

`python3 scripts/campaign_style_lint.py TCSlib/Cryptography/Candidates`: `style_lint: 8 FAIL, 9 WARN
over 8 files`. **No FAIL in the owned file's row**; the FAILs are Rabin's and ElGamal's
`polyTimeComputable_egGroupGenRaw`, pre-existing and not this unit's. The owned file's rows:

```
WARN  TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean  3036 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean  7 public def(s) without a lemma beside them (check 8): IsGenerator, dlInverter, dlRoot, halfBit, halfOracle, majOracle, shiftInverter
INFO  TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean  3036 lines; 59 public / 210 private declarations
```

- **Size (WARN; justification).** The file grows from 697 to 3036 lines. File ownership forbids a
  split inside this fill. The headline's machine and reduction (the `dlb_` section after
  `polyTimeComputable_halfStr`) form a module of their own: proposed for the next shared-file window,
  `Candidates/DiscreteLogHardcoreMachine.lean` imported by this file, and the modular-numeral layer
  beside `Arithmetic.lean`.
- Check 8 lists the seven public definitions of the base (`IsGenerator`, `dlInverter`, `dlRoot`,
  `halfBit`, `halfOracle`, `majOracle`, `shiftInverter`); this fill adds no public definition.

## 6. Diff

Only `TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean` changes (`git diff 16a7d02d --numstat`:
2346 added, 7 removed). The seven `sorry` lines are the only removed lines; every statement and definition is
byte-identical; every added line is a target body, a private `dlb_` declaration or a section header
comment.
