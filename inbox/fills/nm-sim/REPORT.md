# Fill `nm-sim` — checkpoint 1: SIM ⇒ IND proved (every attack)

**Worker:** Claude (external). **Issue base:** `262d6e9ae526c82eb68fe5a6169156bd1504e6d8` on
`cryptography/pass-shelat-ch2-4` (the merge of #294). **Local proof branch:** `fill/nm-sim`, head
`21d43d0c7`, never pushed; the whole series from the base is in `patches/`. **Pack:** read at exchange
`6f1e13ae6`; `SHA256SUMS` 7/7 OK; `order.txt` 252 modules, `roots.txt` 97, `base-sorries.txt` 26.

## Status

| Target | Status | Axioms |
|---|---|---|
| `FixedLengthPKScheme.nmSecure_of_simNMSecure` | **proved** | `propext`, `Classical.choice`, `Quot.sound` |
| `FixedLengthPKScheme.simNMSecure_of_nmSecure_cpa` | admitted (checkpoint 2) | + `sorryAx` |
| `FixedLengthPKScheme.simNMSecure_cpa_iff_nmSecure_cpa` | depends on the second | + `sorryAx` |

`evidence/logs/dev/cp1-axioms.log`. No statement was changed, no escalation is open, and no reader of a
frozen file was needed.

## The proof of `nmSecure_of_simNMSecure` (brief step 1)

The maintainer's route, with the bound `|adv_NM| ≤ 2·adv(D') + adv(D'')`. The sketch in the owned file
now describes the delivered proof (step numbers below are the sketch's).

1. **Sampler** `NMSim.halfSamp S` (uniform, coins `const 1`): on `⟨m₀, m₁⟩` (`paramLen = msgLen + msgLen`) it
   outputs `m_β` for its single coin `β` (`halfSamp_runAt`, `ofFn_drawWith_half`), with history `fun _ => []`
   and `histLen = const 0`. Its coins are one bit (`halfCoins`, `expect_sample_halfCoins`).
2. **SIM adversary** `A'`: T2 (`exists_interactiveHandlerMachine`) on `NMSim.simHandler S ℓ =
   copyHandler …`, which is `NMCCA2.fwdHandler` (imported, not copied) with seed `const 0`, `finCall = const 0`
   and a finalization that returns `A`'s output. `simulate_copyHandler_machine`: against any oracle and state,
   `A'`'s run is `A`'s, its output padded to `ℓ·ctLen + 0` bits. `Sim` comes from `h M A' (q·perCall + finCall) ℓ 0`.
3. **Distinguishers.** `D' = NMSim.tailDist S D` (built with `ofPolyTime` and `D`'s coins and advice): `0` if
   `m₀ = m₁`, else `[D(entry tails) = 1] == [m = m₁]`, where `entryTails` (a `chunkMap`) drops each entry's
   `COPY` flag, so a copy reads as `nmDecrypt`'s `⊥` (`nmOutput_eq_entryTails`). `D'' = NMSim.halfDist S`
   tests `m₀ ≠ m₁`.
4. **Both experiments on T2's lengths** (owned file, `accept_snmReal_eq`, `accept_snmIdeal_eq`):
   `castImpl_snmImpl` shows that `snmImpl`, read along `snmDin`/`snmDout`, is the hybrid oracle
   `NMSim.rImpl … false … ρ ρ' none`; `snmView_realView`/`snmView_idealView` turn the views into the
   list forms `realView`/`idealView`; `simImpl_eq_histImpl`. So `accept (snmReal …) = NMSim.realAcc …` and
   `accept (snmIdeal …) = NMSim.idealAcc …`.
5. **Real** (`NMSim.real_gap`): `2·Pr_real[D' = 1] − Pr_real[D'' = 1] = Pr[D(NM_1) = 1] − Pr[D(NM_0) = 1]`.
   - `accept_nmGame_eq_rImpl`: with the coin `β` fixed, `NM_β` is `A`'s run against `rImpl` with coin `β`
     (`castImpl_indImpl_abs` relates `indImpl` to `rImpl` through the state abstraction `s ↦ s.map fst`).
   - `expect_runB_good`: until a parameter with `m₀ ≠ m₁` is recorded the two coins give the same oracle,
     and such a parameter stays recorded (`expect_eq_until_bad`, Generic).
   - `real_identity` is the identity pointwise in keys and coins; `realAcc_copyHandler`/`realAcc_half`
     reduce `A'`'s experiment to `A`'s runs; linear algebra of expectations finishes.
6. **Ideal** (`NMSim.ideal_gap`): `2·Pr_ideal[D' = 1] = Pr_ideal[D'' = 1]` for every simulator.
   With `histLen = 0` the history oracle ignores the sampler's coin (`histImpl_coins`), so `β` is drawn after
   the run (`expect_sample_comm`); then `ideal_identity` (pointwise) and `D''` ignoring `β`.
7. `abs_le_of_gap` combines them: `ε = 2·ε' + ε''` (`Negligible.const_mul`, `Negligible.add`).

Edge cases: `m₀ = m₁` (both `D'`, `D''` output 0 there, and the coupling makes those runs equal); `msgLen = 0`
(then `m₀ = m₁` always, the advantage is `0 ≤ ε`); `ℓ = 0`; `A` never asking (the state stays `none`, read as
the parameter `0`, which has equal halves); repeated challenges (`rImpl_some`); budget 0 and the codecs'
timeouts (`castImpl_snmImpl` and the transports are equalities of whole runs, timeouts included); the
challenge copied (`entryL`'s `COPY` read as `⊥`, exactly `nmDecrypt_challenge`).

## Changed files (this checkpoint)

| File | Lines | Change |
|---|---|---|
| `NonMalleability/Simulation.lean` (owned) | 752 | target 1 proved; section *The experiments on T2's lengths*; target 1 sketch; `## Main results` |
| `NonMalleability/Simulation/Generic.lean` | 436 | new helper (generic; promotion requests) |
| `NonMalleability/Simulation/Hybrid.lean` | 532 | new helper (the hybrid oracle, views, acceptance rates) |
| `NonMalleability/Simulation/SimIND.lean` | 881 | new helper (sampler, SIM adversary, `D'`, `D''`, identities) |
| `NonMalleability/Simulation/SimINDGap.lean` | 343 | new helper (the two gaps) |

Every helper is in namespace `TCSlib.Cryptography.Composability.NMSim`. The owned file imports all four
(the style lint's facade check requires it). The module title keeps "(statement phase)" until the final.

## Duplication and promotions (preliminary; final list at the final delivery)

- **Imported, not copied:** `NMCCA2.fwdHandler`, `fwdHandler_finRun/_finCall/_advIn/_outLen`,
  `simulate_fwdHandler_impl`, `fields_finInput`, `polyTimeComputable_finFields`, `finA`;
  `AdaptiveCPA.castImpl`, `castImpl_eq`, `castImpl_self`, `expect_simulate_castImpl_toCompOn`,
  `simulate_eq_of_abs`, `ofFn_cast`, `ofFn_splitHalf_fst/_snd`, `padFin_ofFn_zeroBits`;
  `ChallengeSim.expect_sample_equiv/_prod/_comm`, `expect_sub`; `S.ofFn_nthCt`, `S.nmOutput_eq`,
  `S.nmDecrypt_eq`, `S.nmCodec_eq_bitCodec`, `indImpl_dec_onSpec_cast`, `indImpl_challenge_*_onSpec`.
- **DL-30–36 overlap: `flatMap_range_drop`** (`Generic.lean`, private) — the statement of the private lemma of
  `Indistinguishability/Forward.lean` used by `logEmit_encodeLog`, re-derived in general form for `chunkMap_flatten`.
- **Promotion requests:** `Generic.lean` entirely — `buildComp_budget_eq`, `toCompOn_budget_eq` →
  `Games/Machines.lean` (the budget reduction the brief asks for; used in checkpoint 2);
  `expect_congr_of_allOutputs`, `expect_expect_sample`, `bind_congr_of_allOutputs`, `expect_simulate_eager`,
  `expect_eq_until_bad` → `Games/Hopping.lean` / `Games/Probability.lean`; `chunkMap` and its lemmas →
  `Games/Efficiency.lean` (a polytime map over fixed-length blocks). From `Hybrid.lean`: `ofFn_block`,
  `ofFn_natAdd_eq_drop`, `ofFn_eq_map_range`, `decide_map_ofFn`, `chunkAt` (list facts). From
  `SimINDGap.lean` (private): `expect_toCompOn_outLen`, `lin_expect`, `lin_expect'`, `lin_sample`.

## Evidence (this checkpoint)

- `evidence/inputs/`: the pack as read (brief, addendum, README, order, roots, base-sorries, source hashes).
- `evidence/logs/preflight.log`, `packages-check.log` (11 match, 0 mismatch, 4 absent; `.lake/packages` is a
  symlink to this session's earlier narrowed fetch for nm-cca2, same `lake-manifest.json` pins),
  `cache-probe.log`, `bootstrap-upstream.tsv` (the 160 upstream modules of the order, all pass, incl.
  `Simulation` at the base) with per-module logs in `bootstrap/`, `bootstrap-extra.tsv`.
- `evidence/logs/dev/cp1-*.log`: the four helpers and the owned file, checked in order, one module per
  `scripts/lean_check_tree.sh` call (only the second target's `sorry` warning remains);
  `cp1-axioms.log`.
- The sweep, sorry census, whole-file seals and controls, explicit-unfold scan and lint evidence come with the
  final delivery. The campaign lint already passes on the changed files (0 FAIL; the remaining WARNs are on
  files outside this fill).

**Note.** The repository's `AGENTS.md` says not to run `lean`/`lake`; the brief and the addendum require
`scripts/lean_check_tree.sh`. I followed the brief.

## Next (checkpoint 2)

`simNMSecure_of_nmSecure_cpa` along the maintainer's route: the simulator as a T2 handler with one outer query,
the generic budget reduction (`toCompOn_budget_eq`, already in `Generic.lean`), the NM adversary `B` with the
bit encodings of `guessBit`, and `NM_0`/`NM_1` = real/ideal as the hybrids `rImpl … false/true`
(`expect_simulate_rImpl_eager`, `rImpl_eq_of_msgLen_eq_zero` for `msgLen = 0`).
