# Fill report · `bitwise-cpa` · final

**Worker** Claude (external fill, exchange push route). **Issue base**
`4a9b2c91eb2f89c4fb624339d5b4ba9cfd35ac27` on `cryptography/pass-shelat-ch2-4`. **Proof branch**
local `fill/bitwise-cpa` at `4cc388aba` (3 commits over the base; never pushed). **Pack** read at
exchange `f4737d78e`; `sha256sum -c SHA256SUMS` in `outbox/fills/bitwise-cpa/`: all 7 OK
(`evidence/logs/pack-sha256.log`). Source hashes: `sha256sum -c SOURCE-SHA256SUMS` at the base,
197/197 OK (`evidence/logs/source-sha256.log`). Checkpoint 1: exchange `43a16abd1`.

## 1. Result

**`BitPublicKeyScheme.SingleBitSecure.bitwise_padded_cpa` is proved.** No admission remains in the
touched files. The frozen statement is byte-identical to the base (only the body and the sketch
changed). Axioms of the target: `[propext, Classical.choice, Quot.sound]`. No escalation: the
target is true and every reading goes through published readers (one reading found by the seal
was rerouted, §5).

The proof follows the brief's route; step 3 is an exact identity: with `j = j⋆(n) < n`,
`advantage(H_j, H_{j+1}) = distAdv (S.pkEncDist n false) (S.pkEncDist n true) (D.distinguisherL n)`
(`hyb_advantage_eq`), and then `advantage(Ind_0, Ind_1) = advantage(H_0, H_n) ≤ n · distAdv`.

| Brief step | Delivered as |
|---|---|
| 1 bit hybrids | `hybGame S L hL hmsg A q n j` (private): sample `rg`, `A`'s coins `r`, and `n` single-bit encryption tapes `v : Fin n → S.enc.Coins n`; run `A` with `ChallengeSim.chRun` whose challenge `mm` is answered by `padCt L(n)` of `hybCt` (block `i` = `Enc(pk, [l_{n+i}]; v_i)` if `i < j`, `Enc(pk, [l_i]; v_i)` otherwise, `l = ofFn mm = m₀ ‖ m₁`). `accept_indGame_eq`: `Pr[Ind_b = 1] = Pr[H_{b ? n : 0} = 1]`, by eager coins (`BitwiseSim.expect_simulate_indImpl_cpa`), `padded_enc_runAt`, the coin bijection `bitwiseEncCoins` then `coinsCongr`, the layout `bitwise_enc_runAtL` (via `bitwise_enc`), `bitwiseEncCoins_ofFn` and `coinBlock_ofFn_coinBlocks`. At `n = 0` the two ends are the same hybrid and the advantage is `0`. |
| 2 distinguisher `D` (T1) | `BitwiseSim.exists_qHandlerMachine` (T1 for the new generic `qHandler`): lengths `din = [L, n+n]`, `dout = [n+1, L]`, `dα = 1`; seed `n·B(n)` bits (`mul var S.enc.coins`); state `⟨aux, asked :: x⟩` with advice `aux = bwAux S js n = ⟨1^{j⋆}, ⟨1^{(j⋆+1)·B}, 0…⟩⟩` padded to `bwLaux S` bits; `Dec` answered `⊥`; the first challenge recorded and every challenge answered `BitwiseSim.plantAns` of the recorded one (`T₁ ‖ ⟨c, T₂⟩` from the published `blockEncFun`, then `padCt`); output `BitwiseSim.plantOut`: `[a]` for `(0,1)`, `[¬a]` for `(1,0)`, `[0]` for equal bits or no challenge. `j⋆` is chosen per `n` from `exists_advantage_hybrid_gap` (`choose`). |
| 3 exact identity | `hyb_advantage_eq`: both hybrids depend only on the first challenge (`chRun_congr`); `D`'s output (`hrun`) is the post-processed bit of `A`'s run against the planted tuple `W β v re l` (`plantTuple_spec`, `plantOut_recorded`, `plantOut_init`, transport by `indCodec_eq_bitCodec`); resampling coin block `j` (`expect_sample_update`) turns `H_j` into `W (l_j)` and `H_{j+1}` into `W (l_{n+j})` (`planted_eq`, `hybCt_update`); the seed is reindexed by `coinBlocks` and `finCongr (bitwise_enc_coinLen n)`; the signed case split is `ChallengeSim.expect_indicator_sub`. |
| 4 bound | `ε n = n · distAdv(…, D)`: `((singleBitSecure_iff S).1 h D).polyExpr_mul .var`; for `n > 0`, `div_le_iff₀` on the gap. |

**Edge cases.** The computation is treated abstractly, so the proof is uniform in the budget
(`q = 0` included) and in the codec's timeout output `zeroBits 1`, which is just `A`'s output on
both sides. A run with no challenge is the `firstQ = none` branch: both hybrids give `F []`, `D`
outputs `[0]` (`plantOut_init`). Repeated challenges get the recorded answer in the hybrids
(`chRun_query_one_some`) and the same assembled tuple in the handler (`qRun_recorded`,
`simulate_qHandler_recorded`). At `n = 0` the bound is `0 ≤ 0`.

**Checkpoints.** All four steps were completed together, so checkpoint 1 (exchange `43a16abd1`,
proof-branch `1f83fc508`) already carried the complete proof with the checks pending; commit 3
(`4cc388aba`) is the seal fix of §5. Checkpoints 2 and 3 were not sent separately.

## 2. Changed files and declarations

`git diff --stat 4a9b2c91..4cc388aba`: 4 files, 1370 insertions, 19 deletions.

| File | Lines | Change |
|---|---|---|
| `TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA.lean` (owned) | 105 → 553 | 3 imports; new private section `BitwiseCPAProof` before the target; target body and sketch; the module docstring's status phrase |
| `…/PublicKey/BitwiseCPA/QueryHandler.lean` (new helper) | 395 | generic query-recording handler with advice, its simulation, transport, machine by T1 |
| `…/PublicKey/BitwiseCPA/Planted.lean` (new helper) | 316 | the planted tuple, padded answer and final bit (generic in the encryptor), list identities |
| `…/PublicKey/BitwiseCPA/Eager.lean` (new helper) | 192 | eager coins (generic and for `indImpl`), coordinate resampling, readers |

The helpers import neither `BitwiseCPA` nor anything downstream of it; `BitwiseCPA` imports all
three explicitly. All files are below 1000 lines. `AdaptiveCPA.lean`, `OracleSecurity.lean`, the
`OracleSecurity/` helpers, `EnsembleSecurity.lean` and every other existing file are unchanged.
Statements, other declarations (including the two proved corollaries), the statement prose and
global simp attributes are unchanged. **Sketch edits:** the target's `**Proof sketch.**` now
describes the delivered proof; the module docstring's "Main results" line lost "(stated; a `sorry`
under its sketch)" and names the three helpers.

**New public declarations** (namespace `TCSlib.Cryptography.Composability.BitwiseSim`; each with a
formula docstring, and a proof sketch when nontrivial; definitions with `_eq` or case lemmas, the
structure with `simps` field equations, `isSimp := false`):
- `QueryHandler`: `qDin` (+ `_zero`, `_one`), `qDout` (+ `_zero`, `_one`), `qRun` (+ `qRun_eq`,
  `qRun_dec`, `qRun_fresh`, `qRun_recorded`, `polyTimeComputable_qRun`), `qHandler` (+ `simps`
  equations), `decodeFin_nil_getD`, `qHandler_answer_dec`, `simulate_qHandler_recorded`,
  `simulate_qHandler_init`, `chRun_toCompOn_transport_list`, `exists_qHandlerMachine`.
- `Planted`: `ofFn_const_of_eq_one`, `flatten_ofFn_singleton`, `take_ofFn_flatten`,
  `drop_ofFn_flatten`, `headD_drop`, `plantTuple` (+ `_eq`, `polyTimeComputable_plantTuple`,
  `plantTuple_spec`), `plantAns` (+ `_eq`, `polyTimeComputable_plantAns`), `plantOut` (+ `_eq`,
  `plantOut_init`, `plantOut_recorded`, `polyTimeComputable_plantOut`).
- `Eager`: `expect_simulate_eager`, `expect_simulate_indImpl_cpa`, `ofFn_cast`,
  `expect_sample_update`, `indCodec_eq_bitCodec`, `padded_enc_runAt`, `padded_enc_coins`.

**New private declarations in `BitwiseCPA.lean`:** `hybCt`, `hybGame`, `bitwise_runAtL`,
`bitwise_runAt_blocks`, `ofFn_half`, `ofFn_getD_split`, `accept_indGame_eq`, `planted_eq`,
`hybCt_update`, `bwLaux`, `bwAux`, `bwAux_length`, `hyb_advantage_eq`.

## 3. Promotion, duplication and reader requests (DL-30)

**Promotion requests.**
1. `BitwiseSim.expect_simulate_eager` / `expect_simulate_indImpl_cpa`: the eager-coins lemma. The
   `padded_cpa` proof has it as a private lemma of `OracleSecurity.lean`; this copy is restated
   for a generic CPA-shaped oracle and instantiated through `indImpl_*_onSpec`, because a verbatim
   copy outside `OracleSecurity` would read `inLens`/`outLens` definitionally. Proposed home:
   the generic form in `OracleSecurity/ChallengeSim.lean`, the instance as a public lemma of
   `OracleSecurity.lean` (replacing its private one).
2. `indCodec_eq_bitCodec`, `padded_enc_runAt`, `padded_enc_coins`: readers of
   `FixedLengthPKScheme.indCodec` and `PublicKeyScheme.padded` derived from the published ones;
   they belong beside `indCodec_*` and `padded_*` in `OracleSecurity.lean`.
3. `expect_sample_update` (resampling one coordinate of a uniform tuple) belongs with the
   sampling identities of `ChallengeSim` or in `Games/Probability.lean`.
4. `chRun_toCompOn_transport_list` generalizes `ChallengeSim.chRun_toCompOn_transport` to a
   query-dependent answer; it belongs beside it.
5. `ofFn_cast`, `ofFn_const_of_eq_one`, `flatten_ofFn_singleton`, `take_ofFn_flatten`,
   `drop_ofFn_flatten`: generic list facts for a shared list module.

**Duplication.** `headD_drop` (`(l.drop k).headD false = l.getD k false`) duplicates the public
`headD_drop` of `ZeroKnowledge/CommitmentLemmas.lean` (with a general default) and
`getD_eq_headD_drop` of `ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean`; I did not import them
because that would pull the zero-knowledge closure into this unit. Mathlib's
`ofFn_take_eq_take_ofFn` (`Mathlib/Data/Fin/Tuple/Take.lean`) is close to `take_ofFn_flatten` but
is outside the roots. A search found no other existing lemma of these forms.

**Reader requests (none blocking).** `HybridMachine.hybridPre` has no published `_eq` reader, so
its proved polynomial-time bound could not be used; `plantTuple` rebuilds the planted assembly from
`blockEncFun` (with readers `blockState_eq`, `blockEncFun_flatten`, `encodeList_ofFn_split`,
`coinBlock_drop`). A `hybridPre_eq` would let the two share one function.

## 4. Environment, cache and bootstrap

- **Preflight** (`evidence/logs/preflight.log`): `nproc` 4. The cgroup is v1 and
  `memory.limit_in_bytes` is the unlimited sentinel (2^63 − 4096), so the headroom is
  `MemAvailable` = 15,939,212 kB = 15.20 GiB (floor 4 GiB): PASS. The clone's filesystem is ext4
  on `/dev/vda` with 20,396,564,480 B = 19.00 GiB free (floor 12 GiB): PASS; the scratch
  directories are on the same filesystem (no tmpfs).
- **One clone**: `/home/user/fill`, a worktree of the session's checkout, with its own `.lake`.
  It is the clone (and `.lake/packages`) this session used for the `padded-cpa` fill earlier on
  this host; the toolchain and `lake-manifest.json` are identical between the two bases. Nothing
  was copied, moved or deduplicated.
- **Cache**: store before the fetch `/root/.cache/mathlib`, 2,372 files, 118,543,444 bytes
  (`evidence/logs/cache-store.log`), written by the cache tool during that earlier fill; none were
  downloaded by this fill. Narrowed `TAR_OPTIONS=--no-same-owner lake exe cache get` for the 92
  roots (identical to `roots.txt`): "No files to download", "Decompressing 2345 file(s)",
  "Completed successfully!", exit 0 (`evidence/logs/cache-get.log`). No empty `.olean`. Cache
  probe `import Mathlib.Algebra.BigOperators.Field`: passed (`evidence/logs/cache-probe.log`).
- **Packages**: `package check: PASS (0 mismatches)` before and after the fetch; ABSENT
  `doc-gen4`, `UnicodeBasic`, `BibtexQuery`, `MD4Lean`, none imported by the order list
  (`evidence/logs/packages.log`).
- **Bootstrap**: a fresh olean tree (`TCSLIB_OLEANS=.lake/bw-oleans`). The 153-module upstream
  closure of `PublicKey/BitwiseCPA`, in the order list's order, all passed
  (`evidence/logs/bootstrap.log`, `bootstrap-closure.txt`); the remaining modules were built by
  the sweep.
- **Process discipline**: one Lean process at a time, every check through
  `scripts/lean_check_tree.sh` (`evidence/tools/chk.sh` logs start, end, status, elapsed time and
  maximum child RSS). No `lake build`. **Deviation:** one development check of the
  owned module hung in a looping tactic and was stopped after about 40 minutes by the tool
  runner's background limit (no Lean exit code, no output). To locate it I set
  `maxHeartbeats 400000` in the owned file during development and ran that one check under a
  25-minute `timeout` (it finished in 28 s); the cap is gone (the file keeps the base's
  `maxHeartbeats 0`), and no other check was wrapped in a timeout. Development logs:
  `evidence/logs/dev/`.

## 5. Checks

| Check | Result | Evidence |
|---|---|---|
| Owned and helper modules | `BitwiseCPA`, `BitwiseCPA/{QueryHandler, Planted, Eager}`: no errors, no warnings | `logs/sweep.log` |
| Sweep (final head `4cc388aba`) | `order-new.txt`, 200 modules, one `lean_check_tree.sh` call each: **200 passed, 0 failed** | `logs/sweep.log` |
| `sorry` census | **26** (base 27); removed vs base: exactly `bitwise_padded_cpa`; added: none | `logs/sorry-census.txt` |
| Axioms | `bitwise_padded_cpa`: `[propext, Classical.choice, Quot.sound]`; `bitwise_padded_adaptive_cpa` and `exists_adaptive_cpa`: `[propext, sorryAx, Classical.choice, Quot.sound]` (the `sorryAx` is the parallel `adaptive-cpa` target `INDSecure.adaptive_cpa`) | `logs/axioms.log`, `probe/Axioms.lean` |
| Lint | `campaign_style_lint.py TCSlib/Cryptography/Encryption/PublicKey --check8b`: 0 FAIL, 6 WARN over 22 files; the same 6 WARN at the base (19 files), all in untouched files; the helper subdirectory alone: 0 FAIL, 0 WARN | `logs/lint-after.log`, `lint-before.log`, `lint-subdirs.log` |
| Patches | `git apply` of `patches/` onto a clean base worktree reproduces all four `src/` files byte for byte | `logs/patch-reproduce.log` |

An earlier full sweep at `1f83fc508` (before the seal fix) also passed 200/200 with the same census
(`logs/sweep-1.log`, `sorry-census-1.txt`). Resources: peak child RSS 2,945 MiB over all checks;
`BitwiseCPA/Planted` takes about 220 s unsealed (2–3 s sealed, so the time goes to definitional
unfolding attempts that the proof does not need); the owned module takes 25 s.

## 6. Readings: scan, seal, controls, explicit unfolds

- **Scan** (`seal/SealScan.lean`, `logs/seal-scan.log`): roots are the target, its 13 private
  helpers and every declaration of the three helper modules (67 roots, 92 declarations scanned
  with their auxiliaries). 95 foreign TCSlib definitions are used: 66 regular (the seal
  candidates, `seal/candidates.txt`) and 29 reducible (abbrevs such as `bitSpec`, `bitSpecAt`,
  `indSpec`, `NUPPT.Coins`, `padEnc`, and structure projections). **TCSlib instances used: 0.**
- **Seal** (`seal/Seal{QueryHandler,Planted,Eager,BitwiseCPA}.lean`, `logs/seal.log`): verbatim
  copies of the four files with `attribute [local irreducible]` on every regular foreign definition
  their roots use (23, 17, 26 and 48), from each namespace's first `open` on, so the whole file
  including the target and the untouched corollaries is sealed. **All four compile.**
- **Finding and fix.** The first sealed run failed in `SealQueryHandler`: `qHandler`'s
  `advIn_poly` field read the body of the published `RecordHandler.recAdvIn` definitionally. It
  now goes through `recAdvIn_eq` (proof-branch commit 3, `4cc388aba`); the sweep, seal and scans
  were redone at that head. During development the same discipline led me to restate the eager
  coins through `indImpl_*_onSpec`, `indSpec_challengeDom`/`_challengeRng` and `inLens_one`/
  `outLens_one` (`ofFn_cast`) instead of identifying `Fin (inLens n 1)` with
  `Fin (msgLen + msgLen)` by unfolding.
- **Controls** (`seal/SealControls{Unsealed,Sealed}.lean`): eight readings through definition
  bodies, namely `inLens`, `outLens`, `PolyExpr.eval`, `padCt`, `seedIn`, `ChallengeSim.chRun`, and the
  new helpers `qDin` and `plantAns`. Unsealed: all pass. Sealed with the full candidate list: all
  eight fail (8 errors). **8/8.**
- **Explicit-unfold scan** (`seal/RwIds*.lean`, `logs/rwids.log`, `logs/rwids-files.tsv`): every
  identifier the added lines pass to `rw`, `rwa`, `erw`, `simp`, `simp only`, `simp_rw`, `simpa`,
  `dsimp` or `unfold`, resolved in each file's namespace (245 entries). **No foreign definition is
  passed**: the resolved names are theorems, and the only definitions passed are the owned file's
  own private `hybGame`, `hybCt`, `bwAux` and `bwLaux` (listed unresolved because private, with
  local hypotheses).

## 7. Order and roots

`evidence/logs/order-new.txt`: the issued 197-module order with the three helpers inserted
immediately before `PublicKey/BitwiseCPA` (`…/BitwiseCPA/Eager`, `…/Planted`, `…/QueryHandler`),
200 modules; every module's TCSlib imports precede it, and the upstream closure of
`PublicKey/BitwiseCPA` is contained in it. The helpers import no Mathlib module directly; the
Mathlib roots of the extended order are unchanged (92, identical to `roots.txt`).

**Final payload delivered — ready for maintainer review**
