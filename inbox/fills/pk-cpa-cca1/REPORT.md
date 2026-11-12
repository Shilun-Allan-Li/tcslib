# Fill report · `pk-cpa-cca1` · final

**Worker** Claude (external fill, exchange push route). **Issue base**
`8c3afbff69ad1273446750f47c05d424ab13ebe2` on `cryptography/pass-shelat-ch2-4`. **Proof branch**
local `fill/pk-cpa-cca1` at `79f34dadd` (8 commits over the base; never pushed). **Pack** read at
exchange `db04fd415`; `sha256sum -c SHA256SUMS` in `outbox/fills/pk-cpa-cca1/`: all 7 OK
(`evidence/logs/pack-sha256.log`). Source hashes: `sha256sum -c SOURCE-SHA256SUMS` at the base,
242/242 OK (`evidence/logs/source-sha256.log`). Checkpoint 1: exchange `d458a5848`; checkpoint 2:
exchange `d9e7bcce1`.

## 1. Result

**`Composability.prfFixedScheme_cpa` and `Composability.prfFixedScheme_cca1` are proved.** No
admission remains in the touched files. Both statements are byte-identical to the base (only the
bodies and the sketches changed). Axioms of both targets: `[propext, Classical.choice,
Quot.sound]`. No escalation: both targets are true as stated, and every reader the proof needs is
published (the four authorized `OracleSecurity` readers, plus readers in my own helper modules).

**The bound.** For an adversary `A` with budget `q` and the attack `atkOf atkBit` (`CPA` for
`false`, `CCA1` for `true`), there are PRF distinguishers `D₀`, `D₁` with, for every `n`,

`advantage(IND₀, IND₁) ≤ prfAdv(F_n, D₀) + prfAdv(F_n, D₁) + (q(n)² + 1) · 2⁻ⁿ`

(`prf_advantage_le`). The right side is negligible (`prf_indSecure`).

| Brief step | Delivered as |
|---|---|
| 1 PRF → random function | `PRFGame.exists_prfReduction` (`OracleFromPRF/Reduction.lean`). For each bit `b` there is a next-query machine `D_b`: T4 (`exists_toOracleAdversary_of_bitCodec`) of T2's machine (`exists_interactiveHandlerMachine`) for the handler `PRFGame.pkHandler q atkBit b`, through the input-free companion of `A` (`exists_toCompOn_of_toComp`). For **every** `f`, `D_b` with budget `qRed q` accepts against `f` exactly when `A` outputs `1` in the experiment `PRFGame.fImpl … f` (the IND oracles with pad function `f`). The handler's seed is `q(n)` nonce tapes (`pkTapes`). Its state counts the tapes used and records the challenge. Composed with the outer oracle `f`, its run is the experiment with the tapes in advance (`eImpl`) while fewer than `q(n)` tapes are used (`simulate_eq_of_abs_bounded`, `comp_pkAbs`); uniform tapes are fresh nonces (`expect_eImpl`). In the owned file, `accept_prf_indGame` (`n > 0`) shows the IND game is `fImpl … (F n k)` averaged over the key; `expect_indImpl_fImpl` in `Transfer.lean` matches the scheme's oracles call by call. `prfAdv_prfReduction` gives `prfAdv(F_n, D_b) = \|Pr[IND_b = 1] − 𝔼_R Pr[A → 1 against fImpl … R]\|`. |
| 2 random-function game | `PRFGame.expect_lazyImpl` (`Lazy.lean`): averaging over a uniform `R` is the lazy experiment `lazyImpl` (a table, the challenge record and a bad flag). The flag is raised when the challenge's `r*` is already a point of the table (an earlier encryption's nonce or, for CCA1, a pre-challenge decryption's), or a later encryption uses `r*`. `lazyImpl_agree` + `identical_until_bad` (`Collision.lean`): from a good state the two bits give good successors the same law. At the first challenge the pad is changed by `y ↦ y ⊕ m₀ ⊕ m₁` (`xorPerm`, `ctOf_xorPerm`, `expect_sample_equiv`). Decryption is refused after the challenge (`decOpen` for CPA and CCA1). `lazyImpl_step`: from a good state a query raises the flag with probability at most `(\|T\| + 1)/2ⁿ`. This uses `prob_mem_le` through `expect_sample_mem_le`: on the table's keys for the first challenge, and on `[r*]` for an encryption. `lazyImpl_grow`: a query adds at most one point. `prob_bad_le` (a potential argument) gives `Pr[bad] ≤ q · q / 2ⁿ`. Hence `abs_prob_lazyImpl_sub_le` and `abs_expect_fImpl_sub_le`: the two random-function experiments differ by at most `q(n)² / 2ⁿ`. |
| 3 the bound | `prf_advantage_le` (owned, private). For `n > 0`, use the triangle inequality through the two random-function experiments. For `n = 0`, `advantage ≤ 1 ≤ q(0)² + 1`. `prf_indSecure`: `ε n = prfAdv(F_n, D₀) + prfAdv(F_n, D₁) + ((q·q + 1)(n)) · (2⁻¹)ⁿ` is negligible. This follows from `PRF.negligible_prfAdv` (twice, budget `qRed q`), `EnsembleLemmas.negligible_polyExpr_mul`, `negligible_two_pow_neg` and `Negligible.add`. The targets are `prf_indSecure` at `atkBit = false` and `true` (`atkOf_false`, `atkOf_true`). |

**Deviation from the brief's route.** Both target docstrings record this.
- **The bit.** The brief puts the challenge bit in the reduction's seed, with a finalization that compares the guess with it. Instead I hard-wire the bit: one reduction per bit, each forwarding the adversary's guess.
- **The bound.** The brief's bound is `2 · prfAdv + q(n)/2ⁿ`; mine is `prfAdv(D₀) + prfAdv(D₁) + …`. The brief allows this ("or the exact form you prove").
- **The collision term** is `q(n)²/2ⁿ`. The bad event is bounded query by query: at most `q` steps can raise it, each against at most `q` recorded points. A single draw against `q` points is not enough, because the adversary's later encryptions can also hit `r*`.
- **The `+ 1`** covers `n = 0`.

**Edge cases.**
- **Budget and timeout.** The proof treats the adversary's computation abstractly, so it holds for every budget and for the codec's timeout output.
  - `q = 0` is included: `prob_bad_le` gives `0`.
  - The same `A.toComp` run appears in the game, the reduction and the lazy experiments.
  - The reduction's own budget `qRed q = q · 1 + 0` covers that run (`toComp_costBoundedBy`, `simulate_eq_of_abs_bounded`).
  - The handler's finalization asks nothing and returns `A`'s bit (`pkHandler_finish`).
- **`n = 0`:** `advantage ≤ 1` (see the step 3 row above).
- **No challenge:** the record stays `none` and the experiments never read `b`. The challenge never raises the flag.
- **Repeated challenges** return the recorded ciphertext:
  - in the game (`indImpl_challenge_repeat_onSpec`);
  - in `fImpl` and `lazyImpl` (`_challenge_some`);
  - in the handler (`pkHandler_impl_challenge_some`).
- **`Dec` on the challenge:** after the challenge, CPA and CCA1 answer `⊥` (`decOpen_atkOf`), as the game does.
- **`Dec` on malformed strings:** the answer is `⊥`. See `decWF`, `ofFn_prf_decAnswer` (via `decodeFin_runAt_prfDec_of_not_wf`) and `pkHandler_impl_dec_closed`.

**Checkpoints.**
- 1 (`d458a5848`): step 1.
- 2 (`d9e7bcce1`): step 2.
- Final: step 3, the seal fixes (§6) and all checks.

## 2. Changed files and declarations

`git diff --stat 8c3afbff6..79f34dadd`: 8 files, 2975 insertions, 24 deletions.

| File | Lines | Change |
|---|---|---|
| `PrivateKey/OracleFromPRF.lean` (owned) | 579 → 885 | Imports the six helpers. Module docstring: the title's "(statement phase)" is dropped; the status lines of the two targets are updated; a `## Contents` list is added, because `OracleFromPRF/` now exists and the lint treats the file as a facade. Adds the private section `PRFStep` before the targets. Changes the two sketches and bodies. |
| `PrivateKey/OracleSecurity.lean` (authorized readers) | 345 → 374 | Adds `indSpec_encDom`, `indSpec_encRng`, `indImpl_enc_onSpec` and `indImpl_challenge_repeat_onSpec`: public, not `@[simp]`, with formula docstrings, beside the existing `_onSpec` readers. Nothing else changed (0 removed lines). |
| `…/OracleFromPRF/Games.lean` (new) | 327 | Ciphertexts `ctOf`, `decWF`, `decAns`. The experiment with a pad function (`fImpl`) and with nonce tapes (`eImpl`). `expect_simulate_congr`, `simulate_eImpl_congr`, `expect_eImpl`. |
| `…/OracleFromPRF/Handler.lean` (new) | 741 | Lengths `ctP`, `pkDin`, `pkDout`, `pkOut` (abbrev), `pkStLen`. State `recBits`, `pkState`, `pkHState`. Tapes `pkTapes`, `pkSeedTapes`. The T2 handler `pkHandler` (`simps`, `isSimp := false`) and its answers. |
| `…/OracleFromPRF/Reduction.lean` (new) | 372 | `simulate_eq_of_abs_bounded`, `fOuter`, `atkOf`, `qRed`, `pkAbs`, `comp_pkAbs`, the width transports, `toComp_costBoundedBy`, `exists_prfReduction`. |
| `…/OracleFromPRF/Transfer.lean` (new) | 205 | Vector readings. `expect_indImpl_fImpl`: a scheme with `ctOf`-shaped encryption and `decWF`-shaped decryption is `fImpl`, call by call. `indCodec_eq_bitCodec`, `expect_fImpl_transport`. |
| `…/OracleFromPRF/Lazy.lean` (new) | 473 | `LState`, `rStar`, `padAt`, `look`, `ovr`, `addPt`, `hitStar`, `lazyImpl`; `expect_lazyImpl`. |
| `…/OracleFromPRF/Collision.lean` (new) | 498 | `prob_bad_le`, `expect_sample_mem_le`, the `b`-independence lemmas, `xorPerm`, `lazyImpl_agree`/`_stick`/`_grow`/`_step`, `abs_prob_lazyImpl_sub_le`, `abs_expect_fImpl_sub_le`. |

Every file is under 1000 lines. `Handler.lean` is over the lint's 600-line target (INFO only).

**New public declarations.** Each has a formula docstring, and a proof sketch when nontrivial. Definitions have `_eq`, `_apply` or case lemmas.
- **`Games`:**
  - `ctOf` (+ `_eq`, `length_ctOf`), `decWF` (+ `_eq`), `decAns` (+ `_eq`);
  - `expect_simulate_congr`;
  - `fImpl` (+ `_enc`, `_dec`, `_challenge_none`, `_challenge_some`) and `eImpl` (+ the same four);
  - `simulate_eImpl_congr`, `expect_eImpl`.
- **`Handler`:**
  - lengths: `ctP` (+ `_eval`), `pkDin` (+ `_zero/_one/_two`), `pkDout` (+ `_zero/_one/_two`), `pkOut` (+ `_eq`), `pkStLen` (+ `_eq`);
  - state: `recBits` (+ `_none`, `_some`, `length_recBits`), `pkState` (+ `_eq`), `pkHState` (+ `_eq`);
  - tapes: `pkTapes` (+ `_apply`, `ofFn_pkTapes`), `pkSeedTapes` (+ `_eq`);
  - the handler: `pkHandler` with its `simps` equations, `pkHandler_init_eq`, `pkHandler_init_hstate`, `pkHandler_finish`, and the answers `pkHandler_impl_enc`, `_impl_dec_open`, `_impl_dec_closed`, `_impl_challenge_some`, `_impl_challenge_none`;
  - 33 private helpers: the round function `pkRun`, `pkFin`, their polynomial-time proofs and their reading lemmas.
- **`Reduction`:**
  - `simulate_eq_of_abs_bounded`;
  - `fOuter` (+ `_apply`; private `fOuter_tape`), `atkOf` (+ `_false`, `_true`, `decOpen_atkOf`), `qRed` (+ `_eval`), `pkAbs` (+ `_eq`);
  - `comp_pkAbs`, `ofFn_evalFn_toCompOn`, `expect_fImpl_width`, `eval_toOracleAdversary_width`, `toComp_costBoundedBy`, `exists_prfReduction`.
- **`Transfer`:** `ofFn_arrowCongr_finCongr`, `padFin_replicate_false`, `padFin_nil`, `eq_of_ofFn_eq`, `expect_indImpl_fImpl`, `indCodec_eq_bitCodec`, `expect_fImpl_transport`.
- **`Lazy`:**
  - the state: `LState`, `rStar` (+ `_eq`, `rStar_ctOf`), `padAt` (+ `_eq`, `padAt_ctOf`), `look` (+ `_none`, `_some`, `look_flag`), `ovr` (+ `_apply`), `addPt` (+ `_eq`), `hitStar` (+ `_some`, `_none`);
  - the experiment: `lazyImpl` (+ `_enc`, `_dec_open`, `_dec_closed`, `_challenge_some`, `_challenge_none`);
  - recorded values: `zipWith_xor_cancel_left`, `ovr_addPt_of_isSome`, `ovr_addPt_of_none`, `ovr_addPt_self`, `ovr_record_of_none`, `ovr_record_of_some`;
  - `expect_lazyImpl`.
- **`Collision`:**
  - generic: `prob_bad_le`, `expect_sample_mem_le`, `mem_keys_of_lookup_isSome`, `abs_expect_sub_le`;
  - state readings: `length_addPt_le`, `flag_addPt`, `look_eq_of_hitStar`, `isSome_look_eq`, `addPt_eq_of`, `ovr_init`;
  - the change of variables: `xorPerm` (+ `_apply`, `ctOf_xorPerm`);
  - the lazy experiment: `lazyImpl_agree`, `lazyImpl_stick`, `lazyImpl_grow`, `lazyImpl_step`, `abs_prob_lazyImpl_sub_le`, `abs_expect_fImpl_sub_le`.

**New private declarations in `OracleFromPRF.lean`** (section `PRFStep`): `prf_gen_runAt`,
`prfKeyEq`, `ofFn_prfKeyEq`, `prfNonceEq`, `ofFn_prfNonceEq`, `ofFn_prf_encryptAt`,
`ofFn_prf_decAnswer`, `prf_ctLen_eval`, `prf_inLens`, `prf_outLens`, `accept_prf_indGame`,
`prfAdv_prfReduction`, `prf_advantage_le`, `prf_indSecure`.

**Sketch edits.** Both target docstrings keep their first paragraph (the statement prose). Each gets a
`**Deviation:**` paragraph (see §1) and a `**Proof sketch.**` describing the delivered proof, replacing
"Proof sketch (the source's)". The module docstring's status lines now say "proved" and give the bound.

## 3. Promotion, duplication and reader requests (DL-30 to DL-33)

**Promotion requests.** These generic facts are in my helper modules because every other file is
frozen. The proposed homes:
1. **`Games/Probability.lean`** (with DL-30): `Collision.abs_expect_sub_le` (expectations of pointwise
   `ε`-close functions are `ε`-close).
2. **`Games/Hopping.lean`:**
   - `Collision.prob_bad_le`: a bad event raised with probability at most `(size + 1)·δ` per query, by queries that grow the size by at most one, has probability at most `q·(size + q)·δ`. This is the potential argument the brief's "adaptive repeated-nonce event" needs.
   - `Collision.expect_sample_mem_le`: `prob_mem_le` for a fixed list.
3. **`Games/Simulate.lean`** (with DL-32's `simulate_eq_of_abs`):
   - `Games.expect_simulate_congr`: implementations with equal per-call expectations simulate alike.
   - `Reduction.simulate_eq_of_abs_bounded`: DL-32's `AdaptiveCPA.simulate_eq_of_abs` with a counter budget and deterministic steps. It generalizes that lemma's use in this unit.
4. **`Games/Machines.lean` or `Games/Bridges`:** `Reduction.toComp_costBoundedBy`,
   `ofFn_evalFn_toCompOn`, `eval_toOracleAdversary_width`.
5. **Beside `padFin` in `Asymptotic/Adversary.lean`** (with DL-31 and DL-32): `Transfer.padFin_nil`,
   `padFin_replicate_false`, `eq_of_ofFn_eq`, `ofFn_arrowCongr_finCongr`.
6. **A shared list module:** `Lazy.zipWith_xor_cancel_left` and `Collision.mem_keys_of_lookup_isSome`.
   For Bool vectors: `Collision.xorPerm`.
7. **Readers of `OracleSecurity` derived from published ones:** `Transfer.indCodec_eq_bitCodec` for
   the private-key `indCodec`. The public-key one is DL-32's reader request.

**Uses joining open ledger entries.** This fill adds new uses of:
- `GGMRed.ofFn_padFin_of_length` (DL-31);
- `AdaptiveCPA.ofFn_cast` (DL-32);
- `ChallengeSim.expect_sample_equiv`, `_comm` and `_prod` (DL-30);
- `BitwiseSim.expect_sample_update` and `AdaptiveCPA.expect_sample_update` (DL-33);
- `AdaptiveCPA.msgOf`, `extTape`, `ofFn_splitHalf_fst`/`_snd` and `headD_ofFn_one` (DL-32 candidates).

**Duplication inside the owned file.** My private `prf_gen_runAt`, `ofFn_prf_encryptAt` and
`ofFn_prf_decAnswer` overlap the pre-existing private CCA2 helpers `cca2Gen`, `cca2Encrypt`,
`cca2Cipher` and `cca2Decrypt` of the same file. I did not reuse those helpers, for three reasons:
- they are frozen;
- they are stated for the CCA2 adversary's shapes;
- two of them (`cca2Encrypt`, `cca2Gen`) read `PolyExpr.eval` definitionally (see §6).

A consolidation could state one set of readers for the key, encryption and decryption, and prove
both parts from it.

**Reader requests.** None blocking. The four authorized `OracleSecurity` readers were all used.

## 4. Environment, cache and bootstrap

- **Preflight** (`evidence/logs/preflight.log`): `nproc` is 4.
  - Memory: the cgroup v1 limit is the unlimited sentinel, so the headroom is `MemAvailable` = 15.22 GiB (floor 4 GiB): PASS.
  - Disk: the clone's filesystem is ext4 with 18.79 GiB free (floor 12 GiB): PASS.
- **One clone** (`/home/user/fill`): the clone and `.lake/packages` this session used for the earlier
  CPA fills on this host. The toolchain and manifest are identical. For the patch check I added a
  temporary detached `git worktree` of that clone at the base, ran no Lean in it, and removed it.
- **Cache and packages.**
  - The store held 2,372 files (118,543,444 bytes) before the fetch, written by those earlier fills; nothing was downloaded.
  - Narrowed `lake exe cache get` for the 97 roots (identical to `roots.txt`) printed "No files to download", "Decompressing 2370 file(s)" and "Completed successfully!", exit 0 (`cache-get.log`).
  - The cache probe passed (`cache-probe.log`).
  - Packages PASS before and after the fetch (`packages.log`). `doc-gen4`, `UnicodeBasic`, `BibtexQuery` and `MD4Lean` are ABSENT; the order list imports none of them.
- **Bootstrap** into a fresh olean tree `.lake/pk-oleans`:
  - the 128-module closure of `PrivateKey/OracleFromPRF`, in the order list's order (`bootstrap.log`, `bootstrap-closure.txt`);
  - then the 21 + 11 further upstream modules the helpers import, in dependency order (`bootstrap-extra*.log`, `bootstrap-extra*.txt`).

  The sweep rebuilt everything.
- **Process discipline.** One Lean process at a time; every check went through
  `scripts/lean_check_tree.sh` (`evidence/tools/chk.sh` logs start, end, status, elapsed time and
  maximum child RSS). No `lake build`. Two deviations:
  - **A hung check.** One development check of `Collision` ran past the tool runner's 10-minute foreground limit, and I stopped it. The cause was an `exact` whose type check unfolded `ovr` through `fImpl`; I replaced that step with explicit rewrites (`ovr_init`). Afterwards I wrapped some single development checks in `timeout` (15–25 min) as a guard. None timed out.
  - **An aborted sweep.** I aborted a first full sweep after 18 modules because the seal (§6) required source changes. It had just removed `Build/Loop.olean`, which I rebuilt alone before the next check (`logs/dev/sweep-aborted.log`, `logs/dev/loop-rebuild.log`). The reported sweep was then run once at the final head.

  Development logs are in `evidence/logs/dev/`.

## 5. Checks

| Check | Result | Evidence |
|---|---|---|
| Owned and helper modules | `OracleFromPRF`, `OracleFromPRF/{Games, Handler, Reduction, Transfer, Lazy, Collision}`, `OracleSecurity`: no errors, no warnings | `logs/sweep.log` |
| Sweep (final head `79f34dadd`) | `order-new.txt`, 249 modules, one `lean_check_tree.sh` call each: **249 passed, 0 failed** (01:02–01:20 UTC; peak child RSS 2,946 MiB) | `logs/sweep.log` |
| `sorry` census | **27** (base 29); removed vs base: exactly `prfFixedScheme_cpa` and `prfFixedScheme_cca1`; added: none | `logs/sorry-census.txt` |
| Axioms | `prfFixedScheme_cpa` and `prfFixedScheme_cca1`, and the untouched `prfFixedScheme_not_cca2` and `not_prfFixedScheme_cca2`: `[propext, Classical.choice, Quot.sound]` | `logs/axioms.log`, `probe/Axioms.lean` |
| Lint | `campaign_style_lint.py TCSlib/Cryptography/Encryption/PrivateKey --check8b`: 0 FAIL, 5 WARN over 16 files. The base has the same 5 WARN (10 files), all in untouched files. | `logs/lint-after.log`, `lint-before.log` |
| Patches | `git am` of `patches/` (8 patches) onto a clean base worktree gives the proof branch's tree (`5def29bb…` = `5def29bb…`, 0 diff lines) | `logs/patch-reproduce.log` |
| Preservation | `OracleSecurity.lean`: 0 removed lines. Owned file: of the base's 77 declaration and docstring blocks, all are verbatim in the head except the module docstring and the two targets' docstring-and-body blocks. The target statement lines are unchanged. | §2 |

## 6. Readings: scan, seal, controls, explicit unfolds

- **Scan** (`seal/SealScan.lean`, `logs/seal-scan.log`).
  - Roots: every declaration of the six helper modules, the owned file's 14 private `PRFStep` declarations and two targets, and the four authorized readers. That is 177 roots; 248 declarations were scanned with their auxiliaries.
  - A definition is foreign when it lives in another module. So each helper's definitions are foreign to the other helpers.
  - 116 foreign TCSlib definitions are used. 86 are regular; these are the seal candidates (`seal/candidates.txt`). 30 are reducible: abbrevs such as `bitSpec`, `bitSpecAt`, `indSpec`, `NUPPT.Coins`, `LState` and `pkOut`, and structure projections.
  - **TCSlib instances used: 0.**
- **Seal** (`seal/Seal{Games, Handler, Reduction, Transfer, Lazy, Collision, OracleFromPRF, OracleSecurity}.lean`, `logs/seal.log`).
  - Each is a verbatim copy of one of the eight changed or new files, with `attribute [local irreducible]` on every regular foreign definition its roots use (12, 24, 41, 30, 14, 24, 51 and 4 definitions, in that order). The attribute applies from the namespace's first `open` on, so each whole file is sealed.
  - **Seven compile.** `SealOracleFromPRF` fails at exactly two pre-existing, unchanged private CCA2 helpers, `cca2Encrypt` and `cca2Gen`. They read `PolyExpr.eval .var` definitionally: they identify `Fin (PolyExpr.var.eval n)` with `Fin n`.
  - **The failure predates the fill.** `SealOracleFromPRFBase.lean` is the base's copy of the owned file, sealed with the 43 candidates that exist at the base. It fails at the same two declarations and nowhere else.
  - **Every declaration of the fill is sealed.** `SealOracleFromPRFTail.lean` is the head's sealed copy with `PolyExpr.eval` alone re-opened just before `cca2Encrypt`, which comes after both targets and all of `PRFStep`. It compiles.
  - I did not change the CCA2 proofs, because the brief freezes every other declaration. A one-line fix for each would rewrite with `PolyExpr.eval_var`.
- **Findings and fixes.** The first sealed run, at commit `fa1dea766`, failed in all six helpers and in
  the owned file's new code. Several `rfl` and `exact` proofs read definitions directly: `simulate`,
  `CostBoundedBy`, `PolyExpr.eval`, `outLens`/`inLens` (through the `cast` orientation), `INDSecure`,
  `atkOf`, `addPt`, `look`, `lazyImpl`, `fImpl`, `pkHandler` (its `stateLen` and `finCall`) and
  `pkOut`. Commit `79f34dadd` routes each through published readers:
  - `simulate_pure`, `costBoundedBy_query` and `PolyExpr.eval_*`;
  - `inLens_*`/`outLens_*`, with the cast in the reader's direction;
  - `INDSecure_iff` and the new `atkOf_false`/`atkOf_true`;
  - `addPt_eq`, `look_none`, `lazyImpl_*`, and `fImpl_challenge_some` with `Option.map_some`;
  - `pkHandler_finCall`;
  - a handler-typed state `pkHState` (+ `pkHState_eq`, `pkHandler_init_hstate`) for the reduction's state abstraction;
  - `pkOut` made an `abbrev`.

  The sweep, seals, scans and controls were redone at that head.
- **Controls** (`seal/SealControls{Unsealed,Sealed}.lean`, `logs/seal-controls.log`). There are twelve readings through definition bodies: `PolyExpr.eval`, `outLens`, `CostBoundedBy`, `simulate` and `INDSecure`, and the new helpers `atkOf`, `fImpl`, `pkHandler`, `pkHState`, `look`, `addPt` and `lazyImpl`.
  - Unsealed: all pass (0 errors).
  - Sealed with the full candidate list: all twelve fail (12 errors, one per example). **12/12.**
- **Explicit-unfold scan** (`seal/RwIds*.lean`, `logs/rwids-raw.log`, `logs/rwids-files.tsv`).
  - The scan collects every identifier the added lines pass to `rw`, `rwa`, `erw`, `simp`, `simp only`, `simp_rw`, `simpa`, `dsimp` or `unfold`. Each is resolved in its file's namespace with the file's `open`s: 540 entries over the eight files.
  - **No foreign definition is passed.** The definitions passed are each file's own, plus the `↓reduceIte` simproc:
    - `Handler`: `ctP`, `pkTapes`, and the private `pkRun`, `pkFin`;
    - `Reduction`: `atkOf`, `fOuter`, `qRed`;
    - owned file: the private `prfKeyEq`, `prfNonceEq`.
  - Unresolved names are local hypotheses, private lemmas of the same file, or theorem names qualified by a local scheme (`S.inLens_zero` etc.).

## 7. Order and roots

`evidence/logs/order-new.txt` (built by `evidence/tools/order.py`) has 249 modules. It is the
issued 242-module order with the six helpers and `Games/Hopping` added. Every module of the import
closure is inserted before its first consumer, by a stable post-order walk, so every module's
TCSlib imports precede it.

The owned module moves after its new upstream dependencies, which the issued list placed after
it: `AdaptiveCPA/{Hybrid, Handler, Games}`, `BitwiseCPA/Eager`, `OracleSecurity/ChallengeSim`,
`Games/Bridges/*`, `Games/Efficiency*` and others.

The Mathlib roots of the extended order are unchanged: 97, identical to `roots.txt`
(`logs/roots-new.txt`).

**Final payload delivered — ready for maintainer review**
