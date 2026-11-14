# Fill cca2-ett — checkpoint 1 (step 1: the tag key becomes a random function)

**Unit** `cca2-ett` · **Worker** Claude · **Issue base** `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9`
(`cryptography/pass-shelat-ch2-4`, the merge of #299) · **Proof branch** `fill/cca2-ett` (local),
checkpoint commit `9015e943d` · **Lean** 4.25.0, Mathlib at the base's manifest.

**Target status at this checkpoint:** `Composability.ccaScheme_cca2` is still `sorry`. Step 1 of the
route is proved (no `sorry`); steps 2 and 3 are in progress.

## 1. Environment (addendum v1)

- **Preflight** (`evidence/logs/preflight.log`): 4 CPUs; cgroup v1 limit unlimited, so the headroom is
  `MemAvailable` = 16442974208 B = 15.31 GiB; clone filesystem ext4 with 13927960576 B = 12.97 GiB
  free (floor 12 GiB): `PREFLIGHT PASS`. Two worktrees of finished jobs of this session
  (`/workspace/dlc-base`, `/workspace/base-wt`) were removed before the preflight to get above the
  floor; no dependency tree was copied or moved.
- **Cache**: the narrowed `lake exe cache get` for the 98 roots of `roots.txt`
  (`evidence/logs/mathlib-roots.txt` is the same list) printed "No files to download" and
  "Decompressing 2370" and exited 0 (`cache-get.log`). The cache tool's store
  (`~/.cache/mathlib`, `cache-store.log`) already held 2402 archives, left by this session's earlier
  fills on this host; none was downloaded for this fill. No zero-size olean; the probe importing
  `Mathlib.Algebra.BigOperators.Field` elaborates (`cache-probe.log`, `probes/CacheProbe.lean`).
- **Packages** (`packages-check.log`, last line): `RESULT: all present packages match the manifest`
  (`doc-gen4`, `UnicodeBasic`, `BibtexQuery`, `MD4Lean` ABSENT; no module of the order imports them).
- **Bootstrap** (`bootstrap.log`, one module per `scripts/lean_check_tree.sh` call through
  `tools/check.sh`): 264/264 modules of `order.txt`, status 0. The host was restarted twice during
  the bootstrap (a VM restore: uptime 0, `dmesg` "virtual machine fork"); each restart terminated
  the background sweep mid-module (no Lean failure, no OOM event). Both are logged
  (`resume-1.log`, `resume-2.log`) and the sweep resumed at the interrupted module, which was
  re-checked from scratch. Sorry census of the bootstrap = `base-sorries.txt` (24 declarations in 10
  modules; `census-bootstrap.txt`, `census-bootstrap-vs-base.diff`).

## 2. Changed and new files (this checkpoint)

| File | Lines | Role |
|---|---|---|
| `PrivateKey/EncryptThenTag.lean` (owned) | 617 | readers of `ccaScheme` for the transfer; step 1 (`cca_tag_step`); target still `sorry` |
| `EncryptThenTag/Tools.lean` | 269 | generic simulation tools (promotion candidates) |
| `EncryptThenTag/Machines.lean` | 350 | budget cap, parameter halving, width transport (promotion candidates) |
| `EncryptThenTag/Games.lean` | 428 | the CCA2 experiment with a pad function `f` and a tag function `g` |
| `EncryptThenTag/Handler.lean` | 831 | the T2 handler of the tag-key PRF reduction |
| `EncryptThenTag/Reduction.lean` | 386 | the reduction at parameter `2n`; step 1 |
| `EncryptThenTag/Transfer.lean` | 218 | the CCA2 experiment of a scheme as the experiment with `f` and `g` |

Import graph (acyclic; checked by the module checks in the supplied order with the helpers inserted
before the owned file, `evidence/logs/order-with-helpers.txt`): Tools ← Machines; Tools ← Games ←
Handler ← Reduction (also ← Machines, ← `OracleFromPRF.Reduction`); Games ← Transfer; the owned file
imports all six (the style lint treats it as their facade).

## 3. Step 1, as proved

`ETTGame.exists_tagStep` (helper) and `cca_tag_step` (owned file): for a machine adversary `A` with
budget `q` and a bit `b` there is a next-query machine `D` with, at every `n`,

`|Pr[IND_b(A, q(n), n) = 1] − 𝔼_{k₁} 𝔼_R ettAcc(f_{k₁}, R, rej = false, b)| = prfAdv(F_{2n}, D^{q(2n)}_{2n})`,

where `R` ranges over all functions on `2n` bits. With `PRF.negligible_prfAdv` and
`Negligible.comp_of_le` (`φ n = 2n`) this is negligible in `n`; the final combination does that.

**The reduction** (`ETTGame.exists_tagReduction`): the handler `dHandler` holds `k₁` and `q(2n)`
nonce tapes in its seed and the query count and the challenge record in its state; `Enc′` and a
first challenge ask the oracle at `r ‖ c₁`, `Dec′` refuses the record, asks the oracle at the pair of
a well-formed word and compares with the tag. T2 is applied with the budget `q(2n)` to the
input-free companion of a **capped** adversary, then T4 at length `2n`, then the parameter is halved.

**Why the cap and the halving.** `PRF.negligible_prfAdv` bounds machines run at parameter `m` with
an `m`-bit oracle and budget `Q(m)` for a polynomial `Q`. The handler runs the adversary at `n` with
a `2n`-bit oracle. So the distinguisher at `m = 2n` must run T2's machine at `m / 2`
(`exists_halfMachine`, from `NUPPT.exists_reparam_advice`), and T2's budget must be a polynomial in
`2n`: `q(2n)`. The adversary's budget is `q(n)`; `exists_capMachine` gives a machine that, at every
budget `K ≥ q(n)`, computes what `A` computes with budget `q(n)` (after `q(n)` log entries a query
word becomes the empty word, which every bit codec reads as the timeout output). No statement is
weakened: the game is still `A` at budget `q(n)`.

**Transfer** (`ETTGame.accept_indGame_eq`, `accept_cca_indGame`): the real oracles have, call by
call, the laws of `ettImpl (F n k₁) (F (2n) k₂) false b`, through the record
(`expect_simulate_abs`). The readers of `ccaScheme` used: `ccaScheme_gen/enc/dec/ctLen`,
`runAt_ccaGen`, `runAt_ccaEnc`, `ccaDecFun_eq`, `ccaDecOK_eq` and the `NUPPT` run readers. Every
decryption answer is matched, including malformed words and, at `n = 0`, the malformed four-bit
words that decrypt to the empty message: the experiment parses with the same total projections
(`wR`, `wC`, `wT`) and guards (`validW`).

## 4. Remaining route (steps 2 and 3)

- **Step 2** (`rej = false` vs `rej = true`, random `R`): identical until the first non-refused,
  valid `Dec′` query with a pair outside the `Enc′` list (`hitW`, `ettBad`); the probability of the
  flag is bounded by `q(n) / 2^{2n}` by induction over the computation with `R` overridden on the
  revealed pairs (`ovr`, `expect_sample_ovr`): a fresh guess hits `R` at an unrevealed point with
  probability `2^{-2n}`; canonical parsing (`eq_ctW_of_wfW`) excludes the challenge pair for
  `n > 0`.
- **Step 3**: the rejecting experiment with `R` averaged equals a CPA experiment of a T2 machine
  against the §3.9 scheme, with the tags sampled lazily from seed tapes and the decryption answers
  read from a table in the handler's state (GGM's public table lookup `GGMRed.lookup`,
  `lookup_tblOf`); then `prfFixedScheme_cpa` (or its public ingredients `exists_prfReduction` and
  `abs_expect_fImpl_sub_le`).

## 5. New declarations (public; all helpers in namespace `TCSlib.Cryptography.Composability.ETTGame`)

- Tools: `expect_simulate_abs`, `freshImpl`, `freshImpl_apply`, `tapeImpl`, `tapeImpl_apply`,
  `simulate_tapeImpl_congr`, `expect_simulate_tapeImpl`, `ovr`, `ovr_nil`, `ovr_cons`,
  `ovr_of_not_mem`, `ovr_of_mem`, `ovr_update`, `expect_sample_ovr`.
- Machines: `logCount`, `logCount_eq`, `polyTimeComputable_logCount`, `length_logCount_encodeLog`,
  `buildComp_cap`, `capRaw`, `capRaw_eq`, `polyTimeComputable_capRaw`, `exists_capMachine`,
  `exists_halfMachine`, `eval_toOracleAdversary_len`.
- Games: `pairV`, `tagL`, `ctW`, `maskL`, `encW`, `wR`, `wC`, `wT`, `wfW`, `validW`, `decL`, `pairW`
  (each with its `_eq`), `wR_ctW`, `wC_ctW`, `wT_ctW`, `length_maskL`, `length_encW`, `eq_ctW_of_wfW`,
  `wfW_encW`, `eq_of_pairV_eq`, `St` (abbrev, `St_eq`), `refW` (`refW_none`, `refW_some`),
  `decAnsW`, `hitW` (with `_eq`), `decAnsW_agree`, `ettStep` (`ettStep_enc`, `_dec`,
  `_challenge_some`, `_challenge_none`), `ettImpl` (`ettImpl_apply`, `ettImpl_eq_freshImpl`),
  `hitQ` (`hitQ_zero/one/two`), `ettBad` (`ettBad_apply`), `ettTape` (`ettTape_apply`),
  `expect_ettTape`, `expect_ettImpl_transport`, `ettAcc` (`ettAcc_eq`, `ettAcc_nonneg`,
  `ettAcc_le_one`).
- Handler: `ettCt`, `ettDin`, `ettDout`, `tagLen`, `tagOut` (abbrev, `tagOut_eq`), `dStLen`,
  `dSeedLen`, `recBits`, `dState`, `dSeed`, `dTape`, `dHandler` (simps fields), `dHState`, `dHSeed`
  (each with `_eq`/readers), `ofFn_dSeed`, `ofFn_dHSeed`, `ofFn_dHState`, `dHandler_init_hstate`,
  `dHandler_advInput`, `dHandler_finish`, `dHandler_impl_enc`, `dHandler_impl_dec_ref`,
  `dHandler_impl_dec_wf`, `dHandler_impl_dec_nwf`, `dHandler_impl_challenge_some`,
  `dHandler_impl_challenge_none`.
- Reduction: `gOuter` (`gOuter_apply`), `dAbs` (`dAbs_eq`), `dTapes` (`dTapes_eq`, `dTapes_of_lt`),
  `comp_dAbs`, `eval_subst_tagLen`, `expect_ettImpl_outLen`, `exists_tagReduction`,
  `prfAdv_eq_expect`, `exists_tagStep`.
- Transfer: `stRec` (`stRec_eq`), `expect_indImpl_ettImpl`, `accept_indGame_eq`.
- Owned file (all `private`): `cca_ctLen_eval`, `cca_inLens`, `cca_outLens`, `cca_gen_coins`,
  `cca_enc_coins`, `cca_gen_len`, `ccaKeyEq`, `ofFn_ccaKeyEq`, `cca_gen_runAt`, `ccaNonceEq`,
  `ofFn_ccaNonceEq`, `ofFn_cca_encryptAt`, `ofFn_cca_decAnswer`, `accept_cca_indGame`,
  `cca_tag_step`.

No `@[simp]` was added. The one new public `abbrev`s (`St`, `tagOut`) have `St_eq`, `tagOut_eq`.

## 6. Promotion requests, reader requests, PRFGame overlap

**Promotion list** (generic facts placed in the helpers; searches in
`evidence/logs/checkpoint1-searches.log`):
- `expect_simulate_abs` — `Games.simulate_eq_of_abs(_bounded)` requires equal computations
  (deterministic calls); `ProbComp.expect_simulate_congr` requires one state type. This is the law
  version through an abstraction, with a budget.
- `freshImpl`, `tapeImpl`, `expect_simulate_tapeImpl` — the generic form of `PRFGame.expect_eImpl`
  (which is specific to `eImpl`).
- `ovr`, `expect_sample_ovr` — a function overridden by a table (PRFGame's `ovr` is specific to its
  lazy state).
- `logCount`, `length_logCount_encodeLog`, `buildComp_cap`, `exists_capMachine` — the entry
  count of an encoded log and a budget cap for machines. The non-malleability modules have
  `logEmit` / `length_logEmit_cntRead`, but they come after the owned file in the order and are
  specific to their emission; `Games.buildComp_budget_eq` needs the larger-budget run to be already
  bounded, which T2's machines do not publish.
- `exists_halfMachine` — the oracle-adversary form of `EnsembleLemmas.acceptProb_reparam_advice`.
- `eval_toOracleAdversary_len` — `PRFGame.eval_toOracleAdversary_width` fixes the widths to the
  parameter; this is the width-changing form (it is not a copy).

**Reader requests:** none.

**PRFGame overlap:**
- `prfAdv_prfReduction` (private in `OracleFromPRF.lean`): re-derived in general form as
  `ETTGame.prfAdv_eq_expect` (the PRF advantage of any oracle adversary as the gap of two
  expectations), from the published readers `prfAdv_def`, `distAdv_def`, `Bridge.acceptProb_eq`,
  `Bridge.acceptGame_eq`, `accept_eq`, `oracleDist_apply`, `randomFunction_apply`.

## 7. Evidence at this checkpoint (`evidence/`, manifest `evidence/SHA256SUMS`)

- `logs/`: `preflight.log`, `mathlib-roots.txt`, `cache-store.log`, `source-sha256.log`,
  `cache-get.log`, `packages-check.log`, `cache-probe.log`, `order.txt`, `order-with-helpers.txt`,
  `bootstrap.log`, `resume-1.log`, `resume-2.log`, `census-bootstrap.txt`,
  `census-bootstrap-vs-base.diff`, `checkpoint1-checks.log` (fresh checks of the six helpers and the
  owned module, in order; status 0; the owned module's one `sorry` warning is the target),
  `checkpoint1-census.txt`, `checkpoint1-axioms.log` (`propext`, `Classical.choice`, `Quot.sound`
  for the step-1 results and the generic tools), `checkpoint1-lint.log` (0 FAIL; the 5 WARN are in
  files not touched), `checkpoint1-searches.log`.
- `probes/`: `CacheProbe.lean`, `AxiomsCP1.lean`.
- `tools/`: `check.sh`, `sweep_chunk.sh`, `census.py`, `cmpcensus.sh`, `mk.py`, `dev.sh`,
  `pkgcheck.py`, `payload.sh`.

The full sweep, the census against `base-sorries.txt`, the axioms of every stored constant, the
seals A/B with controls and the explicit-unfold scan are for the final delivery.
