# not-cca2 — round 2, final delivery (Claude)

**Status: `Composability.prfFixedScheme_not_cca2` is proved; `not_prfFixedScheme_cca2` now holds
without admissions.** Both print exactly `[propext, Classical.choice, Quot.sound]`. The
232-module sweep passes with 32 admissions: `base-sorries.txt` minus the target.

## Provenance

- Issue base `4a09f3993eb9344fc5714610e41ab141a0144db8` on `cryptography/pass-shelat-ch2-4`.
  Exchange pin `409d4b0dd7485e6173504b2a2a850f1cb9214d0e`. The local branch `fill/not-cca2`, head
  `1e61d862f90fbfb3c25f076a277c400ba066a020`, is in a separate worktree and was never pushed.
  Lean 4.25.0, Mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
- Pack: `sha256sum -c SHA256SUMS` in `outbox/fills/not-cca2/r2` gives 8/8 OK. All 232 issue-base
  sources match `SOURCE-SHA256SUMS`.
- **Round-1 start.** I applied round-1 patches `0001` and `0002` with `git am` at the base. The
  resulting `FromPRF.lean` (`a79e5b37…`) and `OracleFromPRF.lean` (`45cded6f…`) equal the round-1
  `src/` byte for byte (`evidence/logs/round1-apply.log`). Their commits carry a new committer
  but keep the original author and message.
- `patches/` holds the whole series from the base: `0001`, `0002` (round 1) and `0003` (round 2).
  Applying it with `git am` at the base reproduces `src/` (`evidence/logs/patch-replay-final.log`).
  Checkpoint 1 of round 2 is exchange commit `10d11e5a0`. The Lean sources have not changed since.

## Changed files

| File | Change |
|---|---|
| `PrivateKey/FromPRF.lean` | Round 1's authorized `prfScheme_dec` only (unchanged in round 2). |
| `PrivateKey/OracleSecurity.lean` | The authorized readers below; no other change (+46 lines). |
| `PrivateKey/OracleFromPRF.lean` | Target body; four new private helpers; the target's sketch (597 lines). |

### Readers added to `OracleSecurity.lean` (public, not `@[simp]`, docstrings with formulas)

They sit in one block after `indImpl_challenge_repeat`, beside the existing `indImpl_*` readers:

- `indSpec_decDom n : (S.indSpec n).dom 1 = (Fin (S.ctLen.eval n) → Bool)`
- `indSpec_decRng n : (S.indSpec n).rng 1 = (Fin (n + 1) → Bool)`
- `indSpec_challengeDom n : (S.indSpec n).dom 2 = (Fin (n + n) → Bool)`
- `indSpec_challengeRng n : (S.indSpec n).rng 2 = (Fin (S.ctLen.eval n) → Bool)`

  Each is proved by `rw [S.indSpec_eq, bitSpec_dom/rng, S.inLens_*/outLens_*]`.
- `indImpl_dec_onSpec`: the `indImpl_dec` equation for `c : (S.indSpec n).dom 1`, with the query
  read as `cast (S.indSpec_decDom n) c` and the valid answer as
  `cast (S.indSpec_decRng n).symm (decAnswer …)`.
- `indImpl_challenge_none_onSpec`: the `indImpl_challenge_none` equation for
  `mm : (S.indSpec n).dom 2`, with halves `splitHalf (cast (S.indSpec_challengeDom n) mm)` and the
  answer `cast (S.indSpec_challengeRng n).symm c`.

  Both are proved `by simpa only [cast_eq] using S.indImpl_…`.

I used the `_onSpec` form, not the round-1 alternative `indImpl_challenge_none_cast`. It
elaborates, and consumers pass under the seal (below). Unlike the public-key file's
`indImpl_dec_onSpec`, the private-key version also casts the **answer**. Without that cast, a sealed
consumer would have to identify `Fin (n + 1)` with `Fin (S.outLens n 1)` by unfolding.

**Readers deliberately not added**, because the proof does not use them: `indImpl_enc_onSpec`
(`Enc` is never queried) and `indImpl_challenge_repeat_onSpec` (the challenge is asked once). I
read "the challenge pair is required" as the challenge width readers
(`indSpec_challengeDom`/`_challengeRng`) with `indImpl_challenge_none_onSpec`. If the maintainer
meant the `none`/`repeat` equation pair, `repeat_onSpec` is a two-line addition in the same form.
I left it out to follow "add only the readers you use". **Please confirm at review.**

### New private helpers in `OracleFromPRF.lean`

Round 1's 28 helpers are reused unchanged. The new ones:

- `cca2Decrypt`: decrypting `⟨x, v⟩` of `n`-bit words under `k` decodes to `some (v + F n k x)`,
  through `prfFixedScheme_dec`, `prfScheme_dec`, `runAt_prfDec`, `hFE`, `zipWith_xor_ofFn_add`
  and `decodeFin_ofFn`.
- `cca2OfFn_cast`: `List.ofFn (cast h f) = List.ofFn f` for `h` from a width equality `a = b`
  (proved by `subst`). Every width conversion goes through this lemma and the published
  `inLens_*`/`outLens_*` equations.
- `cca2LastBit`: for `n > 0`, `(List.ofFn (Fin.cons true (cca2FlipBits fun _ => b))).getLastD false
  = !b`.
- `cca2Run`, the main simulation. It is stated for **any** `FixedLengthScheme` with nonempty
  ciphertexts, given that each decryption of a flipped challenge `Enc_k(b^n)` yields a message
  `v` whose answer `⟨1, v⟩` ends in `!b`. Under that hypothesis, `cca2Adversary` with budget `2`
  outputs `b` with probability `1`. The proof follows the three activations:
  - `toComp_eq` and `buildComp_succ_of_query`, twice, then `buildComp_zero_of_ret`;
  - `simulate_query`/`simulate_pure`, with `indCodec_decodeMove`/`_encodeEntry`,
    `encodeLog_cons/_nil`, `decodeBitMove_query/_ret` and the round-1 `cca2Adversary_run/_one/_two`;
  - the two new `_onSpec` readers, `decOpen_cca2`, `cca2Alter_ne`, `decAnswer_some`;
  - and `prob_bind`/`expect_const`/`prob_pure`.
- **Target body.** It uses `A = cca2Adversary` and `q = .const 2`. For each `b`, `accept` equals
  `if b then 1 else 0`. That comes from `indGame_eq`, `prob_bind`, `cca2Gen`, `cca2Run`,
  `cca2Cipher`, `cca2Decrypt` and `cca2FlipBits_unmask`. The advantage is then `|0 − 1| = 1`.

**Sketch edits.** Two places in the target's docstring, to describe the delivered proof. Step 1
adds "its query budget is `2`, so the third activation's output is read". Step 3 now reads "for
every key and all coins, `A` outputs `b` (`cca2Run`): `IND_b` accepts with probability `1` if
`b = 1` and `0` if `b = 0`". The statement, statement prose, all other declarations (including the
admitted `prfFixedScheme_cpa`/`_cca1`) and the global simp attributes are unchanged.

**One stale sentence, left for the maintainer.** The module docstring's "Main results" still
describes `prfFixedScheme_not_cca2` as "(Claim 169.a, stated; a `sorry` under its sketch)". The
brief authorizes edits only to the target's sketch, so I left that sentence unchanged. It should
now read "proved".

## Checks

- **Bootstrap.** The 129-module closure of `OracleFromPRF` (`evidence/bootstrap-order.txt`,
  identical to round 1's) ran serially. Modules 1–128 passed, the new `OracleSecurity` readers
  included. Module 129 (`OracleFromPRF`) failed on my first draft; the logged error is
  `Unknown identifier prob`. The fixed file was then rechecked on its own (logs under
  `evidence/logs/`; `bootstrap.tsv` records the failing first run as it happened).
- **Sweep.** The full supplied `order.txt` (232 modules) ran on the final source, in order, one
  module per `scripts/lean_check_tree.sh` call, one Lean process at a time: **232/232 pass**
  (`evidence/logs/sweep.tsv`, per-module logs in `logs/sweep/`). It took 974 s in total; the
  maximum child RSS was 3,134,384 KiB. `FromPRF` (147) and `OracleFromPRF` (162) are rechecked
  within it.
- **Admissions** (`evidence/logs/sweep-admissions.log`): 33 at the base, **32 now**. Every module
  is the same except `OracleFromPRF`, where 3 became 2 (only `prfFixedScheme_not_cca2` removed).
  The changed files raise no other warnings, except one pre-existing unused-simp-argument linter
  note at `FromPRF.lean:128` (`polyTimeComputable_prfDecFun`, untouched).
- **Axioms** (`evidence/logs/axioms-final.log`): `prfFixedScheme_not_cca2`,
  `not_prfFixedScheme_cca2`, `prfScheme_dec` and all six new readers depend on
  `[propext, Classical.choice, Quot.sound]`.
- **Reference census** (`evidence/probes/Refs.lean`, `evidence/logs/refs-final.log`). It
  enumerates the elaborated types and values of the 61 touched declarations of the three files:
  the 7 readers, and every `cca2` declaration of `OracleFromPRF` with generated matchers and
  auxiliaries. It lists each foreign TCSlib constant with its home module and its
  instance/projection status. `evidence/seal-candidates.json` gives each candidate's
  disposition. Reducible abbreviations and primitive projections are recorded but not sealed. So
  is `PolyExpr.eval`, which the brief exempts as notation. No foreign instance occurs; the
  instance-aware alias path of the harness is present but unused.
- **Seal** (`evidence/tools/make_seal.py`, `evidence/probes/Seal*.lean`). Each changed file's body
  is compiled in a probe module with every semireducible foreign candidate made
  `local irreducible`. For `OracleSecurity` and `FromPRF` the seal is applied in a section
  around the touched block. For `OracleFromPRF` it covers the whole body. The three seals are:
  - `OracleFromPRF`: 43 definitions, among them `inLens`, `outLens`, `indImpl`, `indCodec`,
    `bitCodec`, `decodeBitMove`, `buildComp`, `simulate`, `encodeLog`, `prob`/`expect`/`sample`,
    `NUPPT.toComp/runAt/ofPolyTimeUniform`, `decodeFin`, `padFin`, `pairEncode`, `prfScheme`,
    `prfDecFun`, `prfDecWF`;
  - `OracleSecurity`: 7;
  - `FromPRF`: 3.

  **All three pass**, with only the two pre-existing admissions in `OracleFromPRF`
  (`logs/seal-*.log`, `logs/seal-summary.log`).
- **Controls.** Each control passes before sealing and fails after it at the intended `rfl`:
  - `S.inLens n 2 = n + n` (`OracleFromPRF`; this is the round-1 escalation's identification);
  - `zeroBits d j = false` (`OracleSecurity`);
  - `pairEncode x a = …` (`FromPRF`).
- **Development note.** While developing, I prepended a temporary seal of the same kind to the
  owned file, then removed it before committing. That run found the problem with
  `simp only [cast_eq]`: unsealed, it strips the width casts by unfolding `outLens`. The final
  proof only removes a cast through `cast_cast` + `cast_eq` on explicit double casts (`hxc`,
  `hcc`), so it elaborates the same way with and without the seal.
- **Explicit-unfold scan** (`evidence/tools/unfold_scan.py`, `logs/explicit-unfold-scan.log`):
  PASS. The only `unfold` is of the owned `cca2Adversary`. No foreign definition name appears in
  any `rw`/`simp` list of the added lines.
- **Lint.** `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography/Encryption/PrivateKey
  --check8b` gives **0 FAIL, 5 WARN over 10 files**. The warnings are the same pre-existing
  public-def notes as round 1; none concerns a new declaration. `git diff --check` is clean, and
  no added line exceeds 100 characters.

## Environment, cache, resources

- **Preflight** (`logs/preflight.log`):
  - `nproc` 4;
  - no cgroup memory files, so the headroom is `MemAvailable` = 16,171,827,200 B (floor 4 GiB:
    PASS);
  - the clone, toolchain, payload and `/tmp` are on ext4 `/dev/vda`, with 22,684,639,232 B free
    when logged (floor 12 GiB: PASS). The figure was 27,685,502,976 B before the toolchain
    download; the logged preflight was written after it.

  No tmpfs was used.
- **Toolchain.** The official `lean-4.25.0-linux.tar.zst` was downloaded by this session, SHA-256
  `97bee7bda676ca54f4b1cebe323242a08323d75134fecd1ba31cee4db66abb8a` (equal to round 1's), and
  extracted with `TAR_OPTIONS=--no-same-owner`. `zstd` was installed from the package manager to
  extract it.
- **Cache.** The archive store `~/.cache/mathlib` did not exist beforehand (0 files, 0 bytes).
  The narrowed `lake exe cache get` covered the 98 roots, identical to `roots.txt`. It attempted
  2,381 downloads, decompressed 2,381 files and exited 0 with no failed download. No cleaned retry
  was needed.
- **Packages.** Every package present matches the manifest's URL and revision, and the order
  imports no absent package: **PASS (all present packages match)**. `doc-gen4`, `UnicodeBasic`,
  `BibtexQuery` and `MD4Lean` are ABSENT. No zero-size `.olean` (2,390 present). The
  Mathlib-root import probe passed.
- **Process discipline.** Every check, probe, bootstrap and sweep step ran through
  `scripts/lean_check_tree.sh`, one Lean process at a time, wrapped by `evidence/tools/time_check.py`
  for UTC start/end, elapsed time and maximum child RSS (`/usr/bin/time` is absent). No
  `lake build` and no unfiltered cache get. All Python ran as `python3 -I`. The peak was
  3,134,384 KiB RSS, with no OOM or resource symptom.

## Payload

- `REPORT.md`; `patches/0001-0003`; `src/` (the three changed files);
- `evidence/` with:
  - `inputs/`: the r2 pack, exchange README and `policy.md`;
  - `logs/`;
  - `probes/`: cache probe, axioms, census, seals, controls;
  - `tools/`;
  - `seal-candidates.json`, `bootstrap-order.txt`, `delivery.json`;
- `SHA256SUMS` over the payload.
