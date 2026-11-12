# Fill report · `pk-cpa-cca1` · checkpoint 1

**Worker** Claude (external fill, exchange push route). **Issue base**
`8c3afbff69ad1273446750f47c05d424ab13ebe2` on `cryptography/pass-shelat-ch2-4`. **Proof branch**
local `fill/pk-cpa-cca1` (4 commits over the base; never pushed). **Pack** read at exchange
`db04fd415`; `sha256sum -c SHA256SUMS` in `outbox/fills/pk-cpa-cca1/`: all 7 OK
(`evidence/logs/pack-sha256.log`). Source hashes: `sha256sum -c SOURCE-SHA256SUMS` at the base,
242/242 OK (`evidence/logs/source-sha256.log`).

## Status: step 1 done; targets still admitted

**Step 1 (PRF → random function) is proved.** For an adversary `A`, a budget `q`, the attack
(`atkOf true = CCA1`, `atkOf false = CPA`) and a bit `b`:

- `PRFGame.exists_prfReduction` (`OracleFromPRF/Reduction.lean`): a next-query machine `D` (T4 of
  T2's machine for the handler `pkHandler`, through the input-free companion of `A`) such that at
  every `n` and for **every** `f : {0,1}^n → {0,1}^n`, `D` with budget `qRed q` accepts against
  `f` with exactly the probability that `A` outputs `1` in the IND experiment with `f` in place
  of `f_k` (`PRFGame.fImpl`).
- `accept_prf_indGame` (owned, private): for `n > 0`, `Pr[IND_b = 1]` is that experiment averaged
  over a uniform key with `f = F_k`.
- `prfAdv_prfReduction` (owned, private): `prfAdv (F n) D = |Pr[IND_b = 1] − 𝔼_R Pr[A → 1 | f = R]|`,
  so the game with `f_k` equals `D` against the keyed ensemble and the game with a random function
  equals `D` against the random ensemble, as the brief asks.

Route notes. The reduction is one handler per `b` (the bit hard-wired, not in the seed), so the
final bound will be `prfAdv(D₀) + prfAdv(D₁) + (RF-game gap)`. The handler's seed is `q(n)` nonce
tapes; it counts fresh nonces in its state and records the challenge. Its run, composed with the
outer oracle `f`, is the experiment with the tapes in advance (`eImpl`) while fewer than `q(n)`
tapes are used, which the budget guarantees (`simulate_eq_of_abs_bounded`); uniform tapes give
fresh nonces (`expect_eImpl`). At `n = 0` the final bound will use `advantage ≤ 1`.

Next: step 2 (lazy random function, identical until bad, the collision bound) and step 3.

## Files so far

- `PrivateKey/OracleSecurity.lean`: the four authorized readers `indSpec_encDom`,
  `indSpec_encRng`, `indImpl_enc_onSpec`, `indImpl_challenge_repeat_onSpec` (public, not simp,
  formula docstrings), nothing else changed.
- New helpers under `PrivateKey/OracleFromPRF/`: `Games.lean` (327 lines), `Handler.lean` (711),
  `Reduction.lean` (361), `Transfer.lean` (≈190).
- Owned `PrivateKey/OracleFromPRF.lean`: 579 → 784 lines (step-1 section before the targets).

## Environment

- Preflight (`evidence/logs/preflight.log`): `nproc` 4; cgroup v1 limit is the unlimited
  sentinel, headroom = `MemAvailable` = 15.22 GiB (floor 4 GiB): PASS; clone filesystem ext4,
  18.79 GiB free (floor 12 GiB): PASS.
- One clone (`/home/user/fill`), the same clone and `.lake/packages` this session used for the
  earlier CPA fills on this host; toolchain and manifest identical. Cache store 2,372 files /
  118,543,444 bytes before the fetch, written by those earlier fills. Narrowed
  `lake exe cache get` for the 97 roots (identical to `roots.txt`): "No files to download",
  "Decompressing 2370 file(s)", exit 0. Packages PASS; ABSENT `doc-gen4`, `UnicodeBasic`,
  `BibtexQuery`, `MD4Lean`. Cache probe passed.
- Bootstrap into a fresh tree `.lake/pk-oleans`: the 128-module closure of
  `PrivateKey/OracleFromPRF` (all passed), then the 21 + 11 further upstream modules the helpers
  import, in dependency order (`bootstrap-extra*.log`). `Games/Hopping` is not in the issued order
  list; it will be inserted (its imports and roots are already covered).

**Checkpoint 1 — step 1 proved; steps 2 and 3 in progress**
