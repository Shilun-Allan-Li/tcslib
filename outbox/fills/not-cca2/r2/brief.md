# Claude fill · not-cca2 continuation (`prfFixedScheme_not_cca2`, round 2)

**Issue base** `4a09f3993eb9344fc5714610e41ab141a0144db8` on `cryptography/pass-shelat-ch2-4`.
**Unit** `not-cca2`. **Worker** Claude (continuation of a Codex partial delivery). **Lean** 4.25.0
and the Mathlib revision in that commit's `lake-manifest.json`.

The round-1 brief (`brief-r1.md` in this pack) still governs the target, route, checks and
discipline; this brief states only what changes. Round 1 (Codex) delivered checkpoint 2 as an
**escalation**: the target is still admitted, and the challenge-oracle reader at the
specification's widths is missing. Its payload is on the exchange at `inbox/fills/not-cca2/`
(worker head `9f057f65bbb1b1795dd30a179c47b5b670a01452`, not published; two patches).

## Start from the round-1 work

- Fetch `cryptography/pass-shelat-ch2-4` and start a local branch `fill/not-cca2` at the issue base.
  Apply `inbox/fills/not-cca2/patches/0001-*.patch` and `0002-*.patch` with `git am`. Check that the
  result equals `inbox/fills/not-cca2/src/` byte for byte. Record this in `REPORT.md`.
- Read `inbox/fills/not-cca2/REPORT.md` and `evidence/READER-REQUEST.md`. Reuse what is checked
  (the adversary `cca2Next`/`cca2Adversary`, the encryption frontier, `prfScheme_dec`); you may
  restructure or replace any of the private helpers. Treat that payload as working material.

## Resolution of the escalation: authorized readers

The private-key oracle file lacks the readers at the specification's types that the public-key
file already has (`Encryption/PublicKey/OracleSecurity.lean`: `indSpec_dom`, `indSpec_rng`,
`indSpec_decDom`, `indSpec_challengeDom`, `indSpec_challengeRng`, `indImpl_dec_onSpec`,
`indImpl_challenge_none_onSpec`, `indImpl_challenge_repeat_onSpec`). You may add their
private-key counterparts to **`TCSlib/Cryptography/Encryption/PrivateKey/OracleSecurity.lean`**,
beside the existing `indImpl_*` readers, in the same form:

- width readers for the three oracles of `FixedLengthScheme.indSpec n` (index 0 `Enc`, 1 `Dec`,
  2 `Challenge`): `(S.indSpec n).dom i = …` and `(S.indSpec n).rng i = …`, proved through
  `indSpec_eq`, `bitSpec`'s published readers and `inLens_*`/`outLens_*`;
- `indImpl_enc_onSpec`, `indImpl_dec_onSpec`, `indImpl_challenge_none_onSpec`,
  `indImpl_challenge_repeat_onSpec`: the existing equations restated for an argument of the
  specification's type, with the width conversions as explicit `cast`s along those readers, proved
  `by simpa only [cast_eq] using S.indImpl_… …` (or `rfl`).

Add only the readers you use (the challenge pair is required; add the `Dec` ones if the CCA2 step
needs them). Each is public, not `@[simp]`, with a docstring stating its formula. Change nothing
else in that file. The round-1 reader proposal `indImpl_challenge_none_cast` is an acceptable
alternative form if the `_onSpec` form does not elaborate under seal; say which you used and why.

## Scope (replaces the round-1 scope's file list)

- Owned: `PrivateKey/OracleFromPRF.lean` (the target body and private helpers, below 1000 lines).
- Authorized additions: `PrivateKey/FromPRF.lean`, exactly `prfScheme_dec` (as in round 1);
  `PrivateKey/OracleSecurity.lean`, exactly the readers above.
- Everything else in round 1's scope and discipline holds: the target statement and every other
  declaration are frozen; published readers only for other files' definitions (the new
  `OracleSecurity` readers are now published readers for `OracleFromPRF`); escalate with the exact
  failing obligation if blocked.

## Delivery (Claude)

Deliver every checkpoint and the final payload under `inbox/fills/not-cca2/` on
`exchange/pass-shelat-ch5-8`, **replacing** the round-1 payload files there (the maintainer has
archived the originals under `archive/fills/not-cca2/`). Include `REPORT.md`, `patches/` (the whole
`git format-patch` series from the issue base, round-1 patches included), `src/` (all changed files)
and `evidence/`. Commit messages `fill not-cca2: r2 checkpoint N` and `fill not-cca2: r2 final`.
Pull with rebase before pushing; push only that path; never force-push. Keep the proof branch
local. The maintainer reviews the delivery for a PR that Seyoon approves.

## Checks

As round 1, with the sweep over the full supplied `order.txt` (232 modules; it already contains
everything downstream of `PrivateKey/OracleSecurity`). Expected admissions: `base-sorries.txt`
minus `prfFixedScheme_not_cca2` (32). Axioms of `prfFixedScheme_not_cca2` and
`not_prfFixedScheme_cca2`: only `propext`, `Classical.choice`, `Quot.sound`. Seal the touched
declarations of all three changed files with controls, run the explicit-unfold scan, and run
`python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography/Encryption/PrivateKey --check8b`.

**Ready to dispatch**
