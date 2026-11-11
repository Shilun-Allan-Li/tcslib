# not-cca2 — round 2, checkpoint 1 (Claude)

**Status: the target `Composability.prfFixedScheme_not_cca2` is proved.** This checkpoint
carries the proof and the authorized readers. The full 232-module sweep, the instance-aware
seal with controls, the explicit-unfold scan and the style lint follow in the final delivery.

- Issue base `4a09f3993eb9344fc5714610e41ab141a0144db8` (`cryptography/pass-shelat-ch2-4`);
  exchange pin `409d4b0dd7485e6173504b2a2a850f1cb9214d0e`. Local branch `fill/not-cca2`,
  separate checkout, never pushed. Lean 4.25.0; Mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
- Pack: `sha256sum -c SHA256SUMS` in `outbox/fills/not-cca2/r2`: 8/8 OK. Issue-base sources:
  232/232 match `SOURCE-SHA256SUMS`.
- Round-1 patches `0001`, `0002` applied with `git am` at the base; the result equals the round-1
  `src/` byte for byte (`evidence/logs/round1-apply.log`).

## Changes in this checkpoint (patch `0003`)

- `PrivateKey/OracleSecurity.lean` (authorized readers, public, not `@[simp]`, docstrings with
  formulas): `indSpec_decDom`, `indSpec_decRng`, `indSpec_challengeDom`, `indSpec_challengeRng`,
  `indImpl_dec_onSpec`, `indImpl_challenge_none_onSpec`. The `_onSpec` equations carry explicit
  `cast`s on the query **and** the answer, and are proved `by simpa only [cast_eq] using …`.
- `PrivateKey/OracleFromPRF.lean`: the target body; private helpers `cca2Decrypt`,
  `cca2OfFn_cast`, `cca2LastBit`, `cca2Run`; the target's proof sketch now names the budget `2`
  and `cca2Run`. Round-1 helpers are reused unchanged. File length 594 lines.

## Axioms

`prfFixedScheme_not_cca2` and `not_prfFixedScheme_cca2`: `[propext, Classical.choice,
Quot.sound]` (`evidence/logs/axioms-checkpoint.log`).

## Environment so far

Preflight: `nproc` 4; no cgroup memory files, `MemAvailable` 16,171,827,200 B (≥ 4 GiB);
clone filesystem ext4, 22,684,639,232 B free when logged (27.7 GB before the toolchain). Toolchain:
official `lean-4.25.0-linux.tar.zst`, SHA-256 `97bee7bd…6abb8a`. Cache store absent beforehand;
the narrowed fetch of the 98 roots downloaded and unpacked 2,381 files, exit 0, no failures.
Package pins: PASS, four documentation packages ABSENT. Bootstrap: the 129-module closure of
`OracleFromPRF`, serially, all passing except the first draft of the owned file, since fixed
(`evidence/logs/bootstrap.tsv`).
