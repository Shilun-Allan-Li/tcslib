# Fill report: unit rabin (`TCSlib/Cryptography/Candidates/Rabin.lean`)

**Status: in progress (checkpoint 7).** Filled so far: steps 1–6 (10 targets).

## Base and environment

- Base: `16a7d02d69cae1a700c131e3cc3dd918a7b3d6e1` (`git rev-parse`), fetched from
  `cryptography/pass-shelat-ch2-4-eqlemmas`. Local branch `fill/rabin`, never pushed, never rebased.
- Exchange commit read at start: `22e3c69` (descendant of `fe9b979c46c63d083e5e004ad91c0c3dec3edead`).
- Host preflight (`evidence/logs/preflight.log`): `nproc` 4; cgroup v1 memory limit
  `9223372036854771712` (unlimited), so the headroom is `MemAvailable` = 15.39 GiB (floor 4 GiB);
  the clone's filesystem (`/dev/vda`, ext4) has 29.40 GiB free (floor 12 GiB). PASS.
- Toolchain: Lean 4.25.0 (`release.lean-lang.org` is not resolvable from this host, so `elan`
  could not fetch it; I downloaded the official release archive
  `lean-4.25.0-linux.zip` from `github.com/leanprover/lean4/releases/tag/v4.25.0` into
  `/workspace/toolchain` (ext4) and registered it with `elan toolchain link`). After it, 26.8 GiB
  free (re-check floor 8 GiB).
- Cache store before the fetch (`evidence/logs/cache-store.log`): `/root/.cache/mathlib` did not
  exist (0 archives). The narrowed fetch (`evidence/logs/cache-get.log`) used the 75 roots of
  `evidence/logs/mathlib-roots.txt` (identical to `inputs/rabin/roots.txt`): 2344 files
  downloaded, 2344 decompressed, exit 0, no failed download.
- Packages (`evidence/logs/packages-check.log`): "RESULT: PASS: every present package matches the
  manifest; absent: doc-gen4, UnicodeBasic, BibtexQuery, MD4Lean". No module imports an absent
  package. Zero-size oleans: none (`evidence/logs/zero-oleans.log`). Cache probe
  (`import Mathlib.Algebra.BigOperators.Field`) rc 0 (`evidence/logs/cache-probe.log`).
- Bootstrap (`evidence/logs/bootstrap.log`): the 71 modules of `order.txt` that `Rabin.lean`
  imports, in order, all rc 0. Base owned file: rc 0 with exactly the 19 `sorry` warnings
  (`evidence/logs/base-owned-check.log`). `/usr/bin/time` is absent; `evidence/chk.py` logs each
  module's start, end, wall time and child max RSS instead.
- Never `lake build`; never an unfiltered `lake exe cache get`; one Lean process at a time.

## Targets (brief order; updated at each checkpoint)

| # | Target | State |
|---|---|---|
| 1 | `rabinSampler_spec` | filled (sketch followed: activation `rabin_sampler_runAt`, `rabin_dec_unitSampleStr`, canonical decoding `rabin_enc_of_dec`, `rabinEval_spec`) |
| 1 | `blumSampler_spec` | filled (activation `rabin_blumSampler_runAt` with `modExpStr_pairEncode`; `BlumValid` of a generated index; `QR` membership as the square of `unitOfCoprime v`; `blumEval_spec`) |
| 2 | `blumInv_spec` | filled by the brief's **Route** (no `blumSqrt` reading): `rabin_blumInvNat_spec` (CRT value is a residue root with residue `blumInvNat p q y.val`), then `Equiv.symm_apply_eq` on `blumPermAt`; Proof sketch paragraph rewritten |
| 3 | `rabinCollection_sampleClose` | filled: `δ n = 1` for `n < 3` (P3), `e^{-n}` otherwise via S3 (`rabin_statClose_dec`); docstring expanded with a Proof sketch |
| 3 | `rabinBlumTrapdoor_sampleClose` | filled: S3 mapped through squaring, `pushesUniform_sqTo`, `statClose_of_pushesUniform`, `StatClose.trans` (`rabin_statClose_blumDec`); docstring expanded |
| 4 | `oddFactorProb_le` | filled (Correction target; Proof sketch rewritten): conditioning bound `rabin_uprob_subtype_le`; `Pr[E] ≥ 1 − 3/|Π_n| ≥ 1/2` from `|Π_n| ≥ 6` |
| 4 | `blumFactorProb_le` | filled (Proof sketch rewritten): `Pr[E] ≥ B(B−1)/P² ≥ 1/(64n²)` from `hD` |
| 5 | `polyTimeComputable_oddGenRaw` | filled: `rabinGenRaw = rabin_genCore` (`rabin_genCore_eq`) and `rabin_genCore_poly`; generic block loop over `polyTimeComputable_iterateFind` (`rabin_spOut_poly`); test `rabin_oddAcc` (prime, parity by `H.divMod`/`H.le`) |
| 5 | `polyTimeComputable_blumGenRaw` | filled: same generic helpers, test `rabin_blumAcc` (residue mod 4 by `H.divMod`/`H.le`); short docstring expanded into a Proof sketch |
| 6 | `polyTimeComputable_rabinFactorRaw` | filled (Correction target; Proof sketch rewritten): string computation `rabin_fOut` with a zero-padded modulus word so every numeral reads back exactly (also `N = 0`); low `n` bits by `(⟦0⟧_n ++ g).drop |g|` |
