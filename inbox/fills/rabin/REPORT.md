# Fill report: unit rabin (`TCSlib/Cryptography/Candidates/Rabin.lean`)

**Status: in progress (checkpoint 2).** Filled so far: `rabinSampler_spec`, `blumSampler_spec`.

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
