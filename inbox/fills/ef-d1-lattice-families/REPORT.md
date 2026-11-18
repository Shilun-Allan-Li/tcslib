# EF-D1 `ef-d1-lattice-families`: checkpoint 1

**Head:** `d01d3f415f3b5fe88bd9f01a08603687641fb372` on local branch `fill/ef-d1-lattice-families` (not pushed).
**Base:** IO `5ed465f62e4ae0f93ded1a1ba49e807591b589eb`, tree `9155903018d18fbc735791f21485abaaee3e161a`
(checked with `git rev-parse`). **Records read:** `cryptography/pass-shelat-ch2-4` at
`54dcb3021a389831e7f94c3f82616cb7594fa574`; all nine COMMON.md §1 input SHA-256 values match.

## What this checkpoint claims

Both structures compile at the head (`scripts/lean_check_tree.sh`, rc 0, 0 errors in both forms, 0 `sorry`
warnings): `TCSlib/Cryptography/LWE/Efficient.lean` (`LWE.EfficientFamily`),
`TCSlib/Cryptography/SIS/Efficient.lean` (`SIS.EfficientFamily`) and the `SIS.lean` facade line.
`evidence/cp1/summary.txt` binds each log to `git show HEAD:<path>` by SHA-256. The non-vacuity instances
elaborate and their parameter words match the encoding at `κ ≤ 3` (`evidence/probes/D1P1.*`, with a kernel
`decide` check); the consumer smoke test elaborates (`evidence/probes/D1P2.*`).

Not yet claimed (final): C2–C13 in full (canonical seals over the full import closure with controls, axioms,
statement dump, lint diff, clashes, reproduction), *Overlap and reuse*, *Statement changes*, *Scope requests*.

**Advance notice (E-SCOPE, reader only).** `LWE/BitNoise.lean` has no reader for `(bitNoise t f).sample` /
`(centeredNoise t).sample` at a seed of type `Coins`: `bitNoise_sample` and `centeredNoise_sample` are
stated at `Fin _ → Bool` and fail under the Rule-10 seal when consumed at a `Coins`-typed seed. The head takes
the sample equation as a hypothesis in `noise_efficient_of_bitNoise` and `noise_efficient_centeredNoise`
(`CenteredSampleEq`), proved for `T = 0` from published readers (`centeredNoise_bounded`,
`centeredValue_eq`); the non-vacuity instance therefore uses `centeredNoise 0`. Details in the final.

## Environment

Cloud worker; nproc 4, MemTotal 16.47 GB, no cgroup limit (headroom = MemAvailable, 15.6 GB), 21.4 GB disk free
at preflight (`evidence/logs/preflight.log`). Toolchain v4.25.0 installed by elan after the preflight. The cache
archive store was absent before the first fetch (`cache-store.log`). Two narrowed fetches (74 + 9 roots, rc 0;
2375 and 1811 files decompressed); no empty oleans; packages check PASS (4 documentation packages ABSENT).
Bootstrap of the 158-module import closure with a pool of 3: all rc 0, peak per-process maxrss 2.93 GB
(`evidence/logs/pool.log`, `bootstrap/pool-run.tsv`; attempt 1 stopped on a missing import from a bug in my
closure parser and is kept).

## Commits

| hash | subject |
|---|---|
| `583c19f9493f5c3d0dcc135d667cc3a9f2eb751a` | LWE.EfficientFamily: uniform parameter map, bit-seed noise sampler in contract form |
| `d01d3f415f3b5fe88bd9f01a08603687641fb372` | SIS.EfficientFamily: uniform parameter map, dyadic schedules, facade line |
