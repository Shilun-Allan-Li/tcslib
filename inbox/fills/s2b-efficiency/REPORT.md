# Fill s2b-efficiency — checkpoint 1 (the companion)

**Worker** Claude. **Issue base** `b50f0a416cbf0a9f05acf14a254ba53cd97a7701` on
`cryptography/pass-shelat-ch2-4`. **Package** read at exchange commit
`81449bb35998cc291d2f083ab2b07ccbce7fb2a9` (`shasum -c SHA256SUMS`: all OK,
`evidence/logs/package-sha256.log`; `SOURCE-SHA256SUMS`: all OK on the clean issue checkout,
`evidence/logs/source-sha256.log`). Local proof branch `fill/s2b-efficiency` at the issue base.

## Status

| Target | Status at this checkpoint |
|---|---|
| Companion `exists_toCompOn_of_toComp` | **proved** (no `sorry`) |
| T1 `exists_handlerMachine` | admitted (unchanged) |
| T2 `exists_interactiveHandlerMachine` | admitted (unchanged) |
| T4 `exists_toOracleAdversary_of_bitCodec` | admitted (unchanged) |

Proof: `NUPPT.exists_comp A polyTimeComputable_pairSndD polyTimeComputable_id`; `φ` is
`NUPPT.coinsCongr`, and `runAt_coinsCongr`, `pairSndD_pairEncode`, `runAt_eq`, `toCompOn_eq`,
`toComp_eq` conclude. The sketch now names `coinsCongr`/`runAt_coinsCongr` and drops the
remark that `coinLen_eq` was still to be published (it is). Statement and statement prose are
unchanged.

## Changed files

`TCSlib/Cryptography/Games/Efficiency.lean` only (`patches/0001-…`, `src/`).

## Environment (addendum v1)

- Preflight (`evidence/logs/preflight.log`): `nproc` 4; cgroup v1 with no memory limit, so the
  headroom is `MemAvailable` = 15.18 GiB (memory in use 34.9 MiB); 25.33 GiB free on `/dev/vda`
  (ext4). Pass. Toolchain Lean 4.25.0 installed afterwards with `elan`; re-check before the cache:
  23.95 GB free.
- Cache: store absent before the fetch (`cache-store.log`); 68 roots (identical to the supplied
  `roots.txt`), `Attempting to download 2066`, `Decompressing 2066`, exit 0
  (`cache-get.log`). Packages: every present package matches the manifest; ABSENT `doc-gen4`,
  `UnicodeBasic`, `BibtexQuery`, `MD4Lean` (`packages-check.log`, last line
  `RESULT: all present packages match the manifest`). No zero-size olean; root probe passes
  (`cache-probe.log`).
- Bootstrap: modules 1–130 of `order.txt` (everything before `Games/Efficiency`), 130/130 exit 0
  (`bootstrap.log`). The detached background sweep was terminated by the session twice (no OOM
  event); the rest ran in the foreground in chunks, as recorded in the log.
- Check of `Games/Efficiency` at this checkpoint: exit 0, three `sorry` warnings (the three
  remaining targets) (`evidence/logs/checks-cp1.log`).

**Checkpoint 1 delivered — continuing with T1**
