# Fill s2b-efficiency — checkpoint 3 (T4)

**Worker** Claude. **Issue base** `b50f0a416cbf0a9f05acf14a254ba53cd97a7701` on
`cryptography/pass-shelat-ch2-4`. **Package** read at exchange commit
`81449bb35998cc291d2f083ab2b07ccbce7fb2a9` (`shasum -c SHA256SUMS`: all OK,
`evidence/logs/package-sha256.log`; `SOURCE-SHA256SUMS`: all OK on the clean issue checkout,
`evidence/logs/source-sha256.log`). Local proof branch `fill/s2b-efficiency` at the issue base.

## Status

| Target | Status at this checkpoint |
|---|---|
| Companion `exists_toCompOn_of_toComp` | **proved** (checkpoint 1) |
| T1 `exists_handlerMachine` | **proved** (checkpoint 2) |
| T2 `exists_interactiveHandlerMachine` | admitted (unchanged) |
| T4 `exists_toOracleAdversary_of_bitCodec` | **proved** (no `sorry`) |

Companion (checkpoint 1): `NUPPT.exists_comp A polyTimeComputable_pairSndD
polyTimeComputable_id`; `φ` is `NUPPT.coinsCongr`.

T1: `B` is `EffFill.exists_splitMachine` (`NUPPT.ofPolyTime`, then `NUPPT.exists_split` with
`p = H.seedLen`) of the raw function `EffFill.hRaw`, with the advice `⟨A.advice n, H.init n⟩`
(the initial state is an arbitrary function of `n`, so it is advice; `B` is non-uniform). `hRaw`
is an activation loop over `GGMRed.stateLoopFun` (`EffFill.actLoop`) on the state
`⟨L, ⟨s, 1^t⟩⟩`; a round reads `A`'s move through the canonical decoder `EffFill.canonWord`
(`canonWord_eq`: the canonical word of `decodeBitMove`'s move on every word, tested by
re-encoding), and decodes `run`'s answer componentwise (`fixLen`, `ofFn_getD_decodeFin`).
`hRaw_poly` gives polynomial time; `hRaw_spec` (induction on the remaining budget,
`stateLoopFun_eval` through `runsTo_stop`) the functional equation. The sketch of T1 now
describes this proof (advice for `init`, helper names).

T4: `B'` is `NUPPT.exists_comp B bridgePre_poly bridgePost_poly`, `φ = NUPPT.coinsCongr`.
`EffFill.bridgePre` turns `encodeHist` of a history into `⟨[], encodeLog⟩` of the `Fin 1`
`bitCodec` log (one emitted piece per suffix, `polyTimeComputable_iterateEmit` with `pairSndD`;
`bridgePre_encodeHist`). `EffFill.bridgePost` maps `⟨[false], ⟨[], x⟩⟩` to `⟨[false], x⟩`,
`⟨[true], [true]⟩` to `[true, true]`, anything else to `[true, false]`; `bridgePost_spec` shows
the two decoders read corresponding moves on every word (wrong payload length, `ℓ₁(n) = 0` and
the default verdict included). `eval_buildTree_bridge` (induction on the budget) gives the
equality of evaluations; at the timeout the verdict `false` is bit `0` of `zeroBits 1`.

## Changed files

- `TCSlib/Cryptography/Games/Efficiency.lean` (three proof bodies, three sketches, three imports).
- New: `TCSlib/Cryptography/Games/Efficiency/Strings.lean`, `…/Efficiency/Handler.lean`,
  `…/Efficiency/OracleBridge.lean` (EF-1; namespace `TCSlib.Cryptography.Games.EffFill`; `Strings` imports
  `Pseudorandom.Functions.Asymptotic.GGM.Reduction` directly).

## Checks at this checkpoint

`OracleBridge`, `Efficiency`: exit 0; one `sorry` warning (T2) (`evidence/logs/checks-cp3.log`;
`Strings` and `Handler` unchanged since `checks-cp2.log`). `campaign_style_lint.py TCSlib/Cryptography/Games --check8b`:
0 FAIL, 0 WARN.

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

**Checkpoint 3 delivered — continuing with T2**
