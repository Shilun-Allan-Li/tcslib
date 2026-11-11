# Fill report · `bitwise-cpa` · checkpoint 1

**Worker** Claude (external fill, exchange push route). **Issue base**
`4a9b2c91eb2f89c4fb624339d5b4ba9cfd35ac27` on `cryptography/pass-shelat-ch2-4`. **Proof branch**
local `fill/bitwise-cpa` (2 commits over the base; never pushed). **Pack** read at exchange
`f4737d78e`; `sha256sum -c SHA256SUMS` in `outbox/fills/bitwise-cpa/`: all 7 OK
(`evidence/logs/pack-sha256.log`). Source hashes: `sha256sum -c SOURCE-SHA256SUMS` at the base,
197/197 OK (`evidence/logs/source-sha256.log`).

## Status at this checkpoint

**`BitPublicKeyScheme.SingleBitSecure.bitwise_padded_cpa` is proved** (steps 1–4 of the brief
were completed together, so this first checkpoint already carries the complete proof). The owned
module and the three new helper modules check with no errors and no warnings; the owned module has
no `sorry`. The frozen statement is byte-identical to the base.

Pending for the final delivery: the full sweep of the order list, the `sorry` census against
`base-sorries.txt`, the axiom prints, the instance-aware seal with controls, the explicit-unfold
scan and the campaign lint.

## Route (summary; details in the final report)

1. **Hybrids** `H_j` (`hybGame`, private): eager coins, `n` single-bit tapes `v`, the first
   challenge `l = m₀ ‖ m₁` answered with the padded tuple whose block `i` encrypts `l_{n+i}` if
   `i < j` and `l_i` otherwise. `accept_indGame_eq`: `Pr[Ind_b] = Pr[H_{b ? n : 0}]`.
2. **Gap index** `j⋆(n)` from `Games.exists_advantage_hybrid_gap` (`n > 0`; `0` at `n = 0`).
3. **Distinguisher** by T1 for a new generic query-recording handler
   (`BitwiseSim.exists_qHandlerMachine`), advice `⟨1^{j⋆}, ⟨1^{(j⋆+1)B}, 0…⟩⟩` in the initial
   state, seed `n·B(n)` bits, answer `BitwiseSim.plantAns` (the planted tuple, built from the
   published `blockEncFun`), final bit `BitwiseSim.plantOut`. **Exact identity**
   `hyb_advantage_eq`: `advantage(H_{j⋆}, H_{j⋆+1}) = distAdv(pkEncDist 0, pkEncDist 1, D)`.
4. **Bound**: `advantage ≤ n · distAdv`, negligible by `singleBitSecure_iff` and
   `Negligible.polyExpr_mul` with `PolyExpr.var`.

## Environment

- Preflight (`evidence/logs/preflight.log`): `nproc` 4; cgroup v1 limit is the unlimited
  sentinel, so the headroom is `MemAvailable` = 15.20 GiB (floor 4 GiB): PASS; clone filesystem
  ext4 on `/dev/vda`, 19.00 GiB free (floor 12 GiB): PASS. Scratch on the same filesystem.
- One clone (`/home/user/fill`, a worktree of the session's checkout), the same clone and
  `.lake/packages` this session used for the earlier `padded-cpa` fill on this host; the toolchain
  and `lake-manifest.json` are identical between the two bases. Cache store before the fetch:
  2,372 files, 118,543,444 bytes (`evidence/logs/cache-store.log`), written by the cache tool in
  that earlier fill. Narrowed `lake exe cache get` for the 92 roots (identical to `roots.txt`):
  "No files to download", "Decompressing 2345 file(s)", exit 0 (`evidence/logs/cache-get.log`).
- Packages: `package check: PASS (0 mismatches)`; ABSENT `doc-gen4`, `UnicodeBasic`,
  `BibtexQuery`, `MD4Lean` (`evidence/logs/packages.log`). No empty oleans. Cache probe
  (`import Mathlib.Algebra.BigOperators.Field`) passed.
- Bootstrap: fresh olean tree `.lake/bw-oleans`; the 153-module upstream closure of
  `PublicKey/BitwiseCPA` in the order list's order, all passed (`evidence/logs/bootstrap.log`).
  The remaining modules of the order list are checked in the final sweep.
- Development checks are in `evidence/logs/dev/` (one module per `lean_check_tree.sh` call). One
  development check of the owned module was stopped after about 40 minutes by the tool runner's
  background limit (a looping tactic; no Lean exit code). I then capped `maxHeartbeats` at 400000
  in the owned file during development to locate it, and ran that one check under a 25-minute
  `timeout` wrapper (it finished in 28 s). The cap is removed (the file keeps the base's
  `maxHeartbeats 0`); no other check was wrapped in a timeout.

**Checkpoint 1 — complete proof; checks pending**
