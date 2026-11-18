# ef-h11-sharing-bgw — checkpoint 1

**Head of this checkpoint:** `56ade7282be0725db8d270c19527566e6d601c32` (branch `fill/ef-h11-sharing-bgw`, local,
not pushed), one commit on the base. **Base:** IO `5ed465f62e4ae0f93ded1a1ba49e807591b589eb`, tree
`9155903018d18fbc735791f21485abaaee3e161a` (`git rev-parse` checked; matches COMMON §2).

What this checkpoint claims: the efficient secret-sharing interface (`SecretSharing/Efficient.lean`) and the Shamir
instance (`SecretSharing/ShamirEfficient.lean`), with the `SecretSharing.lean` facade lines, compile with rc 0,
0 errors, 0 `sorry` (`evidence/build/cp1/summary.txt`, each source's SHA-256 bound to `git show 56ade728…:<path>`).
Every claim is backed by `patches/` (reproduce the head from the base), `src/` (the three files at the head) and the logs.
Checks C1–C13 and H11-P1…P3 come with the final.

## Base and inputs
- All nine COMMON §1 inputs match their SHA-256 at the records pin `54dcb3021a389831e7f94c3f82616cb7594fa574`.
- Rulings, COMMON.md and the brief read at the same pin.

## Environment (cloud worker)
- Preflight (`evidence/logs/preflight.log`): `nproc` 4. No cgroup v2 memory files, so headroom = `MemAvailable`
  15.0 GiB (above the 4 GiB floor). Disk: 21.5 GB free on ext4 `/dev/vda` (above the 12 GiB floor). Not tmpfs.
- Toolchain: `leanprover/lean4:v4.25.0` via elan.
- Cache store: absent before the fetch (`cache-store.log`).
- Narrowed `lake exe cache get` over 74 Mathlib roots (the closure of the files' imports): 2,340 files downloaded,
  rc 0.
- Packages: every present package matches the manifest's URL and revision. ABSENT: doc-gen4, UnicodeBasic,
  BibtexQuery, MD4Lean. 0 empty oleans.
- Bootstrap: 109-module closure in dependency order.
  - 108 rc 0 (`evidence/build/bootstrap-summary.txt`).
  - `Complexity/ClassP/BinaryArith/DetMod` is still compiling. It is not imported by the new files.
- Pool: `min(4, 15 GiB / 4 GiB) = 3` slots (flock), shared by the lead and the sub-agent. Peak RSS per module is
  about 2.93 GB. Changes are in `pool.log`.

## Sub-agents
- `bgw` writes `MPC/BGW/Efficient.lean` (file C) in its own worktree and olean tree. That file is not part of this
  checkpoint. It is in the final.
