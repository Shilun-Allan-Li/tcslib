# Snapshot adoption after #344 (2026-11-16)

#344 (gate 151, C1E-1 trims in `ClassNP/ExhaustiveReplay`) merged at the commit in ADOPTION.json,
after #343. Its merged-tree replay on `oleans-cf8187` (the #343 merge's snapshot) rebuilt the
4-module downstream closure (4 passed, 0 failed, 0 admissions), and the merge's Lean equals that
replay's prospective tree `6a905753`. No separate adoption replay was run. Its output is adopted
as `oleans-cfb6f2` (874 objects, rehashed on disk against the replay's map). `oleans-cf8187` is
kept as fallback. See ADOPTION.json.

## Snapshot rebase check (2026-11-16, Seyoon's request)

- Base commit T: `c9c51a73e46e5b05bb437e1bc93e9cd7178a0849` (records tip; its Lean equals the #344
  merge `fb6f2e31` and the replayed tree `6a905753`, with 0 differing Lean/toolchain/manifest files).
- `oleans-cfb6f2` is already the full snapshot at T, so no module was rebuilt (0 built, about 1 s).
- Restore check against its map: 0 extra, 0 changed, 0 missing, 874 modules. The map SHA-256 is
  `2a34ed61cfb17a107e601d5046282a0b1008b79f2bb21751dea289291a76e094`.
- The old backups `oleans-cf8187` and `oleans-cc011` were deleted, along with the duplicate name
  `oleans-cl151b-cf8187`. Their manifests are kept in the maintainer scratch (`manifests/`) and
  their SHA-256s in their ADOPTION.json files. Free disk went from 5.4 GB to 6.0 GB.
- From now on, `oleans-cfb6f2` is the restore point and T is the base. There is no older fallback;
  a lost snapshot is rebuilt with `devtools/seyoon/bootstrap-snapshot.sh`.
