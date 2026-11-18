# evidence-s8.zip: correction for G50-03

Gate 50 round 1 (Codex), finding **G50-03** (minor): the inner manifest `owner-prereqs-6b-s8/SHA256SUMS` listed
itself with the empty-file hash, so that one entry failed verification. The other 184 entries passed.
Maintainer sub-agent, 2026-11-18.

| | Archive SHA-256 | Inner `SHA256SUMS` SHA-256 | Manifest lines | `sha256sum -c` |
|---|---|---|---|---|
| Old | `e97aed5847d150d1cc9466b23c66a52e8dd2b978cabd44841a480c35fbe8dd29` | `2e831e4c4d19fb7de19b9cc36a54f5834d06df5c39230027aa2893766e3ba7ad` | 185 | 184 OK, 1 FAILED (itself) |
| New | `d3373171bef4138120192fb3c4bc4d4ecbf7ffc472a6bbbc818dd31f96fefe68` | `4454ed7b27060cd4c50887bd5628d661ce9635e45484d77d6f78bc29071ea5f1` | 184 | 184 OK, 0 FAILED |

- **Change.** Only the self-entry line `e3b0c442…b855  owner-prereqs-6b-s8/SHA256SUMS` was dropped. The other 184
  lines are unchanged, byte for byte and in order.
- **Method.** Every other zip entry was copied unchanged from the old archive: name, order, timestamp, compression,
  attributes and bytes. The script is `rezip.py`, run with `python3 -I`.
- **Content check.**
  - The old archive's contents equal its source directory, `$SP/g6bprereq8/zipstage/owner-prereqs-6b-s8`.
  - Both archives have 217 entries.
  - Extracted, the new tree differs from the old one only in the `SHA256SUMS` line above (`diff -r`).
- **Outer manifest.** The `evidence-s8.zip` line of `evidence-SHA256SUMS` now gives the new hash.
  `sha256sum -c evidence-SHA256SUMS` passes for both archives.
- **Unchanged.** The evidence it binds is the #368 snapshot-8 replay, merge tree
  `ab098201a13ad10829914bfbc6bedcbb2fe52e9e`.
