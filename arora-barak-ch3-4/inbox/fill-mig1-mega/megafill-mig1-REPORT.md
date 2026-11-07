# megafill-mig1 — session report (Claude)

Queue: one integrated item, the MIG-1 F-A → F-C → F-B → F-D megafill
(`campaign/fills/mig1/briefs/megafill-mig1.md`, SHA-256 af596548…a1ea; bundle SHA-256
43ebed1880e470c606811c08ff478e5e96c7b02401b6a150cc48c6a5b5a2ebcf, 324 sections, verified).

| Item | Outcome | Branch | Start | End | Zip SHA-256 |
|---|---|---|---|---|---|
| MIG-1 megafill | **partial** — 17/17 targets + 3/3 gated exports proved, 6/6 rows retired, Catalog copies deleted; full sweep (641 modules), both screens, census, axioms, freeze at the delivered head; seal of verbatim-moved Primitives material (17 errors), MIG-24 T2/T5 and part of T2b/T3 incomplete (see REPORT.md) | `fill/mig1-mega` @ 83ac315ed9e7089466bd16a32f3b71fbadc556d2 → **246d81d2ce247d9e76dcc0ffbfc5080fd1d8fde5** (revision 2; revision 1 was cbfdba8102e6a5d956a1fdd2be7518b490a5abac) | 2026-11-07T07:23:15Z | 2026-11-07T13:32Z | current `fill-mig1-mega-r2.zip` 283c0d2771c37a59844ead5d4516309f6098260b76153fe19c3233d7ca025eca (revision 1 `fill-mig1-mega.zip` 4315dcfd348b9cce1e7dbf02de0b75b7e2596a177039fee823061f5d706962b6) |

Checkpoint zips (all in `arora-barak-ch3-4/inbox/fill-mig1-mega/`):

| Zip | Commit | SHA-256 |
|---|---|---|
| fill-mig1-mega-cp01.zip (F-A same-home group) | f4f205f9427842542c727d6c52f9eae897771162 | 2902aa4aac91b7a8b26c494189cfcb11fa39fe76b63f451e2dfaf9c2633a255f |
| fill-mig1-mega-cp02.zip (F-A) | 3012d8dc89f454c34c7fb8dcfbf5a9e3866921aa | d1f031d594a693e1e494014e656caebf10f113b1e034e21514cec61259f57649 |
| fill-mig1-mega-cp03.zip (F-C; also the cp04 point) | 0d03f8f959ba7d84fc8e9bdc5e932e28c24da30b | d65316ee9f8b073c8ccabd7a694d2f9613ac76e1bbf7c40153db45e1b7538c4a |
| fill-mig1-mega-cp05.zip (F-B targets) | f74d8c0ed8ac1f452a2026e9b1204f0442f40456 | 5744d37d6144ca803134ba247144c3686acca1f0f581f35bacdd45cbc032385c |
| fill-mig1-mega-cp07.zip (F-D) | cbfdba8102e6a5d956a1fdd2be7518b490a5abac | 22d64f8fa9de04e3c82ab3a8a79c06b6a1679917509e409de7a78d3b4b141c9f |
| fill-mig1-mega.zip (final revision 1, validated; superseded) | cbfdba8102e6a5d956a1fdd2be7518b490a5abac | 4315dcfd348b9cce1e7dbf02de0b75b7e2596a177039fee823061f5d706962b6 |
| **fill-mig1-mega-r2.zip (final revision 2, validated; current)** | 246d81d2ce247d9e76dcc0ffbfc5080fd1d8fde5 | 283c0d2771c37a59844ead5d4516309f6098260b76153fe19c3233d7ca025eca |

Shared environment: preflight PASS (4 CPUs; no cgroup memory limit, MemAvailable 15.39 GiB;
29.09 GiB free on ext4); Lean 4.25.0 started normally (no shim); cache store empty before the
fetch; 239 Mathlib roots, 3,331 files downloaded and decompressed, 0 failed; packages 11 present
match, 4 absent (documentation toolchain). Session start 2026-11-07T07:22:26Z; end 2026-11-07T13:33Z.

The maintainer reviews the delivery and prepares the PR(s); no campaign branch was changed and no
PR was opened.
