# Gate 20 · supplement r1 (G20-01)

These are the raw evidence files that `verification.zip` and `landing.zip` left out for size. Each one is the
original, byte-identical to the hash recorded in that ZIP's inner `SHA256SUMS`. Nothing here was re-run.

| Archive | SHA-256 | Files | Completes |
|---|---|---|---|
| `verification-supp.zip` | `5a219acc27e4cb05ecc653af408895a30cd405bafe329a14fcc7863a872d8a72` | 1028 | `verification.zip` (inner manifest `35bfc608…`, 2441 entries) |
| `landing-supp.zip` | `b234696208975c9f14057ce379f458075fe6c5a2be42fe7e68cceabd7c213ed0` | 92 | `landing.zip` (inner manifest `da4ad8b3…`, 188 entries) |

**Paths.** Entry paths are relative to the same root as the main ZIP: the review directory and the rebase-r1
directory respectively. Unzip each supplement over its main ZIP.

**`coverage-check.txt`.** It confirms that the main ZIP and its supplement together hold every manifest path. Every
hash matches, there is no overlap, and the supplement holds nothing outside the manifest.

## What `verification-supp.zip` holds (by top-level directory)

| Directory | Files | Content |
|---|---|---|
| `base-census-run/`, `base-probe-runs/` | 3, 5 | the baseline census and collector runs and logs |
| `base-seals/`, `base-seal-runs/` | 162, 82 | baseline whole-file seal sources, manifests and request records; raw logs and `results.jsonl` |
| `seals/`, `seal-runs/` | 166, 84 | head seal sources, manifests and request records; raw logs and `results.jsonl` |
| `controls/` | 118 | the paired controls: `controls/out/` (the control plan and the 34 generated control sources, sealed `ControlS` and unsealed `ControlU`), `controls/records/` (82 seal request records) and `controls/controls-result.json` |
| `probe-sources/` | 7 | the census and collector probe sources |
| `base-tree/`, `base-tree-extra/` | 231, 4 | the baseline olean-tree build: per-module raw logs and `results.jsonl` |
| `superseded/` | 166 | runs replaced by later ones and kept for completeness: paired-control attempt 1, and the probe runs before and during LE-rule10 (`superseded/DISPOSITION.txt` gives each one's disposition) |

## What `landing-supp.zip` holds

| Directory | Files | Content |
|---|---|---|
| `seals/` | 46 | the 22 nm-sim seal sources for variants A and B, with `seals/{A,B}/manifest.json` and the request records |
| `seal-runs/` | 24 | the 22 raw seal logs and `results.jsonl` |
| `controls-records/` | 22 | the 22 nm-sim seal request records that the paired controls are built from |
