# Duplicate A-3 dispatch: checksum-verified two-run comparison (finding 13)

All three delivered archives remain at `ch2_local/epoch3/` (maintainer-side;
binary archives are not bundle-attachable, so this record carries their
identities and the verified binding).

| Artifact | SHA-256 |
|---|---|
| `fill-ch2-e3cont-A3.zip` (run alpha) | `a5d7948ee3e14749e2c27ae72a8ffd43dc547f39d93c29781dd6b5dcee99767f` |
| `fill-ch2-e3cont-A3 (2).zip` | identical to alpha (same SHA-256) |
| `fill-ch2-e3cont-A3 (1).zip` (run beta, selected) | `161e6cc7ea4b038294e3f51d52803d910acd462419b1f96973d2a08c24d2e9f1` |
| beta's patch `0001-close-padding-cluster.patch` | `f78fde614d5f01f63e434e513ba57b7efce6c4e86aa8ee9937402bdcd996176e` |
| alpha's patch `0001-Close-the-E3-continuation-padding-cluster.patch` | `92bb4d3801f3092a3c85943154acf001be26124636d2d478298446b562b65c54` |

**Binding, mechanically re-verified 2026-10-06 for this record**: applying
beta's patch with `git am` in an isolated worktree at `1c824071^`
(= `61cf5958`, whose owned-file contents are byte-identical to the brief
base `f57cf9c1` — the intervening commit adds briefs only) reproduces tree
`8e1c03588179ae0457ea4b388521aa7bfc43cbe6`, exactly the tree of the
integrated commit `1c824071`. The integration therefore contains beta's
delivery and nothing else.

Alpha was never applied to any branch; no blob from alpha's archive appears
in the repository (its sources remain only inside the archived zip). Alpha's
REPORT opens:

> # E3 continuation A3 — complete padding-cluster delivery

The selection criteria and their application are recorded in the decision
log (2026-10-05) and summarized in the span attestation §6; this record
supplies the checksum layer that finding 13 requested. The no-hybridization
claim is witnessed by the tree identity above.
