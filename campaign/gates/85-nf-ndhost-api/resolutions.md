# The controller-stopped writer and one guess-then-run host (PR #174, an API gate): resolutions

**Gate:** the API gate of PR #174 (`lean/nf-ndhost-api` at `1045624d`). Pack `pack.md`; bundle
SHA-256 `19830ec7067d9df4db4c8cf801c9867093e9908831ce2725aaf645e7d2da050a` (71 sections), the
records at `d51ac787`. **Findings: pending.**

**The replay.** `replay-lnfapi3` passed (user, 2026-10-27): 4 of 4 modules at `1045624d`, 0 failed,
static-equal (`evidence/merged-tree/replay-lnfapi3.log`, `replay-lnfapi3-static.txt`). Its snapshot
is `oleans-lnfapi3`.

**Merge state. #174: not yet clear to merge** (2026-10-27): it waits for this gate.
