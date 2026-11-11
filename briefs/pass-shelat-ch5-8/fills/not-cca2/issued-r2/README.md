# not-cca2 continuation (round 2)

Claude is the selected worker for the continuation (Seyoon, 2026-11-11). The proof base is
`4a09f3993eb9344fc5714610e41ab141a0144db8` on `cryptography/pass-shelat-ch2-4`; start by applying
the round-1 Codex patches from `inbox/fills/not-cca2/patches/`.
Read [the round-2 brief](brief.md), [the round-1 brief](brief-r1.md) and the
[environment addendum](fill-environment-addendum.md).
Verify the package with `shasum -a 256 -c SHA256SUMS` from this directory.

- [Build order](order.txt): 232 TCSlib modules, unchanged from round 1; it contains everything
  downstream of `PrivateKey/OracleSecurity` and `PrivateKey/FromPRF`.
- [Mathlib roots](roots.txt): 98. [Source hashes](SOURCE-SHA256SUMS) at the issue base.
- [Base admissions](base-sorries.txt): 33.

Claude returns checkpoints and the final payload only at `inbox/fills/not-cca2/` on the
exchange. Seyoon dispatches.

**Ready to dispatch**
