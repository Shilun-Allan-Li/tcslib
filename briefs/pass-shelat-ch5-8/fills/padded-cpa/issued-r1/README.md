# Public-key CPA bridge fill (`padded-cpa`)

Claude is the selected worker (Seyoon, 2026-11-11). The proof base is
`4a09f3993eb9344fc5714610e41ab141a0144db8` on `cryptography/pass-shelat-ch2-4`.
Read [the brief](brief.md) and [environment addendum](fill-environment-addendum.md).
Verify the package with `shasum -a 256 -c SHA256SUMS` from this directory.

- [Build order](order.txt) lists 221 TCSlib modules: the upstream closure of
  `Encryption/PublicKey/OracleSecurity` and every module downstream of it.
- [Mathlib roots](roots.txt) lists the 97 direct Mathlib imports of that order.
- [Source hashes](SOURCE-SHA256SUMS) can be checked from the clean issue checkout
  (`shasum -a 256 -c SOURCE-SHA256SUMS` from the repository root).
- [Base admissions](base-sorries.txt) lists the source admissions in that order (31).

Claude returns checkpoints and the final payload only at
`inbox/fills/padded-cpa/` on the exchange. Seyoon dispatches.

**Ready to dispatch**
