# Not-CCA2 fill (`not-cca2`)

Codex is the selected worker (Seyoon, 2026-11-11). The proof base is
`4a09f3993eb9344fc5714610e41ab141a0144db8` on `cryptography/pass-shelat-ch2-4`.
Read [the brief](brief.md) and [environment addendum](fill-environment-addendum.md).
Verify the package with `shasum -a 256 -c SHA256SUMS` from this directory.

- [Build order](order.txt) lists 232 TCSlib modules: the upstream closure of
  `Encryption/PrivateKey/FromPRF` (where one reader is added) and every module downstream of it,
  which includes the target file `Encryption/PrivateKey/OracleFromPRF`.
- [Mathlib roots](roots.txt) lists the 98 direct Mathlib imports of that order.
- [Source hashes](SOURCE-SHA256SUMS) can be checked from the clean issue checkout
  (`shasum -a 256 -c SOURCE-SHA256SUMS` from the repository root).
- [Base admissions](base-sorries.txt) lists the source admissions in that order (33).

Codex returns checkpoints and the final payload as labelled ZIP (or Markdown) artifacts in the
chat and does not push. The maintainer files them under `inbox/fills/not-cca2/`. Seyoon
dispatches.

**Ready to dispatch**
