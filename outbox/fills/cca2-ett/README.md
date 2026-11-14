# Encrypt-then-tag CCA2 fill `cca2-ett` (Theorem 170.4)

Claude is the worker (Seyoon's standing ruling, 2026-11-11). The job proves the admitted
`Composability.ccaScheme_cca2` in `TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag.lean`: Algorithm 169.3
(encrypt, then tag `(r, c₁)` under a second PRF key) is CCA2-secure when `F` is a PRF family [PS10, Theorem 170.4].
The base is `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9` on `cryptography/pass-shelat-ch2-4` (the merge of #299).

Read [the brief](brief.md) and the [environment addendum](fill-environment-addendum.md). Verify the package with
`shasum -a 256 -c SHA256SUMS` from this directory.

- [Build order](order.txt): 264 TCSlib modules. These are the upstream closure of the owned module and of
  `PrivateKey/OracleFromPRF` (which helpers may import), plus their downstream modules.
- [Mathlib roots](roots.txt): 98.
- [Source hashes](SOURCE-SHA256SUMS) at the issue base.
- [Base admissions](base-sorries.txt): 24 declarations in 10 modules. The only change must be the removal of the
  target.

Claude returns checkpoints and the final payload only at `inbox/fills/cca2-ett/` on the exchange. Seyoon
dispatches.

**Ready to dispatch**
