# CCA2 non-malleability fill `nm-cca2` (Theorem 175.9)

Claude is the worker (Seyoon's standing ruling, 2026-11-11). The target is
`FixedLengthPKScheme.indSecure_cca2_iff_nmSecure_cca2` in
`TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability.lean`. The proof base is
`b96ab3ccc1915497ea3138df499eec00b6581db0` on `cryptography/pass-shelat-ch2-4`. This fill runs in parallel with `dl-consolidation`; the
brief's duplication rule binds. Read [the brief](brief.md) and the
[environment addendum](fill-environment-addendum.md). Verify the package with `shasum -a 256 -c SHA256SUMS`
from this directory.

- [Build order](order.txt): 249 TCSlib modules. These are the upstream closure of
  `NonMalleability/Indistinguishability` and every module downstream of it.
- [Mathlib roots](roots.txt): 97.
- [Source hashes](SOURCE-SHA256SUMS) at the issue base.
- [Base admissions](base-sorries.txt): 27.

Claude returns checkpoints and the final payload only at `inbox/fills/nm-cca2/` on the exchange. Seyoon
dispatches.

**Ready to dispatch**
