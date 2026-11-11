# Private-key CPA/CCA1 fill `pk-cpa-cca1`

Claude is the worker (Seyoon's standing ruling, 2026-11-11). Targets `prfFixedScheme_cpa` and
`prfFixedScheme_cca1` in `TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF.lean`. The proof
base is `8c3afbff69ad1273446750f47c05d424ab13ebe2` on `cryptography/pass-shelat-ch2-4`.
Read [the brief](brief.md) and [environment addendum](fill-environment-addendum.md).
Verify the package with `shasum -a 256 -c SHA256SUMS` from this directory.

- [Build order](order.txt): 242 TCSlib modules (the upstream closure of `PrivateKey/OracleFromPRF`
  and every module downstream of it).
- [Mathlib roots](roots.txt): 97. [Source hashes](SOURCE-SHA256SUMS) at the issue base.
- [Base admissions](base-sorries.txt): 29.

Claude returns checkpoints and the final payload only at `inbox/fills/pk-cpa-cca1/` on the exchange.
Seyoon dispatches.

**Ready to dispatch**
