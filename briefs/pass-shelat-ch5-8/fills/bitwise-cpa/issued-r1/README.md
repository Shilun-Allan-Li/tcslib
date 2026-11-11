# CPA pilot fill `bitwise-cpa`

Claude is the selected worker (Seyoon, 2026-11-11). Target `SingleBitSecure.bitwise_padded_cpa` in
`TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA.lean`. The proof base is
`4a9b2c91eb2f89c4fb624339d5b4ba9cfd35ac27` on `cryptography/pass-shelat-ch2-4`.
Read [the brief](brief.md) and [environment addendum](fill-environment-addendum.md).
Verify the package with `shasum -a 256 -c SHA256SUMS` from this directory.

- [Build order](order.txt): 197 TCSlib modules (the upstream closure of `PublicKey/BitwiseCPA` and every
  module downstream of it).
- [Mathlib roots](roots.txt): 92. [Source hashes](SOURCE-SHA256SUMS) at the issue base.
- [Base admissions](base-sorries.txt): 27.

The parallel fill (`adaptive-cpa` / `bitwise-cpa`) owns the other CPA pilot file; neither edits
the other's. Claude returns checkpoints and the final payload only at `inbox/fills/bitwise-cpa/` on the
exchange. Seyoon dispatches.

**Ready to dispatch**
