# Claude fill `prf-long` (ruling B3: the PRF machinery at ℓ-bit outputs)

Claude is the worker (Seyoon's standing ruling, 2026-11-11). The job generalizes the PRF machinery of [PS10,
Theorem 99.2] to `ℓ(n)`-bit outputs, additively, in the frozen `Encryption/PrivateKey/FromPRF*` files and
`Pseudorandom/Functions/Asymptotic/Defs.lean` (ruling B3, 2026-11-14, pre-approved scope). It re-derives the `n`-bit
versions as corollaries and changes no frozen statement. It proves no admitted target; `sc-garble` consumes it. The
base is `7b307d6254f6ed0e98f44cd563f88f9c56b7b1ee` on `cryptography/pass-shelat-ch2-4`, the records tip after #303 and #305–#309. #311 and #312 are not
merged, and this unit depends on neither.

Read [the brief](brief.md) and the [environment addendum](fill-environment-addendum.md). Verify the package with
`shasum -a 256 -c SHA256SUMS` from this directory.

- [Build order](order.txt): 434 TCSlib modules. These are the upstream closure of every module downstream of
  an owned file, and of `Games/Efficiency` (which helpers may import).
- [Mathlib roots](roots.txt): 111.
- [Source hashes](SOURCE-SHA256SUMS) at the issue base.
- [Base admissions](base-sorries.txt): 40 declarations in 19 modules. They must be unchanged.

Claude returns checkpoints and the final payload only at `inbox/fills/prf-long/` on the exchange. Seyoon
dispatches.

**Ready to dispatch**
