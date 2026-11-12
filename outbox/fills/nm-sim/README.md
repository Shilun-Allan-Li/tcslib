# NM simulation fill `nm-sim` (Theorem 174.8)

Claude is the worker (Seyoon's standing ruling, 2026-11-11). The targets are
`FixedLengthPKScheme.nmSecure_of_simNMSecure` and `FixedLengthPKScheme.simNMSecure_of_nmSecure_cpa` in
`TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation.lean`. The proof base is
`262d6e9ae526c82eb68fe5a6169156bd1504e6d8` on `cryptography/pass-shelat-ch2-4` (the merge of #294). This fill runs in parallel with the
landing of `dl-consolidation`; the brief's duplication rule binds. Read [the brief](brief.md) and the
[environment addendum](fill-environment-addendum.md). Verify the package with `shasum -a 256 -c SHA256SUMS`
from this directory.

- [Build order](order.txt): 252 TCSlib modules. These are the upstream closure of
  `NonMalleability/Simulation` and every module downstream of it.
- [Mathlib roots](roots.txt): 97.
- [Source hashes](SOURCE-SHA256SUMS) at the issue base.
- [Base admissions](base-sorries.txt): 26.

Claude returns checkpoints and the final payload only at `inbox/fills/nm-sim/` on the exchange. Seyoon
dispatches.

**Ready to dispatch**
