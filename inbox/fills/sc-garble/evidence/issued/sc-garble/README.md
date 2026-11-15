# Claude fill `sc-garble` (U1: special encryption and garbling probability)

Claude is the worker (Seyoon's standing ruling, 2026-11-11). The job proves seven admitted statements of
`TCSlib/Cryptography/SecureComputation/` [PS10, §6.2.2–6.2.3]: `spDecStr_wrongKey`, `specialScheme_wrongKey` and
`specialScheme_multiMessageSecure` (Claim 157.a) in `SpecialEncryptionSecurity.lean`, `nestedSpecial_wrongKeyBot` in
`GarblingSecurity.lean`, `uprob_not_good_le` (Claim 159.a) in `Garbling.lean`, `yaoSeed_good_whp` in `Yao.lean`
(that body only; the file is shared with the later `sc-yao`), and the B1 statement
`sliceMultiMessageSecure_of_prfOut` in `SpecialEncryptionMulti.lean`. It also publishes the stronger garbling bound
of requirement B2.

**The base is `fbd37f447596d4207c8d08b7ef7602f57fe95198`, the head of draft PR #315 (`prf-long`, branch `land/pass-shelat-prf-long`), not the
records tip.** The proof uses prf-long's D1–D4, which are not merged yet; under the proved-modulo rule the worker
builds on that head, and `sc-garble` lands after #315 merges.

Read [the brief](brief.md), the [environment addendum](fill-environment-addendum.md) and [ruling SG-1](ruling-SG-1.md) (Seyoon, 2026-11-15: a frozen-file exception that removes six private relabelling helpers of `SpecialEncryptionMulti.lean`; it overrides the brief where they differ). Verify the package with
`shasum -a 256 -c SHA256SUMS` from this directory.

- [Build order](order.txt): 166 TCSlib modules, generated at the base. These are the upstream closure of every
  module downstream of the five owned files, and of the modules helpers may import (the `FromPRF` facade,
  `NonMalleability/Simulation/Generic`, `Games/Efficiency`).
- [Mathlib roots](roots.txt): 71.
- [Source hashes](SOURCE-SHA256SUMS) at the base.
- [Base admissions](base-sorries.txt): 32 declarations in 15 modules. The only change must be the removal
  of the seven targets (25 in 11 modules).

Claude returns checkpoints and the final payload only at `inbox/fills/sc-garble/` on the exchange. Seyoon
dispatches.

**Ready to dispatch**
