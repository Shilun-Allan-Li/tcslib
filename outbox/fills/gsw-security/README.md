# Claude fill `gsw-security` (GSW phase 5: F5 SIS columns, F6 Security)

Claude is the worker, a single agent (Seyoon's ruling, 2026-11-16: GSW fill wave, 2 Claude jobs). The job proves
the 6 admitted targets of `TCSlib/Cryptography/Hashing/SIS/Columns.lean` (F5: the column leftover-hash hybrid) and
`TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Security.lean` (F6: IND-CPA of public-key GSW from DLWE,
two DLWE advantages plus `2Nε`); about 270 lines. The parallel job `gsw-core` (F1–F4, F7) starts from the same
base; each cites the other's targets as frozen statements.

**Base.** `486f44f8414c20a2d21e452c44de8b8c8d8513a0`, the gate-closed head of draft PR #333 (`stmt/gsw`; Gate 41
closed by disposition).

**F0 / #332.** #333 is stacked on #332 (`486f44f8~3` is #332's head `94eae71b779c4ca0f76c138d699f4d737dbd6cee`), so
the base contains F0's readers proved. This job does not use them. #332 and #333 merge first; the maintainer
rebases the fills onto the then records tip at landing.

Integration check of #333 on the current tip: pending at issue; the maintainer records the result in the plan.

Read [the brief](brief.md) and the [environment addendum](fill-environment-addendum.md). Verify the package with
`shasum -a 256 -c SHA256SUMS` from this directory.

- [Build order](order.txt): 147 TCSlib modules, generated at the base: the upstream closure of the modules
  downstream of the two owned files (among them the `Hashing` and `AdvancedEncryption` facades) and of
  `Pseudorandom/Indistinguishability`, which the owned files may import.
- [Mathlib roots](roots.txt): 84.
- [Source hashes](SOURCE-SHA256SUMS) at the base.
- [Base admissions](base-sorries.txt): 53 declarations in 15 modules (the 35 GSW targets and 18 complexity-layer
  admissions). The only change must be the removal of the 6 targets (F5 2, F6 4, as in plan §G7): 47 in 13.

Claude returns a checkpoint after F5 and the final payload only at `inbox/fills/gsw-security/` on the exchange.
Seyoon dispatches.

**Ready to dispatch**
