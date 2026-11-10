# Cryptography import shim retirement

[PR #282](https://github.com/Shilun-Allan-Li/tcslib/pull/282) at `f9753af6eff8a786ada92a06d019bb41ab8d1c39` retires the 23 import-only modules approved by Seyoon, including
`Composability.CCA2Scheme`. Its description lists the replacement modules. The surviving Lean files
have import and documentation edits. A source comparison and the previous checked objects both confirm
that the retired modules owned zero Lean declarations.

`Authentication.Defs` remains the shared MAC, signature, and hash interface. `Asymptotic.HardCore`
now collects the family, collection, and balanced-permutation Goldreich–Levin results. The
`FromPermutation` and `Stretch` results are available through their canonical modules. The private-key
and public-key facades explicitly preserve their earlier permutation-to-PRG exports.

The verification used the campaign base `acf3abe4734a709b529e38ee96baff42a3f434e8` and the checked #281 package and
source digests. It checked 1,188 surviving source import
closures and confirmed the ordered providers of 12 public entry points in Lean, with the planned
two-module reduction at `Asymptotic.HardCore`. The 23 retired paths all fail lookup in the new tree.

- 73 native checks cover all affected modules, `TCSlib`, and the Pass–shelat and
  Garg audit aggregates. The fresh olean tree contains 1,151 verified local
  objects, including 1,078 copied by source, object and direct-dependency
  digest. Three retained objects also match fresh independent recompilations byte for byte.
- 3,385 declaration types and bodies from 72 common
  rebuilt modules match after accounting for the location labels of five existing `sorry` proofs.
  The label differences are listed in [the verification receipt](VERIFICATION.json).
- The style comparison has zero new warnings or failures. The live source and tooling sweep has
  zero references to the retired paths.

`cryptography-import-shim-retirement-evidence.zip` has SHA-256 `8b4c0d4c618a17596325f3bab99f36c47b9c869796d3b10413239954b6bbfc22` and contains the check receipts, source diff,
facade comparisons and declaration comparison.

**Clear to merge — native replay, declaration comparison and facade probes pass.**
