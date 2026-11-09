# Asymptotic PRG contract relocation

The verified source at `eb67b18405a968b75155429bb9a7c884874795b5` on `7a9f9ceeb0202584b5561b60061c742fef29181c` moves the PRG contract into
`Pseudorandom.Generators.Asymptotic.Defs` byte-for-byte. The legacy import
re-exports it and the pseudorandomness facade imports the new module.
The map now attributes `Ensemble.Pseudorandom` to its shared ensemble owner
and its concrete-advantage characterization to the generator module.
[PR #264](https://github.com/Shilun-Allan-Li/tcslib/pull/264)

- The 73 affected modules pass, including the library root and campaign Checks.
  The isolated tree verifies 1,013 retained local and 3,810 external objects.
- The old and new standalone imports give the same output for nine declarations.
  The census matches all 31 names, types, values, and axiom dependencies.
  Six declarations contain generated binder labels whose module path changes
  with the move. The comparison rewrites just that path in those labels.
- The owner seal verifies 1,209 requests and reproduces the six inherited
  diagnostics. Both focused HardCore seals pass with the six sealable moved
  definitions masked. The control passes unsealed and fails at `Iff.rfl` with
  `PRG.Secure` sealed.
- The six inherited owner diagnostics and one explicit read move with their
  original lines. Three HardCore ledger rows point to the new module for their
  recorded PRG provider references. [Ledger mapping](READS.json)
- The plain style check has zero findings. The campaign linter treats the
  finite generator implementation as a facade based on its directory name.
  The actual topic facade imports the new module, and the requested reverse
  dependency would create a cycle. The inherited findings match the base.

`prg-defs-checks.zip` has SHA-256 `098bc7d9de68f84a7e70447e40261d2610367c7d4505df1481d08c5725e7602c`. The archive
contains the exact sources, native receipts, census, seal evidence, and lint
comparison.

Seyoon merged the verified source at `850d97de5dff2594d8cdf75f3d7705df4df27108`.
