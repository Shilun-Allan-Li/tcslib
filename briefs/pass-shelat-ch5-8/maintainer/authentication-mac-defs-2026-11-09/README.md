# MAC interface relocation

The campaign base `7f8f8dda2ca17cf9ca002325c1fe878353fff92d` includes Seyoon's merge of #276. Its Lean and checker
inputs match the verified EncryptThenTag head `511564d8aeafe8f5e13a1e30b202aad5e7ff080c`.

[PR #277](https://github.com/Shilun-Allan-Li/tcslib/pull/277) at `f2bc431a3834fcc864ec2ed9fc544a0574ff3102` moves the MAC interface, forgery game, security
predicate and their equations to `Authentication.MAC.Defs`. `Authentication.Encoding`
owns the shared `splitBits` and `atParam` helpers and their reading equations. Both
blocks move verbatim in the original namespace. The old definitions module
re-exports them alongside the signature and hash contracts.

- All nine affected modules and the campaign Checks aggregate pass.
  The replay verified 1,102 unchanged local objects and 3,810 external objects.
- The census matches 251 declaration types, definition
  values, references and axiom sets, including 48
  moved declarations. Lean now emits the coin-space proof separately in the
  signature game and renumbers one auxiliary proof. Their checked proof terms,
  types and axiom sets agree. The legacy and both standalone import probes agree.
- The whole-file seals pass for the original definitions file and all three
  resulting files. Focused seals on PRFMAC, Lamport and HashAndSign pass before
  and after the move. The control blocks reduction of `atParam` and accepts
  its published equation.
- The explicit and generated scans report zero foreign definition reads in
  the changed owners. Both style lints and the diff check pass.

The moved declarations have no admission dependencies. The existing PRF MAC
security statement remains admitted in its construction file. The archive
includes the initial documentation lint findings and the scratch-path probe
failure from the first candidate.

The cleanup ledger was compared against the relocated providers.
[Ledger comparison](READS.json)

`authentication-mac-defs-checks.zip` has SHA-256 `441ab93f4030adff16b6bec62937e6f8fd98074f87f8808bf0de260fbe45d2e0`.
[Verification hashes](VERIFICATION.json)

**Clear to merge — the affected modules, compatibility imports and seals pass.**

Seyoon merged #277 at `e9ce331210a66bf5ec2d47f72e41bfc3457299a6`. The Lean sources and checker inputs match the verified head.
