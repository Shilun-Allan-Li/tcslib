# PRG-based private-key encryption relocation

Seyoon merged #271 at `816738e8edf5968e93a1db0790124955994f21da`. Its Lean and checker inputs match the verified
interface and games head `290353794eccc57bebeeaa2eb7d838d696b82005`.

[PR #272](https://github.com/Shilun-Allan-Li/tcslib/pull/272) at `73d000bfa590f98169f22a1e3bf64b88ebe64d5c` moves the pad construction, correctness proof,
concrete four-hybrid bound and asymptotic single-message security proof to
`Encryption.PrivateKey.FromPRG`. The declaration and proof text moves verbatim.
The legacy `Asymptotic.Encryption` path re-exports the construction and its
prior import closure. The private-key and pseudorandomness construction maps
now point to the new home.

- All 35 affected modules pass, including the root and campaign Checks.
  The replay verifies 1,068 transferred local objects and 3,810 external objects.
- The census matches all 24 declaration types, definition values, elaborated
  references and axiom sets after normalizing four relocated private kernel
  names. The two legacy probes and the standalone `FromPRG` probe agree.
- The relocated file passes the same 1,229 whole-file seal requests as the
  verified #271 baseline. The control blocks direct reduction of `padXor`,
  and its published list-encoding equation still works under the seal. The
  explicit and generated foreign-definition scans report zero reads in scope.
- Plain source lint and the diff check pass. The campaign linter repeats two
  reader warnings, for `padXor` and `prgPadFun`, and five direct-import flags
  in the pseudorandomness map. Those five modules are reachable through
  `Pseudorandom.Functions` on both revisions.

The cleanup ledger was checked against the relocated definition providers.
[Ledger comparison](READS.json)

`private-key-from-prg-checks.zip` has SHA-256 `b428f0d44668803bfc92e0b2c5fe5858ff4600aa88f52b48a1867af85a9be47c`.
[Verification hashes](VERIFICATION.json)

**Clear to merge — the affected modules, standalone and legacy imports, and seals pass.**
