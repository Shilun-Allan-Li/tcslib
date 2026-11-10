# Tagged private-key encryption relocation

The campaign records head `9c2be2c35588d01bd67a6e1f32128fd4a6e06079` includes Seyoon's merge of #275. Its Lean
and checker inputs match the verified OracleFromPRF head `2a62b29d28a0778d93c39ab027e4cd4e85b294d4`.

[PR #276](https://github.com/Shilun-Allan-Li/tcslib/pull/276) at `511564d8aeafe8f5e13a1e30b202aad5e7ff080c` moves the tagged scheme, its machine
implementation, correctness and ciphertext length proofs, and CCA2 statement to
`Encryption.PrivateKey.EncryptThenTag`. The declarations and proof text move
verbatim in the `TCSlib.Cryptography.Composability` namespace. The new module
imports the oracle interface, PRF contract and machine support directly.
`Composability.CCA2Scheme` re-exports the declarations with its prior import
closure. The private-key facade lists the new owner and keeps the compatibility
import to preserve its earlier hard-core exports.

- All five affected modules and the separate campaign Checks replay pass.
  The replay verifies 1,104 transferred local objects and 3,810 external objects.
- The census matches all 45 types, definition values, elaborated references and
  axiom sets. It accounts for two relocated private names. The standalone and
  legacy import probes agree. `ccaScheme_cca2` retains its admission dependency.
- Both whole-file seals pass with the same admission warning. The standalone
  closure uses 1,040 requests from the baseline's 1,899. The controls block
  direct reduction of `ccaScheme` and accept its published length equation.
- The explicit and generated scans report zero foreign reads in the moved
  owner. Source lint, campaign lint and the diff check pass.

The cleanup ledger was checked against the relocated definition providers.
[Ledger comparison](READS.json)

`private-key-encrypt-then-tag-checks.zip` has SHA-256 `ede82065275ee4db8b52ca532c49dd5fd324b17f0751d828640597537744ad69`.
[Verification hashes](VERIFICATION.json)

**Clear to merge — the affected modules, both imports and seals pass.**

Seyoon merged #276 at `f1b67be52e62c9b812099b8377f4c2eef4bf9963`. The Lean sources and checker inputs match the verified head.
