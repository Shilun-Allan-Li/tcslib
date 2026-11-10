# Private-key oracle security relocation

The campaign records head `1b5356b210d952977e4f9bef6278273d75caf1d5` includes Seyoon's merge of #273. Its Lean
and checker inputs match the verified FromPRF head `7e508a4501cfe078a48d84b444abc50443a08443`.

[PR #274](https://github.com/Shilun-Allan-Li/tcslib/pull/274) at `10370bd0683085e54a10a49a5cbe9b2eb2fbcef5` moves the fixed-length interface, attack
modes, oracle implementations and IND security predicate into
`Encryption.PrivateKey.OracleSecurity`. The declarations and proofs move
verbatim in the `TCSlib.Cryptography.Composability` namespace. The new owner
imports the scheme interface and game support directly. `Composability.Defs`
re-exports the declarations with its prior import closure. The private-key
facade and public-key game documentation point to the new owner.

- All 12 affected modules and the separate campaign Checks replay pass.
  The replay verifies 1,095 transferred local objects and 3,810 external objects.
- The census matches all 110 declaration types, definition values, references
  and axiom sets. It accounts for 11 relocated private names and for the
  generated universe binder scopes of `Attack.noConfusion` and
  `Attack.noConfusionType`. The standalone and legacy import probes agree.
- The baseline and relocated whole-file seals pass. The standalone closure
  uses 678 requests from the baseline's 1,314. The controls block direct
  reduction of `decOpen` and accept the published CPA equation.
- The public-key oracle game, PRF wrapper, tagged scheme, and the two
  non-malleability consumers pass focused seals on both revisions with the
  same 25 definitions and matchers per probe. Their warning outputs match.
  The explicit and generated scans report zero foreign reads in the moved owner.
- Source lint, campaign lint and the diff check pass.

The cleanup ledger was checked against the relocated definition providers.
[Ledger comparison](READS.json)

`private-key-oracle-security-checks.zip` has SHA-256 `456b3d4066b59527a1c9219bce858ae6a5abebe0c72a9ba9a69c636d95e7c763`.
[Verification hashes](VERIFICATION.json)

Seyoon merged #274 at `fe7618ebb264350844f1ae97b4c48150d2434b80`. The Lean sources and checker inputs match the verified head.
