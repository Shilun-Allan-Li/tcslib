# Fixed-length PRF scheme and oracle claims relocation

Seyoon merged #274 at `fe7618ebb264350844f1ae97b4c48150d2434b80`. Its Lean and checker inputs match the verified
oracle interface head `10370bd0683085e54a10a49a5cbe9b2eb2fbcef5`.

[PR #275](https://github.com/Shilun-Allan-Li/tcslib/pull/275) at `2a62b29d28a0778d93c39ab027e4cd4e85b294d4` moves the fixed-length PRF wrapper, its length
proof, CPA and CCA1 statements, CCA2 counterexample and derived negation into
`Encryption.PrivateKey.OracleFromPRF`. The declaration and proof text moves
verbatim in the `TCSlib.Cryptography.Composability` namespace.
`Composability.PRFScheme` re-exports the declarations with its prior import
closure. The private-key facade imports the new owner and drops three
import-only compatibility modules from its closure.

- All five affected modules and the separate campaign Checks replay pass.
  The replay verifies 1,103 transferred local objects and 3,810 external objects.
- The census matches all 14 declaration types, definition values, references
  and axiom sets. The CPA, CCA1 and explicit CCA2 counterexample retain their
  admissions. The derived CCA2 negation still depends on the counterexample.
  The standalone and legacy import probes agree.
- The baseline and relocated whole-file seals pass with the same three
  admission warnings. The standalone closure uses 1,841 requests from the
  baseline's 1,946. The controls block direct reduction of the wrapper and
  accept its published projection equation.
- The explicit and generated scans report zero foreign reads in the moved
  owner. Source lint, campaign lint and the diff check pass.

The cleanup ledger was checked against the relocated definition provider.
[Ledger comparison](READS.json)

`private-key-oracle-from-prf-checks.zip` has SHA-256 `5ad9f897c11a388b8b68d4e6497ff58df1e0f54f66c6ecdf7ec4d5c827c65823`.
[Verification hashes](VERIFICATION.json)

**Clear to merge — the affected modules, both imports and seals pass.**
