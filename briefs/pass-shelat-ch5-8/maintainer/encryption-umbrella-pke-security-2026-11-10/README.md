# Encryption map and public-key security relocation

[PR #281](https://github.com/Shilun-Allan-Li/tcslib/pull/281) at `e266fa9509f587297619699e284d12a5c4d149f7` updates the encryption umbrella and links
from the RSA and Rabin documentation to the shared public-key route. It
moves the trapdoor CPA corollary to `Encryption.PublicKey.TrapdoorCPA`
and the two non-malleability formulations to
`Encryption.PublicKey.NonMalleability.Indistinguishability` and
`Encryption.PublicKey.NonMalleability.Simulation`. The three original
`Composability` imports preserve their transitive exports. The moved
declarations and proof text are verbatim, and the RSA and Rabin edits
are comment-only.

The base `19476e28bcc60081d02795ae71c11f2024c217eb` includes the lattice integration in PR #280.
The replay verifies 855 unchanged objects from the checked signature and
hashing head `d9b7bf21dd257c2d14382fdab728633c2e41d006` and runs 318 fresh checks on the
combined source, including all 14 layout-affected modules, the library
root and campaign Checks. The original three owner files were compiled
on the exact base with identical dependency objects.

- All 108 declaration types, definition values, references and axiom sets
  match, with six compiler-private matcher helpers tracked to their new
  owner. The legacy and standalone import probes agree. The umbrella
  probe reaches both private-key routes, the public-key Regev route
  and the relocated security results.
- All six whole-file seals and both reader controls pass. The explicit
  and generated scans found zero foreign definition reads in the moved
  files.
- The existing RSA and Rabin size findings account for the six new comment
  lines in each file. The umbrella linter reports three leaf imports
  that the verified public-key facade supplies transitively. The actual
  umbrella import probe verifies that reachability.

The CPA corollary depends on the admitted `SingleBitSecure.padded_cpa`
bridge. The non-malleability modules retain three direct admissions,
and the simulation-based CPA equivalence uses two of them. All five
declaration dependencies are listed in `DECLARATIONS.json` in the archive.

The cleanup ledger was compared against the relocated providers.
[Ledger comparison](READS.json)

`encryption-umbrella-pke-security-checks.zip` has SHA-256 `96fc8ccc4335cf318905cb1dddb53d3733900475c727b748bb212e4028039c68`.
[Verification hashes](VERIFICATION.json)

**Clear to merge — the combined replay, public import probes and six seals pass.**
