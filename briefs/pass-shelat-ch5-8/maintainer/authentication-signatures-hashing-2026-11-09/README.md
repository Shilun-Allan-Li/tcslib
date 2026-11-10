# Signature and hashing relocation

The campaign base `3e3c6a8cec129793cca29596f61690bd902094cd` includes Seyoon's merge of #278. Its Lean and checker
inputs match the verified PRF-MAC head `c17739c2a4969233167501a2b97928b8d1f7cef0`.

[PR #279](https://github.com/Shilun-Allan-Li/tcslib/pull/279) at `d9b7bf21dd257c2d14382fdab728633c2e41d006` completes the authentication and hashing
layout in two commits. The contract commit `79cd32dcfddc65ef6c68364830375710be72d9d2` moves the
signature and collision-resistant hash interfaces and games. All three
contract files and their import closures match the checked head byte for
byte. The construction commit moves Lamport signatures, hash-and-sign and the
discrete-log hash. The authentication and hashing facades index the resulting
routes. The original import paths preserve their transitive exports.

- All thirteen affected modules and campaign Checks pass. The replay verified
  1,105 unchanged local objects and 3,810 external objects.
- All 214 original declarations match, including their definition values and
  axiom dependencies. The collision game now emits a local coin-space proof
  with the same type, body and axioms as its former shared helper. The old
  import bundle and the canonical import bundle expose the same checked types.
- All four baseline and five relocated whole-file seals pass. The controls
  block direct reduction of signature one-time security and hash evaluation
  and accept their published equations. The explicit and generated foreign
  definition read scans pass.
- The eleven authentication and hashing files pass source lint. The root
  source lint matches its baseline. The campaign linter's existing Lamport
  report follows the moved machine abbreviations. Its five additional root
  reports concern modules reachable through the facades, as verified by the
  import graph and the native root check.

The existing admissions are `lamport_oneTimeSecure`,
`hashAndSign_oneTimeSecure` and `dlHash_crh`. The
`exists_oneTimeSecure_of_crh_owf` corollary still depends on the first two.
The collision game's padding, splitting and membership tests are verbatim.

The LWE/SIS branch at `02726106544597f6988ae50bde4c80071aa64b57` has its own eight SIS modules and
imports `Hashing.SIS` from the same facade path. When reconciling the branches,
use one `Hashing.lean` with imports of `Hashing.CollisionResistant`,
`Hashing.FromDiscreteLog` and `Hashing.SIS`. The source-path and import
comparison is archived in `LWE-SIS.json`. Future SIS consumers can use the
preserved `Authentication.CRH` contract and its collision parser.

The cleanup ledger was compared against the relocated providers.
[Ledger comparison](READS.json)

`authentication-signatures-hashing-checks.zip` has SHA-256 `515d4c3f3fe042f798a1eeadab9861d9223d9e2676b17818121817e9348f6d58`.
[Verification hashes](VERIFICATION.json)

**Clear to merge — declarations, legacy imports, the affected modules and seals pass.**
