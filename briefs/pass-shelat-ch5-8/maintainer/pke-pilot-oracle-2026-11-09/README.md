# Fixed-length public-key schemes and oracle security

Seyoon merged the [ensemble relocation #258](https://github.com/Shilun-Allan-Li/tcslib/pull/258) at `7f3129d5b2ab5f2aac97c2a83eb4893b1217cd5f`.
[PR #259](https://github.com/Shilun-Allan-Li/tcslib/pull/259) moves the fixed-length scheme and oracle games at `b4b04839bd16de049e55f6053b2491db94a9b7e9`.
It follows the [approved pilot](../cleanup-incremental-2026-11-09/final-r1/PKE-PILOT.md).

`OracleSecurity` groups the scheme, canonical padding, challenge codecs
and the CPA, CCA1 and CCA2 games. The general stateful oracle interfaces
live in the shared game modules. The legacy `Composability.PublicKey`
import re-exports the oracle module and houses the trapdoor CPA corollary.
The corollary still uses the pending `BitPublicKeyScheme.SingleBitSecure.padded_cpa`
bridge.

- The replay verifies 1,073 retained objects and compiles all 7 affected
  modules plus campaign Checks. The Checks object and output match #258.
- Standalone probes check the new and legacy imports, including the
  previously approved `pairFstD_padCt` simp rule. The new import closure
  excludes the trapdoor construction.
- The census matches all 236 declaration types, definitions, references
  and axiom dependencies. It maps 128 declarations to the new module
  and accounts for 6 generated private names and elaborator labels.
- All 4 whole-file seals pass with 6,825 requests.
  The explicit and generated-equation scans find zero reads. The thirteen
  sensitivity controls transfer through identical checked closures, and
  the generated-equation collector reruns its two controls.
- Plain and campaign style checks pass. `OracleSecurity` stays in one
  660-line file to keep the padding and game proofs beside their definitions.

The oracle scopes carry no diagnostics. The earlier ensemble ledger remains
the reference for the inherited reads in its own modules.

`VERIFICATION.json` binds the checked head to the evidence.
The SHA-256 of `oracle-checks.zip` is `aba73a03dfc1288c54da21a26c838fac07630c385e15800c64e857c022ab30e4`.

**Clear to merge — the oracle relocation and both imports pass.**
