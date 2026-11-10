# Private-key encryption facade

Seyoon merged #269 at `88befb0df9c2cd295dfc5d6d5a5e861ea4024314`. The Lean sources and checker inputs match
the verified GGM head `39e3a1b167aabe26151f2906e1505d32b8c79dfa`.

[PR #270](https://github.com/Shilun-Allan-Li/tcslib/pull/270) at `597ace8a30ffebe2a24cc4a9d05401ef898149b6` adds
`TCSlib.Cryptography.Encryption.PrivateKey` and imports it from `TCSlib`.
The facade brings together the existing ensemble and adaptive oracle modules.
The old import paths and all definitions, statements and proofs stay in place.

- The PRG single-message and PRF fixed-vector security proofs are available
  through the facade, including the composed PRG-to-encryption existence theorem.
- The fixed-length PRF and encrypt-then-tag constructions are also available.
  The adaptive CPA, CCA1 and CCA2 security proofs and the PRF scheme's CCA2
  counterexample still have admissions. The general CCA2 negation depends on
  that counterexample.
- The facade, the root and the campaign Checks pass one-module-at-a-time Lean
  checking. The replay verifies 1,097 transferred local objects and 3,810
  external objects.
- The standalone probes import only the facade and check 21 names and 11
  axiom sets. The source linter reports zero findings in the facade. The diff
  check passes.

`private-key-facade-checks.zip` has SHA-256 `b843a14dc7dffddfe6e8ea209e783004030e2086b4876bb56a2df3287b6dc04b`.
[Verification hashes](VERIFICATION.json)

Seyoon merged #270 at `afa745102f0f83530f6459a1f78992125be18dd5`. The Lean sources and checker inputs match the verified head.
