# Private-key scheme and ensemble security relocation

Seyoon merged #270 at `afa745102f0f83530f6459a1f78992125be18dd5`. Its Lean and checker inputs match the verified
facade head `597ace8a30ffebe2a24cc4a9d05401ef898149b6`.

[PR #271](https://github.com/Shilun-Allan-Li/tcslib/pull/271) at `290353794eccc57bebeeaa2eb7d838d696b82005` moves the uniform scheme interface and
correctness contract into `Encryption.PrivateKey.Scheme`. The ciphertext
samplers, security predicates, multi-to-single-message reduction and
deterministic-encryption impossibility proof live in
`Encryption.PrivateKey.EnsembleSecurity`. Both modules have standalone imports.
The legacy `Asymptotic.Encryption` import re-exports them and hosts the PRG
construction. The private-key facade lists the two new modules.

The existing coin-transport lemma becomes
`PrivateKeyScheme.acceptProb_distinguisherL_congr` so the ensemble reduction
and PRG proof can share it. The PRG ciphertext and security proofs use the
published `encDist_apply` and `singleMessageSecure_iff` across the new boundary.

- All 35 affected modules pass, including the root and campaign Checks.
  The replay verifies 1,067 transferred local objects and 3,810 external objects.
- The census matches all 80 prior declaration types, definition values and
  axiom sets. It verifies 56 declarations in their new files. It maps three generated private names
  and the promoted coin-transport theorem. The old and new import probes agree.
- Whole-file seals pass for the source owners. The control blocks direct
  reduction of `encDist` and accepts its published equation.
  Focused seals match on eight downstream modules, with
  0 inherited diagnostics on each side.
  The edited files have zero explicit or generated foreign-definition reads.
- The existing four reader warnings follow their definitions. The source lint
  and diff check pass.

The ledger maps 5 deferred provider links to the new owners.
[Ledger mapping](READS.json)

`private-key-interface-checks.zip` has SHA-256 `7334d2d7f9c8901e2ef13011af0e888e63b3a0829da0ab52e922f5c99da98761`.
[Verification hashes](VERIFICATION.json)

Seyoon merged #271 at `816738e8edf5968e93a1db0790124955994f21da`. The Lean sources and checker inputs match the verified head.
