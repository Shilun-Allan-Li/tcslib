# Asymptotic PRGs from one-way permutations

Seyoon merged the stretch relocation #266 at `6387f775c8848e5a1e3be7c36f73be56371c63a3`. The Lean sources and
checker inputs match its verified head `bcb6f33a120dd663d363afe21f6214465578d990`.

[PR #267](https://github.com/Shilun-Allan-Li/tcslib/pull/267) at `fbed01a2bb841ab557396cebb2609cca3de8b06d` puts the one-bit construction and security
proof [PS10, Theorem 79.4], the iterated generator and security proof
[PS10, Corollary 81.7], and `exists_securePRG_of_owp` in
`Pseudorandom.Generators.Asymptotic.FromPermutation`.

The route uses the evaluator and predictor machine in `Asymptotic.HardCoreLemmas`.
`Asymptotic.HardCore.Functions` contains the hard-core predicates and function-family
Goldreich–Levin proofs. `Asymptotic.HardCorePermutation.GoldreichLevin` contains
the balanced permutation proof. The two providers keep the new route free of
import cycles with the `HardCore` and `HardCorePermutation` compatibility imports.

- All 54 affected modules pass, including the library root and campaign Checks.
  The replay also verifies 1,040 transferred local objects and 3,810 external
  objects. Its roots cover 1,094 local modules.
- The census matches 151 declaration types, definition values, and axiom sets.
  It maps 143 declarations to the new files and 17 private names to their
  relocated spellings. All moved proof and definition bodies match by source
  bytes. Both legacy probes agree with the base, and the standalone import
  exposes the three security results.
- The three baseline and four head whole-file seals match all eight inherited
  diagnostics to the exact same proof steps. Six are now in `HardCore.Functions`
  and two in `FromPermutation`. The balanced permutation and claims seals pass.
  The unsealed control passes, direct reduction fails under the mask, and
  the published `PermFamily.hardCore_iff` passes under the same mask.
  The explicit source and generated-equation scans have zero hits. Three
  deferred provider references to `owpPredictorSnoc` map to its new home.
  [Ledger mapping](READS.json)
- The source style check reports zero findings. The campaign linter's added
  facade report comes from finite `Generators.lean` sharing the directory name.
  `Pseudorandom.lean` exports `FromPermutation` directly. The reader warnings
  and the size notice for the balanced proof carry forward from its old home.

`from-permutation-checks.zip` has SHA-256 `9c50663351fd8ffab1e8a76faf3bd098c3327be2c4a26734a65a29a9a3d7c7be`.
[Verification hashes](VERIFICATION.json)

**Clear to merge — the legacy imports, affected modules and seal comparison pass.**
